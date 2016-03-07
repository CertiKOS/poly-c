Require Import Utf8.
Require Import Wf.
Require Import ZArith.
Require Import Omega.

Notation "a ≥ b" := (Z.ge a b).
Notation "a < b" := (Z.lt a b).
Notation "a + b" := (Z.add a b).
Notation "a - b" := (Z.sub a b).

Section S.

  (* Heaps. *)
  Hypothesis H: Type.

  (* CFG vertices and edges. *)
  Definition V := nat.
  Definition E := (V * (H → H) * Z * V)%type.

  Section SEMANTICS.
    Hypothesis edges: E → Prop.

    Inductive steps: (H * V) → (H * V) → Prop :=
      steps_intro: ∀ H₁ v₁ H₂ v₂ act δ (EDG: edges (v₁, act, δ, v₂)),
                     steps (H₁, v₁) (H₂, v₂).

    Inductive safe: Z → (H * V) → Prop :=
      safe_intro: ∀ n H₁ v₁
                    (FUEL: ∀ act δ v₂ (EDG: edges (v₁, act, δ, v₂)), n ≥ δ)
                    (SAFE: ∀ act δ v₂ (EDG: edges (v₁, act, δ, v₂)), safe (n-δ) (act H₁, v₂)),
                    safe n (H₁, v₁).
    Theorem safewk:
      ∀ n₂ H v (SAFE: safe n₂ (H, v)) n₁ (GE: n₁ ≥ n₂),
        safe n₁ (H, v).
    Proof.
      intros until 1.
      induction SAFE as [? ? ? ? ? IND].
      constructor; intros.
      + generalize (FUEL _ _ _ EDG).
        intros; omega.
      + generalize (SAFE _ _ _ EDG).
        intros. apply IND with (δ).
        assumption. omega.
    Qed.
      
  End SEMANTICS.

  (* We assume a decidable set of final CFG vertices. *)
  Definition has_succ (edges: E → Prop) v := ∃ act δ v₂, edges (v, act, δ, v₂).
  Definition final (edges: E → Prop) v    := ¬ has_succ edges v.
  Hypothesis is_final: ∀ edges v, (final edges v) ∨ (has_succ edges v).

  (* The two soundness conditions of potential annotations. *)
  Definition sound_step (edges: E → Prop) (ψ: V → (H → Z)) :=
    ∀ v₁ v₂ act δ (EDGE: edges (v₁, act, δ, v₂)),
     ∀ H, ψ v₁ H - δ ≥ ψ v₂ (act H).
  Definition sound_free (edges: E → Prop) (ψ: V → (H → Z)) :=
    ∀ v₁ v₂ act δ (EDGE: edges (v₁, act, δ, v₂)),
     δ < 0 → ∀ H, ψ v₁ H ≥ 0.
  Definition sound_final (edges: E → Prop) (ψ: V → (H → Z)) :=
    ∀ v, final edges v → ∀ H, ψ v H ≥ 0.

  (* Define what a terminating configuration is. *)
  Definition terminates {A: Type} (R: A → A → Prop) x :=
    Acc (λ x y, R y x) x.

  (* First, the positivity lemma. *)
  Lemma soundness1:
    ∀ (v₁: V) (H₁: H) (edges: E → Prop)
      (ψ: V → (H → Z))
      (SOUNDS: sound_step edges ψ)
      (SOUNDN: sound_free edges ψ)
      (SOUNDF: sound_final edges ψ) 
      (TERM: terminates (steps edges) (H₁, v₁)),
      ψ v₁ H₁ ≥ 0.
  Proof.
    do 7 intro.
    set (conf := (H₁, v₁)).
    replace v₁ with (snd conf) by reflexivity.
    replace H₁ with (fst conf) by reflexivity.
    generalize conf. clear conf H₁ v₁.
    induction 1 as [[H₁ v₁] TERM IND]. simpl in *.
    destruct (is_final edges v₁) as [? | NOTFIN].
    now auto using SOUNDF.
    destruct NOTFIN as [act [δ [v₂ EDG]]].
    assert (STEP: steps edges (H₁, v₁) (act H₁, v₂)).
    now econstructor; eauto.
    generalize (IND _ STEP).
    generalize (SOUNDS _ _ _ _ EDG H₁).
    simpl. intros.
    assert (DIS: δ ≥ 0 ∨ δ < 0) by omega.
    destruct DIS. omega.
    eauto using SOUNDN.
  Qed.

  (* Second, the actual soundness! *)
  Theorem soundness:
    ∀ (v₁: V) (H₁: H) (edges: E → Prop)          (* CFG program *)
      (ψ: V → (H → Z))                           (* Potential annotations on CFG vertices. *)
      (SOUNDS: sound_step edges ψ)               (* The annotations are sound. *)
      (SOUNDN: sound_free edges ψ)
      (SOUNDF: sound_final edges ψ)  
      (TERM: terminates (steps edges) (H₁, v₁)), (* The program is strongly terminating. *)
      safe edges (ψ v₁ H₁) (H₁,v₁).
  Proof.
    do 7 intro.
    set (conf := (H₁, v₁)).
    replace v₁ with (snd conf) by reflexivity.
    replace H₁ with (fst conf) by reflexivity.
    generalize conf. clear conf H₁ v₁.
    induction 1 as [[H₁ v₁] TERM IND]. simpl in *.
    constructor; intros.
    + generalize (SOUNDS v₁ v₂ act δ EDG H₁).
      assert (SIGN: ψ v₂ (act H₁) ≥ 0)
        by (eapply soundness1, TERM, steps_intro; eauto).
      omega.
    + apply safewk with (n₂ := ψ v₂ (act H₁)).
      - set (conf := (act H₁, v₂)).
        replace v₂       with (snd conf) by reflexivity.
        replace (act H₁) with (fst conf) by reflexivity.
        apply IND. econstructor; eauto.
      - auto using SOUNDS.
  Qed.
    
End S.
