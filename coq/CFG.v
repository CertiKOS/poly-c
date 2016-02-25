Require Import Utf8.
Require Import Wf.
Require Import ZArith.
Require Import Omega.

Notation "a ≥ b" := (Z.ge a b).
Notation "a + b" := (Z.add a b).
Notation "a - b" := (Z.sub a b).

Definition Zpos := {z | z ≥ 0}.
Definition projZ (dp: Zpos) := proj1_sig dp.
Coercion   projZ: Zpos >-> Z.

Section S.

  (* Heaps. *)
  Hypothesis H: Type.

  (* CFG vertices and edges. *)
  Definition V := nat.
  Definition E := (V * (H → H) * Zpos * V)%type.

  Section SEMANTICS.
    Hypothesis edges: E → Prop.

    Inductive steps: (H * V) → (H * V) → Prop :=
      steps_intro: ∀ H₁ v₁ H₂ v₂ act δ (EDG: edges (v₁, act, δ, v₂)),
                     steps (H₁, v₁) (H₂, v₂).

    Inductive safe: Z → (H * V) → Prop :=
      safe_intro: ∀ n H₁ v₁
                    (FUEL:  ∀ act δ v₂ (EDG: edges (v₁, act, δ, v₂)), n ≥ δ)
                    (SAFE₂: ∀ act δ v₂ (EDG: edges (v₁, act, δ, v₂)), safe (n-δ) (act H₁, v₂)),
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
      + generalize (SAFE₂ _ _ _ EDG).
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
  Definition sound_final (edges: E → Prop) (ψ: V → (H → Z)) :=
    ∀ v, final edges v → ∀ H, ψ v H ≥ 0.

  (* Well_founded has to have its operands swapped! *)
  Definition terminates {A: Type} (R: A → A → Prop) :=
    well_founded (λ x y, R y x).


  (* First, the positivity lemma. *)
  Lemma soundness1:
    ∀ (edges: E → Prop) (entry: V)     (* CFG program *)
      (TERM: terminates (steps edges)) (* The program is (super) strongly terminating. *)
      (ψ: V → (H → Z))                 (* Potential annotations on CFG vertices. *)
      (SOUNDS: sound_step edges ψ)     (* The annotations are sound. *)
      (SOUNDF: sound_final edges ψ),  
    ∀ H₀ v₀, ψ v₀ H₀ ≥ 0.
  Proof.
    intros.
    set (conf := (H₀, v₀)).
    replace v₀ with (snd conf) by reflexivity.
    replace H₀ with (fst conf) by reflexivity.
    generalize conf. clear conf H₀ v₀.
    apply (well_founded_ind TERM).
    intros [H₀ v₀] IND. simpl.
    destruct (is_final edges v₀) as [? | NOTFIN].
    now auto using SOUNDF.
    destruct NOTFIN as [act [δ [v₁ EDG]]].
    assert (STEP: steps edges (H₀, v₀) (act H₀, v₁)).
    now econstructor; eauto.
    generalize (IND _ STEP).
    generalize (SOUNDS _ _ _ _ EDG H₀).
    simpl. intros.
    assert (δ ≥ 0) by (unfold projZ; apply proj2_sig).
    omega.
  Qed.

  (* Second, the actual soundness! *)
  Theorem soundness:
    ∀ (edges: E → Prop) (entry: V)     (* CFG program *)
      (TERM: terminates (steps edges)) (* The program is (super) strongly terminating. *)
      (ψ: V → (H → Z))                 (* Potential annotations on CFG vertices. *)
      (SOUNDS: sound_step edges ψ)     (* The annotations are sound. *)
      (SOUNDF: sound_final edges ψ),  
    ∀ H₀, safe edges (ψ entry H₀) (H₀, entry).
  Proof.
    intros.
    set (conf := (H₀, entry)).
    replace entry with (snd conf) by reflexivity.
    replace H₀    with (fst conf) by reflexivity.
    generalize conf. clear conf H₀ entry.
    apply (well_founded_ind TERM).
    intros [H₁ v₁] IND. simpl.
    constructor; intros.
    + generalize (SOUNDS v₁ v₂ act δ EDG H₁).
      assert (SIGN: ψ v₂ (act H₁) ≥ 0) by eauto using soundness1.
      omega.
    + apply safewk with (n₂ := ψ v₂ (act H₁)).
      - set (conf := (act H₁, v₂)).
        replace v₂       with (snd conf) by reflexivity.
        replace (act H₁) with (fst conf) by reflexivity.
        apply IND. econstructor; eauto.
      - auto using SOUNDS.
  Qed.
    
End S.
