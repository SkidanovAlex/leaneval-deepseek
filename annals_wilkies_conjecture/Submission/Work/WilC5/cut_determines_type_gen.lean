import Mathlib
import Submission.Work.WilC5.cut_determines_type_two_models
import Submission.Work.WilC5.exists_fin_relabel_elim_uniform
import Submission.Work.WilC2.Dcl

set_option maxHeartbeats 1000000

namespace Work.WilC5

open FirstOrder FirstOrder.Language

/-- **Splitting the last variable off a block of variables.**

`ψ` has free variables `γ ⊕ Fin (n+1)`: a `γ`-block and `n+1` further variables, the first of which
is a distinguished point.  The relabelled formula `ψ.relabel splitPointMap` has free variables
`(γ ⊕ Fin n) ⊕ Fin 1`, i.e. the point has been moved into the final singleton block and the other
`n` variables have been absorbed into the first block; on an assignment that sends the `n` extra
variables to `p (Sum.inr i)` and the point to `x`, the two formulas have the same truth value.

This is the syntactic step that lets the one-point form of "the cut determines the type" be applied
to a tuple of extra variables. -/
theorem realize_relabel_split_point {L : FirstOrder.Language} {γ : Type} {n : ℕ} {M : Type}
    [L.Structure M] (ψ : L.Formula (γ ⊕ Fin (n + 1))) (p : γ ⊕ Fin n → M) (x : M) :
    (ψ.relabel (Sum.elim
        (fun a : γ => (Sum.inl (Sum.inl a) : (γ ⊕ Fin n) ⊕ Fin 1))
        (Fin.cons (Sum.inr 0) (fun i : Fin n => (Sum.inl (Sum.inr i)))))).Realize
      (Sum.elim p (fun _ : Fin 1 => x)) ↔
    ψ.Realize (Sum.elim (fun a : γ => p (Sum.inl a)) (Fin.cons x (fun i => p (Sum.inr i)))) := by
  rw [Formula.realize_relabel]
  refine iff_of_eq (congrArg (fun w => ψ.Realize w) ?_)
  funext z
  rcases z with a | j
  · simp [Sum.elim_inl]
  · induction j using Fin.cases with
    | zero => simp [Sum.elim_inr]
    | succ i => simp [Sum.elim_inr, Sum.elim_inl]

theorem cut_determines_type_gen (hOM : WilkiesDesign.CG.OMinModels) {K L : Type}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TR]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    [FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TR]
    {A : Set K} (hA : Work.WilC2.Dcl A ⊆ A) {B : Set L} (hB : Work.WilC2.Dcl B ⊆ B)
    (σ : A → B)
    (hσ : ∀ {n : ℕ} (φ : WilkiesDesign.CG.LRc.Formula (Fin n)) (a : Fin n → A),
      (φ.Realize (fun i => (a i : K)) ↔ φ.Realize (fun i => (σ (a i) : L))))
    {x : K} {y : L}
    (hcut : (∀ a : A, ((a : K) < x ↔ σ a < y)) ∧ (∀ a : A, (x < (a : K) ↔ y < σ a)))
    {n : ℕ} (ψ : WilkiesDesign.CG.LRc.Formula (A ⊕ Fin (n + 1))) (v : Fin n → A) :
    (ψ.Realize (Sum.elim (fun a : A => (a : K)) (Fin.cons x (fun i => ((v i : K)))))) ↔
      (ψ.Realize (Sum.elim (fun a : A => ((σ a : L)))
        (Fin.cons y (fun i => ((σ (v i) : L)))))) := by
  classical
  -- ### 1. Move the point variable into the final singleton block
  let τ : A ⊕ Fin (n + 1) → (A ⊕ Fin n) ⊕ Fin 1 :=
    Sum.elim (fun a : A => (Sum.inl (Sum.inl a) : (A ⊕ Fin n) ⊕ Fin 1))
      (Fin.cons (Sum.inr 0 : (A ⊕ Fin n) ⊕ Fin 1) (fun i : Fin n => (Sum.inl (Sum.inr i))))
  -- ### 2. Compress the (possibly infinite) parameter block `A` to finitely many parameters,
  --     uniformly in the model
  obtain ⟨m, σ₀, χ, hχ⟩ :=
    Work.WilC5.exists_fin_relabel_elim_uniform (ψ.relabel τ)
  -- ### 3. The finite parameter list of the compressed formula
  set W : Fin m → A := (fun i => Sum.elim (fun a : A => a) (fun j : Fin n => v j) (σ₀ i)) with hWdef
  have hW₁ : (fun i : Fin m => (W i : K)) =
      (Sum.elim (fun a : A => (a : K)) (fun j : Fin n => ((v j : A) : K))) ∘ σ₀ := by
    funext i
    rcases h : σ₀ i with a | j <;>
      simp only [hWdef, h, Function.comp_apply, Sum.elim_inl, Sum.elim_inr]
  have hW₂ : (fun i : Fin m => ((σ (W i) : B) : L)) =
      (Sum.elim (fun a : A => ((σ a : B) : L)) (fun j : Fin n => ((σ (v j) : B) : L))) ∘ σ₀ := by
    funext i
    rcases h : σ₀ i with a | j <;>
      simp only [hWdef, h, Function.comp_apply, Sum.elim_inl, Sum.elim_inr]
  -- ### 4. The two sides in the language of the compressed formula
  have hK : χ.Realize (Sum.elim (fun i : Fin m => (W i : K)) (fun _ : Fin 1 => x)) ↔
      ψ.Realize (Sum.elim (fun a : A => (a : K)) (Fin.cons x (fun i => ((v i : A) : K)))) := by
    have h1 := hχ (M := K) (Sum.elim (fun a : A => (a : K)) (fun j : Fin n => ((v j : A) : K)))
      (fun _ : Fin 1 => x)
    rw [← hW₁] at h1
    refine h1.trans ?_
    simpa using realize_relabel_split_point (L := WilkiesDesign.CG.LRc) ψ
      (Sum.elim (fun a : A => (a : K)) (fun j : Fin n => ((v j : A) : K))) x
  have hL : χ.Realize (Sum.elim (fun i : Fin m => ((σ (W i) : B) : L)) (fun _ : Fin 1 => y)) ↔
      ψ.Realize (Sum.elim (fun a : A => ((σ a : B) : L))
        (Fin.cons y (fun i => ((σ (v i) : B) : L)))) := by
    have h1 := hχ (M := L) (Sum.elim (fun a : A => ((σ a : B) : L))
      (fun j : Fin n => ((σ (v j) : B) : L))) (fun _ : Fin 1 => y)
    rw [← hW₂] at h1
    refine h1.trans ?_
    simpa using realize_relabel_split_point (L := WilkiesDesign.CG.LRc) ψ
      (Sum.elim (fun a : A => ((σ a : B) : L)) (fun j : Fin n => ((σ (v j) : B) : L))) y
  -- ### 5. The two-model theorem for the compressed formula
  have key := Work.WilC5.cut_determines_type_two_models (A' := B) hOM hA hB σ hσ hcut χ W
  exact hK.symm.trans (key.trans hL)

end Work.WilC5
