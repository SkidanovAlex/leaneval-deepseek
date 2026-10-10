import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Submission.Work.SSGRoute.PTW.RestrictRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PTW

/-!
# Weights of finite dimensional `regRep`-invariant submodules

This file proves `Work.SSGRoute.PTW.exists_character_of_finiteDim_regRep_submodule`.
The mathematical content is the classical fact that a finite dimensional (unitary)
representation of a commutative group over `ℂ` has a *weight*: a common eigenvector for the
whole group.  We obtain it from the simultaneous diagonalisation of a *commuting family of
self-adjoint operators* (Mathlib's `LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute`),
applied to the operators `ρ g + ρ g⁻¹` and `i (ρ g⁻¹ - ρ g)`, where `ρ = restrictRepHom`.

Concretely, given a finite dimensional `regRep`-invariant submodule `E ≤ L²(Q, μ)` and `y : Q`
acting nontrivially on `E`:

* the joint eigenspaces of the commuting family `{ρ g + ρ g⁻¹, i (ρ g⁻¹ - ρ g) : g : Q}`
  span `E`, and on each of them `ρ g` is a scalar `ψ g`;
* because `ρ y ≠ 1` on `E`, one of those joint eigenspaces is not contained in `ker (ρ y - 1)`;
* on it, `ψ : Q → ℂ` is a multiplicative functional with `ψ y ≠ 1` and `ψ g = ⟪v, ρ g v⟫ / ‖v‖²`
  for a fixed nonzero vector `v`, hence continuous;
* `ψ` is packaged into a continuous monoid homomorphism `χ : Q →* ℂˣ`.

The auxiliary `char*` definitions and lemmas below build the spectral input; they are stated for
an arbitrary `regRep`-invariant submodule so that they are reusable.
-/

section Helpers

variable {Q : Type*} [CommGroup Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q]
  [T2Space Q] [MeasurableSpace Q] [BorelSpace Q] {μ : MeasureTheory.Measure Q}
  [MeasureTheory.Measure.IsMulLeftInvariant μ] [MeasureTheory.IsProbabilityMeasure μ]
  [MeasureTheory.IsLocallyFiniteMeasure μ] [MeasureTheory.Measure.InnerRegularCompactLTTop μ]

/-- The restricted regular representation on an invariant submodule, viewed as a linear map. -/
noncomputable def charRho (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) (g : Q) : E →ₗ[ℂ] E :=
  (Work.SSGRoute.PTW.restrictRepHom (μ := μ) E hE g : E →ₗ[ℂ] E)

/-- The self-adjoint operator `ρ g + ρ g⁻¹`. -/
noncomputable def charAop (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) (g : Q) : E →ₗ[ℂ] E :=
  charRho (μ:=μ) E hE g + charRho (μ:=μ) E hE g⁻¹

/-- The self-adjoint operator `i (ρ g⁻¹ - ρ g)`. -/
noncomputable def charBop (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) (g : Q) : E →ₗ[ℂ] E :=
  Complex.I • (charRho (μ:=μ) E hE g⁻¹ - charRho (μ:=μ) E hE g)

theorem charRho_injective (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) (g : Q) :
    Function.Injective (charRho (μ:=μ) E hE g) := by
  intro a b hab
  exact (Work.SSGRoute.PTW.restrictRepHom (μ:=μ) E hE g).injective hab

theorem charRho_mul_apply (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) (g h : Q) (v : E) :
    (charRho (μ:=μ) E hE (g * h)) v = (charRho (μ:=μ) E hE g) ((charRho (μ:=μ) E hE h) v) := by
  apply Subtype.ext
  show Work.SSGRoute.PTW.regRep (g*h) (v : MeasureTheory.Lp ℂ 2 μ)
    = Work.SSGRoute.PTW.regRep g (Work.SSGRoute.PTW.regRep h (v : MeasureTheory.Lp ℂ 2 μ))
  rw [Work.SSGRoute.PTW.regRep_mul_apply]

theorem charRho_one (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) :
    charRho (μ:=μ) E hE 1 = 1 := by
  apply LinearMap.ext
  intro v
  apply Subtype.ext
  show Work.SSGRoute.PTW.regRep (1:Q) (v : MeasureTheory.Lp ℂ 2 μ) = (v : MeasureTheory.Lp ℂ 2 μ)
  rw [Work.SSGRoute.PTW.regRep_one]
  rfl

theorem charRho_inner (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) (g : Q) (x y : E) :
    inner ℂ ((charRho (μ:=μ) E hE g) x) ((charRho (μ:=μ) E hE g) y) = inner ℂ x y :=
  LinearIsometryEquiv.inner_map_map (Work.SSGRoute.PTW.restrictRepHom (μ:=μ) E hE g) x y

theorem charRho_apply_inv (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) (g : Q) (v : E) :
    (charRho (μ:=μ) E hE g) ((charRho (μ:=μ) E hE g⁻¹) v) = v := by
  apply Subtype.ext
  show Work.SSGRoute.PTW.regRep g (Work.SSGRoute.PTW.regRep g⁻¹ (v : MeasureTheory.Lp ℂ 2 μ)) = (v : MeasureTheory.Lp ℂ 2 μ)
  rw [← Work.SSGRoute.PTW.regRep_mul_apply, mul_inv_cancel, Work.SSGRoute.PTW.regRep_one]
  rfl

theorem charRho_inv_apply (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) (g : Q) (v : E) :
    (charRho (μ:=μ) E hE g⁻¹) ((charRho (μ:=μ) E hE g) v) = v := by
  apply Subtype.ext
  show Work.SSGRoute.PTW.regRep g⁻¹ (Work.SSGRoute.PTW.regRep g (v : MeasureTheory.Lp ℂ 2 μ)) = (v : MeasureTheory.Lp ℂ 2 μ)
  rw [← Work.SSGRoute.PTW.regRep_mul_apply, inv_mul_cancel, Work.SSGRoute.PTW.regRep_one]
  rfl

theorem charInnerRhoRhoInv (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) (g : Q) (x y : E) :
    inner ℂ ((charRho (μ:=μ) E hE g) x) y = inner ℂ x ((charRho (μ:=μ) E hE g⁻¹) y) := by
  conv_lhs => rw [← charRho_apply_inv (μ:=μ) E hE g y]
  rw [charRho_inner]

theorem charInnerRhoInvRho (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) (g : Q) (x y : E) :
    inner ℂ ((charRho (μ:=μ) E hE g⁻¹) x) y = inner ℂ x ((charRho (μ:=μ) E hE g) y) := by
  conv_lhs => rw [← charRho_inv_apply (μ:=μ) E hE g y]
  rw [charRho_inner]

theorem charAop_isSymmetric (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) (g : Q) :
    (charAop (μ:=μ) E hE g).IsSymmetric := by
  intro x y
  simp only [charAop, LinearMap.add_apply]
  rw [inner_add_left, inner_add_right, charInnerRhoRhoInv, charInnerRhoInvRho, add_comm]

theorem charBop_isSymmetric (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) (g : Q) :
    (charBop (μ:=μ) E hE g).IsSymmetric := by
  intro x y
  simp only [charBop, LinearMap.smul_apply, LinearMap.sub_apply]
  rw [inner_smul_left, inner_sub_left]
  rw [inner_smul_right, inner_sub_right]
  rw [charInnerRhoInvRho, charInnerRhoRhoInv, Complex.conj_I]
  ring

theorem charRho_commute (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) (g h : Q) :
    Commute (charRho (μ:=μ) E hE g) (charRho (μ:=μ) E hE h) := by
  rw [Commute]
  apply LinearMap.ext
  intro v
  simp only [Module.End.mul_apply]
  apply Subtype.ext
  show Work.SSGRoute.PTW.regRep g (Work.SSGRoute.PTW.regRep h (v : MeasureTheory.Lp ℂ 2 μ))
    = Work.SSGRoute.PTW.regRep h (Work.SSGRoute.PTW.regRep g (v : MeasureTheory.Lp ℂ 2 μ))
  rw [← Work.SSGRoute.PTW.regRep_mul_apply, ← Work.SSGRoute.PTW.regRep_mul_apply, mul_comm]

theorem charAop_commute (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) (g h : Q) :
    Commute (charAop (μ:=μ) E hE g) (charAop (μ:=μ) E hE h) := by
  try unfold charAop
  try unfold charBop
  exact
    Commute.add_left
      (Commute.add_right (charRho_commute (μ:=μ) E hE g h) (charRho_commute (μ:=μ) E hE g h⁻¹))
      (Commute.add_right (charRho_commute (μ:=μ) E hE g⁻¹ h) (charRho_commute (μ:=μ) E hE g⁻¹ h⁻¹))

theorem charBop_commute (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) (g h : Q) :
    Commute (charBop (μ:=μ) E hE g) (charBop (μ:=μ) E hE h) := by
  have hc : ∀ x y : Q, ∀ v : E, charRho (μ:=μ) E hE x (charRho (μ:=μ) E hE y v)
      = charRho (μ:=μ) E hE y (charRho (μ:=μ) E hE x v) := fun x y v => by
    have := LinearMap.congr_fun (charRho_commute (μ:=μ) E hE x y).eq v
    simpa only [Module.End.mul_apply] using this
  rw [Commute, SemiconjBy]
  apply LinearMap.ext
  intro v
  simp only [charAop, charBop, Module.End.mul_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.add_apply, map_smul, map_sub, map_add, hc g h, hc g h⁻¹, hc g⁻¹ h, hc g⁻¹ h⁻¹]
  try abel
  try module

theorem charAop_Bop_commute (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) (g h : Q) :
    Commute (charAop (μ:=μ) E hE g) (charBop (μ:=μ) E hE h) := by
  have hc : ∀ x y : Q, ∀ v : E, charRho (μ:=μ) E hE x (charRho (μ:=μ) E hE y v)
      = charRho (μ:=μ) E hE y (charRho (μ:=μ) E hE x v) := fun x y v => by
    have := LinearMap.congr_fun (charRho_commute (μ:=μ) E hE x y).eq v
    simpa only [Module.End.mul_apply] using this
  rw [Commute, SemiconjBy]
  apply LinearMap.ext
  intro v
  simp only [charAop, charBop, Module.End.mul_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.add_apply, map_smul, map_sub, map_add, hc g h, hc g h⁻¹, hc g⁻¹ h, hc g⁻¹ h⁻¹]
  try abel
  try module

theorem charBop_Aop_commute (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) (g h : Q) :
    Commute (charBop (μ:=μ) E hE g) (charAop (μ:=μ) E hE h) := by
  have hc : ∀ x y : Q, ∀ v : E, charRho (μ:=μ) E hE x (charRho (μ:=μ) E hE y v)
      = charRho (μ:=μ) E hE y (charRho (μ:=μ) E hE x v) := fun x y v => by
    have := LinearMap.congr_fun (charRho_commute (μ:=μ) E hE x y).eq v
    simpa only [Module.End.mul_apply] using this
  rw [Commute, SemiconjBy]
  apply LinearMap.ext
  intro v
  simp only [charAop, charBop, Module.End.mul_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    LinearMap.add_apply, map_smul, map_sub, map_add, hc g h, hc g h⁻¹, hc g⁻¹ h, hc g⁻¹ h⁻¹]
  try abel
  try module

/-- The commuting family of self-adjoint operators whose joint eigenspaces are the weights. -/
noncomputable def charTopOp (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) : Q ⊕ Q → E →ₗ[ℂ] E
  | Sum.inl g => charAop (μ:=μ) E hE g
  | Sum.inr g => charBop (μ:=μ) E hE g

theorem charTopOp_isSymmetric (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) (i : Q ⊕ Q) :
    (charTopOp (μ:=μ) E hE i).IsSymmetric := by
  cases i with
  | inl g => exact charAop_isSymmetric (μ:=μ) E hE g
  | inr g => exact charBop_isSymmetric (μ:=μ) E hE g

theorem charTopOp_commute (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) :
    Pairwise (Function.onFun Commute (charTopOp (μ:=μ) E hE)) := by
  intro i j hij
  cases i with
  | inl g =>
    cases j with
    | inl h => exact charAop_commute (μ:=μ) E hE g h
    | inr h => exact charAop_Bop_commute (μ:=μ) E hE g h
  | inr g =>
    cases j with
    | inl h => exact charBop_Aop_commute (μ:=μ) E hE g h
    | inr h => exact charBop_commute (μ:=μ) E hE g h

/-- The reconstruction of `ρ g` from the self-adjoint operators `A g` and `B g`. -/
theorem charRho_eq (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) (g : Q) :
    charRho (μ:=μ) E hE g = (2:ℂ)⁻¹ • (charAop (μ:=μ) E hE g + Complex.I • charBop (μ:=μ) E hE g) := by
  apply LinearMap.ext
  intro v
  simp only [charAop, charBop, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.sub_apply]
  rw [smul_smul, Complex.I_mul_I, neg_smul, one_smul, neg_sub]
  module

theorem charRho_continuous_apply (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) (v : E) :
    Continuous fun g : Q => (charRho (μ:=μ) E hE g) v := by
  have hcont : Continuous (fun g : Q => (((charRho (μ:=μ) E hE g) v : E) : MeasureTheory.Lp ℂ 2 μ)) := by
    rw [show (fun g : Q => (((charRho (μ:=μ) E hE g) v : E) : MeasureTheory.Lp ℂ 2 μ))
        = fun g : Q => Work.SSGRoute.PTW.regRep (μ:=μ) g (v : MeasureTheory.Lp ℂ 2 μ) from rfl]
    exact Work.SSGRoute.PTW.continuous_regRep_apply (μ:=μ) (v : MeasureTheory.Lp ℂ 2 μ)
  exact Continuous.subtype_mk hcont (fun g => ((charRho (μ:=μ) E hE g) v).2)

end Helpers

/-- **Weight of a finite dimensional subrepresentation.**  A finite dimensional
`regRep`-invariant submodule of `Lp ℂ 2 μ` on which `y` acts nontrivially has a continuous
character `χ : Q →* ℂˣ` with `χ y ≠ 1`.

Proof route (all inside the finite dimensional complex inner product space `E`, `Q` abelian):
take a nonzero `regRep`-invariant submodule `W` of minimal dimension; for `g : Q` the operators
`A := ρ g + ρ g⁻¹` and `B := ρ g - ρ g⁻¹` (times `-i`) are commuting self-adjoint endomorphisms of
`W`, so by the finite dimensional spectral theorem
(`LinearMap.IsSymmetric.direct_sum_isInternal` / `.orthogonalFamily_eigenspaces`) each of them
acts as a scalar on the minimal `W`; hence so does `ρ g = (A + iB)/2`, say `ρ g = χ g • 1`.
Then `χ` is a monoid homomorphism, `χ y ≠ 1`, and it is continuous because for `0 ≠ w ∈ W`,
`χ g = ⟪regRep g w, w⟫ / ‖w‖²` and `g ↦ regRep g w` is continuous
(`Work.SSGRoute.PTW.continuous_regRep_apply`). -/
theorem exists_character_of_finiteDim_regRep_submodule {Q : Type*} [CommGroup Q]
    [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q] [T2Space Q] [MeasurableSpace Q]
    [BorelSpace Q] {μ : MeasureTheory.Measure Q} [MeasureTheory.Measure.IsMulLeftInvariant μ]
    [MeasureTheory.IsProbabilityMeasure μ] [MeasureTheory.IsLocallyFiniteMeasure μ]
    [MeasureTheory.Measure.InnerRegularCompactLTTop μ] (E : Submodule ℂ (MeasureTheory.Lp ℂ 2 μ))
    (hE : ∀ (h : Q), ∀ v ∈ E, Work.SSGRoute.PTW.regRep (μ := μ) h v ∈ E) [FiniteDimensional ℂ E]
    (y : Q) (hy : Work.SSGRoute.PTW.restrictRepHom (μ := μ) E hE y ≠ 1) :
    ∃ χ : Q →* ℂˣ, Continuous χ ∧ χ y ≠ 1 := by
  -- Simultaneous diagonalisation of the commuting family of self-adjoint operators.
  have hdecomp : (⨆ χ : (Q ⊕ Q) → ℂ,
      ⨅ i, Module.End.eigenspace (charTopOp (μ:=μ) E hE i) (χ i)) = ⊤ :=
    LinearMap.IsSymmetric.iSup_iInf_eq_top_of_commute
      (T := charTopOp (μ:=μ) E hE)
      (fun i => charTopOp_isSymmetric (μ:=μ) E hE i)
      (charTopOp_commute (μ:=μ) E hE)
  -- `y` acts nontrivially, so `ρ y - 1 ≠ 0`.
  have hyne : (charRho (μ:=μ) E hE y - 1) ≠ 0 := by
    intro h
    apply hy
    apply LinearIsometryEquiv.ext
    intro v
    show (charRho (μ:=μ) E hE y) v = v
    have h1 := congrArg (fun f : E →ₗ[ℂ] E => f v) h
    rw [LinearMap.sub_apply, Module.End.one_apply, LinearMap.zero_apply] at h1
    exact sub_eq_zero.mp h1
  -- Pick a joint eigenspace `V` not contained in `ker (ρ y - 1)`.
  obtain ⟨χ, hχ⟩ : ∃ χ : (Q ⊕ Q) → ℂ,
      ¬ (⨅ i, Module.End.eigenspace (charTopOp (μ:=μ) E hE i) (χ i)) ≤
        (charRho (μ:=μ) E hE y - 1).ker := by
    by_contra hc
    push Not at hc
    apply hyne
    apply LinearMap.ext
    intro v
    have htop : (⊤ : Submodule ℂ E) ≤ (charRho (μ:=μ) E hE y - 1).ker := by
      rw [← hdecomp]
      exact iSup_le hc
    exact LinearMap.mem_ker.mp (htop Submodule.mem_top)
  obtain ⟨v₀, hv₀V, hv₀⟩ : ∃ v : E,
      v ∈ (⨅ i, Module.End.eigenspace (charTopOp (μ:=μ) E hE i) (χ i)) ∧
      (charRho (μ:=μ) E hE y) v ≠ v := by
    by_contra h
    push Not at h
    exact hχ (fun v hv => by
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
      exact h v hv)
  -- On `V`, `ρ g` is the scalar `ψ g`.
  let ψ : Q → ℂ := fun g => (χ (Sum.inl g) + Complex.I * χ (Sum.inr g)) / 2
  have hψ : ∀ g (v : E), v ∈ (⨅ i, Module.End.eigenspace (charTopOp (μ:=μ) E hE i) (χ i)) →
      (charRho (μ:=μ) E hE g) v = ψ g • v := by
    intro g v hv
    have hv' : ∀ i, v ∈ Module.End.eigenspace (charTopOp (μ:=μ) E hE i) (χ i) :=
      (Submodule.mem_iInf _).mp hv
    have hA : (charAop (μ:=μ) E hE g) v = χ (Sum.inl g) • v := by
      have h := hv' (Sum.inl g)
      rwa [Module.End.mem_eigenspace_iff] at h
    have hB : (charBop (μ:=μ) E hE g) v = χ (Sum.inr g) • v := by
      have h := hv' (Sum.inr g)
      rwa [Module.End.mem_eigenspace_iff] at h
    rw [charRho_eq (μ:=μ) E hE g, LinearMap.smul_apply, LinearMap.add_apply,
      LinearMap.smul_apply, hA, hB]
    have hinner : χ (Sum.inl g) • v + Complex.I • (χ (Sum.inr g) • v)
        = (χ (Sum.inl g) + Complex.I * χ (Sum.inr g)) • v := by
      rw [add_smul, smul_smul]
    rw [hinner, smul_smul]
    change (2⁻¹ * (χ (Sum.inl g) + Complex.I * χ (Sum.inr g))) • v
      = ((χ (Sum.inl g) + Complex.I * χ (Sum.inr g)) / 2) • v
    congr 1
    ring
  have hv₀0 : v₀ ≠ 0 := by
    intro h0
    exact hv₀ (by rw [h0, map_zero])
  have hψv : ∀ g, (charRho (μ:=μ) E hE g) v₀ = ψ g • v₀ := fun g => hψ g v₀ hv₀V
  -- `ψ` is a multiplicative functional.
  have hsmul_inj : ∀ a b : ℂ, a • v₀ = b • v₀ → a = b := by
    intro a b hab
    have h0 : (a - b) • v₀ = 0 := (sub_smul a b v₀).trans (sub_eq_zero.mpr hab)
    rcases smul_eq_zero.mp h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hv₀0
  have hψ1 : ψ 1 = 1 := by
    apply hsmul_inj
    rw [← hψv 1, charRho_one]
    simp
  have hψmul : ∀ g h : Q, ψ (g * h) = ψ g * ψ h := by
    intro g h
    apply hsmul_inj
    rw [← hψv (g * h), charRho_mul_apply, hψv h, map_smul, hψv g, smul_smul, mul_comm]
  have hψ_ne0 : ∀ g, ψ g ≠ 0 := by
    intro g h
    have h0 : (charRho (μ:=μ) E hE g) v₀ = (charRho (μ:=μ) E hE g) 0 := by
      rw [map_zero, hψv g, h, zero_smul]
    exact hv₀0 ((charRho_injective (μ:=μ) E hE g) h0)
  have hψy : ψ y ≠ 1 := by
    intro h
    exact hv₀ (by rw [hψv y, h, one_smul])
  -- `ψ` is continuous, as `ψ g = ⟪v₀, ρ g v₀⟫ / ⟪v₀, v₀⟫`.
  have hinner0 : inner ℂ v₀ v₀ ≠ 0 := inner_self_ne_zero.mpr hv₀0
  have hcontψ : Continuous ψ := by
    have hv : Continuous fun g : Q => (charRho (μ:=μ) E hE g) v₀ :=
      charRho_continuous_apply (μ:=μ) E hE v₀
    have hinner : Continuous fun g : Q => inner ℂ v₀ ((charRho (μ:=μ) E hE g) v₀) :=
      Continuous.inner continuous_const hv
    have hkey : ψ = fun g : Q => inner ℂ v₀ ((charRho (μ:=μ) E hE g) v₀) / inner ℂ v₀ v₀ := by
      funext g
      have h1 : inner ℂ v₀ ((charRho (μ:=μ) E hE g) v₀) = ψ g * inner ℂ v₀ v₀ := by
        rw [hψv g]
        exact inner_smul_right v₀ v₀ (ψ g)
      rw [h1]
      exact (mul_div_cancel_right₀ (ψ g) hinner0).symm
    rw [hkey]
    exact hinner.div_const _
  -- Package `ψ` as a continuous character.
  let χm : Q →* ℂˣ :=
    { toFun := fun g => Units.mk0 (ψ g) (hψ_ne0 g)
      map_one' := by
        apply Units.ext
        rw [Units.val_mk0, Units.val_one]
        exact hψ1
      map_mul' := by
        intro g h
        apply Units.ext
        rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.val_mk0]
        exact hψmul g h }
  refine ⟨χm, ?_, ?_⟩
  · rw [Units.continuous_iff]
    refine ⟨?_, ?_⟩
    · have hcomp : (Units.val ∘ χm) = ψ := by
        funext g
        rfl
      rw [hcomp]
      exact hcontψ
    · have heq : (fun g : Q => ↑((χm g)⁻¹)) = fun g : Q => ψ g⁻¹ := by
        funext g
        rw [← map_inv χm g]
        rfl
      rw [heq]
      exact hcontψ.comp continuous_inv
  · intro h
    apply hψy
    have h2 : (↑(χm y) : ℂ) = 1 := by
      have h3 := congrArg (fun u : ℂˣ => (u : ℂ)) h
      rwa [Units.val_one] at h3
    exact h2

end Work.SSGRoute.PTW
