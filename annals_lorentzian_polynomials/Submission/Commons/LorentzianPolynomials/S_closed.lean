import Mathlib
import Submission.Commons.Analysis.MvPolynomial.isStable_closed
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable

open Finsupp Matrix MvPolynomial UpperHalfPlane Topology Set
open scoped MvPowerSeries.WithPiTopology

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.LorentzianPolynomials

/-- The module topology on `H n d`. -/
instance instTopologicalSpaceH (n d : ℕ) : TopologicalSpace (H n d) :=
  moduleTopology ℝ (homogeneousSubmodule (Fin n) ℝ d)

/-- We write `S n d` for the set of degree `d` homogeneous stable polynomials in `n`
variables with nonnegative coefficients. -/
abbrev S (n d : ℕ) : Set (H n d) :=
  { f | IsStable f.1 ∧ ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m }

/-- Scalar multiplication by `ℝ` is continuous on `MvPolynomial (Fin n) ℝ`, where the
polynomial topology is the one induced from multivariate power series. -/
lemma continuousSMul_mvPolynomial (n : ℕ) :
    ContinuousSMul ℝ (MvPolynomial (Fin n) ℝ) := by
  classical
  let f : MvPolynomial (Fin n) ℝ → MvPowerSeries (Fin n) ℝ := MvPolynomial.toMvPowerSeries
  have hf_ind : IsInducing f := by
    dsimp [f]
    exact (MvPolynomial.toMvPowerSeries_isUniformInducing (σ := Fin n) (R := ℝ)).isInducing
  refine ⟨?continuous_smul⟩
  rw [hf_ind.continuous_iff]
  have hcomp : (f ∘ fun p : ℝ × MvPolynomial (Fin n) ℝ => p.1 • p.2) =
      (fun p : ℝ × MvPowerSeries (Fin n) ℝ => p.1 • p.2) ∘
        (fun p : ℝ × MvPolynomial (Fin n) ℝ => (p.1, f p.2)) := by
    funext p
    dsimp [f]
  rw [hcomp]
  exact Continuous.comp continuous_smul
    (continuous_fst.prodMk (hf_ind.continuous.comp continuous_snd))

/-- The set of stable polynomials, as a subset of the finite-dimensional space of degree-`d`
homogeneous polynomials, is closed for the module topology. -/
lemma isClosed_stable_modTopology (n d : ℕ) :
    @IsClosed (homogeneousSubmodule (Fin n) ℝ d)
      (moduleTopology ℝ (homogeneousSubmodule (Fin n) ℝ d))
      {f | IsStable f.1} := by
  classical
  let X := homogeneousSubmodule (Fin n) ℝ d
  let τX : TopologicalSpace X := moduleTopology ℝ X
  let τsub : TopologicalSpace X := instTopologicalSpaceSubtype
  haveI : ContinuousSMul ℝ (MvPolynomial (Fin n) ℝ) := continuousSMul_mvPolynomial n
  have hclosed_subtype : @IsClosed X τsub
      {f : X | f.1 = 0 ∨ ∀ z : Fin n → ℍ,
        MvPolynomial.aeval (((↑) : ℍ → ℂ) ∘ z) f.1 ≠ 0} :=
    Commons.Analysis.MvPolynomial.isStable_closed n d
  have hle : @moduleTopology ℝ _ X _ _ ≤ τsub := by
    refine @moduleTopology_le ℝ _ X _ _ τsub ?_ ?_
    · infer_instance
    · infer_instance
  have hcont : @Continuous X X τX τsub id := by
    rw [@continuous_id_iff_le]
    exact hle
  have hpre := @IsClosed.preimage X X τX τsub id hcont _ hclosed_subtype
  change @IsClosed X τX {f | IsStable f.1}
  simpa [Set.preimage_id, IsStable] using hpre

/-- The coefficient functional on the space of degree-`d` homogeneous polynomials, as a linear
map to `ℝ`. -/
def coeLinear (n d : ℕ) (m : Fin n →₀ ℕ) :
    homogeneousSubmodule (Fin n) ℝ d →ₗ[ℝ] ℝ where
  toFun := fun f => f.1.coeff m
  map_add' := by
    intro f g
    simp [MvPolynomial.coeff_add]
  map_smul' := by
    intro r f
    simp [MvPolynomial.coeff_smul]

/-- The coefficient functional is continuous for the module topology. -/
lemma continuous_coeLinear (n d : ℕ) (m : Fin n →₀ ℕ) :
    @Continuous (homogeneousSubmodule (Fin n) ℝ d) ℝ
      (moduleTopology ℝ (homogeneousSubmodule (Fin n) ℝ d)) inferInstance
      (coeLinear n d m) := by
  let X := homogeneousSubmodule (Fin n) ℝ d
  let τX : TopologicalSpace X := moduleTopology ℝ X
  letI : TopologicalSpace X := τX
  haveI : IsModuleTopology ℝ X := ⟨rfl⟩
  exact IsModuleTopology.continuous_of_linearMap (coeLinear n d m)

/-- The set of degree-`d` homogeneous polynomials with nonnegative coefficients is closed. -/
lemma isClosed_nonneg_coeff (n d : ℕ) :
    @IsClosed (homogeneousSubmodule (Fin n) ℝ d)
      (moduleTopology ℝ (homogeneousSubmodule (Fin n) ℝ d))
      {f | ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m} := by
  classical
  let X := homogeneousSubmodule (Fin n) ℝ d
  let τX : TopologicalSpace X := moduleTopology ℝ X
  letI : TopologicalSpace X := τX
  have hmain : @IsClosed X τX {f : X | ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m} := by
    rw [Set.ofPred_forall]
    apply isClosed_iInter
    intro m
    have hclosed : @IsClosed X τX {f : X | 0 ≤ (coeLinear n d m) f} := by
      exact isClosed_le (α := ℝ) (β := X) continuous_const (continuous_coeLinear n d m)
    simpa [coeLinear] using hclosed
  exact hmain

/-- The set `S n d` of degree-`d` homogeneous stable polynomials with nonnegative coefficients
is closed in `H n d`. -/
theorem S_closed (n d : ℕ) : IsClosed (S n d) := by
  classical
  change @IsClosed (homogeneousSubmodule (Fin n) ℝ d)
    (moduleTopology ℝ (homogeneousSubmodule (Fin n) ℝ d))
    {f : homogeneousSubmodule (Fin n) ℝ d |
      IsStable f.1 ∧ ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m}
  change @IsClosed (homogeneousSubmodule (Fin n) ℝ d)
    (moduleTopology ℝ (homogeneousSubmodule (Fin n) ℝ d))
    ({f : homogeneousSubmodule (Fin n) ℝ d | IsStable f.1} ∩
      {f : homogeneousSubmodule (Fin n) ℝ d | ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m})
  exact @IsClosed.inter (homogeneousSubmodule (Fin n) ℝ d)
    {f : homogeneousSubmodule (Fin n) ℝ d | IsStable f.1}
    {f : homogeneousSubmodule (Fin n) ℝ d | ∀ m : Fin n →₀ ℕ, 0 ≤ f.1.coeff m}
    (moduleTopology ℝ (homogeneousSubmodule (Fin n) ℝ d))
    (isClosed_stable_modTopology n d) (isClosed_nonneg_coeff n d)

end Commons.LorentzianPolynomials
