import Mathlib
import ChallengeDeps
import Submission.Poisson
import Submission.Commons.Lattice.PoissonSummation.lattice_shifted_mass_le_rank
import Submission.Commons.Lattice.Gaussian.orthFam_mass_prod
import Submission.Commons.Lattice.Discrete.discreteTopology_quotLattice
import Submission.Commons.Lattice.PoissonSummation.lattice_psf
import Submission.Commons.Lattice.Module.basis_extension_pure
import Submission.VoronoiMeasure
import Submission.Commons.LinearAlgebra.Projection.linearIndependent_proj_complement
import Submission.Commons.LinearAlgebra.Independence.linearIndependent_of_ambient
import Submission.Commons.LinearAlgebra.Projection.linearIndependent_proj_complement
import Submission.Commons.LinearAlgebra.Independence.linearIndependent_of_ambient

open Module MeasureTheory Metric
open scoped Real BigOperators InnerProductSpace RealInnerProductSpace ENNReal NNReal Pointwise
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Submission.QuotientLattice

variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

noncomputable section

/-! ## Real span of a ℤ-lattice -/

/-- The real span of a `ℤ`-submodule of `E`. -/
def realSpan (ℒ : Submodule ℤ E) : Submodule ℝ E := Submodule.span ℝ (ℒ : Set E)

lemma mem_realSpan {ℒ : Submodule ℤ E} {x : E} (hx : x ∈ ℒ) : x ∈ realSpan ℒ :=
  Submodule.subset_span hx

/-! ## Orthogonal projections onto a subspace and its complement -/

/-- Decomposition of `x` into its components in `S` and `Sᗮ` (orthogonal complement). -/
lemma proj_decomp (S : Submodule ℝ E) (x : E) :
    x = S.starProjection x + Sᗮ.starProjection x := by
  have h : Sᗮ.starProjection x = x - S.starProjection x := by
    rw [Submodule.starProjection_orthogonal' S]
    rfl
  rw [h]
  abel

/-- The component in `Sᗮ` of `x` equals `x` minus the component in `S`. -/
lemma proj_orth_comp (S : Submodule ℝ E) (x : E) :
    Sᗮ.starProjection x = x - S.starProjection x := by
  rw [Submodule.starProjection_orthogonal' S]
  rfl

/-- For `x` with orthogonal components `a ∈ S` and `b ∈ Sᗮ`, the norm squares add. -/
lemma norm_sq_orthogonal_add (S : Submodule ℝ E) {a b : E} (ha : a ∈ S) (hb : b ∈ Sᗮ) :
    ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have horth : ⟪a, b⟫_ℝ = 0 := ((Submodule.mem_orthogonal (K := S) b).mp hb) a ha
  simpa [horth] using norm_add_sq (𝕜 := ℝ) (x := a) (y := b)

/-- Square of the norm decomposes over the orthogonal decomposition `E = S ⊕ Sᗮ`. -/
lemma norm_sq_proj_add (S : Submodule ℝ E) (x : E) :
    ‖x‖ ^ 2 = ‖S.starProjection x‖ ^ 2 + ‖Sᗮ.starProjection x‖ ^ 2 := by
  have hx : x = S.starProjection x + Sᗮ.starProjection x := proj_decomp S x
  have hS : S.starProjection x ∈ S := Submodule.starProjection_apply_mem S x
  have hSo : Sᗮ.starProjection x ∈ Sᗮ := Submodule.starProjection_apply_mem Sᗮ x
  calc
    ‖x‖ ^ 2 = ‖S.starProjection x + Sᗮ.starProjection x‖ ^ 2 := by rw [← hx]
    _ = ‖S.starProjection x‖ ^ 2 + ‖Sᗮ.starProjection x‖ ^ 2 :=
      norm_sq_orthogonal_add S hS hSo

/-- The orthogonal projection onto a subspace does not increase the norm. -/
lemma norm_starProjection_le (S : Submodule ℝ E) (x : E) : ‖S.starProjection x‖ ≤ ‖x‖ := by
  have h : ‖x‖ ^ 2 = ‖S.starProjection x‖ ^ 2 + ‖Sᗮ.starProjection x‖ ^ 2 := norm_sq_proj_add S x
  nlinarith [sq_nonneg ‖Sᗮ.starProjection x‖, norm_nonneg x, norm_nonneg (S.starProjection x)]

/-- Projection onto `S` kills elements of the orthogonal complement of `S`. -/
lemma starProjection_eq_zero_of_mem_orthogonal (S : Submodule ℝ E) {x : E} (hx : x ∈ Sᗮ) :
    S.starProjection x = 0 := by
  simpa using (Submodule.eq_starProjection_of_mem_orthogonal (K := S) (u := x) (v := 0)
    (Submodule.zero_mem S) (by simpa using hx))

/-- Projection onto `Sᗮ` kills elements of `S`. -/
lemma starProjection_orthogonal_eq_zero_of_mem (S : Submodule ℝ E) {x : E} (hx : x ∈ S) :
    Sᗮ.starProjection x = 0 := by
  have hx' : x ∈ Sᗮᗮ := by
    rw [Submodule.orthogonal_orthogonal S]
    exact hx
  exact starProjection_eq_zero_of_mem_orthogonal Sᗮ hx'

/-! ## The quotient lattice: orthogonal projection of `ℒ` onto `Sᗮ` -/

/-- The image of a `ℤ`-submodule under the orthogonal projection onto the orthogonal
complement of the subspace `S`.  For `S = realSpan ℒ'` with `ℒ'` primitive in `ℒ`, this is
the quotient lattice `ℒ/ℒ'` of the paper. -/
def quotLattice (ℒ : Submodule ℤ E) (S : Submodule ℝ E) : Submodule ℤ E :=
  ℒ.map ((Sᗮ.starProjection : E →ₗ[ℝ] E).restrictScalars ℤ)

/-- Elements of the quotient lattice lie in the orthogonal complement of `S`. -/
lemma quotLattice_le_orthogonal (ℒ : Submodule ℤ E) (S : Submodule ℝ E) :
    quotLattice ℒ S ≤ Sᗮ.restrictScalars ℤ := by
  intro x hx
  rcases (Submodule.mem_map.mp hx) with ⟨y, hy, rfl⟩
  exact Submodule.starProjection_apply_mem Sᗮ y

/-- Membership in the quotient lattice. -/
lemma mem_quotLattice {ℒ : Submodule ℤ E} {S : Submodule ℝ E} {x : E} :
    x ∈ quotLattice ℒ S ↔ ∃ y ∈ ℒ, Sᗮ.starProjection y = x := by
  constructor
  · intro hx
    rcases (Submodule.mem_map.mp hx) with ⟨y, hy, hxy⟩
    exact ⟨y, hy, hxy⟩
  · rintro ⟨y, hy, hxy⟩
    exact Submodule.mem_map.mpr ⟨y, hy, hxy⟩

/-- The projection map from `ℒ` to the quotient lattice (as a map between types). -/
def quotMap (ℒ : Submodule ℤ E) (S : Submodule ℝ E) : ℒ → quotLattice ℒ S :=
  fun y => ⟨Sᗮ.starProjection (y : E), by
    rw [mem_quotLattice]
    exact ⟨y, y.2, rfl⟩⟩

/-- `quotMap` is surjective (by construction). -/
lemma quotMap_surjective (ℒ : Submodule ℤ E) (S : Submodule ℝ E) :
    Function.Surjective (quotMap ℒ S) := by
  intro q
  rcases (mem_quotLattice.mp q.2) with ⟨y, hy, hq⟩
  exact ⟨⟨y, hy⟩, Subtype.ext hq⟩

/-- Ambient-primitive sublattice: `ℒ' = ℒ ∩ spanℝ(ℒ')`. -/
def Primitive (ℒ' ℒ : Submodule ℤ E) : Prop :=
  ∀ x : E, x ∈ ℒ' ↔ x ∈ ℒ ∧ x ∈ realSpan ℒ'

/-- A primitive sublattice is a sublattice. -/
lemma Primitive.le {ℒ' ℒ : Submodule ℤ E} (h : Primitive ℒ' ℒ) : ℒ' ≤ ℒ := by
  intro x hx
  exact (h x).mp hx |>.1

/-- For an ambient-primitive `ℒ' ⊆ ℒ` with `S = span ℒ'`, the kernel of the projection
`ℒ → quotLattice ℒ S` is exactly `ℒ'`. -/
lemma ker_quotMap (ℒ' ℒ : Submodule ℤ E) (S : Submodule ℝ E) (hS : S = realSpan ℒ')
    (hp : Primitive ℒ' ℒ) :
    ∀ x : E, x ∈ ℒ ∧ Sᗮ.starProjection x = 0 ↔ x ∈ ℒ' := by
  intro x
  constructor
  · rintro ⟨hxL, hx0⟩
    have hxy : S.starProjection x = x := by
      rw [proj_orth_comp S x] at hx0
      exact (sub_eq_zero.mp hx0).symm
    have hxS0 : x ∈ S := by simpa [hxy] using (Submodule.starProjection_apply_mem S x)
    have hxS : x ∈ realSpan ℒ' := by simpa [hS] using hxS0
    exact (hp x).mpr ⟨hxL, hxS⟩
  · intro hx
    constructor
    · exact Primitive.le hp hx
    · exact starProjection_orthogonal_eq_zero_of_mem S
        (by simpa [hS] using mem_realSpan (ℒ := ℒ') hx)


/-- The Gaussian mass `ρ_s(ℒ)` as an ambient-norm sum (equals `ReverseMinkowski.ρ`). -/
def mass (s : ℝ) (ℒ : Submodule ℤ E) : ℝ :=
  ∑' y : ℒ, rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2)

/-- Multiplication by `α` as a real-linear map. -/
def smulMap (α : ℝ) : E →ₗ[ℝ] E where
  toFun := fun x => α • x
  map_add' := by intro x y; simp [smul_add]
  map_smul' := by intro r x; simp [smul_smul, mul_comm]

/-- The lattice `α • ℒ := {α•x | x ∈ ℒ}` (as a `ℤ`-submodule of `E`). -/
def smulLattice (α : ℝ) (ℒ : Submodule ℤ E) : Submodule ℤ E :=
  ℒ.map ((smulMap α).restrictScalars ℤ)

lemma mem_smulLattice {α : ℝ} {ℒ : Submodule ℤ E} {z : E} :
    z ∈ smulLattice α ℒ ↔ ∃ y ∈ ℒ, α • (y : E) = z := by
  constructor
  · intro hz
    rcases (Submodule.mem_map.mp hz) with ⟨y, hy, hz'⟩
    exact ⟨y, hy, hz'⟩
  · rintro ⟨y, hy, hz'⟩
    exact Submodule.mem_map.mpr ⟨y, hy, hz'⟩

/-- For `α ≠ 0`, scaling is a bijection between `ℒ` and `α•ℒ`. -/
def smulEquiv (α : ℝ) (ℒ : Submodule ℤ E) (hα : α ≠ 0) : ℒ ≃ smulLattice α ℒ where
  toFun := fun y => ⟨α • (y : E), by
    rw [mem_smulLattice]
    exact ⟨y, y.2, rfl⟩⟩
  invFun := fun z => ⟨(α⁻¹ : ℝ) • (z : E), by
    classical
    rcases (mem_smulLattice.mp z.2) with ⟨y0, hy0, hz0⟩
    have hz1 : (α⁻¹ : ℝ) • (z : E) = (y0 : E) := by
      rw [← hz0]
      rw [smul_smul]
      rw [inv_mul_cancel₀ hα, one_smul]
    exact by simpa [hz1] using hy0⟩
  left_inv := by
    intro y
    apply Subtype.ext
    dsimp
    rw [smul_smul]
    rw [inv_mul_cancel₀ hα, one_smul]
  right_inv := by
    intro z
    apply Subtype.ext
    dsimp
    rw [smul_smul]
    rw [mul_inv_cancel₀ hα, one_smul]

/-- The Gaussian sum over `ℒ` is summable. -/
lemma summable_mass (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] (s : ℝ) (hs : 0 < s) :
    Summable (fun y : ℒ => rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2)) := by
  have hc : 0 < Real.pi / s ^ 2 := by positivity
  have h' : Summable (fun y : ℒ => rexp (-(Real.pi / s ^ 2) * ‖(y : E)‖ ^ 2)) :=
    Commons.Lattice.Summable.summable_exp_neg_mul_norm_sq (c := Real.pi / s ^ 2) hc
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h'

/-- **Scaling a lattice down increases its Gaussian mass**: for `0 < α ≤ 1`,
`ρ_s(ℒ) ≤ ρ_s(α•ℒ)`. -/
lemma mass_le_of_smul {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (s : ℝ) (hs : 0 < s) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) :
    mass s ℒ ≤ mass s (smulLattice α ℒ) := by
  classical
  let e : ℒ ≃ smulLattice α ℒ := smulEquiv α ℒ (ne_of_gt hα0)
  let f : ℒ → ℝ := fun y => rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2)
  let g : ℒ → ℝ := fun y => rexp (-Real.pi * ‖α • (y : E)‖ ^ 2 / s ^ 2)
  have hg_mass : mass s (smulLattice α ℒ) = ∑' y : ℒ, g y := by
    dsimp [mass, g]
    calc
      (∑' z : smulLattice α ℒ, rexp (-Real.pi * ‖(z : E)‖ ^ 2 / s ^ 2))
          = ∑' y : ℒ, rexp (-Real.pi * ‖((e y : smulLattice α ℒ) : E)‖ ^ 2 / s ^ 2) := by
            exact (Equiv.tsum_eq e (fun z : smulLattice α ℒ => rexp (-Real.pi * ‖(z : E)‖ ^ 2 / s ^ 2))).symm
      _ = ∑' y : ℒ, rexp (-Real.pi * ‖α • (y : E)‖ ^ 2 / s ^ 2) := by
        apply tsum_congr
        intro y
        congr 1
  have hpt : ∀ y : ℒ, f y ≤ g y := by
    intro y
    dsimp [f, g]
    apply Real.exp_le_exp.mpr
    have hnorm : ‖α • (y : E)‖ ^ 2 ≤ ‖(y : E)‖ ^ 2 := by
      have hnm : ‖α • (y : E)‖ = α * ‖(y : E)‖ := by
        rw [norm_smul]
        rw [Real.norm_eq_abs, abs_of_nonneg hα0.le]
      rw [hnm]
      have hb0 : 0 ≤ ‖(y : E)‖ := norm_nonneg _
      have hmul : α * ‖(y : E)‖ ≤ ‖(y : E)‖ := by
        simpa using (mul_le_of_le_one_left hb0 hα1)
      exact pow_le_pow_left₀ (mul_nonneg hα0.le hb0) hmul 2
    have hpm : Real.pi * ‖α • (y : E)‖ ^ 2 ≤ Real.pi * ‖(y : E)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hnorm (le_of_lt Real.pi_pos)
    have hneg : -Real.pi * ‖(y : E)‖ ^ 2 ≤ -Real.pi * ‖α • (y : E)‖ ^ 2 := by
      simpa [mul_neg, neg_mul] using (neg_le_neg hpm)
    exact div_le_div_of_nonneg_right hneg (sq_nonneg s)
  have hsm_f : Summable f := by
    dsimp [f]
    exact summable_mass ℒ s hs
  have hsm_g : Summable g := by
    have hc : 0 < Real.pi * α ^ 2 / s ^ 2 := by positivity
    have h' : Summable (fun y : ℒ => rexp (-(Real.pi * α ^ 2 / s ^ 2) * ‖(y : E)‖ ^ 2)) :=
      Commons.Lattice.Summable.summable_exp_neg_mul_norm_sq (c := Real.pi * α ^ 2 / s ^ 2) hc
    have hg' : g = (fun y : ℒ => rexp (-(Real.pi * α ^ 2 / s ^ 2) * ‖(y : E)‖ ^ 2)) := by
      funext y
      dsimp [g]
      congr 1
      have hnm : ‖α • (y : E)‖ ^ 2 = α ^ 2 * ‖(y : E)‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hα0.le]
        ring
      rw [hnm]
      field_simp [ne_of_gt hs]
    rw [hg']
    exact h'
  have hsum_le : (∑' y : ℒ, f y) ≤ ∑' y : ℒ, g y := Summable.tsum_le_tsum hpt hsm_f hsm_g
  calc
    mass s ℒ = ∑' y : ℒ, f y := by rfl
    _ ≤ ∑' y : ℒ, g y := hsum_le
    _ = mass s (smulLattice α ℒ) := hg_mass.symm


/-- **Gaussian mass is monotone under a norm-decreasing bijection**: if `e : ℒ ≃ ℒ₂` and
`‖(e y : E)‖ ≤ ‖(y : E)‖` for all `y : ℒ`, then `ρ_s(ℒ) ≤ ρ_s(ℒ₂)`. -/
lemma mass_le_of_norm_decreasing {ℒ ℒ₂ : Submodule ℤ E} [DiscreteTopology ℒ]
    [DiscreteTopology ℒ₂] (s : ℝ) (hs : 0 < s) (e : ℒ ≃ ℒ₂)
    (hnorm : ∀ y : ℒ, ‖((e y : ℒ₂) : E)‖ ≤ ‖(y : E)‖) :
    mass s ℒ ≤ mass s ℒ₂ := by
  classical
  let f : ℒ → ℝ := fun y => rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2)
  let g : ℒ → ℝ := fun y => rexp (-Real.pi * ‖((e y : ℒ₂) : E)‖ ^ 2 / s ^ 2)
  have hg_mass : mass s ℒ₂ = ∑' y : ℒ, g y := by
    dsimp [mass, g]
    exact (Equiv.tsum_eq e (fun z : ℒ₂ => rexp (-Real.pi * ‖(z : E)‖ ^ 2 / s ^ 2))).symm
  have hpt : ∀ y : ℒ, f y ≤ g y := by
    intro y
    dsimp [f, g]
    apply Real.exp_le_exp.mpr
    -- -π‖y‖²/s² ≤ -π‖ey‖²/s² : from ‖ey‖ ≤ ‖y‖
    have hsq : ‖((e y : ℒ₂) : E)‖ ^ 2 ≤ ‖(y : E)‖ ^ 2 := by
      nlinarith [hnorm y, norm_nonneg ((e y : ℒ₂) : E), norm_nonneg (y : E)]
    have hpm : Real.pi * ‖((e y : ℒ₂) : E)‖ ^ 2 ≤ Real.pi * ‖(y : E)‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (le_of_lt Real.pi_pos)
    have hneg : -Real.pi * ‖(y : E)‖ ^ 2 ≤ -Real.pi * ‖((e y : ℒ₂) : E)‖ ^ 2 := by
      simpa [mul_neg, neg_mul] using (neg_le_neg hpm)
    exact div_le_div_of_nonneg_right hneg (sq_nonneg s)
  have hsm_f : Summable f := by
    dsimp [f]
    exact summable_mass ℒ s hs
  have hsm_g : Summable g := by
    dsimp [g]
    -- g y = exp(-c ‖ey‖²) with ey ranging...; use reindexed summability over ℒ₂
    have hsm2 : Summable (fun z : ℒ₂ => rexp (-Real.pi * ‖(z : E)‖ ^ 2 / s ^ 2)) :=
      summable_mass ℒ₂ s hs
    -- pull back through the equivalence
    have hpb : Summable (fun y : ℒ => rexp (-Real.pi * ‖((e y : ℒ₂) : E)‖ ^ 2 / s ^ 2)) := by
      exact (Equiv.summable_iff
        (f := fun z : ℒ₂ => rexp (-Real.pi * ‖(z : E)‖ ^ 2 / s ^ 2)) e).mpr hsm2
    simpa [g] using hpb
  have hsum_le : (∑' y : ℒ, f y) ≤ ∑' y : ℒ, g y := Summable.tsum_le_tsum hpt hsm_f hsm_g
  calc
    mass s ℒ = ∑' y : ℒ, f y := by rfl
    _ ≤ ∑' y : ℒ, g y := hsum_le
    _ = mass s ℒ₂ := hg_mass.symm

/-- The quotient map `ℒ → quotLattice ℒ S` as an additive group homomorphism. -/
def quotHom (ℒ : Submodule ℤ E) (S : Submodule ℝ E) : ℒ →+ quotLattice ℒ S where
  toFun := quotMap ℒ S
  map_zero' := by
    apply Subtype.ext
    simp [quotMap]
  map_add' := by
    intro x y
    apply Subtype.ext
    dsimp [quotMap]
    simpa using (map_add (Sᗮ.starProjection : E →ₗ[ℝ] E) (x : E) (y : E))

/-- The kernel of the quotient homomorphism is `ℒ'` (for primitive `ℒ'`). -/
lemma ker_quotHom {ℒ' ℒ : Submodule ℤ E} (S : Submodule ℝ E) (hS : S = realSpan ℒ')
    (hp : Primitive ℒ' ℒ) : ∀ y : ℒ, quotMap ℒ S y = 0 ↔ (y : E) ∈ ℒ' := by
  intro y
  constructor
  · intro h0
    have hv : Sᗮ.starProjection (y : E) = 0 := by
      have hval := congrArg (fun z : quotLattice ℒ S => (z : E)) h0
      simpa [quotMap] using hval
    exact (ker_quotMap ℒ' ℒ S hS hp (y : E)).mp ⟨y.2, hv⟩
  · intro hy
    apply Subtype.ext
    change Sᗮ.starProjection ((y : ℒ) : E) = (0 : E)
    exact starProjection_orthogonal_eq_zero_of_mem S (by simpa [hS] using mem_realSpan (ℒ := ℒ') hy)

/-- A choice of representatives: a section of `quotMap`. -/
noncomputable def sect (ℒ : Submodule ℤ E) (S : Submodule ℝ E) : quotLattice ℒ S → ℒ :=
  fun v => Classical.choose (quotMap_surjective ℒ S v)

/-- The section satisfies `quotMap (sect v) = v`. -/
lemma sect_spec (ℒ : Submodule ℤ E) (S : Submodule ℝ E) (v : quotLattice ℒ S) :
    quotMap ℒ S (sect ℒ S v) = v :=
  Classical.choose_spec (quotMap_surjective ℒ S v)

/-- value-level: the projection of the section is the section value. -/
lemma sect_proj (ℒ : Submodule ℤ E) (S : Submodule ℝ E) (v : quotLattice ℒ S) :
    Sᗮ.starProjection ((sect ℒ S v : ℒ) : E) = (v : E) := by
  have hval := congrArg (fun z : quotLattice ℒ S => (z : E)) (sect_spec ℒ S v)
  simpa [quotMap] using hval

/-- value-level: elements of `ℒ'` project to zero (primitivity + membership in span). -/
lemma prim_proj_zero {ℒ' ℒ : Submodule ℤ E} (S : Submodule ℝ E) (hS : S = realSpan ℒ')
    (_hp : Primitive ℒ' ℒ) (x : ℒ') : Sᗮ.starProjection ((x : ℒ') : E) = 0 := by
  exact starProjection_orthogonal_eq_zero_of_mem S
    (by simpa [hS] using mem_realSpan (ℒ := ℒ') x.2)

/-- For primitive `ℒ' ⊆ ℒ`, `quotMap` sends the sum `sect v + x` (with `x ∈ ℒ'`) to `v`. -/
lemma quotMap_add_prim {ℒ' ℒ : Submodule ℤ E} (S : Submodule ℝ E) (hS : S = realSpan ℒ')
    (hp : Primitive ℒ' ℒ) (v : quotLattice ℒ S) (x : ℒ') :
    quotMap ℒ S (⟨(sect ℒ S v : E) + (x : E), by
      exact Submodule.add_mem _ (sect ℒ S v).2 (Primitive.le hp x.2)⟩) = v := by
  apply Subtype.ext
  dsimp [quotMap]
  calc
    Sᗮ.starProjection (((sect ℒ S v : ℒ) : E) + ((x : ℒ') : E))
        = Sᗮ.starProjection ((sect ℒ S v : ℒ) : E) + Sᗮ.starProjection ((x : ℒ') : E) := by
          rw [map_add]
    _ = (v : E) := by rw [sect_proj ℒ S v, prim_proj_zero S hS hp x]; simp

/-- For `y : ℒ`, `y − sect (quotMap y)` has value-level projection zero and lies in `ℒ'`. -/
lemma sub_sect_mem_prim {ℒ' ℒ : Submodule ℤ E} (S : Submodule ℝ E) (hS : S = realSpan ℒ')
    (hp : Primitive ℒ' ℒ) (y : ℒ) :
    (y : E) - (sect ℒ S (quotMap ℒ S y) : E) ∈ ℒ' := by
  let sy : ℒ := sect ℒ S (quotMap ℒ S y)
  have hsub : (y : E) - (sy : E) ∈ ℒ := by
    exact Submodule.sub_mem _ y.2 sy.2
  have hproj : Sᗮ.starProjection ((y : E) - (sy : E)) = 0 := by
    rw [map_sub]
    have hsy : Sᗮ.starProjection ((sect ℒ S (quotMap ℒ S y) : ℒ) : E) =
        Sᗮ.starProjection ((y : ℒ) : E) := by
      have hv := congrArg (fun z : quotLattice ℒ S => (z : E)) (sect_spec ℒ S (quotMap ℒ S y))
      simpa [quotMap] using hv
    rw [hsy]
    abel
  exact (ker_quotMap ℒ' ℒ S hS hp ((y : E) - (sy : E))).mp ⟨hsub, hproj⟩

/-- Forward map of the coset bijection: `(y', v) ↦ y' + sect v ∈ ℒ`. -/
noncomputable def cosetTo {ℒ' ℒ : Submodule ℤ E} (S : Submodule ℝ E) (_hS : S = realSpan ℒ')
    (hp : Primitive ℒ' ℒ) : (ℒ' × quotLattice ℒ S) → ℒ :=
  fun p => ⟨(sect ℒ S p.2 : E) + (p.1 : E), by
    exact Submodule.add_mem _ (sect ℒ S p.2).2 (Primitive.le hp p.1.2)⟩

/-- Inverse map of the coset bijection: `y ↦ (y − sect (quotMap y), quotMap y)`. -/
noncomputable def cosetInv {ℒ' ℒ : Submodule ℤ E} (S : Submodule ℝ E) (hS : S = realSpan ℒ')
    (hp : Primitive ℒ' ℒ) : ℒ → (ℒ' × quotLattice ℒ S) :=
  fun y => ⟨⟨(y : E) - (sect ℒ S (quotMap ℒ S y) : E), sub_sect_mem_prim S hS hp y⟩,
    quotMap ℒ S y⟩

lemma coset_left_inv {ℒ' ℒ : Submodule ℤ E} (S : Submodule ℝ E) (hS : S = realSpan ℒ')
    (hp : Primitive ℒ' ℒ) (p : ℒ' × quotLattice ℒ S) :
    cosetInv S hS hp (cosetTo S hS hp p) = p := by
  apply Prod.ext
  · apply Subtype.ext
    dsimp [cosetInv, cosetTo]
    rw [quotMap_add_prim S hS hp p.2 p.1]
    abel
  · apply Subtype.ext
    dsimp [cosetInv, cosetTo]
    exact congrArg (fun z : quotLattice ℒ S => (z : E)) (quotMap_add_prim S hS hp p.2 p.1)

lemma coset_right_inv {ℒ' ℒ : Submodule ℤ E} (S : Submodule ℝ E) (hS : S = realSpan ℒ')
    (hp : Primitive ℒ' ℒ) (y : ℒ) :
    cosetTo S hS hp (cosetInv S hS hp y) = y := by
  apply Subtype.ext
  dsimp [cosetInv, cosetTo]
  abel

/-- The `ℒ'`-coset decomposition of `ℒ` over the quotient `Q = quotLattice ℒ S`:
`(y', v) ↦ y' + s(v)` is a bijection `ℒ' × Q ≃ ℒ` for primitive `ℒ'`. -/
noncomputable def cosetEquiv {ℒ' ℒ : Submodule ℤ E} (S : Submodule ℝ E) (hS : S = realSpan ℒ')
    (hp : Primitive ℒ' ℒ) : (ℒ' × quotLattice ℒ S) ≃ ℒ where
  toFun := cosetTo S hS hp
  invFun := cosetInv S hS hp
  left_inv := coset_left_inv S hS hp
  right_inv := coset_right_inv S hS hp



/-- A linear isometry between inner-product spaces induces a type equivalence between a
`ℤ`-submodule and its image. -/
noncomputable def isoLatticeEquiv {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
    [InnerProductSpace ℝ E₁] [InnerProductSpace ℝ E₂] (F : E₁ ≃ₗᵢ[ℝ] E₂)
    (ℒ : Submodule ℤ E₁) : ℒ ≃ ℒ.map ((F.toLinearEquiv : E₁ →ₗ[ℝ] E₂).restrictScalars ℤ) where
  toFun := fun y => ⟨F (y : E₁), by
    exact Submodule.mem_map.mpr ⟨y, y.2, rfl⟩⟩
  invFun := fun z => ⟨F.symm (z : E₂), by
    classical
    rcases (Submodule.mem_map.mp z.2) with ⟨y, hy, hz⟩
    have hFz : F.symm (z : E₂) = y := by
      rw [← hz]
      simp
    exact by simpa [hFz] using hy⟩
  left_inv := by
    intro y
    apply Subtype.ext
    simp
  right_inv := by
    intro z
    apply Subtype.ext
    simp

/-- **Isometric transport of Gaussian lattice sums**: for a linear isometry `F : E₁ ≃ₗᵢ E₂`,
the Gaussian sum over `ℒ ≤ E₁` equals the Gaussian sum over its image `F(ℒ) ≤ E₂`. -/
lemma gaussian_tsum_iso {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
    [InnerProductSpace ℝ E₁] [InnerProductSpace ℝ E₂] (F : E₁ ≃ₗᵢ[ℝ] E₂) (s : ℝ)
    (ℒ : Submodule ℤ E₁) :
    (∑' y : ℒ, rexp (-Real.pi * ‖(y : E₁)‖ ^ 2 / s ^ 2)) =
      (∑' z : ℒ.map ((F.toLinearEquiv : E₁ →ₗ[ℝ] E₂).restrictScalars ℤ),
        rexp (-Real.pi * ‖(z : E₂)‖ ^ 2 / s ^ 2)) := by
  classical
  let e : ℒ ≃ ℒ.map ((F.toLinearEquiv : E₁ →ₗ[ℝ] E₂).restrictScalars ℤ) := isoLatticeEquiv F ℒ
  have hn : ∀ y : ℒ, ‖(((e y : ℒ.map ((F.toLinearEquiv : E₁ →ₗ[ℝ] E₂).restrictScalars ℤ)) : E₂))‖ =
      ‖(y : E₁)‖ := by
    intro y
    dsimp [e, isoLatticeEquiv]
    exact F.norm_map (y : E₁)
  have h1 : (∑' y : ℒ, rexp (-Real.pi * ‖(y : E₁)‖ ^ 2 / s ^ 2)) =
      ∑' y : ℒ, rexp (-Real.pi * ‖(((e y : ℒ.map ((F.toLinearEquiv : E₁ →ₗ[ℝ] E₂).restrictScalars ℤ)) : E₂))‖ ^ 2 / s ^ 2) := by
        apply tsum_congr
        intro y
        congr 1
        rw [hn y]
  calc
    (∑' y : ℒ, rexp (-Real.pi * ‖(y : E₁)‖ ^ 2 / s ^ 2))
        = ∑' y : ℒ, rexp (-Real.pi * ‖(((e y : ℒ.map ((F.toLinearEquiv : E₁ →ₗ[ℝ] E₂).restrictScalars ℤ)) : E₂))‖ ^ 2 / s ^ 2) := h1
    _ = (∑' z : ℒ.map ((F.toLinearEquiv : E₁ →ₗ[ℝ] E₂).restrictScalars ℤ),
        rexp (-Real.pi * ‖(z : E₂)‖ ^ 2 / s ^ 2)) := by
          exact Equiv.tsum_eq e (fun z : ℒ.map ((F.toLinearEquiv : E₁ →ₗ[ℝ] E₂).restrictScalars ℤ) =>
            rexp (-Real.pi * ‖(z : E₂)‖ ^ 2 / s ^ 2))




/-- Reindexing a sum over a lattice through an isometry. -/
lemma tsum_iso_reindex {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
    [InnerProductSpace ℝ E₁] [InnerProductSpace ℝ E₂] (F : E₁ ≃ₗᵢ[ℝ] E₂)
    (ℒ : Submodule ℤ E₁) (f : E₂ → ℝ) :
    (∑' y : ℒ, f (F (y : E₁))) =
      ∑' z : ℒ.map ((F.toLinearEquiv : E₁ →ₗ[ℝ] E₂).restrictScalars ℤ), f (z : E₂) := by
  classical
  let e : ℒ ≃ ℒ.map ((F.toLinearEquiv : E₁ →ₗ[ℝ] E₂).restrictScalars ℤ) := isoLatticeEquiv F ℒ
  calc
    (∑' y : ℒ, f (F (y : E₁))) = ∑' y : ℒ, f (((e y : ℒ.map ((F.toLinearEquiv : E₁ →ₗ[ℝ] E₂).restrictScalars ℤ)) : E₂)) := by
      apply tsum_congr
      intro y
      congr 1
    _ = ∑' z : ℒ.map ((F.toLinearEquiv : E₁ →ₗ[ℝ] E₂).restrictScalars ℤ), f (z : E₂) := by
      exact Equiv.tsum_eq e (fun z : ℒ.map ((F.toLinearEquiv : E₁ →ₗ[ℝ] E₂).restrictScalars ℤ) => f (z : E₂))

/-- **Isometric transport of shifted Gaussian lattice sums.** -/
lemma gaussian_tsum_iso_shift {E₁ E₂ : Type*} [NormedAddCommGroup E₁] [NormedAddCommGroup E₂]
    [InnerProductSpace ℝ E₁] [InnerProductSpace ℝ E₂] (F : E₁ ≃ₗᵢ[ℝ] E₂) (s : ℝ)
    (ℒ : Submodule ℤ E₁) (u : E₁) :
    (∑' y : ℒ, rexp (-Real.pi * ‖(y : E₁) - u‖ ^ 2 / s ^ 2)) =
      (∑' z : ℒ.map ((F.toLinearEquiv : E₁ →ₗ[ℝ] E₂).restrictScalars ℤ),
        rexp (-Real.pi * ‖(z : E₂) - F u‖ ^ 2 / s ^ 2)) := by
  classical
  have h1 : (∑' y : ℒ, rexp (-Real.pi * ‖(y : E₁) - u‖ ^ 2 / s ^ 2)) =
      ∑' y : ℒ, rexp (-Real.pi * ‖F ((y : E₁) - u)‖ ^ 2 / s ^ 2) := by
    apply tsum_congr
    intro y
    congr 1
    rw [F.norm_map]
  have h2 : (∑' y : ℒ, rexp (-Real.pi * ‖F ((y : E₁) - u)‖ ^ 2 / s ^ 2)) =
      ∑' y : ℒ, rexp (-Real.pi * ‖F (y : E₁) - F u‖ ^ 2 / s ^ 2) := by
    apply tsum_congr
    intro y
    congr 1
    rw [F.map_sub]
  calc
    (∑' y : ℒ, rexp (-Real.pi * ‖(y : E₁) - u‖ ^ 2 / s ^ 2))
        = ∑' y : ℒ, rexp (-Real.pi * ‖F (y : E₁) - F u‖ ^ 2 / s ^ 2) := by
          rw [h1, h2]
    _ = (∑' z : ℒ.map ((F.toLinearEquiv : E₁ →ₗ[ℝ] E₂).restrictScalars ℤ),
        rexp (-Real.pi * ‖(z : E₂) - F u‖ ^ 2 / s ^ 2)) := by
          exact tsum_iso_reindex F ℒ (fun w : E₂ => rexp (-Real.pi * ‖w - F u‖ ^ 2 / s ^ 2))



lemma shifted_inner_le {ℒ : Submodule ℤ E} [DiscreteTopology ℒ] (s : ℝ) (hs : 0 < s)
    (u : E) (hu : u ∈ realSpan ℒ) :
    (∑' y : ℒ, rexp (-Real.pi * ‖(y : E) - u‖ ^ 2 / s ^ 2)) ≤ mass s ℒ := by
  dsimp [mass]
  exact Commons.Lattice.PoissonSummation.lattice_shifted_mass_le_rank (ℒ := ℒ) s hs u
    (by simpa [realSpan] using hu)

/-- **direct_sum_rho** (paper Lemma 2.6-ish): for an ambient-primitive sublattice
`ℒ' ⊆ ℒ`, `ρ_s(ℒ) ≤ ρ_s(ℒ') · ρ_s(ℒ/ℒ')`, where the quotient is the orthogonal
projection `quotLattice ℒ (realSpan ℒ')`. -/
theorem mass_le_mul_quot {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (S : Submodule ℝ E) (hS : S = realSpan ℒ') (hp : Primitive ℒ' ℒ)
    [DiscreteTopology (quotLattice ℒ S)] (s : ℝ) (hs : 0 < s) :
    mass s ℒ ≤ mass s ℒ' * mass s (quotLattice ℒ S) := by
  classical
  let Q : Submodule ℤ E := quotLattice ℒ S
  haveI : DiscreteTopology Q := ‹DiscreteTopology (quotLattice ℒ S)›
  let e : (ℒ' × Q) ≃ ℒ := cosetEquiv S hS hp
  -- value of e p
  have hG : ∀ p : ℒ' × Q, (((e p : ℒ)) : E) = ((sect ℒ S p.2 : ℒ) : E) + ((p.1 : ℒ') : E) := by
    intro p
    dsimp [e, cosetEquiv, cosetTo]
  have hA : ∀ y' : ℒ', ((y' : ℒ') : E) ∈ S := by
    intro y'
    rw [hS]
    exact mem_realSpan (ℒ := ℒ') y'.2
  have hB : ∀ v : Q, ((v : Q) : E) ∈ Sᗮ := by
    intro v
    exact (quotLattice_le_orthogonal ℒ S) v.2
  have hsec : ∀ v : Q, ((sect ℒ S v : ℒ) : E) =
      S.starProjection ((sect ℒ S v : ℒ) : E) + ((v : Q) : E) := by
    intro v
    calc
      ((sect ℒ S v : ℒ) : E) = S.starProjection ((sect ℒ S v : ℒ) : E) +
          Sᗮ.starProjection ((sect ℒ S v : ℒ) : E) :=
            (proj_decomp S ((sect ℒ S v : ℒ) : E))
      _ = S.starProjection ((sect ℒ S v : ℒ) : E) + ((v : Q) : E) := by
        rw [sect_proj ℒ S v]
  have hnorm : ∀ p : ℒ' × Q, ‖(((e p : ℒ)) : E)‖ ^ 2 =
      ‖S.starProjection ((sect ℒ S p.2 : ℒ) : E) + ((p.1 : ℒ') : E)‖ ^ 2 +
        ‖(((p.2 : Q)) : E)‖ ^ 2 := by
    intro p
    have hval : (((e p : ℒ)) : E) = ((sect ℒ S p.2 : ℒ) : E) + ((p.1 : ℒ') : E) := hG p
    have hsec' : ((sect ℒ S p.2 : ℒ) : E) =
        S.starProjection ((sect ℒ S p.2 : ℒ) : E) + ((p.2 : Q) : E) := hsec p.2
    have hdecomp : ((sect ℒ S p.2 : ℒ) : E) + ((p.1 : ℒ') : E) =
        (S.starProjection ((sect ℒ S p.2 : ℒ) : E) + ((p.1 : ℒ') : E)) + ((p.2 : Q) : E) := by
      conv_lhs => rw [hsec']
      abel
    calc
      ‖(((e p : ℒ)) : E)‖ ^ 2 = ‖(((sect ℒ S p.2 : ℒ) : E) + ((p.1 : ℒ') : E))‖ ^ 2 := by rw [hval]
      _ = ‖(S.starProjection ((sect ℒ S p.2 : ℒ) : E) + ((p.1 : ℒ') : E)) + ((p.2 : Q) : E)‖ ^ 2 := by
        rw [hdecomp]
      _ = ‖S.starProjection ((sect ℒ S p.2 : ℒ) : E) + ((p.1 : ℒ') : E)‖ ^ 2 +
          ‖(((p.2 : Q)) : E)‖ ^ 2 := norm_sq_orthogonal_add S
            (Submodule.add_mem _ (Submodule.starProjection_apply_mem S ((sect ℒ S p.2 : ℒ) : E)) (hA p.1))
            (hB p.2)
  have hterm : ∀ p : ℒ' × Q,
      rexp (-Real.pi * ‖(((e p : ℒ)) : E)‖ ^ 2 / s ^ 2) =
        (rexp (-Real.pi * ‖S.starProjection ((sect ℒ S p.2 : ℒ) : E) + ((p.1 : ℒ') : E)‖ ^ 2 / s ^ 2)) *
          rexp (-Real.pi * ‖(((p.2 : Q)) : E)‖ ^ 2 / s ^ 2) := by
    intro p
    rw [hnorm p]
    rw [← Real.exp_add]
    congr 1
    ring
  let A : Q → ℒ' → ℝ := fun v y' =>
    rexp (-Real.pi * ‖S.starProjection ((sect ℒ S v : ℒ) : E) + ((y' : ℒ') : E)‖ ^ 2 / s ^ 2)
  let B : Q → ℝ := fun v => rexp (-Real.pi * ‖(((v : Q)) : E)‖ ^ 2 / s ^ 2)
  let F : ℒ' × Q → ℝ := fun p => rexp (-Real.pi * ‖(((e p : ℒ)) : E)‖ ^ 2 / s ^ 2)
  let F2 : ℒ' × Q → ℝ := fun p => (A p.2) (p.1) * B p.2
  have hF_eq : F = F2 := by
    funext p
    dsimp [F, F2]
    exact hterm p
  have hsmF : Summable F := by
    have hiff := Equiv.summable_iff (e := e)
      (f := fun y : ℒ => rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2))
    exact hiff.mpr (summable_mass ℒ s hs)
  have hsmF2 : Summable F2 := by
    rw [← hF_eq]
    exact hsmF
  -- inner shifted-mass bound
  have hinner : ∀ v : Q, (∑' y' : ℒ', A v y') ≤ mass s ℒ' := by
    intro v
    let xv : E := S.starProjection ((sect ℒ S v : ℒ) : E)
    have hxv : xv ∈ realSpan ℒ' := by
      dsimp [xv]
      rw [← hS]
      exact Submodule.starProjection_apply_mem S ((sect ℒ S v : ℒ) : E)
    have hle := shifted_inner_le (ℒ := ℒ') s hs (-xv) (Submodule.neg_mem _ hxv)
    dsimp [A]
    simpa [xv, add_comm] using hle
  -- now iterate: Σ' over v of inner sums
  have hsmB : Summable B := by
    dsimp [B]
    exact summable_mass Q s hs
  have hsmh : Summable (fun v : Q => mass s ℒ' * B v) := (hsmB.mul_left (mass s ℒ'))
  have hpt : ∀ v : Q, (∑' y' : ℒ', F2 (y', v)) ≤ mass s ℒ' * B v := by
    intro v
    have hB0 : 0 ≤ B v := by dsimp [B]; positivity
    have hle := hinner v
    calc
      (∑' y' : ℒ', F2 (y', v)) = (∑' y' : ℒ', A v y') * B v := by
        dsimp [F2]
        rw [tsum_mul_right]
      _ ≤ mass s ℒ' * B v := by
        exact mul_le_mul_of_nonneg_right hle hB0
  have hg_nonneg : ∀ v : Q, 0 ≤ ∑' y' : ℒ', F2 (y', v) := by
    intro v
    exact tsum_nonneg (fun y' => by dsimp [F2, A, B]; positivity)
  have hsmg : Summable (fun v : Q => ∑' y' : ℒ', F2 (y', v)) :=
    Summable.of_nonneg_of_le hg_nonneg hpt hsmh
  -- main chain
  calc
    mass s ℒ = ∑' p : ℒ' × Q, F p := by
      dsimp [mass, F]
      rw [← Equiv.tsum_eq e (fun y : ℒ => rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2))]
    _ = ∑' p : ℒ' × Q, F2 p := by rw [hF_eq]
    _ = ∑' v : Q, ∑' y' : ℒ', F2 (y', v) := by
      -- swap product order then Fubini
      let sw : Q × ℒ' ≃ ℒ' × Q := Equiv.prodComm Q ℒ'
      have hswap : (∑' q : Q × ℒ', F2 (sw q)) = ∑' p : ℒ' × Q, F2 p := by
        exact Equiv.tsum_eq sw F2
      have hsmsw : Summable (fun q : Q × ℒ' => F2 (sw q)) := by
        exact (Equiv.summable_iff (e := sw) (f := F2)).mpr hsmF2
      calc
        (∑' p : ℒ' × Q, F2 p) = ∑' q : Q × ℒ', F2 (sw q) := hswap.symm
        _ = ∑' v : Q, ∑' y' : ℒ', F2 (sw (v, y')) := by
          exact Summable.tsum_prod hsmsw
        _ = ∑' v : Q, ∑' y' : ℒ', F2 (y', v) := by
          apply tsum_congr
          intro v
          apply tsum_congr
          intro y'
          rfl
    _ ≤ ∑' v : Q, mass s ℒ' * B v := Summable.tsum_le_tsum hpt hsmg hsmh
    _ = mass s ℒ' * ∑' v : Q, B v := by
      rw [tsum_mul_left]
    _ = mass s ℒ' * mass s (quotLattice ℒ S) := by rfl

/-- two submodules are elementwise orthogonal -/
def OrthogonalPair (W₁ W₂ : Submodule ℤ E) : Prop :=
  ∀ x : E, x ∈ W₁ → ∀ y : E, y ∈ W₂ → ⟪x, y⟫_ℝ = 0

/-- disjoint (only common element is 0) -/
def DisjointPair (W₁ W₂ : Submodule ℤ E) : Prop :=
  ∀ x : E, x ∈ W₁ → x ∈ W₂ → x = 0

/-- elementwise-orthogonal submodules are disjoint (nondegenerate inner product). -/
lemma disjoint_of_orthogonal {W₁ W₂ : Submodule ℤ E} (hop : OrthogonalPair W₁ W₂) :
    DisjointPair W₁ W₂ := by
  intro x hx1 hx2
  have hxx : ⟪x, x⟫_ℝ = 0 := hop x hx1 x hx2
  have hsq : ‖x‖ ^ 2 = 0 := by
    have := (real_inner_self_eq_norm_sq x)
    nlinarith
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)

/-- the internal sum `W₁ ⊔ W₂`, as a definition (so it can be used as a type). -/
noncomputable def supMod (W₁ W₂ : Submodule ℤ E) : Submodule ℤ E := W₁ ⊔ W₂

/-- addition map (x,y) ↦ x + y to the internal sum -/
noncomputable def sumTo (W₁ W₂ : Submodule ℤ E) : (W₁ × W₂) → ↥(supMod W₁ W₂) :=
  fun p => ⟨(p.1 : E) + (p.2 : E), by
    exact Submodule.mem_sup.mpr ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩⟩

/-- every element of the internal sum has a representation -/
lemma sumTo_surj (W₁ W₂ : Submodule ℤ E) (z : ↥(supMod W₁ W₂)) :
    ∃ p : W₁ × W₂, (p.1 : E) + (p.2 : E) = (z : E) := by
  have hz := (Submodule.mem_sup.mp (by simpa [supMod] using z.2))
  rcases hz with ⟨x₁, hx₁, y₁, hy₁, hz'⟩
  exact ⟨⟨⟨x₁, hx₁⟩, ⟨y₁, hy₁⟩⟩, hz'⟩

/-- injectivity of addition on the ambient values for disjoint summands -/
lemma supAdd_injE {W₁ W₂ : Submodule ℤ E} (hd : DisjointPair W₁ W₂) :
    ∀ {x₁ y₁ x₂ y₂ : E}, x₁ ∈ W₁ → y₁ ∈ W₂ → x₂ ∈ W₁ → y₂ ∈ W₂ →
      x₁ + y₁ = x₂ + y₂ → x₁ = x₂ ∧ y₁ = y₂ := by
  intro x₁ y₁ x₂ y₂ hx₁ hy₁ hx₂ hy₂ h
  have hz : (x₁ + y₁) - (x₂ + y₂) = 0 := by rw [h]; abel
  have hid : (x₁ - x₂) - (y₂ - y₁) = (x₁ + y₁) - (x₂ + y₂) := by abel
  have hsub : x₁ - x₂ = y₂ - y₁ := by
    have hz' : (x₁ - x₂) - (y₂ - y₁) = 0 := by rw [hid, hz]
    exact sub_eq_zero.mp hz'
  have hzero : x₁ - x₂ = 0 := hd (x₁ - x₂) (Submodule.sub_mem _ hx₁ hx₂) (by
    rw [hsub]
    exact Submodule.sub_mem _ hy₂ hy₁)
  have hx : x₁ = x₂ := sub_eq_zero.mp hzero
  have hy : y₁ = y₂ := by
    have hz2 : y₂ - y₁ = 0 := by rw [← hsub, hzero]
    apply sub_eq_zero.mp
    have : y₁ - y₂ = -(y₂ - y₁) := by abel
    rw [this, hz2, neg_zero]
  exact ⟨hx, hy⟩

/-- for disjoint summands the addition map is injective -/
lemma sumTo_inj {W₁ W₂ : Submodule ℤ E} (hd : DisjointPair W₁ W₂) :
    Function.Injective (sumTo W₁ W₂) := by
  intro p q h
  have hval := congrArg (fun z : ↥(supMod W₁ W₂) => (z : E)) h
  have hv : (p.1 : E) + (p.2 : E) = (q.1 : E) + (q.2 : E) := by simpa [sumTo] using hval
  rcases (supAdd_injE hd p.1.2 p.2.2 q.1.2 q.2.2 hv) with ⟨hx, hy⟩
  apply Prod.ext
  · apply Subtype.ext
    exact hx
  · apply Subtype.ext
    exact hy

/-- for disjoint summands, the addition map is a bijection. -/
noncomputable def sumEquiv (W₁ W₂ : Submodule ℤ E) (hd : DisjointPair W₁ W₂) :
    (W₁ × W₂) ≃ ↥(supMod W₁ W₂) where
  toFun := sumTo W₁ W₂
  invFun := fun z => Classical.choose (sumTo_surj W₁ W₂ z)
  left_inv := by
    intro p
    apply sumTo_inj hd
    apply Subtype.ext
    simpa [sumTo] using (Classical.choose_spec (sumTo_surj W₁ W₂ (sumTo W₁ W₂ p)))
  right_inv := by
    intro z
    apply Subtype.ext
    simpa [sumTo] using (Classical.choose_spec (sumTo_surj W₁ W₂ z))

/-- Pythagoras for two orthogonal lattice elements in the ambient space. -/
lemma norm_sq_orthogonal_ambient {W₁ W₂ : Submodule ℤ E} (hop : OrthogonalPair W₁ W₂)
    (p : W₁ × W₂) : ‖((sumTo W₁ W₂ p : ↥(supMod W₁ W₂)) : E)‖ ^ 2 =
      ‖(p.1 : E)‖ ^ 2 + ‖(p.2 : E)‖ ^ 2 := by
  have horth : ⟪(p.1 : E), (p.2 : E)⟫_ℝ = 0 := hop (p.1 : E) p.1.2 (p.2 : E) p.2.2
  dsimp [sumTo]
  simpa [horth] using (norm_add_sq (𝕜 := ℝ) (x := (p.1 : E)) (y := (p.2 : E)))

/-- **ρ factorizes over an orthogonal internal sum of two lattices**:
`ρ_s(W₁ ⊔ W₂) = ρ_s(W₁) · ρ_s(W₂)`. -/
lemma mass_sup_mul {W₁ W₂ : Submodule ℤ E}
    [DiscreteTopology (supMod W₁ W₂)] (hop : OrthogonalPair W₁ W₂) (s : ℝ) (hs : 0 < s) :
    mass s (supMod W₁ W₂) = mass s W₁ * mass s W₂ := by
  classical
  have hd : DisjointPair W₁ W₂ := disjoint_of_orthogonal hop
  let e : (W₁ × W₂) ≃ ↥(supMod W₁ W₂) := sumEquiv W₁ W₂ hd
  let gTop : ↥(supMod W₁ W₂) → ℝ := fun z => rexp (-Real.pi * ‖(z : E)‖ ^ 2 / s ^ 2)
  let g : (W₁ × W₂) → ℝ := fun p =>
    rexp (-Real.pi * ‖(p.1 : E)‖ ^ 2 / s ^ 2) * rexp (-Real.pi * ‖(p.2 : E)‖ ^ 2 / s ^ 2)
  have hval : ∀ p : W₁ × W₂, (((e p : ↥(supMod W₁ W₂)) : E)) = (p.1 : E) + (p.2 : E) := by
    intro p
    dsimp [e, sumEquiv, sumTo]
  have hpythag : ∀ p : W₁ × W₂, ‖(p.1 : E) + (p.2 : E)‖ ^ 2 =
      ‖(p.1 : E)‖ ^ 2 + ‖(p.2 : E)‖ ^ 2 := by
    intro p
    have horth : ⟪(p.1 : E), (p.2 : E)⟫_ℝ = 0 := hop (p.1 : E) p.1.2 (p.2 : E) p.2.2
    simpa [horth] using (norm_add_sq (𝕜 := ℝ) (x := (p.1 : E)) (y := (p.2 : E)))
  have hpt : ∀ p : W₁ × W₂, gTop (e p) = g p := by
    intro p
    dsimp [gTop, g]
    rw [hval p]
    rw [hpythag p]
    rw [← Real.exp_add]
    congr 1
    ring
  have hsmgTop : Summable gTop := by
    dsimp [gTop]
    exact summable_mass (supMod W₁ W₂) s hs
  have hsmg : Summable g := by
    have hpull : Summable (fun p : W₁ × W₂ => gTop (e p)) := by
      exact (Equiv.summable_iff (e := e) (f := gTop)).mpr hsmgTop
    have hfun : g = (fun p : W₁ × W₂ => gTop (e p)) := by
      funext p
      exact (hpt p).symm
    rw [hfun]
    exact hpull
  have hfactor : (∑' p : W₁ × W₂, g p) = mass s W₁ * mass s W₂ := by
    calc
      (∑' p : W₁ × W₂, g p) = ∑' x : W₁, ∑' y : W₂, g (x, y) := by
        exact Summable.tsum_prod hsmg
      _ = ∑' x : W₁, rexp (-Real.pi * ‖(x : E)‖ ^ 2 / s ^ 2) *
          (∑' y : W₂, rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2)) := by
            apply tsum_congr
            intro x
            dsimp [g]
            rw [tsum_mul_left]
      _ = (∑' x : W₁, rexp (-Real.pi * ‖(x : E)‖ ^ 2 / s ^ 2)) *
          (∑' y : W₂, rexp (-Real.pi * ‖(y : E)‖ ^ 2 / s ^ 2)) := by
            rw [tsum_mul_right]
      _ = mass s W₁ * mass s W₂ := by rfl
  calc
    mass s (supMod W₁ W₂) = ∑' z : ↥(supMod W₁ W₂), gTop z := by rfl
    _ = ∑' p : W₁ × W₂, gTop (e p) := (Equiv.tsum_eq e gTop).symm
    _ = ∑' p : W₁ × W₂, g p := by
      apply tsum_congr
      exact hpt
    _ = mass s W₁ * mass s W₂ := hfactor



/-- ρ over an internal orthogonal sum is ≤ ρ over the internal sum of scaled pieces
(0 < αᵢ ≤ 1 shrinks each piece, which increases its Gaussian mass). -/
lemma mass_sup_le_sup_smul {W₁ W₂ : Submodule ℤ E} [DiscreteTopology W₁] [DiscreteTopology W₂]
    [DiscreteTopology (supMod W₁ W₂)] (hop : OrthogonalPair W₁ W₂)
    (s : ℝ) (hs : 0 < s) {α₁ α₂ : ℝ} (ha₁ : 0 < α₁) (ha₁' : α₁ ≤ 1)
    (ha₂ : 0 < α₂) (ha₂' : α₂ ≤ 1)
    [DiscreteTopology (supMod (smulLattice α₁ W₁) (smulLattice α₂ W₂))] :
    mass s (supMod W₁ W₂) ≤ mass s (supMod (smulLattice α₁ W₁) (smulLattice α₂ W₂)) := by
  classical
  have hopS : OrthogonalPair (smulLattice α₁ W₁) (smulLattice α₂ W₂) := by
    intro x hx y hy
    rcases (mem_smulLattice.mp hx) with ⟨x₀, hx₀, hx0⟩
    rcases (mem_smulLattice.mp hy) with ⟨y₀, hy₀, hy0⟩
    have horth : ⟪(x₀ : E), (y₀ : E)⟫_ℝ = 0 := hop (x₀ : E) hx₀ (y₀ : E) hy₀
    -- ⟪α₁•x₀, α₂•y₀⟫ = α₁α₂·⟪x₀,y₀⟫ = 0
    rw [← hx0, ← hy0]
    rw [real_inner_smul_left, real_inner_smul_right]
    rw [horth]
    ring
  have hnonneg : ∀ ℒ : Submodule ℤ E, 0 ≤ mass s ℒ := by
    intro ℒ
    dsimp [mass]
    exact tsum_nonneg (fun y => by positivity)
  calc
    mass s (supMod W₁ W₂) = mass s W₁ * mass s W₂ := mass_sup_mul (W₁ := W₁) (W₂ := W₂) hop s hs
    _ ≤ mass s (smulLattice α₁ W₁) * mass s (smulLattice α₂ W₂) := by
      exact mul_le_mul (mass_le_of_smul (ℒ := W₁) s hs ha₁ ha₁')
        (mass_le_of_smul (ℒ := W₂) s hs ha₂ ha₂')
        (hnonneg W₂) (hnonneg (smulLattice α₁ W₁))
    _ = mass s (supMod (smulLattice α₁ W₁) (smulLattice α₂ W₂)) := by
      exact (mass_sup_mul (W₁ := smulLattice α₁ W₁) (W₂ := smulLattice α₂ W₂) hopS s hs).symm



/-- Multiplying a discrete lattice by a nonzero real scalar keeps it discrete. -/
lemma discrete_smulLattice (α : ℝ) (hα : α ≠ 0) (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] :
    DiscreteTopology (smulLattice α ℒ) := by
  let f : E → E := fun x => (α⁻¹ : ℝ) • x
  have hcont : Continuous f := by dsimp [f]; fun_prop
  have hinj : Function.Injective f := by
    intro x y hxy
    dsimp [f] at hxy
    have hsub : (α⁻¹ : ℝ) • x - (α⁻¹ : ℝ) • y = 0 := by rw [hxy]; abel
    have h' : (α⁻¹ : ℝ) • (x - y) = 0 := by
      rw [smul_sub]
      exact hsub
    have hz : x - y = 0 := (smul_eq_zero.mp h').resolve_left (inv_ne_zero hα)
    exact sub_eq_zero.mp hz
  have hDs : DiscreteTopology (f ⁻¹' (ℒ : Set E)) :=
    DiscreteTopology.preimage_of_continuous_injective (s := (ℒ : Set E)) hcont hinj
  have hset : (f ⁻¹' (ℒ : Set E)) = (smulLattice α ℒ : Set E) := by
    ext z
    constructor
    · intro hz
      change z ∈ smulLattice α ℒ
      rw [smulLattice]
      rw [Submodule.mem_map]
      refine ⟨(α⁻¹ : ℝ) • z, ?_, ?_⟩
      · exact hz
      · dsimp [smulMap]
        rw [smul_smul]
        field_simp [hα]
        simp
    · intro hz
      change z ∈ smulLattice α ℒ at hz
      rw [smulLattice] at hz
      rw [Submodule.mem_map] at hz
      rcases hz with ⟨y, hy, hzy⟩
      dsimp [f]
      have hyz : (α⁻¹ : ℝ) • z = y := by
        dsimp [smulMap] at hzy
        rw [← hzy]
        rw [smul_smul]
        field_simp [hα]
        simp
      simpa [hyz] using hy
  change DiscreteTopology (smulLattice α ℒ : Set E)
  rw [← hset]
  exact hDs


/-- ρ is nonnegative. -/
lemma mass_nonneg (ℒ : Submodule ℤ E) (s : ℝ) : 0 ≤ mass s ℒ := by
  dsimp [mass]
  exact tsum_nonneg (fun y => by positivity)

/-- Finite product rule over pairwise-orthogonal pieces (local wrapper around the commons
`orthFam_mass_prod`). -/
lemma mass_finFam_prod {k : ℕ} (W : Fin k → Submodule ℤ E) (S : Submodule ℤ E)
    (hS : S = ⨆ i : Fin k, W i) [DiscreteTopology S]
    (horth : ∀ i j : Fin k, i ≠ j → OrthogonalPair (W i) (W j))
    (hdisc : ∀ i : Fin k, DiscreteTopology (W i)) (s : ℝ) (hs : 0 < s) :
    mass s S = ∏ i : Fin k, mass s (W i) := by
  have horth' : ∀ i j : Fin k, i ≠ j → ∀ x : E, x ∈ W i → ∀ y : E, y ∈ W j → inner ℝ x y = 0 := by
    intro i j hij x hx y hy
    exact horth i j hij x hx y hy
  have h := Commons.Lattice.Gaussian.orthFam_mass_prod (n := n) (W := W) (S := S) hS horth' hdisc s hs
  simpa [mass] using h

/-- Scaling each of finitely many pairwise-orthogonal pieces down (0 < αᵢ ≤ 1) can only
increase the Gaussian mass of the internal sum. -/
lemma mass_finFam_le_scaled {k : ℕ} (W : Fin k → Submodule ℤ E) (S : Submodule ℤ E)
    (hS : S = ⨆ i : Fin k, W i) [DiscreteTopology S]
    (horth : ∀ i j : Fin k, i ≠ j → OrthogonalPair (W i) (W j))
    (hdisc : ∀ i : Fin k, DiscreteTopology (W i))
    (α : Fin k → ℝ) (hα0 : ∀ i, 0 < α i) (hα1 : ∀ i, α i ≤ 1)
    (S' : Submodule ℤ E) (hS' : S' = ⨆ i : Fin k, smulLattice (α i) (W i))
    [DiscreteTopology S'] (s : ℝ) (hs : 0 < s) :
    mass s S ≤ mass s S' := by
  classical
  let W' : Fin k → Submodule ℤ E := fun i => smulLattice (α i) (W i)
  have horth' : ∀ i j : Fin k, i ≠ j → OrthogonalPair (W' i) (W' j) := by
    intro i j hij x hx y hy
    dsimp [W'] at hx hy
    rcases (mem_smulLattice.mp hx) with ⟨x₀, hx₀, hx0⟩
    rcases (mem_smulLattice.mp hy) with ⟨y₀, hy₀, hy0⟩
    have hz : ⟪(x₀ : E), (y₀ : E)⟫_ℝ = 0 := horth i j hij (x₀ : E) hx₀ (y₀ : E) hy₀
    rw [← hx0, ← hy0]
    rw [real_inner_smul_left, real_inner_smul_right]
    rw [hz]
    ring
  have hdisc' : ∀ i : Fin k, DiscreteTopology (W' i) := by
    intro i
    dsimp [W']
    haveI : DiscreteTopology (W i) := hdisc i
    exact discrete_smulLattice (α i) (ne_of_gt (hα0 i)) (W i)
  calc
    mass s S = ∏ i : Fin k, mass s (W i) := mass_finFam_prod (W := W) (S := S) hS horth hdisc s hs
    _ ≤ ∏ i : Fin k, mass s (W' i) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact mass_nonneg (W i) s
      · intro i hi
        dsimp [W']
        exact mass_le_of_smul (ℒ := W i) s hs (hα0 i) (hα1 i)
    _ = mass s S' := by
      exact (mass_finFam_prod (W := W') (S := S') (by simpa [W'] using hS') horth' hdisc' s hs).symm


/-- elements of W₁ are orthogonal to every element of the real span of W₂ -/
lemma orth_pair_left_span {W₁ W₂ : Submodule ℤ E} (hop : OrthogonalPair W₁ W₂) :
    ∀ x : E, x ∈ realSpan W₁ → ∀ y : E, y ∈ W₂ → ⟪x, y⟫_ℝ = 0 := by
  intro x hx y hy
  refine Submodule.span_induction (s := (W₁ : Set E))
    (p := fun t (ht : t ∈ Submodule.span ℝ (W₁ : Set E)) => ⟪t, y⟫_ℝ = 0) ?_ ?_ ?_ ?_ hx
  · intro a ha
    exact hop a ha y hy
  · simp
  · intro a b ha hb hpa hpb
    rw [inner_add_left]
    rw [hpa, hpb]
    ring
  · intro r a ha hpa
    rw [real_inner_smul_left]
    rw [hpa]
    ring

/-- elements of the real span of W₁ are orthogonal to W₂ -/
lemma orth_pair_right_span {W₁ W₂ : Submodule ℤ E} (hop : OrthogonalPair W₁ W₂) :
    ∀ x : E, x ∈ W₁ → ∀ y : E, y ∈ realSpan W₂ → ⟪x, y⟫_ℝ = 0 := by
  intro x hx y hy
  refine Submodule.span_induction (s := (W₂ : Set E))
    (p := fun t (ht : t ∈ Submodule.span ℝ (W₂ : Set E)) => ⟪x, t⟫_ℝ = 0) ?_ ?_ ?_ ?_ hy
  · intro a ha
    exact hop x hx a ha
  · simp
  · intro a b ha hb hpa hpb
    rw [inner_add_right]
    rw [hpa, hpb]
    ring
  · intro r a ha hpa
    rw [real_inner_smul_right]
    rw [hpa]
    ring

/-- The internal sum of two pairwise-orthogonal discrete lattices is discrete. -/
lemma discrete_supMod {W₁ W₂ : Submodule ℤ E} [DiscreteTopology W₁] [DiscreteTopology W₂]
    (hop : OrthogonalPair W₁ W₂) : DiscreteTopology (supMod W₁ W₂) := by
  classical
  let T₁ : Submodule ℝ E := realSpan W₁
  let T₂ : Submodule ℝ E := realSpan W₂
  have hdec : ∀ z : ↥(supMod W₁ W₂),
      T₁.starProjection ((z : E)) ∈ W₁ ∧ T₂.starProjection ((z : E)) ∈ W₂ ∧
      (z : E) = T₁.starProjection ((z : E)) + T₂.starProjection ((z : E)) := by
    intro z
    rcases (Submodule.mem_sup.mp (by simpa [supMod] using z.2)) with ⟨x₁, hx₁, y₁, hy₁, hz⟩
    have hp1x : T₁.starProjection ((z : E)) = x₁ := by
      calc
        T₁.starProjection ((z : E)) = T₁.starProjection (x₁ + y₁) := by rw [hz]
        _ = T₁.starProjection x₁ + T₁.starProjection y₁ := by
          exact map_add (T₁.starProjection : E →ₗ[ℝ] E) x₁ y₁
        _ = x₁ + 0 := by
          congr 1
          · exact (Submodule.starProjection_eq_self_iff (K := T₁)).mpr (by dsimp [T₁]; exact mem_realSpan (ℒ := W₁) hx₁)
          · apply starProjection_eq_zero_of_mem_orthogonal T₁
            rw [Submodule.mem_orthogonal]
            intro u hu
            exact orth_pair_left_span (W₁ := W₁) (W₂ := W₂) hop u (by simpa [T₁] using hu) y₁ hy₁
        _ = x₁ := by simp
    have hp2y : T₂.starProjection ((z : E)) = y₁ := by
      calc
        T₂.starProjection ((z : E)) = T₂.starProjection (x₁ + y₁) := by rw [hz]
        _ = T₂.starProjection x₁ + T₂.starProjection y₁ := by
          exact map_add (T₂.starProjection : E →ₗ[ℝ] E) x₁ y₁
        _ = 0 + y₁ := by
          congr 1
          · apply starProjection_eq_zero_of_mem_orthogonal T₂
            rw [Submodule.mem_orthogonal]
            intro u hu
            rw [real_inner_comm]
            exact orth_pair_right_span (W₁ := W₁) (W₂ := W₂) hop x₁ hx₁ u (by simpa [T₂] using hu)
          · exact (Submodule.starProjection_eq_self_iff (K := T₂)).mpr (by dsimp [T₂]; exact mem_realSpan (ℒ := W₂) hy₁)
        _ = y₁ := by simp
    refine ⟨?_, ?_, ?_⟩
    · rw [hp1x]
      exact hx₁
    · rw [hp2y]
      exact hy₁
    · rw [hp1x, hp2y]
      exact hz.symm
  let dec : ↥(supMod W₁ W₂) → W₁ × W₂ := fun z =>
    (⟨T₁.starProjection ((z : E)), (hdec z).1⟩, ⟨T₂.starProjection ((z : E)), (hdec z).2.1⟩)
  have hinj : Function.Injective dec := by
    intro z w hzw
    apply Subtype.ext
    have hc1 : T₁.starProjection ((z : E)) = T₁.starProjection ((w : E)) := by
      have := congrArg (fun p : W₁ × W₂ => ((p.1 : W₁) : E)) hzw
      simpa [dec] using this
    have hc2 : T₂.starProjection ((z : E)) = T₂.starProjection ((w : E)) := by
      have := congrArg (fun p : W₁ × W₂ => ((p.2 : W₂) : E)) hzw
      simpa [dec] using this
    calc
      (z : E) = T₁.starProjection ((z : E)) + T₂.starProjection ((z : E)) := (hdec z).2.2
      _ = T₁.starProjection ((w : E)) + T₂.starProjection ((w : E)) := by rw [hc1, hc2]
      _ = (w : E) := (hdec w).2.2.symm
  have hcont : Continuous dec := by
    dsimp [dec]
    fun_prop
  exact DiscreteTopology.of_continuous_injective (β := W₁ × W₂) (f := dec) hcont hinj


lemma discreteTopology_of_subsingleton {α : Type*} [TopologicalSpace α] [Subsingleton α] :
    DiscreteTopology α := by
  rw [discreteTopology_iff_forall_isOpen]
  intro s
  classical
  by_cases hne : s.Nonempty
  · have hsU : s = Set.univ := by
      ext x
      constructor
      · intro hx
        trivial
      · intro hx
        rcases hne with ⟨y, hy⟩
        have hxy : x = y := Subsingleton.elim x y
        simpa [hxy] using hy
    rw [hsU]
    exact isOpen_univ
  · have hs_empty : s = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
    rw [hs_empty]
    exact isOpen_empty

/-- the zero submodule is discrete -/
lemma discrete_bot : DiscreteTopology (⊥ : Submodule ℤ E) := by
  haveI : Subsingleton (⊥ : Submodule ℤ E) := ⟨fun x y => by
    apply Subtype.ext
    have hx : (x : E) = 0 := (Submodule.mem_bot (R := ℤ)).mp x.2
    have hy : (y : E) = 0 := (Submodule.mem_bot (R := ℤ)).mp y.2
    rw [hx, hy]⟩
  exact discreteTopology_of_subsingleton (α := (⊥ : Submodule ℤ E))

/-- complete-lattice identity: a `Fin (k+1)`-sup splits into the first and remaining pieces -/
lemma iSup_fin_succ_front {α : Type*} [CompleteLattice α] {k : ℕ} (f : Fin (k + 1) → α) :
    (⨆ i : Fin (k + 1), f i) = f 0 ⊔ (⨆ i : Fin k, f (Fin.succ i)) := by
  apply le_antisymm
  · refine iSup_le ?_
    intro i
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
    · exact le_sup_left
    · exact le_trans (le_iSup (fun j : Fin k => f (Fin.succ j)) j) le_sup_right
  · apply sup_le
    · exact le_iSup f 0
    · refine iSup_le ?_
      intro j
      exact le_iSup f (Fin.succ j)

/-- a submodule orthogonal to every member of a family is orthogonal to the family sup -/
lemma orthogonalPair_piece_iSup {ι : Type*} (Q : ι → Submodule ℤ E) {W₀ : Submodule ℤ E}
    (h : ∀ j : ι, OrthogonalPair W₀ (Q j)) : OrthogonalPair W₀ (⨆ j : ι, Q j) := by
  intro x hx y hy
  refine Submodule.iSup_induction (p := Q) (motive := fun y => ⟪x, y⟫_ℝ = 0) hy ?_ ?_ ?_
  · intro j z hz
    exact h j x hx z hz
  · simp
  · intro a b ha hb
    rw [inner_add_right]
    rw [ha, hb]
    ring

lemma iSup_fin0_eq_bot {W : Fin 0 → Submodule ℤ E} :
    (⨆ i : Fin 0, W i) = (⊥ : Submodule ℤ E) := by
  apply le_antisymm
  · refine iSup_le ?_
    intro i
    exfalso
    exact (Nat.not_lt_zero i.val i.isLt)
  · exact bot_le

/-- the internal sup of a finite pairwise-orthogonal family of discrete lattices is discrete -/
lemma discrete_supFam : ∀ (k : ℕ) (W : Fin k → Submodule ℤ E),
    (∀ i j : Fin k, i ≠ j → OrthogonalPair (W i) (W j)) →
    (∀ i : Fin k, DiscreteTopology (W i)) →
    ∀ (S : Submodule ℤ E), S = ⨆ i : Fin k, W i → DiscreteTopology S := by
  intro k
  induction k with
  | zero =>
      intro W horth hdisc S hS
      rw [hS]
      rw [iSup_fin0_eq_bot]
      exact discrete_bot
  | succ k ih =>
      intro W horth hdisc S hS
      have hsplit : (⨆ i : Fin (k + 1), W i) = supMod (W 0) (⨆ j : Fin k, W (Fin.succ j)) := by
        rw [iSup_fin_succ_front (f := fun i : Fin (k + 1) => W i)]
        rfl
      rw [hS, hsplit]
      haveI : DiscreteTopology (W 0) := hdisc 0
      have horthT : ∀ i j : Fin k, i ≠ j → OrthogonalPair (W (Fin.succ i)) (W (Fin.succ j)) := by
        intro i j hij
        exact horth (Fin.succ i) (Fin.succ j) (by intro h; exact hij ((Fin.succ_injective k) h))
      have hdiscT : ∀ i : Fin k, DiscreteTopology (W (Fin.succ i)) := fun i => hdisc (Fin.succ i)
      let Tail : Submodule ℤ E := ⨆ j : Fin k, W (Fin.succ j)
      have hdiscTail : DiscreteTopology Tail := by
        dsimp [Tail]
        exact ih (fun j : Fin k => W (Fin.succ j)) horthT hdiscT Tail (by rfl)
      haveI : DiscreteTopology Tail := hdiscTail
      have hopT : OrthogonalPair (W 0) Tail := by
        dsimp [Tail]
        apply orthogonalPair_piece_iSup (W₀ := W 0) (Q := fun j : Fin k => W (Fin.succ j))
        intro j
        exact horth 0 (Fin.succ j) (by intro h; exact Fin.succ_ne_zero j h.symm)
      exact discrete_supMod hopT


/-- The quotient lattice of a primitive sublattice is discrete. -/
lemma discrete_quotLattice {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (S : Submodule ℝ E) (hS : S = realSpan ℒ') (hp : Primitive ℒ' ℒ) :
    DiscreteTopology (quotLattice ℒ S) := by
  change DiscreteTopology
    (ℒ.map (((Submodule.orthogonal S).starProjection : E →ₗ[ℝ] E).restrictScalars ℤ))
  exact Commons.Lattice.Discrete.discreteTopology_quotLattice (ℒ' := ℒ') (ℒ := ℒ) S
    (by simpa [realSpan] using hS)
    (by intro x; rw [hp x]; simp [← hS])


/-- The quotient lattice is the Z-span of the projections of a Z-basis of ℒ. -/
lemma quotLattice_eq_span_proj {ℒ : Submodule ℤ E}
    (b : Module.Basis (Fin n) ℤ ℒ) (S : Submodule ℝ E) :
    quotLattice ℒ S = Submodule.span ℤ
      (Set.range (fun j : Fin n => Sᗮ.starProjection ((b j : ℒ) : E))) := by
  classical
  let p : E →ₗ[ℤ] E := (Sᗮ.starProjection : E →ₗ[ℝ] E).restrictScalars ℤ
  apply le_antisymm
  · -- ⊆ : image elements are ℤ-combinations of the projected basis values
    intro z hz
    rw [mem_quotLattice] at hz
    rcases hz with ⟨y, hy, hzy⟩
    -- expand y in the basis
    have hy' : (y : E) = ∑ j : Fin n, (b.repr ⟨y, hy⟩ j : ℤ) • ((b j : ℒ) : E) := by
      have hc := Commons.Lattice.PoissonSummation.coerce_basis_expand (ℒ := ℒ) (b := b) ⟨y, hy⟩
      simpa using hc
    -- z = p y = Σ coeff • p (b j)
    rw [← hzy]
    change p (y : E) ∈ Submodule.span ℤ
      (Set.range (fun j : Fin n => Sᗮ.starProjection ((b j : ℒ) : E)))
    rw [hy']
    rw [map_sum]
    apply Submodule.sum_mem
    intro j hj
    rw [map_smul p (b.repr ⟨y, hy⟩ j : ℤ) ((b j : ℒ) : E)]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    exact ⟨j, rfl⟩
  · -- ⊇ : span of projected basis values ⊆ image
    rw [Submodule.span_le]
    intro z hz
    rcases hz with ⟨j, hz⟩
    rw [← hz]
    exact Submodule.mem_map.mpr ⟨(b j : ℒ), (b j : ℒ).2, rfl⟩


/-- tail embedding Fin (n-d) ↪ Fin n (shifts by d) -/
noncomputable def tailEmb {n d : ℕ} (hd : d ≤ n) (j : Fin (n - d)) : Fin n :=
  ⟨d + j.val, by omega⟩

/-- When the projections of the first d basis vectors vanish, the quotient lattice is
generated by the projected tail of the basis. -/
lemma quotLattice_eq_span_tail {ℒ : Submodule ℤ E} {d : ℕ} (hd : d ≤ n)
    (b : Module.Basis (Fin n) ℤ ℒ) (S : Submodule ℝ E)
    (hzero : ∀ i : Fin d, Sᗮ.starProjection ((b (Fin.castLE hd i) : ℒ) : E) = 0) :
    quotLattice ℒ S = Submodule.span ℤ
      (Set.range (fun j : Fin (n - d) => Sᗮ.starProjection ((b (tailEmb (n := n) hd j) : ℒ) : E))) := by
  classical
  have hspan := quotLattice_eq_span_proj (ℒ := ℒ) b S
  -- it suffices to show span(full) = span(tail); hspan gives quotLattice = span(full)
  rw [hspan]
  apply le_antisymm
  · -- span(full) ⊆ span(tail): each generator is in span(tail)
    rw [Submodule.span_le]
    intro z hz
    rcases hz with ⟨k, hz⟩
    rw [← hz]
    by_cases hk : k.val < d
    · -- k in the castLE image ⇒ projection is 0
      have hk' : k = Fin.castLE hd ⟨k.val, hk⟩ := by
        apply Fin.ext
        rfl
      have hz0 : Sᗮ.starProjection ((b k : ℒ) : E) = 0 := by
        rw [hk']
        exact hzero ⟨k.val, hk⟩
      change Sᗮ.starProjection ((b k : ℒ) : E) ∈
        Submodule.span ℤ (Set.range (fun j : Fin (n - d) => Sᗮ.starProjection ((b (tailEmb (n := n) hd j) : ℒ) : E)))
      rw [hz0]
      apply Submodule.zero_mem
    · -- k in the tail image
      let k' : Fin (n - d) := ⟨k.val - d, by omega⟩
      have hdval : d ≤ k.val := le_of_not_gt hk
      have hkt : k = tailEmb (n := n) hd k' := by
        apply Fin.ext
        dsimp [tailEmb]
        dsimp [k']
        omega
      change Sᗮ.starProjection ((b k : ℒ) : E) ∈
        Submodule.span ℤ (Set.range (fun j : Fin (n - d) => Sᗮ.starProjection ((b (tailEmb (n := n) hd j) : ℒ) : E)))
      rw [hkt]
      apply Submodule.subset_span
      exact ⟨k', rfl⟩
  · -- span(tail) ⊆ span(full)
    rw [Submodule.span_le]
    intro z hz
    rcases hz with ⟨j, hz⟩
    rw [← hz]
    apply Submodule.subset_span
    exact ⟨tailEmb (n := n) hd j, rfl⟩


lemma finrank_le_of_le {ℒ' ℒ : Submodule ℤ E} (hle : ℒ' ≤ ℒ)
    [Module.Free ℤ ℒ] [Module.Finite ℤ ℒ] [Module.Free ℤ ℒ'] [Module.Finite ℤ ℒ'] :
    Module.finrank ℤ ℒ' ≤ Module.finrank ℤ ℒ := by
  let C : Submodule ℤ ℒ := ℒ'.comap (ℒ.subtype)
  have hC : Module.finrank ℤ C = Module.finrank ℤ ℒ' := by
    exact (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hle))
  have hC2 : Module.finrank ℤ C ≤ Module.finrank ℤ ℒ := by
    exact Submodule.finrank_le C
  linarith

lemma fullrank_finrank (ℒ : Submodule ℤ E) [DiscreteTopology ℒ] (hℒ : IsZLattice ℝ ℒ) :
    Module.finrank ℤ ℒ = n := by
  have h := ZLattice.rank ℝ ℒ
  simpa using h

/-- Adapted basis in the primitive full-rank context: e is a ℤ-basis of ℒ whose first d
vectors are the canonical basis vectors of ℒ'. -/
lemma exists_adapted_basis {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (hℒ : IsZLattice ℝ ℒ) (hp : Primitive ℒ' ℒ) :
    ∃ e : Module.Basis (Fin n) ℤ ℒ,
      ∀ i : Fin (finrank ℤ ℒ'),
        ((e (Fin.castLE (by
          have hle : ℒ' ≤ ℒ := Primitive.le hp
          haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
          haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
          haveI : Module.Free ℤ ℒ' := instModuleFree_of_discrete_submodule ℒ'
          haveI : Module.Finite ℤ ℒ' := instModuleFinite_of_discrete_submodule ℒ'
          have hn : Module.finrank ℤ ℒ = n := fullrank_finrank ℒ hℒ
          linarith [finrank_le_of_le (ℒ' := ℒ') (ℒ := ℒ) hle]) i) : ℒ) : E) =
        ((Module.finBasis ℤ ℒ' i : ℒ') : E) := by
  classical
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  haveI : Module.Free ℤ ℒ' := instModuleFree_of_discrete_submodule ℒ'
  haveI : Module.Finite ℤ ℒ' := instModuleFinite_of_discrete_submodule ℒ'
  let hd : finrank ℤ ℒ' ≤ n := by
    have hle : ℒ' ≤ ℒ := Primitive.le hp
    have hn : Module.finrank ℤ ℒ = n := fullrank_finrank ℒ hℒ
    linarith [finrank_le_of_le (ℒ' := ℒ') (ℒ := ℒ) hle]
  have hn : Module.finrank ℤ ℒ = n := fullrank_finrank ℒ hℒ
  rcases (Commons.Lattice.Module.basis_extension_pure (hd := hd) (ℒ' := ℒ') (ℒ := ℒ)
    (hle := Primitive.le hp) (hrank := hn) (b' := Module.finBasis ℤ ℒ')
    (hprim := fun x => hp x)) with ⟨e, he⟩
  refine ⟨e, ?_⟩
  intro i
  -- he : ∀ i, (e (castLE hd i) : ℒ : E) = ((finBasis ℤ ℒ' i : ℒ') : E)
  exact he i


/-- Adapted basis + tail-spanning of the quotient, in the primitive full-rank context. -/
lemma exists_adapted_basis_span {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (hℒ : IsZLattice ℝ ℒ) (S : Submodule ℝ E) (hS : S = realSpan ℒ') (hp : Primitive ℒ' ℒ)
    (hd : Module.finrank ℤ ℒ' ≤ n) :
    ∃ e : Module.Basis (Fin n) ℤ ℒ,
      quotLattice ℒ S = Submodule.span ℤ
        (Set.range (fun j : Fin (n - Module.finrank ℤ ℒ') =>
          Sᗮ.starProjection (((e (tailEmb (n := n) hd j) : ℒ)) : E))) := by
  classical
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  haveI : Module.Free ℤ ℒ' := instModuleFree_of_discrete_submodule ℒ'
  haveI : Module.Finite ℤ ℒ' := instModuleFinite_of_discrete_submodule ℒ'
  rcases (exists_adapted_basis (ℒ' := ℒ') (ℒ := ℒ) hℒ hp) with ⟨e, he⟩
  refine ⟨e, ?_⟩
  -- hzero: first-d projections vanish
  have hzero : ∀ i : Fin (finrank ℤ ℒ'),
      Sᗮ.starProjection (((e (Fin.castLE hd i) : ℒ)) : E) = 0 := by
    intro i
    have hval : ((e (Fin.castLE hd i) : ℒ) : E) = ((Module.finBasis ℤ ℒ' i : ℒ') : E) := he i
    have hxS : ((e (Fin.castLE hd i) : ℒ) : E) ∈ S := by
      rw [hval]
      rw [hS]
      exact mem_realSpan (ℒ := ℒ') (Module.finBasis ℤ ℒ' i).2
    exact starProjection_orthogonal_eq_zero_of_mem S hxS
  exact quotLattice_eq_span_tail (n := n) hd e S hzero


/-- ambient expansion of a lattice element in any Z-basis of the lattice -/
lemma ambient_basis_expand {ℒ : Submodule ℤ E} {m : ℕ}
    (b : Module.Basis (Fin m) ℤ ℒ) (x : ℒ) :
    (x : E) = ∑ i : Fin m, (b.repr x i : ℤ) • ((b i : ℒ) : E) := by
  classical
  have hsum : (∑ i : Fin m, (b.repr x i : ℤ) • (b i : ℒ)) = x := by
    simp [b.sum_repr x]
  calc
    (x : E) = (ℒ.subtype : ℒ →ₗ[ℤ] E) x := rfl
    _ = (ℒ.subtype : ℒ →ₗ[ℤ] E) (∑ i : Fin m, (b.repr x i : ℤ) • (b i : ℒ)) := by rw [hsum]
    _ = ∑ i : Fin m, (ℒ.subtype : ℒ →ₗ[ℤ] E) ((b.repr x i : ℤ) • (b i : ℒ)) := by rw [map_sum]
    _ = ∑ i : Fin m, (b.repr x i : ℤ) • ((b i : ℒ) : E) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul]
      rfl

/-- The real span of a lattice is the real span of the values of its canonical basis. -/
lemma realSpan_eq_span_basis {ℒ : Submodule ℤ E} [Module.Free ℤ ℒ] [Module.Finite ℤ ℒ] :
    realSpan ℒ = Submodule.span ℝ
      (Set.range (fun i : Fin (finrank ℤ ℒ) => ((Module.finBasis ℤ ℒ i : ℒ) : E))) := by
  classical
  let b := Module.finBasis ℤ ℒ
  apply le_antisymm
  · rw [realSpan]
    exact Submodule.span_le.mpr (by
      intro x hx
      have hExp : ((⟨x, hx⟩ : ℒ) : E) = ∑ i : Fin (finrank ℤ ℒ),
          (b.repr ⟨x, hx⟩ i : ℤ) • ((b i : ℒ) : E) := by
        exact ambient_basis_expand (ℒ := ℒ) (b := b) ⟨x, hx⟩
      have hxval : ((⟨x, hx⟩ : ℒ) : E) = x := rfl
      have hmem : x ∈ Submodule.span ℝ
          (Set.range (fun i : Fin (finrank ℤ ℒ) => ((b i : ℒ) : E))) := by
        rw [← hxval, hExp]
        apply Submodule.sum_mem
        intro i hi
        rw [← (Int.cast_smul_eq_zsmul (R := ℝ) (n := b.repr ⟨x, hx⟩ i) ((b i : ℒ) : E))]
        apply Submodule.smul_mem
        apply Submodule.subset_span
        exact ⟨i, rfl⟩
      exact hmem)
  · rw [realSpan]
    exact Submodule.span_le.mpr (by
      intro x hx
      rcases hx with ⟨i, hx⟩
      rw [← hx]
      exact mem_realSpan (ℒ := ℒ) (b i).2)
/-- the index split map: first d indices (castLE) then the tail -/
noncomputable def finSplitMap {d : ℕ} (hd : d ≤ n) : (Fin d ⊕ Fin (n - d)) → Fin n
  | Sum.inl i => Fin.castLE hd i
  | Sum.inr j => tailEmb (n := n) hd j

lemma finSplitMap_injective {d : ℕ} (hd : d ≤ n) :
    Function.Injective (finSplitMap (n := n) hd) := by
  intro x y hxy
  cases x with
  | inl i =>
      cases y with
      | inl i' =>
          have hv := congrArg Fin.val hxy
          have hv2 : i.val = i'.val := by simpa [finSplitMap, Fin.castLE] using hv
          exact congrArg Sum.inl (Fin.val_injective hv2)
      | inr j =>
          exfalso
          have hv := congrArg Fin.val hxy
          have hi : i.val < d := by exact i.2
          have hj : d ≤ (tailEmb (n := n) hd j).val := by dsimp [tailEmb]; omega
          have hv2 : (Fin.castLE hd i).val = (tailEmb (n := n) hd j).val := by simpa [finSplitMap] using hv
          have hle : (Fin.castLE hd i).val < d := by simp [Fin.castLE]
          omega
  | inr j =>
      cases y with
      | inl i =>
          exfalso
          have hv := congrArg Fin.val hxy
          have hj : d ≤ (tailEmb (n := n) hd j).val := by dsimp [tailEmb]; omega
          have hv2 : (tailEmb (n := n) hd j).val = (Fin.castLE hd i).val := by simpa [finSplitMap] using hv
          have hi : (Fin.castLE hd i).val < d := by simp [Fin.castLE]
          omega
      | inr j' =>
          have hv := congrArg Fin.val hxy
          have hv2 : j.val = j'.val := by
            dsimp [finSplitMap, tailEmb] at hv
            omega
          exact congrArg Sum.inr (Fin.val_injective hv2)

/-- values of a full-rank Z-basis are R-independent in E -/
lemma linIndep_basis_values {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) (e : Module.Basis (Fin n) ℤ ℒ) :
    LinearIndependent ℝ (fun k : Fin n => ((e k : ℒ) : E)) := by
  haveI : IsZLattice ℝ ℒ := hℒ
  rw [show (fun k : Fin n => ((e k : ℒ) : E)) = (e.ofZLatticeBasis ℝ ℒ) by
    funext k; simp]
  exact (e.ofZLatticeBasis ℝ ℒ).linearIndependent

/-- the (u,v)-reindexed family of adapted-basis values is R-independent -/
lemma linIndep_reindexed {ℒ : Submodule ℤ E} [DiscreteTopology ℒ]
    (hℒ : IsZLattice ℝ ℒ) {d : ℕ} (hd : d ≤ n) (e : Module.Basis (Fin n) ℤ ℒ) :
    LinearIndependent ℝ (fun x : Fin d ⊕ Fin (n - d) =>
      ((e (finSplitMap (n := n) hd x) : ℒ) : E)) := by
  exact (linIndep_basis_values hℒ e).comp (finSplitMap (n := n) hd) (finSplitMap_injective (n := n) hd)


/-- The projected tail of an adapted basis is Z-linearly independent in the ambient space. -/
lemma tail_values_linIndep_Z {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (hℒ : IsZLattice ℝ ℒ) (S : Submodule ℝ E) (hS : S = realSpan ℒ')
    (hd : Module.finrank ℤ ℒ' ≤ n) (e : Module.Basis (Fin n) ℤ ℒ)
    (he : ∀ i : Fin (Module.finrank ℤ ℒ'),
      ((e (Fin.castLE hd i) : ℒ) : E) = ((Module.finBasis ℤ ℒ' i : ℒ') : E)) :
    LinearIndependent ℤ (fun j : Fin (n - Module.finrank ℤ ℒ') =>
      Sᗮ.starProjection (((e (tailEmb (n := n) hd j) : ℒ)) : E)) := by
  classical
  haveI : IsZLattice ℝ ℒ := hℒ
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  haveI : Module.Free ℤ ℒ' := instModuleFree_of_discrete_submodule ℒ'
  haveI : Module.Finite ℤ ℒ' := instModuleFinite_of_discrete_submodule ℒ'
  let d := Module.finrank ℤ ℒ'
  have hS' : S = Submodule.span ℝ (Set.range
      (fun i : Fin (Module.finrank ℤ ℒ') => ((e (Fin.castLE hd i) : ℒ) : E))) := by
    rw [hS]
    have hb : realSpan ℒ' = Submodule.span ℝ (Set.range
        (fun i : Fin (Module.finrank ℤ ℒ') => ((Module.finBasis ℤ ℒ' i : ℒ') : E))) :=
      realSpan_eq_span_basis (ℒ := ℒ')
    rw [hb]
    congr 1
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      refine ⟨i, he i⟩
    · rintro ⟨i, rfl⟩
      refine ⟨i, (he i).symm⟩
  have hf : LinearIndependent ℝ (Sum.elim
      (fun i : Fin (Module.finrank ℤ ℒ') => ((e (Fin.castLE hd i) : ℒ) : E))
      (fun j : Fin (n - Module.finrank ℤ ℒ') => ((e (tailEmb (n := n) hd j) : ℒ) : E))) := by
    have hfeq : Sum.elim
        (fun i : Fin (Module.finrank ℤ ℒ') => ((e (Fin.castLE hd i) : ℒ) : E))
        (fun j : Fin (n - Module.finrank ℤ ℒ') => ((e (tailEmb (n := n) hd j) : ℒ) : E)) =
        (fun x : Fin (Module.finrank ℤ ℒ') ⊕ Fin (n - Module.finrank ℤ ℒ') =>
          ((e (finSplitMap hd x) : ℒ) : E)) := by
      funext x
      cases x with
      | inl i => rfl
      | inr j => rfl
    rw [hfeq]
    exact linIndep_reindexed (ℒ := ℒ) hℒ hd e
  have hc := Commons.LinearAlgebra.Projection.linearIndependent_proj_complement (n := n)
    (d := Module.finrank ℤ ℒ') (r := n - Module.finrank ℤ ℒ')
    (u := fun i : Fin (Module.finrank ℤ ℒ') => ((e (Fin.castLE hd i) : ℒ) : E))
    (v := fun j : Fin (n - Module.finrank ℤ ℒ') => ((e (tailEmb (n := n) hd j) : ℒ) : E))
    S hS' hf
  have hprojR : LinearIndependent ℝ (fun j : Fin (n - Module.finrank ℤ ℒ') =>
      Sᗮ.starProjection (((e (tailEmb (n := n) hd j) : ℒ)) : E)) := by
    simpa using hc
  exact hprojR.restrict_scalars' ℤ


/-- For an adapted basis, the quotient lattice equals the Z-span of the projected tail. -/
lemma adapted_span_tail {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (S : Submodule ℝ E) (hS : S = realSpan ℒ')
    (hd : Module.finrank ℤ ℒ' ≤ n) (e : Module.Basis (Fin n) ℤ ℒ)
    (he : ∀ i : Fin (Module.finrank ℤ ℒ'),
      ((e (Fin.castLE hd i) : ℒ) : E) = ((Module.finBasis ℤ ℒ' i : ℒ') : E)) :
    quotLattice ℒ S = Submodule.span ℤ
      (Set.range (fun j : Fin (n - Module.finrank ℤ ℒ') =>
        Sᗮ.starProjection (((e (tailEmb (n := n) hd j) : ℒ)) : E))) := by
  classical
  have hzero : ∀ i : Fin (Module.finrank ℤ ℒ'),
      Sᗮ.starProjection (((e (Fin.castLE hd i) : ℒ)) : E) = 0 := by
    intro i
    have hval : ((e (Fin.castLE hd i) : ℒ) : E) = ((Module.finBasis ℤ ℒ' i : ℒ') : E) := he i
    have hxS : ((e (Fin.castLE hd i) : ℒ) : E) ∈ S := by
      rw [hval]
      rw [hS]
      exact mem_realSpan (ℒ := ℒ') (Module.finBasis ℤ ℒ' i).2
    exact starProjection_orthogonal_eq_zero_of_mem S hxS
  exact quotLattice_eq_span_tail (n := n) hd e S hzero

/-- Basis of the quotient lattice from an adapted basis of ℒ. -/
lemma quotBasis_of_adapted {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (hℒ : IsZLattice ℝ ℒ) (S : Submodule ℝ E) (hS : S = realSpan ℒ')
    (hd : Module.finrank ℤ ℒ' ≤ n) (e : Module.Basis (Fin n) ℤ ℒ)
    (he : ∀ i : Fin (Module.finrank ℤ ℒ'),
      ((e (Fin.castLE hd i) : ℒ) : E) = ((Module.finBasis ℤ ℒ' i : ℒ') : E)) :
    ∃ β : Module.Basis (Fin (n - Module.finrank ℤ ℒ')) ℤ (quotLattice ℒ S),
      ∀ j : Fin (n - Module.finrank ℤ ℒ'),
        ((β j : quotLattice ℒ S) : E) =
          Sᗮ.starProjection (((e (tailEmb (n := n) hd j) : ℒ)) : E) := by
  classical
  let P : Submodule ℤ E := quotLattice ℒ S
  let w' : Fin (n - Module.finrank ℤ ℒ') → P := fun j =>
    ⟨Sᗮ.starProjection (((e (tailEmb (n := n) hd j) : ℒ)) : E), by
      rw [mem_quotLattice]
      exact ⟨(e (tailEmb (n := n) hd j) : ℒ), (e (tailEmb (n := n) hd j) : ℒ).2, rfl⟩⟩
  have hvals : (fun j : Fin (n - Module.finrank ℤ ℒ') => ((w' j : P) : E)) =
      (fun j : Fin (n - Module.finrank ℤ ℒ') =>
        Sᗮ.starProjection (((e (tailEmb (n := n) hd j) : ℒ)) : E)) := by
    funext j
    rfl
  have hspanQ : Submodule.span ℤ (Set.range (fun j : Fin (n - Module.finrank ℤ ℒ') => ((w' j : P) : E))) = P := by
    rw [hvals]
    dsimp [P]
    exact (adapted_span_tail (n := n) S hS hd e he).symm
  have hspanInt : ⊤ ≤ Submodule.span ℤ (Set.range w') := by
    intro z hz
    have hzQ : (z : E) ∈ (P : Set E) := z.2
    have hzspanE : (z : E) ∈ (Submodule.span ℤ (Set.range
        (fun j : Fin (n - Module.finrank ℤ ℒ') => ((w' j : P) : E))) : Set E) := by
      simpa [hspanQ] using hzQ
    rcases (Submodule.mem_span_range_iff_exists_fun (R := ℤ)
        (v := fun j : Fin (n - Module.finrank ℤ ℒ') => ((w' j : P) : E)) (x := (z : E))).mp hzspanE with ⟨c, hc⟩
    have hzP : (∑ j : Fin (n - Module.finrank ℤ ℒ'), c j • (w' j : P)) = z := by
      apply Subtype.ext
      calc
        (((∑ j : Fin (n - Module.finrank ℤ ℒ'), c j • (w' j : P)) : P) : E)
            = (P.subtype : P →ₗ[ℤ] E) (∑ j : Fin (n - Module.finrank ℤ ℒ'), c j • (w' j : P)) := rfl
        _ = ∑ j : Fin (n - Module.finrank ℤ ℒ'), c j • ((w' j : P) : E) := by
            rw [map_sum]
            simp
        _ = (z : E) := hc
    exact (Submodule.mem_span_range_iff_exists_fun (R := ℤ) (v := w') (x := z)).2 ⟨c, hzP⟩
  have hliQ : LinearIndependent ℤ w' := by
    apply Commons.LinearAlgebra.Independence.linearIndependent_of_ambient (P := P) (v := w')
    rw [hvals]
    exact tail_values_linIndep_Z (n := n) (ℒ' := ℒ') (ℒ := ℒ) hℒ S hS hd e he
  let β : Module.Basis (Fin (n - Module.finrank ℤ ℒ')) ℤ P := Module.Basis.mk hliQ hspanInt
  refine ⟨β, ?_⟩
  intro j
  -- β j = w' j, then (w' j : P) : E = value
  have hb : (β j : P) = w' j := by
    simp [β, w']
  rw [hb]


/-- Adapted basis of ℒ together with a basis of the quotient lattice on the projected tail. -/
lemma exists_adapted_quotBasis {ℒ' ℒ : Submodule ℤ E} [DiscreteTopology ℒ] [DiscreteTopology ℒ']
    (hℒ : IsZLattice ℝ ℒ) (S : Submodule ℝ E) (hS : S = realSpan ℒ') (hp : Primitive ℒ' ℒ) :
    ∃ (hd : Module.finrank ℤ ℒ' ≤ n) (e : Module.Basis (Fin n) ℤ ℒ)
      (β : Module.Basis (Fin (n - Module.finrank ℤ ℒ')) ℤ (quotLattice ℒ S)),
      (∀ i : Fin (Module.finrank ℤ ℒ'),
        ((e (Fin.castLE hd i) : ℒ) : E) = ((Module.finBasis ℤ ℒ' i : ℒ') : E)) ∧
      (∀ j : Fin (n - Module.finrank ℤ ℒ'),
        ((β j : quotLattice ℒ S) : E) = Sᗮ.starProjection (((e (tailEmb (n := n) hd j) : ℒ)) : E)) := by
  classical
  haveI : Module.Free ℤ ℒ := instModuleFree_of_discrete_submodule ℒ
  haveI : Module.Finite ℤ ℒ := instModuleFinite_of_discrete_submodule ℒ
  haveI : Module.Free ℤ ℒ' := instModuleFree_of_discrete_submodule ℒ'
  haveI : Module.Finite ℤ ℒ' := instModuleFinite_of_discrete_submodule ℒ'
  let hd : Module.finrank ℤ ℒ' ≤ n := by
    have hle : ℒ' ≤ ℒ := Primitive.le hp
    have hn : Module.finrank ℤ ℒ = n := fullrank_finrank ℒ hℒ
    linarith [finrank_le_of_le (ℒ' := ℒ') (ℒ := ℒ) hle]
  rcases (exists_adapted_basis (ℒ' := ℒ') (ℒ := ℒ) hℒ hp) with ⟨e, he⟩
  rcases (quotBasis_of_adapted (n := n) (ℒ' := ℒ') (ℒ := ℒ) hℒ S hS hd e he) with ⟨β, hβval⟩
  refine ⟨hd, e, β, ?_⟩
  constructor
  · intro i
    exact he i
  · exact hβval


end
end Submission.QuotientLattice
