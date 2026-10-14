import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.HarOp_pointwise_sq
import Submission.Work.FTS.StrongPersist.L3Aux.acoef_gamCoef_slots_le
import Submission.Work.FTS.StrongPersist.SupZ.swap_abs
import Submission.Work.FTS_RegExport.RXT.Sys.continuousAt_Qang_of_bounds
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sin_two_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityStep.Step

set_option autoImplicit false

/-! ## Regularity bookkeeping

The regularity class `Work.FTS.CoercivityStep.HkReg α k f` (`SmoothNbhd f ∧ HkMem α k f`)
descends in the order, is preserved by `D_θ`, `D_z` (one order down), and is closed under
the pointwise operations used by the linearity clauses. -/






/-! ## The open quadrant inside the domain -/

/-- Membership in the open quadrant `Qd`, unfolded. -/
theorem mem_Qd_iff {z θ : ℝ} :
    ((z, θ) ∈ Work.FTS.CoercivityStep.Qd)
      ↔ z ∈ Set.Ioi (0 : ℝ) ∧ θ ∈ Set.Ioo (0 : ℝ) (π / 2) := by
  rw [Work.FTS.CoercivityStep.Qd, Set.mem_prod]




/-! ## Differentiability of the slices -/

/-- The `z`-slice of a `SmoothNbhd` function is differentiable at every point of `nbhU`. -/
theorem differentiableAt_slice_fst {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    {z θ : ℝ} (hy : (z, θ) ∈ Work.Spaces.nbhU) : DifferentiableAt ℝ (fun z' => f z' θ) z := by
  have hd : DifferentiableAt ℝ (Function.uncurry f) (z, θ) :=
    (hf.contDiffAt (Work.Spaces.isOpen_nbhU.mem_nhds hy)).differentiableAt (by norm_num)
  change DifferentiableAt ℝ (Function.uncurry f ∘ fun z' : ℝ => (z', θ)) z
  exact hd.comp z (hasFDerivAt_prodMk_left z θ).differentiableAt

/-- The `θ`-slice of a `SmoothNbhd` function is differentiable at every point of `nbhU`. -/
theorem differentiableAt_slice_snd {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.SmoothNbhd f)
    {z θ : ℝ} (hy : (z, θ) ∈ Work.Spaces.nbhU) : DifferentiableAt ℝ (fun θ' => f z θ') θ := by
  have hd : DifferentiableAt ℝ (Function.uncurry f) (z, θ) :=
    (hf.contDiffAt (Work.Spaces.isOpen_nbhU.mem_nhds hy)).differentiableAt (by norm_num)
  change DifferentiableAt ℝ (Function.uncurry f ∘ fun θ' : ℝ => (z, θ')) θ
  exact hd.comp θ (hasFDerivAt_prodMk_right z θ).differentiableAt

/-! ## The pointwise calculus of `D_θ`, `D_z` on `Iz × Iθ` -/





/-! ## Congruence of the derivatives on the open quadrant -/



/-! ## The Cauchy–Schwarz constant of the new pairing -/


/-! ## Congruence of the pairing in its second argument -/


/-! ## Regularity of the derivative-sums of a sum

For `f, g ∈ HkReg α (n+1)` with `f + g ∈ HkReg α (n+1)`, the functions `D_θf + D_θg` and
`D_zf + D_zg` are again of class `HkReg α n`: they are smooth (closure of `SmoothNbhd`
under addition) and their `ℋ^n` integrand is honest, because on `(0,∞) × I_θ` they agree
with `D_θ(f+g)`, resp. `D_z(f+g)`, whose integrand is honest by `HkReg_dth`/`HkReg_dz`
applied to the *sum*. -/




/-! ## Closure of `HkMem` under scalar multiplication

The last ingredient is that the `ℋ^k`-integrand of a scalar multiple is the multiple of
the integrand: for smooth `f` the iterated operators `D_z^i`, `D_z^jD_θ^i` are
`ℝ`-homogeneous on the neighbourhood `nbhU` on which `SmoothNbhd` is stated (the
totalised `deriv` being homogeneous on a *differentiable* argument), whence

  `HkIntegrand α k (c·f) = c² · HkIntegrand α k f`  on `Iz × Iθ`,

and the honesty of the integrand transfers by `Integrable.congr`. -/

/-- `D_z^i(c·f) = c·D_z^i f` on `nbhU`, for `SmoothNbhd f`. -/
private theorem DzIter_const_mul_nbh (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.SmoothNbhd f) (i : ℕ) :
    Set.EqOn (fun y : ℝ × ℝ => Work.Spaces.DzIter i (fun z θ => c * f z θ) y.1 y.2)
      (fun y : ℝ × ℝ => c * Work.Spaces.DzIter i f y.1 y.2) Work.Spaces.nbhU := by
  induction i with
  | zero => intro y hy; rfl
  | succ n ih =>
      intro y hy
      obtain ⟨z, θ⟩ := y
      have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ Work.Spaces.nbhU :=
        (Continuous.prodMk_left θ).continuousAt.eventually
          (Work.Spaces.isOpen_nbhU.mem_nhds hy)
      have heq : (fun z' => Work.Spaces.DzIter n (fun z θ => c * f z θ) z' θ) =ᶠ[𝓝 z]
          (fun z' => c * Work.Spaces.DzIter n f z' θ) := by
        filter_upwards [hnb] with z' hz'
        exact ih hz'
      have h1 : DifferentiableAt ℝ (fun z' => Work.Spaces.DzIter n f z' θ) z :=
        differentiableAt_slice_fst (Work.Spaces.SmoothNbhd.DzIter hf n) hy
      have hderiv : deriv (fun z' => Work.Spaces.DzIter n (fun z θ => c * f z θ) z' θ) z
          = c * deriv (fun z' => Work.Spaces.DzIter n f z' θ) z := by
        rw [heq.deriv_eq]
        exact deriv_const_mul c h1
      show z * deriv (fun z' => Work.Spaces.DzIter n (fun z θ => c * f z θ) z' θ) z
          = c * (z * deriv (fun z' => Work.Spaces.DzIter n f z' θ) z)
      rw [hderiv]; ring

/-- `D_θ^i(c·f) = c·D_θ^i f` on `nbhU`, for `SmoothNbhd f`. -/
private theorem DthIter_const_mul_nbh (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.SmoothNbhd f) (i : ℕ) :
    Set.EqOn (fun y : ℝ × ℝ => Work.Spaces.DthIter i (fun z θ => c * f z θ) y.1 y.2)
      (fun y : ℝ × ℝ => c * Work.Spaces.DthIter i f y.1 y.2) Work.Spaces.nbhU := by
  induction i with
  | zero => intro y hy; rfl
  | succ n ih =>
      intro y hy
      obtain ⟨z, θ⟩ := y
      have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ Work.Spaces.nbhU :=
        (Continuous.prodMk_right z).continuousAt.eventually
          (Work.Spaces.isOpen_nbhU.mem_nhds hy)
      have heq : (fun θ' => Work.Spaces.DthIter n (fun z θ => c * f z θ) z θ') =ᶠ[𝓝 θ]
          (fun θ' => c * Work.Spaces.DthIter n f z θ') := by
        filter_upwards [hnb] with θ' hθ'
        exact ih hθ'
      have h1 : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n f z θ') θ :=
        differentiableAt_slice_snd (Work.Spaces.SmoothNbhd.DthIter hf n) hy
      have hderiv : deriv (fun θ' => Work.Spaces.DthIter n (fun z θ => c * f z θ) z θ') θ
          = c * deriv (fun θ' => Work.Spaces.DthIter n f z θ') θ := by
        rw [heq.deriv_eq]
        exact deriv_const_mul c h1
      show Real.sin (2 * θ)
            * deriv (fun θ' => Work.Spaces.DthIter n (fun z θ => c * f z θ) z θ') θ
          = c * (Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter n f z θ') θ)
      rw [hderiv]; ring

/-- `D_z^jD_θ^i(c·f) = c·D_z^jD_θ^i f` on `nbhU`, for `SmoothNbhd f`. -/
private theorem mixed_const_mul_nbh (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.SmoothNbhd f) (j i : ℕ) {z θ : ℝ}
    (hy : (z, θ) ∈ Work.Spaces.nbhU) :
    Work.Spaces.mixed j i (fun z θ => c * f z θ) z θ
      = c * Work.Spaces.mixed j i f z θ := by
  have hEq : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i (fun z θ => c * f z θ)))
      (Function.uncurry (fun z θ => c * Work.Spaces.DthIter i f z θ)) Work.Spaces.nbhU := by
    intro y hy'
    obtain ⟨z', θ'⟩ := y
    simpa only [Function.uncurry] using DthIter_const_mul_nbh c hf i hy'
  have e1 : Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => c * f z θ)) z θ
      = Work.Spaces.DzIter j (fun z θ => c * Work.Spaces.DthIter i f z θ) z θ :=
    Work.Spaces.DzIter_congr hEq j hy
  have e2 : Work.Spaces.DzIter j (fun z θ => c * Work.Spaces.DthIter i f z θ) z θ
      = c * Work.Spaces.DzIter j (Work.Spaces.DthIter i f) z θ :=
    DzIter_const_mul_nbh c (Work.Spaces.SmoothNbhd.DthIter hf i) j hy
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (fun z θ => c * f z θ)) z θ
      = c * Work.Spaces.DzIter j (Work.Spaces.DthIter i f) z θ
  rw [e1, e2]

/-- The `ℋ^k`-integrand of a scalar multiple, for smooth `f`: it is `c²` times the
integrand of `f`. -/
theorem HkIntegrand_const_mul (α : ℝ) (k : ℕ) (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.SmoothNbhd f) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ
      = c ^ 2 * Work.Spaces.HkIntegrand α k f z θ := by
  have hy : (z, θ) ∈ Work.Spaces.nbhU := Work.Spaces.mem_nbhU hz hθ
  have hZ : ∀ i, Work.Spaces.DzIter i (fun z θ => c * f z θ) z θ
      = c * Work.Spaces.DzIter i f z θ := fun i => DzIter_const_mul_nbh c hf i hy
  have hM : ∀ j i, Work.Spaces.mixed j i (fun z θ => c * f z θ) z θ
      = c * Work.Spaces.mixed j i f z θ := fun j i => mixed_const_mul_nbh c hf j i hy
  have h1 : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => c * f z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      = c ^ 2 * ∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i f z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hZ i]; ring
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (fun z θ => c * f z θ) z θ * Work.Spaces.Wt α z θ) ^ 2
          else 0)
      = c ^ 2 * ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc, hM j i]; ring
    · rw [if_neg hc, if_neg hc, mul_zero]
  simp only [Work.Spaces.HkIntegrand]
  rw [h1, h2]; ring

/-- `Iz` is measurable. -/
theorem measurableSet_Iz_fts : MeasurableSet Work.Spaces.Iz := by
  simpa only [Work.Spaces.Iz] using measurableSet_Ici

/-- `Iθ` is measurable. -/
theorem measurableSet_Iθ_fts : MeasurableSet Work.Spaces.Iθ := by
  simpa only [Work.Spaces.Iθ] using measurableSet_Icc

/-- **`ℋ^k` is closed under multiplication by a scalar.** -/
theorem HkMem_smul (α : ℝ) (k : ℕ) (c : ℝ) {f : ℝ → ℝ → ℝ}
    (hf : Work.Spaces.SmoothNbhd f) (hm : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (fun z θ => c * f z θ) := by
  have hae : ∀ z ∈ Work.Spaces.Iz,
      (fun θ => Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
        =ᵐ[volume.restrict Work.Spaces.Iθ]
          (fun θ => c ^ 2 * Work.Spaces.HkIntegrand α k f z θ) :=
    fun z hz => (ae_restrict_mem measurableSet_Iθ_fts).mono
      (fun θ hθ => HkIntegrand_const_mul α k c hf hz hθ)
  have hzeq : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (fun z θ => c * f z θ) z θ)
        = c ^ 2 * ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ := by
    intro z hz
    rw [integral_congr_ae (hae z hz), integral_const_mul]
  exact ⟨fun z hz => ((hm.1 z hz).const_mul (c ^ 2)).congr (hae z hz).symm,
    IntegrableOn.congr_fun (hm.2.const_mul (c ^ 2)) (fun z hz => (hzeq z hz).symm)
      measurableSet_Iz_fts⟩

/-! ## Regularity of the derivative of a scalar multiple

`D_θ(c·f)` and `c·D_θf` agree on `(0,∞) × I_θ`, so each is in `HkReg α n` as soon as one
of them is; the membership of `c·D_θf` is the `HkMem`-closure under scalar multiplication
(`HkMem_smul`). -/





/-! ## The induction step -/


end Work.FTS.CoercivityStep.Step
