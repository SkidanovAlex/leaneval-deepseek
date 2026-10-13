import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.FstarHkAux
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.PsiInt_sq_mul_w_le_open
import Submission.Work.FTS.EllipticEst.FstarDzIter_sq_mul_w_le_open
import Submission.Work.Elliptic.SinSliceBounds
import Submission.Work.Spaces.SmoothCompact_Aux
import Submission.Work.FTS.EllipticEst.GbarSin.FstarDzIter_chain_open
import Submission.Work.FTS.EllipticEst.GbarSin.Fstar_local_integrableOn
import Submission.Work.FTS.EllipticEst.GbarSin.HkIntegrand_GbarSin_le
import Submission.Work.FTS.EllipticEst.GbarSin.continuousOn_HkIntegrand_radial_sin
import Submission.Work.FTS.EllipticEst.aestronglyMeasurable_integral_Itheta_Q0
import Submission.Work.FTS.EllipticEst.continuousOn_of_primitive_of_sqrt_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-!
# `F_*(F)·sin 2θ ∈ ℋ^k` for an open-quadrant smooth source `F`

This module proves

  `Work.FTS.EllipticEst.HkMem_FstarSin_open`:
for `0 < α ≤ 1`, a source `F` which is `C^∞` on the open quadrant
`Q0 = (0,∞) × (0,π/2)` (`Work.FTS.EllipticEst.SmoothOpen F`) and lies in the weighted space
`ℋ^k` (`Work.Spaces.HkMem α k F`), the angular moment `F_*(F)(z) = ∫_θ F(z,θ) sinθcos²θ dθ`
multiplied by the angular profile `sin 2θ` lies again in `ℋ^k`.

This is the open-quadrant analogue of `Work.FTS.EllipticEst.HkMem_FstarSin`
(`Fstar_sin_HkMem_HkNorm.lean`), which assumes the much stronger `Work.Spaces.SmoothNbhd F`.

## The route

* `F_*(F)(z)·sin 2θ` is a product `R(z)·χ(θ)` of a radial and an angular factor, so the two
  product rules `D_z^j (R(z)χ(θ)) = (rDzIter j R)(z)·χ(θ)` (`DzIter_mul_of_radial`) and
  `D_θ^i (R(z)χ(θ)) = R(z)·(D_θ^i χ)(0,θ)` (`DthIter_mul_of_angular`) turn the `ℋ^k`-integrand
  of the target into an explicit sum in which only the radial iterates `rDzIter j R` and the
  angular profiles `sinIter i = D_θ^i(sin 2θ)` occur (`HkIntegrand_GbarSin_eq`).
* The angular profiles are bounded against the weight (`sinIter_weight_bound`), which gives the
  pointwise bound `HkIntegrand α k (F_*·sin 2θ) z θ ≤ K·w(z)²·Σ_{j≤k}(rDzIter j F_* z)²` with
  `K` independent of `α`, of `F` and of the point (`HkIntegrand_FstarSin_le`).
* The radial iterates are the angular moments of the radial derivatives of `F`:
  `rDzIter j (F_*(F)) = F_*(D_z^j F)` on `(0,∞)` for `j ≤ k - 1` and a.e. for `j = k`
  (`rDzIter_Fstar_eq`, `rDzIter_Fstar_ae`).  This is an induction whose step is the fundamental
  theorem of calculus applied to the chain relation
  `F_*(D_z^j F) z - F_*(D_z^j F) s = ∫_{s}^{z} F_*(D_z^{j+1}F) r / r dr`
  (`GbarSin.FstarDzIter_chain_open`), the a.e. statement at the top level coming from the
  Lebesgue differentiation theorem (`LocallyIntegrable.ae_hasDerivAt_integral`).
* Cauchy–Schwarz on the angular slice bounds each moment by a single summand of the
  `ℋ^k`-integrand of `F` (`FstarDzIter_sq_mul_w_le_open`), and those summands are dominated by
  the `θ`-integral of that integrand, which is integrable by hypothesis (`hmem`).

The two halves of `HkMem` are then obtained directly: the `θ`-slices of the target integrand are
bounded (by the explicit form above) hence integrable for every `z ∈ Iz`, and the `z`-integral of
the slices is a.e. dominated by a constant multiple of the slice-integral of the source's
`ℋ^k`-integrand, which is integrable.
-/

/-! ## Elementary facts -/

/-- `F_*(D_z^j F)` is `PsiInt F j`, definitionally. -/
theorem PsiInt_eq_Fstar_DzIter (F : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) :
    PsiInt F j z = Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z := rfl

/-- `(0,∞)` and `Iz = [0,∞)` carry the same restricted Lebesgue measure. -/
theorem restrict_Ioi_eq_restrict_Iz :
    volume.restrict (Set.Ioi (0 : ℝ)) = volume.restrict Work.Spaces.Iz := by
  rw [show Work.Spaces.Iz = Set.Ici (0 : ℝ) from rfl]
  exact Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici

/-- The integral of a constant over `Iθ`. -/
theorem integral_const_Iθ (c : ℝ) : (∫ θ in Work.Spaces.Iθ, c) = (π / 2) * c := by
  rw [Work.Spaces.Iθ, MeasureTheory.setIntegral_const, smul_eq_mul]
  have hvol : volume.real (Set.Icc (0 : ℝ) (π / 2)) = π / 2 := by
    rw [MeasureTheory.measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), sub_zero]
  rw [hvol]

/-- `sinθcos²θ` is continuous on `Iθ`. -/
theorem continuousOn_sinCos2_Iθ : ContinuousOn Work.Elliptic.sinCos2 Work.Spaces.Iθ := by
  unfold Work.Elliptic.sinCos2
  fun_prop

/-- The `j`-th weighted `L²`-slice of the source,
`A_j(z) = ∫_θ (D_z^j F(z,θ)·w(z)/sin(2θ)^{η/2})² dθ`. -/
noncomputable def AjF (F : ℝ → ℝ → ℝ) (j : ℕ) : ℝ → ℝ :=
  fun z => ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.DzIter j F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2

@[simp] theorem AjF_apply (F : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) :
    AjF F j z = ∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.DzIter j F z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := rfl

theorem AjF_nonneg (F : ℝ → ℝ → ℝ) (j : ℕ) (z : ℝ) : 0 ≤ AjF F j z :=
  integral_nonneg fun θ => sq_nonneg _

/-! ## The weighted slices `A_j` and the angular moments -/

/-- The `j`-th summand of the `ℋ^k`-integrand is dominated by the whole `ℋ^k`-integrand. -/
theorem AjF_le_HkIntegrand_integral (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    AjF F j z ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ := by
  rw [AjF_apply]
  exact integral_mono_of_nonneg (Eventually.of_forall fun θ => sq_nonneg _) (hmem.1 z hz)
    (Eventually.of_forall fun θ => Work.Spaces.sq_le_HkIntegrand_z α k F z θ j hj)

/-- The weighted slice `A_j` is a.e. strongly measurable. -/
theorem AjF_aesm (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F) (j : ℕ) :
    AEStronglyMeasurable (AjF F j) (volume.restrict (Set.Ioi 0)) := by
  have hg : ContinuousOn (fun p : ℝ × ℝ => (Work.Spaces.DzIter j F p.1 p.2
      * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2) Q0 :=
    (hF.continuousOn_summand j).pow 2
  have h := aestronglyMeasurable_integral_Itheta_Q0
    (fun z θ : ℝ => (Work.Spaces.DzIter j F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    hg (fun _ : ℝ => (1 : ℝ)) continuousOn_const
  show AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
    (Work.Spaces.DzIter j F z θ
      * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
    (volume.restrict (Set.Ioi 0))
  simpa only [mul_one] using h

/-- The angular moment `z ↦ F_*(D_z^j F)(z)` is a.e. strongly measurable. -/
theorem PsiInt_aesm (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F) (j : ℕ) :
    AEStronglyMeasurable (fun z => PsiInt F j z) (volume.restrict (Set.Ioi 0)) := by
  have hg : ContinuousOn (Function.uncurry (Work.Spaces.DzIter j F)) Q0 :=
    (hF.DzIter j).continuousOn
  have h := aestronglyMeasurable_integral_Itheta_Q0 (Work.Spaces.DzIter j F) hg
    Work.Elliptic.sinCos2 continuousOn_sinCos2_Iθ
  show AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ,
    Work.Spaces.DzIter j F z θ * Work.Elliptic.sinCos2 θ) (volume.restrict (Set.Ioi 0))
  simpa only [PsiInt, mul_one] using h

/-- The slice functional `A_j` is integrable on `(0,∞)`. -/
theorem AjF_integrableOn (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) :
    IntegrableOn (AjF F j) (Set.Ioi 0) := by
  have hmaj : IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k F z θ) (Set.Ioi 0) := by
    show Integrable _ (volume.restrict (Set.Ioi 0))
    rw [restrict_Ioi_eq_restrict_Iz]
    exact hmem.2
  refine hmaj.mono' (AjF_aesm α k F hF j) ?_
  show ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
    ‖AjF F j z‖ ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ
  rw [ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun z hz => ?_
  have hzI : z ∈ Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]; exact le_of_lt (Set.mem_Ioi.mp hz)
  rw [Real.norm_of_nonneg (AjF_nonneg F j z)]
  exact AjF_le_HkIntegrand_integral α k F hmem j hj hzI

/-! ## Cauchy–Schwarz for the angular moment -/

/-- The Cauchy–Schwarz bound `(F_*(D_z^j F) z)² w(z)² ≤ (π/2)A_j(z)`, in the form of a bound
on the absolute value of the moment. -/
theorem PsiInt_sqrt_bound (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) {z : ℝ} (hz : 0 < z) :
    |PsiInt F j z| ≤ Real.sqrt (π / 2) * Real.sqrt (AjF F j z) / Work.Spaces.w z := by
  have hsq : (PsiInt F j z) ^ 2 * (Work.Spaces.w z) ^ 2 ≤ (π / 2) * AjF F j z := by
    rw [PsiInt_eq_Fstar_DzIter, AjF_apply]
    exact FstarDzIter_sq_mul_w_le_open α k F hF hmem j hj hz
  have hA0 : 0 ≤ AjF F j z := AjF_nonneg F j z
  have hw0 : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
  have hdiv : (PsiInt F j z) ^ 2 ≤ ((π / 2) * AjF F j z) / (Work.Spaces.w z) ^ 2 :=
    (le_div_iff₀ (pow_pos hw0 2)).mpr hsq
  have hTnn : 0 ≤ Real.sqrt (π / 2) * Real.sqrt (AjF F j z) / Work.Spaces.w z := by positivity
  have hTsq : (Real.sqrt (π / 2) * Real.sqrt (AjF F j z) / Work.Spaces.w z) ^ 2
      = ((π / 2) * AjF F j z) / (Work.Spaces.w z) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hA0]
  have hU2 : (PsiInt F j z) ^ 2
      ≤ (Real.sqrt (π / 2) * Real.sqrt (AjF F j z) / Work.Spaces.w z) ^ 2 := by
    rw [hTsq]; exact hdiv
  calc |PsiInt F j z| = Real.sqrt ((PsiInt F j z) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((Real.sqrt (π / 2) * Real.sqrt (AjF F j z) / Work.Spaces.w z) ^ 2) :=
        Real.sqrt_le_sqrt hU2
    _ = Real.sqrt (π / 2) * Real.sqrt (AjF F j z) / Work.Spaces.w z := Real.sqrt_sq hTnn

/-! ## Continuity of the angular moments -/

/-- **Continuity of the angular moments.**  For `j + 1 ≤ k` the moment `F_*(D_z^j F)` is
continuous on `(0,∞)`: by the chain relation it is the primitive of `F_*(D_z^{j+1}F)/r`, which
obeys the weighted square-root bound with the integrable majorant `A_{j+1}`. -/
theorem PsiInt_continuousOn (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 1 ≤ k) :
    ContinuousOn (fun z => PsiInt F j z) (Set.Ioi 0) := by
  refine continuousOn_of_primitive_of_sqrt_bound (u := fun z => PsiInt F j z)
    (v := fun z => PsiInt F (j + 1) z) (A := AjF F (j + 1))
    (AjF_integrableOn α k F hF hmem (j + 1) hj) ?_ ?_
  · intro r hr
    exact PsiInt_sqrt_bound α k F hF hmem (j + 1) hj hr
  · intro s z hs hsz
    exact Work.FTS.EllipticEst.GbarSin.FstarDzIter_chain_open α k F hF hmem j hj hs hsz

/-! ## Local integrability of the moment density `F_*(D_z^j F)/r` -/

/-- `F_*(D_z^j F)(r)/r` is integrable on `(0,b)` for `b > 0`: the weighted square-root
bound `√x ≤ 1 + x` and the integrability of `A_j` give an `L¹` majorant. -/
theorem PsiInt_div_integrableOn (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun r => PsiInt F j r / r) (Set.Ioo 0 b) := by
  have hsub : Set.Ioo (0 : ℝ) b ⊆ Set.Ioi (0 : ℝ) := fun x hx => hx.1
  -- the majorant `√(π/2)·(1 + A_j)` on `(0,b)`
  have hAint : IntegrableOn (AjF F j) (Set.Ioo 0 b) :=
    (AjF_integrableOn α k F hF hmem j hj).mono_set hsub
  have hconst : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Ioo 0 b) := by
    refine integrableOn_const ?_
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_ne_top
  have hmaj : IntegrableOn (fun r => Real.sqrt (π / 2) * (1 + AjF F j r)) (Set.Ioo 0 b) :=
    (hconst.add hAint).const_mul (Real.sqrt (π / 2))
  have haesm : AEStronglyMeasurable (fun r => PsiInt F j r / r)
      (volume.restrict (Set.Ioo 0 b)) :=
    ((PsiInt_aesm F hF j).mono_measure (Measure.restrict_mono hsub le_rfl)).mul
      (measurable_id.inv.aestronglyMeasurable)
  refine Integrable.mono' hmaj haesm ?_
  rw [ae_restrict_iff' measurableSet_Ioo]
  refine Eventually.of_forall fun r hr => ?_
  have hr0 : 0 < r := hr.1
  have hbd := PsiInt_sqrt_bound α k F hF hmem j hj hr0
  have hA0 : 0 ≤ AjF F j r := AjF_nonneg F j r
  have hsqrt : Real.sqrt (AjF F j r) ≤ 1 + AjF F j r := by
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith⟩
  have hwr : (Work.Spaces.w r * r)⁻¹ = r / (1 + r) ^ 2 := by
    rw [Work.Spaces.w]; field_simp
  have hratio : r / (1 + r) ^ 2 ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith [hr0.le]
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hr0]
  calc |PsiInt F j r| / r
      ≤ (Real.sqrt (π / 2) * Real.sqrt (AjF F j r) / Work.Spaces.w r) / r :=
        div_le_div_of_nonneg_right hbd hr0.le
    _ = Real.sqrt (π / 2) * Real.sqrt (AjF F j r) * (r / (1 + r) ^ 2) := by
        rw [div_div, div_eq_mul_inv, hwr]
    _ ≤ Real.sqrt (π / 2) * Real.sqrt (AjF F j r) * 1 :=
        mul_le_mul_of_nonneg_left hratio (by positivity)
    _ ≤ Real.sqrt (π / 2) * (1 + AjF F j r) := by
        have := mul_le_mul_of_nonneg_left hsqrt (Real.sqrt_nonneg (π / 2))
        linarith [this]

/-! ## The extended density and its local integrability -/

/-- The density `F_*(D_z^j F)(r)/r`, extended by `0` to the nonpositive half-line, is locally
integrable on `ℝ`. -/
theorem locallyIntegrable_PsiInt_div (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) :
    LocallyIntegrable (fun r : ℝ => if 0 < r then PsiInt F j r / r else 0) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨N, hN⟩ := hK.bddAbove
  obtain ⟨M, hM⟩ := hK.bddBelow
  set R : ℝ := max |M| |N| with hR
  have hR0 : 0 ≤ R := le_trans (abs_nonneg M) (le_max_left _ _)
  have hsub : K ⊆ Set.Ioo (-(R + 1)) (R + 1) := by
    intro x hx
    have hxN : x ≤ N := hN hx
    have hxM : M ≤ x := hM hx
    have h1 : -M ≤ R := le_trans (neg_le_abs M) (le_max_left _ _)
    have h2 : N ≤ R := le_trans (le_abs_self N) (le_max_right _ _)
    exact ⟨by linarith [h1, hxM], by linarith [hxN, h2]⟩
  set g : ℝ → ℝ := fun r => if 0 < r then PsiInt F j r / r else 0 with hg
  have hset : Set.Ioo (-(R + 1)) (R + 1)
      = (Set.Ioo (-(R + 1)) 0 ∪ Set.Ioo 0 (R + 1)) ∪ {0} := by
    ext x
    constructor
    · intro hx
      rcases lt_trichotomy x 0 with h | h | h
      · exact Or.inl (Or.inl ⟨hx.1, h⟩)
      · exact Or.inr h
      · exact Or.inl (Or.inr ⟨h, hx.2⟩)
    · rintro ((⟨h1, h2⟩ | ⟨h3, h4⟩) | h5)
      · exact ⟨h1, by linarith [h2, hR0]⟩
      · exact ⟨by linarith [h3, hR0], h4⟩
      · rw [Set.mem_singleton_iff.mp h5]; exact ⟨by linarith [hR0], by linarith [hR0]⟩
  have hA : IntegrableOn g (Set.Ioo (-(R + 1)) 0) :=
    (integrableOn_zero).congr_fun (fun x hx => by
      simp only [hg, if_neg (not_lt.mpr hx.2.le)]) measurableSet_Ioo
  have hB : IntegrableOn g (Set.Ioo 0 (R + 1)) :=
    (PsiInt_div_integrableOn α k F hF hmem j hj (b := R + 1) (by linarith)).congr_fun
      (fun x hx => by simp only [hg, if_pos hx.1]) measurableSet_Ioo
  have hC : IntegrableOn g ({0} : Set ℝ) := integrableOn_singleton (by simp) (by simp)
  have hbig : IntegrableOn g (Set.Ioo (-(R + 1)) (R + 1)) := by
    rw [hset]
    exact (hA.union hB).union hC
  exact hbig.mono_set hsub

/-! ## Differentiation of the angular moments in the interior -/

/-- **The derivative of the angular moments.**  For `j + 2 ≤ k` the moment `F_*(D_z^j F)` is
differentiable at every `z > 0` with derivative `F_*(D_z^{j+1}F)(z)/z`: its increments are the
integral of `F_*(D_z^{j+1}F)(r)/r` (the chain relation) and that density is continuous at `z`
because `F_*(D_z^{j+1}F)` is continuous (`j + 2 ≤ k`). -/
theorem hasDerivAt_PsiInt (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 2 ≤ k) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (fun u => PsiInt F j u) (PsiInt F (j + 1) z / z) z := by
  set a : ℝ := z / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have haz : a < z := by rw [ha]; linarith
  have hchain : ∀ s u : ℝ, 0 < s → s ≤ u →
      PsiInt F j u - PsiInt F j s = ∫ r in s..u, PsiInt F (j + 1) r / r :=
    fun s u hs hsu => GbarSin.FstarDzIter_chain_open α k F hF hmem j (by omega) hs hsu
  have hcont : ContinuousOn (fun r => PsiInt F (j + 1) r / r) (Set.Ioi 0) :=
    (PsiInt_continuousOn α k F hF hmem (j + 1) (by omega)).div continuousOn_id
      (fun r hr => ne_of_gt hr)
  have hmeas : StronglyMeasurableAtFilter (fun r => PsiInt F (j + 1) r / r) (𝓝 z) volume :=
    _root_.AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
      ((PsiInt_aesm F hF (j + 1)).mul measurable_id.inv.aestronglyMeasurable)
      (isOpen_Ioi.mem_nhds hz)
  have hint : IntervalIntegrable (fun r => PsiInt F (j + 1) r / r) volume a z := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le haz.le]
    exact (PsiInt_div_integrableOn α k F hF hmem (j + 1) (by omega) (b := 2 * z)
      (by linarith)).mono_set (fun x hx => ⟨by linarith [ha0, hx.1], by linarith [hx.2, hz]⟩)
  have hderiv := intervalIntegral.integral_hasDerivAt_right hint hmeas
    (hcont.continuousAt (isOpen_Ioi.mem_nhds hz))
  have hev : (fun u : ℝ => PsiInt F j u) =ᶠ[𝓝 z]
      (fun u => (∫ r in a..u, PsiInt F (j + 1) r / r) + PsiInt F j a) := by
    filter_upwards [Ioi_mem_nhds haz] with u hu
    have h := hchain a u ha0 hu.le
    linarith
  exact (hderiv.add_const _).congr_of_eventuallyEq hev

/-! ## The a.e. derivative identity (Lebesgue differentiation) -/

/-- **The a.e. derivative identity.**  For `j + 1 ≤ k`, almost everywhere on `(0,∞)` the
derivative of the moment `F_*(D_z^j F)` is `F_*(D_z^{j+1}F)/z`.  This is the Lebesgue
differentiation theorem applied to the chain relation (no continuity of the top level moment is
available, so the statement is only a.e.). -/
theorem ae_deriv_PsiInt (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j + 1 ≤ k) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      deriv (fun u => PsiInt F j u) z = PsiInt F (j + 1) z / z := by
  set g : ℝ → ℝ := fun r => if 0 < r then PsiInt F (j + 1) r / r else 0 with hg
  have hae : ∀ᵐ z ∂(volume : Measure ℝ), ∀ c, HasDerivAt (fun u => ∫ x in c..u, g x) (g z) z :=
    LocallyIntegrable.ae_hasDerivAt_integral (locallyIntegrable_PsiInt_div α k F hF hmem (j + 1) hj)
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hae] with z hzall
  intro hzmem
  have hz : 0 < z := hzmem
  set a : ℝ := z / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have haz : a < z := by rw [ha]; linarith
  have hev : (fun u : ℝ => PsiInt F j u) =ᶠ[𝓝 z]
      (fun u => (∫ x in a..u, g x) + PsiInt F j a) := by
    filter_upwards [Ioi_mem_nhds haz] with u hu
    have h1 : PsiInt F j u - PsiInt F j a = ∫ r in a..u, PsiInt F (j + 1) r / r :=
      GbarSin.FstarDzIter_chain_open α k F hF hmem j hj ha0 hu.le
    have h2 : (∫ r in a..u, PsiInt F (j + 1) r / r) = ∫ x in a..u, g x := by
      refine intervalIntegral.integral_congr (μ := volume) ?_
      rw [Set.uIcc_of_le (le_of_lt hu)]
      intro x hx
      have hx0 : 0 < x := by linarith [ha0, hx.1]
      show PsiInt F (j + 1) x / x = g x
      simp only [hg, if_pos hx0]
    rw [h2] at h1
    linarith
  have hder := (hzall a).add_const (PsiInt F j a)
  rw [Filter.EventuallyEq.deriv_eq hev, hder.deriv]
  simp only [hg, if_pos hz]

/-! ## The radial iterates of the moment are the angular moments -/

/-- **`D_z^j F_* = F_*(D_z^j F)` on `(0,∞)` for `j ≤ k - 1`.** -/
theorem rDzIter_Fstar_eq_PsiInt (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) :
    ∀ j : ℕ, j ≤ k - 1 → ∀ z ∈ Set.Ioi (0 : ℝ),
      rDzIter j (fun z => Work.Elliptic.Fstar F z) z = PsiInt F j z := by
  intro j
  induction j with
  | zero => intro _ z _; exact (PsiInt_eq_Fstar_DzIter F 0 z).symm
  | succ n ih =>
      intro hn z hz
      have hnk : n ≤ k - 1 := by omega
      have hev : (fun u => rDzIter n (fun z => Work.Elliptic.Fstar F z) u) =ᶠ[𝓝 z]
          (fun u => PsiInt F n u) := by
        filter_upwards [Ioi_mem_nhds hz] with u hu
        exact ih hnk u hu
      have hder := hasDerivAt_PsiInt α k F hF hmem n (by omega) hz
      rw [rDzIter_succ, rDz, Filter.EventuallyEq.deriv_eq hev, hder.deriv,
        mul_div_cancel₀ _ (ne_of_gt hz)]

/-- **`D_z^k F_* = F_*(D_z^k F)` a.e. on `(0,∞)`.**  Unlike the lower levels, the identity at the
top level is only available almost everywhere: the derivative of `F_*(D_z^{k-1}F)` is
`F_*(D_z^kF)/z` only a.e. (Lebesgue differentiation). -/
theorem rDzIter_Fstar_eq_PsiInt_ae (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) :
    ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      rDzIter k (fun z => Work.Elliptic.Fstar F z) z = PsiInt F k z := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk
    filter_upwards with z
    exact (PsiInt_eq_Fstar_DzIter F 0 z).symm
  · have hk2 : k = (k - 1) + 1 := by omega
    have hev := ae_deriv_PsiInt α k F hF hmem (k - 1) (by omega)
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at hev
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    filter_upwards [hev] with z hz
    intro hzmem
    have hevfun : (fun u => rDzIter (k - 1) (fun z => Work.Elliptic.Fstar F z) u) =ᶠ[𝓝 z]
        (fun u => PsiInt F (k - 1) u) := by
      filter_upwards [Ioi_mem_nhds hzmem] with u hu
      exact rDzIter_Fstar_eq_PsiInt α k F hF hmem (k - 1) (by omega) u hu
    rw [hk2, rDzIter_succ, rDz, Filter.EventuallyEq.deriv_eq hevfun, hz hzmem,
      mul_div_cancel₀ _ (ne_of_gt hzmem)]

/-! ## Measurability of the radial powers `x ↦ x ^ c` -/

/-- The real power function `x ↦ x ^ c` is measurable (for every real exponent). -/
theorem measurable_rpow_const (c : ℝ) : Measurable (fun x : ℝ => x ^ c) := by
  have hsplit : (fun x : ℝ => x ^ c) = fun x => if 0 ≤ x then
      (if x = 0 then (if c = 0 then 1 else 0) else Real.exp (Real.log x * c))
      else Real.exp (Real.log x * c) * Real.cos (c * Real.pi) := by
    funext x
    by_cases hx : 0 ≤ x
    · rw [if_pos hx, Real.rpow_def_of_nonneg hx]
    · rw [if_neg hx, Real.rpow_def_of_neg (lt_of_not_ge hx)]
  rw [hsplit]
  refine Measurable.ite measurableSet_Ici ?_ ?_
  · refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
    exact Real.measurable_exp.comp (Real.measurable_log.mul measurable_const)
  · exact (Real.measurable_exp.comp (Real.measurable_log.mul measurable_const)).mul measurable_const

/-- `θ ↦ sin(2θ)^c` is measurable. -/
theorem measurable_sin_two_rpow (c : ℝ) : Measurable (fun θ : ℝ => (Real.sin (2 * θ)) ^ c) :=
  (measurable_rpow_const c).comp (by fun_prop)

/-! ## The pointwise `ℋ^k`-integrand bound for a radial profile times `sin 2θ` -/

/-- **Pointwise bound for the `ℋ^k`-integrand of `R(z)·sin 2θ`.**  For every radial profile `R`
and every `0 < α ≤ 1`,

  `HkIntegrand α k (R(z)·sin 2θ) z θ ≤ K_k · w(z)² · Σ_{j ≤ k} (D_z^j R(z))²`

with `K_k` independent of `α`, of `R` and of the point. -/
theorem HkIntegrand_radial_sin_le (k : ℕ) : ∃ K : ℝ, 0 ≤ K ∧ ∀ (α : ℝ) (R : ℝ → ℝ),
    0 < α → α ≤ 1 → ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (fun z θ => R z * Real.sin (2 * θ)) z θ
        ≤ K * (Work.Spaces.w z) ^ 2 *
            ∑ j ∈ Finset.range (k + 1), (rDzIter j R z) ^ 2 := by
  classical
  let C : ℕ → ℝ := fun i => Classical.choose (sinIter_weight_bound i)
  have hCnn : ∀ i, 0 ≤ C i := fun i => (Classical.choose_spec (sinIter_weight_bound i)).1
  have hCb : ∀ i (α : ℝ), 0 < α → α ≤ 1 → ∀ θ ∈ Work.Spaces.Iθ,
      (sinIter i θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) ≤ C i :=
    fun i => (Classical.choose_spec (sinIter_weight_bound i)).2
  refine ⟨1 + ∑ i ∈ Finset.range (k + 1), C i, ?_, ?_⟩
  · have h0 : 0 ≤ ∑ i ∈ Finset.range (k + 1), C i := Finset.sum_nonneg fun i _ => hCnn i
    linarith
  · intro α R hα hα1 z hz θ hθ
    have hsin_nn : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hsin_le : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have heta0 : (0 : ℝ) < Work.Spaces.eta := by norm_num [Work.Spaces.eta]
    have heta2 : Work.Spaces.eta ≤ 2 := by norm_num [Work.Spaces.eta]
    have hA := sum_sq_first_le k (fun i => rDzIter i R z) (Work.Spaces.w z) (Real.sin (2 * θ))
      Work.Spaces.eta heta0 heta2 hsin_nn hsin_le
    have hB := sum_sq_second_le k (fun j => rDzIter j R z) C (fun i => sinIter i θ)
      (Work.Spaces.w z) (Real.sin (2 * θ)) (Work.Spaces.gam α) hsin_nn hCnn
      (fun i _ => hCb i α hα hα1 θ hθ)
    rw [GbarSin.HkIntegrand_GbarSin_eq α k R z θ]
    simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
    refine le_trans (add_le_add hA hB) (le_of_eq ?_)
    ring

/-! ## Measurability of the `ℋ^k`-integrand of `R(z)·sin 2θ` (fixed `z`) -/

/-- For fixed `z` the `ℋ^k`-integrand of `R(z)·sin 2θ` is a measurable function of the angle. -/
theorem measurable_HkIntegrand_radial_sin (α : ℝ) (k : ℕ) (R : ℝ → ℝ) (z : ℝ) :
    Measurable (fun θ => Work.Spaces.HkIntegrand α k
      (fun z θ => R z * Real.sin (2 * θ)) z θ) := by
  have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
  have hratio : Measurable (fun θ : ℝ =>
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) :=
    (measurable_sin_two_rpow (Work.Spaces.eta / 2)).inv.const_mul (Work.Spaces.w z)
  have hWt : Measurable (fun θ : ℝ => Work.Spaces.Wt α z θ) := by
    simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
    exact (measurable_sin_two_rpow (-(Work.Spaces.gam α / 2))).const_mul (Work.Spaces.w z)
  have hsinIter : ∀ i : ℕ, Measurable (sinIter i) := fun i =>
    (GbarSin.continuous_sinIter i).measurable
  have hfun : (fun θ => Work.Spaces.HkIntegrand α k (fun z θ => R z * Real.sin (2 * θ)) z θ)
      = fun θ => (∑ i ∈ Finset.range (k + 1), (rDzIter i R z * Real.sin (2 * θ)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        + ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              (rDzIter j R z * sinIter i θ * Work.Spaces.Wt α z θ) ^ 2 else 0) := by
    funext θ
    exact GbarSin.HkIntegrand_GbarSin_eq α k R z θ
  rw [hfun]
  refine Measurable.add ?_ ?_
  · refine Finset.measurable_sum _ fun i _ => ?_
    have h1 : Measurable (fun θ : ℝ => rDzIter i R z * (Real.sin (2 * θ)
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) :=
      (hsin.mul hratio).const_mul _
    simpa only [mul_assoc] using h1.pow_const 2
  · refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · have hif : (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ k then
          (rDzIter j R z * sinIter i θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          = fun θ => (rDzIter j R z * sinIter i θ * Work.Spaces.Wt α z θ) ^ 2 := by
        funext θ; rw [if_pos hc]
      rw [hif]
      have h1 : Measurable (fun θ : ℝ => rDzIter j R z
          * (sinIter i θ * Work.Spaces.Wt α z θ)) :=
        (hsinIter i).mul hWt |>.const_mul _
      simpa only [mul_assoc] using h1.pow_const 2
    · have hif : (fun θ : ℝ => (if 1 ≤ i ∧ i + j ≤ k then
          (rDzIter j R z * sinIter i θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          = fun _ => (0 : ℝ) := by
        funext θ; rw [if_neg hc]
      rw [hif]
      exact measurable_const

/-! ## The `θ`-slices of the target integrand are integrable -/

/-- **Clause one of `ℋ^k`-membership**: for every `z ∈ Iz` the `θ`-slice of the `ℋ^k`-integrand
of `F_*(F)·sin 2θ` is integrable on `Iθ`.  The slice is measurable
(`measurable_HkIntegrand_radial_sin`) and bounded by the constant
`K·w(z)²·Σ_{j≤k}(D_z^jF_*(z))²` (`HkIntegrand_radial_sin_le`). -/
theorem integrableOn_HkIntegrand_fstarSin_slice (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) {z : ℝ} (hz : z ∈ Work.Spaces.Iz) :
    IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k
      (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ) Work.Spaces.Iθ := by
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · subst hz0
    rw [show (fun θ => Work.Spaces.HkIntegrand α k
        (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) 0 θ) = fun _ => (0 : ℝ) from
      funext fun θ => by simp [Work.Spaces.HkIntegrand, Work.Spaces.Wt, Work.Spaces.w]]
    exact integrableOn_zero
  · obtain ⟨K, hKnn, hK⟩ := HkIntegrand_radial_sin_le k
    have hsin_int : IntegrableOn (fun _ : ℝ => K * (Work.Spaces.w z) ^ 2 *
        ∑ j ∈ Finset.range (k + 1), (rDzIter j (fun z => Work.Elliptic.Fstar F z) z) ^ 2)
        Work.Spaces.Iθ :=
      integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
    refine Integrable.mono' hsin_int
      ((measurable_HkIntegrand_radial_sin α k (fun z => Work.Elliptic.Fstar F z) z).aestronglyMeasurable)
      ?_
    rw [ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from by
      rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
    refine Eventually.of_forall fun θ hθ => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (Work.Spaces.HkIntegrand_nonneg α k _ z θ)]
    exact hK α (fun z => Work.Elliptic.Fstar F z) hα hα1 z hz θ hθ

/-! ## Almost everywhere strong measurability of the radial iterates of `F_*` -/

/-- The radial iterates `D_z^j F_*` are a.e. strongly measurable for `j ≤ k` (they are the
angular moments `F_*(D_z^j F)`). -/
theorem rDzIter_Fstar_aesm (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hF : SmoothOpen F)
    (hmem : Work.Spaces.HkMem α k F) (j : ℕ) (hj : j ≤ k) :
    AEStronglyMeasurable (fun z => rDzIter j (fun z => Work.Elliptic.Fstar F z) z)
      (volume.restrict Work.Spaces.Iz) := by
  rw [← restrict_Ioi_eq_restrict_Iz]
  rcases lt_or_eq_of_le hj with hj' | hj'
  · refine (PsiInt_aesm F hF j).aemeasurable.congr ?_ |>.aestronglyMeasurable
    rw [Filter.EventuallyEq, MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
    exact Eventually.of_forall fun z hz =>
      (rDzIter_Fstar_eq_PsiInt α k F hF hmem j (by omega) z hz).symm
  · refine (PsiInt_aesm F hF j).aemeasurable.congr ?_ |>.aestronglyMeasurable
    have hk : (fun z => rDzIter k (fun z => Work.Elliptic.Fstar F z) z)
        =ᵐ[volume.restrict (Set.Ioi 0)] (fun z => PsiInt F k z) :=
      rDzIter_Fstar_eq_PsiInt_ae α k F hF hmem
    rw [hj']
    exact hk.symm

/-! ## Joint a.e. strong measurability of the target integrand -/

/-- The uncurried `ℋ^k`-integrand of `F_*(F)·sin 2θ` is a.e. strongly measurable for the product
of the restricted measures. -/
theorem aestronglyMeasurable_HkIntegrand_fstarSin_joint (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ)
    (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k
        (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  set R : ℝ → ℝ := fun z => Work.Elliptic.Fstar F z with hR
  set μ : Measure ℝ := volume.restrict Work.Spaces.Iz with hμ
  set ν : Measure ℝ := volume.restrict Work.Spaces.Iθ with hν
  have hwmeas : Measurable (fun z : ℝ => Work.Spaces.w z) := by
    have h : (fun z : ℝ => Work.Spaces.w z) = fun z => (1 + z) ^ 2 * (z ^ 2)⁻¹ := rfl
    rw [h]
    exact (((measurable_const.add measurable_id).pow_const 2).mul
      ((measurable_id.pow_const 2).inv))
  -- the radial pieces are the `D_z^j F_*`, the angular pieces are explicit in `θ`
  have hz : ∀ j : ℕ, j ≤ k → AEStronglyMeasurable (fun p : ℝ × ℝ => rDzIter j R p.1) (μ.prod ν) :=
    fun j hj => (rDzIter_Fstar_aesm α k F hF hmem j hj).comp_fst
  have hsin : Measurable (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
  have hA : Measurable (fun θ : ℝ =>
      Real.sin (2 * θ) / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) :=
    hsin.div (measurable_sin_two_rpow (Work.Spaces.eta / 2))
  have hB : ∀ i : ℕ, Measurable (fun θ : ℝ =>
      sinIter i θ * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α / 2))) := fun i =>
    (GbarSin.continuous_sinIter i).measurable.mul (measurable_sin_two_rpow _)
  have hsum1 : AEStronglyMeasurable (∑ i ∈ Finset.range (k + 1), fun p : ℝ × ℝ =>
        (rDzIter i R p.1 * Work.Spaces.w p.1) ^ 2
          * (Real.sin (2 * p.2) / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) ^ 2)
      (μ.prod ν) := by
    refine Finset.aestronglyMeasurable_sum (Finset.range (k + 1)) (fun i hi => ?_)
    have hi' : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => rDzIter i R p.1 * Work.Spaces.w p.1)
        (μ.prod ν) :=
      (hz i hi').mul (hwmeas.aestronglyMeasurable.comp_fst)
    have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
        Real.sin (2 * p.2) / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2)) (μ.prod ν) :=
      hA.aestronglyMeasurable.comp_snd
    exact (h1.pow 2).mul (h2.pow 2)
  have hsum2 : AEStronglyMeasurable (∑ i ∈ Finset.range (k + 1),
        ∑ j ∈ Finset.range (k + 1), fun p : ℝ × ℝ =>
          (if 1 ≤ i ∧ i + j ≤ k then
            ((rDzIter j R p.1 * Work.Spaces.w p.1) ^ 2
              * (sinIter i p.2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) ^ 2)
          else 0)) (μ.prod ν) := by
    refine Finset.aestronglyMeasurable_sum (Finset.range (k + 1)) (fun i hi =>
      Finset.aestronglyMeasurable_sum (Finset.range (k + 1)) (fun j hj => ?_))
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · have hif : (fun p : ℝ × ℝ =>
          (if 1 ≤ i ∧ i + j ≤ k then
            ((rDzIter j R p.1 * Work.Spaces.w p.1) ^ 2
              * (sinIter i p.2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) ^ 2)
          else 0))
          = fun p : ℝ × ℝ => ((rDzIter j R p.1 * Work.Spaces.w p.1) ^ 2
              * (sinIter i p.2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) ^ 2) := by
        funext p; rw [if_pos hc]
      rw [hif]
      have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => rDzIter j R p.1 * Work.Spaces.w p.1)
          (μ.prod ν) :=
        (hz j hj').mul (hwmeas.aestronglyMeasurable.comp_fst)
      have h2 : AEStronglyMeasurable (fun p : ℝ × ℝ =>
          sinIter i p.2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) (μ.prod ν) :=
        (hB i).aestronglyMeasurable.comp_snd
      exact (h1.pow 2).mul (h2.pow 2)
    · have hif : (fun p : ℝ × ℝ =>
          (if 1 ≤ i ∧ i + j ≤ k then
            ((rDzIter j R p.1 * Work.Spaces.w p.1) ^ 2
              * (sinIter i p.2 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2))) ^ 2)
          else 0)) = fun _ => (0 : ℝ) := by
        funext p; rw [if_neg hc]
      rw [hif]
      exact aestronglyMeasurable_const
  have hmain := hsum1.add hsum2
  refine (hmain.aemeasurable.congr ?_).aestronglyMeasurable
  rw [Filter.EventuallyEq]
  filter_upwards with p
  simp only [Pi.add_apply, Finset.sum_apply]
  rw [GbarSin.HkIntegrand_GbarSin_eq α k R p.1 p.2]
  simp only [Work.Spaces.Wt, Work.Spaces.wTheta]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : 1 ≤ i ∧ i + j ≤ k
    · rw [if_pos hc, if_pos hc]; ring
    · rw [if_neg hc, if_neg hc]


/-! ## The a.e. bound on the slice-integral of the target -/

/-- **The a.e. slice-integral bound.**  Almost everywhere on `Iz` the `θ`-integral of the
`ℋ^k`-integrand of `F_*(F)·sin 2θ` is bounded by a constant multiple of that of the source.

The pointwise bound `HkIntegrand_radial_sin_le` integrates to a multiple of
`w(z)²·Σ_{j≤k}(D_z^jF_*(z))²`; a.e. (everywhere for `j < k`, a.e. for `j = k`) the radial iterates
are the angular moments `F_*(D_z^jF)`, and Cauchy–Schwarz in `θ` bounds each of those by the
corresponding summand of the source integrand. -/
theorem ae_HkIntegrand_fstarSin_slice_integral_le (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᵐ z ∂(volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ)
        ≤ K * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
  obtain ⟨K, hKnn, hK⟩ := HkIntegrand_radial_sin_le k
  refine ⟨(π / 2) * K * (π / 2) * ((k : ℝ) + 1), by positivity, ?_⟩
  have hk := rDzIter_Fstar_eq_PsiInt_ae α k F hF hmem
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at hk
  rw [← restrict_Ioi_eq_restrict_Iz]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
  filter_upwards [hk] with z hkz
  intro hzmem
  have hz : 0 < z := hzmem
  have hzI : z ∈ Work.Spaces.Iz := le_of_lt hz
  have hid : ∀ j : ℕ, j ≤ k → rDzIter j (fun z => Work.Elliptic.Fstar F z) z = PsiInt F j z := by
    intro j hj
    rcases lt_or_eq_of_le hj with hj' | hj'
    · exact rDzIter_Fstar_eq_PsiInt α k F hF hmem j (by omega) z hzmem
    · rw [hj']
      exact hkz hzmem
  -- Step 1: integrate the pointwise bound, and Cauchy–Schwarz on each summand
  have hmaj_int : IntegrableOn (fun _ : ℝ => K * (Work.Spaces.w z) ^ 2 *
      ∑ j ∈ Finset.range (k + 1), (rDzIter j (fun z => Work.Elliptic.Fstar F z) z) ^ 2)
      Work.Spaces.Iθ :=
    integrableOn_const (by rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  have hstep1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
        (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ)
      ≤ (π / 2) * (K * (Work.Spaces.w z) ^ 2 *
          ∑ j ∈ Finset.range (k + 1), (rDzIter j (fun z => Work.Elliptic.Fstar F z) z) ^ 2) := by
    have h1 : (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, K * (Work.Spaces.w z) ^ 2 *
            ∑ j ∈ Finset.range (k + 1),
              (rDzIter j (fun z => Work.Elliptic.Fstar F z) z) ^ 2 := by
      refine integral_mono_of_nonneg
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k _ z θ)
        hmaj_int ?_
      rw [Filter.EventuallyLE]
      rw [MeasureTheory.ae_restrict_iff' (show MeasurableSet Work.Spaces.Iθ from by
        rw [Work.Spaces.Iθ]; exact measurableSet_Icc)]
      exact Eventually.of_forall fun θ hθ =>
        hK α (fun z => Work.Elliptic.Fstar F z) hα hα1 z hzI θ hθ
    calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
          (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ)
        ≤ ∫ θ in Work.Spaces.Iθ, K * (Work.Spaces.w z) ^ 2 *
            ∑ j ∈ Finset.range (k + 1),
              (rDzIter j (fun z => Work.Elliptic.Fstar F z) z) ^ 2 := h1
      _ = (π / 2) * (K * (Work.Spaces.w z) ^ 2 *
            ∑ j ∈ Finset.range (k + 1),
              (rDzIter j (fun z => Work.Elliptic.Fstar F z) z) ^ 2) := integral_const_Iθ _
  -- Step 2: Cauchy–Schwarz on the angular slice
  have hstep2 : (Work.Spaces.w z) ^ 2 *
        ∑ j ∈ Finset.range (k + 1), (rDzIter j (fun z => Work.Elliptic.Fstar F z) z) ^ 2
      ≤ (π / 2) * (∑ j ∈ Finset.range (k + 1), AjF F j z) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    have hper : ∀ j ∈ Finset.range (k + 1),
        (Work.Spaces.w z) ^ 2 * (rDzIter j (fun z => Work.Elliptic.Fstar F z) z) ^ 2
          ≤ (π / 2) * AjF F j z := by
      intro j hj
      have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [hid j hjk]
      have h := FstarDzIter_sq_mul_w_le_open α k F hF hmem j hjk hz
      rw [show Work.Elliptic.Fstar (Work.Spaces.DzIter j F) z = PsiInt F j z from
        (PsiInt_eq_Fstar_DzIter F j z).symm] at h
      calc (Work.Spaces.w z) ^ 2 * (PsiInt F j z) ^ 2
          = (PsiInt F j z) ^ 2 * (Work.Spaces.w z) ^ 2 := by ring
        _ ≤ (π / 2) * AjF F j z := h
    exact Finset.sum_le_sum hper
  -- Step 3: sum the slice masses
  have hsummass : (∑ j ∈ Finset.range (k + 1), AjF F j z)
      ≤ ((k : ℝ) + 1) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by
    have h1 : (∑ j ∈ Finset.range (k + 1), AjF F j z)
        ≤ ∑ _j ∈ Finset.range (k + 1),
            (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) :=
      Finset.sum_le_sum fun j hj =>
        AjF_le_HkIntegrand_integral α k F hmem j
          (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hzI
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one] using h1
  have hπ2 : (0 : ℝ) ≤ π / 2 := le_of_lt Real.pi_div_two_pos
  have hKπ : (0 : ℝ) ≤ K * (π / 2) := mul_nonneg hKnn hπ2
  calc (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
        (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ)
      ≤ (π / 2) * (K * (Work.Spaces.w z) ^ 2 *
          ∑ j ∈ Finset.range (k + 1), (rDzIter j (fun z => Work.Elliptic.Fstar F z) z) ^ 2) :=
        hstep1
    _ = K * (π / 2) * ((Work.Spaces.w z) ^ 2 *
          ∑ j ∈ Finset.range (k + 1), (rDzIter j (fun z => Work.Elliptic.Fstar F z) z) ^ 2) := by
        ring
    _ ≤ K * (π / 2) * ((π / 2) * (∑ j ∈ Finset.range (k + 1), AjF F j z)) :=
        mul_le_mul_of_nonneg_left hstep2 hKπ
    _ ≤ K * (π / 2) * ((π / 2) *
          (((k : ℝ) + 1) * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsummass hπ2) hKπ
    _ = (π / 2) * K * (π / 2) * ((k : ℝ) + 1) *
          (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k F z θ) := by ring


/-! ## Item two of `ℋ^k`-membership: integrability of the `z`-integral of the slices -/

/-- **Clause two of `ℋ^k`-membership**: the `z`-integral of the `θ`-slices of the `ℋ^k`-integrand
of `F_*(F)·sin 2θ` is integrable on `Iz`. -/
theorem integrableOn_HkIntegrand_fstarSin_outer (α : ℝ) (k : ℕ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hα1 : α ≤ 1) (hF : SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
      (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ) Work.Spaces.Iz := by
  obtain ⟨K, hKnn, hK⟩ := ae_HkIntegrand_fstarSin_slice_integral_le α k F hα hα1 hF hmem
  have hprod : AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k
      (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    aestronglyMeasurable_HkIntegrand_fstarSin_joint α k F hF hmem
  have haesm : AEStronglyMeasurable (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k
      (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) z θ)
      (volume.restrict Work.Spaces.Iz) :=
    AEStronglyMeasurable.integral_prod_right' hprod
  refine Integrable.mono' (hmem.2.const_mul K) haesm ?_
  filter_upwards [hK] with z hz
  rw [Real.norm_of_nonneg (integral_nonneg fun θ =>
    Work.Spaces.HkIntegrand_nonneg α k _ z θ)]
  exact hz

theorem HkMem_FstarSin_open (k : ℕ) (α : ℝ) (F : ℝ → ℝ → ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (hF : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry F) (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)))
    (hmem : Work.Spaces.HkMem α k F) :
    Work.Spaces.HkMem α k (fun z θ => Work.Elliptic.Fstar F z * Real.sin (2 * θ)) :=
  ⟨fun _ hz => integrableOn_HkIntegrand_fstarSin_slice α k F hα hα1 hz,
    integrableOn_HkIntegrand_fstarSin_outer α k F hα hα1 (smoothOpen_of_forall hF) hmem⟩

end Work.FTS.EllipticEst
