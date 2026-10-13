import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Tactic.Have
import Submission.Work.EllipticEst.Core.Defs
import Submission.Work.EllipticEst.Core.mixedSliceLe
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.Core

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

set_option autoImplicit false

/-!
# The mixed-derivative family of the interpolation estimate

For `1 ≤ i` and `i + j ≤ k` the `(i,j)`-summand of the left-hand side of
`HkSqLHS_le_summands` is

`∫_z w(z)² ∫_θ (D_z^{j+1} D_θ^i ∂_θ V)² sin(2θ)^{-γ}`,

a mixed derivative of order `i + j` of `∂_θ V`.  The present file shows that the whole
family is dominated by the `ℋ^k`-norm of `∂_θ²V`: the point is that

`D_θ^i ∂_θ V = D_θ^{i-1}(sin(2θ) · ∂_θ²V)`

and the Leibniz expansion of `D_θ^{i-1}` of that product produces only the derivatives
`D_θ^b ∂_θ²V`, `b ≤ i - 1`, with coefficients `D_θ^a(sin 2θ)` that are `O(sin 2θ)`.
The `θ`-pointwise inequality for this expansion is `mixedSliceLe_pointwise` (already
proved in `mixedSliceLe`); here we

* identify the weighted square `(D_z^{j+1}D_θ^b∂_θ²V · W)²` of the right-hand side of
  that pointwise inequality with one of the *summands* of `HkIntegrand α k (∂_θ²V)`
  (`Work.Spaces.sq_le_HkIntegrand_mixed`/`_z`), so that each of them is bounded by the
  whole integrand;
* integrate the resulting slicewise inequality in `θ` (`integral_mono_of_nonneg`, which
  needs no measurability of the smaller integrand) and in `z` (same, using the
  marginal integrability supplied by `HkMem`);
* sum over the finitely many slots `(i,j)`, `1 ≤ i`, `i+j ≤ k`, and use `α ≤ 1/4` so
  that `α² ≤ 1`.

Nothing here needs the two angular-vanishing hypotheses of the statement, nor the
`ℋ^k`-membership of `D_zV` or `D_z²V`; they are simply carried along.
-/

/-! ## Weight identities on `Iθ` -/

/-- `wTheta α θ ^ 2 = thGam α θ` on `Iθ`, for `0 < α`: the angular weight of the mixed
slots of `HkIntegrand` is the square of the weight `w_θ` of the paper. -/
lemma wTheta_sq_eq_thGam {α : ℝ} (hα : 0 < α) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.wTheta α θ ^ 2 = Work.FTS.EllipticEst.thGam α θ := by
  have hγpos : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  have hγ2 : -(Work.Spaces.gam α / 2) ≠ 0 :=
    neg_ne_zero.mpr (ne_of_gt (by linarith : 0 < Work.Spaces.gam α / 2))
  have hγ : -(Work.Spaces.gam α) ≠ 0 := neg_ne_zero.mpr (ne_of_gt hγpos)
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.EllipticEst.sin_two_nonneg hθ
  rcases eq_or_lt_of_le hs with h0 | hpos
  · simp only [Work.Spaces.wTheta, Work.FTS.EllipticEst.thGam, ← h0]
    rw [Real.zero_rpow hγ2, Real.zero_rpow hγ]
    norm_num
  · simp only [Work.Spaces.wTheta, Work.FTS.EllipticEst.thGam]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hpos)]
    congr 1
    ring

/-- `Wt α z θ ^ 2 = w z ^ 2 * thGam α θ` on `Iθ`: the square of the full weight of the
mixed slots is the radial weight squared times the angular weight. -/
lemma Wt_sq_eq {α : ℝ} (hα : 0 < α) (z : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Wt α z θ ^ 2 = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thGam α θ := by
  simp only [Work.Spaces.Wt]
  rw [mul_pow, wTheta_sq_eq_thGam hα hθ]

/-- `(w z / sin(2θ)^{η/2})^2 = w z ^ 2 * thEta θ` on `Iθ`: the square of the radial weight
of the `D_z`-family is the radial weight squared times `thEta`. -/
lemma w_div_sin_sq_eq (z : ℝ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.thEta θ := by
  have hη : (Work.Spaces.eta) ≠ 0 := by norm_num [Work.Spaces.eta]
  have hη2 : (Work.Spaces.eta / 2) ≠ 0 := by norm_num [Work.Spaces.eta]
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.EllipticEst.sin_two_nonneg hθ
  rcases eq_or_lt_of_le hs with h0 | hpos
  · simp only [Work.FTS.EllipticEst.thEta, ← h0]
    rw [Real.zero_rpow (neg_ne_zero.mpr hη), Real.zero_rpow hη2]
    simp
  · have hsq : (Real.sin (2 * θ) ^ (Work.Spaces.eta / 2)) ^ 2
        = Real.sin (2 * θ) ^ Work.Spaces.eta := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hpos)]
      congr 1
      ring
    simp only [Work.FTS.EllipticEst.thEta]
    rw [div_pow, hsq, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt hpos) Work.Spaces.eta]

/-- The `θ`-integral of the `ℋ^k`-integrand is nonnegative. -/
lemma integral_HkIntegrand_nonneg (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ :=
  MeasureTheory.integral_nonneg_of_ae
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k f z θ))

/-! ## The pointwise (in `(z,θ)`) bound -/

/-- **The pointwise bound of the mixed family.**  For `1 ≤ i`, `i + j ≤ k`, `z > 0` and
every `θ ∈ Iθ`, the weighted square of `D_z^{j+1}D_θ^i∂_θV` (with the *unweighted*
weight `w(z)² thGam α θ`) is bounded by a constant times the `ℋ^k`-integrand of
`∂_θ²V`.  It is the Leibniz expansion `mixedSliceLe_pointwise` followed by the
identification of each of its terms with a summand of `HkIntegrand α k (∂_θ²V)`. -/
lemma mixedIntS_pointwise_le {k : ℕ} {K : ℝ} (hKpos : 0 ≤ K)
    (hK : ∀ i ≤ k, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.EllipticEst.LopIter i s1 θ| ≤ K * s1 θ)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {V : ℝ → ℝ → ℝ}
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) sliceU)
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) {z : ℝ} (hz : 0 < z) :
    ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ)
        ≤ ((i : ℝ) * 4 ^ (i - 1) * K ^ 2) * ((i : ℝ) + 1)
            * Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ := by
  intro θ hθ
  have hik : i ≤ k := by omega
  have hCptnn : 0 ≤ (i : ℝ) * 4 ^ (i - 1) * K ^ 2 := by positivity
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ :=
    Work.Spaces.HkIntegrand_nonneg _ _ _ _ _
  have hpw := mixedSliceLe_pointwise hKpos hK hα hα1 hV hi hik j hz θ hθ
  have h2 := mul_le_mul_of_nonneg_left hpw (sq_nonneg (Work.Spaces.w z))
  have hb : ∀ b ∈ Finset.Icc 1 (i - 1),
      (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ)
      ≤ Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ := by
    intro b hb
    have hb1 : 1 ≤ b := (Finset.mem_Icc.mp hb).1
    have hbjk : b + (j + 1) ≤ k := by
      have := (Finset.mem_Icc.mp hb).2
      omega
    have hmix := Work.Spaces.sq_le_HkIntegrand_mixed α k (Work.Spaces.pthIter 2 V) z θ b
      (j + 1) hb1 hbjk
    have hgoal : (Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ
          * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
            * Work.FTS.EllipticEst.thGam α θ) := by
      rw [mul_pow, Wt_sq_eq hα z hθ]; ring
    rwa [hgoal] at hmix
  have hzsl : (Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
        * Work.FTS.EllipticEst.thEta θ)
      ≤ Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ := by
    have hz0 := Work.Spaces.sq_le_HkIntegrand_z α k (Work.Spaces.pthIter 2 V) z θ (j + 1)
      (by omega)
    have hgoal : (Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 V) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        = (Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
            * Work.FTS.EllipticEst.thEta θ) := by
      rw [mul_pow, w_div_sin_sq_eq z hθ]; ring
    rwa [hgoal] at hz0
  have hsum : (Work.Spaces.w z) ^ 2 * ((∑ b ∈ Finset.Icc 1 (i - 1),
        (Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
          * Work.FTS.EllipticEst.thGam α θ)
      + (Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
          * Work.FTS.EllipticEst.thEta θ)
      ≤ ((i : ℝ) + 1) * Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ := by
    rw [mul_add, Finset.mul_sum]
    have hcard : ((Finset.Icc 1 (i - 1)).card : ℝ) ≤ (i : ℝ) := by
      have h1 : (Finset.Icc 1 (i - 1)).card ≤ i := by
        have hsub : Finset.Icc 1 (i - 1) ⊆ Finset.range i := fun b hb =>
          Finset.mem_range.mpr (by have h := (Finset.mem_Icc.mp hb).2; omega)
        calc (Finset.Icc 1 (i - 1)).card ≤ (Finset.range i).card := Finset.card_le_card hsub
          _ = i := Finset.card_range i
      exact_mod_cast h1
    calc (∑ b ∈ Finset.Icc 1 (i - 1), (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed (j + 1) b
            (Work.Spaces.pthIter 2 V) z θ) ^ 2 * Work.FTS.EllipticEst.thGam α θ))
          + (Work.Spaces.w z) ^ 2 * ((Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ)
        ≤ (∑ b ∈ Finset.Icc 1 (i - 1),
            Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ)
          + Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ :=
          add_le_add (Finset.sum_le_sum hb) hzsl
      _ = ((Finset.Icc 1 (i - 1)).card : ℝ)
            * Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ
          + Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (i : ℝ) * Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ
          + Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ :=
          add_le_add (mul_le_mul_of_nonneg_right hcard hHnn) le_rfl
      _ = ((i : ℝ) + 1) * Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ := by ring
  calc (Work.Spaces.w z) ^ 2 * ((Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
        * Work.FTS.EllipticEst.thGam α θ)
      ≤ (Work.Spaces.w z) ^ 2 * (((i : ℝ) * 4 ^ (i - 1) * K ^ 2)
          * ((∑ b ∈ Finset.Icc 1 (i - 1),
                (Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
                  * Work.FTS.EllipticEst.thGam α θ)
            + (Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ)) := h2
    _ = ((i : ℝ) * 4 ^ (i - 1) * K ^ 2)
          * ((Work.Spaces.w z) ^ 2 * ((∑ b ∈ Finset.Icc 1 (i - 1),
                (Work.Spaces.mixed (j + 1) b (Work.Spaces.pthIter 2 V) z θ) ^ 2
                  * Work.FTS.EllipticEst.thGam α θ)
            + (Work.Spaces.DzIter (j + 1) (Work.Spaces.pthIter 2 V) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ)) := by ring
    _ ≤ ((i : ℝ) * 4 ^ (i - 1) * K ^ 2)
          * (((i : ℝ) + 1) * Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ) :=
        mul_le_mul_of_nonneg_left hsum hCptnn
    _ = ((i : ℝ) * 4 ^ (i - 1) * K ^ 2) * ((i : ℝ) + 1)
          * Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ := by ring

/-! ## Integration of the pointwise bound -/

/-- The slicewise consequence of `mixedIntS_pointwise_le`: for every `z ∈ Iz` the
`θ`-slice integrand `mixedIntS α i j V z` is bounded by a constant times the
`θ`-integral of the `ℋ^k`-integrand of `∂_θ²V`. -/
lemma mixedIntS_le_slice {k : ℕ} {K : ℝ} (hKpos : 0 ≤ K)
    (hK : ∀ i ≤ k, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.EllipticEst.LopIter i s1 θ| ≤ K * s1 θ)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {V : ℝ → ℝ → ℝ}
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) sliceU)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V))
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) :
    ∀ z ∈ Work.Spaces.Iz,
      mixedIntS α i j V z
        ≤ ((i : ℝ) * 4 ^ (i - 1) * K ^ 2) * ((i : ℝ) + 1)
            * (∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 V) z θ) := by
  intro z hz
  rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
  · rw [show mixedIntS α i j V z = 0 from by
        rw [← hz0]; simp [mixedIntS, Work.Spaces.w]]
    exact mul_nonneg (by positivity) (integral_HkIntegrand_nonneg α k _ z)
  · have hrew : mixedIntS α i j V z
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2
            * ((Work.Spaces.mixed (j + 1) i (Work.Spaces.pth V) z θ) ^ 2
                * Work.FTS.EllipticEst.thGam α θ) := by
      rw [mixedIntS]
      exact (MeasureTheory.integral_const_mul _ _).symm
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mul_nonneg (sq_nonneg _)
          (mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.thGam_nonneg hθ))))
      ((hmem.1 z hz).const_mul _)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => mixedIntS_pointwise_le hKpos hK hα hα1 hV hi hij hzpos θ hθ))
    rw [hrew, MeasureTheory.integral_const_mul]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul] at hmono
    exact hmono

/-- **The slot estimate.**  For `1 ≤ i`, `i + j ≤ k`, the `z`-integral of
`mixedIntS α i j V z` is bounded by a constant times `HkSq α k (∂_θ²V)`.  This is
`mixedIntS_le_slice` integrated in `z` with `integral_mono_of_nonneg`. -/
lemma mixedIntS_integral_le {k : ℕ} {K : ℝ} (hKpos : 0 ≤ K)
    (hK : ∀ i ≤ k, ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.EllipticEst.LopIter i s1 θ| ≤ K * s1 θ)
    {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {V : ℝ → ℝ → ℝ}
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) sliceU)
    (hmem : Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V))
    {i j : ℕ} (hi : 1 ≤ i) (hij : i + j ≤ k) :
    ∫ z in Work.Spaces.Iz, mixedIntS α i j V z
      ≤ ((i : ℝ) * 4 ^ (i - 1) * K ^ 2) * ((i : ℝ) + 1)
          * Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V) := by
  have hpt := mixedIntS_le_slice hKpos hK hα hα1 hV hmem hi hij
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => by
      rw [mixedIntS]
      exact mul_nonneg (sq_nonneg _)
        (MeasureTheory.integral_nonneg_of_ae
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
            (fun θ hθ => mul_nonneg (sq_nonneg _)
              (Work.FTS.EllipticEst.thGam_nonneg hθ))))))
    (hmem.2.const_mul _)
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici fun z hz => hpt z hz)
  rw [MeasureTheory.integral_const_mul] at hmono
  exact hmono

/-! ## The family -/

/-- **The mixed-derivative family of the interpolation estimate.**  For every `k` there
is a constant `C > 0` such that for `0 < α ≤ 1/4` and every `V` smooth on the open
quadrant with `V ∈ ℋ^k` in the three relevant norms,

`α² ∑_{1 ≤ i, i+j ≤ k} ∫_z w² ∫_θ (D_z^{j+1}D_θ^i∂_θV)² sin(2θ)^{-γ}
   ≤ C (α⁴ HkSq(D_z²V) + HkSq(∂_θ²V) + α² HkSq(D_zV))`.

Each summand is estimated by a summand of `HkSq α k (∂_θ²V)`, so the right-hand side is
dominated by its second term; the factor `α² ≤ 1` and the finitely many slots produce
the stated constant. -/
theorem mixedFamily_le (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (V : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.SmoothOpen V →
      (∀ z : ℝ, V z 0 = 0) → (∀ z : ℝ, V z (Real.pi / 2) = 0) →
      Work.Spaces.HkMem α k (Work.Spaces.DzIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 V) →
      Work.Spaces.HkMem α k (Work.Spaces.Dz V) →
      α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          if 1 ≤ i ∧ i + j ≤ k then
            ∫ z in Work.Spaces.Iz, Work.EllipticEst.Core.mixedIntS α i j V z
          else 0)
        ≤ C * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
            + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
            + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := by
  obtain ⟨K, hKpos, hK⟩ := Work.FTS.EllipticEst.sd_lop_iter_sin_bound k
  have hKnn : 0 ≤ K := hKpos.le
  refine ⟨1 + ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k, ?_, ?_⟩
  · positivity
  · intro α V hα hα14 hV _ _ _ hPth2 _
    have hα1 : α ≤ 1 := by linarith
    have hV' : ContDiffOn ℝ ∞ (Function.uncurry V) sliceU := hV
    set B : ℝ := Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V) with hB
    have hBnn : 0 ≤ B := by rw [hB]; exact Work.Spaces.HkSq_nonneg _ _ _
    -- the per-slot estimate
    have hslot : ∀ i j, i ∈ Finset.range (k + 1) → j ∈ Finset.range (k + 1) →
        (if 1 ≤ i ∧ i + j ≤ k then
            ∫ z in Work.Spaces.Iz, mixedIntS α i j V z else 0)
          ≤ K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 * B := by
      intro i j hi hj
      by_cases hc : 1 ≤ i ∧ i + j ≤ k
      · rw [if_pos hc]
        refine le_trans (mixedIntS_integral_le hKnn hK hα hα1 hV' hPth2 hc.1 hc.2) ?_
        have hi1 : (i : ℝ) ≤ (k : ℝ) + 1 := by
          exact_mod_cast (by omega : i ≤ k + 1)
        have hi2 : (i : ℝ) + 1 ≤ (k : ℝ) + 1 := by
          exact_mod_cast (by omega : i + 1 ≤ k + 1)
        have hp : (4 : ℝ) ^ (i - 1) ≤ (4 : ℝ) ^ k :=
          pow_le_pow_right₀ (by norm_num) (by omega)
        have hfirst : (i : ℝ) * 4 ^ (i - 1) * K ^ 2 ≤ ((k : ℝ) + 1) * (4 : ℝ) ^ k * K ^ 2 :=
          mul_le_mul (mul_le_mul hi1 hp (by positivity) (by positivity)) le_rfl
            (sq_nonneg K) (by positivity)
        have hle : (i : ℝ) * 4 ^ (i - 1) * K ^ 2 * ((i : ℝ) + 1)
            ≤ K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 := by
          calc (i : ℝ) * 4 ^ (i - 1) * K ^ 2 * ((i : ℝ) + 1)
              ≤ (((k : ℝ) + 1) * (4 : ℝ) ^ k * K ^ 2) * ((k : ℝ) + 1) :=
                mul_le_mul hfirst hi2 (by positivity) (by positivity)
            _ = K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 := by ring
        exact mul_le_mul_of_nonneg_right hle hBnn
      · rw [if_neg hc]
        exact mul_nonneg (by positivity) hBnn
    -- the full sum
    have hsum : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            ∫ z in Work.Spaces.Iz, mixedIntS α i j V z else 0))
        ≤ (((k : ℝ) + 1) * ((k : ℝ) + 1))
            * (K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 * B) := by
      calc (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k then
              ∫ z in Work.Spaces.Iz, mixedIntS α i j V z else 0))
          ≤ ∑ _i ∈ Finset.range (k + 1), ∑ _j ∈ Finset.range (k + 1),
              (K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 * B) :=
            Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hslot i j hi hj
        _ = (((k : ℝ) + 1) * ((k : ℝ) + 1))
              * (K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 * B) := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast
            ring
    have hα2le : α ^ 2 ≤ 1 := by nlinarith [sq_nonneg (α - 1)]
    have hcnn : 0 ≤ 1 + ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k := by positivity
    calc α ^ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k then
            ∫ z in Work.Spaces.Iz, mixedIntS α i j V z else 0))
        ≤ α ^ 2 * ((((k : ℝ) + 1) * ((k : ℝ) + 1))
            * (K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 * B)) :=
          mul_le_mul_of_nonneg_left hsum (sq_nonneg α)
      _ ≤ 1 * ((((k : ℝ) + 1) * ((k : ℝ) + 1))
            * (K ^ 2 * (4 : ℝ) ^ k * ((k : ℝ) + 1) ^ 2 * B)) :=
          mul_le_mul_of_nonneg_right hα2le (by positivity)
      _ = ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k * B := by ring
      _ ≤ (1 + ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k) * B := by
          have h1 : ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k
              ≤ 1 + ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k := by linarith
          calc ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k * B
              = (((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k) * B := by ring
            _ ≤ (1 + ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k) * B :=
                mul_le_mul_of_nonneg_right h1 hBnn
      _ ≤ (1 + ((k : ℝ) + 1) ^ 4 * K ^ 2 * (4 : ℝ) ^ k)
            * (α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V)
              + Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 V)
              + α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V)) := by
          refine mul_le_mul_of_nonneg_left ?_ hcnn
          rw [hB]
          have hA : 0 ≤ α ^ 4 * Work.Spaces.HkSq α k (Work.Spaces.DzIter 2 V) :=
            mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg _ _ _)
          have hD : 0 ≤ α ^ 2 * Work.Spaces.HkSq α k (Work.Spaces.Dz V) :=
            mul_nonneg (by positivity) (Work.Spaces.HkSq_nonneg _ _ _)
          linarith

end

end Work.EllipticEst.Core
