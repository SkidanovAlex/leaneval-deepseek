/-
# `FTS/ClassC/HonestCut/radGreen_modeEnergy_of_compactSupport`

The sharp per-mode weighted `L²` bound for the mode-`m` radial Green function
`a = radGreen α m c` (`PhiStar/Radial/Defs.lean`) of the mode ODE

  `−α²z²a'' − α(5+α)z a' + λ_m a = c`,   `λ_m = lamR m = 2m(2m+5)`   (`Radial.radGreen_solves`),

for a source `c` which is `C^∞` on `(0,∞)`, bounded, and **compactly supported in `[1,2]`**:

  `(λ_m − 3α² − 3α(5+α)/2)² · ∫_0^∞ a² w²  ≤  ∫_0^∞ c² w²`,   `w(z) = (1+z)²/z²`.

This is `Work.FTS.ClassC.radGreen_modeEnergy` (which is `ModeEnergyCS.modeWeightedEnergy_sq`
instantiated at the explicit Green function) with its *eight* hypotheses discharged by compact
support:

* the source's two-sided decay and power hypotheses `hdec`, `hvy` (`c ≡ 0` off `[1,2]`);
* the three Green-formula integrability hypotheses `hg0`, `hg0'`, `hginf`
  (`c ≡ 0` on `(0,1)`; on `(1,∞)` the integrand is dominated by the integrable
  `M t^{−2m/α−1}`);
* the derivative slots `HasDerivAt a`, `HasDerivAt (deriv a)`, from the `C^∞`-regularity
  `radGreen_smooth_of_contDiffOn`;
* the four weighted `L²` integrability slots: the source square `c²w²` (compact support), the
  pairing `c a w²` (AM–GM against the two squares), and the two solution slots `a²w²`, `(z a')²w²`.

The two solution slots are derived from the near-`0`/far-`∞` pointwise bounds of `radGreen`
(`radGreen_near_pointwise_bound`: `|a z| ≤ B z^d`, `|z a' z| ≤ B z^d` with `d > 3/2` for
`z ≤ 1`; `radGreen_far_pointwise_bound`: `|a z| ≤ C/z`, `|z a' z| ≤ C/z` for `z ≥ 1`) by the
helper `radGreen_w2_slots_of_pointwise_bounds` below: near `0` the weight contributes
`w² ≤ 16z^{−4}`, so the integrand is `≲ z^{2d−4}` with `2d − 4 > −1`; far out `w² ≤ 16` and the
integrand is `≲ z^{−2}`.

With `m ≥ 1` the coefficient is positive: `λ_m ≥ 14`, `3α² ≤ 3/16`,
`3α(5+α)/2 ≤ 2`, so `λ_m − 3α² − 3α(5+α)/2 ≥ 11.8`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.ClassC.RadGreenModeEnergy
import Submission.Work.FTS.ClassC.radGreen_smooth_of_contDiffOn
import Submission.Work.FTS.EllExist.Honesty.radGreen_l2_far
import Submission.Work.FTS.ClassC.HonestCut.radGreen_compact_source
import Submission.Work.FTS.ClassC.HonestCut.radGreen_hasDerivAt_slots
import Submission.Work.FTS.ClassC.HonestCut.radGreen_near_pointwise_bound
import Submission.Work.FTS.ClassC.HonestCut.radGreen_far_pointwise_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC.HonestCut

local notation "w" => Work.Spaces.w
local notation "a" => Work.FTS.PhiStar.Radial.radGreen

/-- **The two weighted `L²` slots of the mode-`m` Green function, from pointwise bounds.**

If `radGreen α m c` obeys a near-`0` bound `|a z| ≤ B z^d`, `|z a' z| ≤ B z^d` with `d > 3/2`
(on `0 < z ≤ 1`) and a far bound `|a z| ≤ C/z`, `|z a' z| ≤ C/z` (on `z ≥ 1`), then both
`(z a')² w²` and `a² w²` are integrable on `(0,∞)`.  Near `0` the weight contributes
`w² ≤ 16 z^{−4}`, so the integrands are dominated by `16 B² z^{2d−4}`, integrable because
`2d − 4 > −1`; far out `w² ≤ 16` and they are dominated by `16 C² z^{−2}`.  The two pieces are
glued at `z = 1` (a null point). -/
theorem radGreen_w2_slots_of_pointwise_bounds {α : ℝ} (m : ℕ) {c : ℝ → ℝ}
    (hderiv : ∀ z : ℝ, 0 < z → HasDerivAt (fun z => a α m c z)
      (deriv (fun z => a α m c z) z) z)
    (hderiv2 : ∀ z : ℝ, 0 < z → HasDerivAt (deriv (fun z => a α m c z))
      (deriv (deriv (fun z => a α m c z)) z) z)
    (hnear : ∃ B d : ℝ, 0 ≤ B ∧ 3 / 2 < d ∧ ∀ z : ℝ, 0 < z → z ≤ 1 →
      |a α m c z| ≤ B * z ^ d ∧ |z * deriv (fun z' => a α m c z') z| ≤ B * z ^ d)
    (hfar : ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, 1 ≤ z →
      |a α m c z| ≤ C / z ∧ |z * deriv (fun z' => a α m c z') z| ≤ C / z) :
    MeasureTheory.IntegrableOn (fun z : ℝ => (z * deriv (fun z' => a α m c z') z) ^ 2
        * (w z) ^ 2) (Set.Ioi 0)
      ∧ MeasureTheory.IntegrableOn (fun z : ℝ => (a α m c z) ^ 2 * (w z) ^ 2) (Set.Ioi 0) := by
  obtain ⟨B, d, hBnn, _hd, hnb⟩ := hnear
  obtain ⟨C, _hCnn, hfb⟩ := hfar
  -- continuity of `deriv (radGreen α m c)` and of `radGreen α m c` on the open half-line
  have hdcont : ContinuousOn (deriv (fun z => a α m c z)) (Set.Ioi 0) :=
    fun z hz => (hderiv2 z hz).continuousAt.continuousWithinAt
  have hacont : ContinuousOn (fun z => a α m c z) (Set.Ioi 0) :=
    fun z hz => (hderiv z hz).continuousAt.continuousWithinAt
  -- continuity of `w²` on `(0,∞)`
  have hwcont : ContinuousOn (fun z : ℝ => (w z) ^ 2) (Set.Ioi 0) := by
    unfold Work.Spaces.w
    refine (((continuous_const.add continuous_id).continuousOn.pow 2).div
      (continuous_id.continuousOn.pow 2) (fun z hz => ?_)).pow 2
    exact pow_ne_zero 2 (ne_of_gt hz)
  -- the near/far gluing: `(0,1) ∪ (1,∞)` is `(0,∞)` up to the null point `1`
  have glue : ∀ f : ℝ → ℝ, MeasureTheory.IntegrableOn f (Set.Ioo 0 1) →
      MeasureTheory.IntegrableOn f (Set.Ioi 1) → MeasureTheory.IntegrableOn f (Set.Ioi 0) := by
    intro f h1 h2
    have hA : MeasureTheory.IntegrableOn f (Set.Icc 0 1) :=
      h1.congr_set_ae MeasureTheory.Ioo_ae_eq_Icc.symm
    have hB : MeasureTheory.IntegrableOn f (Set.Ici 1) :=
      h2.congr_set_ae MeasureTheory.Ioi_ae_eq_Ici.symm
    have hU : MeasureTheory.IntegrableOn f (Set.Icc 0 1 ∪ Set.Ici 1) := hA.union hB
    have hset : Set.Icc (0 : ℝ) 1 ∪ Set.Ici 1 = Set.Ici 0 := by
      ext x
      simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
      constructor
      · rintro (⟨h1', _⟩ | h3) <;> linarith
      · intro h
        rcases le_or_gt x 1 with h' | h'
        · exact Or.inl ⟨h, h'⟩
        · exact Or.inr h'.le
    rw [hset] at hU
    exact hU.congr_set_ae MeasureTheory.Ioi_ae_eq_Ici
  -- the near-`0` estimate, for any continuous `F` with `|F| ≤ B z^d`
  have near_of_bound : ∀ F : ℝ → ℝ, ContinuousOn F (Set.Ioo 0 1) →
      (∀ z : ℝ, 0 < z → z ≤ 1 → |F z| ≤ B * z ^ d) →
      MeasureTheory.IntegrableOn (fun z : ℝ => (F z) ^ 2 * (w z) ^ 2) (Set.Ioo 0 1) := by
    intro F hFc hFb
    have hpow : MeasureTheory.IntegrableOn (fun z : ℝ => z ^ (2 * d - 4)) (Set.Ioo 0 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff (s := 2 * d - 4) (t := 1) one_pos).mpr
        (by linarith)
    have hdom : MeasureTheory.IntegrableOn (fun z : ℝ => (16 * B ^ 2) * z ^ (2 * d - 4))
        (Set.Ioo 0 1) := hpow.const_mul _
    refine MeasureTheory.Integrable.mono' hdom ?_ ?_
    · exact ((hFc.pow 2).mul (hwcont.mono (fun z hz => hz.1))).aestronglyMeasurable
        measurableSet_Ioo
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with z hz
      have hz0 : 0 < z := hz.1
      have hz1 : z ≤ 1 := le_of_lt hz.2
      have hb := hFb z hz0 hz1
      have hsq : (F z) ^ 2 ≤ (B * z ^ d) ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg _) hb 2
        simpa only [sq_abs] using h
      have hBz : 0 ≤ B * z ^ d := mul_nonneg hBnn (Real.rpow_nonneg hz0.le _)
      have hw : (w z) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
        rw [Work.Spaces.w, div_pow]
        rw [show ((1 + z) ^ 2) ^ 2 = (1 + z) ^ 4 by ring,
          show (z ^ 2) ^ 2 = z ^ 4 by ring]
      have hw16 : (w z) ^ 2 ≤ 16 / z ^ 4 := by
        rw [hw]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        have h2 : (1 + z) ^ 4 ≤ 2 ^ 4 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 4
        norm_num at h2
        exact h2
      have hsub : (z ^ d) ^ 2 / z ^ 4 = z ^ (2 * d - 4) := by
        rw [← Real.rpow_mul_natCast hz0.le d 2, ← Real.rpow_natCast z 4,
          ← Real.rpow_sub hz0]
        congr 1
        push_cast
        ring
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc (F z) ^ 2 * (w z) ^ 2
          ≤ (B * z ^ d) ^ 2 * (16 / z ^ 4) :=
            mul_le_mul hsq hw16 (by positivity) (pow_nonneg hBz 2)
        _ = 16 * B ^ 2 * ((z ^ d) ^ 2 / z ^ 4) := by ring
        _ = 16 * B ^ 2 * z ^ (2 * d - 4) := by rw [hsub]
        _ = (16 * B ^ 2) * z ^ (2 * d - 4) := by ring
  -- the far estimate, for any continuous `F` with `|F| ≤ C / z` on `[1,∞)`
  have far_of_bound : ∀ F : ℝ → ℝ, ContinuousOn F (Set.Ioi 1) →
      (∀ z : ℝ, 1 ≤ z → |F z| ≤ C / z) →
      MeasureTheory.IntegrableOn (fun z : ℝ => (F z) ^ 2 * (w z) ^ 2) (Set.Ioi 1) := by
    intro F hFc hFb
    have hdom : MeasureTheory.IntegrableOn (fun z : ℝ => (16 * C ^ 2) * z ^ (-2 : ℝ))
        (Set.Ioi 1) :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1)
        (by norm_num : (0 : ℝ) < 1)).const_mul _
    refine MeasureTheory.Integrable.mono' hdom ?_ ?_
    · exact ((hFc.pow 2).mul (hwcont.mono (fun z hz => by
        simp only [Set.mem_Ioi] at hz ⊢; linarith))).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      have hz1 : 1 ≤ z := le_of_lt hz
      have hz0 : 0 < z := lt_of_lt_of_le one_pos hz1
      have hb := hFb z hz1
      have hsq : (F z) ^ 2 ≤ (C / z) ^ 2 := by
        have h := pow_le_pow_left₀ (abs_nonneg _) hb 2
        simpa only [sq_abs] using h
      have hw16 : (w z) ^ 2 ≤ 16 :=
        Work.FTS.EllExist.Honesty.w_sq_le_sixteen_of_one_le hz1
      have hzsq : (C / z) ^ 2 = C ^ 2 * z ^ (-2 : ℝ) := by
        rw [div_pow, div_eq_mul_inv, ← Real.rpow_natCast (z) 2, ← Real.rpow_neg hz0.le]
        norm_num
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc (F z) ^ 2 * (w z) ^ 2 ≤ (C / z) ^ 2 * 16 :=
            mul_le_mul hsq hw16 (by positivity) (by positivity)
        _ = (16 * C ^ 2) * z ^ (-2 : ℝ) := by rw [hzsq]; ring
  refine ⟨glue _ (near_of_bound _ ?_ (fun z hz0 hz1 => (hnb z hz0 hz1).2)) ?_,
    glue _ (near_of_bound _ ?_ (fun z hz0 hz1 => (hnb z hz0 hz1).1)) ?_⟩
  · exact continuous_id.continuousOn.mul (hdcont.mono (fun z hz => hz.1))
  · exact far_of_bound _ (continuous_id.continuousOn.mul
      (hdcont.mono (fun z hz => by simp only [Set.mem_Ioi] at hz ⊢; linarith)))
      (fun z hz => (hfb z hz).2)
  · exact hacont.mono (fun z hz => hz.1)
  · exact far_of_bound _ (hacont.mono (fun z hz => by
      simp only [Set.mem_Ioi] at hz ⊢; linarith)) (fun z hz => (hfb z hz).1)

theorem radGreen_modeEnergy_of_compactSupport {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (m : ℕ) (hm : 1 ≤ m) {c : ℝ → ℝ}
    (hc : ∀ n : ℕ, ContDiffOn ℝ n c (Set.Ioi 0))
    (hM : ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, |c t| ≤ M)
    (hsupp : ∀ z : ℝ, z ∉ Set.Icc 1 2 → c z = 0) :
    (Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2) ^ 2
        * (∫ z in Set.Ioi 0, (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2
            * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Set.Ioi 0, (c z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
  -- the source-side facts discharged by compact support, and the `c²w²`-slot
  obtain ⟨hcont, hdec, hvy, hg0, hg0', hginf, hint4⟩ :=
    Work.FTS.ClassC.HonestCut.radGreen_compact_source (α := α) hα hα4 m hc hM hsupp
  -- `C^∞`-regularity of the Green function on `(0,∞)`, and its two derivative slots
  have hsmooth : ∀ n : ℕ,
      ContDiffOn ℝ n (fun z => Work.FTS.PhiStar.Radial.radGreen α m c z) (Set.Ioi 0) :=
    Work.FTS.ClassC.radGreen_smooth_of_contDiffOn (α := α) hα m hc hg0 hg0' hginf
  obtain ⟨hderiv, hderiv2⟩ :=
    Work.FTS.ClassC.HonestCut.radGreen_hasDerivAt_slots (α := α) m hsmooth
  -- the two weighted `L²` slots of the solution, from the near-`0`/far-`∞` bounds
  obtain ⟨hint1, hint2⟩ := Work.FTS.ClassC.HonestCut.radGreen_w2_slots_of_pointwise_bounds
    (α := α) m hderiv hderiv2
    (Work.FTS.ClassC.HonestCut.radGreen_near_pointwise_bound (α := α) hα hα4 m hm hcont hvy
      hg0 hg0' hginf)
    (Work.FTS.ClassC.HonestCut.radGreen_far_pointwise_bound (α := α) hα hα4 m hcont hdec
      hg0 hg0' hginf)
  -- the pairing slot `c a w²`, by AM–GM against the two squares
  have ha : ContinuousOn (fun z : ℝ => Work.FTS.PhiStar.Radial.radGreen α m c z)
      (Set.Ioi 0) := fun z hz => (hderiv z hz).continuousAt.continuousWithinAt
  have hint3 : MeasureTheory.IntegrableOn
      (fun z : ℝ => c z * Work.FTS.PhiStar.Radial.radGreen α m c z * (Work.Spaces.w z) ^ 2)
      (Set.Ioi 0) := by
    have hdom : MeasureTheory.Integrable
        (fun z : ℝ => ((c z) ^ 2 * (Work.Spaces.w z) ^ 2
          + (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2 * (Work.Spaces.w z) ^ 2) / 2)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
      simpa only [Pi.add_apply] using (hint4.add hint2).div_const 2
    refine MeasureTheory.Integrable.mono' hdom ?_ ?_
    · have hw : ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
        unfold Work.Spaces.w
        refine (((continuous_const.add continuous_id).continuousOn.pow 2).div
          (continuous_id.continuousOn.pow 2) (fun z hz => ?_)).pow 2
        exact pow_ne_zero 2 (ne_of_gt hz)
      exact ((hcont.mul ha).mul hw).aestronglyMeasurable measurableSet_Ioi
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      rw [Real.norm_eq_abs]
      refine abs_le.mpr ⟨?_, ?_⟩
      · nlinarith [sq_nonneg (c z * Work.Spaces.w z
            + Work.FTS.PhiStar.Radial.radGreen α m c z * Work.Spaces.w z)]
      · nlinarith [sq_nonneg (c z * Work.Spaces.w z
            - Work.FTS.PhiStar.Radial.radGreen α m c z * Work.Spaces.w z)]
  -- the sharp per-mode energy bound, with all slots in place
  exact Work.FTS.ClassC.radGreen_modeEnergy hα hα4 m hm hcont hdec hvy hg0 hg0' hginf
    hderiv hderiv2 hint1 hint2 hint3 hint4

end Work.FTS.ClassC.HonestCut
