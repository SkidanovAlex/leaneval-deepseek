/-
# `FarAux.Basic` — the first-order relations for the two Green pieces of `radGreen`

`radGreen α m c = K (G1 + G2)` with `K = radK α m`, and

  `G1 α m c z = z^{s⁻} ∫₀^z c t t^{-1-s⁻} dt`,  `s⁻ = -(2m+5)/α = -radQ α m`,
  `G2 α m c z = z^{s⁺} ∫_z^∞ c t t^{-1-s⁺} dt`,  `s⁺ = 2m/α = radP α m`.

This file proves the two first-order relations

  `z G1' = s⁻ G1 + c`   (on `(0,∞)`, assuming the inner integrand converges on `(0,1)`)
  `z G2' = s⁺ G2 - c`   (on `(0,∞)`, from the decay at `∞`),

together with the general `Dzu`-recursion `dzu_recursion_on` on an open set `U ∌ 0` that turns
them into the pointwise expansion of the iterates `D_z^i`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllExist.Honesty.RadGreenDzuAux
import Submission.Work.FTS.EllExist.Honesty.G1Aux
import Submission.Work.FTS.EllExist.Honesty.radGreen_l2_far
import Submission.Work.FTS.EllExist.Honesty.radPsi_hasDerivAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllExist.Honesty

open Work.FTS.PhiStar.RadialWAux (radP radQ radK radP_pos radQ_pos)

/-- `|x - y| ≤ |x| + |y|` (in the form used for the coefficients of the expansion). -/
lemma abs_sub_le_abs_add (x y : ℝ) : |x - y| ≤ |x| + |y| := by
  rw [abs_le]
  constructor <;> linarith [le_abs_self x, neg_abs_le x, le_abs_self y, neg_abs_le y]

/-- `radPsi = G2` pointwise (the `u ↦ zu` change of variables). -/
lemma radPsi_eq_G2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) {z : ℝ} (hz : 0 < z) :
    Work.FTS.PhiStar.RadialWAux.radPsi α m c z = G2 α m c z := by
  have h := Work.FTS.PhiStar.RadialWAux.integral_Ioi_one_rpow c
    (-(radP α m) - 1) hz
  simp only [G2, Work.FTS.PhiStar.RadialWAux.radPsi, radP] at *
  rw [h]
  ring_nf

/-- The far-field integrability input of `radPsi_hasDerivAt`, obtained from the decay hypothesis. -/
lemma integrableOn_abs_mul_rpow_far {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ)
    (hm : 1 ≤ m) {c : ℝ → ℝ} (M : ℝ) (hM : 0 ≤ M) (hc : ContinuousOn c (Set.Ioi 0))
    (hdec : ∀ t, 1 ≤ t → |c t| ≤ M * t ^ (-(2 * (m : ℝ) / α) - 2)) :
    IntegrableOn (fun t => |c t| * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1) := by
  set p : ℝ := 2 * (m : ℝ) / α with hp
  have hp8 : 8 ≤ p := by rw [hp]; exact eight_le_two_m_div α hα hα4 m hm
  have hexp : -2 * p - 3 < -1 := by linarith
  have hdom : Integrable (fun t : ℝ => M * t ^ (-2 * p - 3))
      (volume.restrict (Set.Ioi 1)) :=
    (integrableOn_Ioi_rpow_of_lt (a := -2 * p - 3) hexp one_pos).const_mul M
  have hcont : ContinuousOn (fun t : ℝ => |c t| * t ^ (-p - 1)) (Set.Ioi 0) :=
    hc.abs.mul (continuousOn_id.rpow_const (fun t ht => Or.inl (ne_of_gt ht)))
  have hmeas : AEStronglyMeasurable (fun t : ℝ => |c t| * t ^ (-p - 1))
      (volume.restrict (Set.Ioi 1)) :=
    (hcont.mono (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))).aestronglyMeasurable
      measurableSet_Ioi
  refine Integrable.mono' hdom hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht1 : 1 ≤ t := le_of_lt ht
  have ht0 : 0 < t := lt_trans one_pos ht
  have hpk : |c t| ≤ M * t ^ (-p - 2) := hdec t ht1
  have hp1 : 0 < t ^ (-p - 1) := Real.rpow_pos_of_pos ht0 _
  have hmul : t ^ (-p - 2) * t ^ (-p - 1) = t ^ (-2 * p - 3) := by
    rw [← Real.rpow_add ht0]
    congr 1
    ring
  have hmain : |c t| * t ^ (-p - 1) ≤ M * t ^ (-2 * p - 3) :=
    calc |c t| * t ^ (-p - 1) ≤ (M * t ^ (-p - 2)) * t ^ (-p - 1) :=
          mul_le_mul_of_nonneg_right hpk hp1.le
      _ = M * t ^ (-2 * p - 3) := by rw [mul_assoc, hmul]
  rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_pos hp1]
  exact hmain

/-- `z G2' = s⁺ G2 - c` on `(1,∞)`. -/
lemma G2_hasDerivAt {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (m : ℕ) (hm : 1 ≤ m)
    {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (hinf : IntegrableOn (fun t => |c t| * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    ∀ z ∈ Set.Ioi 1, HasDerivAt (G2 α m c)
      ((radP α m * G2 α m c z - c z) / z) z := by
  intro z hz
  have hz0 : 0 < z := lt_trans one_pos hz
  have h := radPsi_hasDerivAt (c := c) hα hα4 m hm hc hinf z hz0
  have hev : Work.FTS.PhiStar.RadialWAux.radPsi α m c =ᶠ[𝓝 z] G2 α m c := by
    filter_upwards [isOpen_Ioi.mem_nhds hz0] with y hy
    exact radPsi_eq_G2 α m c hy
  have hd : (radP α m * Work.FTS.PhiStar.RadialWAux.radPsi α m c z - c z) / z
      = (radP α m * G2 α m c z - c z) / z := by
    rw [radPsi_eq_G2 α m c hz0]
  exact (h.congr_of_eventuallyEq hev.symm).congr_deriv hd

/-- `z G1' = s⁻ G1 + c` on `(0,∞)`, assuming the inner integrand converges on `(0,1)`. -/
lemma G1_hasDerivAt_of_intervalIntegrable {α : ℝ} {m : ℕ} {c : ℝ → ℝ} (hc : ContinuousOn c (Set.Ioi 0))
    (hInt : IntegrableOn (G1f α m c) (Set.Ioo 0 1)) :
    ∀ z ∈ Set.Ioi 0, HasDerivAt (G1 α m c)
      (((-radQ α m) * G1 α m c z + c z) / z) z := by
  intro z hz
  have hz0 : z ≠ 0 := ne_of_gt hz
  have hA : HasDerivAt (G1A α m c) (G1f α m c z) z := G1A_hasDerivAt hc hInt z hz
  have hpow : HasDerivAt (fun y : ℝ => y ^ (G1s α m)) (G1s α m * z ^ (G1s α m - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hz0)
  have hprod := hpow.mul hA
  have hfun : G1 α m c = fun y => y ^ (G1s α m) * G1A α m c y := by
    funext y
    exact G1_eq_zpow_mul_G1A α m c y
  have hqs : G1s α m = -radQ α m := by
    rw [G1s, radQ, neg_div]
  refine (hprod.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hfun)).congr_deriv ?_
  rw [← hqs, eq_div_iff hz0, G1_eq_zpow_mul_G1A]
  have hGf : G1f α m c z = c z * z ^ (G1a α m - 1) := rfl
  have e1 : z ^ (G1s α m - 1) * z = z ^ (G1s α m) := by
    rw [Real.rpow_sub_one hz0 (G1s α m)]
    exact div_mul_cancel₀ _ hz0
  have e2 : z ^ (G1s α m) * z ^ (G1a α m - 1) = z⁻¹ := by
    rw [← Real.rpow_add hz, show G1s α m + (G1a α m - 1) = -1 from by
      simp only [G1s, G1a]; ring, Real.rpow_neg_one]
  calc (G1s α m * z ^ (G1s α m - 1) * G1A α m c z
        + z ^ (G1s α m) * G1f α m c z) * z
      = G1s α m * G1A α m c z * (z ^ (G1s α m - 1) * z)
        + c z * (z ^ (G1s α m) * z ^ (G1a α m - 1)) * z := by
        rw [hGf]; ring
    _ = G1s α m * G1A α m c z * z ^ (G1s α m) + c z * z⁻¹ * z := by rw [e1, e2]
    _ = G1s α m * (z ^ (G1s α m) * G1A α m c z) + c z := by
        have hz1 : z⁻¹ * z = 1 := inv_mul_cancel₀ hz0
        linear_combination (c z) * hz1

/-- `Dzu`-recursion on an open set: if `z f'(z) = lam f(z) + A(z)` on the open set `U ∌ 0`, then
`Dzu i f z = lam^i f(z) + Σ_{t<i} lam^{i-1-t} Dzu t A z` there.  (`U ∌ 0` is what makes the
division in the first-order relation cancel.) -/
theorem dzu_recursion_on {U : Set ℝ} (hU : IsOpen U) (hU0 : ∀ z ∈ U, z ≠ 0)
    {f A : ℝ → ℝ} {lam : ℝ} {n : ℕ}
    (hf : ∀ z ∈ U, HasDerivAt f ((lam * f z + A z) / z) z)
    (hA : ∀ t ≤ n, ∀ z ∈ U, DifferentiableAt ℝ (Dzu t A) z) :
    ∀ i ≤ n, ∀ z ∈ U,
      Dzu i f z = lam ^ i * f z + ∑ t ∈ Finset.range i, lam ^ (i - 1 - t) * Dzu t A z := by
  intro i
  induction i with
  | zero => intro _ z _; simp
  | succ k ih =>
    intro hk z hz
    have hzk : k ≤ n := Nat.le_of_succ_le hk
    have hz0 : z ≠ 0 := hU0 z hz
    have hagree : Filter.EventuallyEq (nhds z) (Dzu k f)
        (fun w => lam ^ k * f w + ∑ t ∈ Finset.range k, lam ^ (k - 1 - t) * Dzu t A w) := by
      filter_upwards [hU.mem_nhds hz] with w hw
      exact ih hzk w hw
    have hsum : HasDerivAt
        (fun w => ∑ t ∈ Finset.range k, lam ^ (k - 1 - t) * Dzu t A w)
        (∑ t ∈ Finset.range k, lam ^ (k - 1 - t) * deriv (Dzu t A) z) z := by
      refine HasDerivAt.fun_sum (A := fun t w => lam ^ (k - 1 - t) * Dzu t A w)
        (A' := fun t => lam ^ (k - 1 - t) * deriv (Dzu t A) z) ?_
      intro t ht
      exact ((hA t (le_trans (Finset.mem_range.mp ht).le hzk) z hz).hasDerivAt).const_mul _
    have hstep : HasDerivAt
        (fun w => lam ^ k * f w + ∑ t ∈ Finset.range k, lam ^ (k - 1 - t) * Dzu t A w)
        (lam ^ k * ((lam * f z + A z) / z)
          + ∑ t ∈ Finset.range k, lam ^ (k - 1 - t) * deriv (Dzu t A) z) z :=
      ((hf z hz).const_mul (lam ^ k)).add hsum
    have hLsum : z * (∑ t ∈ Finset.range k, lam ^ (k - 1 - t) * deriv (Dzu t A) z)
        = ∑ t ∈ Finset.range k, lam ^ (k - 1 - t) * Dzu (t + 1) A z := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun t _ => ?_)
      show z * (lam ^ (k - 1 - t) * deriv (Dzu t A) z)
        = lam ^ (k - 1 - t) * Dzu (t + 1) A z
      rw [show Dzu (t + 1) A z = z * deriv (Dzu t A) z from rfl]
      ring
    have hRsum : (∑ t ∈ Finset.range (k + 1), lam ^ (k + 1 - 1 - t) * Dzu t A z)
        = (∑ t ∈ Finset.range k, lam ^ (k - 1 - t) * Dzu (t + 1) A z)
          + lam ^ k * A z := by
      rw [Finset.sum_range_succ']
      rw [show (∑ t ∈ Finset.range k,
            lam ^ (k + 1 - 1 - (t + 1)) * Dzu (t + 1) A z)
          = (∑ t ∈ Finset.range k, lam ^ (k - 1 - t) * Dzu (t + 1) A z) from
        Finset.sum_congr rfl (fun t _ => by
          rw [show k + 1 - 1 - (t + 1) = k - 1 - t from by omega])]
      rw [show k + 1 - 1 - 0 = k from by omega, Dzu_zero]
    have hzpart : z * (lam ^ k * ((lam * f z + A z) / z))
        = lam ^ (k + 1) * f z + lam ^ k * A z := by
      have h1 : z * ((lam * f z + A z) / z) = lam * f z + A z := mul_div_cancel₀ _ hz0
      calc z * (lam ^ k * ((lam * f z + A z) / z))
          = lam ^ k * (z * ((lam * f z + A z) / z)) := by ring
        _ = lam ^ k * (lam * f z + A z) := by rw [h1]
        _ = lam ^ (k + 1) * f z + lam ^ k * A z := by rw [pow_succ]; ring
    change z * deriv (Dzu k f) z = lam ^ (k + 1) * f z
      + ∑ t ∈ Finset.range (k + 1), lam ^ (k + 1 - 1 - t) * Dzu t A z
    rw [hagree.deriv_eq, hstep.deriv]
    rw [mul_add, hLsum, hzpart, hRsum]
    ring

end Work.FTS.EllExist.Honesty
