import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.SmallBoxA0.OneDPotMainId.gfun_eq
import Submission.Work.SmallBoxA0.OneDPotMainId.ibp_tail_shell
import Submission.Work.SmallBoxA0.OneDPotMainId.qfun_eq_tail
import Submission.Work.SmallBoxA0.OneDPotMainId.tailI_intervalIntegrable
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.SmallBoxA0

/-- `Ufun p r = ∫_{t ∈ (0,r)} qfun p t` agrees with the interval-integral shell potential
`ShellI p R r = ∫_0^r TailI p R t dt`, because `qfun p = TailI p R` on `(0,R]`. -/
lemma Ufun_eq_ShellI {R : ℝ} (p : ℝ → ℝ)
    (hp0 : ∀ r : ℝ, R ≤ r → p r = 0)
    {r : ℝ} (hr : 0 ≤ r) (hrR : r ≤ R) :
    Ufun p r = ShellI p R r := by
  rw [Ufun, ShellI, ← integral_Ioo_eq_intervalIntegral hr (f := fun t => TailI p R t)]
  exact setIntegral_congr_fun measurableSet_Ioo
    (fun t ht => OneDPotMainId.qfun_eq_tail p hp0 ht.1 (ht.2.le.trans hrR))

/-- `s ↦ s * p s` is interval integrable on `ε..R` for `0 < ε < R`, since there
`s * p s = (s ^ 2 * p s) / s` with `s⁻¹ ≤ ε⁻¹` bounded and `s ^ 2 * p s ∈ L¹`. -/
lemma intervalIntegrable_mul_self {R ε : ℝ} (hε : 0 < ε) (hεR : ε < R) (p : ℝ → ℝ)
    (hp : MeasureTheory.IntegrableOn (fun r : ℝ => r ^ 2 * p r) (Set.Ioo (0 : ℝ) R)) :
    IntervalIntegrable (fun s : ℝ => s * p s) MeasureTheory.volume ε R := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hεR.le,
    integrableOn_Ioc_iff_integrableOn_Ioo (f := fun s : ℝ => s * p s)]
  have hsub : Set.Ioo ε R ⊆ Set.Ioo (0 : ℝ) R := fun x hx => ⟨lt_trans hε hx.1, hx.2⟩
  have hmain : Integrable (fun x : ℝ => x⁻¹ * (x ^ 2 * p x)) (volume.restrict (Set.Ioo ε R)) :=
    (hp.mono_set hsub).bdd_mul (f := fun x : ℝ => x⁻¹) (c := ε⁻¹)
      ((measurable_id.inv).aestronglyMeasurable)
      (by
        filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
        rw [Real.norm_eq_abs, abs_inv, abs_of_pos (lt_trans hε hx.1)]
        simpa only [one_div] using one_div_le_one_div_of_le hε hx.1.le)
  refine hmain.congr ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with x hx
  have hx0 : x ≠ 0 := ne_of_gt (lt_trans hε hx.1)
  refine (inv_mul_eq_iff_eq_mul₀ hx0).mpr ?_
  ring

/-- The one-dimensional main identity: for a radial profile `p` vanishing past `R` with
`r ↦ r ^ 2 * p r` integrable on `(0,R)`, and `0 < ε < R`,
`∫_ε^R (r^2 p r) Gfun p r = ∫_ε^R (qfun p r)^2 + qfun p ε * Ufun p ε`. -/
theorem OneDPotMainId {R : ℝ} (hR : 0 < R) (p : ℝ → ℝ)
    (hp : MeasureTheory.IntegrableOn (fun r : ℝ => r ^ 2 * p r) (Set.Ioo (0 : ℝ) R))
    (hp0 : ∀ r : ℝ, R ≤ r → p r = 0)
    {ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    ∫ r in Set.Ioo ε R, (r ^ 2 * p r) * Gfun p r
      = (∫ r in Set.Ioo ε R, (qfun p r) ^ 2) + qfun p ε * Ufun p ε := by
  have hInt : IntervalIntegrable (fun s : ℝ => s * p s) MeasureTheory.volume ε R :=
    intervalIntegrable_mul_self hε hεR p hp
  have hHon : IntervalIntegrable (TailI p R) MeasureTheory.volume 0 R :=
    OneDPotMainId.tailI_intervalIntegrable hR p hp
  have hibp := OneDPotMainId.ibp_tail_shell hε hεR p hInt hHon
  have hLHS : ∫ r in Set.Ioo ε R, (r ^ 2 * p r) * Gfun p r
      = ∫ r in ε..R, (r * p r) * ShellI p R r := by
    rw [integral_Ioo_eq_intervalIntegral hεR.le (f := fun r => (r ^ 2 * p r) * Gfun p r)]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with r hr
    rw [Set.uIoc_of_le hεR.le] at hr
    have hr0 : 0 < r := lt_trans hε hr.1
    rw [OneDPotMainId.gfun_eq hR p hp hp0 hr0, Ufun_eq_ShellI p hp0 hr0.le hr.2]
    field_simp
  have hRHS : ∫ r in Set.Ioo ε R, (qfun p r) ^ 2 = ∫ r in ε..R, (TailI p R r) ^ 2 := by
    rw [integral_Ioo_eq_intervalIntegral hεR.le (f := fun r => (qfun p r) ^ 2)]
    apply intervalIntegral.integral_congr_ae
    filter_upwards with r hr
    rw [Set.uIoc_of_le hεR.le] at hr
    rw [OneDPotMainId.qfun_eq_tail p hp0 (lt_trans hε hr.1) hr.2]
  have h1 : qfun p ε = TailI p R ε :=
    OneDPotMainId.qfun_eq_tail p hp0 hε hεR.le
  have h2 : Ufun p ε = ShellI p R ε := Ufun_eq_ShellI p hp0 hε.le hεR.le
  rw [hLHS, hRHS, hibp, h1, h2]

end Work.SmallBoxA0
