/-
# `Submission.Work.FIPiChain.P3S3.Grho_sum_zavg_le`

The `z`-averaged dyadic `ρ`-window bound of the `PiBig` endgame.

The hypothesis is the *integrated* window `RhoWindowInt2 atilc x wc E C zc (e·sc·zc)`, i.e.

  `∫_{zc}^{e·sc·zc} Grho x C t / t dt ≤ E`  (`RhoWindowInt2_atilc_iff`),

and the conclusion is the `z`-average over the *small* window `[zc, e·zc]` of the dyadic
position sum:

  `∫_{zc}^{e·zc} (Σ_{j<Jc} Grho x C (2^j z)) / z dz ≤ Jc · E`.

Indeed, the substitution `u = 2^j z` in the `j`-th term turns it into
`∫_{2^j·zc}^{e·2^j·zc} Grho x C u / u du`, and the interval `[2^j·zc, e·2^j·zc]` is contained in
the hypothesis window `[zc, e·sc·zc]` because `2^j ≤ sc = 2^{Jc}` for `j < Jc`.  Since
`Grho x C` is nonnegative (`Grho_nonneg`, using `1 ≤ C`), each term is at most the hypothesis,
and the sum of the `Jc` terms is at most `Jc · E`.

The measure-theoretic prerequisites are:

* measurability of `t ↦ Grho x C t` (imported from the sibling module `Grho_measurable_u`);
* a uniform bound `|Grho x C t| ≤ GrhoBoundConst x · C` (`Grho_abs_le_const`, proved below from
  the elementary `|XrhoC| ≤ Σ_n τ(n)|ã(mn)|` bound `Work.FIChain.abs_XrhoC_le` and the
  integrability helper `integrableOn_div_of_bound`).

The two ingredients give interval integrability of `t ↦ Grho x C t / t` on any `[a,b]` with
`a > 0`, which is what `intervalIntegral.integral_mono_interval` (the window containment step)
and `intervalIntegral.integral_finsetSum` (the sum/integral interchange) require.
-/
import Mathlib
import Submission.Work.FIPiChain.Defs
import Submission.Work.FIPiChain.P3S3.Grho_measurable_u

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.FIPiChain.P3S3

open MeasureTheory
open scoped Interval

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Helpers -/

/-- `∫_p^q F (c·u)/u du = ∫_{c·p}^{c·q} F w / w dw` for `c > 0`: the substitution `w = c·u`
against the invariant measure `du/u`. -/
private lemma comp_mul_div_self (F : ℝ → ℝ) {c : ℝ} (hc : 0 < c) (p q : ℝ) :
    (∫ u in p..q, F (c * u) / u) = ∫ w in (c * p)..(c * q), F w / w := by
  have hG : ∀ u : ℝ, F (c * u) / u = c * (F (c * u) / (c * u)) := by
    intro u
    rcases eq_or_ne u 0 with rfl | hu
    · simp
    · field_simp
  rw [intervalIntegral.integral_congr (fun u _ => hG u)]
  rw [intervalIntegral.integral_const_mul]
  have h1 : (∫ u in p..q, F (c * u) / (c * u)) = c⁻¹ * ∫ w in c * p..c * q, F w / w := by
    have := intervalIntegral.integral_comp_mul_left (a := p) (b := q) (c := c)
      (fun w : ℝ => F w / w) hc.ne'
    simpa using this
  rw [h1]; field_simp

/-- A measurable function bounded by `V` is, after division by the identity, integrable on any
`(a,b]` with `a > 0` (the quotient is then bounded by `V/a`). -/
private lemma integrableOn_div_of_bound {F : ℝ → ℝ} {a b V : ℝ}
    (hF : Measurable F) (hFb : ∀ u : ℝ, |F u| ≤ V) (ha : 0 < a) :
    IntegrableOn (fun u : ℝ => F u / u) (Set.Ioc a b) volume := by
  refine MeasureTheory.IntegrableOn.of_bound (measure_Ioc_lt_top)
    (hF.div measurable_id).aestronglyMeasurable (V / a) ?_
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  refine Filter.Eventually.of_forall (fun u hu => ?_)
  have hu_pos : 0 < u := lt_trans ha hu.1
  have hu_ge : a ≤ u := le_of_lt hu.1
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hu_pos]
  refine (div_le_div_of_nonneg_left (abs_nonneg (F u)) ha hu_ge).trans ?_
  exact div_le_div_of_nonneg_right (hFb u) ha.le

/-- `wc m = τ(m)² ≥ 0`. -/
private lemma wc_nonneg (m : ℕ) : 0 ≤ Work.FIChain.wc m := by
  rw [Work.FIChain.wc, Work.FITop.w0]; positivity

/-- The constant bounding `|Grho N C t|`, uniformly in `t` (and in `s ∈ [1,C]`):
`Σ_{m ≤ N} wc m · Σ_{n ≤ N} τ(n)·|ã(mn)|`. -/
private noncomputable def GrhoBoundConst (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, Work.FIChain.wc m *
    (∑ n ∈ Finset.Icc 1 N, (n.divisors.card : ℝ) * |Work.FIChain.atilc (m * n)|)

private lemma GrhoBoundConst_nonneg (N : ℕ) : 0 ≤ GrhoBoundConst N := by
  unfold GrhoBoundConst
  refine Finset.sum_nonneg (fun m _ => mul_nonneg (wc_nonneg m) ?_)
  exact Finset.sum_nonneg (fun n _ => mul_nonneg (by positivity) (abs_nonneg _))

/-- **Uniform bound for `Grho`**: for `1 ≤ C` and every `t`,
`|Grho N C t| ≤ GrhoBoundConst N · C`.

The `s`-integrand `Σ_m wc m |XrhoC(…,s,t,2t)|` is bounded by the constant `GrhoBoundConst N`
(`abs_XrhoC_le`), so the `s`-integral over `[1,C]` is at most that constant times `C`. -/
private lemma Grho_abs_le_const (N : ℕ) (C : ℝ) (hC : 1 ≤ C) (u : ℝ) :
    |Work.FIPiChain.Grho N C u| ≤ GrhoBoundConst N * C := by
  set f : ℝ → ℝ := fun s => ∑ m ∈ Finset.Icc 1 N, Work.FIChain.wc m *
      |Work.FITop.XrhoC Work.FIChain.atilc N m s u (2 * u)| with hf
  have hf_meas : Measurable f := by
    rw [hf]
    refine Finset.measurable_sum _ (fun m _ => ?_)
    exact measurable_const.mul
      ((Work.FIChain.measurable_XrhoC Work.FIChain.atilc N m u (2 * u)).abs)
  have hf_bd : ∀ s : ℝ, |f s| ≤ GrhoBoundConst N := by
    intro s
    have hnn : 0 ≤ f s := by
      rw [hf]
      exact Finset.sum_nonneg (fun m _ => mul_nonneg (wc_nonneg m) (abs_nonneg _))
    rw [abs_of_nonneg hnn, hf]
    refine (Finset.sum_le_sum (fun m _ => mul_le_mul_of_nonneg_left
      (Work.FIChain.abs_XrhoC_le Work.FIChain.atilc N m s u (2 * u)) (wc_nonneg m))).trans ?_
    simp only [GrhoBoundConst]
    exact le_rfl
  have hIntF : IntervalIntegrable (fun s : ℝ => f s / s) volume (1 : ℝ) C :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hC).mpr
      (integrableOn_div_of_bound hf_meas hf_bd one_pos)
  have hIntG : IntervalIntegrable (fun s : ℝ => GrhoBoundConst N / s) volume (1 : ℝ) C :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hC).mpr
      (integrableOn_div_of_bound measurable_const
        (fun s => by rw [abs_of_nonneg (GrhoBoundConst_nonneg N)]) one_pos)
  have hpt : ∀ s ∈ Set.Icc (1 : ℝ) C, |f s / s| ≤ GrhoBoundConst N / s := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs.1
    rw [abs_div, abs_of_pos hspos]
    exact div_le_div_of_nonneg_right (hf_bd s) hspos.le
  have hpt2 : ∀ s ∈ Set.Icc (1 : ℝ) C, GrhoBoundConst N / s ≤ GrhoBoundConst N := by
    intro s hs
    have h1 : GrhoBoundConst N / s ≤ GrhoBoundConst N / 1 :=
      div_le_div_of_nonneg_left (GrhoBoundConst_nonneg N) one_pos hs.1
    simpa using h1
  have hGrho : Work.FIPiChain.Grho N C u = ∫ s in (1 : ℝ)..C, f s / s := by
    rw [Work.FIPiChain.Grho, hf]
  calc |Work.FIPiChain.Grho N C u|
      = |∫ s in (1 : ℝ)..C, f s / s| := by rw [hGrho]
    _ ≤ ∫ s in (1 : ℝ)..C, |f s / s| := by
        simpa [Real.norm_eq_abs, abs_div] using
          intervalIntegral.norm_integral_le_integral_norm (f := fun s : ℝ => f s / s) hC
    _ ≤ ∫ s in (1 : ℝ)..C, GrhoBoundConst N / s :=
        intervalIntegral.integral_mono_ae_restrict hC hIntF.abs hIntG
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpt)
    _ ≤ ∫ s in (1 : ℝ)..C, GrhoBoundConst N :=
        intervalIntegral.integral_mono_ae_restrict hC hIntG intervalIntegrable_const
          (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpt2)
    _ ≤ GrhoBoundConst N * C := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        rw [mul_comm (C - 1) (GrhoBoundConst N)]
        exact mul_le_mul_of_nonneg_left (by linarith) (GrhoBoundConst_nonneg N)

/-! ## The main lemma -/

theorem Grho_sum_zavg_le (x : ℕ) (B E : ℝ) (hzc : 1 ≤ Work.FIChain.zc x B) (hE : 0 ≤ E)
    (hwin : Work.FIChain.RhoWindowInt2 Work.FIChain.atilc x Work.FIChain.wc E
      (((⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ))
      (Work.FIChain.zc x B) (Real.exp 1 * (Work.FIChain.sc x B * Work.FIChain.zc x B))) :
    (∫ z in Work.FIChain.zc x B..(Real.exp 1 * Work.FIChain.zc x B),
        (∑ j ∈ Finset.range (Work.FIChain.Jc x B),
          Work.FIPiChain.Grho x (((⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ))
            ((2 : ℝ) ^ j * z)) / z)
      ≤ (Work.FIChain.Jc x B : ℝ) * E := by
  set C : ℝ := (((⌊(Work.FIChain.zc x B) ^ (1 - Work.FIChain.etac)⌋₊ : ℕ) : ℝ)) with hCdef
  set lo : ℝ := Work.FIChain.zc x B with hlodef
  set J : ℕ := Work.FIChain.Jc x B with hJdef
  -- ## The truncation level is at least `1`, so that `Grho` is nonnegative.
  have hC1 : 1 ≤ C := by
    rw [hCdef]
    have h1 : (1 : ℝ) ≤ lo ^ (1 - Work.FIChain.etac) :=
      Real.one_le_rpow (x := lo) (z := 1 - Work.FIChain.etac) hzc
        (by norm_num [Work.FIChain.etac])
    have h2 : (0 : ℕ) < ⌊lo ^ (1 - Work.FIChain.etac)⌋₊ := Nat.floor_pos.mpr h1
    have h3 : (1 : ℕ) ≤ ⌊lo ^ (1 - Work.FIChain.etac)⌋₊ := h2
    exact_mod_cast h3
  -- ## Elementary order facts for the two windows.
  have hlo1 : 1 ≤ lo := by rw [hlodef]; exact hzc
  have hlopos : 0 < lo := lt_of_lt_of_le zero_lt_one hlo1
  have hsc1 : 1 ≤ Work.FIChain.sc x B := by
    rw [Work.FIChain.sc]; exact one_le_pow₀ (by norm_num)
  have hexp1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hepos : 0 < Real.exp 1 := Real.exp_pos 1
  have hlo_e : lo ≤ Real.exp 1 * lo := by nlinarith [hexp1, hlopos]
  have hlo_hi : lo ≤ Real.exp 1 * (Work.FIChain.sc x B * lo) := by
    have h1 : lo ≤ Work.FIChain.sc x B * lo := by nlinarith [hsc1, hlopos]
    nlinarith [hexp1, h1, hlopos]
  -- ## The hypothesis, in integral form.
  have hwinI : (∫ t in lo..(Real.exp 1 * (Work.FIChain.sc x B * lo)),
      Work.FIPiChain.Grho x C t / t) ≤ E :=
    (Work.FIPiChain.RhoWindowInt2_atilc_iff x E C lo
      (Real.exp 1 * (Work.FIChain.sc x B * lo))).mp hwin
  -- ## Measurability and a uniform bound for `Grho x C`.
  have hGmeas : Measurable (fun u : ℝ => Work.FIPiChain.Grho x C u) := Grho_measurable_u x C
  have hVbd : ∀ u : ℝ, |Work.FIPiChain.Grho x C u| ≤ GrhoBoundConst x * C :=
    fun u => Grho_abs_le_const x C hC1 u
  -- ## Integrability of the `j = 0` window (the hypothesis of `integral_mono_interval`).
  have hIntG : IntervalIntegrable (fun t : ℝ => Work.FIPiChain.Grho x C t / t) volume lo
      (Real.exp 1 * (Work.FIChain.sc x B * lo)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hlo_hi).mpr
      (integrableOn_div_of_bound hGmeas hVbd hlopos)
  -- ## Integrability of every dyadic summand (for the interchange of sum and integral).
  have hIntj : ∀ j ∈ Finset.range J,
      IntervalIntegrable (fun z : ℝ => Work.FIPiChain.Grho x C ((2 : ℝ) ^ j * z) / z) volume lo
        (Real.exp 1 * lo) := by
    intro j _
    have hm : Measurable (fun z : ℝ => Work.FIPiChain.Grho x C ((2 : ℝ) ^ j * z)) :=
      hGmeas.comp (measurable_id.const_mul _)
    have hb : ∀ z : ℝ, |Work.FIPiChain.Grho x C ((2 : ℝ) ^ j * z)| ≤ GrhoBoundConst x * C :=
      fun z => hVbd _
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hlo_e).mpr
      (integrableOn_div_of_bound hm hb hlopos)
  -- ## Sum/integral interchange on the `z`-window.
  have hswap : (∫ z in lo..(Real.exp 1 * lo),
        (∑ j ∈ Finset.range J, Work.FIPiChain.Grho x C ((2 : ℝ) ^ j * z)) / z)
      = ∑ j ∈ Finset.range J, ∫ z in lo..(Real.exp 1 * lo),
          Work.FIPiChain.Grho x C ((2 : ℝ) ^ j * z) / z := by
    have hfun : (fun z : ℝ => (∑ j ∈ Finset.range J, Work.FIPiChain.Grho x C ((2 : ℝ) ^ j * z)) / z)
        = fun z : ℝ => ∑ j ∈ Finset.range J, Work.FIPiChain.Grho x C ((2 : ℝ) ^ j * z) / z := by
      funext z; rw [Finset.sum_div]
    rw [hfun]
    exact intervalIntegral.integral_finsetSum hIntj
  -- ## Every dyadic summand is at most `E`.
  have hterm : ∀ j ∈ Finset.range J,
      (∫ z in lo..(Real.exp 1 * lo), Work.FIPiChain.Grho x C ((2 : ℝ) ^ j * z) / z) ≤ E := by
    intro j hj
    have hjJ : j ≤ J := le_of_lt (Finset.mem_range.mp hj)
    have hpow : (2 : ℝ) ^ j ≤ Work.FIChain.sc x B := by
      rw [Work.FIChain.sc]
      exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℝ) < 2)).mpr hjJ
    rw [comp_mul_div_self (Work.FIPiChain.Grho x C) (c := (2 : ℝ) ^ j) (by positivity) lo
      (Real.exp 1 * lo)]
    have hb1 : (2 : ℝ) ^ j * lo ≤ (2 : ℝ) ^ j * (Real.exp 1 * lo) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      nlinarith [hexp1, hlopos]
    have hb2 : (2 : ℝ) ^ j * (Real.exp 1 * lo) ≤ Real.exp 1 * (Work.FIChain.sc x B * lo) := by
      calc (2 : ℝ) ^ j * (Real.exp 1 * lo) = Real.exp 1 * ((2 : ℝ) ^ j * lo) := by ring
        _ ≤ Real.exp 1 * (Work.FIChain.sc x B * lo) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hlopos.le) hepos.le
    have hca : lo ≤ (2 : ℝ) ^ j * lo := by
      have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
      nlinarith [h1, hlopos]
    have hcore := intervalIntegral.integral_mono_interval (μ := volume)
      (f := fun t : ℝ => Work.FIPiChain.Grho x C t / t)
      (a := (2 : ℝ) ^ j * lo) (b := (2 : ℝ) ^ j * (Real.exp 1 * lo))
      (c := lo) (d := Real.exp 1 * (Work.FIChain.sc x B * lo)) hca hb1 hb2 ?_ hIntG
    · linarith [hcore, hwinI]
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun t ht =>
        div_nonneg (Work.FIPiChain.Grho_nonneg x hC1 t)
          (le_of_lt (lt_of_lt_of_le hlopos (le_of_lt ht.1))))
  -- ## Assembly.
  calc (∫ z in lo..(Real.exp 1 * lo),
        (∑ j ∈ Finset.range J, Work.FIPiChain.Grho x C ((2 : ℝ) ^ j * z)) / z)
      = ∑ j ∈ Finset.range J, ∫ z in lo..(Real.exp 1 * lo),
          Work.FIPiChain.Grho x C ((2 : ℝ) ^ j * z) / z := hswap
    _ ≤ ∑ j ∈ Finset.range J, E := Finset.sum_le_sum hterm
    _ = (J : ℝ) * E := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end

end Work.FIPiChain.P3S3
