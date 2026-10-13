/-
# `psiSeries_atTop_zero_of_cptQ` — the mode series decays at `z = ∞`

For `0 < α ≤ 1/4` and a source `G` which is `C^∞` on `ℝ²` and supported in a compact rectangle
of the *open* quadrant, the mode series `psiSeries α G z θ = Σ_m acoeff α m G z · eFam m θ` of
the mode-wise solution of `bslOp α Ψ = G` tends to `0` as `z → ∞`, for every `θ ∈ Iθ`.

**Route.**  Since every slice of `G` vanishes identically off the support box `[a,b] × [c,d]`
(`0 < a`), the source `c_m := cmode m G` of the `m`-th mode radial equation is supported in
`[a,b]`.  Two facts then combine:

* **decay of the radial Green function.**  For *every* `m` (including `m = 0`, where the
  growing indicial exponent is `rgP α 0 = 0` and the sharper Cauchy–Schwarz bound of
  `ModalSolution.radGreen_abs_le` is unavailable) one has

    `|radGreen α m c z| ≤ 2·rgK α m·√(∫_{z>0} c²)·z^{-1/2}`   (`z > 0`),

  i.e. each `acoeff α m G ·` decays like `z^{-1/2}`, with the `m`-dependence carried entirely
  by the finite `L²` mass `B m := √(∫_{z>0} (cmode m G)²)`
  (`RadGreenAll.radGreen_abs_le_all`);
* **decay of the masses.**  `B m` itself is rapidly small: under a uniform bound
  `|cmode m G| ≤ Mb m` with `Mb m ≲ (m+1)^{-4}` — for `m ≥ 1` the rapid decay of the mode
  coefficients of a compactly supported smooth source
  (`Honesty.cmode_decay_of_cptQ`), for `m = 0` the crude bound
  `Honesty.CmodeZero.cmode_zero_abs_le_of_cptQ` — the support estimate
  `Honesty.CmodeMass.cmode_sq_mass_le` gives `B m ≤ Mb m √b`, and the resulting majorant
  `bound m = 6·(rgK α m·(m+1))·Mb m·√b` is summable, since `rgK α m·(m+1) ≤ 1/(4α)`.

Tannery's theorem (`tendsto_tsum_of_dominated_convergence`) for the filter `atTop` then
interchanges the limit with the `tsum`: every summand
`acoeff α m G · · eFam m θ` tends to `0` (squeeze against `z^{-1/2} → 0`, a constant times
`|eFam m θ| ≤ 3(m+1)`), and on `z ≥ 1` the whole family is dominated by the summable `bound`,
using `z^{-1/2} ≤ 1`.

Note that no moment condition (`Fstar G = 0`) on the source is assumed: the `m = 0` mode is
handled by the uniform (rather than decaying) bound `cmode_zero_abs_le_of_cptQ`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Honesty.CptDefs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le
import Submission.Work.FTS.EllExist.RadGreenDefs
import Submission.Work.EllipticEst.ModalSolution.cmode_memLp
import Submission.Work.FTS.PhiStar.Honesty.cmode_decay_of_cptQ
import Submission.Work.FTS.PhiStar.Honesty.RadGreenAll.radGreen_abs_le_all
import Submission.Work.FTS.PhiStar.Honesty.CmodeMass.cmode_sq_mass_le
import Submission.Work.FTS.PhiStar.Honesty.CmodeZero.cmode_zero_abs_le_of_cptQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter
open scoped Real Topology BigOperators

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-! ## Elementary arithmetic -/

/-- `rgK α m · (m+1) ≤ 1/(4α)`; this is what makes the majorant summable. -/
private lemma rgK_mul_succ_le {α : ℝ} (hα : 0 < α) (m : ℕ) :
    Work.FTS.EllExist.rgK α m * ((m : ℝ) + 1) ≤ 1 / (4 * α) := by
  have hden : 0 < α * (4 * (m : ℝ) + 5) := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    positivity
  have hden' : 0 < 4 * α := by positivity
  rw [Work.FTS.EllExist.rgK, one_div_mul_eq_div, div_le_div_iff₀ hden hden']
  nlinarith [Nat.cast_nonneg (α := ℝ) m]

/-- `Σ_m 1/(m+1)^4` converges. -/
private lemma summable_one_div_add_one_pow_four :
    Summable (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1) ^ 4) := by
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 4) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  have hshift := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 4) 1).mpr hbase
  simpa only [Nat.cast_add, Nat.cast_one] using hshift

/-- The arithmetic comparison behind the summability of the majorant. -/
private lemma bound_le_aux {α b K C : ℝ} (hα : 0 < α) (hK : 0 ≤ K) (hC : 0 ≤ C) (m : ℕ) :
    6 * (Work.FTS.EllExist.rgK α m * ((m : ℝ) + 1)) * ((K + C) / ((m : ℝ) + 1) ^ 4)
        * Real.sqrt b
      ≤ (3 * Real.sqrt b * (K + C) / (2 * α)) / ((m : ℝ) + 1) ^ 4 := by
  have hrk := rgK_mul_succ_le hα m
  have hden : 0 < ((m : ℝ) + 1) ^ 4 := by positivity
  have hKC : 0 ≤ K + C := by linarith
  have hb : (0 : ℝ) ≤ Real.sqrt b := Real.sqrt_nonneg b
  have hstep : 6 * (Work.FTS.EllExist.rgK α m * ((m : ℝ) + 1)) ≤ 6 * (1 / (4 * α)) := by
    linarith
  have h1 : 6 * (Work.FTS.EllExist.rgK α m * ((m : ℝ) + 1))
        * ((K + C) / ((m : ℝ) + 1) ^ 4) * Real.sqrt b
      ≤ 6 * (1 / (4 * α)) * ((K + C) / ((m : ℝ) + 1) ^ 4) * Real.sqrt b := by
    have h2 := mul_le_mul_of_nonneg_right hstep (div_nonneg hKC hden.le)
    calc 6 * (Work.FTS.EllExist.rgK α m * ((m : ℝ) + 1))
            * ((K + C) / ((m : ℝ) + 1) ^ 4) * Real.sqrt b
        = (6 * (Work.FTS.EllExist.rgK α m * ((m : ℝ) + 1))
            * ((K + C) / ((m : ℝ) + 1) ^ 4)) * Real.sqrt b := by ring
      _ ≤ (6 * (1 / (4 * α)) * ((K + C) / ((m : ℝ) + 1) ^ 4)) * Real.sqrt b :=
          mul_le_mul_of_nonneg_right h2 hb
      _ = 6 * (1 / (4 * α)) * ((K + C) / ((m : ℝ) + 1) ^ 4) * Real.sqrt b := by ring
  refine le_trans h1 (le_of_eq ?_)
  have hαne : α ≠ 0 := hα.ne'
  have hdne : ((m : ℝ) + 1) ^ 4 ≠ 0 := hden.ne'
  field_simp
  ring

/-! ## The decay of the mode series -/

theorem psiSeries_atTop_zero_of_cptQ {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.PhiStar.Honesty.SmoothCptQ G) :
    ∀ θ ∈ Work.Spaces.Iθ,
      Filter.Tendsto (fun z => Work.FTS.PhiStar.Series.psiSeries α G z θ)
        Filter.atTop (nhds 0) := by
  intro θ hθ
  -- ## the support box, the `m = 0` bound, the rapid decay
  obtain ⟨a, b, c, d, ha, hab, hc, hcd, hd, Hbox⟩ := hG.cpt.exists_box
  have hb0 : 0 ≤ b := le_of_lt (lt_trans ha hab)
  obtain ⟨K0, hK00, hK0b⟩ := Work.FTS.PhiStar.Honesty.CmodeZero.cmode_zero_abs_le_of_cptQ hG
  obtain ⟨C, hC0, hCb⟩ := Work.FTS.PhiStar.Honesty.cmode_decay_of_cptQ hG 0 4
  have hα1 : α ≤ 1 := by linarith
  -- ## the mode coefficients vanish when the slice does
  have hcmzero : ∀ (m : ℕ) (z : ℝ), z ∉ Set.Icc a b →
      Work.FTS.PhiStar.Series.cmode m G z = 0 := by
    intro m z hz
    have hslice : ∀ θ' : ℝ, G z θ' = 0 := by
      intro θ'
      by_contra hne
      exact hz (Hbox z θ' hne).1
    have hnum : (∫ θ' in (0 : ℝ)..(Real.pi / 2),
        G z θ' * Work.FTS.PhiStar.Gegenbauer.eFam m θ' * Real.cos θ') = 0 := by
      have h1 : (∫ θ' in (0 : ℝ)..(Real.pi / 2),
            G z θ' * Work.FTS.PhiStar.Gegenbauer.eFam m θ' * Real.cos θ')
          = ∫ θ' in (0 : ℝ)..(Real.pi / 2), (0 : ℝ) :=
        intervalIntegral.integral_congr (fun x _ => by rw [hslice x, zero_mul, zero_mul])
      rw [h1, intervalIntegral.integral_zero]
    rw [Work.FTS.PhiStar.Series.cmode, hnum, zero_div]
  -- ## a single sup bound for every mode
  set Msup : ℕ → ℝ := fun m => (K0 + C) / ((m : ℝ) + 1) ^ 4 with hMsupdef
  have hMsup0 : ∀ m, 0 ≤ Msup m := by
    intro m
    rw [hMsupdef]
    positivity
  have hcmb : ∀ m t, |Work.FTS.PhiStar.Series.cmode m G t| ≤ Msup m := by
    intro m t
    rw [hMsupdef]
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      have h1 : K0 ≤ K0 + C := by linarith
      simpa using le_trans (hK0b t) h1
    · have h := hCb m hm t
      rw [Work.Spaces.DzIter_zero] at h
      have h2 : C / ((m : ℝ) + 1) ^ 4 ≤ (K0 + C) / ((m : ℝ) + 1) ^ 4 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith
      exact le_trans h h2
  -- ## the `L²` mass of the source of the radial equation
  have hmass : ∀ m : ℕ,
      MeasureTheory.IntegrableOn
          (fun t : ℝ => Work.FTS.PhiStar.Series.cmode m G t ^ 2) (Set.Ioi 0) ∧
        (∫ t in Set.Ioi 0, (Work.FTS.PhiStar.Series.cmode m G t) ^ 2) ≤ (Msup m) ^ 2 * b := by
    intro m
    refine Work.FTS.PhiStar.Honesty.CmodeMass.cmode_sq_mass_le
      (c := fun t => Work.FTS.PhiStar.Series.cmode m G t) hb0 (hMsup0 m)
      (Work.EllipticEst.ModalSolution.aesm_cmode hG.smoothOpen m) ?_ (fun t => hcmb m t)
    intro t ht
    exact hcmzero m t (fun hmem => absurd hmem.2 (not_le.mpr ht))
  -- ## the `L²` mass and its square root
  set B : ℕ → ℝ := fun m => Real.sqrt (∫ t in Set.Ioi 0, Work.FTS.PhiStar.Series.cmode m G t ^ 2)
    with hBdef
  have hBle : ∀ m, B m ≤ Msup m * Real.sqrt b := by
    intro m
    have h := (hmass m).2
    have h2 : Real.sqrt (∫ t in Set.Ioi 0, Work.FTS.PhiStar.Series.cmode m G t ^ 2)
        ≤ Real.sqrt ((Msup m) ^ 2 * b) := Real.sqrt_le_sqrt h
    rw [Real.sqrt_mul (sq_nonneg (Msup m)), Real.sqrt_sq (hMsup0 m)] at h2
    simpa only [hBdef] using h2
  -- ## the per-mode bound (with the uniform constant `2`)
  have hac : ∀ m z, 0 < z →
      |Work.FTS.PhiStar.Series.acoeff α m G z| ≤
        2 * Work.FTS.EllExist.rgK α m * B m * z ^ (-(1 / 2) : ℝ) := by
    intro m z hz
    have h := Work.FTS.PhiStar.Honesty.RadGreenAll.radGreen_abs_le_all
      (hα := hα) (hα1 := hα1) m (hmass m).1 hz
    rw [Work.FTS.PhiStar.Series.acoeff]
    simpa only [hBdef] using h
  -- ## each summand tends to `0`
  have hlim : ∀ m : ℕ, Filter.Tendsto
      (fun z : ℝ => Work.FTS.PhiStar.Series.acoeff α m G z
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ) Filter.atTop (nhds 0) := by
    intro m
    have hz : Filter.Tendsto (fun z : ℝ => z ^ (-(1 / 2) : ℝ)) Filter.atTop (nhds 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have hC' : Filter.Tendsto (fun z : ℝ =>
        (2 * Work.FTS.EllExist.rgK α m * B m
          * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|) * z ^ (-(1 / 2) : ℝ))
        Filter.atTop (nhds 0) := by
      have h0 := hz.const_mul
        (2 * Work.FTS.EllExist.rgK α m * B m * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|)
      simpa using h0
    refine squeeze_zero_norm' ?_ hC'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz0
    rw [Real.norm_eq_abs, abs_mul]
    calc |Work.FTS.PhiStar.Series.acoeff α m G z|
            * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ (2 * Work.FTS.EllExist.rgK α m * B m * z ^ (-(1 / 2) : ℝ))
            * |Work.FTS.PhiStar.Gegenbauer.eFam m θ| :=
          mul_le_mul_of_nonneg_right (hac m z hz0) (abs_nonneg _)
      _ = (2 * Work.FTS.EllExist.rgK α m * B m
            * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|) * z ^ (-(1 / 2) : ℝ) := by ring
  -- ## the summable majorant
  set bound : ℕ → ℝ := fun m =>
    6 * (Work.FTS.EllExist.rgK α m * ((m : ℝ) + 1)) * Msup m * Real.sqrt b with hbounddef
  have hbound0 : ∀ m, 0 ≤ bound m := by
    intro m
    rw [hbounddef]
    have hrk : 0 < Work.FTS.EllExist.rgK α m := Work.FTS.EllExist.rgK_pos hα m
    positivity
  have hbound_le : ∀ m : ℕ,
      bound m ≤ (3 * Real.sqrt b * (K0 + C) / (2 * α)) / ((m : ℝ) + 1) ^ 4 := by
    intro m
    rw [hbounddef]
    exact bound_le_aux (b := b) (K := K0) (C := C) hα hK00 hC0 m
  have hsum : Summable bound := by
    have hbase : Summable (fun m : ℕ => (3 * Real.sqrt b * (K0 + C) / (2 * α))
        / ((m : ℝ) + 1) ^ 4) := by
      have h0 : Summable (fun m : ℕ => (3 * Real.sqrt b * (K0 + C) / (2 * α))
          * ((1 : ℝ) / ((m : ℝ) + 1) ^ 4)) :=
        summable_one_div_add_one_pow_four.mul_left _
      exact h0.congr (fun m => (div_eq_mul_one_div _ _).symm)
    exact Summable.of_nonneg_of_le hbound0 hbound_le hbase
  -- ## the domination
  have hdom : ∀ᶠ z in Filter.atTop, ∀ m : ℕ,
      ‖Work.FTS.PhiStar.Series.acoeff α m G z
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ‖ ≤ bound m := by
    refine eventually_atTop.mpr ⟨1, fun z hz1 => ?_⟩
    intro m
    have hz0 : (0 : ℝ) < z := lt_of_lt_of_le one_pos hz1
    have hzp : z ^ (-(1 / 2) : ℝ) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hz1 (by norm_num)
    have hE : |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ 3 * ((m : ℝ) + 1) :=
      le_trans (Work.FTS.PhiStar.Series.abs_eFam_le_sqrt_Npsi m hθ)
        (Work.FTS.PhiStar.Series.sqrt_Npsi_le_three m)
    have hAc : 0 ≤ 2 * Work.FTS.EllExist.rgK α m * B m * z ^ (-(1 / 2) : ℝ) := by
      have hrk : 0 < Work.FTS.EllExist.rgK α m := Work.FTS.EllExist.rgK_pos hα m
      positivity
    have hmid : 2 * Work.FTS.EllExist.rgK α m * B m * z ^ (-(1 / 2) : ℝ)
        ≤ 2 * Work.FTS.EllExist.rgK α m * Msup m * Real.sqrt b := by
      have h1 : B m * z ^ (-(1 / 2) : ℝ) ≤ Msup m * Real.sqrt b :=
        calc B m * z ^ (-(1 / 2) : ℝ) ≤ (Msup m * Real.sqrt b) * z ^ (-(1 / 2) : ℝ) :=
              mul_le_mul_of_nonneg_right (hBle m) (Real.rpow_nonneg hz0.le _)
          _ ≤ (Msup m * Real.sqrt b) * 1 :=
              mul_le_mul_of_nonneg_left hzp (mul_nonneg (hMsup0 m) (Real.sqrt_nonneg b))
          _ = Msup m * Real.sqrt b := mul_one _
      have hrk2 : 0 ≤ 2 * Work.FTS.EllExist.rgK α m := by
        have hrk : 0 < Work.FTS.EllExist.rgK α m := Work.FTS.EllExist.rgK_pos hα m
        linarith
      calc 2 * Work.FTS.EllExist.rgK α m * B m * z ^ (-(1 / 2) : ℝ)
          = 2 * Work.FTS.EllExist.rgK α m * (B m * z ^ (-(1 / 2) : ℝ)) := by ring
        _ ≤ 2 * Work.FTS.EllExist.rgK α m * (Msup m * Real.sqrt b) :=
            mul_le_mul_of_nonneg_left h1 hrk2
        _ = 2 * Work.FTS.EllExist.rgK α m * Msup m * Real.sqrt b := by ring
    rw [Real.norm_eq_abs, abs_mul]
    calc |Work.FTS.PhiStar.Series.acoeff α m G z|
            * |Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ (2 * Work.FTS.EllExist.rgK α m * B m * z ^ (-(1 / 2) : ℝ))
            * (3 * ((m : ℝ) + 1)) := mul_le_mul (hac m z hz0) hE (abs_nonneg _) hAc
      _ ≤ (2 * Work.FTS.EllExist.rgK α m * Msup m * Real.sqrt b)
            * (3 * ((m : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hmid (by positivity)
      _ = bound m := by rw [hbounddef]; ring
  -- ## Tannery
  have hmain := tendsto_tsum_of_dominated_convergence (𝓕 := Filter.atTop)
    (f := fun z m => Work.FTS.PhiStar.Series.acoeff α m G z
      * Work.FTS.PhiStar.Gegenbauer.eFam m θ)
    (g := fun _ : ℕ => (0 : ℝ)) (bound := bound) hsum hlim hdom
  simpa only [tsum_zero, Work.FTS.PhiStar.Series.psiSeries] using hmain

end Work.FTS.PhiStar.Honesty
