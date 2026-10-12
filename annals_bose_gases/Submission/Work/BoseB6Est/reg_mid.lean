import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Submission.Work.BoseB6Est.beta_close_bounds
import Submission.Work.BoseB6Est.fsInt
import Submission.Work.BoseB6Est.gFun_beta_diff_lin
import Submission.Work.BoseB6Est.gFun_tau_diff
import Submission.Work.BoseB6Est.radialTauDiffBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node B6-est — the middle region `(c₁, min 4 T]` of the `I₁` estimate

`reg_mid`: the part of `∫₀^∞ r²(G − G₀)dr` over `(c₁, min 4 T]`, where `G` is FS's
physical radial Bogoliubov integrand and `G₀` the model integrand, is bounded by
`3900·ε(μ,ρ_z)`.

Unlike the far region `(4,T]`, on `(c₁, min 4 T]` the radius `r` is *not* bounded
below by a positive constant: the region reaches down to the kinetic cutoff `c₁`,
where `τ̃` vanishes and the isolated pointwise bound `|G| ≤ 26.2 + 26.2²/(2r²)`
is useless (and `r²·(G−G₀)` fails to be `O(ε)` pointwise).  The estimate is
therefore made on the *two-variable increment*

  `G − G₀ = [gFun τ̃(r) β(r) r − gFun r² β(r) r] + [gFun r² β(r) r − gFun r² 8π r]`

(`fsGR_eq_gFun`, `fsG0R_eq_gFun`), each summand of which carries a factor
`(r² − τ̃(r))` resp. `(β(r) − 8π)`:

* **τ-increment** (`gFun_tau_diff`): `≤ 2β²(r²−τ̃)/(2τ̃+β) ≤ 2β(r²−τ̃)`, and
  `r² − τ̃(r) ≤ 2r(c₁ + ε_Tc₂)` (`radialTauDiffBound`), `β(r) ≤ 26.2` on `r ≤ T`
  (`FsKernel.beta_le_B0`).  Hence `r²·[τ-part] ≤ 4·26.2·(c₁+ε_Tc₂)·r`.
* **β-increment** (`gFun_beta_diff_lin`): `|gFun r² β r − gFun r² 8π r|
  ≤ max(β,8π)|β−8π|/r² ≤ 26.2·η·r/r²`, and `|β(r) − 8π| ≤ ηr`
  (`beta_close_bounds`).  Hence `r²·[β-part] ≤ 26.2·η·r`.

Both right-hand sides are linear in `r`, and

  `c₁ ≤ 2ε`, `ε_Tc₂ ≤ ε` (`FsI1Regime.c1_le_eps`, `FsI1Regime.eTc2_le_eps`),
  `η ≤ ε` (`hEpsEta`),

so, integrating over `(c₁, min 4 T] ⊆ (0,4]` where `∫ r dr = 8`,

  `∫_{(c₁,min 4 T]} r²(G−G₀) ≤ (105·(c₁+ε_Tc₂) + 26.2·η)·8 ≤ (105·3 + 26.2)·8·ε`,

which is `2729.6·ε ≤ 3900·ε`.  The constant `105 = 4·26.2 + 0.2` is the crude
`4·26.2 = 104.8` rounded up, so that no sharp numerical optimisation is needed.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators

set_option maxHeartbeats 1000000

namespace Work.BoseB6Est

/-! ## The two pure increment bounds

These are stated for abstract reals: they only use `gFun_tau_diff` and
`gFun_beta_diff_lin` and the two *linear* size hypotheses on the increments. -/

/-- **The `τ`-increment is `O(r² − τ)`.**  For `0 ≤ τ ≤ r²`, `0 < β ≤ B`,
`r > 0` and `r² − τ ≤ 2rS` with `S ≥ 0`:
`r²·[gFun τ β r − gFun r² β r] ≤ 4B·S·r`.

Indeed `gFun τ β r − gFun r² β r ≤ 2β²(r²−τ)/(r²(2τ+β))`, so after multiplying by
`r²` the bound is `2β²(r²−τ)/(2τ+β) ≤ 2β(r²−τ) ≤ 2β·2rS ≤ 4BSr`. -/
lemma gFun_tau_increment_le {τ b r S B : ℝ}
    (hτ : 0 ≤ τ) (hτr : τ ≤ r ^ 2) (hb : 0 < b) (hbB : b ≤ B)
    (hr : 0 < r) (hS : 0 ≤ S) (hd : r ^ 2 - τ ≤ 2 * r * S) :
    r ^ 2 * (gFun τ b r - gFun (r ^ 2) b r) ≤ 4 * B * S * r := by
  have hb0 : 0 ≤ b := hb.le
  have hd0 : 0 ≤ r ^ 2 - τ := by linarith
  have hden : 0 < 2 * τ + b := by linarith
  have hA := gFun_tau_diff hτ hτr hb0 hr
  have step1 : r ^ 2 * (gFun τ b r - gFun (r ^ 2) b r)
      ≤ r ^ 2 * (2 * b ^ 2 * (r ^ 2 - τ) / (r ^ 2 * (2 * τ + b))) :=
    mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hA) (sq_nonneg r)
  have step2 : r ^ 2 * (2 * b ^ 2 * (r ^ 2 - τ) / (r ^ 2 * (2 * τ + b)))
      = 2 * b ^ 2 * (r ^ 2 - τ) / (2 * τ + b) := by
    field_simp
  have step3 : 2 * b ^ 2 * (r ^ 2 - τ) / (2 * τ + b) ≤ 2 * b * (r ^ 2 - τ) := by
    rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg (mul_nonneg hb0 hd0) hτ]
  have step4 : 2 * b * (r ^ 2 - τ) ≤ 2 * b * (2 * r * S) := by nlinarith [hb0, hd]
  have step5 : 2 * b * (2 * r * S) ≤ 4 * B * S * r := by
    nlinarith [hbB, mul_nonneg hr.le hS, hb0, hS]
  linarith [step1, step2, step3, step4, step5]

/-- **The `β`-increment is `O(|β − 8π|)`.**  With `B ≥ max b b'` and
`|b − b'| ≤ ηr`: `r²·[gFun r² b r − gFun r² b' r] ≤ B·η·r`. -/
lemma gFun_beta_increment_le {b b' r B η : ℝ}
    (hb : 0 ≤ b) (hb' : 0 ≤ b') (hr : 0 < r) (hB : max b b' ≤ B)
    (hab : |b - b'| ≤ η * r) :
    r ^ 2 * (gFun (r ^ 2) b r - gFun (r ^ 2) b' r) ≤ B * η * r := by
  have hA := gFun_beta_diff_lin (b := b) (b' := b') (r := r) hb hb' hr
  have step1 : r ^ 2 * (gFun (r ^ 2) b r - gFun (r ^ 2) b' r)
      ≤ r ^ 2 * (max b b' / r ^ 2 * |b - b'|) :=
    mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) hA) (sq_nonneg r)
  have step2 : r ^ 2 * (max b b' / r ^ 2 * |b - b'|) = max b b' * |b - b'| := by
    field_simp
  have step3 : max b b' * |b - b'| ≤ B * (η * r) := by
    have h0 : 0 ≤ max b b' := le_trans hb (le_max_left b b')
    have h1 : 0 ≤ |b - b'| := abs_nonneg _
    nlinarith [hB, h0, h1, hab]
  calc r ^ 2 * (gFun (r ^ 2) b r - gFun (r ^ 2) b' r)
      ≤ max b b' * |b - b'| := le_trans step1 (le_of_eq step2)
    _ ≤ B * (η * r) := step3
    _ = B * η * r := by ring

/-! ## The pointwise bound on `(c₁, min 4 T]` -/

/-- **Pointwise bound on the middle region.**  For `r ∈ (c₁, min 4 T]`,

  `r²(G(r) − G₀(r)) ≤ (105·(c₁ + ε_Tc₂) + 26.2·η)·r`. -/
theorem reg_mid_pointwise (K : FsKernel) {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) {r : ℝ}
    (hr : r ∈ Set.Ioc c1 (min 4 K.T)) :
    r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r)
      ≤ (105 * (c1 + εT * c2) + 26.2 * K.η) * r := by
  have hrmin : r ≤ min 4 K.T := hr.2
  have hrT : r ≤ K.T := le_trans hrmin (min_le_right (4:ℝ) K.T)
  have hr0 : 0 < r := lt_of_le_of_lt h.hc1 hr.1
  have hε1 : εT ≤ 1 := by linarith [h.hε1]
  have hc2 : 0 ≤ c2 := le_trans h.hc1 h.hc12
  have hτ0 : 0 ≤ Work.BoseB6.fsTau εT c1 c2 r := fsTau_nonneg h.hε0 hε1 hr0.le
  have hτy : Work.BoseB6.fsTau εT c1 c2 r ≤ r ^ 2 :=
    fsTau_le_sq h.hε0 h.hε1 h.hc1 h.hc12 hr0.le
  have hb0 : 0 ≤ K.β r := K.nonneg r
  have hbhi : K.β r ≤ 26.2 := FsKernel.beta_le_B0 K h.hηT hr0
  have hβabs : |K.β r - 8 * Real.pi| ≤ K.η * r :=
    (beta_close_bounds h.hηT hr0.le hrT).2.1
  have hbpos : 0 < K.β r := by
    have h8 : 8 * Real.pi - 1 ≤ K.β r := (beta_close_bounds h.hηT hr0.le hrT).2.2.2
    nlinarith [Real.pi_gt_three]
  have hτd : r ^ 2 - Work.BoseB6.fsTau εT c1 c2 r ≤ 2 * r * (c1 + εT * c2) :=
    radialTauDiffBound h.hε0 hε1 h.hc1 h.hc12 hr0.le
  have hS0 : 0 ≤ c1 + εT * c2 := by nlinarith [mul_nonneg h.hε0 hc2, h.hc1]
  have hπ : (8 : ℝ) * Real.pi ≤ 26.2 := by nlinarith [Real.pi_lt_d2]
  -- split into the `τ`- and `β`-increments
  have hsplit : fsGR K εT c1 c2 r - fsG0R r
      = (gFun (Work.BoseB6.fsTau εT c1 c2 r) (K.β r) r - gFun (r ^ 2) (K.β r) r)
        + (gFun (r ^ 2) (K.β r) r - gFun (r ^ 2) (8 * Real.pi) r) := by
    rw [fsGR_eq_gFun, fsG0R_eq_gFun]
    ring
  rw [hsplit, mul_add]
  have hA := gFun_tau_increment_le hτ0 hτy hbpos hbhi hr0 hS0 hτd
  have hB := gFun_beta_increment_le hb0 (le_of_lt (by positivity : (0:ℝ) < 8 * Real.pi))
    hr0 (max_le hbhi hπ) hβabs
  have hA' : r ^ 2 * (gFun (Work.BoseB6.fsTau εT c1 c2 r) (K.β r) r - gFun (r ^ 2) (K.β r) r)
      ≤ 105 * (c1 + εT * c2) * r := by
    refine le_trans hA ?_
    nlinarith [mul_nonneg hS0 hr0.le]
  have hB' : r ^ 2 * (gFun (r ^ 2) (K.β r) r - gFun (r ^ 2) (8 * Real.pi) r)
      ≤ 26.2 * K.η * r := hB
  nlinarith [hA', hB']

/-! ## The integral over `(c₁, min 4 T]` -/

theorem reg_mid (K : FsKernel) {a R ρz μ εT c1 c2 Kl s d : ℝ}
    (h : FsI1Regime K a R ρz μ εT c1 c2 Kl s d) :
    (∫ r in Set.Ioc c1 (min 4 K.T), r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r))
      ≤ 3900 * Work.BoseB6.lhyEps a R εT Kl s d μ := by
  have hε0 : 0 ≤ Work.BoseB6.lhyEps a R εT Kl s d μ := FsI1Regime.lhyEps_nonneg h
  have hε1 : εT ≤ 1 := by linarith [h.hε1]
  have hS3 : c1 + εT * c2 ≤ 3 * Work.BoseB6.lhyEps a R εT Kl s d μ :=
    h.c1_add_eTc2_le
  have hηe : K.η ≤ Work.BoseB6.lhyEps a R εT Kl s d μ := h.hEpsEta
  have hc2 : 0 ≤ c2 := le_trans h.hc1 h.hc12
  have hS0 : 0 ≤ c1 + εT * c2 := by nlinarith [mul_nonneg h.hε0 hc2, h.hc1]
  have hC0 : 0 ≤ 105 * (c1 + εT * c2) + 26.2 * K.η := by nlinarith [K.ηnn]
  -- integrability of the integrand and of the majorant
  have hg1 : IntegrableOn (fun r : ℝ => r ^ 2 * fsGR K εT c1 c2 r) (Set.Ioi 0) :=
    integrableOn_r2_fsGR K h.hε0 hε1 h.hηT
  have hg0 : IntegrableOn (fun r : ℝ => r ^ 2 * fsG0R r) (Set.Ioi 0) :=
    integrableOn_r2_fsG0R
  have hg : IntegrableOn (fun r : ℝ => r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r))
      (Set.Ioi 0) :=
    (MeasureTheory.integrableOn_congr_fun
      (f := fun r : ℝ => r ^ 2 * fsGR K εT c1 c2 r - r ^ 2 * fsG0R r)
      (g := fun r : ℝ => r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r))
      (fun r _ => by ring) measurableSet_Ioi).mp (hg1.sub hg0)
  have hmaj : IntegrableOn (fun r : ℝ => (105 * (c1 + εT * c2) + 26.2 * K.η) * r)
      (Set.Ioc c1 (min 4 K.T)) := by
    refine IntegrableOn.of_bound (μ := volume) (s := Set.Ioc c1 (min 4 K.T))
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) ?_
      ((105 * (c1 + εT * c2) + 26.2 * K.η) * 4) ?_
    · exact (measurable_const.mul measurable_id).aestronglyMeasurable.restrict
    · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall (fun r hr => ?_)
      have hr4 : r ≤ 4 := le_trans hr.2 (min_le_left (4:ℝ) K.T)
      have hr0 : 0 ≤ r := le_trans h.hc1 hr.1.le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC0 hr0)]
      nlinarith [hr4, hC0]
  -- monotone comparison with the majorant
  have hmono : (∫ r in Set.Ioc c1 (min 4 K.T),
        r ^ 2 * (fsGR K εT c1 c2 r - fsG0R r))
      ≤ ∫ r in Set.Ioc c1 (min 4 K.T), (105 * (c1 + εT * c2) + 26.2 * K.η) * r :=
    setIntegral_mono_on (hg.mono_set (fun r hr => lt_of_le_of_lt h.hc1 hr.1))
      hmaj measurableSet_Ioc (fun r hr => reg_mid_pointwise K h hr)
  -- `∫_{(c₁, min 4 T]} r ≤ 8`
  have hct : c1 ≤ min 4 K.T :=
    le_min (le_trans (FsI1Regime.c1_le_one h) (by norm_num)) h.hc1T.le
  have hr8 : (∫ r in Set.Ioc c1 (min 4 K.T), r) ≤ 8 := by
    rw [← intervalIntegral.integral_of_le hct, integral_id]
    have h1 : min 4 K.T ≤ 4 := min_le_left (4:ℝ) K.T
    have h2 : 0 ≤ min 4 K.T := le_trans h.hc1 hct
    have h3 : (min 4 K.T) ^ 2 ≤ 16 := by nlinarith
    nlinarith [sq_nonneg c1]
  have hCm : (∫ r in Set.Ioc c1 (min 4 K.T), (105 * (c1 + εT * c2) + 26.2 * K.η) * r)
      = (105 * (c1 + εT * c2) + 26.2 * K.η)
        * (∫ r in Set.Ioc c1 (min 4 K.T), r) :=
    MeasureTheory.integral_const_mul _ _
  have hfin : (105 * (c1 + εT * c2) + 26.2 * K.η)
        * (∫ r in Set.Ioc c1 (min 4 K.T), r)
      ≤ 3900 * Work.BoseB6.lhyEps a R εT Kl s d μ := by
    have h1 : (105 * (c1 + εT * c2) + 26.2 * K.η) * 8
        ≤ 3900 * Work.BoseB6.lhyEps a R εT Kl s d μ := by
      nlinarith [hS3, hηe, hε0]
    nlinarith [hC0, hr8, h1]
  linarith [hmono, hCm, hfin]

end Work.BoseB6Est
