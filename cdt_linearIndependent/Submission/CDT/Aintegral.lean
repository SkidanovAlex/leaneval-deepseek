import Mathlib
import Submission.CDT.ZagierH
import Submission.CDT.ZagierHBC
import Submission.CDT.L2chi3Corollary
import Submission.CDT.EichlerInput
import Submission.Commons.Analysis.Integral.doubleIntegral_inv_one_sub_mul
import Submission.Commons.Analysis.Integral.zetaintegral_recurrence_parametric

/-!
# The ζ-side of node (2): the paper's `(Aintegral)` display

The paper (Remark after Proposition `functionsH`, display `(Aintegral)`)
gives the ζ-analogue of the `(Cintegral)` display, this time for the
**Möbius transform** `f ↦ (1/(1+x))·f(x/(x+1))` of the companion series
(the paper's `(Gs)` display, in which the transform of `H_A` is Zagier's
sequence **A**: `1, 2, 10, 56, …`, and the transform of `H_C` starts
`x + 4x² + (208/9)x³ + …`):

```lean
ζ(2)·G_A(x) − 4·G_C(x) = Σₙ xⁿ·(−1)ⁿ·∫₀¹∫₀¹ (1−s²)ⁿ(1−t²)ⁿ/(1−st)^{n+1} ds dt
```

with `G_A(x) = (1/(1+x))·H_A(x/(x+1))`, `G_C(x) = (1/(1+x))·H_C(x/(x+1))`.

This module formalises that display's *infrastructure*:

* the formal Möbius map `mobPhi = x/(1+x)` and the transform `mobTrans`,
  with `GAtr = mobTrans HA`, `GCtr = mobTrans HC` — the coefficient streams
  of `GAtr`/`GCtr` are what the display speaks about;
* the ζ-side double integral `zetaJ n` and the pointwise kernel bound that
  the paper uses (`max |(1−s²)(1−t²)/(1−st)| = 1`, attained at `s = t = 0`,
  i.e. `(1−s²)(1−t²) ≤ (1−st)²`), together with the resulting uniform bound
  `|zetaJ n| ≤ ζ(2)` (`zetaJ_bound`) and the `n = 0` evaluation
  `zetaJ 0 = ζ(2) = ∫∫dsdt/(1−st)` (commons
  `doubleIntegral_inv_one_sub_mul`);
* **the ζ-side recurrence is PROVED** (`zetaJ_recurrence`, all `n ≥ 1`)
  from the commons lemma `zetaintegral_recurrence_parametric` (fleet L136):
  `(n+1)²I_{n+1} = −(7n²+7n+2)Iₙ + 8n²I_{n−1}` — the exact companion of the
  `(7,−8,2)` Zagier recurrence of `G_A`/`G_C`;
* the coefficient identity `AintegralIdentity` (the paper's display); its
  `n = 0` instance `AintegralIdentityAt_zero` is PROVED here: the transform's
  constant terms `[x⁰]G_A = 1`, `[x⁰]G_C = 0` come from
  `mobTrans_coeff_zero`, and `I₀ = ζ(2)` is `zetaJ_zero_eq`.  **The identity
  for all `n` is PROVED in the companion module
  `Submission.CDT.AintegralAssembled`** (`AintegralIdentity_proved`); the
  route, recorded here and carried out there: with the *correct* gauge factor
  (`f(u) = G(u/(1−u))/(1−u)`) the pullback of
  `u(1−u)(1−9u)f'' + (1−20u+27u²)f' + 3(3u−1)f = 0` under the Möbius map
  `u = x/(1+x)` is exactly the `(7,−8,2)`-ODE
  `x(1−8x)(1+x)G'' + (1−14x−24x²)G' − 2(1+4x)G = 0` (commons
  `Commons.Analysis.Differential.ode_pullback_mobius`, fleet L137), so
  `G_A` solves it and `G_C` solves it with right-hand side `1`; `[xⁿ]`-
  extraction (commons `Commons.RingTheory.PowerSeries.ode_78_coeff`, fleet
  L144) gives `(n+1)²g_{n+1} = (7n²+7n+2)gₙ + 8n²g_{n−1}` (whose first
  values `g₀ = 1, g₁ = 2, g₂ = 10, g₃ = 56` match Zagier's sequence A = the
  Franel numbers) for `G_A` at every `n` and for `G_C` at `n ≥ 1`; the
  signed integrals `Kₙ = (−1)ⁿIₙ` satisfy the same recurrence
  (`zetaJ_recurrence`), and `I₀ = ζ(2)`, `I₁ = 4 − 2ζ(2)` (commons
  `Commons.Analysis.Integral.doubleIntegral_zetaJ_one`, fleet L141) match
  the initial values, so two-step induction closes the identity, and its
  consequence `overconvergesCtr_of_aintegral` makes the *transformed*
  difference `[xⁿ]G_C − (ζ(2)/4)·[xⁿ]G_A` overconverge (radius ≥ 1) — the
  ζ-side mirror of `overconvergesB_of_cintegral` of
  `Submission.CDT.L2chi3Cintegral`.

The identity itself is the classical Beukers/Apéry ζ(2) evaluation; its
numerical instances `n = 0,1,2,3` (`ζ(2)·1 = I₀ = ζ(2)`, `2ζ(2) − 4 = −I₁`,
`10ζ(2) − 16 = I₂`, `56ζ(2) − 208/9 = −I₃`) are verified to 30 digits.
-/

namespace Submission.CDT

noncomputable section

open scoped BigOperators

/-- the Möbius map `x ↦ x/(1+x)` as a formal power series -/
def mobPhi : PowerSeries ℚ := PowerSeries.X * ((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹

/-- the paper's `(Gs)` transform `f(x) ↦ (1/(1+x))·f(x/(x+1))` -/
def mobTrans (f : PowerSeries ℚ) : PowerSeries ℚ :=
  ((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹ * f.subst mobPhi

/-- the paper's `G_A(x) = (1/(1+x))·H_A(x/(x+1))` (Zagier's sequence **A**) -/
def GAtr : PowerSeries ℚ := mobTrans HA

/-- the paper's `G_C(x) = (1/(1+x))·H_C(x/(x+1))` -/
def GCtr : PowerSeries ℚ := mobTrans HC

lemma mobPhi_constantCoeff : (mobPhi : PowerSeries ℚ).constantCoeff = 0 := by
  rw [mobPhi, map_mul, PowerSeries.constantCoeff_X, zero_mul]

/-- the constant term of a substituted series is unchanged (the substituting
series `x/(1+x)` has vanishing constant term) -/
lemma subst_mobPhi_constantCoeff (f : PowerSeries ℚ) :
    MvPowerSeries.constantCoeff (f.subst mobPhi) = MvPowerSeries.constantCoeff f := by
  rw [show MvPowerSeries.constantCoeff (f.subst mobPhi)
      = MvPowerSeries.coeff (0 : Unit →₀ ℕ) (f.subst mobPhi) from rfl]
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero' mobPhi_constantCoeff)
    f (0 : Unit →₀ ℕ)]
  rw [finsum_eq_single _ 0]
  · rw [pow_zero]
    have h1 : (MvPowerSeries.coeff (0 : Unit →₀ ℕ)) (1 : PowerSeries ℚ) = 1 := by
      rw [show MvPowerSeries.coeff (0 : Unit →₀ ℕ) (1 : PowerSeries ℚ)
          = MvPowerSeries.constantCoeff (1 : PowerSeries ℚ) from rfl, map_one]
    rw [h1, smul_eq_mul, mul_one, PowerSeries.coeff_zero_eq_constantCoeff]
    exact PowerSeries.constantCoeff_eq f
  · intro d hd
    have h : MvPowerSeries.coeff (0 : Unit →₀ ℕ) ((mobPhi : PowerSeries ℚ) ^ d) = 0 := by
      rw [show MvPowerSeries.coeff (0 : Unit →₀ ℕ) ((mobPhi : PowerSeries ℚ) ^ d)
          = PowerSeries.constantCoeff ((mobPhi : PowerSeries ℚ) ^ d) from rfl]
      rw [map_pow, mobPhi_constantCoeff, zero_pow hd]
    rw [h, smul_zero]

/-- the Möbius transform preserves the constant term -/
lemma mobTrans_coeff_zero (f : PowerSeries ℚ) : (mobTrans f).coeff 0 = f.coeff 0 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_eq,
    PowerSeries.constantCoeff_eq]
  rw [mobTrans, show MvPowerSeries.constantCoeff
        (((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹ * f.subst mobPhi)
      = MvPowerSeries.constantCoeff (((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹)
        * MvPowerSeries.constantCoeff (f.subst mobPhi) from
      map_mul MvPowerSeries.constantCoeff _ _]
  rw [show MvPowerSeries.constantCoeff (((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹)
        = PowerSeries.constantCoeff (((PowerSeries.X : PowerSeries ℚ) + 1)⁻¹) from rfl]
  rw [PowerSeries.constantCoeff_inv]
  have hc : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries ℚ) + 1) = 1 := by
    rw [map_add, PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_one, zero_add]
  rw [hc, inv_one, one_mul, subst_mobPhi_constantCoeff]

lemma GAtr_coeff_zero : GAtr.coeff 0 = 1 := by
  rw [GAtr, mobTrans_coeff_zero, coeff_HA]
  exact HA_coeff_zero

lemma GCtr_coeff_zero : GCtr.coeff 0 = 0 := by
  rw [GCtr, mobTrans_coeff_zero, coeff_HC]
  exact HC_coeff_zero

/-! ## The ζ-side double integral -/

/-- the `(Aintegral)` summand `(1−s²)ⁿ(1−t²)ⁿ/(1−st)^{n+1}` -/
def zetaKernel (n : ℕ) (s t : ℝ) : ℝ :=
  (1 - s ^ 2) ^ n * (1 - t ^ 2) ^ n / (1 - s * t) ^ (n + 1)

/-- the `n`-th `(Aintegral)` double integral
`Iₙ = ∫₀¹∫₀¹ (1−s²)ⁿ(1−t²)ⁿ/(1−st)^{n+1} ds dt` -/
def zetaJ (n : ℕ) : ℝ :=
  ∫ s in (0 : ℝ)..1, ∫ t in (0 : ℝ)..1, zetaKernel n s t

/-- **the paper's kernel inequality**: `(1−s²)(1−t²) ≤ (1−st)²`, i.e.
`|(1−s²)(1−t²)/(1−st)| ≤ 1`, with equality at `s = t = 0` -/
lemma one_sub_sq_mul_le (s t : ℝ) : (1 - s ^ 2) * (1 - t ^ 2) ≤ (1 - s * t) ^ 2 := by
  nlinarith [sq_nonneg (s - t)]

lemma zetaKernel_nonneg (n : ℕ) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) : 0 ≤ zetaKernel n s t := by
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have hst1 : s * t ≤ 1 := by nlinarith
  have h1 : 0 ≤ 1 - s ^ 2 := by linarith
  have h2 : 0 ≤ 1 - t ^ 2 := by linarith
  have h3 : 0 ≤ 1 - s * t := by linarith
  exact div_nonneg (mul_nonneg (pow_nonneg h1 n) (pow_nonneg h2 n)) (pow_nonneg h3 (n + 1))

/-- **the paper's bound**: the `(Aintegral)` kernel is bounded by `1` on the
unit square for `n ≥ 1` -/
lemma zetaKernel_le_one (n : ℕ) (hn : 1 ≤ n) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : zetaKernel n s t ≤ 1 := by
  have hs2 : s ^ 2 ≤ 1 := by nlinarith
  have ht2 : t ^ 2 ≤ 1 := by nlinarith
  have hst0 : 0 ≤ s * t := mul_nonneg hs0 ht0
  have hst1 : s * t ≤ 1 := by nlinarith
  have hP0 : 0 ≤ (1 - s ^ 2) * (1 - t ^ 2) := mul_nonneg (by linarith) (by linarith)
  have hD0 : 0 ≤ 1 - s * t := by linarith
  have hD1 : 1 - s * t ≤ 1 := by linarith
  have hP : (1 - s ^ 2) * (1 - t ^ 2) ≤ (1 - s * t) ^ 2 := one_sub_sq_mul_le s t
  have h1 : ((1 - s ^ 2) * (1 - t ^ 2)) ^ n ≤ (1 - s * t) ^ (n + 1) := by
    calc ((1 - s ^ 2) * (1 - t ^ 2)) ^ n
        ≤ ((1 - s * t) ^ 2) ^ n := pow_le_pow_left₀ hP0 hP n
      _ = (1 - s * t) ^ (2 * n) := by rw [← pow_mul]
      _ ≤ (1 - s * t) ^ (n + 1) := by
          apply pow_le_pow_of_le_one hD0 hD1
          omega
  rw [zetaKernel, ← mul_pow]
  exact div_le_one_of_le₀ h1 (pow_nonneg hD0 (n + 1))

lemma zetaKernel_abs_le_one (n : ℕ) (hn : 1 ≤ n) {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : |zetaKernel n s t| ≤ 1 := by
  rw [abs_of_nonneg (zetaKernel_nonneg n hs0 hs1 ht0 ht1)]
  exact zetaKernel_le_one n hn hs0 hs1 ht0 ht1

lemma inner_zetaJ_abs (n : ℕ) (hn : 1 ≤ n) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |(∫ t in (0 : ℝ)..1, zetaKernel n s t)| ≤ 1 := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := 1) (f := fun t : ℝ => zetaKernel n s t) (by
        intro x hx
        have hx' : x ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hx
        rcases Set.mem_Ioc.mp hx' with ⟨hx0, hx1⟩
        exact zetaKernel_abs_le_one n hn hs0 hs1 (le_of_lt hx0) hx1)
  simpa using hb

/-- the `(Aintegral)` double integrals are bounded by `1` for `n ≥ 1` -/
lemma zetaJ_abs_le_one (n : ℕ) (hn : 1 ≤ n) : |zetaJ n| ≤ 1 := by
  unfold zetaJ
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := 1)
      (f := fun s : ℝ => ∫ t in (0 : ℝ)..1, zetaKernel n s t) (by
        intro s hs
        have hs' : s ∈ Set.Ioc (0 : ℝ) 1 := by
          simpa [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
        rcases Set.mem_Ioc.mp hs' with ⟨hs0, hs1⟩
        exact inner_zetaJ_abs n hn (le_of_lt hs0) hs1)
  simpa using hb

/-- `ζ(2) = Σ'ₙ 1/n² ≥ 1` (the `n = 1` term) -/
lemma one_le_zeta2Real : 1 ≤ zeta2Real := by
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
  have h1 : (1 : ℝ) / ((1 : ℕ) : ℝ) ^ 2 ≤ ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ 2 :=
    hsum.le_tsum 1 (fun b _ => by positivity)
  rw [zeta2Real]
  simpa using h1

/-- `I₀ = ∫₀¹∫₀¹ ds dt/(1−st) = ζ(2)`: the `n = 0` instance of the
`(Aintegral)` integral, from the commons lemma
`doubleIntegral_inv_one_sub_mul`. -/
lemma zetaJ_zero_eq : zetaJ 0 = zeta2Real := by
  have hfun : (fun s : ℝ => ∫ t in (0 : ℝ)..1, zetaKernel 0 s t)
      = (fun s : ℝ => ∫ t in (0 : ℝ)..1, (1 - s * t)⁻¹) := by
    funext s
    apply intervalIntegral.integral_congr
    intro t ht
    simp [zetaKernel]
  rw [zetaJ, hfun, Commons.Analysis.Integral.doubleIntegral_inv_one_sub_mul]
  have hsum : Summable (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2)
  have hsh := hsum.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, Nat.cast_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
    div_zero, zero_add] at hsh
  have hgoal : (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)
      = ∑' n : ℕ, (1 : ℝ) / ((n : ℝ)) ^ 2 := by
    have h' : (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2)
        = ∑' n : ℕ, (fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ 2) (n + 1) := by
      apply tsum_congr
      intro n
      push_cast
      ring
    rw [h']
    exact hsh
  rw [zeta2Real]
  exact hgoal

/-- **the `(Aintegral)` bound**: `|Iₙ| ≤ ζ(2)` for every `n` -/
lemma zetaJ_bound : ∀ n : ℕ, |zetaJ n| ≤ zeta2Real := by
  intro n
  rcases Nat.eq_zero_or_pos n with hn | hn
  · rw [hn, zetaJ_zero_eq, abs_of_nonneg (by linarith [one_le_zeta2Real])]
  · exact le_trans (zetaJ_abs_le_one n hn) one_le_zeta2Real

/-- **the ζ-side recurrence is PROVED**: the classical Beukers/Apéry ζ(2)
recurrence for the `(Aintegral)` double integrals,
`(n+1)²I_{n+1} = −(7n²+7n+2)Iₙ + 8n²I_{n−1}` — the companion case of the
`(7,−8,2)` Zagier recurrence of the paper's `G_A`, from the commons lemma
`Commons.Analysis.Integral.zetaintegral_recurrence_parametric` -/
theorem zetaJ_recurrence : ∀ n : ℕ, 1 ≤ n →
    (((n + 1 : ℕ) : ℝ)) ^ 2 * zetaJ (n + 1)
      = - (7 * ((n : ℕ) : ℝ) ^ 2 + 7 * ((n : ℕ) : ℝ) + 2) * zetaJ n
        + 8 * ((n : ℕ) : ℝ) ^ 2 * zetaJ (n - 1) := by
  intro n hn
  have h := Commons.Analysis.Integral.zetaintegral_recurrence_parametric n hn
  simp only [zetaJ, zetaKernel]
  rw [show n + 1 + 1 = n + 2 from by omega, show n - 1 + 1 = n from by omega]
  exact h

/-! ## The `(Aintegral)` coefficient identity -/

/-- **`(Aintegral)`, coefficient form at a single degree `n`**:
`ζ(2)·[xⁿ]G_A − 4·[xⁿ]G_C = (−1)ⁿ·Iₙ`. -/
def AintegralIdentityAt (n : ℕ) : Prop :=
  zeta2Real * (((GAtr.coeff n : ℚ) : ℝ)) - 4 * (((GCtr.coeff n : ℚ) : ℝ))
    = (-1 : ℝ) ^ n * zetaJ n

/-- **the paper's `(Aintegral)` identity**, coefficientwise -/
def AintegralIdentity : Prop := ∀ n : ℕ, AintegralIdentityAt n

/-- **the `n = 0` instance of `(Aintegral)`**: `ζ(2) = I₀` -/
lemma AintegralIdentityAt_zero : AintegralIdentityAt 0 := by
  unfold AintegralIdentityAt
  rw [GAtr_coeff_zero, GCtr_coeff_zero, zetaJ_zero_eq]
  norm_num

/-- **the ζ-side overconvergence bridge**: the `(Aintegral)` identity plus the
kernel bound make the *Möbius-transformed* difference
`[xⁿ]G_C − (ζ(2)/4)·[xⁿ]G_A` overconverge (radius ≥ 1) — the ζ-side mirror of
`overconvergesB_of_cintegral`. -/
theorem overconvergesCtr_of_aintegral (hId : AintegralIdentity)
    (hBd : ∀ n : ℕ, |zetaJ n| ≤ zeta2Real) :
    OverconvergesUnit (fun n : ℕ =>
      ((GCtr.coeff n : ℚ) : ℝ) - (zeta2Real / 4) * ((GAtr.coeff n : ℚ) : ℝ)) := by
  unfold OverconvergesUnit
  intro r hr0 hr1
  refine ⟨zeta2Real / 4, by linarith [one_le_zeta2Real], ?_⟩
  intro n
  simp only []
  have h1 : ((GCtr.coeff n : ℚ) : ℝ) - (zeta2Real / 4) * ((GAtr.coeff n : ℚ) : ℝ)
      = -((zeta2Real * ((GAtr.coeff n : ℚ) : ℝ)) - 4 * ((GCtr.coeff n : ℚ) : ℝ)) / 4 := by
    ring
  rw [h1, hId n]
  have h2 : |(-1 : ℝ) ^ n * zetaJ n| = |zetaJ n| := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  rw [abs_div, abs_neg, h2, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have hz0 : 0 ≤ zeta2Real := by linarith [one_le_zeta2Real]
  have hb := hBd n
  have hstep1 : |zetaJ n| / 4 ≤ zeta2Real / 4 := div_le_div_of_nonneg_right hb (by norm_num)
  have hstep2 : zeta2Real / 4 ≤ (zeta2Real / 4) / r ^ n := by
    rw [le_div_iff₀ (pow_pos hr0 n)]
    exact mul_le_of_le_one_right (div_nonneg hz0 (by norm_num)) (pow_le_one₀ hr0.le hr1.le)
  exact le_trans hstep1 hstep2

end

end Submission.CDT
