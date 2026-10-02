import Mathlib
import Submission.Work.FatouDeg.Petal.DefsAux
import Submission.Work.FatouDeg.Petal.polyBoundsAux
import Submission.Work.FatouDeg.Petal.petalGeomDefs
import Submission.Work.FatouDeg.Petal.logOneSubRemBound
import Submission.Work.FatouDeg.Petal.logMulOfSector
import Submission.Work.FatouDeg.Petal.invPowOneSubRemBound
import Submission.Work.FatouDeg.Petal.polyTaylor2RemBound
import Submission.Work.FatouDeg.Petal.uQtailAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 1000000

noncomputable section

open scoped Topology
open Polynomial

namespace Work.FatouDeg.Petal

/-- Product bound for norms. -/
private lemma norm_mul_le {a b : ℂ} {A B : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) :
    ‖a * b‖ ≤ A * B := by
  rw [norm_mul]
  exact mul_le_mul ha hb (norm_nonneg b) (le_trans (norm_nonneg a) ha)

/-- Triangle inequality for six terms. -/
private lemma norm_sum6_le (a b c d e f : ℂ) :
    ‖a + b + c + d + e + f‖ ≤ ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ := by
  have h1 := norm_add_le (a + b + c + d + e) f
  have h2 := norm_add_le (a + b + c + d) e
  have h3 := norm_add_le (a + b + c) d
  have h4 := norm_add_le (a + b) c
  have h5 := norm_add_le a b
  linarith only [h1, h2, h3, h4, h5]

/-- **The defect of the approximate coordinate vanishes to order `m`.**

Let `n = m-1` (so `m ≥ 4` gives `n ≥ 3`), `u z = 1 - z * G z`, `x z = z^n * u z`, so that
`Pfun m G z = z * (1 - x z)`.  Assume the two polynomial facts `hcoef`, `hPQ` (proved in
`polyAlgebraAux`): `u * Qpoly m G ≡ 1` modulo `z^(m-1)`, and `n * Ppoly m G - X*(Ppoly m G)' =
Qpoly m G`.

Then for all sufficiently small `ρ` (depending on `m` and on a bound `M` for `G` on the ball of
radius `2ρ`) the defect `Rfun m G z = Afun m G (Pfun m G z) - Afun m G z - 1` of the approximate
Abel coordinate `Afun m G z = (z^(m-1))⁻¹ * (Ppoly m G).eval z + betac m G * Complex.log z`
satisfies `‖Rfun m G z‖ ≤ C * ‖z‖^m` on the working domain `Dom m ρ`. -/
theorem defectBoundAux (m : ℕ) (hm : 3 ≤ m) (G : Polynomial ℂ) (M : ℝ)
    (hcoef : ∀ j : ℕ, j < m - 1 → ((upoly G) * (Qpoly m G)).coeff j = if j = 0 then 1 else 0)
    (hPQ : Polynomial.C (((m - 1 : ℕ) : ℂ)) * (Ppoly m G)
      - Polynomial.X * (Polynomial.derivative (Ppoly m G)) = Qpoly m G) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      (∀ z : ℂ, ‖z‖ ≤ 2 * ρ → ‖G.eval z‖ ≤ M) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Dom m ρ, ‖Rfun m G z‖ ≤ C * ‖z‖ ^ m := by
  have hm2 : 2 ≤ m := by omega
  have hm1 : 1 ≤ m := by omega
  obtain ⟨Cin, hCin0, hCin⟩ := invPowOneSubRemBound (m - 1)
  obtain ⟨Clog, hClog0, hClog⟩ := logOneSubRemBound
  obtain ⟨Cpt, hCpt0, hCpt⟩ := polyTaylor2RemBound (Ppoly m G)
  obtain ⟨B, hB⟩ := uQtailAux m hm2 G hcoef
  obtain ⟨⟨KŘ, hKŘ0, hKŘb⟩, -⟩ := polyBoundsAux m hm2 G
  obtain ⟨KP, hKP0, hKP⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℂ, ‖w‖ ≤ 1 → ‖(Ppoly m G).eval w‖ ≤ K :=
    ⟨_, Finset.sum_nonneg fun i _ => norm_nonneg _, fun w hw => norm_eval_le_sum_coeff _ w hw⟩
  obtain ⟨KPd, hKPd0, hKPd⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℂ, ‖w‖ ≤ 1 →
      ‖(Polynomial.derivative (Ppoly m G)).eval w‖ ≤ K :=
    ⟨_, Finset.sum_nonneg fun i _ => norm_nonneg _, fun w hw => norm_eval_le_sum_coeff _ w hw⟩
  obtain ⟨KPdd, hKPdd0, hKPdd⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℂ, ‖w‖ ≤ 1 →
      ‖(Polynomial.derivative (Polynomial.derivative (Ppoly m G))).eval w‖ ≤ K :=
    ⟨_, Finset.sum_nonneg fun i _ => norm_nonneg _, fun w hw => norm_eval_le_sum_coeff _ w hw⟩
  obtain ⟨KB, hKB0, hKB⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ w : ℂ, ‖w‖ ≤ 1 → ‖B.eval w‖ ≤ K :=
    ⟨_, Finset.sum_nonneg fun i _ => norm_nonneg _, fun w hw => norm_eval_le_sum_coeff _ w hw⟩
  refine ⟨1 / (32 * (1 + max M 0)), by positivity, ?_⟩
  intro ρ hρ hρle hG
  set M' : ℝ := max M 0 with hM'def
  have hM'0 : 0 ≤ M' := le_max_right M 0
  have hG' : ∀ z : ℂ, ‖z‖ ≤ 2 * ρ → ‖G.eval z‖ ≤ M' :=
    fun z hz => le_trans (hG z hz) (le_max_left M 0)
  have hρ32 : ρ ≤ 1 / 32 := by
    calc ρ ≤ 1 / (32 * (1 + M')) := hρle
      _ ≤ 1 / 32 := one_div_le_one_div_of_le (by norm_num) (by linarith only [hM'0])
  have hr1 : 2 * ρ ≤ 1 := by linarith only [hρ32]
  have hrq : 2 * ρ ≤ 1 / 4 := by linarith only [hρ32]
  have hρkey : 2 * ρ * (1 + M') ≤ 1 / 16 := by
    have h2 : ρ * (32 * (1 + M')) ≤ 1 :=
      (le_div_iff₀ (by linarith only [hM'0] : (0 : ℝ) < 32 * (1 + M'))).mp hρle
    linarith only [h2]
  set n : ℕ := m - 1 with hn
  have hnm : n + 1 = m := by omega
  have hnm1 : m - 1 = n := by omega
  have hn1 : 1 ≤ n := by omega
  have hn3 : 2 ≤ n := by omega
  set Ac : ℂ := ((n : ℂ) * ((n : ℂ) + 1)) / 2 with hAcdef
  set β : ℂ := betac m G with hβdef
  set cc : ℂ := ((upoly G) * (Qpoly m G)).coeff (m - 1) with hccdef
  have hβc : β = cc + (m : ℂ) / 2 := by rw [hβdef, hccdef]; rfl
  set U : ℝ := 1 + 2 * ρ * M' with hUdef
  have hU1 : 1 ≤ U := by rw [hUdef]; linarith only [hM'0, hρ.le, mul_nonneg hρ.le hM'0]
  have hU0 : 0 ≤ U := by linarith only [hU1]
  -- the constant
  set KH1 : ℝ := ‖β‖ * M' + U ^ 2 * ((2 * ρ) * KPdd / 2 + (n : ℝ) * KPd)
      + M' * (U + 1) * ‖Ac‖ * KP + ‖Ac‖ * KŘ with hKH1def
  set X2 : ℝ := U ^ 3 * ((n : ℝ) * (2 * ρ) ^ 2 * KPdd / 2 + ‖Ac‖ * (2 * ρ) * KPd)
      + ‖β‖ * U ^ 2 / 2 with hX2def
  set X3 : ℝ := U ^ 4 * (‖Ac‖ * (2 * ρ) ^ 2 * KPdd / 2) with hX3def
  set X4 : ℝ := U ^ 3 * (Cin * KP + (1 + (n : ℝ) / 2 + ‖Ac‖ / 4) * Cpt * (2 * ρ) ^ 3) with hX4def
  set X5 : ℝ := ‖β‖ * Clog * U ^ 3 with hX5def
  set KH2 : ℝ := (2 * ρ) ^ (n - 1) * X2 with hKH2def
  set KH3 : ℝ := (2 * ρ) ^ (2 * n - 1) * X3 with hKH3def
  set Kres : ℝ := (2 * ρ) ^ (n - 1) * X4 with hKresdef
  set Ksig : ℝ := (2 * ρ) ^ (2 * n - 1) * X5 with hKsigdef
  have hKH10 : 0 ≤ KH1 := by rw [hKH1def]; positivity
  have hX20 : 0 ≤ X2 := by rw [hX2def]; positivity
  have hX30 : 0 ≤ X3 := by rw [hX3def]; positivity
  have hX40 : 0 ≤ X4 := by rw [hX4def]; positivity
  have hX50 : 0 ≤ X5 := by rw [hX5def]; positivity
  have hKH20 : 0 ≤ KH2 := by rw [hKH2def]; positivity
  have hKH30 : 0 ≤ KH3 := by rw [hKH3def]; positivity
  have hKres0 : 0 ≤ Kres := by rw [hKresdef]; positivity
  have hKsig0 : 0 ≤ Ksig := by rw [hKsigdef]; positivity
  refine ⟨KB + KH1 + KH2 + KH3 + Kres + Ksig, by linarith only [hKB0, hKH10, hKH20, hKH30, hKres0, hKsig0], ?_⟩
  intro z hz
  obtain ⟨hznorm, hzsect⟩ := (mem_Dom (m := m) (ρ := ρ)).mp hz
  have hzre : 0 < z.re := lt_of_le_of_lt (mul_nonneg (by positivity) (abs_nonneg z.im)) hzsect
  have hz0 : z ≠ 0 := by intro h; rw [h] at hzre; simp at hzre
  have hzle1 : ‖z‖ ≤ 1 := by linarith only [hznorm, hrq]
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hznn : 0 ≤ ‖z‖ := norm_nonneg z
  -- the atoms
  set w : ℂ := z ^ n with hwdef
  have hw0 : w ≠ 0 := by rw [hwdef]; exact pow_ne_zero _ hz0
  set Gz : ℂ := G.eval z with hGzdef
  have hGzb : ‖Gz‖ ≤ M' := by rw [hGzdef]; exact hG' z hznorm.le
  set uz : ℂ := (upoly G).eval z with huzdef
  have huz_val : uz = 1 - z * Gz := by
    rw [huzdef, upoly, hGzdef]; simp
  have huzb : ‖uz‖ ≤ U := by
    rw [hUdef, huz_val]
    have h1 : ‖(1 : ℂ) - z * Gz‖ ≤ 1 + ‖z * Gz‖ := by
      simpa using norm_sub_le (1 : ℂ) (z * Gz)
    rw [norm_mul] at h1
    have h2 : ‖z‖ * ‖Gz‖ ≤ 2 * ρ * M' := by
      calc ‖z‖ * ‖Gz‖ ≤ (2 * ρ) * M' :=
            mul_le_mul hznorm.le hGzb (norm_nonneg _) (by linarith only [hρ.le])
        _ = 2 * ρ * M' := by ring
    linarith only [h1, h2]
  set Qz : ℂ := (Qpoly m G).eval z with hQzdef
  set Pz : ℂ := (Ppoly m G).eval z with hPzdef
  set Pd : ℂ := (Polynomial.derivative (Ppoly m G)).eval z with hPddef
  set Pdd : ℂ := (Polynomial.derivative (Polynomial.derivative (Ppoly m G))).eval z with hPdddef
  have hPzb : ‖Pz‖ ≤ KP := by rw [hPzdef]; exact hKP z hzle1
  have hPdb : ‖Pd‖ ≤ KPd := by rw [hPddef]; exact hKPd z hzle1
  have hPddb : ‖Pdd‖ ≤ KPdd := by rw [hPdddef]; exact hKPdd z hzle1
  have hcn : (((m - 1 : ℕ) : ℂ)) = (n : ℂ) := by rw [hnm1]
  have hcnz : z ^ (m - 1) = z ^ n := by rw [hnm1]
  have hQzeq : Qz = (n : ℂ) * Pz - z * Pd := by
    have h := congrArg (fun p : Polynomial ℂ => p.eval z) hPQ
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] at h
    rw [← hPzdef, ← hPddef, ← hQzdef, hcn] at h
    exact h.symm
  set P0 : ℂ := (Ppoly m G).coeff 0 with hP0def
  have hP0val : P0 = 1 / (n : ℂ) := by
    have h := coeff_zero_Ppoly m hm2 G
    rw [hcn] at h
    rw [hP0def]; exact h
  have hP0b : ‖P0‖ ≤ KP := by
    have h := hKP 0 (by norm_num : ‖(0 : ℂ)‖ ≤ 1)
    simpa only [hP0def, Polynomial.coeff_zero_eq_eval_zero] using h
  set Ř : ℂ := (Pz - P0) / z with hŘdef
  have hPŘ : Pz = P0 + z * Ř := by rw [hŘdef]; field_simp; ring
  have hŘb : ‖Ř‖ ≤ KŘ := by
    have h1 : ‖Pz - P0‖ ≤ KŘ * ‖z‖ := by
      have h := hKŘb z hzle1
      rw [hcn] at h
      rw [← hPzdef, ← hP0val] at h
      exact h
    have h2 : ‖Pz - P0‖ = ‖z‖ * ‖Ř‖ := by
      rw [hPŘ, add_sub_cancel_left, norm_mul]
    rw [h2] at h1
    nlinarith only [h1, hzpos, norm_nonneg Ř, hKŘ0]
  have hAcP0 : Ac * P0 = (m : ℂ) / 2 := by
    have hcast : ((n : ℂ) + 1) = (m : ℂ) := by rw [← hnm]; push_cast; ring
    have hn0 : (n : ℂ) ≠ 0 := by
      simpa using (Nat.cast_ne_zero (R := ℂ)).mpr (by omega : n ≠ 0)
    rw [hAcdef, hP0val, hcast]
    field_simp
  set x : ℂ := w * uz with hxdef
  have hxb : ‖x‖ ≤ 1 / 2 := by
    rw [hxdef, hwdef, norm_mul, norm_pow]
    have h1 : ‖z‖ ^ n ≤ 2 * ρ := by
      have h2 : ‖z‖ ^ n ≤ (2 * ρ) ^ n := pow_le_pow_left₀ hznn hznorm.le n
      have h3 : (2 * ρ) ^ n ≤ (2 * ρ) ^ 1 :=
        pow_le_pow_of_le_one (by linarith only [hρ.le]) hr1 (by omega)
      simpa using le_trans h2 h3
    have h3 : ‖z‖ ^ n * ‖uz‖ ≤ (2 * ρ) * U :=
      mul_le_mul h1 huzb (norm_nonneg _) (by linarith only [hρ.le])
    have hUM : U ≤ 1 + M' := by rw [hUdef]; nlinarith only [hr1, hM'0]
    have h4 : (2 * ρ) * U ≤ 1 / 2 := by nlinarith only [hUM, hρkey, hρ.le]
    linarith only [h3, h4]
  set yv : ℂ := (1 - x) ^ n with hyvdef
  set logdy : ℂ := Complex.log (1 - x) with hlogdydef
  set δ : ℂ := yv⁻¹ - (1 + (n : ℂ) * x + Ac * x ^ 2) with hδdef
  have hδb : ‖δ‖ ≤ Cin * ‖x‖ ^ 3 := by
    rw [hδdef, hAcdef]; exact hCin x hxb
  set σ : ℂ := logdy + x + x ^ 2 / 2 with hσdef
  have hσb : ‖σ‖ ≤ Clog * ‖x‖ ^ 3 := by
    rw [hσdef, hlogdydef]; exact hClog x hxb
  set Pzy : ℂ := (Ppoly m G).eval (z * (1 - x)) with hPzydef
  set Pt : ℂ := Pz - x * z * Pd + (x * z) ^ 2 / 2 * Pdd with hPtdef
  have hεb : ‖Pzy - Pt‖ ≤ Cpt * ‖x‖ ^ 3 * ‖z‖ ^ 3 := by
    rw [hPzydef, hPtdef, hPzdef, hPddef, hPdddef]
    exact hCpt z x hzle1 hxb
  have hPzyb : ‖Pzy‖ ≤ KP := by
    rw [hPzydef]
    apply hKP
    rw [norm_mul]
    have h1 : ‖1 - x‖ ≤ 1 + ‖x‖ := by simpa using norm_sub_le (1 : ℂ) x
    have h1' : ‖1 - x‖ ≤ 1 + 1 / 2 := by linarith only [h1, hxb]
    have h2 : ‖z‖ * ‖1 - x‖ ≤ (2 * ρ) * (1 + 1 / 2) :=
      mul_le_mul hznorm.le h1' (norm_nonneg _) (by linarith only [hρ.le])
    linarith only [h2, hrq]
  -- the polynomial identities from the hypotheses
  have hBzval : z ^ m * B.eval z = uz * Qz - 1 - cc * z ^ n := by
    have h := congrArg (fun p : Polynomial ℂ => p.eval z) hB
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_one, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] at h
    rw [← huzdef, ← hQzdef, hcnz] at h
    exact h.symm
  set Bz : ℂ := B.eval z with hBzdef
  have hBzb : ‖Bz‖ ≤ KB := by rw [hBzdef]; exact hKB z hzle1
  have hBzval' : z ^ m * Bz = uz * Qz - 1 - cc * z ^ n := by
    rw [hBzdef]; exact hBzval
  -- the truncation atoms
  set H2 : ℂ := z ^ 2 * Pdd / 2 - (n : ℂ) * z * Pd + Ac * Pz with hH2def
  set H2' : ℂ := (n : ℂ) * z ^ 2 * Pdd / 2 - Ac * z * Pd with hH2'def
  set H2'' : ℂ := Ac * z ^ 2 * Pdd / 2 with hH2''def
  set H1 : ℂ := β * Gz + uz ^ 2 * (z * Pdd / 2 - (n : ℂ) * Pd) - Gz * (uz + 1) * Ac * Pz
      + Ac * Ř with hH1def
  set T2 : ℂ := uz ^ 3 * H2' - β * uz ^ 2 / 2 with hT2def
  set T3 : ℂ := uz ^ 4 * H2'' with hT3def
  set T5 : ℂ := δ * Pzy + (1 + (n : ℂ) * x + Ac * x ^ 2) * (Pzy - Pt) with hT5def
  -- the relation `uz^2 * H2 - β * uz + cc = z * H1`
  have hα : uz ^ 2 * H2 - β * uz + cc = z * H1 := by
    rw [hH2def, hH1def, huz_val, hβc, hPŘ]
    linear_combination hAcP0
  -- the reduction of `Rfun` to the truncated expression
  have hpf : Pfun m G z = z * (1 - x) := by
    rw [Pfun_eq_mul_one_sub_pgx m hm1 G z]
    simp only [pgx]
    have h1 : z ^ (m - 1) = w := by rw [hcnz, hwdef]
    have h2 : (1 - z * G.eval z) = uz := by rw [huz_val, hGzdef]
    rw [h1, h2, ← hxdef]
  have hlogdy : Complex.log (Pfun m G z) = Complex.log z + logdy := by
    rw [hpf, hlogdydef]
    exact logMulOfSector hzre hxb
  have hRfun : Rfun m G z = w⁻¹ * (yv⁻¹ * Pzy - Pz) + β * logdy - 1 := by
    have h1 : (Pfun m G z ^ n)⁻¹ = w⁻¹ * yv⁻¹ := by
      rw [hpf, mul_pow, mul_inv, ← hwdef, ← hyvdef]
    have h2 : (Ppoly m G).eval (Pfun m G z) = Pzy := by rw [hpf, hPzydef]
    have h3 : (z ^ n)⁻¹ = w⁻¹ := by rw [hwdef]
    have hcnp : Pfun m G z ^ (m - 1) = Pfun m G z ^ n := by rw [hnm1]
    simp only [Rfun, Afun, hβdef, hcnp, h1, h2, hcnz, h3, hlogdy, ← hPzdef]
    ring_nf
  have hRfunmul : w * Rfun m G z = (yv⁻¹ * Pzy - Pz) + β * w * logdy - w := by
    rw [hRfun]; field_simp
  -- the truncated version
  have hAexp : (1 + (n : ℂ) * x + Ac * x ^ 2) * (Pz - x * z * Pd + (x * z) ^ 2 / 2 * Pdd) - Pz
      = x * Qz + x ^ 2 * H2 + x ^ 3 * H2' + x ^ 4 * H2'' := by
    rw [hQzeq, hH2def, hH2'def, hH2''def]
    ring
  have hKEY : (1 + (n : ℂ) * x + Ac * x ^ 2) * (Pz - x * z * Pd + (x * z) ^ 2 / 2 * Pdd) - Pz
        - β * w * x - β * w * x ^ 2 / 2 - w
      = w * (z ^ m * Bz) + w ^ 2 * z * H1 + w ^ 3 * (uz ^ 3 * H2' - β * uz ^ 2 / 2)
        + w ^ 4 * (uz ^ 4 * H2'') := by
    rw [hAexp]
    have hcoll : x * Qz + x ^ 2 * H2 + x ^ 3 * H2' + x ^ 4 * H2'' - β * w * x - β * w * x ^ 2 / 2 - w
        = w * uz * Qz - w - cc * w ^ 2 + w ^ 2 * (uz ^ 2 * H2 - β * uz + cc)
          + w ^ 3 * (uz ^ 3 * H2' - β * uz ^ 2 / 2) + w ^ 4 * (uz ^ 4 * H2'') := by
      rw [hxdef]; ring
    rw [hcoll]
    have hstep : w * uz * Qz - w - cc * w ^ 2 + w ^ 2 * (uz ^ 2 * H2 - β * uz + cc)
          + w ^ 3 * (uz ^ 3 * H2' - β * uz ^ 2 / 2) + w ^ 4 * (uz ^ 4 * H2'')
        = w * (z ^ m * Bz) + w ^ 2 * z * H1 + w ^ 3 * (uz ^ 3 * H2' - β * uz ^ 2 / 2)
          + w ^ 4 * (uz ^ 4 * H2'') := by
      have e1 : w * (z ^ m * Bz) = w * uz * Qz - w - cc * w ^ 2 := by
        rw [hBzval']; ring
      have e2 : w ^ 2 * z * H1 = w ^ 2 * (uz ^ 2 * H2 - β * uz + cc) := by
        rw [show w ^ 2 * z * H1 = w ^ 2 * (z * H1) from by ring, ← hα]
      rw [e1, e2]
    rw [hstep]
  have hsplit : w * Rfun m G z = (1 + (n : ℂ) * x + Ac * x ^ 2) * Pt - Pz - β * w * x
        - β * w * x ^ 2 / 2 - w + T5 + β * w * σ := by
    rw [hRfunmul, hT5def, hδdef, hσdef]
    ring
  have hmul : w * Rfun m G z
      = w * (z ^ m * Bz + (w * z) * H1 + w ^ 2 * (uz ^ 3 * H2' - β * uz ^ 2 / 2)
            + w ^ 3 * (uz ^ 4 * H2'')) + (T5 + β * w * σ) := by
    rw [hsplit, hPtdef, hKEY]
    ring
  have hRfundec : Rfun m G z = z ^ m * Bz + (w * z) * H1 + w ^ 2 * (uz ^ 3 * H2' - β * uz ^ 2 / 2)
      + w ^ 3 * (uz ^ 4 * H2'') + w⁻¹ * T5 + β * σ := by
    calc Rfun m G z = w⁻¹ * (w * Rfun m G z) := by
          rw [← mul_assoc, inv_mul_cancel₀ hw0, one_mul]
      _ = w⁻¹ * (w * (z ^ m * Bz + (w * z) * H1 + w ^ 2 * (uz ^ 3 * H2' - β * uz ^ 2 / 2)
              + w ^ 3 * (uz ^ 4 * H2'')) + (T5 + β * w * σ)) := by rw [hmul]
      _ = z ^ m * Bz + (w * z) * H1 + w ^ 2 * (uz ^ 3 * H2' - β * uz ^ 2 / 2)
            + w ^ 3 * (uz ^ 4 * H2'') + w⁻¹ * T5 + β * σ := by
          field_simp; ring
  -- bounds for the individual factors
  have hU3 : (1 : ℝ) ≤ U ^ 3 := one_le_pow₀ hU1
  have hH2'b : ‖H2'‖ ≤ (n : ℝ) * (2 * ρ) ^ 2 * KPdd / 2 + ‖Ac‖ * (2 * ρ) * KPd := by
    rw [hH2'def]
    have heq1 : ‖(n : ℂ) * z ^ 2 * Pdd / 2‖ = (n : ℝ) * ‖z‖ ^ 2 * ‖Pdd‖ / 2 := by
      rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_natCast]; norm_num
    have heq2 : ‖Ac * z * Pd‖ = ‖Ac‖ * (‖z‖ * ‖Pd‖) := by
      rw [norm_mul, norm_mul]; ring
    have e1 : ‖(n : ℂ) * z ^ 2 * Pdd / 2‖ ≤ (n : ℝ) * (2 * ρ) ^ 2 * KPdd / 2 := by
      rw [heq1]
      have h1 : ‖z‖ ^ 2 ≤ (2 * ρ) ^ 2 := pow_le_pow_left₀ hznn hznorm.le 2
      have h2 : ‖z‖ ^ 2 * ‖Pdd‖ ≤ (2 * ρ) ^ 2 * KPdd :=
        mul_le_mul h1 hPddb (norm_nonneg _) (by positivity)
      have h3 : (n : ℝ) * (‖z‖ ^ 2 * ‖Pdd‖) ≤ (n : ℝ) * ((2 * ρ) ^ 2 * KPdd) :=
        mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg n)
      linarith only [h3]
    have e2 : ‖Ac * z * Pd‖ ≤ ‖Ac‖ * (2 * ρ) * KPd := by
      rw [heq2]
      have h1 : ‖z‖ * ‖Pd‖ ≤ (2 * ρ) * KPd :=
        mul_le_mul hznorm.le hPdb (norm_nonneg _) (by linarith only [hρ.le])
      have h2 : ‖Ac‖ * (‖z‖ * ‖Pd‖) ≤ ‖Ac‖ * ((2 * ρ) * KPd) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      linarith only [h2]
    exact le_trans (norm_sub_le _ _) (add_le_add e1 e2)
  have hT2b : ‖T2‖ ≤ X2 := by
    rw [hT2def, hX2def]
    have huz3 : ‖uz ^ 3‖ ≤ U ^ 3 := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg uz) huzb 3
    have hb1 : ‖uz ^ 3 * H2'‖ ≤ U ^ 3 * ((n : ℝ) * (2 * ρ) ^ 2 * KPdd / 2 + ‖Ac‖ * (2 * ρ) * KPd) :=
      norm_mul_le huz3 hH2'b
    have heq : ‖β * uz ^ 2 / 2‖ = ‖β‖ * ‖uz‖ ^ 2 / 2 := by
      rw [norm_div, norm_mul, norm_pow]; norm_num
    have hb2 : ‖β * uz ^ 2 / 2‖ ≤ ‖β‖ * U ^ 2 / 2 := by
      rw [heq]
      have h1 : ‖uz‖ ^ 2 ≤ U ^ 2 := pow_le_pow_left₀ (norm_nonneg uz) huzb 2
      have h2 : ‖β‖ * ‖uz‖ ^ 2 ≤ ‖β‖ * U ^ 2 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      linarith only [h2]
    exact le_trans (norm_sub_le _ _) (add_le_add hb1 hb2)
  have hH2''b : ‖H2''‖ ≤ ‖Ac‖ * (2 * ρ) ^ 2 * KPdd / 2 := by
    rw [hH2''def]
    have heq : ‖Ac * z ^ 2 * Pdd / 2‖ = ‖Ac‖ * ‖z‖ ^ 2 * ‖Pdd‖ / 2 := by
      rw [norm_div, norm_mul, norm_mul, norm_pow]; norm_num
    rw [heq]
    have h1 : ‖z‖ ^ 2 ≤ (2 * ρ) ^ 2 := pow_le_pow_left₀ hznn hznorm.le 2
    have h2 : ‖z‖ ^ 2 * ‖Pdd‖ ≤ (2 * ρ) ^ 2 * KPdd :=
      mul_le_mul h1 hPddb (norm_nonneg _) (by positivity)
    have h3 : ‖Ac‖ * (‖z‖ ^ 2 * ‖Pdd‖) ≤ ‖Ac‖ * ((2 * ρ) ^ 2 * KPdd) :=
      mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    linarith only [h3]
  have hT3b : ‖T3‖ ≤ X3 := by
    rw [hT3def, hX3def]
    have huz4 : ‖uz ^ 4‖ ≤ U ^ 4 := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg uz) huzb 4
    exact norm_mul_le huz4 hH2''b
  have hH1b : ‖H1‖ ≤ KH1 := by
    rw [hKH1def, hH1def]
    have b1 : ‖β * Gz‖ ≤ ‖β‖ * M' := norm_mul_le le_rfl hGzb
    have b2 : ‖uz ^ 2 * (z * Pdd / 2 - (n : ℂ) * Pd)‖ ≤ U ^ 2 * ((2 * ρ) * KPdd / 2 + (n : ℝ) * KPd) := by
      have hinner : ‖z * Pdd / 2 - (n : ℂ) * Pd‖ ≤ (2 * ρ) * KPdd / 2 + (n : ℝ) * KPd := by
        have heq1 : ‖z * Pdd / 2‖ = ‖z‖ * ‖Pdd‖ / 2 := by
          rw [norm_div, norm_mul]; norm_num
        have heq2 : ‖(n : ℂ) * Pd‖ = (n : ℝ) * ‖Pd‖ := by
          rw [norm_mul, Complex.norm_natCast]
        have e1 : ‖z * Pdd / 2‖ ≤ (2 * ρ) * KPdd / 2 := by
          rw [heq1]
          have h1 : ‖z‖ * ‖Pdd‖ ≤ (2 * ρ) * KPdd :=
            mul_le_mul hznorm.le hPddb (norm_nonneg _) (by linarith only [hρ.le])
          linarith only [h1]
        have e2 : ‖(n : ℂ) * Pd‖ ≤ (n : ℝ) * KPd := by
          rw [heq2]; exact mul_le_mul_of_nonneg_left hPdb (Nat.cast_nonneg n)
        exact le_trans (norm_sub_le _ _) (add_le_add e1 e2)
      have huz2 : ‖uz ^ 2‖ ≤ U ^ 2 := by rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg uz) huzb 2
      exact norm_mul_le huz2 hinner
    have b3 : ‖Gz * (uz + 1) * Ac * Pz‖ ≤ M' * (U + 1) * ‖Ac‖ * KP := by
      have huz1 : ‖uz + 1‖ ≤ U + 1 := le_trans (by simpa using norm_add_le uz 1) (by linarith only [huzb])
      have h1 : ‖Gz * (uz + 1) * Ac * Pz‖ = ‖Gz‖ * ‖uz + 1‖ * ‖Ac‖ * ‖Pz‖ := by
        rw [norm_mul, norm_mul, norm_mul]
      rw [h1]
      have h3 : ‖Gz‖ * ‖uz + 1‖ ≤ M' * (U + 1) :=
        mul_le_mul hGzb huz1 (norm_nonneg _) (by linarith only [hM'0])
      have hMU : 0 ≤ M' * (U + 1) := by positivity
      have h4 : ‖Gz‖ * ‖uz + 1‖ * ‖Ac‖ ≤ M' * (U + 1) * ‖Ac‖ :=
        mul_le_mul h3 le_rfl (norm_nonneg _) hMU
      have hMU' : 0 ≤ M' * (U + 1) * ‖Ac‖ := by positivity
      exact mul_le_mul h4 hPzb (norm_nonneg _) hMU'
    have b4 : ‖Ac * Ř‖ ≤ ‖Ac‖ * KŘ := norm_mul_le le_rfl hŘb
    have b5 : ‖β * Gz + uz ^ 2 * (z * Pdd / 2 - (n : ℂ) * Pd) - Gz * (uz + 1) * Ac * Pz + Ac * Ř‖
        ≤ ‖β * Gz‖ + ‖uz ^ 2 * (z * Pdd / 2 - (n : ℂ) * Pd)‖ + ‖Gz * (uz + 1) * Ac * Pz‖ + ‖Ac * Ř‖ := by
      have h1 := norm_add_le (β * Gz + uz ^ 2 * (z * Pdd / 2 - (n : ℂ) * Pd) - Gz * (uz + 1) * Ac * Pz) (Ac * Ř)
      have h2 := norm_sub_le (β * Gz + uz ^ 2 * (z * Pdd / 2 - (n : ℂ) * Pd)) (Gz * (uz + 1) * Ac * Pz)
      have h3 := norm_add_le (β * Gz) (uz ^ 2 * (z * Pdd / 2 - (n : ℂ) * Pd))
      linarith only [h1, h2, h3]
    exact le_trans b5 (by linarith only [b1, b2, b3, b4])
  -- the T5 bound
  have hxpow : ‖x‖ ^ 3 ≤ ‖z‖ ^ (3 * n) * U ^ 3 := by
    have h1 : ‖x‖ ≤ ‖z‖ ^ n * U := by
      rw [hxdef, hwdef, norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left huzb (by positivity)
    calc ‖x‖ ^ 3 ≤ (‖z‖ ^ n * U) ^ 3 := pow_le_pow_left₀ (norm_nonneg x) h1 3
      _ = ‖z‖ ^ (3 * n) * U ^ 3 := by
          have h3 : (‖z‖ ^ n) ^ 3 = ‖z‖ ^ (3 * n) := by
            rw [← pow_mul, show n * 3 = 3 * n by omega]
          rw [mul_pow, h3]
  have hT5b : ‖T5‖ ≤ ‖x‖ ^ 3 * (Cin * KP + (1 + (n : ℝ) / 2 + ‖Ac‖ / 4) * Cpt * ‖z‖ ^ 3) := by
    rw [hT5def]
    have e1 : ‖δ * Pzy‖ ≤ ‖x‖ ^ 3 * (Cin * KP) := by
      have h := norm_mul_le hδb hPzyb
      calc ‖δ * Pzy‖ ≤ (Cin * ‖x‖ ^ 3) * KP := h
        _ = ‖x‖ ^ 3 * (Cin * KP) := by ring
    have e2 : ‖(1 + (n : ℂ) * x + Ac * x ^ 2)‖ ≤ 1 + (n : ℝ) / 2 + ‖Ac‖ / 4 := by
      have h1 : ‖(n : ℂ) * x‖ ≤ (n : ℝ) / 2 := by
        rw [norm_mul, Complex.norm_natCast]
        have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith only [hnn, hxb]
      have h2 : ‖Ac * x ^ 2‖ ≤ ‖Ac‖ / 4 := by
        rw [norm_mul, norm_pow]
        have h3 : ‖x‖ ^ 2 ≤ 1 / 4 := by nlinarith only [norm_nonneg x, hxb]
        nlinarith only [norm_nonneg Ac, h3]
      have t1 := norm_add_le (1 + (n : ℂ) * x) (Ac * x ^ 2)
      have t2 := norm_add_le (1 : ℂ) ((n : ℂ) * x)
      simp only [norm_one] at t2
      linarith only [t1, t2, h1, h2]
    have e3 : ‖(1 + (n : ℂ) * x + Ac * x ^ 2) * (Pzy - Pt)‖
        ≤ (1 + (n : ℝ) / 2 + ‖Ac‖ / 4) * (Cpt * ‖x‖ ^ 3 * ‖z‖ ^ 3) :=
      norm_mul_le e2 hεb
    have e4 : ‖δ * Pzy + (1 + (n : ℂ) * x + Ac * x ^ 2) * (Pzy - Pt)‖
        ≤ ‖δ * Pzy‖ + ‖(1 + (n : ℂ) * x + Ac * x ^ 2) * (Pzy - Pt)‖ := norm_add_le _ _
    have e5 : ‖δ * Pzy‖ + ‖(1 + (n : ℂ) * x + Ac * x ^ 2) * (Pzy - Pt)‖
        ≤ ‖x‖ ^ 3 * (Cin * KP + (1 + (n : ℝ) / 2 + ‖Ac‖ / 4) * Cpt * ‖z‖ ^ 3) := by
      have h : ‖x‖ ^ 3 * (Cin * KP) + (1 + (n : ℝ) / 2 + ‖Ac‖ / 4) * (Cpt * ‖x‖ ^ 3 * ‖z‖ ^ 3)
          = ‖x‖ ^ 3 * (Cin * KP + (1 + (n : ℝ) / 2 + ‖Ac‖ / 4) * Cpt * ‖z‖ ^ 3) := by ring
      linarith only [e1, e3]
    linarith only [e4, e5]
  have hRfundecT5 : Rfun m G z = z ^ m * Bz + (w * z) * H1 + w ^ 2 * T2 + w ^ 3 * T3 + w⁻¹ * T5
      + β * σ := by
    rw [hRfundec, hT2def, hT3def]
  -- the bounds for the six terms
  have hterm1 : ‖z ^ m * Bz‖ ≤ ‖z‖ ^ m * KB := by
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_left hBzb (by positivity)
  have hterm2 : ‖(w * z) * H1‖ ≤ ‖z‖ ^ m * KH1 := by
    rw [norm_mul, norm_mul, hwdef, norm_pow]
    rw [show ‖z‖ ^ n * ‖z‖ = ‖z‖ ^ m from by rw [← pow_succ, hnm]]
    exact mul_le_mul_of_nonneg_left hH1b (by positivity)
  have hterm3 : ‖w ^ 2 * T2‖ ≤ ‖z‖ ^ m * KH2 := by
    rw [hKH2def]
    have hw2 : ‖w ^ 2‖ = ‖z‖ ^ (2 * n) := by
      rw [hwdef, norm_pow, norm_pow, ← pow_mul, show n * 2 = 2 * n by omega]
    calc ‖w ^ 2 * T2‖ = ‖z‖ ^ (2 * n) * ‖T2‖ := by rw [norm_mul, hw2]
      _ ≤ ‖z‖ ^ (2 * n) * X2 := mul_le_mul_of_nonneg_left hT2b (by positivity)
      _ = ‖z‖ ^ m * (‖z‖ ^ (n - 1) * X2) := by
          rw [show 2 * n = m + (n - 1) by omega, pow_add]; ring
      _ ≤ ‖z‖ ^ m * ((2 * ρ) ^ (n - 1) * X2) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hznn hznorm.le (n - 1)) hX20)
            (by positivity)
  have hterm4 : ‖w ^ 3 * T3‖ ≤ ‖z‖ ^ m * KH3 := by
    rw [hKH3def]
    have hw3 : ‖w ^ 3‖ = ‖z‖ ^ (3 * n) := by
      rw [hwdef, norm_pow, norm_pow, ← pow_mul, show n * 3 = 3 * n by omega]
    calc ‖w ^ 3 * T3‖ = ‖z‖ ^ (3 * n) * ‖T3‖ := by rw [norm_mul, hw3]
      _ ≤ ‖z‖ ^ (3 * n) * X3 := mul_le_mul_of_nonneg_left hT3b (by positivity)
      _ = ‖z‖ ^ m * (‖z‖ ^ (2 * n - 1) * X3) := by
          rw [show 3 * n = m + (2 * n - 1) by omega, pow_add]; ring
      _ ≤ ‖z‖ ^ m * ((2 * ρ) ^ (2 * n - 1) * X3) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hznn hznorm.le (2 * n - 1)) hX30)
            (by positivity)
  have hterm5 : ‖w⁻¹ * T5‖ ≤ ‖z‖ ^ m * Kres := by
    rw [hKresdef]
    have hw1 : ‖w⁻¹‖ = (‖z‖⁻¹) ^ n := by rw [hwdef, norm_inv, norm_pow, inv_pow]
    have hcans : (‖z‖⁻¹) ^ n * ‖z‖ ^ (3 * n) = ‖z‖ ^ (2 * n) := by
      have hpow : ‖z‖ ^ (3 * n) = ‖z‖ ^ n * ‖z‖ ^ (2 * n) := by
        rw [← pow_add]; congr 1; omega
      rw [inv_pow, hpow, ← mul_assoc,
        inv_mul_cancel₀ (pow_ne_zero n (norm_ne_zero_iff.mpr hz0)), one_mul]
    have hstep : ‖w⁻¹ * T5‖ ≤ ‖z‖ ^ (2 * n) * X4 := by
      calc ‖w⁻¹ * T5‖ = (‖z‖⁻¹) ^ n * ‖T5‖ := by rw [norm_mul, hw1]
        _ ≤ (‖z‖⁻¹) ^ n * (‖x‖ ^ 3 * (Cin * KP + (1 + (n : ℝ) / 2 + ‖Ac‖ / 4) * Cpt * ‖z‖ ^ 3)) :=
            mul_le_mul_of_nonneg_left hT5b (by positivity)
        _ ≤ (‖z‖⁻¹) ^ n * ((‖z‖ ^ (3 * n) * U ^ 3) *
              (Cin * KP + (1 + (n : ℝ) / 2 + ‖Ac‖ / 4) * Cpt * ‖z‖ ^ 3)) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right hxpow (by positivity)
        _ = ‖z‖ ^ (2 * n) * (U ^ 3 * (Cin * KP + (1 + (n : ℝ) / 2 + ‖Ac‖ / 4) * Cpt * ‖z‖ ^ 3)) := by
            have hstep2 : (‖z‖⁻¹) ^ n * (‖z‖ ^ (3 * n) * U ^ 3)
                * (Cin * KP + (1 + (n : ℝ) / 2 + ‖Ac‖ / 4) * Cpt * ‖z‖ ^ 3)
                = ‖z‖ ^ (2 * n) * (U ^ 3 * (Cin * KP + (1 + (n : ℝ) / 2 + ‖Ac‖ / 4) * Cpt * ‖z‖ ^ 3)) := by
              rw [← mul_assoc, hcans]
              ring
            calc (‖z‖⁻¹) ^ n * ((‖z‖ ^ (3 * n) * U ^ 3) *
                  (Cin * KP + (1 + (n : ℝ) / 2 + ‖Ac‖ / 4) * Cpt * ‖z‖ ^ 3))
                = (‖z‖⁻¹) ^ n * (‖z‖ ^ (3 * n) * U ^ 3)
                  * (Cin * KP + (1 + (n : ℝ) / 2 + ‖Ac‖ / 4) * Cpt * ‖z‖ ^ 3) := by ring
              _ = ‖z‖ ^ (2 * n) * (U ^ 3 * (Cin * KP + (1 + (n : ℝ) / 2 + ‖Ac‖ / 4) * Cpt * ‖z‖ ^ 3)) :=
                  hstep2
        _ ≤ ‖z‖ ^ (2 * n) * X4 := by
            rw [hX4def]
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            have h1 : ‖z‖ ^ 3 ≤ (2 * ρ) ^ 3 := pow_le_pow_left₀ hznn hznorm.le 3
            have h2 : (1 + (n : ℝ) / 2 + ‖Ac‖ / 4) * Cpt * ‖z‖ ^ 3
                ≤ (1 + (n : ℝ) / 2 + ‖Ac‖ / 4) * Cpt * (2 * ρ) ^ 3 :=
              mul_le_mul_of_nonneg_left h1 (by positivity)
            linarith only [h2]
    calc ‖w⁻¹ * T5‖ ≤ ‖z‖ ^ (2 * n) * X4 := hstep
      _ = ‖z‖ ^ m * (‖z‖ ^ (n - 1) * X4) := by
          rw [show 2 * n = m + (n - 1) by omega, pow_add]; ring
      _ ≤ ‖z‖ ^ m * ((2 * ρ) ^ (n - 1) * X4) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hznn hznorm.le (n - 1)) hX40)
            (by positivity)
  have hterm6 : ‖β * σ‖ ≤ ‖z‖ ^ m * Ksig := by
    rw [hKsigdef, hX5def]
    have hbs : ‖β * σ‖ ≤ ‖β‖ * (Clog * ‖x‖ ^ 3) := norm_mul_le le_rfl hσb
    calc ‖β * σ‖ ≤ ‖β‖ * (Clog * (‖z‖ ^ (3 * n) * U ^ 3)) := by
          refine le_trans hbs ?_
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg β)
          exact mul_le_mul_of_nonneg_left hxpow hClog0
      _ = ‖z‖ ^ m * (‖z‖ ^ (2 * n - 1) * (‖β‖ * Clog * U ^ 3)) := by
          rw [show 3 * n = m + (2 * n - 1) by omega, pow_add]; ring
      _ ≤ ‖z‖ ^ m * ((2 * ρ) ^ (2 * n - 1) * (‖β‖ * Clog * U ^ 3)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hznn hznorm.le (2 * n - 1))
              (by positivity))
            (by positivity)
  -- conclusion
  calc ‖Rfun m G z‖
      = ‖z ^ m * Bz + (w * z) * H1 + w ^ 2 * T2 + w ^ 3 * T3 + w⁻¹ * T5 + β * σ‖ := by
        rw [hRfundecT5]
    _ ≤ ‖z ^ m * Bz‖ + ‖(w * z) * H1‖ + ‖w ^ 2 * T2‖ + ‖w ^ 3 * T3‖ + ‖w⁻¹ * T5‖ + ‖β * σ‖ :=
        norm_sum6_le _ _ _ _ _ _
    _ ≤ ‖z‖ ^ m * KB + ‖z‖ ^ m * KH1 + ‖z‖ ^ m * KH2 + ‖z‖ ^ m * KH3 + ‖z‖ ^ m * Kres
          + ‖z‖ ^ m * Ksig :=
        add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hterm1 hterm2) hterm3) hterm4) hterm5) hterm6
    _ = (KB + KH1 + KH2 + KH3 + Kres + Ksig) * ‖z‖ ^ m := by ring

end Work.FatouDeg.Petal
