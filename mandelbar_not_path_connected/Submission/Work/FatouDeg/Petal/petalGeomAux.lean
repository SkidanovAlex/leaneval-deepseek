import Mathlib
import Submission.Work.FatouDeg.Petal.DefsAux
import Submission.Work.FatouDeg.Petal.petalGeomDefs
import Submission.Work.FatouDeg.Petal.petalArgBound
import Submission.Work.FatouDeg.Petal.petalTrigBoundMin
import Submission.Work.FatouDeg.Petal.petalNormBound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open scoped Topology
open Set Filter Metric

namespace Work.FatouDeg.Petal

/-! ## Elementary rewritings of `pgSfun` at the powers of `z` -/

theorem pgSfun_eq_sin (c : ℝ) (hc : 0 < c) {z : ℂ} (hz : z ≠ 0) :
    pgSfun c z = Real.sqrt (1 + c ^ 2) * ‖z‖ * Real.sin (pgTheta c - z.arg) := by
  rw [pgSfun_arg c hz, pgCosSub c z.arg hc]
  ring

theorem pgSfun_pow_eq_sin (c : ℝ) (hc : 0 < c) (m : ℕ) {z : ℂ} (hz : z ≠ 0) :
    pgSfun c (z ^ m) = Real.sqrt (1 + c ^ 2) * ‖z‖ ^ m * Real.sin (pgTheta c - m * z.arg) := by
  rw [pgSfun_pow c m hz, pgCosSub c (m * z.arg) hc]
  ring

theorem pgSfun_neg_eq_sin (c : ℝ) (hc : 0 < c) {z : ℂ} (hz : z ≠ 0) :
    pgSfun (-c) z = Real.sqrt (1 + c ^ 2) * ‖z‖ * Real.sin (pgTheta c + z.arg) := by
  have h : Real.cos z.arg - (-c) * Real.sin z.arg = Real.cos z.arg + c * Real.sin z.arg := by
    ring
  rw [pgSfun_arg (-c) hz, h, pgCosAdd c z.arg hc]
  ring

theorem pgSfun_neg_pow_eq_sin (c : ℝ) (hc : 0 < c) (m : ℕ) {z : ℂ} (hz : z ≠ 0) :
    pgSfun (-c) (z ^ m) = Real.sqrt (1 + c ^ 2) * ‖z‖ ^ m * Real.sin (pgTheta c + m * z.arg) := by
  have h : Real.cos (m * z.arg) - (-c) * Real.sin (m * z.arg)
      = Real.cos (m * z.arg) + c * Real.sin (m * z.arg) := by ring
  rw [pgSfun_pow (-c) m hz, h, pgCosAdd c (m * z.arg) hc]
  ring

theorem pgSfun_Pfun_decomp (m : ℕ) (G : Polynomial ℂ) (c : ℝ) (z : ℂ) :
    pgSfun c (Pfun m G z) = pgSfun c z - pgSfun c (z ^ m) + pgSfun c (z ^ (m + 1) * G.eval z) := by
  simp only [Pfun, pgSfun_add, pgSfun_sub]

/-! ## The half-angle conditions for the two sectors -/

theorem pgTheta_cDom_lt (m : ℕ) (hm : 3 ≤ m) :
    ((m : ℝ) + 1) * pgTheta (7 * (m : ℝ) / 8) < Real.pi / 2 := by
  have hmpos : (0 : ℝ) < m := by positivity
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have h1c : 1 / (7 * (m : ℝ) / 8) = 8 / (7 * (m : ℝ)) := by rw [one_div_div]
  have hpos : (0 : ℝ) < 8 / (7 * (m : ℝ)) := by positivity
  rw [pgTheta, h1c]
  have hle : Real.arctan (8 / (7 * (m : ℝ))) ≤ 8 / (7 * (m : ℝ)) := Real.arctan_le_self hpos.le
  have hbound : 8 * ((m : ℝ) + 1) / (7 * (m : ℝ)) < Real.pi / 2 := by
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 7 * (m : ℝ))]
    nlinarith [Real.pi_gt_d20, hmpos, hm3]
  calc ((m : ℝ) + 1) * Real.arctan (8 / (7 * (m : ℝ)))
      ≤ ((m : ℝ) + 1) * (8 / (7 * (m : ℝ))) :=
        mul_le_mul_of_nonneg_left hle (by linarith : (0 : ℝ) ≤ (m : ℝ) + 1)
    _ = 8 * ((m : ℝ) + 1) / (7 * (m : ℝ)) := by ring
    _ < Real.pi / 2 := hbound

theorem pgTheta_m_lt (m : ℕ) (hm : 3 ≤ m) :
    ((m : ℝ) + 1) * pgTheta (m : ℝ) < Real.pi / 2 := by
  have hmpos : (0 : ℝ) < m := by positivity
  have hm3 : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hpos : (0 : ℝ) < 1 / (m : ℝ) := by positivity
  have hle : Real.arctan (1 / (m : ℝ)) ≤ 1 / (m : ℝ) := Real.arctan_le_self hpos.le
  have hbound : ((m : ℝ) + 1) * (1 / (m : ℝ)) < Real.pi / 2 := by
    rw [mul_one_div, div_lt_iff₀ hmpos]
    nlinarith [Real.pi_gt_three, hmpos, hm3]
  calc ((m : ℝ) + 1) * Real.arctan (1 / (m : ℝ))
      ≤ ((m : ℝ) + 1) * (1 / (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hle (by linarith : (0 : ℝ) ≤ (m : ℝ) + 1)
    _ < Real.pi / 2 := hbound

/-! ## The one-step sector preservation -/

theorem pgSectorStep (m : ℕ) (hm : 3 ≤ m) (G : Polynomial ℂ) (c : ℝ) (hc : 0 < c)
    (hπ : ((m : ℝ) + 1) * pgTheta c < Real.pi / 2) (M : ℝ) (hM : 0 ≤ M) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      (∀ w : ℂ, ‖w‖ ≤ 2 * ρ → ‖G.eval w‖ ≤ M) →
      ∀ z : ℂ, ‖z‖ < 2 * ρ → pgSfun c z > 0 → pgSfun (-c) z > 0 →
        pgSfun c (Pfun m G z) > 0 ∧ pgSfun (-c) (Pfun m G z) > 0 := by
  have hm1 : (1 : ℕ) ≤ m := by omega
  have hmR : (0 : ℝ) < m := by positivity
  have hm3R : (3 : ℝ) ≤ m := by exact_mod_cast hm
  have hθ1pos : 0 < pgTheta c := Real.arctan_pos.mpr (by positivity)
  set θ1 := pgTheta c with hθ1
  set s := Real.sin (((m : ℝ) - 1) * θ1 / m) with hs
  set S := Real.sin (((m : ℝ) + 1) * θ1) with hS
  have hθ1π : θ1 < Real.pi / 2 := by rw [hθ1]; exact Real.arctan_lt_pi_div_two _
  have hθ1pi : θ1 < Real.pi := by linarith [Real.pi_pos]
  have hspos : 0 < s := by
    rw [hs]
    have hm1pos : (0 : ℝ) < (m : ℝ) - 1 := by linarith [hm3R]
    refine Real.sin_pos_of_pos_of_lt_pi ?_ ?_
    · exact div_pos (mul_pos hm1pos hθ1pos) hmR
    · have hle : ((m : ℝ) - 1) * θ1 / m ≤ θ1 := by
        rw [div_le_iff₀ hmR]; nlinarith [hθ1pos]
      linarith
  have hSpos : 0 < S := by
    rw [hS]
    exact Real.sin_pos_of_pos_of_lt_pi (by nlinarith [hθ1pos])
      (by linarith [hπ, Real.pi_pos])
  set K := max M S with hK
  have hKpos : 0 < K := lt_of_lt_of_le hSpos (le_max_right M S)
  refine ⟨min (1 / 2) (s / (12 * K)), lt_min (by norm_num) (by positivity), ?_⟩
  intro ρ hρ hρle hG z hr hsz hsmz
  have hsec : c * |z.im| < z.re := by
    have h1 : c * z.im < z.re := by have := hsz; rw [pgSfun] at this; linarith
    have h2 : -(c * z.im) < z.re := by have := hsmz; rw [pgSfun_neg] at this; linarith
    rcases le_or_gt 0 z.im with h | h
    · rw [abs_of_nonneg h]; exact h1
    · rw [abs_of_neg h]; linarith
  have hzre : 0 < z.re := lt_of_le_of_lt (mul_nonneg hc.le (abs_nonneg _)) hsec
  have hz : z ≠ 0 := by intro h; rw [h] at hzre; simp at hzre
  have hθabs : |z.arg| < θ1 := by rw [hθ1]; exact petalArgBound c hc hzre hsec
  have hρ1 : ρ ≤ 1 / 2 := le_trans hρle (min_le_left _ _)
  have hρK : ρ * K ≤ s / 12 := by
    have h2 : ρ ≤ s / (12 * K) := le_trans hρle (min_le_right _ _)
    calc ρ * K ≤ (s / (12 * K)) * K := mul_le_mul_of_nonneg_right h2 hKpos.le
      _ = s / 12 := by field_simp
  have hr1 : ‖z‖ < 1 := by linarith
  have hrK : ‖z‖ * K ≤ s / 6 := by
    calc ‖z‖ * K ≤ (2 * ρ) * K := le_of_lt (by nlinarith [hr, hKpos])
      _ = 2 * (ρ * K) := by ring
      _ ≤ 2 * (s / 12) := by linarith [hρK]
      _ = s / 6 := by ring
  have hrM : ‖z‖ * M ≤ s / 6 :=
    le_trans (mul_le_mul_of_nonneg_left (le_max_left M S) (norm_nonneg z)) hrK
  have hrS : ‖z‖ * S ≤ s / 6 :=
    le_trans (mul_le_mul_of_nonneg_left (le_max_right M S) (norm_nonneg z)) hrK
  have hrpos : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hε0 : 0 ≤ ‖z‖ ^ (m - 1) := by positivity
  have hε1 : ‖z‖ ^ (m - 1) ≤ 1 := pow_le_one₀ (norm_nonneg z) hr1.le
  have hrpow : ‖z‖ ^ (m - 1) ≤ ‖z‖ := by
    have hmm : 1 ≤ m - 1 := by omega
    calc ‖z‖ ^ (m - 1) ≤ ‖z‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg z) hr1.le hmm
      _ = ‖z‖ := pow_one _
  have hSz : ‖z‖ ^ (m - 1) * S ≤ s / 6 :=
    le_trans (mul_le_mul_of_nonneg_right hrpow hSpos.le) hrS
  have hMz : ‖z‖ ^ m * M ≤ s / 6 := by
    have hmm : ‖z‖ ^ m ≤ ‖z‖ ^ 1 := pow_le_pow_of_le_one (norm_nonneg z) hr1.le hm1
    calc ‖z‖ ^ m * M ≤ ‖z‖ ^ 1 * M := mul_le_mul_of_nonneg_right hmm hM
      _ = ‖z‖ * M := by ring
      _ ≤ s / 6 := hrM
  have hpm : ‖z‖ ^ m = ‖z‖ * ‖z‖ ^ (m - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hm1]
  have hp1 : ‖z‖ ^ (m + 1) = ‖z‖ ^ m * ‖z‖ := pow_succ _ _
  have hminpos : 0 < ‖z‖ * min ((‖z‖ ^ (m - 1)) * s) (s - (‖z‖ ^ (m - 1)) * S)
      - ‖z‖ ^ (m + 1) * M := by
    rcases le_total ((‖z‖ ^ (m - 1)) * s) (s - (‖z‖ ^ (m - 1)) * S) with hle | hle
    · rw [min_eq_left hle]
      have heq : ‖z‖ * (‖z‖ ^ (m - 1) * s) - ‖z‖ ^ (m + 1) * M
          = ‖z‖ ^ m * (s - ‖z‖ * M) := by rw [hp1, hpm]; ring
      rw [heq]
      exact mul_pos (pow_pos hrpos m) (by linarith [hrM])
    · rw [min_eq_right hle]
      have heq : ‖z‖ * (s - ‖z‖ ^ (m - 1) * S) - ‖z‖ ^ (m + 1) * M
          = ‖z‖ * (s - ‖z‖ ^ (m - 1) * S - ‖z‖ ^ m * M) := by rw [hp1]; ring
      rw [heq]
      exact mul_pos hrpos (by linarith [hSz, hMz])
  have hsqrt : 0 < Real.sqrt (1 + c ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hx : ∀ d : ℝ, d ^ 2 = c ^ 2 →
      -(Real.sqrt (1 + c ^ 2) * (‖z‖ ^ (m + 1) * M)) ≤ pgSfun d (z ^ (m + 1) * G.eval z) := by
    intro d hd
    have h1 : |pgSfun d (z ^ (m + 1) * G.eval z)|
        ≤ Real.sqrt (1 + c ^ 2) * (‖z‖ ^ (m + 1) * M) := by
      calc |pgSfun d (z ^ (m + 1) * G.eval z)|
          ≤ Real.sqrt (1 + d ^ 2) * ‖z ^ (m + 1) * G.eval z‖ := pgSfun_abs_le d _
        _ = Real.sqrt (1 + c ^ 2) * ‖z ^ (m + 1) * G.eval z‖ := by rw [hd]
        _ = Real.sqrt (1 + c ^ 2) * (‖z‖ ^ (m + 1) * ‖G.eval z‖) := by rw [norm_mul, norm_pow]
        _ ≤ Real.sqrt (1 + c ^ 2) * (‖z‖ ^ (m + 1) * M) := by
            apply mul_le_mul_of_nonneg_left _ hsqrt.le
            exact mul_le_mul_of_nonneg_left (hG z (le_of_lt hr)) (by positivity)
    linarith [neg_abs_le (pgSfun d (z ^ (m + 1) * G.eval z)), h1]
  -- trigonometric bounds
  have huc0 : 0 ≤ θ1 - z.arg := by linarith [le_abs_self z.arg, hθabs]
  have huc1 : θ1 - z.arg ≤ 2 * θ1 := by linarith [neg_le_abs z.arg, hθabs]
  have hum0 : 0 ≤ θ1 + z.arg := by linarith [neg_le_abs z.arg, hθabs]
  have hum1 : θ1 + z.arg ≤ 2 * θ1 := by linarith [le_abs_self z.arg, hθabs]
  have hA : min ((‖z‖ ^ (m - 1)) * s) (s - (‖z‖ ^ (m - 1)) * S)
      ≤ Real.sin (θ1 - z.arg) - (‖z‖ ^ (m - 1)) * Real.sin (θ1 - (m : ℝ) * z.arg) := by
    have h := petalTrigBoundMin m hm θ1 (‖z‖ ^ (m - 1)) (θ1 - z.arg) hθ1pos hπ hε0 hε1 huc0 huc1
    have harg : (m : ℝ) * (θ1 - z.arg) - ((m : ℝ) - 1) * θ1 = θ1 - (m : ℝ) * z.arg := by ring
    rw [harg] at h
    exact h
  have hB : min ((‖z‖ ^ (m - 1)) * s) (s - (‖z‖ ^ (m - 1)) * S)
      ≤ Real.sin (θ1 + z.arg) - (‖z‖ ^ (m - 1)) * Real.sin (θ1 + (m : ℝ) * z.arg) := by
    have h := petalTrigBoundMin m hm θ1 (‖z‖ ^ (m - 1)) (θ1 + z.arg) hθ1pos hπ hε0 hε1 hum0 hum1
    have harg : (m : ℝ) * (θ1 + z.arg) - ((m : ℝ) - 1) * θ1 = θ1 + (m : ℝ) * z.arg := by ring
    rw [harg] at h
    exact h
  -- decompositions
  have hdec_c : pgSfun c (Pfun m G z)
      = Real.sqrt (1 + c ^ 2) * (‖z‖ * (Real.sin (θ1 - z.arg)
            - ‖z‖ ^ (m - 1) * Real.sin (θ1 - (m : ℝ) * z.arg)))
          + pgSfun c (z ^ (m + 1) * G.eval z) := by
    have e1 : pgSfun c z = Real.sqrt (1 + c ^ 2) * ‖z‖ * Real.sin (θ1 - z.arg) :=
      pgSfun_eq_sin c hc hz
    have e2 : pgSfun c (z ^ m)
        = Real.sqrt (1 + c ^ 2) * ‖z‖ ^ m * Real.sin (θ1 - (m : ℝ) * z.arg) :=
      pgSfun_pow_eq_sin c hc m hz
    rw [pgSfun_Pfun_decomp, e1, e2, hpm]
    ring
  have hdec_mc : pgSfun (-c) (Pfun m G z)
      = Real.sqrt (1 + c ^ 2) * (‖z‖ * (Real.sin (θ1 + z.arg)
            - ‖z‖ ^ (m - 1) * Real.sin (θ1 + (m : ℝ) * z.arg)))
          + pgSfun (-c) (z ^ (m + 1) * G.eval z) := by
    have e1 : pgSfun (-c) z = Real.sqrt (1 + c ^ 2) * ‖z‖ * Real.sin (θ1 + z.arg) :=
      pgSfun_neg_eq_sin c hc hz
    have e2 : pgSfun (-c) (z ^ m)
        = Real.sqrt (1 + c ^ 2) * ‖z‖ ^ m * Real.sin (θ1 + (m : ℝ) * z.arg) :=
      pgSfun_neg_pow_eq_sin c hc m hz
    rw [pgSfun_Pfun_decomp, e1, e2, hpm]
    ring
  have hleE : Real.sqrt (1 + c ^ 2) * (‖z‖ * min ((‖z‖ ^ (m - 1)) * s) (s - (‖z‖ ^ (m - 1)) * S))
      ≤ Real.sqrt (1 + c ^ 2) * (‖z‖ * (Real.sin (θ1 - z.arg)
          - ‖z‖ ^ (m - 1) * Real.sin (θ1 - (m : ℝ) * z.arg))) := by
    apply mul_le_mul_of_nonneg_left _ hsqrt.le
    exact mul_le_mul_of_nonneg_left hA (norm_nonneg z)
  have hleF : Real.sqrt (1 + c ^ 2) * (‖z‖ * min ((‖z‖ ^ (m - 1)) * s) (s - (‖z‖ ^ (m - 1)) * S))
      ≤ Real.sqrt (1 + c ^ 2) * (‖z‖ * (Real.sin (θ1 + z.arg)
          - ‖z‖ ^ (m - 1) * Real.sin (θ1 + (m : ℝ) * z.arg))) := by
    apply mul_le_mul_of_nonneg_left _ hsqrt.le
    exact mul_le_mul_of_nonneg_left hB (norm_nonneg z)
  have hC : ∀ d e : ℝ,
      -(Real.sqrt (1 + c ^ 2) * (‖z‖ ^ (m + 1) * M)) ≤ d →
      Real.sqrt (1 + c ^ 2) * (‖z‖ * min ((‖z‖ ^ (m - 1)) * s) (s - (‖z‖ ^ (m - 1)) * S)) ≤ e →
      0 < e + d := by
    intro d e hd he
    have h := mul_pos hsqrt hminpos
    nlinarith [h, hd, he]
  constructor
  · rw [hdec_c]
    exact hC _ _ (hx c (by ring)) hleE
  · rw [hdec_mc]
    exact hC _ _ (hx (-c) (by ring)) hleF

/-! ## A cosine lower bound on the sector -/

theorem pgCos_ge (m : ℕ) (hm : 3 ≤ m) (c : ℝ) (hc : 0 < c)
    (hπ : ((m : ℝ) + 1) * pgTheta c < Real.pi / 2) {z : ℂ} (hzre : 0 < z.re)
    (hz : c * |z.im| < z.re) :
    Real.cos (((m : ℝ) - 1) * z.arg) ≥ Real.cos (((m : ℝ) + 1) * pgTheta c) := by
  have harg : |z.arg| < pgTheta c := petalArgBound c hc hzre hz
  have hθc : 0 < pgTheta c := Real.arctan_pos.mpr (by positivity)
  have hm1nn : (0 : ℝ) ≤ (m : ℝ) - 1 := by
    have : (3 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have h2 : Real.cos (((m : ℝ) - 1) * z.arg) = Real.cos (((m : ℝ) - 1) * |z.arg|) := by
    rw [← Real.cos_abs (((m : ℝ) - 1) * z.arg), abs_mul, abs_of_nonneg hm1nn]
  rw [h2]
  apply Real.cos_le_cos_of_nonneg_of_le_pi
  · positivity
  · linarith [hπ, Real.pi_pos]
  · nlinarith [harg, hm1nn, hθc]

/-! ## The main theorem -/

theorem petalGeomAux (m : ℕ) (hm : 3 ≤ m) (G : Polynomial ℂ) (M : ℝ) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ →
      (∀ z : ℂ, ‖z‖ ≤ 2 * ρ → ‖G.eval z‖ ≤ M) →
      Set.MapsTo (Pfun m G) (Dom m ρ) (Dom m ρ) ∧
      Set.MapsTo (Pfun m G) (Pet m ρ) (Pet m ρ) ∧
      (∀ z ∈ Dom m ρ, ‖Pfun m G z‖ ≤ ‖z‖) ∧
      ∃ c : ℝ, 0 < c ∧ ∀ z ∈ Dom m ρ,
        (‖z‖ ^ (m - 1))⁻¹ + c ≤ (‖Pfun m G z‖ ^ (m - 1))⁻¹ := by
  by_cases hM : 0 ≤ M
  · have hm1 : (1 : ℕ) ≤ m := by omega
    have hm3R : (3 : ℝ) ≤ m := by exact_mod_cast hm
    have hcDom : (0 : ℝ) < 7 * (m : ℝ) / 8 := by positivity
    have hcPet : (0 : ℝ) < (m : ℝ) := by positivity
    have hπDom := pgTheta_cDom_lt m hm
    have hπPet := pgTheta_m_lt m hm
    obtain ⟨ρS1, hρS1pos, hρS1⟩ := pgSectorStep m hm G (7 * (m : ℝ) / 8) hcDom hπDom M hM
    obtain ⟨ρS2, hρS2pos, hρS2⟩ := pgSectorStep m hm G (m : ℝ) hcPet hπPet M hM
    set cm := Real.cos (((m : ℝ) + 1) * pgTheta (7 * (m : ℝ) / 8)) with hcm
    have hcmpos : 0 < cm := by
      rw [hcm]
      apply Real.cos_pos_of_mem_Ioo
      have hθp : 0 < pgTheta (7 * (m : ℝ) / 8) := Real.arctan_pos.mpr (by positivity)
      exact ⟨by nlinarith, by linarith [hπDom]⟩
    obtain ⟨ρN, hρNpos, hρN⟩ := petalNormBound m hm G M hM cm hcmpos
    refine ⟨min ρN (min ρS1 ρS2), lt_min hρNpos (lt_min hρS1pos hρS2pos), ?_⟩
    intro ρ hρ hρle hG
    have hρN' : ρ ≤ ρN := le_trans hρle (min_le_left _ _)
    have hρS1' : ρ ≤ ρS1 := le_trans hρle (le_trans (min_le_right _ _) (min_le_left _ _))
    have hρS2' : ρ ≤ ρS2 := le_trans hρle (le_trans (min_le_right _ _) (min_le_right _ _))
    have hsecDom : ∀ {z : ℂ}, z ∈ Dom m ρ → (7 * (m : ℝ) / 8) * |z.im| < z.re :=
      fun {z} hz => (mem_Dom.mp hz).2
    have hrDom : ∀ {z : ℂ}, z ∈ Dom m ρ → ‖z‖ < 2 * ρ := fun {z} hz => (mem_Dom.mp hz).1
    have hzreDom : ∀ {z : ℂ}, z ∈ Dom m ρ → 0 < z.re := fun {z} hz =>
      lt_of_le_of_lt (mul_nonneg (by positivity) (abs_nonneg _)) (hsecDom hz)
    have hzneDom : ∀ {z : ℂ}, z ∈ Dom m ρ → z ≠ 0 := by
      intro z hz h
      have := hzreDom hz
      rw [h] at this
      simp at this
    have hpgDom : ∀ {z : ℂ}, z ∈ Dom m ρ →
        pgSfun (7 * (m : ℝ) / 8) z > 0 ∧ pgSfun (-(7 * (m : ℝ) / 8)) z > 0 := by
      intro z hz
      have hs := hsecDom hz
      have h1 : (7 * (m : ℝ) / 8) * z.im < z.re :=
        lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_abs_self z.im) hcDom.le) hs
      have h2 : -((7 * (m : ℝ) / 8) * z.im) < z.re := by
        have := mul_le_mul_of_nonneg_left (neg_le_abs z.im) hcDom.le
        linarith [hs, this]
      constructor
      · rw [pgSfun]; linarith
      · rw [pgSfun_neg]; linarith
    have hcosDom : ∀ {z : ℂ}, z ∈ Dom m ρ → Real.cos (((m : ℝ) - 1) * z.arg) ≥ cm := by
      intro z hz
      rw [hcm]
      exact pgCos_ge m hm (7 * (m : ℝ) / 8) hcDom hπDom (hzreDom hz) (hsecDom hz)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro z hz
      rw [mem_Dom] at hz ⊢
      obtain ⟨hzr, hzs⟩ := hz
      have hzD : z ∈ Dom m ρ := mem_Dom.mpr ⟨hzr, hzs⟩
      obtain ⟨hp1, hp2⟩ := hpgDom hzD
      obtain ⟨hsec1, hsec2⟩ := hρS1 ρ hρ hρS1' hG z hzr hp1 hp2
      obtain ⟨hν1, hν2⟩ := hρN ρ hρ hρN' hG z (hzneDom hzD) hzr (hcosDom hzD)
      refine ⟨lt_of_le_of_lt hν1 hzr, ?_⟩
      have h4 : (7 * (m : ℝ) / 8) * (Pfun m G z).im < (Pfun m G z).re := by
        have := hsec1; rw [pgSfun] at this; linarith
      have h5 : -((7 * (m : ℝ) / 8) * (Pfun m G z).im) < (Pfun m G z).re := by
        have := hsec2; rw [pgSfun_neg] at this; linarith
      rcases le_or_gt 0 (Pfun m G z).im with h | h
      · rw [abs_of_nonneg h]; exact h4
      · rw [abs_of_neg h]; linarith
    · intro z hz
      rw [mem_Pet] at hz ⊢
      obtain ⟨hzr, hzs⟩ := hz
      have hzD : z ∈ Dom m ρ := Pet_subset_Dom m (by omega) ρ (mem_Pet.mpr ⟨hzr, hzs⟩)
      have hpgP : pgSfun (m : ℝ) z > 0 ∧ pgSfun (-(m : ℝ)) z > 0 := by
        have h1 : (m : ℝ) * z.im < z.re :=
          lt_of_le_of_lt (mul_le_mul_of_nonneg_left (le_abs_self z.im) hcPet.le) hzs
        have h2 : -((m : ℝ) * z.im) < z.re := by
          have := mul_le_mul_of_nonneg_left (neg_le_abs z.im) hcPet.le
          linarith [hzs, this]
        constructor
        · rw [pgSfun]; linarith
        · rw [pgSfun_neg]; linarith
      have hrPet : ‖z‖ < 2 * ρ := lt_of_lt_of_le hzr (by linarith)
      obtain ⟨hp1, hp2⟩ := hρS2 ρ hρ hρS2' hG z hrPet hpgP.1 hpgP.2
      have hν := (hρN ρ hρ hρN' hG z (hzneDom hzD) hrPet (hcosDom hzD)).1
      refine ⟨lt_of_le_of_lt hν hzr, ?_⟩
      have h4 : (m : ℝ) * (Pfun m G z).im < (Pfun m G z).re := by
        have := hp1; rw [pgSfun] at this; linarith
      have h5 : -((m : ℝ) * (Pfun m G z).im) < (Pfun m G z).re := by
        have := hp2; rw [pgSfun_neg] at this; linarith
      rcases le_or_gt 0 (Pfun m G z).im with h | h
      · rw [abs_of_nonneg h]; exact h4
      · rw [abs_of_neg h]; linarith
    · intro z hz
      exact (hρN ρ hρ hρN' hG z (hzneDom hz) (hrDom hz) (hcosDom hz)).1
    · refine ⟨(((m : ℝ) - 1) * cm / 2), ?_, ?_⟩
      · have : (0 : ℝ) < (m : ℝ) - 1 := by linarith [hm3R]
        positivity
      · intro z hz
        exact (hρN ρ hρ hρN' hG z (hzneDom hz) (hrDom hz) (hcosDom hz)).2
  · refine ⟨1, one_pos, ?_⟩
    intro ρ hρ hρle hG
    exfalso
    have h0 : ‖(0 : ℂ)‖ ≤ 2 * ρ := by rw [norm_zero]; linarith
    have h1 := hG 0 h0
    have h2 := norm_nonneg (G.eval 0)
    linarith [not_le.mp hM]

end Work.FatouDeg.Petal
