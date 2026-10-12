import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseGateFS.TauTilde
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseGateFS.TauRows` — the τ̃-rows of the gate

The four elementary rows of the smoothed symbol `tauTilde` (`BOSE_BOXFOCK_LEAD.md`
§2.2) together with the `P_H^q` domination they feed:

* `tauTilde_le_sq` — `τ̃ k ≤ ‖k‖²` (from `φ ≤ (r-1)₊²`);
* `tauTilde_ge_kink` — `(1-ε_T)(r - (sℓ)⁻¹)₊² + ε_T(r - (dsℓ)⁻¹)₊² ≤ τ̃ k`
  (from `φ ≥ (r-2)₊²`), the input of the `P_H^q` domination `arith_tauTilde_ge`;
* `tauTilde_deficit` — `‖k‖² - τ̃ k ≤ 4‖k‖/(dsℓ)` (the two previous rows, `d ≤ 1`);
* `A_ge_of_taurad` — the pair `(A_ge, ABq)` on `P_H^q` at `KzEnvAt E ρ` from any
  τ-domination `‖k‖²/2 + 3ρK₀a ≤ τ k` (the repointing of
  `Work.BoseK15.A_ge_and_AB_of_taurad` without the `K15Input` package).
-/

noncomputable section

open scoped BigOperators Pointwise

namespace Work.BoseGateFS

open Work.BoseB7

/-! ## 0. One-variable arithmetic -/

/-- `max 0 (x/c) = max 0 x / c` for `c > 0`. -/
lemma max_zero_div (c x : ℝ) (hc : 0 < c) : max 0 (x / c) = max 0 x / c := by
  by_cases h : x ≤ 0
  · have hxc : x / c ≤ 0 := div_nonpos_of_nonpos_of_nonneg h hc.le
    rw [max_eq_left hxc, max_eq_left h, zero_div]
  · have hx : 0 < x := not_le.mp h
    have hxc : 0 ≤ x / c := div_nonneg hx.le hc.le
    rw [max_eq_right hxc, max_eq_right hx.le]

/-- The one-variable core of `τ̃ ≤ ‖k‖²`: for `c > 0`, `c²φ(r/c) ≤ r²`. -/
lemma sq_mul_phi_le (φ : ℝ → ℝ) (hφ : ∀ s : ℝ, φ s ≤ (max 0 (s - 1)) ^ 2)
    {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) : c ^ 2 * φ (r / c) ≤ r ^ 2 := by
  by_cases h1 : r / c ≤ 1
  · have hm : max 0 (r / c - 1) = 0 := max_eq_left (by linarith)
    have h0 : φ (r / c) ≤ 0 := by simpa [hm] using hφ (r / c)
    have h2 := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg c) h0
    nlinarith
  · have hlt : 1 < r / c := not_le.mp h1
    have hcr : c < r := by
      have h := (lt_div_iff₀ hc).mp hlt
      simpa using h
    have hm : max 0 (r / c - 1) = r / c - 1 := max_eq_right (by linarith)
    have h0 : φ (r / c) ≤ (r / c - 1) ^ 2 := by simpa [hm] using hφ (r / c)
    have hEq : c ^ 2 * (r / c - 1) ^ 2 = (r - c) ^ 2 := by
      field_simp
    have hle : (r - c) ^ 2 ≤ r ^ 2 := by nlinarith
    calc c ^ 2 * φ (r / c) ≤ c ^ 2 * (r / c - 1) ^ 2 :=
          mul_le_mul_of_nonneg_left h0 (sq_nonneg c)
      _ = (r - c) ^ 2 := hEq
      _ ≤ r ^ 2 := hle

/-- The one-variable core of the kinked lower bound: for `c > 0`,
`c² · (max 0 (r/c - 2))² = (max (r - 2c) 0)²`. -/
lemma sq_mul_max_sub (c r : ℝ) (hc : 0 < c) :
    c ^ 2 * max 0 (r / c - 2) ^ 2 = max (r - 2 * c) 0 ^ 2 := by
  have h1 : r / c - 2 = (r - 2 * c) / c := by field_simp
  rw [h1, max_zero_div c (r - 2 * c) hc, max_comm (r - 2 * c) 0]
  field_simp

/-- The deficit arithmetic: for `0 ≤ x ≤ y` and `0 ≤ ε_T ≤ 1`,
`r² - ((1-ε_T)(r-x)₊² + ε_T(r-y)₊²) ≤ 4ry`. -/
lemma deficit_arith {eT x y r : ℝ} (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1)
    (hx0 : 0 ≤ x) (hxy : x ≤ y) (hr : 0 ≤ r) :
    r ^ 2 - ((1 - eT) * max (r - x) 0 ^ 2 + eT * max (r - y) 0 ^ 2) ≤ 4 * r * y := by
  by_cases h : r ≤ y
  · have h1 : max (r - x) 0 ≤ r := max_le (by linarith) hr
    have h2 : max (r - y) 0 ≤ r := max_le (by linarith) hr
    have h3 : (max (r - x) 0) ^ 2 ≤ r ^ 2 :=
      pow_le_pow_left₀ (le_max_right _ _) h1 2
    have h4 : (max (r - y) 0) ^ 2 ≤ r ^ 2 :=
      pow_le_pow_left₀ (le_max_right _ _) h2 2
    have h5 : (1 - eT) * max (r - x) 0 ^ 2 + eT * max (r - y) 0 ^ 2 ≤ r ^ 2 := by
      have ha : (1 - eT) * max (r - x) 0 ^ 2 ≤ (1 - eT) * r ^ 2 :=
        mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ 1 - eT)
      have hb : eT * max (r - y) 0 ^ 2 ≤ eT * r ^ 2 := mul_le_mul_of_nonneg_left h4 heT0
      calc (1 - eT) * max (r - x) 0 ^ 2 + eT * max (r - y) 0 ^ 2
          ≤ (1 - eT) * r ^ 2 + eT * r ^ 2 := add_le_add ha hb
        _ = r ^ 2 := by ring
    have h6 : r ^ 2 ≤ 4 * r * y := by nlinarith [mul_nonneg hr (sub_nonneg.mpr h)]
    have hS : 0 ≤ (1 - eT) * max (r - x) 0 ^ 2 + eT * max (r - y) 0 ^ 2 :=
      add_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) (mul_nonneg heT0 (sq_nonneg _))
    linarith [hS, h5, h6]
  · have hyr : y < r := not_le.mp h
    have hxr : x ≤ r := le_trans hxy hyr.le
    have hm1 : max (r - x) 0 = r - x := max_eq_left (sub_nonneg.mpr hxr)
    have hm2 : max (r - y) 0 = r - y := max_eq_left (sub_nonneg.mpr hyr.le)
    rw [hm1, hm2]
    have hid : r ^ 2 - ((1 - eT) * (r - x) ^ 2 + eT * (r - y) ^ 2)
        = (1 - eT) * (2 * r * x - x ^ 2) + eT * (2 * r * y - y ^ 2) := by ring
    rw [hid]
    have h3 : (1 - eT) * (2 * r * x - x ^ 2) ≤ (1 - eT) * (2 * r * y) := by
      apply mul_le_mul_of_nonneg_left _ (by linarith : (0 : ℝ) ≤ 1 - eT)
      nlinarith [mul_nonneg hr (sub_nonneg.mpr hxy), sq_nonneg x]
    have h4 : eT * (2 * r * y - y ^ 2) ≤ eT * (2 * r * y) := by
      apply mul_le_mul_of_nonneg_left _ heT0
      nlinarith [sq_nonneg y]
    have h5 : (1 - eT) * (2 * r * y) + eT * (2 * r * y) = 2 * r * y := by ring
    have hy0 : 0 ≤ y := le_trans hx0 hxy
    have h6 : 2 * r * y ≤ 4 * r * y := by nlinarith [mul_nonneg hr hy0]
    linarith [h3, h4, h5.le, h6]

/-! ## 1. `τ̃ ≤ ‖k‖²` -/

theorem tauTilde_le_sq {φ : ℝ → ℝ} (hφ : ∀ r : ℝ, φ r ≤ (max 0 (r - 1)) ^ 2)
    {eT s d ℓ : ℝ} (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) (hs : 0 < s) (hd : 0 < d) (hℓ : 0 < ℓ)
    (k : EuclideanSpace ℝ (Fin 3)) :
    tauTilde φ eT s d ℓ k ≤ ‖k‖ ^ 2 := by
  have hx : (0 : ℝ) < (2 * s * ℓ)⁻¹ := by positivity
  have hy : (0 : ℝ) < (2 * d * s * ℓ)⁻¹ := by positivity
  have h1 := sq_mul_phi_le φ hφ hx (norm_nonneg k)
  have h2 := sq_mul_phi_le φ hφ hy (norm_nonneg k)
  have h3 : 0 ≤ 1 - eT := by linarith
  simp only [tauTilde]
  calc (1 - eT) * ((2 * s * ℓ)⁻¹) ^ 2 * φ (‖k‖ / (2 * s * ℓ)⁻¹)
        + eT * ((2 * d * s * ℓ)⁻¹) ^ 2 * φ (‖k‖ / (2 * d * s * ℓ)⁻¹)
      = (1 - eT) * (((2 * s * ℓ)⁻¹) ^ 2 * φ (‖k‖ / (2 * s * ℓ)⁻¹))
        + eT * (((2 * d * s * ℓ)⁻¹) ^ 2 * φ (‖k‖ / (2 * d * s * ℓ)⁻¹)) := by ring
    _ ≤ (1 - eT) * ‖k‖ ^ 2 + eT * ‖k‖ ^ 2 :=
          add_le_add (mul_le_mul_of_nonneg_left h1 h3) (mul_le_mul_of_nonneg_left h2 heT0)
    _ = ‖k‖ ^ 2 := by ring

/-! ## 2. The kinked lower bound -/

theorem tauTilde_ge_kink {φ : ℝ → ℝ} (hφ : ∀ r : ℝ, (max 0 (r - 2)) ^ 2 ≤ φ r)
    {eT s d ℓ : ℝ} (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) (hs : 0 < s) (hd : 0 < d) (hℓ : 0 < ℓ)
    (k : EuclideanSpace ℝ (Fin 3)) :
    (1 - eT) * max (‖k‖ - (s * ℓ)⁻¹) 0 ^ 2 + eT * max (‖k‖ - (d * s * ℓ)⁻¹) 0 ^ 2
      ≤ tauTilde φ eT s d ℓ k := by
  have hx : (0 : ℝ) < (2 * s * ℓ)⁻¹ := by positivity
  have hy : (0 : ℝ) < (2 * d * s * ℓ)⁻¹ := by positivity
  have h1 := hφ (‖k‖ / (2 * s * ℓ)⁻¹)
  have h2 := hφ (‖k‖ / (2 * d * s * ℓ)⁻¹)
  have hm1 := sq_mul_max_sub (2 * s * ℓ)⁻¹ ‖k‖ hx
  have hm2 := sq_mul_max_sub (2 * d * s * ℓ)⁻¹ ‖k‖ hy
  rw [show 2 * (2 * s * ℓ)⁻¹ = (s * ℓ)⁻¹ from by field_simp] at hm1
  rw [show 2 * (2 * d * s * ℓ)⁻¹ = (d * s * ℓ)⁻¹ from by field_simp] at hm2
  have h3 : 0 ≤ 1 - eT := by linarith
  simp only [tauTilde]
  calc (1 - eT) * max (‖k‖ - (s * ℓ)⁻¹) 0 ^ 2
        + eT * max (‖k‖ - (d * s * ℓ)⁻¹) 0 ^ 2
      = (1 - eT) * (((2 * s * ℓ)⁻¹) ^ 2 * max 0 (‖k‖ / (2 * s * ℓ)⁻¹ - 2) ^ 2)
        + eT * (((2 * d * s * ℓ)⁻¹) ^ 2 * max 0 (‖k‖ / (2 * d * s * ℓ)⁻¹ - 2) ^ 2) := by
          rw [← hm1, ← hm2]
    _ ≤ (1 - eT) * (((2 * s * ℓ)⁻¹) ^ 2 * φ (‖k‖ / (2 * s * ℓ)⁻¹))
        + eT * (((2 * d * s * ℓ)⁻¹) ^ 2 * φ (‖k‖ / (2 * d * s * ℓ)⁻¹)) := by
          refine add_le_add ?_ ?_
          · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 (sq_nonneg _)) h3
          · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 (sq_nonneg _)) heT0
    _ = (1 - eT) * ((2 * s * ℓ)⁻¹) ^ 2 * φ (‖k‖ / (2 * s * ℓ)⁻¹)
        + eT * ((2 * d * s * ℓ)⁻¹) ^ 2 * φ (‖k‖ / (2 * d * s * ℓ)⁻¹) := by ring

/-! ## 3. The deficit bound -/

theorem tauTilde_deficit {φ : ℝ → ℝ} (hφ : ∀ r : ℝ, (max 0 (r - 2)) ^ 2 ≤ φ r)
    {eT s d ℓ : ℝ} (heT0 : 0 ≤ eT) (heT1 : eT ≤ 1) (hs : 0 < s) (hd0 : 0 < d) (hd1 : d ≤ 1)
    (hℓ : 0 < ℓ) (k : EuclideanSpace ℝ (Fin 3)) :
    ‖k‖ ^ 2 - tauTilde φ eT s d ℓ k ≤ 4 * ‖k‖ / (d * s * ℓ) := by
  have hx : (0 : ℝ) < (s * ℓ)⁻¹ := by positivity
  have hy : (0 : ℝ) < (d * s * ℓ)⁻¹ := by positivity
  have hxy : (s * ℓ)⁻¹ ≤ (d * s * ℓ)⁻¹ := by
    have hpos : 0 < s * ℓ := by positivity
    rw [inv_le_inv₀ hpos (by positivity)]
    have h := mul_le_mul_of_nonneg_right hd1 hpos.le
    nlinarith
  have hge := tauTilde_ge_kink hφ heT0 heT1 hs hd0 hℓ k
  have harith := deficit_arith heT0 heT1 hx.le hxy (norm_nonneg k)
  have hfin : 4 * (d * s * ℓ)⁻¹ = 4 / (d * s * ℓ) := by field_simp
  have hfin2 : 4 * ‖k‖ * (d * s * ℓ)⁻¹ = 4 * ‖k‖ / (d * s * ℓ) := by
    rw [div_eq_mul_inv]
  linarith [hge, harith, hfin2.le, hfin2.ge]

/-! ## 4. The `P_H^q` domination at `KzEnvAt E ρ` -/

theorem A_ge_of_taurad {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {F : Work.BoseB7.FockData Mode} {E : Work.BoseB7.Q3Env Mode} {K₀ ρ : ℝ}
    (hW1 : ∀ k : Mode, |E.W1 k| ≤ K₀ * E.aScat) (hρ : 0 ≤ ρ)
    (htaurad : ∀ q : Mode, F.PHq E.KH E.aScat q →
      ‖F.kmom q‖ ^ 2 / 2 + 3 * ρ * K₀ * E.aScat ≤ E.tau q) :
    (∀ q : Mode, F.PHq E.KH E.aScat q →
        ‖F.kmom q‖ ^ 2 / 2 ≤ (Work.BoseFixR.KzEnvAt E ρ).A q) ∧
      (∀ q : Mode, F.PHq E.KH E.aScat q →
        2 * |(Work.BoseFixR.KzEnvAt E ρ).B q| ≤ (Work.BoseFixR.KzEnvAt E ρ).A q) := by
  have hkey : ∀ q : Mode, F.PHq E.KH E.aScat q →
      ‖F.kmom q‖ ^ 2 / 2 + 2 * ρ * K₀ * E.aScat
        ≤ (Work.BoseFixR.KzEnvAt E ρ).A q := by
    intro q hq
    have h1 := htaurad q hq
    have h2 := (abs_le.mp (hW1 q)).1
    have h4 : (Work.BoseFixR.KzEnvAt E ρ).A q = E.tau q + ρ * E.W1 q := rfl
    have h5 : ρ * (-(K₀ * E.aScat)) ≤ ρ * E.W1 q := mul_le_mul_of_nonneg_left h2 hρ
    rw [h4]
    linarith
  refine ⟨fun q hq => ?_, fun q hq => ?_⟩
  · have h := hkey q hq
    have hA : (Work.BoseFixR.KzEnvAt E ρ).A q = E.tau q + ρ * E.W1 q := rfl
    rw [hA] at h
    have h2 : ρ * (2 * |E.W1 q|) ≤ ρ * (2 * (K₀ * E.aScat)) :=
      mul_le_mul_of_nonneg_left (by linarith [hW1 q]) hρ
    have h3 : |E.W1 q| ≥ 0 := abs_nonneg _
    nlinarith [h, h2, h3]
  · have h := hkey q hq
    have hA : (Work.BoseFixR.KzEnvAt E ρ).A q = E.tau q + ρ * E.W1 q := rfl
    have hB : (Work.BoseFixR.KzEnvAt E ρ).B q = ρ * E.W1 q := rfl
    rw [hA] at h
    have h3 : |ρ * E.W1 q| = ρ * |E.W1 q| := by rw [abs_mul, abs_of_nonneg hρ]
    rw [hB, h3]
    have h2 : ρ * (2 * |E.W1 q|) ≤ ρ * (2 * (K₀ * E.aScat)) :=
      mul_le_mul_of_nonneg_left (by linarith [hW1 q]) hρ
    nlinarith [h, h2]

end Work.BoseGateFS
