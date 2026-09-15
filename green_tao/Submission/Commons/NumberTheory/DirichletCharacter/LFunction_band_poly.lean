import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LFunction_norm_half_plane
import Submission.Commons.NumberTheory.DirichletCharacter.completedLFunction_eq
import Submission.Commons.NumberTheory.DirichletCharacter.rootNumber_norm_eq_one
import Submission.Commons.NumberTheory.DirichletCharacter.gammaFactor_ratio_band_large_t

open Complex DirichletCharacter
open scoped Real
set_option autoImplicit false

namespace Commons.NumberTheory.DirichletCharacter

noncomputable section

/-- inverse of a non-trivial character is non-trivial -/
private lemma inv_ne_one_of_ne_one {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    χ⁻¹ ≠ 1 := by
  intro h
  apply hχ
  have hh := congrArg (fun ψ : DirichletCharacter ℂ N => ψ⁻¹) h
  simpa using hh

/-- Γ does not vanish away from the non-positive integers. -/
private lemma gamma_ne_zero_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) : Complex.Gamma z ≠ 0 := by
  refine Complex.Gamma_ne_zero (s := z) ?_
  intro m hm
  apply hz
  rw [hm]
  simp

/-- If the imaginary part is non-zero, the gamma factor does not vanish. -/
private lemma gammaFactor_ne_zero_of_im_ne_zero {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : s.im ≠ 0) : χ.gammaFactor s ≠ 0 := by
  rcases χ.even_or_odd with hE | hO
  · rw [Even.gammaFactor_def hE]
    have hArg : ((s / 2).im ≠ 0) := by
      rw [Complex.div_im]
      simpa using hs
    have hπ : ((Real.pi : ℂ) ^ (-s / 2)) ≠ 0 := by
      rw [Complex.cpow_ne_zero_iff]
      exact Or.inl (by exact_mod_cast (ne_of_gt Real.pi_pos) : (Real.pi : ℂ) ≠ 0)
    have hΓ : Complex.Gamma (s / 2) ≠ 0 := gamma_ne_zero_of_im_ne_zero hArg
    simpa [Complex.Gammaℝ_def] using mul_ne_zero hπ hΓ
  · rw [Odd.gammaFactor_def hO]
    have hs1 : (s + 1).im ≠ 0 := by simpa using hs
    have hArg : (((s + 1) / 2).im ≠ 0) := by
      rw [Complex.div_im]
      simpa using hs1
    have hπ : ((Real.pi : ℂ) ^ (-(s + 1) / 2)) ≠ 0 := by
      rw [Complex.cpow_ne_zero_iff]
      exact Or.inl (by exact_mod_cast (ne_of_gt Real.pi_pos) : (Real.pi : ℂ) ≠ 0)
    have hΓ : Complex.Gamma ((s + 1) / 2) ≠ 0 := gamma_ne_zero_of_im_ne_zero hArg
    simpa [Complex.Gammaℝ_def] using mul_ne_zero hπ hΓ

/-- completed L function equals L times gamma factor, wherever gamma factor is nonzero -/
private lemma completedLFunction_eq_mul_gammaFactor_of_ne_zero {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {s : ℂ} (hsγ : χ.gammaFactor s ≠ 0)
    (hs0 : s ≠ 0) : completedLFunction χ s = LFunction χ s * χ.gammaFactor s := by
  have h := LFunction_eq_completed_div_gammaFactor χ s (Or.inl hs0)
  rw [h]
  exact (div_mul_cancel₀ _ hsγ).symm

/-- The functional equation in L-form (away from gamma poles). -/
private lemma LFunction_gammaFactor_FE {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχprim : χ.IsPrimitive) {s : ℂ} (hsγ : χ.gammaFactor s ≠ 0)
    (hsγ' : (χ⁻¹).gammaFactor (1 - s) ≠ 0) (hs0 : s ≠ 0) (h1s0 : 1 - s ≠ 0) :
    LFunction χ s * χ.gammaFactor s =
      ((N : ℂ) ^ (1 / 2 - s)) * χ.rootNumber *
        (LFunction (χ⁻¹) (1 - s) * (χ⁻¹).gammaFactor (1 - s)) := by
  have hFE := completedLFunction_eq χ hχprim s
  have hL1 : completedLFunction χ s = LFunction χ s * χ.gammaFactor s :=
    completedLFunction_eq_mul_gammaFactor_of_ne_zero χ hsγ hs0
  have hL2 : completedLFunction (χ⁻¹) (1 - s) = LFunction (χ⁻¹) (1 - s) * (χ⁻¹).gammaFactor (1 - s) :=
    completedLFunction_eq_mul_gammaFactor_of_ne_zero (χ := χ⁻¹) (s := 1 - s) hsγ' h1s0
  rw [hL1, hL2] at hFE
  simpa [mul_assoc, mul_comm, mul_left_comm] using hFE

/-- bound the L-function to the right: re ≥ 1/8 gives 16 N (1+|t|). -/
private lemma LFunction_bound_right {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {s : ℂ} (hs : (1 / 8 : ℝ) ≤ s.re) :
    ‖LFunction χ s‖ ≤ 16 * (N : ℝ) * (1 + |s.im|) := by
  have hs0 : 0 < s.re := lt_of_lt_of_le (by norm_num) hs
  have hb := LFunction_norm_half_plane χ hχ hs0
  have htri := Complex.norm_le_abs_re_add_abs_im s
  have hre_nonneg : 0 ≤ s.re := le_of_lt hs0
  have hnorm_le : ‖s‖ ≤ s.re + |s.im| := by
    calc
      ‖s‖ ≤ |s.re| + |s.im| := htri
      _ = s.re + |s.im| := by rw [abs_of_nonneg hre_nonneg]
  have hinv : (s.re)⁻¹ ≤ 8 := by
    have hle : 1 / s.re ≤ 8 := by
      have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < (1 / 8 : ℝ)) hs
      simpa using h
    simpa using hle
  have hdiv : ‖s‖ / s.re ≤ 8 * (1 + |s.im|) := by
    calc
      ‖s‖ / s.re ≤ (s.re + |s.im|) / s.re := by
        exact div_le_div_of_nonneg_right hnorm_le (le_of_lt hs0)
      _ = 1 + (s.re)⁻¹ * |s.im| := by
        field_simp [ne_of_gt hs0]
      _ ≤ 8 * (1 + |s.im|) := by
        have hle2 : (s.re)⁻¹ * |s.im| ≤ 8 * |s.im| := by
          exact mul_le_mul_of_nonneg_right hinv (abs_nonneg s.im)
        nlinarith
  calc
    ‖LFunction χ s‖ ≤ 2 * (N : ℝ) * ‖s‖ / s.re := hb
    _ = 2 * (N : ℝ) * (‖s‖ / s.re) := by ring
    _ ≤ 2 * (N : ℝ) * (8 * (1 + |s.im|)) := by
      exact mul_le_mul_of_nonneg_left hdiv (by positivity)
    _ = 16 * (N : ℝ) * (1 + |s.im|) := by ring

/-- `(N:ℝ)` is at least 1. -/
private lemma nat_ge_one (N : ℕ) [NeZero N] : (1 : ℝ) ≤ (N : ℝ) := by
  exact_mod_cast (Nat.succ_le_of_lt (Nat.pos_of_ne_zero (NeZero.ne N)))

/-- region A: bounded near the imaginary axis by a constant (entire function on compact). -/
private lemma LFunction_bound_small_im {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ s : ℂ, |s.im| ≤ 1 → -1 ≤ s.re → s.re ≤ (1 / 8 : ℝ) →
      ‖LFunction χ s‖ ≤ M := by
  classical
  let K : Set ℂ := Metric.closedBall (0 : ℂ) 2
  have hcont : Continuous fun z : ℂ => ‖LFunction χ z‖ :=
    (differentiable_LFunction hχ).continuous.norm
  have hK : IsCompact K := ProperSpace.isCompact_closedBall (0 : ℂ) 2
  obtain ⟨M0, hM0⟩ := IsCompact.exists_bound_of_continuousOn hK (hcont.continuousOn)
  refine ⟨max M0 0, le_max_right M0 0, ?_⟩
  intro s hs_im hs_low hs_high
  have hnorm_le_two : ‖s‖ ≤ 2 := by
    have hre_abs : |s.re| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith
    have htri := Complex.norm_le_abs_re_add_abs_im s
    calc
      ‖s‖ ≤ |s.re| + |s.im| := htri
      _ ≤ 2 := by linarith
  have hmem : s ∈ K := by
    dsimp [K]
    simpa [dist_eq_norm, sub_zero] using hnorm_le_two
  have hb0 := hM0 s hmem
  have hb : ‖LFunction χ s‖ ≤ M0 := by
    simpa using hb0
  exact le_trans hb (le_max_left M0 0)

/-- main band bound in the left region with large imaginary part. -/
private lemma LFunction_bound_left_large_im {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive)
    {C₀ κ₀ : ℝ} (hC₀ : 0 < C₀) (hκ₀ : 0 ≤ κ₀)
    (hratio : ∀ (σ : ℝ), -1 ≤ σ → σ ≤ (1 / 8 : ℝ) → ∀ t : ℝ, 1 ≤ |t| →
      ‖(χ⁻¹).gammaFactor (1 - ((σ : ℂ) + I * (t : ℂ))) /
          χ.gammaFactor ((σ : ℂ) + I * (t : ℂ))‖ ≤ C₀ * (1 + |t|) ^ κ₀)
    {s : ℂ} (hs_low : -1 ≤ s.re) (hs_high : s.re ≤ (1 / 8 : ℝ)) (hs_t : 1 ≤ |s.im|) :
    ‖LFunction χ s‖ ≤ 16 * C₀ * (N : ℝ) ^ (5 / 2 : ℝ) * (1 + |s.im|) ^ (1 + κ₀) := by
  have ht_ne : s.im ≠ 0 := by
    intro h
    rw [h] at hs_t
    norm_num at hs_t
  have hs0 : s ≠ 0 := by
    intro h
    apply ht_ne
    rw [h]
    simp
  have h1s0 : (1 - s) ≠ 0 := by
    intro h
    apply ht_ne
    have him : (1 - s).im = 0 := by rw [h]; simp
    simpa using him
  have hγs : χ.gammaFactor s ≠ 0 := gammaFactor_ne_zero_of_im_ne_zero χ ht_ne
  have hγ1s : (χ⁻¹).gammaFactor (1 - s) ≠ 0 := by
    apply gammaFactor_ne_zero_of_im_ne_zero (χ := χ⁻¹)
    simpa using ht_ne
  have hFE := LFunction_gammaFactor_FE χ hχprim (s := s) hγs hγ1s hs0 h1s0
  let A : ℝ := ‖((N : ℂ) ^ (1 / 2 - s))‖
  let B : ℝ := ‖χ.rootNumber‖
  let C : ℝ := ‖LFunction (χ⁻¹) (1 - s)‖
  let D : ℝ := ‖(χ⁻¹).gammaFactor (1 - s)‖
  let G : ℝ := ‖χ.gammaFactor s‖
  have hγs_pos : 0 < G := by dsimp [G]; exact norm_pos_iff.mpr hγs
  have hG_ne : G ≠ 0 := ne_of_gt hγs_pos
  have hnm1 : ‖((N : ℂ) ^ (1 / 2 - s)) * χ.rootNumber *
        (LFunction (χ⁻¹) (1 - s) * (χ⁻¹).gammaFactor (1 - s))‖ = A * B * C * D := by
    dsimp [A, B, C, D]
    rw [norm_mul]
    rw [norm_mul]
    rw [norm_mul]
    ring
  have hnorm_eq : ‖LFunction χ s‖ * G = A * B * C * D := by
    calc
      ‖LFunction χ s‖ * G = ‖LFunction χ s‖ * ‖χ.gammaFactor s‖ := rfl
      _ = ‖LFunction χ s * χ.gammaFactor s‖ := by rw [norm_mul]
      _ = ‖((N : ℂ) ^ (1 / 2 - s)) * χ.rootNumber *
            (LFunction (χ⁻¹) (1 - s) * (χ⁻¹).gammaFactor (1 - s))‖ := by rw [hFE]
      _ = A * B * C * D := hnm1
  have hL_div : ‖LFunction χ s‖ = (A * B * C * D) / G := by
    calc
      ‖LFunction χ s‖ = (‖LFunction χ s‖ * G) / G := by field_simp [hG_ne]
      _ = (A * B * C * D) / G := by rw [hnorm_eq]
  -- estimates of the factors
  let b : ℝ := 1 + |s.im|
  have hb_pos : 0 < b := by dsimp [b]; positivity
  have hσ : (1 / 2 - s.re) ≤ 3 / 2 := by linarith
  have hA : A ≤ (N : ℝ) ^ (3 / 2 : ℝ) := by
    dsimp [A]
    have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
    have hEq : ‖((N : ℂ) ^ (1 / 2 - s))‖ = (N : ℝ) ^ ((1 / 2 : ℝ) - s.re) := by
      rw [← Complex.ofReal_natCast (n := N)]
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hNpos (1 / 2 - s)]
      congr 1
      simp
    rw [hEq]
    exact Real.rpow_le_rpow_of_exponent_le (nat_ge_one N) hσ
  have hB : B = 1 := by
    dsimp [B]
    exact rootNumber_norm_eq_one χ hχprim
  have hre1s : (1 / 8 : ℝ) ≤ (1 - s).re := by
    simp
    linarith
  have hC : C ≤ 16 * (N : ℝ) * b := by
    dsimp [C, b]
    have hb' := LFunction_bound_right (χ := χ⁻¹) (inv_ne_one_of_ne_one χ hχ)
      (s := 1 - s) hre1s
    simpa using hb'
  have hs_form : s = ((s.re : ℝ) : ℂ) + I * (s.im : ℂ) := by
    apply Complex.ext <;> simp
  have hDG : D / G ≤ C₀ * b ^ κ₀ := by
    have hrr := hratio (s.re) hs_low hs_high (s.im) hs_t
    calc
      D / G = ‖(χ⁻¹).gammaFactor (1 - s)‖ / ‖χ.gammaFactor s‖ := rfl
      _ = ‖(χ⁻¹).gammaFactor (1 - s) / χ.gammaFactor s‖ := by
            rw [norm_div]
      _ ≤ C₀ * b ^ κ₀ := by
            dsimp [b]
            rw [← hs_form] at hrr
            simpa using hrr
  -- put the pieces together
  have hNpos : 0 < (N : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne N))
  have hNadd : (N : ℝ) ^ (3 / 2 : ℝ) * (N : ℝ) = (N : ℝ) ^ (5 / 2 : ℝ) := by
    calc
      (N : ℝ) ^ (3 / 2 : ℝ) * (N : ℝ) = (N : ℝ) ^ (3 / 2 : ℝ) * (N : ℝ) ^ (1 : ℝ) := by
        rw [Real.rpow_one]
      _ = (N : ℝ) ^ ((3 / 2 : ℝ) + 1) := by
        rw [← Real.rpow_add hNpos (3 / 2 : ℝ) 1]
      _ = (N : ℝ) ^ (5 / 2 : ℝ) := by norm_num
  have hbadd : b * b ^ κ₀ = b ^ (1 + κ₀) := by
    calc
      b * b ^ κ₀ = b ^ (1 : ℝ) * b ^ κ₀ := by rw [Real.rpow_one]
      _ = b ^ (1 + κ₀) := by
        rw [← Real.rpow_add hb_pos 1 κ₀]
  calc
    ‖LFunction χ s‖ = (A * B * C * D) / G := hL_div
    _ = A * B * C * (D / G) := by field_simp [hG_ne]
    _ = A * C * (D / G) := by rw [hB]; ring
    _ ≤ (N : ℝ) ^ (3 / 2 : ℝ) * (16 * (N : ℝ) * b) * (C₀ * b ^ κ₀) := by
          gcongr
    _ = 16 * C₀ * ((N : ℝ) ^ (3 / 2 : ℝ) * (N : ℝ)) * (b * b ^ κ₀) := by ring
    _ = 16 * C₀ * (N : ℝ) ^ (5 / 2 : ℝ) * (1 + |s.im|) ^ (1 + κ₀) := by
          rw [hNadd, hbadd]

/-- absorb `a·x^p·y^q ≤ C·x^k·y^k` when `0 ≤ a ≤ C`, `p,q ≤ k`, `x,y ≥ 1`. -/
private lemma absorb_pow {x y k : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hk : 0 ≤ k)
    {a C : ℝ} (ha0 : 0 ≤ a) (hCa : a ≤ C) {p q : ℝ} (hp : p ≤ k) (hq : q ≤ k) :
    a * x ^ p * y ^ q ≤ C * x ^ k * y ^ k := by
  have hxp : x ^ p ≤ x ^ k := Real.rpow_le_rpow_of_exponent_le hx hp
  have hyq : y ^ q ≤ y ^ k := Real.rpow_le_rpow_of_exponent_le hy hq
  have hxp0 : 0 ≤ x ^ p := Real.rpow_nonneg (by linarith : 0 ≤ x) p
  have hyq0 : 0 ≤ y ^ q := Real.rpow_nonneg (by linarith : 0 ≤ y) q
  have hxk0 : 0 ≤ x ^ k := Real.rpow_nonneg (by linarith : 0 ≤ x) k
  have hC0 : 0 ≤ C := le_trans ha0 hCa
  have hCxk0 : 0 ≤ C * x ^ k := mul_nonneg hC0 hxk0
  calc
    a * x ^ p * y ^ q ≤ C * x ^ p * y ^ q := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCa hxp0) hyq0
    _ ≤ C * x ^ k * y ^ q := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hxp hC0) hyq0
    _ ≤ C * x ^ k * y ^ k := by
      exact mul_le_mul_of_nonneg_left hyq hCxk0

/-- **Polynomial bound for the Dirichlet L-function of a primitive non-trivial character on
the band `-1 ≤ Re s ≤ 8`** — `‖L(χ,s)‖ ≤ C·(1+|Im s|)^k·N^k`. -/
theorem LFunction_band_poly {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hχprim : χ.IsPrimitive) :
    ∃ C k : ℝ, 0 < C ∧ 0 ≤ k ∧ ∀ s : ℂ, (-1 : ℝ) ≤ s.re → s.re ≤ 8 →
      ‖DirichletCharacter.LFunction χ s‖ ≤ C * (1 + |s.im|) ^ k * (N : ℝ) ^ k := by
  classical
  obtain ⟨C₀, κ₀, hC₀, hκ₀, hratio⟩ := gammaFactor_ratio_band_large_t χ
  obtain ⟨M₀, hM₀nn, hM₀⟩ := LFunction_bound_small_im χ hχ
  let k : ℝ := max (5 / 2 : ℝ) (1 + κ₀)
  let C : ℝ := 16 * C₀ + 16 + M₀ + 1
  have hk0 : 0 ≤ k := by
    dsimp [k]
    exact le_max_of_le_left (by norm_num : 0 ≤ (5 / 2 : ℝ))
  have hkge1 : (1 : ℝ) ≤ k := by
    dsimp [k]
    exact le_max_of_le_left (by norm_num : (1 : ℝ) ≤ (5 / 2 : ℝ))
  have hk52 : (5 / 2 : ℝ) ≤ k := by dsimp [k]; exact le_max_left _ _
  have hk1k : 1 + κ₀ ≤ k := by dsimp [k]; exact le_max_right _ _
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hC_ge16C0 : 16 * C₀ ≤ C := by dsimp [C]; linarith
  have hC_ge16 : (16 : ℝ) ≤ C := by dsimp [C]; linarith
  have hC_geM : M₀ ≤ C := by dsimp [C]; nlinarith [hM₀nn]
  refine ⟨C, k, hCpos, hk0, ?_⟩
  intro s hs_low hs_high
  let Nn : ℝ := (N : ℝ)
  let b : ℝ := 1 + |s.im|
  have hN1 : 1 ≤ Nn := by dsimp [Nn]; exact nat_ge_one N
  have hb1 : 1 ≤ b := by dsimp [b]; linarith [abs_nonneg s.im]
  have hNn_nonneg : 0 ≤ Nn := by linarith
  have hb_nonneg : 0 ≤ b := by linarith
  by_cases hright : (1 / 8 : ℝ) ≤ s.re
  · -- right region: re ≥ 1/8
    have hbnd : ‖LFunction χ s‖ ≤ 16 * Nn * b := by
      have h0 := LFunction_bound_right χ hχ hright
      dsimp [Nn, b] at h0 ⊢
      simpa using h0
    calc
      ‖DirichletCharacter.LFunction χ s‖ ≤ 16 * Nn * b := hbnd
      _ ≤ C * Nn ^ k * b ^ k := by
        have h16 : (16 : ℝ) ≤ C := hC_ge16
        simpa [Real.rpow_one] using
          (absorb_pow (x := Nn) (y := b) (a := (16 : ℝ)) (C := C) (p := (1 : ℝ)) (q := (1 : ℝ))
            hN1 hb1 hk0 (by norm_num : 0 ≤ (16 : ℝ)) h16 hkge1 hkge1)
      _ = C * b ^ k * Nn ^ k := by ring
  · have hs_high' : s.re ≤ (1 / 8 : ℝ) := le_of_not_ge hright
    by_cases ht : 1 ≤ |s.im|
    · -- left region, large imaginary part (functional equation)
      have hbnd := LFunction_bound_left_large_im χ hχ hχprim (hC₀ := hC₀) (hκ₀ := hκ₀)
        hratio hs_low hs_high' ht
      have hbnd' : ‖LFunction χ s‖ ≤ (16 * C₀) * Nn ^ (5 / 2 : ℝ) * b ^ (1 + κ₀) := by
        dsimp [Nn, b] at hbnd ⊢
        simpa [mul_assoc] using hbnd
      calc
        ‖DirichletCharacter.LFunction χ s‖ ≤ (16 * C₀) * Nn ^ (5 / 2 : ℝ) * b ^ (1 + κ₀) := hbnd'
        _ ≤ C * Nn ^ k * b ^ k := by
          exact absorb_pow (x := Nn) (y := b) (a := 16 * C₀) (C := C)
            (p := (5 / 2 : ℝ)) (q := 1 + κ₀)
            hN1 hb1 hk0 (by positivity : 0 ≤ 16 * C₀) hC_ge16C0 hk52 hk1k
        _ = C * b ^ k * Nn ^ k := by ring
    · -- small imaginary part: continuous on compact
      have ht1 : |s.im| ≤ 1 := le_of_lt (lt_of_not_ge ht)
      have hbnd : ‖LFunction χ s‖ ≤ M₀ := hM₀ s ht1 hs_low hs_high'
      have hb1' : (1 : ℝ) ≤ b ^ k := Real.one_le_rpow hb1 hk0
      have hN1' : (1 : ℝ) ≤ Nn ^ k := Real.one_le_rpow hN1 hk0
      calc
        ‖DirichletCharacter.LFunction χ s‖ ≤ M₀ := hbnd
        _ ≤ C := hC_geM
        _ ≤ C * b ^ k := by
          simpa using (mul_le_mul_of_nonneg_left hb1' (by positivity : 0 ≤ C))
        _ ≤ C * b ^ k * Nn ^ k := by
          simpa using (mul_le_mul_of_nonneg_left hN1' (by positivity : 0 ≤ C * b ^ k))
        _ = C * (1 + |s.im|) ^ k * (N : ℝ) ^ k := by
          dsimp [b, Nn]

end
end Commons.NumberTheory.DirichletCharacter
