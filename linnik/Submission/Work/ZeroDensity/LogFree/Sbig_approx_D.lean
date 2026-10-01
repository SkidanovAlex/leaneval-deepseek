import Mathlib
import Submission.Work.ZeroDensity.LogFree.Defs
import Submission.Work.LinnikAreas.Density4.Sbig_approx

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.ZeroDensity.LogFree

open Work.LinnikAreas.Density4

/-! ## Auxiliary real-analysis lemmas

These are the two analytic ingredients of `Sbig_approx` (HB (11.10) plus the tail), restated at a
general scale `(L, U)`: the evaluation of the tail majorant and its arithmetic closure. -/

/-- **Tail evaluation of the `Sbig` majorant.**  For `a > 0` and `c ≥ 0`,
`Σ_{k} (k+c)³ e^{-a(k+c)} ≤ e^{-ac}·[(1+1/a)c³ + (6c²/a + 24c/a² + 48/a³)(1+2/a)]`.
The cube is expanded, the Taylor bounds `e^x ≥ 1+x`, `1+x+x²/2 ≤ e^x`, `1+x+x²/2+x³/6 ≤ e^x`
give `k s^k ≤ 2/a`, `k² s^k ≤ 8/a²`, `k³ s^k ≤ 48/a³` for `s = e^{-a/2}`, and everything reduces to
geometric series with `1/(1-e^{-t}) ≤ 1 + 1/t`. -/
private theorem cube_exp_tsum_bound_aux {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    (∑' k : ℕ, (((k : ℝ) + c)^3) * Real.exp (-(a * ((k : ℝ) + c))))
      ≤ Real.exp (-(a*c)) * ((1 + 1/a) * c^3 + (6*c^2/a + 24*c/a^2 + 48/a^3) * (1 + 2/a)) := by
  have hhalf : {t : ℝ} → 0 < t → 1 / (1 - Real.exp (-t)) ≤ 1 + 1/t := by
    intro t ht
    have h1t : (0:ℝ) < 1 + t := by linarith
    have hexp : Real.exp (-t) ≤ 1/(1+t) := by
      rw [Real.exp_neg, one_div, inv_le_inv₀ (Real.exp_pos t) h1t]
      linarith [Real.add_one_le_exp t]
    have hpos : 0 < 1 - Real.exp (-t) := by
      have := Real.exp_lt_one_iff.mpr (by linarith : -t < 0); linarith
    have hpos' : 0 < t/(1+t) := by positivity
    have hden : t/(1+t) ≤ 1 - Real.exp (-t) := by
      have h2 : t/(1+t) = 1 - 1/(1+t) := by field_simp; ring
      linarith
    calc 1 / (1 - Real.exp (-t)) ≤ 1 / (t/(1+t)) := one_div_le_one_div_of_le hpos' hden
      _ = 1 + 1/t := by field_simp; ring
  set r : ℝ := Real.exp (-a) with hr
  set s : ℝ := Real.exp (-(a/2)) with hs
  have hr0 : 0 < r := by rw [hr]; exact Real.exp_pos _
  have hr1 : r < 1 := by rw [hr]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hs0 : 0 < s := by rw [hs]; exact Real.exp_pos _
  have hs1 : s < 1 := by rw [hs]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hrsum : (∑' k : ℕ, r^k) = (1-r)⁻¹ := tsum_geometric_of_lt_one hr0.le hr1
  have hssum : (∑' k : ℕ, s^k) = (1-s)⁻¹ := tsum_geometric_of_lt_one hs0.le hs1
  have hrsq : r = s^2 := by rw [hr, hs, sq, ← Real.exp_add]; congr 1; ring
  have hrpow : ∀ k : ℕ, r^k = (s^k)^2 := by
    intro k
    have h1 : r^k = s^k * s^k := by rw [hrsq, sq, mul_pow]
    rw [h1, sq]
  have hs_pow : ∀ k : ℕ, s^k = Real.exp (-((a*(k:ℝ))/2)) := by
    intro k
    rw [hs, ← Real.exp_nat_mul]; congr 1; ring
  have he_mul : ∀ k : ℕ, Real.exp ((a*(k:ℝ))/2) * s^k = 1 := by
    intro k
    rw [hs_pow k, ← Real.exp_add, show (a*(k:ℝ))/2 + -((a*(k:ℝ))/2) = 0 by ring, Real.exp_zero]
  have hk1 : ∀ k : ℕ, (k:ℝ) * s^k ≤ 2/a := by
    intro k
    have hle : (k:ℝ) ≤ (2/a) * Real.exp ((a*(k:ℝ))/2) := by
      have h2 : (2/a) * ((a*(k:ℝ))/2) = (k:ℝ) := by field_simp
      calc (k:ℝ) = (2/a) * ((a*(k:ℝ))/2) := h2.symm
        _ ≤ (2/a) * Real.exp ((a*(k:ℝ))/2) :=
            mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp ((a*(k:ℝ))/2)]) (by positivity)
    calc (k:ℝ) * s^k ≤ ((2/a) * Real.exp ((a*(k:ℝ))/2)) * s^k :=
          mul_le_mul_of_nonneg_right hle (by positivity)
      _ = (2/a) * (Real.exp ((a*(k:ℝ))/2) * s^k) := by ring
      _ = (2/a) * 1 := by rw [he_mul k]
      _ = 2/a := by ring
  have hk2 : ∀ k : ℕ, (k:ℝ)^2 * s^k ≤ 8/a^2 := by
    intro k
    have hx : 0 ≤ (a*(k:ℝ))/2 := by positivity
    have hle : ((a*(k:ℝ))/2)^2/2 ≤ Real.exp ((a*(k:ℝ))/2) := by
      have := Real.quadratic_le_exp_of_nonneg hx; linarith
    have hle2 : (k:ℝ)^2 ≤ (8/a^2) * Real.exp ((a*(k:ℝ))/2) := by
      have h3 : ((a*(k:ℝ))/2)^2/2 = a^2*(k:ℝ)^2/8 := by ring
      rw [h3] at hle
      have h4 : (a^2*(k:ℝ)^2/8) * (8/a^2) = (k:ℝ)^2 := by field_simp
      calc (k:ℝ)^2 = (a^2*(k:ℝ)^2/8) * (8/a^2) := h4.symm
        _ ≤ Real.exp ((a*(k:ℝ))/2) * (8/a^2) := mul_le_mul_of_nonneg_right hle (by positivity)
        _ = (8/a^2) * Real.exp ((a*(k:ℝ))/2) := by ring
    calc (k:ℝ)^2 * s^k ≤ ((8/a^2) * Real.exp ((a*(k:ℝ))/2)) * s^k :=
          mul_le_mul_of_nonneg_right hle2 (by positivity)
      _ = (8/a^2) * (Real.exp ((a*(k:ℝ))/2) * s^k) := by ring
      _ = 8/a^2 := by rw [he_mul k]; ring
  have hk3 : ∀ k : ℕ, (k:ℝ)^3 * s^k ≤ 48/a^3 := by
    intro k
    have hx : 0 ≤ (a*(k:ℝ))/2 := by positivity
    have h := Real.sum_le_exp_of_nonneg hx 4
    have h2 : (∑ i ∈ Finset.range 4, ((a*(k:ℝ))/2)^i / (i.factorial : ℝ))
        = 1 + (a*(k:ℝ))/2 + ((a*(k:ℝ))/2)^2/2 + ((a*(k:ℝ))/2)^3/6 := by
      simp [Finset.sum_range_succ]; ring
    rw [h2] at h
    have hle : ((a*(k:ℝ))/2)^3/6 ≤ Real.exp ((a*(k:ℝ))/2) := by
      have hnn : 0 ≤ 1 + (a*(k:ℝ))/2 + ((a*(k:ℝ))/2)^2/2 := by positivity
      linarith
    have hle2 : (k:ℝ)^3 ≤ (48/a^3) * Real.exp ((a*(k:ℝ))/2) := by
      have h3 : ((a*(k:ℝ))/2)^3/6 = a^3*(k:ℝ)^3/48 := by ring
      rw [h3] at hle
      have h4 : (a^3*(k:ℝ)^3/48) * (48/a^3) = (k:ℝ)^3 := by field_simp
      calc (k:ℝ)^3 = (a^3*(k:ℝ)^3/48) * (48/a^3) := h4.symm
        _ ≤ Real.exp ((a*(k:ℝ))/2) * (48/a^3) := mul_le_mul_of_nonneg_right hle (by positivity)
        _ = (48/a^3) * Real.exp ((a*(k:ℝ))/2) := by ring
    calc (k:ℝ)^3 * s^k ≤ ((48/a^3) * Real.exp ((a*(k:ℝ))/2)) * s^k :=
          mul_le_mul_of_nonneg_right hle2 (by positivity)
      _ = (48/a^3) * (Real.exp ((a*(k:ℝ))/2) * s^k) := by ring
      _ = 48/a^3 := by rw [he_mul k]; ring
  have hkey : ∀ k : ℕ, ((k:ℝ)+c)^3 * Real.exp (-(a*((k:ℝ)+c)))
      ≤ Real.exp (-(a*c)) * (c^3 * r^k + (6*c^2/a + 24*c/a^2 + 48/a^3) * s^k) := by
    intro k
    have hexpfac : Real.exp (-(a*((k:ℝ)+c))) = Real.exp (-(a*c)) * r^k := by
      rw [hr, show -(a*((k:ℝ)+c)) = -(a*c) + (k:ℝ)*(-a) by ring, Real.exp_add, Real.exp_nat_mul]
    have hkr : (k:ℝ) * r^k ≤ (2/a) * s^k := by
      rw [hrpow k]
      calc (k:ℝ) * (s^k)^2 = ((k:ℝ)*s^k) * s^k := by ring
        _ ≤ (2/a) * s^k := mul_le_mul_of_nonneg_right (hk1 k) (by positivity)
    have hk2r : (k:ℝ)^2 * r^k ≤ (8/a^2) * s^k := by
      rw [hrpow k]
      calc (k:ℝ)^2 * (s^k)^2 = ((k:ℝ)^2*s^k) * s^k := by ring
        _ ≤ (8/a^2) * s^k := mul_le_mul_of_nonneg_right (hk2 k) (by positivity)
    have hk3r : (k:ℝ)^3 * r^k ≤ (48/a^3) * s^k := by
      rw [hrpow k]
      calc (k:ℝ)^3 * (s^k)^2 = ((k:ℝ)^3*s^k) * s^k := by ring
        _ ≤ (48/a^3) * s^k := mul_le_mul_of_nonneg_right (hk3 k) (by positivity)
    have hsplit : ((k:ℝ)+c)^3 * (Real.exp (-(a*c)) * r^k)
        = Real.exp (-(a*c)) * (((k:ℝ)+c)^3 * r^k) := by ring
    rw [hexpfac, hsplit]
    have hexpand : ((k:ℝ)+c)^3 * r^k
        = c^3 * r^k + 3*c^2 * ((k:ℝ)*r^k) + 3*c * ((k:ℝ)^2*r^k) + ((k:ℝ)^3*r^k) := by ring
    rw [hexpand]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    have h1 := mul_le_mul_of_nonneg_left hkr (by positivity : (0:ℝ) ≤ 3*c^2)
    have h2 := mul_le_mul_of_nonneg_left hk2r (by positivity : (0:ℝ) ≤ 3*c)
    have h4 : 3*c^2 * ((2/a)*s^k) + 3*c*((8/a^2)*s^k) + (48/a^3)*s^k
        = (6*c^2/a + 24*c/a^2 + 48/a^3)*s^k := by ring
    linarith [h1, h2, hk3r, h4]
  have hs1' : Summable (fun k : ℕ => c^3 * r^k) := (summable_geometric_of_lt_one hr0.le hr1).mul_left _
  have hs2' : Summable (fun k : ℕ => (6*c^2/a + 24*c/a^2 + 48/a^3) * s^k) :=
    (summable_geometric_of_lt_one hs0.le hs1).mul_left _
  have hmaj : Summable (fun k : ℕ => Real.exp (-(a*c)) * (c^3 * r^k + (6*c^2/a + 24*c/a^2 + 48/a^3) * s^k)) :=
    (hs1'.add hs2').mul_left _
  have hlhs : Summable (fun k : ℕ => ((k:ℝ)+c)^3 * Real.exp (-(a*((k:ℝ)+c)))) :=
    Summable.of_nonneg_of_le (fun k => by positivity) hkey hmaj
  calc (∑' k : ℕ, ((k:ℝ)+c)^3 * Real.exp (-(a*((k:ℝ)+c))))
      ≤ ∑' k : ℕ, Real.exp (-(a*c)) * (c^3 * r^k + (6*c^2/a + 24*c/a^2 + 48/a^3) * s^k) :=
        Summable.tsum_le_tsum hkey hlhs hmaj
    _ = Real.exp (-(a*c)) * (c^3 * (1-r)⁻¹ + (6*c^2/a + 24*c/a^2 + 48/a^3) * (1-s)⁻¹) := by
        rw [tsum_mul_left, Summable.tsum_add hs1' hs2', tsum_mul_left, tsum_mul_left, hrsum, hssum]
    _ ≤ Real.exp (-(a*c)) * ((1 + 1/a) * c^3 + (6*c^2/a + 24*c/a^2 + 48/a^3) * (1 + 2/a)) := by
        have h1 : (1-r)⁻¹ ≤ 1 + 1/a := by
          have h := hhalf ha
          rw [one_div, ← hr] at h
          exact h
        have h2 : (1-s)⁻¹ ≤ 1 + 2/a := by
          have h := hhalf (by linarith : (0:ℝ) < a/2)
          rw [one_div, ← hs, show (1:ℝ)/(a/2) = 2/a by ring] at h
          exact h
        have hc3 : (0:ℝ) ≤ c^3 := by positivity
        have hC : (0:ℝ) ≤ 6*c^2/a + 24*c/a^2 + 48/a^3 := by positivity
        have hA : (0:ℝ) ≤ Real.exp (-(a*c)) := (Real.exp_pos _).le
        apply mul_le_mul_of_nonneg_left _ hA
        calc c^3 * (1-r)⁻¹ + (6*c^2/a + 24*c/a^2 + 48/a^3) * (1-s)⁻¹
            ≤ c^3 * (1 + 1/a) + (6*c^2/a + 24*c/a^2 + 48/a^3) * (1 + 2/a) :=
              add_le_add (mul_le_mul_of_nonneg_left h1 hc3) (mul_le_mul_of_nonneg_left h2 hC)
          _ = (1 + 1/a) * c^3 + (6*c^2/a + 24*c/a^2 + 48/a^3) * (1 + 2/a) := by ring

/-- **Arithmetic closure of the `Sbig` tail at a general scale.**  For `u > 0`, `L ≥ log 2`,
`U = e^{uL}`, `a = L²/U` and `U ≤ c ≤ U+1`,
`e^{-ac}[(1+1/a)c³ + (6c²/a + 24c/a² + 48/a³)(1+2/a)] ≤ 10⁶ e^{8u²}/L`. -/
private theorem tail_majorant_le_aux {u L U a c : ℝ} (hu : 0 < u) (hL : Real.log 2 ≤ L)
    (hUL : U = Real.exp (u * L)) (ha : a = L ^ 2 / U) (hUc : U ≤ c) (hc : c ≤ U + 1) :
    Real.exp (-(a * c)) *
      ((1 + 1 / a) * c ^ 3 + (6 * c ^ 2 / a + 24 * c / a ^ 2 + 48 / a ^ 3) * (1 + 2 / a))
      ≤ 1000000 * Real.exp (8 * u ^ 2) / L := by
  have hLpos : 0 < L := lt_of_lt_of_le (Real.log_pos (by norm_num)) hL
  have hU1 : 1 ≤ U := by
    rw [hUL]
    exact (Real.one_lt_exp_iff.mpr (by positivity)).le
  have hUpos : 0 < U := lt_of_lt_of_le zero_lt_one hU1
  have hc0 : 0 ≤ c := by linarith
  have hapos : 0 < a := by rw [ha]; positivity
  have hexp_le : Real.exp (-(a*c)) ≤ Real.exp (-(L^2)) := by
    apply Real.exp_le_exp.mpr
    have h1 : a * c = L^2 * (c/U) := by rw [ha]; field_simp
    have h2 : 1 ≤ c/U := (le_div_iff₀ hUpos).mpr (by simpa using hUc)
    have h3 : L^2 ≤ L^2 * (c/U) := by
      have := pow_pos hLpos 2
      nlinarith
    rw [h1]; linarith
  have hbr : 0 ≤ (1 + 1 / a) * c ^ 3 + (6 * c ^ 2 / a + 24 * c / a ^ 2 + 48 / a ^ 3) * (1 + 2 / a) := by
    have h1 : 0 < 1 + 1/a := by positivity
    have h2 : 0 ≤ c^3 := by positivity
    have h3 : 0 ≤ 6 * c ^ 2 / a + 24 * c / a ^ 2 + 48 / a ^ 3 := by positivity
    have h4 : 0 < 1 + 2/a := by positivity
    positivity
  have harith := arith_bound (u := u) (L := L) (c := c) (a := a) (U := U)
    hu hL hU1 hUL ha hc0 hc
  rw [le_div_iff₀ hLpos]
  calc (Real.exp (-(a * c)) *
      ((1 + 1 / a) * c ^ 3 + (6 * c ^ 2 / a + 24 * c / a ^ 2 + 48 / a ^ 3) * (1 + 2 / a))) * L
      = L * (Real.exp (-(a * c)) *
          ((1 + 1 / a) * c ^ 3 + (6 * c ^ 2 / a + 24 * c / a ^ 2 + 48 / a ^ 3) * (1 + 2 / a))) := by
        ring
    _ ≤ L * (Real.exp (-(L^2)) *
          ((1 + 1 / a) * c ^ 3 + (6 * c ^ 2 / a + 24 * c / a ^ 2 + 48 / a ^ 3) * (1 + 2 / a))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hexp_le hbr) hLpos.le
    _ ≤ 1000000 * Real.exp (8 * u ^ 2) := harith

/-- **The general form of `Sbig_approx` (HB (1992) §11, (11.10) plus the tail) at an abstract
scale.**  `L ≥ log 2`, `U = e^{uL}` with `u > 0`, `1 < W ≤ U ≤ V`, `|Re ρ| ≤ 1`:
`‖Σ_n Ψ(n)Θ(n)χ(n)n^{-ρ}e^{-nL²/U} - e^{-L²/U}‖ ≤ 10⁶ e^{8u²}/L`. -/
private theorem Sbig_approx_gen (u : ℝ) (hu : 0 < u) :
    ∀ (q : ℕ) [NeZero q] (L : ℝ), Real.log 2 ≤ L →
      ∀ (U V W : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ),
        1 < W → W ≤ U → U ≤ V → U = Real.exp (u * L) → |ρ.re| ≤ 1 →
        ‖Work.LinnikAreas.Density4.Sbig q U V W L χ ρ
            - ((Real.exp (-(L ^ 2 / U)) : ℝ) : ℂ)‖
          ≤ 1000000 * Real.exp (8 * u^2) / L := by
  intro q _inst L hL2 U V W χ ρ hW1 hWU hUV hUexp hre
  set a : ℝ := L^2/U with hadef
  have hL : 0 < L := lt_of_lt_of_le (Real.log_pos (by norm_num)) hL2
  have hU1 : 1 < U := by
    rw [hUexp]
    exact Real.one_lt_exp_iff.mpr (by positivity)
  have hUpos : 0 < U := lt_trans zero_lt_one hU1
  have ha : 0 < a := by rw [hadef]; exact div_pos (pow_pos hL 2) hUpos
  -- the summand
  set F : ℕ → ℂ := fun n => detCoeff q U V W χ ρ n * ((Real.exp (-(n:ℝ)*a) : ℝ) : ℂ) with hFdef
  have hSbig : Sbig q U V W L χ ρ = ∑' n, F n := by
    rw [Sbig, hFdef]
    apply tsum_congr
    intro n
    congr 2
    rw [hadef]; ring_nf
  have hF0 : F 0 = 0 := by
    simp only [hFdef, detCoeff, Nat.cast_zero]
    simp [psiS_zero]
  have hF1 : F 1 = ((Real.exp (-a) : ℝ) : ℂ) := by
    simp only [hFdef, detCoeff, Nat.cast_one, psiS_one (le_of_lt hU1), thetaS_one hW1,
      Complex.ofReal_one, one_cpow, map_one, mul_one]
    ring_nf
  have hFzero : ∀ n : ℕ, 2 ≤ n → (n:ℝ) ≤ U → F n = 0 := by
    intro n hn hnU
    have hp : psiS U V n = 0 := psiM_divisor_sum_zero (le_of_lt hU1) hUV hn hnU
    simp only [hFdef, detCoeff, hp, Complex.ofReal_zero, zero_mul]
  have hsumm : Summable F := by
    simp only [hFdef]
    exact summable_detCoeff_mul_exp (q := q) U V W χ ρ hUpos ha
  -- the integer cut-off
  set N : ℕ := Nat.floor U + 1 with hNdef
  have hN1 : 1 < N := by
    rw [hNdef]
    have : 1 ≤ Nat.floor U := Nat.le_floor (by push_cast; exact le_of_lt hU1)
    omega
  have hNU : U < (N:ℝ) := by
    rw [hNdef]
    have := Nat.lt_floor_add_one U
    push_cast
    linarith
  have hNle : (N:ℝ) ≤ U + 1 := by
    rw [hNdef]
    have := Nat.floor_le (a := U) hUpos.le
    push_cast
    linarith
  have hN0 : (0:ℝ) ≤ (N:ℝ) := by positivity
  have hsumN : (∑ i ∈ Finset.range N, F i) = ((Real.exp (-a) : ℝ) : ℂ) := by
    rw [Finset.sum_eq_single (1 : ℕ)]
    · exact hF1
    · intro b hb hb1
      rw [Finset.mem_range] at hb
      have hbN : b ≤ Nat.floor U := by rw [hNdef] at hb; omega
      have hbU : (b:ℝ) ≤ U := by
        have h1 : (b:ℝ) ≤ ((Nat.floor U : ℕ) : ℝ) := by exact_mod_cast hbN
        have h2 : ((Nat.floor U : ℕ) : ℝ) ≤ U := Nat.floor_le (a := U) hUpos.le
        linarith
      rcases Nat.eq_zero_or_pos b with h0 | h0
      · subst h0; exact hF0
      · exact hFzero b (by omega) hbU
    · intro h1not
      exact absurd (Finset.mem_range.mpr hN1) h1not
  have hsplit : (∑' n, F n) = ((Real.exp (-a) : ℝ) : ℂ) + ∑' k, F (k + N) := by
    have h := hsumm.sum_add_tsum_nat_add N
    rw [hsumN] at h
    rw [← h]
  have hmain : ‖Sbig q U V W L χ ρ - ((Real.exp (-(L^2/U)) : ℝ) : ℂ)‖ = ‖∑' k, F (k + N)‖ := by
    have he : (Real.exp (-(L^2/U)) : ℝ) = Real.exp (-a) := by rw [hadef]
    rw [he, hSbig, hsplit]
    rw [add_sub_cancel_left]
  -- summability and termwise bounds
  have htail_sum : Summable (fun k : ℕ => F (k + N)) := (summable_nat_add_iff N).mpr hsumm
  have hnorm : ‖∑' k, F (k + N)‖ ≤ ∑' k, ‖F (k + N)‖ := norm_tsum_le_tsum_norm htail_sum.norm
  have hpt : ∀ k : ℕ, ‖F (k + N)‖ ≤ (((k:ℝ) + (N:ℝ))^3) * Real.exp (-(a * ((k:ℝ) + (N:ℝ)))) := by
    intro k
    have hbase : (((k+N : ℕ):ℝ)) = (k:ℝ) + (N:ℝ) := by push_cast; ring
    have h1 : ‖F (k + N)‖ ≤ (((k:ℝ) + (N:ℝ))^3) * Real.exp (-(((k:ℝ) + (N:ℝ)) * a)) := by
      have hnorm' : ‖F (k + N)‖
          = ‖detCoeff q U V W χ ρ (k + N)‖ * Real.exp (-(((k:ℝ) + (N:ℝ)) * a)) := by
        rw [hFdef]
        simp only
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        rw [show -↑(k+N) * a = -(((k:ℝ) + (N:ℝ)) * a) by rw [hbase]; ring]
      rw [hnorm']
      have hc := detCoeff_norm_le_cube (U := U) (V := V) (W := W) hUpos χ hre (k+N)
      rw [hbase] at hc
      exact mul_le_mul_of_nonneg_right hc (Real.exp_pos _).le
    calc ‖F (k + N)‖ ≤ (((k:ℝ) + (N:ℝ))^3) * Real.exp (-(((k:ℝ) + (N:ℝ)) * a)) := h1
      _ = (((k:ℝ) + (N:ℝ))^3) * Real.exp (-(a * ((k:ℝ) + (N:ℝ)))) := by
          rw [show -(((k:ℝ) + (N:ℝ)) * a) = -(a * ((k:ℝ) + (N:ℝ))) by ring]
  have hmaj : Summable (fun k : ℕ => (((k:ℝ) + (N:ℝ))^3) * Real.exp (-(a * ((k:ℝ) + (N:ℝ))))) :=
    summable_cube_exp ha hN0
  have hle1 : (∑' k : ℕ, ‖F (k + N)‖)
      ≤ ∑' k : ℕ, (((k:ℝ) + (N:ℝ))^3) * Real.exp (-(a * ((k:ℝ) + (N:ℝ)))) :=
    Summable.tsum_le_tsum hpt htail_sum.norm hmaj
  have hcub := cube_exp_tsum_bound_aux (a := a) (c := (N:ℝ)) ha hN0
  have hle2 : (∑' k : ℕ, (((k:ℝ) + (N:ℝ))^3) * Real.exp (-(a * ((k:ℝ) + (N:ℝ)))))
      ≤ Real.exp (-(a * (N:ℝ))) * ((1 + 1/a) * (N:ℝ)^3
          + (6*(N:ℝ)^2/a + 24*(N:ℝ)/a^2 + 48/a^3) * (1 + 2/a)) := hcub
  have hle3 : Real.exp (-(a * (N:ℝ))) * ((1 + 1/a) * (N:ℝ)^3
      + (6*(N:ℝ)^2/a + 24*(N:ℝ)/a^2 + 48/a^3) * (1 + 2/a))
      ≤ 1000000 * Real.exp (8*u^2) / L :=
    tail_majorant_le_aux (u := u) (L := L) (U := U) (a := a) (c := (N:ℝ))
      hu hL2 hUexp hadef (le_of_lt hNU) hNle
  calc ‖Sbig q U V W L χ ρ - ((Real.exp (-(L^2/U)) : ℝ) : ℂ)‖
      = ‖∑' k : ℕ, F (k + N)‖ := hmain
    _ ≤ ∑' k : ℕ, ‖F (k + N)‖ := hnorm
    _ ≤ ∑' k : ℕ, (((k:ℝ) + (N:ℝ))^3) * Real.exp (-(a * ((k:ℝ) + (N:ℝ)))) := hle1
    _ ≤ Real.exp (-(a * (N:ℝ))) * ((1 + 1/a) * (N:ℝ)^3
          + (6*(N:ℝ)^2/a + 24*(N:ℝ)/a^2 + 48/a^3) * (1 + 2/a)) := hle2
    _ ≤ 1000000 * Real.exp (8*u^2) / L := hle3

/-- HB (1992) §11 (11.10) at the scale `𝓓 = q(T+2)`: the second smoothed sum
`Sbig = Σ_n Ψ(n)Θ(n)χ(n)n^{-ρ}e^{-nL²/U}` (mollifiers of HB (11.6),(11.7), `L = log 𝓓`,
`U = 𝓓^u`) differs from `e^{-L²/U}` by at most `C/L`, uniformly in `q ≥ 2`, `T ≥ 1`, the
non-principal character, and every `ρ` with `|Re ρ| ≤ 1`.

This is `Work.LinnikAreas.Density4.Sbig_approx` with the scale `q` replaced by `𝓓 = q(T+2)`:
the proof only uses `L = log 𝓓 ≥ log 2`, `U = 𝓓^u = e^{uL}`, `1 < W ≤ U ≤ V`, `|Re ρ| ≤ 1`,
`Σ_{d|n} ψ_d = 0` for `2 ≤ n ≤ U` (`psiM_divisor_sum_zero`), `‖detCoeff n‖ ≤ n³`
(`detCoeff_norm_le_cube`) and the arithmetic closure `arith_bound`; all of these are available
verbatim, with `q` replaced by `𝓓` throughout. -/
theorem Sbig_approx_D (u : ℝ) (hu : 0 < u) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (T : ℝ), 2 ≤ q → 1 ≤ T →
        ∀ (V W : ℝ) (χ : DirichletCharacter ℂ q) (ρ : ℂ),
          1 < W → W ≤ Work.ZeroDensity.LogFree.Dpow q T u →
          Work.ZeroDensity.LogFree.Dpow q T u ≤ V → |ρ.re| ≤ 1 →
          ‖Work.LinnikAreas.Density4.Sbig q (Work.ZeroDensity.LogFree.Dpow q T u) V W
              (Work.ZeroDensity.LogFree.Lscale q T) χ ρ
            - ((Real.exp (-((Work.ZeroDensity.LogFree.Lscale q T) ^ 2 /
                Work.ZeroDensity.LogFree.Dpow q T u)) : ℝ) : ℂ)‖
            ≤ C / Work.ZeroDensity.LogFree.Lscale q T := by
  refine ⟨1000000 * Real.exp (8*u^2) + 1, by positivity, ?_⟩
  intro q _inst T hq hT V W χ ρ hW1 hWU hUV hre
  set L : ℝ := Lscale q T with hLdef
  set U : ℝ := Dpow q T u with hUdef
  have hscale2 : (2:ℝ) ≤ scale q T := by
    have hqR : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    have hT2 : (3:ℝ) ≤ T + 2 := by linarith
    rw [scale]
    nlinarith
  have hscale_pos : 0 < scale q T := by linarith
  have hL2 : Real.log 2 ≤ L := by
    rw [hLdef, Lscale]
    exact Real.log_le_log (by norm_num) hscale2
  have hLpos : 0 < L := lt_of_lt_of_le (Real.log_pos (by norm_num)) hL2
  have hUexp : U = Real.exp (u * L) := by
    rw [hUdef, Dpow, hLdef, Lscale, Real.rpow_def_of_pos hscale_pos]
    congr 1; ring
  have hgen := Sbig_approx_gen u hu q L hL2 U V W χ ρ hW1 hWU hUV hUexp hre
  refine hgen.trans ?_
  apply div_le_div_of_nonneg_right (by linarith [Real.exp_pos (8*u^2)]) hLpos.le

end Work.ZeroDensity.LogFree
