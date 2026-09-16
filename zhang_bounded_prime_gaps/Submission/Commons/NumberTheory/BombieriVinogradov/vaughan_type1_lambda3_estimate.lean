import Mathlib
import Submission.Commons.NumberTheory.ArithmeticFunction.vaughan_coefficient_bound
import Submission.Commons.NumberTheory.DirichletCharacter.charSum_range_le_polyaVinogradov

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.BombieriVinogradov

open scoped BigOperators

/-- The inner character sum `Σ_{r ≤ m} χ(r)`, truncated at an arbitrary natural `m ≥ 0`
(so that the truncation `y / t` may be `0`), is bounded by the Pólya–Vinogradov bound. -/
private lemma l3_charSum_le (C : ℝ) (hC0 : 0 ≤ C)
    (hPV : ∀ (q : ℕ), 2 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ a b : ℕ, a ≤ b →
      ‖∑ n ∈ Finset.Icc a b, χ (n : ZMod q)‖ ≤ C * Real.sqrt q * Real.log (2 * (q : ℝ) + 2))
    (q : ℕ) (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (m : ℕ) :
    ‖∑ r ∈ Finset.Icc 1 m, χ (r : ZMod q)‖ ≤ C * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    rw [Finset.Icc_eq_empty_iff.mpr (by omega : ¬ (1:ℕ) ≤ 0), Finset.sum_empty, norm_zero]
    have h1 : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
    have h2 : 0 ≤ Real.log (2 * (q : ℝ) + 2) := by
      apply Real.log_nonneg
      have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
      linarith
    exact mul_nonneg (mul_nonneg hC0 h1) h2
  · exact hPV q hq χ hχ 1 m hm

/-- Pointwise (in `y`, uniformly) bound for the `λ₃` piece at a non-principal character. -/
private lemma l3_pointwise_ge2 (C : ℝ) (hC0 : 0 ≤ C)
    (hPV : ∀ (q : ℕ), 2 ≤ q → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ a b : ℕ, a ≤ b →
      ‖∑ n ∈ Finset.Icc a b, χ (n : ZMod q)‖ ≤ C * Real.sqrt q * Real.log (2 * (q : ℝ) + 2))
    {T : ℕ} (hT : 1 ≤ T) (a : ℕ → ℂ)
    (ha : ∀ t ∈ Finset.Icc 1 T, ‖a t‖ ≤ Real.log (T : ℝ))
    (q : ℕ) (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (y : ℕ) :
    ‖∑ t ∈ Finset.Icc 1 T, a t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))‖
      ≤ (T : ℝ) * Real.log (T : ℝ) * (C * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)) := by
  have hlogT_nn : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by exact_mod_cast hT)
  have hBnn : 0 ≤ C * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) := by
    have h1 : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
    have h2 : 0 ≤ Real.log (2 * (q : ℝ) + 2) := by
      apply Real.log_nonneg
      have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
      linarith
    exact mul_nonneg (mul_nonneg hC0 h1) h2
  have hinner : ∀ t : ℕ,
      ‖∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q)‖ ≤ C * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) :=
    fun t => l3_charSum_le C hC0 hPV q hq χ hχ (y / t)
  calc ‖∑ t ∈ Finset.Icc 1 T, a t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))‖
      ≤ ∑ t ∈ Finset.Icc 1 T, ‖a t * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ t ∈ Finset.Icc 1 T, Real.log (T : ℝ) * (C * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)) := by
        apply Finset.sum_le_sum
        intro t ht
        rw [norm_mul, norm_mul]
        have h1 : ‖a t‖ ≤ Real.log (T : ℝ) := ha t ht
        have h2 : ‖χ (t : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
        have h3 : ‖∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q)‖ ≤
            C * Real.sqrt q * Real.log (2 * (q : ℝ) + 2) := hinner t
        calc ‖a t‖ * ‖χ (t : ZMod q)‖ * ‖∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q)‖
            ≤ Real.log (T : ℝ) * 1 * (C * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)) :=
              mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hlogT_nn) h3 (norm_nonneg _)
                (mul_nonneg hlogT_nn zero_le_one)
          _ = Real.log (T : ℝ) * (C * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)) := by ring
    _ = (T : ℝ) * (Real.log (T : ℝ) * (C * Real.sqrt q * Real.log (2 * (q : ℝ) + 2))) := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    _ = (T : ℝ) * Real.log (T : ℝ) * (C * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)) := by ring

/-- Pointwise (in `y ≤ x`) bound for the `λ₃` piece at a level-`1` (principal) character,
using the trivial bound on the inner character sum and the harmonic sum bound. -/
private lemma l3_pointwise_one {T x : ℕ} (hT : 1 ≤ T) (a : ℕ → ℂ)
    (ha : ∀ t ∈ Finset.Icc 1 T, ‖a t‖ ≤ Real.log (T : ℝ))
    (χ : DirichletCharacter ℂ 1) (y : ℕ) (hy : y ≤ x) :
    ‖∑ t ∈ Finset.Icc 1 T, a t * χ (t : ZMod 1) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod 1))‖
      ≤ (x : ℝ) * Real.log (T : ℝ) * (1 + Real.log (T : ℝ)) := by
  have hlogT_nn : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by exact_mod_cast hT)
  have hinner : ∀ t : ℕ, ‖∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod 1)‖ ≤ ((y / t : ℕ) : ℝ) := by
    intro t
    calc ‖∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod 1)‖
        ≤ ∑ r ∈ Finset.Icc 1 (y / t), ‖χ (r : ZMod 1)‖ := norm_sum_le _ _
      _ ≤ ∑ r ∈ Finset.Icc 1 (y / t), (1 : ℝ) :=
          Finset.sum_le_sum (fun r _ => DirichletCharacter.norm_le_one χ _)
      _ = ((y / t : ℕ) : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, mul_one]
  have hsum : ∑ t ∈ Finset.Icc 1 T, ((t : ℝ))⁻¹ ≤ 1 + Real.log (T : ℝ) := by
    have h2 : (harmonic T : ℝ) = ∑ t ∈ Finset.Icc 1 T, ((t : ℝ))⁻¹ := by
      rw [harmonic_eq_sum_Icc]; push_cast; ring
    have h1 : (harmonic T : ℝ) ≤ 1 + Real.log (T : ℝ) := harmonic_le_one_add_log T
    linarith
  have hyx : (y : ℝ) ≤ (x : ℝ) := by exact_mod_cast hy
  calc ‖∑ t ∈ Finset.Icc 1 T, a t * χ (t : ZMod 1) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod 1))‖
      ≤ ∑ t ∈ Finset.Icc 1 T,
          ‖a t * χ (t : ZMod 1) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod 1))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ t ∈ Finset.Icc 1 T, Real.log (T : ℝ) * ((y : ℝ) * (t : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro t ht
        rw [norm_mul, norm_mul]
        have h1 : ‖a t‖ ≤ Real.log (T : ℝ) := ha t ht
        have h2 : ‖χ (t : ZMod 1)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
        have h3 : ‖∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod 1)‖ ≤ ((y / t : ℕ) : ℝ) := hinner t
        have h4 : ((y / t : ℕ) : ℝ) ≤ (y : ℝ) * (t : ℝ)⁻¹ := by
          calc ((y / t : ℕ) : ℝ) ≤ (y : ℝ) / (t : ℝ) := Nat.cast_div_le
            _ = (y : ℝ) * (t : ℝ)⁻¹ := by rw [div_eq_mul_inv]
        calc ‖a t‖ * ‖χ (t : ZMod 1)‖ * ‖∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod 1)‖
            ≤ Real.log (T : ℝ) * 1 * ((y / t : ℕ) : ℝ) :=
              mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) hlogT_nn) h3 (norm_nonneg _)
                (mul_nonneg hlogT_nn zero_le_one)
          _ ≤ Real.log (T : ℝ) * 1 * ((y : ℝ) * (t : ℝ)⁻¹) :=
              mul_le_mul_of_nonneg_left h4 (mul_nonneg hlogT_nn zero_le_one)
          _ = Real.log (T : ℝ) * ((y : ℝ) * (t : ℝ)⁻¹) := by ring
    _ = Real.log (T : ℝ) * ((y : ℝ) * ∑ t ∈ Finset.Icc 1 T, ((t : ℝ))⁻¹) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ ≤ Real.log (T : ℝ) * ((x : ℝ) * (1 + Real.log (T : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ hlogT_nn
        exact mul_le_mul hyx hsum (by positivity) (by positivity)
    _ = (x : ℝ) * Real.log (T : ℝ) * (1 + Real.log (T : ℝ)) := by ring

/-- The Vaughan coefficient of the `λ₃` piece, restricted to `t ≤ T`, is bounded by `log T`. -/
private lemma l3_coef_le (T t : ℕ) (ht : t ∈ Finset.Icc 1 T) :
    ‖∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
        ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ)
          * ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ)‖ ≤ Real.log (T : ℝ) := by
  have h := Commons.NumberTheory.ArithmeticFunction.vaughan_coefficient_bound T T t
  have heq : (∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
        ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ)
          * ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ))
      = (∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
        ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ)
          * ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ)) := by
    apply Finset.sum_congr rfl
    intro kl _
    ring
  rw [heq]
  have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
  have htT : t ≤ T := (Finset.mem_Icc.mp ht).2
  have hlogt : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg (by exact_mod_cast ht1)
  rw [max_eq_right hlogt] at h
  refine h.trans ?_
  have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast (by omega : 0 < t)
  have htT' : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast htT
  exact Real.log_le_log htpos htT'

/-- The primitive Dirichlet characters modulo `q`, as a finite set. -/
private noncomputable def prims (q : ℕ) : Finset (DirichletCharacter ℂ q) :=
  @Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive) (Classical.decPred _) Finset.univ

private lemma mem_prims {q : ℕ} {χ : DirichletCharacter ℂ q} : χ ∈ prims q ↔ χ.IsPrimitive := by
  simp [prims]

/-- The number of primitive characters modulo `q` is at most `q.totient`. -/
private lemma l3_prim_card_le (q : ℕ) (hq : 1 ≤ q) : (((prims q).card : ℕ) : ℝ) ≤ (q.totient : ℝ) := by
  classical
  have hnez : NeZero q := ⟨by omega⟩
  have hle := Finset.card_filter_le (Finset.univ : Finset (DirichletCharacter ℂ q))
      (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
  have hc : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have : (Finset.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive) Finset.univ).card
      ≤ q.totient := le_trans hle (le_of_eq hc)
  simpa only [prims] using (show (((Finset.filter (fun χ : DirichletCharacter ℂ q => χ.IsPrimitive)
      Finset.univ).card : ℕ) : ℝ) ≤ (q.totient : ℝ) by exact_mod_cast this)

/-- The supremum defining the `λ₃` piece of Vaughan's decomposition. -/
private noncomputable def l3sup (T x q : ℕ) (χ : DirichletCharacter ℂ q) : ℝ :=
  sSup ((fun y : ℕ => ‖∑ t ∈ Finset.Icc 1 T,
      (∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
        ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
          ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ))
      * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))‖) '' Set.Icc 1 x)

/-- **Type I estimate for the small `t`-part of the `λ₃` piece of Vaughan's decomposition**
(piece `S₃'` of Vaughan's mean value theorem, Akbary--Hambrook (6.12)): with
`a_t = Σ_{d e = t, d,e ≤ T} μ d · Λ e` (so `|a_t| ≤ log t`), `2 ≤ Q`, `1 ≤ T ≤ x`, the
totient-weighted average over primitive characters of `sup_{y≤x} ‖Σ_{t≤T} a_t χ(t) Σ_{r≤y/t} χ(r)‖`
is `≪ (x + T Q^{5/2}) log³(xQ)`.

Method: `|a_t| ≤ log t ≤ log T`
(`Commons.NumberTheory.ArithmeticFunction.vaughan_coefficient_bound`), then bound the inner
interval character sums by `Commons.NumberTheory.DirichletCharacter.charSum_range_le_polyaVinogradov`
uniformly in the truncation, and sum `√q log q` over `q ≤ Q` (the trivial character `q = 1`
contributing `≪ x log² x`).
-/
theorem vaughan_type1_lambda3_estimate :
    ∃ C : ℝ, 0 < C ∧ ∀ x Q T : ℕ, 2 ≤ x → 2 ≤ Q → 1 ≤ T → T ≤ x →
      (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ (@Finset.filter (DirichletCharacter ℂ q) (fun χ => χ.IsPrimitive)
                (Classical.decPred _) Finset.univ),
          sSup ((fun y : ℕ => ‖∑ t ∈ Finset.Icc 1 T,
              (∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
                ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
                  ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ))
              * χ (t : ZMod q) * (∑ r ∈ Finset.Icc 1 (y / t), χ (r : ZMod q))‖) '' Set.Icc 1 x))
      ≤ C * ((x : ℝ) + (T : ℝ) * (Q : ℝ) ^ (5 / 2 : ℝ))
          * (Real.log ((x : ℝ) * (Q : ℝ) + 2)) ^ 3 := by
  classical
  obtain ⟨Cpv, hCpvpos, hCpv⟩ :=
    Commons.NumberTheory.DirichletCharacter.charSum_range_le_polyaVinogradov
  refine ⟨5 + 5 * Cpv, by positivity, ?_⟩
  intro x Q T hx hQ hT hTx
  set L : ℝ := Real.log ((x : ℝ) * (Q : ℝ) + 2) with hLdef
  have hx1 : 1 ≤ x := by omega
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast (by omega : 1 ≤ Q)
  have hQnn : (0 : ℝ) ≤ (Q : ℝ) := by positivity
  have hxnn : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hQ2 : (2 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hTnn : (0 : ℝ) ≤ (T : ℝ) := by positivity
  have h6 : (6 : ℝ) ≤ (x : ℝ) * (Q : ℝ) + 2 := by
    have hx2 : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
    have hmul : (2 : ℝ) * 2 ≤ (x : ℝ) * (Q : ℝ) := mul_le_mul hx2 hQ2 (by norm_num) hxnn
    linarith
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by positivity : (0:ℝ) < (x:ℝ)*(Q:ℝ)+2)]
    have : Real.exp 1 < 6 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    linarith
  have hLnn : 0 ≤ L := le_of_lt (lt_of_lt_of_le zero_lt_one hL1)
  have hlogT_le_L : Real.log (T : ℝ) ≤ L := by
    rw [hLdef]
    apply Real.log_le_log (by positivity : (0:ℝ) < (T:ℝ))
    have hTx' : (T : ℝ) ≤ (x : ℝ) := by exact_mod_cast hTx
    have hxle : (x : ℝ) ≤ (x : ℝ) * (Q : ℝ) + 2 := by
      have hm : (x : ℝ) * 1 ≤ (x : ℝ) * (Q : ℝ) := mul_le_mul_of_nonneg_left hQ1 hxnn
      linarith
    linarith
  have ha : ∀ t ∈ Finset.Icc 1 T,
      ‖∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
        ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
          ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ)‖ ≤ Real.log (T : ℝ) :=
    fun t ht => l3_coef_le T t ht
  change (∑ q ∈ Finset.Icc 1 Q, ((q : ℝ) / (q.totient : ℝ)) *
        ∑ χ ∈ prims q, l3sup T x q χ)
      ≤ (5 + 5 * Cpv) * ((x : ℝ) + (T : ℝ) * (Q : ℝ) ^ (5 / 2 : ℝ)) * L ^ 3
  have hsup_ge2 : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q), 2 ≤ q → χ.IsPrimitive →
      l3sup T x q χ ≤
        (T : ℝ) * Real.log (T : ℝ) * (Cpv * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)) := by
    intro q χ hq hprim
    rw [l3sup]
    haveI : NeZero q := ⟨by omega⟩
    have hχ1 : χ ≠ 1 := by
      intro h
      have hc : χ.conductor = q := (DirichletCharacter.isPrimitive_def χ).mp hprim
      rw [h, DirichletCharacter.conductor_one] at hc
      omega
    apply csSup_le
    · exact ⟨_, ⟨1, ⟨le_rfl, hx1⟩, rfl⟩⟩
    · rintro b ⟨y, _hy, rfl⟩
      exact l3_pointwise_ge2 Cpv (le_of_lt hCpvpos) hCpv hT
        (fun t => ∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
          ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
            ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ))
        ha q hq χ hχ1 y
  have hsup_one : ∀ χ : DirichletCharacter ℂ 1,
      l3sup T x 1 χ ≤ (x : ℝ) * Real.log (T : ℝ) * (1 + Real.log (T : ℝ)) := by
    intro χ
    rw [l3sup]
    apply csSup_le
    · exact ⟨_, ⟨1, ⟨le_rfl, hx1⟩, rfl⟩⟩
    · rintro b ⟨y, hy, rfl⟩
      exact l3_pointwise_one hT
        (fun t => ∑ kl ∈ (Finset.Icc 1 T ×ˢ Finset.Icc 1 T).filter (fun kl => kl.1 * kl.2 = t),
          ((ArithmeticFunction.moebius kl.2 : ℤ) : ℂ) *
            ((ArithmeticFunction.vonMangoldt kl.1 : ℝ) : ℂ))
        ha χ y hy.2
  have hF1 : (((1:ℕ) : ℝ) / ((1:ℕ).totient : ℝ)) * (∑ χ ∈ prims 1, l3sup T x 1 χ)
      ≤ 2 * (x : ℝ) * L ^ 2 := by
    rw [show (((1:ℕ) : ℝ) / ((1:ℕ).totient : ℝ)) = 1 by rw [Nat.totient_one]; norm_num, one_mul]
    have hlogTnn : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by exact_mod_cast hT)
    have hB1nn : 0 ≤ (x : ℝ) * Real.log (T : ℝ) * (1 + Real.log (T : ℝ)) := by positivity
    have hcard1 : (((prims 1).card : ℕ) : ℝ) ≤ 1 := by
      simpa [Nat.totient_one] using l3_prim_card_le 1 (le_refl 1)
    have h1log : 0 ≤ 1 + Real.log (T : ℝ) := by linarith
    calc (∑ χ ∈ prims 1, l3sup T x 1 χ)
        ≤ (prims 1).card • ((x : ℝ) * Real.log (T : ℝ) * (1 + Real.log (T : ℝ))) :=
          Finset.sum_le_card_nsmul (prims 1) (fun χ => l3sup T x 1 χ) _
            (fun χ _ => hsup_one χ)
      _ = ((prims 1).card : ℝ) * ((x : ℝ) * Real.log (T : ℝ) * (1 + Real.log (T : ℝ))) := by
          rw [nsmul_eq_mul]
      _ ≤ 1 * ((x : ℝ) * Real.log (T : ℝ) * (1 + Real.log (T : ℝ))) :=
          mul_le_mul_of_nonneg_right hcard1 hB1nn
      _ = (x : ℝ) * Real.log (T : ℝ) * (1 + Real.log (T : ℝ)) := one_mul _
      _ ≤ 2 * (x : ℝ) * L ^ 2 := by
          have hone : 1 + Real.log (T : ℝ) ≤ 2 * L := by linarith
          calc (x : ℝ) * Real.log (T : ℝ) * (1 + Real.log (T : ℝ))
              ≤ (x : ℝ) * L * (1 + Real.log (T : ℝ)) :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlogT_le_L hxnn) h1log
            _ ≤ (x : ℝ) * L * (2 * L) := mul_le_mul_of_nonneg_left hone (mul_nonneg hxnn hLnn)
            _ = 2 * (x : ℝ) * L ^ 2 := by ring
  have hQ32 : (Q : ℝ) * Real.sqrt (Q : ℝ) = (Q : ℝ) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    have h := Real.rpow_add (show (0:ℝ) < (Q:ℝ) by positivity) (1:ℝ) (1/2:ℝ)
    simp only [Real.rpow_one, show (1:ℝ) + 1/2 = 3/2 by norm_num] at h
    exact h.symm
  have hQpow : (Q : ℝ) ^ (5 / 2 : ℝ) = (Q : ℝ) ^ (3 / 2 : ℝ) * (Q : ℝ) := by
    have h := Real.rpow_add (show (0:ℝ) < (Q:ℝ) by positivity) (3/2:ℝ) (1:ℝ)
    simp only [Real.rpow_one, show (3:ℝ)/2 + 1 = 5/2 by norm_num] at h
    exact h
  have hF2 : (∑ q ∈ Finset.Icc 2 Q, ((q : ℝ) / (q.totient : ℝ)) *
        (∑ χ ∈ prims q, l3sup T x q χ)) ≤
      Cpv * (T : ℝ) * (Q : ℝ) ^ (5 / 2 : ℝ) * L ^ 2 := by
    have hBnn : 0 ≤ Cpv * (T : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) * L ^ 2 := by
      have h1 : 0 ≤ (Q : ℝ) ^ (3/2 : ℝ) := Real.rpow_nonneg hQnn _
      positivity
    calc (∑ q ∈ Finset.Icc 2 Q, ((q : ℝ) / (q.totient : ℝ)) * (∑ χ ∈ prims q, l3sup T x q χ))
        ≤ ∑ q ∈ Finset.Icc 2 Q, Cpv * (T : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) * L ^ 2 := by
          apply Finset.sum_le_sum
          intro q hq
          have hq2 : 2 ≤ q := (Finset.mem_Icc.mp hq).1
          have hqQ : q ≤ Q := (Finset.mem_Icc.mp hq).2
          have hqnn : (0:ℝ) ≤ (q:ℝ) := by positivity
          have hφpos : (0 : ℝ) < (q.totient : ℝ) := by
            have : 0 < q.totient := Nat.totient_pos.mpr (by omega)
            exact_mod_cast this
          have hlogTnn : 0 ≤ Real.log (T : ℝ) := Real.log_nonneg (by exact_mod_cast hT)
          have hBqnn : 0 ≤ (T : ℝ) * Real.log (T : ℝ) *
              (Cpv * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)) := by
            have h2 : 0 ≤ Real.sqrt (q:ℝ) := Real.sqrt_nonneg _
            have h3 : 0 ≤ Real.log (2*(q:ℝ)+2) := by
              apply Real.log_nonneg
              have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq2
              linarith
            positivity
          have hcardq : (((prims q).card : ℕ) : ℝ) ≤ (q.totient : ℝ) := l3_prim_card_le q (by omega)
          have hinner : (∑ χ ∈ prims q, l3sup T x q χ) ≤ (q.totient : ℝ) *
              ((T : ℝ) * Real.log (T : ℝ) * (Cpv * Real.sqrt q * Real.log (2*(q:ℝ)+2))) := by
            calc (∑ χ ∈ prims q, l3sup T x q χ)
                ≤ (prims q).card • ((T : ℝ) * Real.log (T : ℝ) *
                    (Cpv * Real.sqrt q * Real.log (2*(q:ℝ)+2))) :=
                  Finset.sum_le_card_nsmul (prims q) (fun χ => l3sup T x q χ) _
                    (fun χ hχ => hsup_ge2 q χ hq2 (mem_prims.mp hχ))
              _ = ((prims q).card : ℝ) * ((T : ℝ) * Real.log (T : ℝ) *
                    (Cpv * Real.sqrt q * Real.log (2*(q:ℝ)+2))) := by rw [nsmul_eq_mul]
              _ ≤ (q.totient : ℝ) * ((T : ℝ) * Real.log (T : ℝ) *
                    (Cpv * Real.sqrt q * Real.log (2*(q:ℝ)+2))) :=
                  mul_le_mul_of_nonneg_right hcardq hBqnn
          have hdivnn : 0 ≤ (q : ℝ) / (q.totient : ℝ) := div_nonneg hqnn (le_of_lt hφpos)
          calc ((q : ℝ) / (q.totient : ℝ)) * (∑ χ ∈ prims q, l3sup T x q χ)
              ≤ ((q : ℝ) / (q.totient : ℝ)) * ((q.totient : ℝ) *
                  ((T : ℝ) * Real.log (T : ℝ) *
                    (Cpv * Real.sqrt q * Real.log (2*(q:ℝ)+2)))) :=
                  mul_le_mul_of_nonneg_left hinner hdivnn
            _ = (q : ℝ) * ((T : ℝ) * Real.log (T : ℝ) *
                  (Cpv * Real.sqrt q * Real.log (2*(q:ℝ)+2))) := by
                  rw [← mul_assoc, div_mul_cancel₀ (q:ℝ) (ne_of_gt hφpos)]
            _ ≤ Cpv * (T : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) * L ^ 2 := by
                  have hqle : (q : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hqQ
                  have hsqrts : Real.sqrt (q : ℝ) ≤ Real.sqrt (Q : ℝ) := Real.sqrt_le_sqrt hqle
                  have hlogqL : Real.log (2 * (q : ℝ) + 2) ≤ L := by
                    rw [hLdef]
                    apply Real.log_le_log (by positivity)
                    have h1 : (2:ℝ) * (q:ℝ) ≤ (2:ℝ) * (Q:ℝ) :=
                      mul_le_mul_of_nonneg_left hqle (by norm_num)
                    have hx2 : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx
                    have h2 : (2:ℝ) * (Q:ℝ) ≤ (x:ℝ) * (Q:ℝ) :=
                      mul_le_mul_of_nonneg_right hx2 hQnn
                    linarith
                  have hq32le : (q : ℝ) * Real.sqrt (q:ℝ) ≤ (Q:ℝ) * Real.sqrt (Q:ℝ) :=
                    mul_le_mul hqle hsqrts (Real.sqrt_nonneg _) hQnn
                  have hlogqnn : 0 ≤ Real.log (2*(q:ℝ)+2) := by
                    apply Real.log_nonneg
                    have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq2
                    linarith
                  have hprod : Cpv * (T:ℝ) * Real.log (T:ℝ) * ((q:ℝ) * Real.sqrt (q:ℝ))
                        * Real.log (2*(q:ℝ)+2)
                      ≤ Cpv * (T:ℝ) * L * ((Q:ℝ) * Real.sqrt (Q:ℝ)) * L := by
                    have h_a : Cpv * (T:ℝ) * Real.log (T:ℝ) ≤ Cpv * (T:ℝ) * L :=
                      mul_le_mul_of_nonneg_left hlogT_le_L
                        (mul_nonneg (le_of_lt hCpvpos) hTnn)
                    have hprod1 : Cpv * (T:ℝ) * Real.log (T:ℝ) * ((q:ℝ) * Real.sqrt (q:ℝ))
                        ≤ Cpv * (T:ℝ) * L * ((Q:ℝ) * Real.sqrt (Q:ℝ)) :=
                      mul_le_mul h_a hq32le (mul_nonneg hqnn (Real.sqrt_nonneg _))
                        (mul_nonneg (mul_nonneg (le_of_lt hCpvpos) hTnn) hLnn)
                    exact mul_le_mul hprod1 hlogqL hlogqnn
                      (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hCpvpos) hTnn) hLnn)
                        (mul_nonneg hQnn (Real.sqrt_nonneg _)))
                  calc (q : ℝ) * ((T : ℝ) * Real.log (T : ℝ) *
                        (Cpv * Real.sqrt q * Real.log (2 * (q : ℝ) + 2)))
                      = Cpv * (T:ℝ) * Real.log (T:ℝ) * ((q:ℝ) * Real.sqrt (q:ℝ))
                          * Real.log (2*(q:ℝ)+2) := by ring
                    _ ≤ Cpv * (T:ℝ) * L * ((Q:ℝ) * Real.sqrt (Q:ℝ)) * L := hprod
                    _ = Cpv * (T : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) * L ^ 2 := by rw [hQ32]; ring
      _ = (Finset.Icc 2 Q).card • (Cpv * (T : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) * L ^ 2) :=
          Finset.sum_const _
      _ ≤ Q • (Cpv * (T : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) * L ^ 2) := by
          apply nsmul_le_nsmul_left hBnn
          rw [Nat.card_Icc]
          omega
      _ = (Q : ℝ) * (Cpv * (T : ℝ) * (Q : ℝ) ^ (3 / 2 : ℝ) * L ^ 2) := by rw [nsmul_eq_mul]
      _ = Cpv * (T : ℝ) * (Q : ℝ) ^ (5 / 2 : ℝ) * L ^ 2 := by rw [hQpow]; ring
  rw [show Finset.Icc 1 Q = insert 1 (Finset.Icc 2 Q) by
        ext q; simp only [Finset.mem_Icc, Finset.mem_insert]; omega,
      Finset.sum_insert (by simp only [Finset.mem_Icc]; omega)]
  calc (((1:ℕ):ℝ)/((1:ℕ).totient:ℝ)) * (∑ χ ∈ prims 1, l3sup T x 1 χ)
        + ∑ q ∈ Finset.Icc 2 Q, ((q:ℝ)/(q.totient:ℝ)) * (∑ χ ∈ prims q, l3sup T x q χ)
      ≤ 2 * (x:ℝ) * L^2 + Cpv * (T:ℝ) * (Q:ℝ)^(5/2:ℝ) * L^2 := add_le_add hF1 hF2
    _ ≤ (5 + 5*Cpv) * ((x:ℝ) + (T:ℝ)*(Q:ℝ)^(5/2:ℝ)) * L^3 := by
        have hTQnn : 0 ≤ (T:ℝ) * (Q:ℝ)^(5/2:ℝ) :=
          mul_nonneg hTnn (Real.rpow_nonneg hQnn _)
        have hXnn : 0 ≤ (x:ℝ) + (T:ℝ)*(Q:ℝ)^(5/2:ℝ) := by linarith [hxnn, hTQnn]
        have hA : 2*(x:ℝ) + Cpv * ((T:ℝ) * (Q:ℝ)^(5/2:ℝ)) ≤
            (2+Cpv) * ((x:ℝ) + (T:ℝ)*(Q:ℝ)^(5/2:ℝ)) := by
          nlinarith [mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hTQnn,
            mul_nonneg (le_of_lt hCpvpos) hxnn]
        have h2 : L^2 ≤ L^3 := by
          have : L^3 = L^2 * L := by ring
          rw [this]
          exact le_mul_of_one_le_right (sq_nonneg L) hL1
        have hXcl : 0 ≤ ((2:ℝ)+Cpv) * ((x:ℝ) + (T:ℝ)*(Q:ℝ)^(5/2:ℝ)) :=
          mul_nonneg (by linarith [hCpvpos]) hXnn
        calc 2 * (x:ℝ) * L^2 + Cpv * (T:ℝ) * (Q:ℝ)^(5/2:ℝ) * L^2
            = (2*(x:ℝ) + Cpv*((T:ℝ)*(Q:ℝ)^(5/2:ℝ))) * L^2 := by ring
          _ ≤ ((2+Cpv) * ((x:ℝ) + (T:ℝ)*(Q:ℝ)^(5/2:ℝ))) * L^2 :=
              mul_le_mul_of_nonneg_right hA (sq_nonneg L)
          _ ≤ ((2+Cpv) * ((x:ℝ) + (T:ℝ)*(Q:ℝ)^(5/2:ℝ))) * L^3 :=
              mul_le_mul_of_nonneg_left h2 hXcl
          _ ≤ ((5+5*Cpv) * ((x:ℝ) + (T:ℝ)*(Q:ℝ)^(5/2:ℝ))) * L^3 :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (by linarith [hCpvpos] : (2:ℝ)+Cpv ≤ 5+5*Cpv) hXnn)
                (pow_nonneg hLnn 3)
          _ = (5 + 5*Cpv) * ((x:ℝ) + (T:ℝ)*(Q:ℝ)^(5/2:ℝ)) * L^3 := by ring

end Commons.NumberTheory.BombieriVinogradov
