import Mathlib
import Submission.Commons.Analysis.Walsh.rademacher_parseval_inner
import Submission.Commons.Analysis.Walsh.rademacher_hilbert_even_moment

namespace Work.Analysis.Variation

open Finset

noncomputable section

/-- The coercion of the real sign `±1` to `ℂ` agrees with the complex sign. -/
private lemma sign_cast (b : Bool) :
    ((if b then (1 : ℝ) else -1) : ℂ) = (if b then (1 : ℂ) else -1) := by
  cases b <;> norm_num

/-- Rademacher--Parseval identity with the complex sign convention used below. -/
private lemma parseval_sq (n : ℕ) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (x : Fin n → H) :
    (∑ e : Fin n → Bool, ‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • x i‖ ^ (2 : ℕ))
      = (2 : ℝ) ^ n * ∑ i : Fin n, ‖x i‖ ^ (2 : ℕ) := by
  simpa only [sign_cast] using Commons.Analysis.Walsh.rademacher_parseval_inner n x

/-- **Finite Paley--Zygmund, arbitrary positive exponent.**  If `W ≥ 0` on a nonempty finite type
`ι` satisfies `∑ W² = #ι * σ₂` and `∑ W⁴ ≤ C * #ι * σ₂²`, then for every `q > 0` the `q`-th
moment of `W` is at least `((4C)^{-1/q}/√2) σ₂^{1/2}`.  The threshold in the Paley--Zygmund
argument is `θ = 1/2` and the cardinality input is Cauchy--Schwarz. -/
private theorem finite_paley_zygmund_rpow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hι : 0 < Fintype.card ι) (W : ι → ℝ) (hW : ∀ i, 0 ≤ W i)
    {σ2 C : ℝ} (hσ2 : 0 ≤ σ2) (hC : 0 < C)
    (h2 : ∑ i, W i ^ (2 : ℕ) = (Fintype.card ι : ℝ) * σ2)
    (h4 : ∑ i, W i ^ (4 : ℕ) ≤ C * (Fintype.card ι : ℝ) * σ2 ^ (2 : ℕ))
    {q : ℝ} (hq : 0 < q) :
    ((4 * C) ^ (-(1 / q)) / Real.sqrt 2) * σ2 ^ ((1 : ℝ) / 2)
      ≤ ((∑ i, W i ^ q) / (Fintype.card ι : ℝ)) ^ ((1 : ℝ) / q) := by
  classical
  have hNpos : (0:ℝ) < (Fintype.card ι : ℝ) := by exact_mod_cast hι
  rcases eq_or_lt_of_le hσ2 with h0 | hpos
  · rw [← h0, Real.zero_rpow (by norm_num : ((1:ℝ)/2) ≠ 0), mul_zero]
    exact Real.rpow_nonneg
      (div_nonneg (Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hW i) q)) hNpos.le) _
  · set r : ℝ := Real.sqrt (σ2 / 2) with hr
    have hrnonneg : 0 ≤ r := by rw [hr]; exact Real.sqrt_nonneg _
    set S : Finset ι := Finset.univ.filter (fun i => σ2 / 2 ≤ W i ^ 2) with hS
    -- The complement of the "good set" carries at most half of the second moment.
    have hcompl : ∑ i ∈ Sᶜ, W i ^ 2 ≤ (Fintype.card ι : ℝ) * (σ2 / 2) := by
      have h1 : ∑ i ∈ Sᶜ, W i ^ 2 ≤ ∑ i ∈ Sᶜ, (σ2 / 2) := by
        apply Finset.sum_le_sum
        intro i hi
        have hp : ¬ (σ2 / 2 ≤ W i ^ 2) := by
          have hni : i ∉ S := Finset.mem_compl.mp hi
          simpa [hS, Finset.mem_filter] using hni
        exact le_of_lt (not_le.mp hp)
      have h2' : ∑ i ∈ Sᶜ, (σ2 / 2) = (Sᶜ.card : ℝ) * (σ2 / 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      have h3 : (Sᶜ.card : ℝ) ≤ (Fintype.card ι : ℝ) := by
        exact_mod_cast Finset.card_le_univ (Sᶜ)
      calc ∑ i ∈ Sᶜ, W i ^ 2 ≤ ∑ i ∈ Sᶜ, (σ2 / 2) := h1
        _ = (Sᶜ.card : ℝ) * (σ2 / 2) := h2'
        _ ≤ (Fintype.card ι : ℝ) * (σ2 / 2) := mul_le_mul_of_nonneg_right h3 (by positivity)
    have hSsum : (Fintype.card ι : ℝ) * σ2 / 2 ≤ ∑ i ∈ S, W i ^ 2 := by
      have hsp := Finset.sum_add_sum_compl S (fun i => W i ^ 2)
      linarith [hcompl, h2, hsp]
    -- Cauchy--Schwarz on the good set.
    have hCS : (∑ i ∈ S, W i ^ 2) ^ 2 ≤ (S.card : ℝ) * ∑ i ∈ S, W i ^ 4 := by
      have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ : ι => (1:ℝ)) (fun i => W i ^ 2)
      have e1 : (∑ i ∈ S, (1:ℝ) * W i ^ 2) = ∑ i ∈ S, W i ^ 2 := by simp
      have e2 : (∑ i ∈ S, (1:ℝ)^2) = (S.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; simp
      have e3 : (∑ i ∈ S, (W i ^ 2)^2) = ∑ i ∈ S, W i ^ 4 := by
        apply Finset.sum_congr rfl; intro i _; ring
      rwa [e1, e2, e3] at h
    have hS4 : ∑ i ∈ S, W i ^ 4 ≤ C * (Fintype.card ι : ℝ) * σ2 ^ 2 :=
      (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        (fun i _ _ => by positivity)).trans h4
    have hkey : ((Fintype.card ι : ℝ) * σ2 / 2)^2
        ≤ (S.card : ℝ) * C * (Fintype.card ι : ℝ) * σ2^2 := by
      have h1 : ((Fintype.card ι : ℝ) * σ2 / 2)^2 ≤ (∑ i ∈ S, W i ^ 2)^2 :=
        pow_le_pow_left₀ (by positivity) hSsum 2
      have h2' : (S.card : ℝ) * ∑ i ∈ S, W i ^ 4
          ≤ (S.card : ℝ) * (C * (Fintype.card ι : ℝ) * σ2^2) :=
        mul_le_mul_of_nonneg_left hS4 (Nat.cast_nonneg _)
      nlinarith [h1, hCS, h2']
    -- Cardinality of the good set.
    have hcard : (Fintype.card ι : ℝ) / (4 * C) ≤ (S.card : ℝ) := by
      have hfac : 0 < (Fintype.card ι : ℝ) * σ2 ^ 2 := by positivity
      have hkey' : ((Fintype.card ι : ℝ) / 4) * ((Fintype.card ι : ℝ) * σ2^2)
          ≤ ((S.card : ℝ) * C) * ((Fintype.card ι : ℝ) * σ2^2) := by
        have hh := hkey
        ring_nf at hh ⊢
        linarith [hh]
      have h2'' : (Fintype.card ι : ℝ) / 4 ≤ (S.card : ℝ) * C :=
        le_of_mul_le_mul_right hkey' hfac
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 4 * C)]
      nlinarith [h2'']
    -- The `q`-th moment lower bound.
    have hSq : ((Fintype.card ι : ℝ) / (4 * C)) * r ^ q ≤ ∑ i, W i ^ q := by
      have ha : ∑ i ∈ S, W i ^ q ≤ ∑ i, W i ^ q :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
          (fun i _ _ => Real.rpow_nonneg (hW i) q)
      have hb : (S.card : ℝ) * r ^ q ≤ ∑ i ∈ S, W i ^ q := by
        have hpt : ∀ i ∈ S, r ^ q ≤ W i ^ q := by
          intro i hi
          have hp : σ2 / 2 ≤ W i ^ 2 := by
            have hh := hi
            rw [hS, Finset.mem_filter] at hh
            exact hh.2
          have hrle : r ≤ W i := by
            rw [hr]
            calc Real.sqrt (σ2/2) ≤ Real.sqrt (W i ^ 2) := Real.sqrt_le_sqrt hp
              _ = W i := Real.sqrt_sq (hW i)
          exact Real.rpow_le_rpow hrnonneg hrle hq.le
        calc (S.card : ℝ) * r ^ q = ∑ i ∈ S, r ^ q := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ ∑ i ∈ S, W i ^ q := Finset.sum_le_sum hpt
      have hc : ((Fintype.card ι : ℝ) / (4 * C)) * r ^ q ≤ (S.card : ℝ) * r ^ q :=
        mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg hrnonneg q)
      linarith [ha, hb, hc]
    have hfinal : r ^ q / (4 * C) ≤ (∑ i, W i ^ q) / (Fintype.card ι : ℝ) := by
      have hd := div_le_div_of_nonneg_right hSq hNpos.le
      have hsimp : ((Fintype.card ι : ℝ) / (4 * C)) * r ^ q / (Fintype.card ι : ℝ)
          = r ^ q / (4 * C) := by
        field_simp
      rwa [hsimp] at hd
    have hbase : 0 ≤ r ^ q / (4 * C) := by positivity
    have hpow := Real.rpow_le_rpow hbase hfinal (by positivity : (0:ℝ) ≤ 1/q)
    have hval1 : (r ^ q) ^ (1/q) = r := by
      rw [← Real.rpow_mul hrnonneg, show q * (1/q) = 1 by field_simp, Real.rpow_one]
    have hval2 : ((4 * C) ^ (1/q))⁻¹ = (4 * C) ^ (-(1/q)) :=
      (Real.rpow_neg (by positivity : (0:ℝ) ≤ 4*C) (1/q)).symm
    have hval : (r ^ q / (4 * C)) ^ (1/q) = r * (4*C)^(-(1/q)) := by
      rw [Real.div_rpow (Real.rpow_nonneg hrnonneg q) (by positivity : (0:ℝ) ≤ 4*C), hval1,
        div_eq_mul_inv, hval2]
    rw [hval] at hpow
    have hr_eq : r = σ2 ^ ((1:ℝ)/2) / Real.sqrt 2 := by
      rw [hr, Real.sqrt_div (le_of_lt hpos), Real.sqrt_eq_rpow σ2]
    have hfin : ((4 * C) ^ (-(1/q)) / Real.sqrt 2) * σ2 ^ ((1:ℝ)/2) = r * (4*C)^(-(1/q)) := by
      rw [hr_eq]; ring
    rw [hfin]
    exact hpow

/-- **Khintchine's inequality, lower bound, for small exponents, Hilbert-space valued.**  For
`0 < q ≤ 1` there is `c = c q > 0` such that for every complex Hilbert space `H` and every finite
family `x : Fin n → H` of vectors,
`c (∑_i ‖x_i‖²)^{1/2} ≤ ((1/2^n) ∑_{ε ∈ {±1}^n} ‖∑_i ε_i x_i‖^q)^{1/q}`.
The companion one-sided results for `q ≥ 1` already exist as
`Commons.Analysis.Walsh.exists_khintchine_hilbert` (import
`Submission.Commons.Analysis.Walsh.exists_khintchine_hilbert`); only `0 < q ≤ 1` is new, and for
`q < 1` this is not a convexity statement (`t ↦ t^q` is concave, so Jensen gives the wrong
direction).  Suggested proof via Paley--Zygmund: put `Z = ‖∑ ε_i x_i‖²`; then `E Z = ∑_i ‖x_i‖²`
(`Commons.Analysis.Walsh.rademacher_parseval_inner`, or the private `parseval_complex` in
`Submission.Commons.Analysis.Walsh.khintchine_lower_hilbert`) and
`E Z² = E ‖∑ ε_i x_i‖⁴ ≤ 3 (∑_i ‖x_i‖²)²` (the private `norm_fourth_sum_le` in
`khintchine_lower_hilbert.lean`, or `rademacher_hilbert_even_moment` at `m = 2`, or the upper half
of `exists_khintchine_hilbert` at `p = 4`); Paley--Zygmund
(`P (Z ≥ θ E Z) ≥ (1-θ)² (E Z)² / E Z²`, proved by Cauchy--Schwarz) then gives
`E ‖∑ ε_i x_i‖^q ≥ (θ E Z)^{q/2} P (Z ≥ θ E Z)`.  The `q = 1` case is already available as
`Commons.Analysis.Walsh.khintchine_lower_hilbert`, so `q < 1` is the only new content. -/
theorem khintchine_lower_hilbert_small {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {q : ℝ} (hq : 0 < q) (hq1 : q ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (x : Fin n → H),
      c * (∑ i : Fin n, ‖x i‖ ^ 2) ^ ((1 : ℝ) / 2)
        ≤ ((∑ e : Fin n → Bool,
            ‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • x i‖ ^ q) / (2 : ℝ) ^ n)
          ^ ((1 : ℝ) / q) := by
  classical
  obtain ⟨K, hKpos, hKeven⟩ := Commons.Analysis.Walsh.rademacher_hilbert_even_moment
  -- The constant produced by Paley--Zygmund with threshold `1/2` and fourth-moment constant
  -- `C = (2K)^2` (from the even-moment bound at `m = 2`).
  refine ⟨(4 * (K * 2) ^ 2) ^ (-(1 / q)) / Real.sqrt 2, ?_, ?_⟩
  · exact div_pos (Real.rpow_pos_of_pos (by positivity) _) (Real.sqrt_pos.mpr (by norm_num))
  · intro n x
    have hcard : ((Fintype.card (Fin n → Bool) : ℕ) : ℝ) = (2:ℝ)^n := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]; push_cast; ring
    have hι : 0 < Fintype.card (Fin n → Bool) := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]; norm_num
    set W : (Fin n → Bool) → ℝ :=
      fun e => ‖∑ i : Fin n, (if e i then (1 : ℂ) else -1) • x i‖ with hWdef
    set σ : ℝ := ∑ i : Fin n, ‖x i‖ ^ (2:ℕ) with hσdef
    have h2 : ∑ e, W e ^ (2:ℕ) = (Fintype.card (Fin n → Bool) : ℝ) * σ := by
      rw [hWdef, hσdef, hcard]
      exact parseval_sq n x
    have h4 : ∑ e, W e ^ (4:ℕ) ≤ (K*2)^2 * (Fintype.card (Fin n → Bool) : ℝ) * σ ^ (2:ℕ) := by
      have h := hKeven 2 (by norm_num) (H := H) n x
      rw [div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^n)] at h
      rw [← hcard, ← hσdef] at h
      have hh : (∑ e : Fin n → Bool, W e ^ (4:ℕ))
          ≤ (K*2)^2 * σ^(2:ℕ) * (Fintype.card (Fin n → Bool) : ℝ) := h
      calc (∑ e : Fin n → Bool, W e ^ (4:ℕ))
          ≤ (K*2)^2 * σ^(2:ℕ) * (Fintype.card (Fin n → Bool) : ℝ) := hh
        _ = (K*2)^2 * (Fintype.card (Fin n → Bool) : ℝ) * σ ^ (2:ℕ) := by ring
    have hPZ := finite_paley_zygmund_rpow (ι := Fin n → Bool) hι W (fun e => norm_nonneg _)
        (σ2 := σ) (C := (K*2)^2) (by positivity) (by positivity) h2 h4 hq
    rw [← hcard]
    exact hPZ

end

end Work.Analysis.Variation
