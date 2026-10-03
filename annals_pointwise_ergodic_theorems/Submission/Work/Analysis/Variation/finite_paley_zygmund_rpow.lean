import Mathlib

namespace Work.Analysis.Variation

open Finset

/-- **Finite Paley--Zygmund for an arbitrary positive exponent.**  Let `W ≥ 0` be a nonnegative
function on a nonempty finite type `ι` with second moment `∑ W² = #ι * σ2` and fourth moment
`∑ W⁴ ≤ C * #ι * σ2²`.  Then for every `q > 0` the `q`-th moment of `W` is bounded below by
`(4C)^{-1/q} / √2 * σ2^{1/2}`.  The proof is Cauchy--Schwarz (Paley--Zygmund with threshold
`θ = 1/2` on the set `{W² ≥ σ2/2}`). -/
theorem finite_paley_zygmund_rpow {ι : Type*} [Fintype ι] [DecidableEq ι]
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

end Work.Analysis.Variation
