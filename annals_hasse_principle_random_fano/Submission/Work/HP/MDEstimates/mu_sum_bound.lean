import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDCommon
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.MDEstimates.mu_sum_aux
import Submission.Work.HP.MDEstimates.dmin_facts
import Submission.Work.HP.MDEstimates.mu_div_det_bound
import Submission.Work.HP.MDEstimates.layer_cake_min_sum
import Submission.Work.HP.MDEstimates.detGam_low
import Submission.Work.HP.MDEstimates.EE_lower
import Submission.Work.HP.MDEstimates.pair_counts_clean

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Filter
open scoped BigOperators

namespace Work.HP.MDEstimates

/-- `Omega d n B` is finite. -/
private lemma omega_finite (d n : ℕ) (B : ℝ) : (Omega d n B).Finite :=
  (MDBasic.finite_sets d n 0 B (fun _ => True)).2.2

/-- `(n-1)(n+1-d) ≥ 3` for `2 ≤ d ≤ n` with `(d,n) ∉ {(2,2),(3,3)}`. -/
private lemma key_exp (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2))
    (h33 : (d, n) ≠ (3, 3)) : 3 ≤ (n - 1) * (n + 1 - d) := by
  rcases Nat.lt_or_ge d n with h | h
  · have hn3 : 3 ≤ n := by omega
    have h2 : 2 ≤ n + 1 - d := by omega
    calc 3 ≤ 2 * 2 := by norm_num
      _ ≤ (n - 1) * (n + 1 - d) := Nat.mul_le_mul (by omega) h2
  · have hnd : n = d := by omega
    rcases Nat.lt_or_ge n 4 with h' | h'
    · have hn : n = 2 ∨ n = 3 := by omega
      rcases hn with hn | hn
      · have hd2 : d = 2 := by omega
        exact absurd (by simp [hd2, hn]) h22
      · have hd3 : d = 3 := by omega
        exact absurd (by simp [hd3, hn]) h33
    · have hone : n + 1 - d = 1 := by omega
      rw [hone]
      calc (3 : ℕ) ≤ n - 1 := by omega
        _ = (n - 1) * 1 := (Nat.mul_one _).symm

/-- The set counted by `ellXY` is finite. -/
private lemma ellXY_finite {n r : ℕ} (A B' Δ : ℝ) :
    ({q : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) | LinearIndependent ℤ ![q.1, q.2] ∧
      eNorm q.1 ≤ A ∧ eNorm q.2 ≤ B' ∧ dmin r {q.1, q.2} ≤ Δ} : Set _).Finite :=
  ((MDBasic.finite_eNorm_le (ι := Fin (n + 1)) A).prod
    (MDBasic.finite_eNorm_le (ι := Fin (n + 1)) B')).subset
    (fun q hq => ⟨hq.2.1, hq.2.2.1⟩)

/-- Elements of `Omega d n B` in a dyadic box with `dmin r {·,·} ≤ Δ` are counted by `ellXY`. -/
private lemma card_filter_le_ell (d n : ℕ) (B : ℝ)
    (S : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)))
    (hS : ∀ p, p ∈ S ↔ p ∈ Omega d n B) (r : ℕ) (A B' Δ : ℝ) :
    (S.filter (fun p => eNorm p.1 ≤ A ∧ eNorm p.2 ≤ B' ∧ dmin r {p.1, p.2} ≤ Δ)).card
      ≤ ellXY n r A B' Δ := by
  classical
  have hsub : ∀ p ∈ S.filter
        (fun p => eNorm p.1 ≤ A ∧ eNorm p.2 ≤ B' ∧ dmin r {p.1, p.2} ≤ Δ),
      p ∈ ({q : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) | LinearIndependent ℤ ![q.1, q.2] ∧
        eNorm q.1 ≤ A ∧ eNorm q.2 ≤ B' ∧ dmin r {q.1, q.2} ≤ Δ} : Set _) := by
    intro p hp
    obtain ⟨hpS, hp1, hp2, hp3⟩ := Finset.mem_filter.mp hp
    have hmem := (hS p).mp hpS
    exact ⟨linIndep_of_ne_pm hmem.1.1 hmem.2.1.1 hmem.2.2.1 hmem.2.2.2, hp1, hp2, hp3⟩
  let T : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
    S.filter (fun p => eNorm p.1 ≤ A ∧ eNorm p.2 ≤ B' ∧ dmin r {p.1, p.2} ≤ Δ)
  have hfin := ellXY_finite (n := n) (r := r) A B' Δ
  have hsubT : T ⊆ hfin.toFinset := by
    intro p hp
    rw [Set.Finite.mem_toFinset]
    exact hsub p hp
  have h2 : T.card ≤ (ellXY n r A B' Δ) := by
    rw [ellXY, Set.ncard_eq_toFinset_card _ hfin]
    exact Finset.card_le_card hsubT
  exact h2

/-- Primitive vectors of `ℤ^{n+1}` have norm at least `1`. -/
private lemma one_le_eNorm_prim {n : ℕ} {v : Fin (n + 1) → ℤ} (hv : IsPrim v) :
    (1 : ℝ) ≤ eNorm v :=
  one_le_eNorm_of_ne_zero (isPrim_ne_zero hv)



/-- Product bound for five factors. -/
private lemma mul4_le_mul4 {a1 a2 a3 a4 b1 b2 b3 b4 : ℝ}
    (h1 : a1 ≤ b1) (h2 : a2 ≤ b2) (h3 : a3 ≤ b3) (h4 : a4 ≤ b4)
    (h1n : 0 ≤ a1) (h2n : 0 ≤ a2) (h3n : 0 ≤ a3) (h4n : 0 ≤ a4)
    (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hb3 : 0 ≤ b3) :
    a1 * a2 * a3 * a4 ≤ b1 * b2 * b3 * b4 := by
  have w1 : a1 * a2 ≤ b1 * b2 := mul_le_mul h1 h2 h2n hb1
  have w2 : a1 * a2 * a3 ≤ b1 * b2 * b3 := mul_le_mul w1 h3 h3n (by positivity)
  exact mul_le_mul w2 h4 h4n (by positivity)

/-- **Main estimate.**  There are constants `K, B₀` with `K > 0` such that for all `B ≥ B₀`,
`∑_{Ω(B)} μ(x,y)/det Γ_{x,y} ≤ K (log B)^{16} B^{8/3}`. -/
private theorem sum_bound (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2))
    (h33 : (d, n) ≠ (3, 3)) (Cdet : ℝ) (hCdet : 0 < Cdet)
    (hdet : ∀ x y : Fin (n + 1) → ℤ, IsPrim x → IsPrim y → LinearIndependent ℤ ![x, y] →
      dmin 2 {x, y} * eNorm x ^ (d - 1) * eNorm y ^ (d - 1) ≤ Cdet * detL (Gam d n x y)) :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ B : ℝ, B₀ ≤ B →
      ∑ᶠ p ∈ Omega d n B, muXY n p.1 p.2 / detL (Gam d n p.1 p.2)
        ≤ K * Real.log B ^ 16 * B ^ ((8 : ℝ) / 3) := by
  have hn2 : 2 ≤ n := le_trans hd hdn
  have hn3 : 3 ≤ n := by
    rcases Nat.lt_or_ge n 3 with h | h
    · have hn : n = 2 := by omega
      have hd2 : d = 2 := by omega
      exact absurd (by simp [hn, hd2]) h22
    · exact h
  obtain ⟨hD2one, hD2XY, hD3one, hD3XY⟩ := dmin_facts n hn2
  obtain ⟨K2, hK2pos, hK2⟩ := pair_counts_clean n 2 hn2 le_rfl (by omega)
  obtain ⟨K3, hK3pos, hK3⟩ := pair_counts_clean n 3 hn2 (by norm_num) (by omega)
  obtain ⟨Clc, hClcpos, hlc⟩ := layer_cake_min_sum n d hn3 hd hdn
  refine ⟨3 * (n : ℝ) ^ 2 * Cdet * Clc * (K2 + K3 + 2) ^ 2 * 2 ^ 20, 16, by positivity, ?_⟩
  intro B hB
  have hB1 : (1 : ℝ) ≤ B := by linarith
  have hB2 : (2 : ℝ) ≤ B := by linarith
  have hBpos : (0 : ℝ) < B := by linarith
  have hexp1 : Real.exp 1 ≤ B := by linarith [Real.exp_one_lt_d9]
  have hlogB1 : (1 : ℝ) ≤ Real.log B := by
    rw [Real.le_log_iff_exp_le hBpos]
    exact hexp1
  have hlogB0 : (0 : ℝ) ≤ Real.log B := le_trans zero_le_one hlogB1
  set R : ℝ := B ^ (1 / ((n : ℝ) + 1 - d)) with hRdef
  have hnd1 : (1 : ℝ) ≤ (n : ℝ) + 1 - d := by
    have h1 : ((d : ℕ) : ℝ) ≤ ((n : ℕ) : ℝ) := by exact_mod_cast hdn
    push_cast
    linarith
  have hnd1' : (0 : ℝ) < (n : ℝ) + 1 - d := by linarith
  have hRpos : 0 < R := by
    rw [hRdef]; exact Real.rpow_pos_of_pos hBpos _
  have hR1 : 1 ≤ R := by
    rw [hRdef]
    calc (1 : ℝ) = B ^ (0 : ℝ) := (Real.rpow_zero B).symm
      _ ≤ B ^ (1 / ((n : ℝ) + 1 - d)) := by
          apply Real.rpow_le_rpow_of_exponent_le hB1
          rw [one_div]
          exact inv_nonneg.mpr hnd1'.le
  have hRle : R ≤ B := by
    rw [hRdef]
    calc B ^ (1 / ((n : ℝ) + 1 - d)) ≤ B ^ (1 : ℝ) := by
          apply Real.rpow_le_rpow_of_exponent_le hB1
          rw [one_div]
          exact inv_le_one_of_one_le₀ hnd1
      _ = B := Real.rpow_one B
  have h2R1 : (1 : ℝ) ≤ 2 * R := by linarith
  have h2Rpos : (0 : ℝ) < 2 * R := by linarith
  have h2R2 : 2 * R ≤ B ^ (2 : ℕ) := by nlinarith
  have hR2ge1 : (1 : ℝ) ≤ R ^ 2 := by nlinarith
  have hlogR : Real.log (2 * R) ≤ 2 * Real.log B := by
    calc Real.log (2 * R) ≤ Real.log (B ^ (2 : ℕ)) := Real.log_le_log h2Rpos h2R2
      _ = 2 * Real.log B := by rw [Real.log_pow]; push_cast; ring
  have hlogR0 : (0 : ℝ) ≤ Real.log (2 * R) := Real.log_nonneg h2R1
  have hlog2R2 : Real.log (2 * R ^ 2) ≤ 2 * Real.log (2 * R) := by
    have h1 : Real.log (2 * R ^ 2) = Real.log 2 + 2 * Real.log R := by
      rw [show (2 : ℝ) * R ^ 2 = 2 * R ^ (2 : ℕ) by ring]
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      ring
    have h3 : 2 * Real.log (2 * R) = 2 * (Real.log 2 + Real.log R) := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hRpos)]
    have h4 : Real.log 2 ≤ 2 * Real.log 2 := by
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      linarith
    rw [h1, h3]
    linarith
  have hL8 : Real.log (2 * R) ^ 8 ≤ 2 ^ 8 * Real.log B ^ 8 := by
    calc Real.log (2 * R) ^ 8 ≤ (2 * Real.log B) ^ 8 := pow_le_pow_left₀ hlogR0 hlogR 8
      _ = 2 ^ 8 * Real.log B ^ 8 := by rw [mul_pow]
  have hLam16 : (2 * Real.log (2 * R)) ^ 2 ≤ 16 * Real.log B ^ 2 := by
    calc (2 * Real.log (2 * R)) ^ 2 = 4 * Real.log (2 * R) ^ 2 := by ring
      _ ≤ 4 * (2 * Real.log B) ^ 2 := by
          have := pow_le_pow_left₀ hlogR0 hlogR 2
          linarith
      _ = 16 * Real.log B ^ 2 := by ring
  -- exponent bookkeeping
  have hn2R : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
  have hn1pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hkey : (3 : ℝ) ≤ ((n : ℝ) - 1) * ((n : ℝ) + 1 - (d : ℝ)) := by
    by_cases hdn' : n = d
    · have h1 : (n : ℝ) + 1 - (d : ℝ) = 1 := by rw [hdn']; ring
      rw [h1, mul_one]
      have hn4 : 4 ≤ n := by
        by_contra hcon
        have hn23 : n = 2 ∨ n = 3 := by omega
        rcases hn23 with h | h
        · have hd2 : d = 2 := by omega
          exact h22 (by simp [hd2, h])
        · have hd3 : d = 3 := by omega
          exact h33 (by simp [hd3, h])
      have h2 : (4 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn4
      linarith
    · have h1 : (2 : ℝ) ≤ (n : ℝ) - 1 := by
        have : 3 ≤ n := by omega
        have h3 : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast this
        linarith
      have h2 : (2 : ℝ) ≤ (n : ℝ) + 1 - (d : ℝ) := by
        have : d + 2 ≤ n + 1 := by omega
        have h3 : ((d : ℝ) + 2) ≤ ((n : ℝ) + 1) := by exact_mod_cast this
        linarith
      nlinarith [h1, h2]
  have hid2 : ((n : ℝ) - 1) * ((n : ℝ) + 1 - (d : ℝ))
      = (n : ℝ) ^ 2 - (n : ℝ) * (d : ℝ) + (d : ℝ) - 1 := by ring
  have hu : (4 : ℝ) ≤ (n : ℝ) ^ 2 - (n : ℝ) * (d : ℝ) + (d : ℝ) := by nlinarith [hkey, hid2]
  set E : ℝ := (2 * (n : ℝ) - 1) / ((n : ℝ) - 1) + (n : ℝ) - (d : ℝ) - 1 with hEdef
  have hEbound : R ^ (2 * E) ≤ B ^ ((8 : ℝ) / 3) := by
    rw [hRdef, ← Real.rpow_mul (le_of_lt hBpos), hEdef]
    refine Real.rpow_le_rpow_of_exponent_le hB1 ?_
    rw [one_div, inv_mul_le_iff₀ hnd1']
    have hid1 : ((2 * (n : ℝ) - 1) / ((n : ℝ) - 1) + (n : ℝ) - (d : ℝ) - 1) * ((n : ℝ) - 1)
        = (n : ℝ) ^ 2 - (n : ℝ) * (d : ℝ) + (d : ℝ) := by
      field_simp
      ring
    have hgoal : 2 * ((2 * (n : ℝ) - 1) / ((n : ℝ) - 1) + (n : ℝ) - (d : ℝ) - 1)
        * ((n : ℝ) - 1) ≤ (8 / 3) * ((n : ℝ) + 1 - (d : ℝ)) * ((n : ℝ) - 1) := by
      calc 2 * ((2 * (n : ℝ) - 1) / ((n : ℝ) - 1) + (n : ℝ) - (d : ℝ) - 1) * ((n : ℝ) - 1)
          = 2 * (((2 * (n : ℝ) - 1) / ((n : ℝ) - 1) + (n : ℝ) - (d : ℝ) - 1)
              * ((n : ℝ) - 1)) := by ring
        _ = 2 * ((n : ℝ) ^ 2 - (n : ℝ) * (d : ℝ) + (d : ℝ)) := by rw [hid1]
        _ ≤ (8 / 3) * ((n : ℝ) ^ 2 - (n : ℝ) * (d : ℝ) + (d : ℝ) - 1) := by nlinarith [hu]
        _ = (8 / 3) * (((n : ℝ) - 1) * ((n : ℝ) + 1 - (d : ℝ))) := by rw [hid2]
        _ = (8 / 3) * ((n : ℝ) + 1 - (d : ℝ)) * ((n : ℝ) - 1) := by ring
    have hgoal' : 2 * ((2 * (n : ℝ) - 1) / ((n : ℝ) - 1) + (n : ℝ) - (d : ℝ) - 1)
        * ((n : ℝ) - 1) ≤ ((n : ℝ) + 1 - (d : ℝ)) * (8 / 3) * ((n : ℝ) - 1) := by
      linarith [hgoal]
    exact le_of_mul_le_mul_right hgoal' hn1pos
  -- the set of pairs
  set S : Finset ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) := (omega_finite d n B).toFinset with hSdef
  have hSmem : ∀ p, p ∈ S ↔ p ∈ Omega d n B := by
    intro p
    rw [hSdef]
    exact Set.Finite.mem_toFinset (omega_finite d n B)
  have hmem : ∀ p ∈ S, p.1 ∈ Xi d n B ∧ p.2 ∈ Xi d n B ∧ p.1 ≠ p.2 ∧ p.1 ≠ -p.2 :=
    fun p hp => (hSmem p).mp hp
  have hPrim1 : ∀ p ∈ S, IsPrim p.1 := fun p hp => (hmem p hp).1.1
  have hPrim2 : ∀ p ∈ S, IsPrim p.2 := fun p hp => (hmem p hp).2.1.1
  have hLI : ∀ p ∈ S, LinearIndependent ℤ ![p.1, p.2] := fun p hp =>
    linIndep_of_ne_pm (hPrim1 p hp) (hPrim2 p hp) (hmem p hp).2.2.1 (hmem p hp).2.2.2
  have hXn : ∀ p ∈ S, eNorm p.1 ≤ R := fun p hp => (hmem p hp).1.2
  have hYn : ∀ p ∈ S, eNorm p.2 ≤ R := fun p hp => (hmem p hp).2.1.2
  have hD3R2 : ∀ p ∈ S, dmin 3 {p.1, p.2} ≤ R ^ 2 := by
    intro p hp
    have h := hD3XY p.1 p.2 (hLI p hp)
    have h1 := hXn p hp
    have h2 := hYn p hp
    have h3 : (0 : ℝ) ≤ eNorm p.1 := Real.sqrt_nonneg _
    have h4 : (0 : ℝ) ≤ eNorm p.2 := Real.sqrt_nonneg _
    nlinarith [h, h1, h2, h3, h4, hR1]
  -- auxiliary constants
  set Lam : ℝ := (2 * Real.log (2 * R)) ^ 2 with hLamdef
  have hLam1 : 1 ≤ Lam := by
    have h : (1 : ℝ) < 2 * Real.log (2 * R) := by
      have h2 := Real.log_two_gt_d9
      have h3 : Real.log 2 ≤ Real.log (2 * R) :=
        Real.log_le_log (by norm_num) (by linarith : (2 : ℝ) ≤ 2 * R)
      linarith
    rw [hLamdef]; nlinarith [h]
  have hLam0 : (0 : ℝ) ≤ Lam := le_trans zero_le_one hLam1
  set K2' : ℝ := max K2 1 with hK2'def
  set K3' : ℝ := max K3 1 * Lam with hK3'def
  have hK2'1 : 1 ≤ K2' := le_max_right _ _
  have hK3'1 : 1 ≤ K3' := by
    rw [hK3'def]
    have h1 : (1 : ℝ) ≤ max K3 1 := le_max_right _ _
    nlinarith [h1, hLam1]
  have hK3'pos : (0 : ℝ) < K3' := lt_of_lt_of_le zero_lt_one hK3'1
  have hK2'pos : (0 : ℝ) < K2' := lt_of_lt_of_le zero_lt_one hK2'1
  have hK3'eq : K3' = max K3 1 * Lam := hK3'def
  set a : ℝ := ((n : ℝ) - 2) / ((n : ℝ) - 1) with hadef
  set b : ℝ := 1 / ((n : ℝ) - 1) with hbdef
  have ha_le : a ≤ 1 := by
    rw [hadef, div_le_iff₀ hn1pos]
    linarith
  have hb_le : b ≤ 1 := by
    rw [hbdef, div_le_iff₀ hn1pos]
    linarith
  -- the counting hypothesis for `dmin 2`
  have hC2 : ∀ A B' Δ : ℝ, 1 ≤ A → 1 ≤ B' → 1 ≤ Δ →
      ((S.filter fun p => eNorm p.1 ≤ A ∧ eNorm p.2 ≤ B' ∧ dmin 2 {p.1, p.2} ≤ Δ).card : ℝ)
        ≤ K2' * A ^ 2 * B' ^ 2 * Δ ^ (n - 1) := by
    intro A B' Δ hA hB' hΔ
    have hcard := card_filter_le_ell d n B S hSmem 2 A B' Δ
    have hpc : (ellXY n 2 A B' Δ : ℝ) ≤ K2 * A ^ 2 * B' ^ 2 * Δ ^ (n - 1) := by
      have := hK2 A B' Δ hA hB' hΔ
      simpa using this
    have h1 : ((S.filter fun p => eNorm p.1 ≤ A ∧ eNorm p.2 ≤ B' ∧
        dmin 2 {p.1, p.2} ≤ Δ).card : ℝ) ≤ (ellXY n 2 A B' Δ : ℝ) := by
      exact_mod_cast hcard
    have h2 : K2 * A ^ 2 * B' ^ 2 * Δ ^ (n - 1) ≤ K2' * A ^ 2 * B' ^ 2 * Δ ^ (n - 1) := by
      rw [mul_assoc K2 (A ^ 2) (B' ^ 2), mul_assoc K2' (A ^ 2) (B' ^ 2)]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left K2 1) (by positivity)) (by positivity)
    linarith
  -- the same count with the `A^3 B^3` shape
  have hC2' : ∀ A B' Δ : ℝ, 1 ≤ A → 1 ≤ B' → 1 ≤ Δ →
      ((S.filter fun p => eNorm p.1 ≤ A ∧ eNorm p.2 ≤ B' ∧ dmin 2 {p.1, p.2} ≤ Δ).card : ℝ)
        ≤ K2' * A ^ 3 * B' ^ 3 * Δ ^ (n - 1) := by
    intro A B' Δ hA hB' hΔ
    refine (hC2 A B' Δ hA hB' hΔ).trans ?_
    have ht : (1 : ℝ) ≤ A * B' := one_le_mul_of_one_le_of_one_le hA hB'
    have hpow : A ^ 2 * B' ^ 2 ≤ A ^ 3 * B' ^ 3 := by
      calc A ^ 2 * B' ^ 2 = (A * B') ^ 2 := by ring
        _ ≤ (A * B') ^ 3 := by
            calc (A * B') ^ 2 = (A * B') ^ 2 * 1 := by ring
              _ ≤ (A * B') ^ 2 * (A * B') := mul_le_mul_of_nonneg_left ht (by positivity)
              _ = (A * B') ^ 3 := by ring
        _ = A ^ 3 * B' ^ 3 := by ring
    have h1 : K2' * A ^ 2 * B' ^ 2 ≤ K2' * A ^ 3 * B' ^ 3 := by
      rw [mul_assoc K2' (A ^ 2) (B' ^ 2), mul_assoc K2' (A ^ 3) (B' ^ 3)]
      exact mul_le_mul_of_nonneg_left hpow hK2'pos.le
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  -- the counting hypothesis for `dmin 3`
  have hC3 : ∀ A B' Δ : ℝ, 1 ≤ A → 1 ≤ B' → 1 ≤ Δ →
      ((S.filter fun p => eNorm p.1 ≤ A ∧ eNorm p.2 ≤ B' ∧ dmin 3 {p.1, p.2} ≤ Δ).card : ℝ)
        ≤ K3' * A ^ 3 * B' ^ 3 * Δ ^ (n - 1) := by
    intro A B' Δ hA hB' hΔ
    have hmin1 : (1 : ℝ) ≤ min Δ (R ^ 2) := le_min hΔ hR2ge1
    have hcard := card_filter_le_ell d n B S hSmem 3 A B' (min Δ (R ^ 2))
    have hpc : (ellXY n 3 A B' (min Δ (R ^ 2)) : ℝ)
        ≤ K3 * A ^ 3 * B' ^ 3 * (min Δ (R ^ 2)) ^ (n - 1)
          * Real.log (2 * min Δ (R ^ 2)) ^ 2 := by
      have := hK3 A B' (min Δ (R ^ 2)) hA hB' hmin1
      simpa using this
    have h1 : ((S.filter fun p => eNorm p.1 ≤ A ∧ eNorm p.2 ≤ B' ∧
        dmin 3 {p.1, p.2} ≤ min Δ (R ^ 2)).card : ℝ) ≤ (ellXY n 3 A B' (min Δ (R ^ 2)) : ℝ) := by
      exact_mod_cast hcard
    have hsub : (S.filter fun p => eNorm p.1 ≤ A ∧ eNorm p.2 ≤ B' ∧ dmin 3 {p.1, p.2} ≤ Δ).card
        ≤ (S.filter fun p => eNorm p.1 ≤ A ∧ eNorm p.2 ≤ B' ∧
            dmin 3 {p.1, p.2} ≤ min Δ (R ^ 2)).card := by
      apply Finset.card_le_card
      intro p hp
      obtain ⟨hpS, h1, h2, h3⟩ := Finset.mem_filter.mp hp
      exact Finset.mem_filter.mpr ⟨hpS, h1, h2, le_min h3 (hD3R2 p hpS)⟩
    have hlogmin : Real.log (2 * min Δ (R ^ 2)) ^ 2 ≤ Lam := by
      have hp2 : min Δ (R ^ 2) ≤ R ^ 2 := min_le_right _ _
      have h2Δ : (0 : ℝ) < 2 * min Δ (R ^ 2) := by linarith
      have hle : Real.log (2 * min Δ (R ^ 2)) ≤ 2 * Real.log (2 * R) := by
        calc Real.log (2 * min Δ (R ^ 2)) ≤ Real.log (2 * R ^ 2) :=
              Real.log_le_log h2Δ (by nlinarith)
          _ ≤ 2 * Real.log (2 * R) := hlog2R2
      have h0 : 0 ≤ Real.log (2 * min Δ (R ^ 2)) := Real.log_nonneg (by linarith)
      rw [hLamdef]
      exact pow_le_pow_left₀ h0 hle 2
    have hminpow : (min Δ (R ^ 2)) ^ (n - 1) ≤ Δ ^ (n - 1) :=
      pow_le_pow_left₀ (by positivity) (min_le_left _ _) (n - 1)
    have hkey2 : K3 * Real.log (2 * min Δ (R ^ 2)) ^ 2 ≤ K3' := by
      have hK3le : K3 ≤ max K3 1 := le_max_left _ _
      calc K3 * Real.log (2 * min Δ (R ^ 2)) ^ 2
          ≤ max K3 1 * Real.log (2 * min Δ (R ^ 2)) ^ 2 :=
            mul_le_mul_of_nonneg_right hK3le (by positivity)
        _ ≤ max K3 1 * Lam := mul_le_mul_of_nonneg_left hlogmin (by positivity)
        _ = K3' := hK3'eq.symm
    have h2 : K3 * A ^ 3 * B' ^ 3 * (min Δ (R ^ 2)) ^ (n - 1)
        * Real.log (2 * min Δ (R ^ 2)) ^ 2 ≤ K3' * A ^ 3 * B' ^ 3 * Δ ^ (n - 1) := by
      calc K3 * A ^ 3 * B' ^ 3 * (min Δ (R ^ 2)) ^ (n - 1)
            * Real.log (2 * min Δ (R ^ 2)) ^ 2
          = A ^ 3 * B' ^ 3 * (min Δ (R ^ 2)) ^ (n - 1)
            * (K3 * Real.log (2 * min Δ (R ^ 2)) ^ 2) := by ring
        _ ≤ A ^ 3 * B' ^ 3 * Δ ^ (n - 1) * K3' :=
            mul_le_mul (mul_le_mul_of_nonneg_left hminpow (by positivity)) hkey2
              (by positivity) (by positivity)
        _ = K3' * A ^ 3 * B' ^ 3 * Δ ^ (n - 1) := by ring
    have h3 : ((S.filter fun p => eNorm p.1 ≤ A ∧ eNorm p.2 ≤ B' ∧
        dmin 3 {p.1, p.2} ≤ Δ).card : ℝ) ≤
        (K3 * A ^ 3 * B' ^ 3 * (min Δ (R ^ 2)) ^ (n - 1)
          * Real.log (2 * min Δ (R ^ 2)) ^ 2 : ℝ) := by
      have h4 : ((S.filter fun p => eNorm p.1 ≤ A ∧ eNorm p.2 ≤ B' ∧
          dmin 3 {p.1, p.2} ≤ Δ).card : ℝ)
          ≤ ((S.filter fun p => eNorm p.1 ≤ A ∧ eNorm p.2 ≤ B' ∧
              dmin 3 {p.1, p.2} ≤ min Δ (R ^ 2)).card : ℝ) := by
        exact_mod_cast hsub
      linarith [h4, h1, hpc]
    linarith [h3, h2]
  -- the two applications of the dyadic estimate
  have hLC1 : (∑ p ∈ S, 1 / (dmin 2 {p.1, p.2} * dmin 3 {p.1, p.2} *
        eNorm p.1 ^ (d - 2) * eNorm p.2 ^ (d - 2)))
      ≤ Clc * K2' ^ a * K3' ^ b * R ^ (2 * E) * Real.log (2 * R) ^ 8 := by
    have h := hlc _ S (fun p => eNorm p.1) (fun p => eNorm p.2)
      (fun p => dmin 2 {p.1, p.2}) (fun p => dmin 3 {p.1, p.2}) K2' K3' R
      hK2'1 hK3'1 hR1 (fun p hp => ⟨one_le_eNorm_prim (hPrim1 p hp), hXn p hp⟩)
      (fun p hp => ⟨one_le_eNorm_prim (hPrim2 p hp), hYn p hp⟩)
      (fun p hp => ⟨hD2one p.1 p.2 (hLI p hp), hD2XY p.1 p.2 (hLI p hp)⟩)
      (fun p hp => ⟨hD3one p.1 p.2 (hLI p hp), hD3XY p.1 p.2 (hLI p hp)⟩)
      hC2 hC3
    simpa [hadef, hbdef, hEdef] using h
  have hLC2 : (∑ p ∈ S, 1 / (dmin 2 {p.1, p.2} * dmin 2 {p.1, p.2} *
        eNorm p.1 ^ (d - 2) * eNorm p.2 ^ (d - 2)))
      ≤ Clc * K2' ^ a * K2' ^ b * R ^ (2 * E) * Real.log (2 * R) ^ 8 := by
    have h := hlc _ S (fun p => eNorm p.1) (fun p => eNorm p.2)
      (fun p => dmin 2 {p.1, p.2}) (fun p => dmin 2 {p.1, p.2}) K2' K2' R
      hK2'1 hK2'1 hR1 (fun p hp => ⟨one_le_eNorm_prim (hPrim1 p hp), hXn p hp⟩)
      (fun p hp => ⟨one_le_eNorm_prim (hPrim2 p hp), hYn p hp⟩)
      (fun p hp => ⟨hD2one p.1 p.2 (hLI p hp), hD2XY p.1 p.2 (hLI p hp)⟩)
      (fun p hp => ⟨hD2one p.1 p.2 (hLI p hp), hD2XY p.1 p.2 (hLI p hp)⟩)
      hC2 hC2'
    simpa [hadef, hbdef, hEdef] using h
  -- the pointwise bound, summed
  have hpt : (∑ p ∈ S, muXY n p.1 p.2 / detL (Gam d n p.1 p.2))
      ≤ 3 * (n : ℝ) ^ 2 * Cdet * ((∑ p ∈ S, 1 / (dmin 2 {p.1, p.2} * dmin 3 {p.1, p.2} *
            eNorm p.1 ^ (d - 2) * eNorm p.2 ^ (d - 2)))
          + (∑ p ∈ S, 1 / (dmin 2 {p.1, p.2} * dmin 2 {p.1, p.2} *
            eNorm p.1 ^ (d - 2) * eNorm p.2 ^ (d - 2)))) := by
    have h1 : (∑ p ∈ S, muXY n p.1 p.2 / detL (Gam d n p.1 p.2))
        ≤ ∑ p ∈ S, 3 * (n : ℝ) ^ 2 * Cdet *
            (1 / (dmin 2 {p.1, p.2} * dmin 3 {p.1, p.2} *
                eNorm p.1 ^ (d - 2) * eNorm p.2 ^ (d - 2))
             + 1 / (dmin 2 {p.1, p.2} * dmin 2 {p.1, p.2} *
                eNorm p.1 ^ (d - 2) * eNorm p.2 ^ (d - 2))) := by
      apply Finset.sum_le_sum
      intro p hp
      have h := mu_div_det_bound d n hd hdn Cdet hCdet p.1 p.2 (hPrim1 p hp) (hPrim2 p hp)
        (hLI p hp) (hdet p.1 p.2 (hPrim1 p hp) (hPrim2 p hp) (hLI p hp))
      simpa [sq] using h
    have h2 : (∑ p ∈ S, 3 * (n : ℝ) ^ 2 * Cdet *
          (1 / (dmin 2 {p.1, p.2} * dmin 3 {p.1, p.2} *
              eNorm p.1 ^ (d - 2) * eNorm p.2 ^ (d - 2))
           + 1 / (dmin 2 {p.1, p.2} * dmin 2 {p.1, p.2} *
              eNorm p.1 ^ (d - 2) * eNorm p.2 ^ (d - 2))))
        = 3 * (n : ℝ) ^ 2 * Cdet * ((∑ p ∈ S, 1 / (dmin 2 {p.1, p.2} * dmin 3 {p.1, p.2} *
              eNorm p.1 ^ (d - 2) * eNorm p.2 ^ (d - 2)))
            + (∑ p ∈ S, 1 / (dmin 2 {p.1, p.2} * dmin 2 {p.1, p.2} *
              eNorm p.1 ^ (d - 2) * eNorm p.2 ^ (d - 2)))) := by
      have h1 : (∑ p ∈ S, 3 * (n : ℝ) ^ 2 * Cdet *
            (1 / (dmin 2 {p.1, p.2} * dmin 3 {p.1, p.2} *
                eNorm p.1 ^ (d - 2) * eNorm p.2 ^ (d - 2))
             + 1 / (dmin 2 {p.1, p.2} * dmin 2 {p.1, p.2} *
                eNorm p.1 ^ (d - 2) * eNorm p.2 ^ (d - 2))))
          = (∑ p ∈ S, 3 * (n : ℝ) ^ 2 * Cdet *
              (1 / (dmin 2 {p.1, p.2} * dmin 3 {p.1, p.2} *
                  eNorm p.1 ^ (d - 2) * eNorm p.2 ^ (d - 2))))
            + (∑ p ∈ S, 3 * (n : ℝ) ^ 2 * Cdet *
              (1 / (dmin 2 {p.1, p.2} * dmin 2 {p.1, p.2} *
                  eNorm p.1 ^ (d - 2) * eNorm p.2 ^ (d - 2)))) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      rw [h1, ← Finset.mul_sum, ← Finset.mul_sum, ← mul_add]
    linarith [h1, h2]
  -- factor bounds
  have hb1 : K2' ^ a ≤ K2 + K3 + 2 := by
    have h1 : K2' ≤ K2 + K3 + 2 := by
      rw [hK2'def]
      have h2 : max K2 1 ≤ K2 + 1 := max_le (by linarith) (by linarith)
      linarith [hK3pos]
    calc K2' ^ a ≤ K2' ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK2'1 ha_le
      _ = K2' := Real.rpow_one K2'
      _ ≤ K2 + K3 + 2 := h1
  have hb3 : K2' ^ b ≤ K2 + K3 + 2 := by
    have h1 : K2' ≤ K2 + K3 + 2 := by
      rw [hK2'def]
      have h2 : max K2 1 ≤ K2 + 1 := max_le (by linarith) (by linarith)
      linarith [hK3pos]
    calc K2' ^ b ≤ K2' ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hK2'1 hb_le
      _ = K2' := Real.rpow_one K2'
      _ ≤ K2 + K3 + 2 := h1
  have hb2 : K3' ^ b ≤ (K2 + K3 + 2) * (16 * Real.log B ^ 2) := by
    have hmul : K3' ^ b = (max K3 1) ^ b * Lam ^ b := by
      rw [hK3'eq, Real.mul_rpow (by positivity) hLam0]
    rw [hmul]
    have h1 : (max K3 1) ^ b ≤ max K3 1 := by
      calc (max K3 1) ^ b ≤ (max K3 1) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (le_max_right _ _) hb_le
        _ = max K3 1 := Real.rpow_one _
    have h2 : Lam ^ b ≤ Lam := by
      calc Lam ^ b ≤ Lam ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hLam1 hb_le
        _ = Lam := Real.rpow_one _
    have hK3le : max K3 1 ≤ K2 + K3 + 2 := by
      have h3 : max K3 1 ≤ K3 + 1 := max_le (by linarith) (by linarith)
      linarith [hK2pos]
    have hLamle : Lam ≤ 16 * Real.log B ^ 2 := by
      rw [hLamdef]; exact hLam16
    calc (max K3 1) ^ b * Lam ^ b ≤ (max K3 1) * Lam :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ ≤ (K2 + K3 + 2) * (16 * Real.log B ^ 2) :=
          mul_le_mul hK3le hLamle (by positivity) (by positivity)
  have hK23 : (0 : ℝ) < K2 + K3 + 2 := by linarith
  -- the mid-point bound
  have hsum12 : (∑ p ∈ S, 1 / (dmin 2 {p.1, p.2} * dmin 3 {p.1, p.2} *
        eNorm p.1 ^ (d - 2) * eNorm p.2 ^ (d - 2)))
      + (∑ p ∈ S, 1 / (dmin 2 {p.1, p.2} * dmin 2 {p.1, p.2} *
        eNorm p.1 ^ (d - 2) * eNorm p.2 ^ (d - 2)))
      ≤ (Clc * (K2 + K3 + 2) * ((K2 + K3 + 2) * (16 * Real.log B ^ 2) + (K2 + K3 + 2)))
        * B ^ ((8 : ℝ) / 3) * (2 ^ 8 * Real.log B ^ 8) := by
    have hfac : Clc * K2' ^ a * K3' ^ b * R ^ (2 * E) * Real.log (2 * R) ^ 8
        + Clc * K2' ^ a * K2' ^ b * R ^ (2 * E) * Real.log (2 * R) ^ 8
        = Clc * K2' ^ a * (K3' ^ b + K2' ^ b) * R ^ (2 * E) * Real.log (2 * R) ^ 8 := by
      ring
    have hs1 : Clc * K2' ^ a ≤ Clc * (K2 + K3 + 2) := mul_le_mul_of_nonneg_left hb1 hClcpos.le
    have hs2 : K3' ^ b + K2' ^ b ≤ (K2 + K3 + 2) * (16 * Real.log B ^ 2) + (K2 + K3 + 2) :=
      add_le_add hb2 hb3
    have hs3 : R ^ (2 * E) ≤ B ^ ((8 : ℝ) / 3) := hEbound
    have hs4 : Real.log (2 * R) ^ 8 ≤ 2 ^ 8 * Real.log B ^ 8 := hL8
    have hmid : Clc * K2' ^ a * (K3' ^ b + K2' ^ b) * R ^ (2 * E) * Real.log (2 * R) ^ 8
        ≤ (Clc * (K2 + K3 + 2) * ((K2 + K3 + 2) * (16 * Real.log B ^ 2) + (K2 + K3 + 2)))
          * B ^ ((8 : ℝ) / 3) * (2 ^ 8 * Real.log B ^ 8) :=
      mul4_le_mul4 hs1 hs2 hs3 hs4 (by positivity) (by positivity) (by positivity) (by positivity)
        (by positivity) (by positivity) (by positivity)
    linarith [hLC1, hLC2, hfac, hmid]
  -- the final arithmetic
  have hfinal : (Clc * (K2 + K3 + 2) * ((K2 + K3 + 2) * (16 * Real.log B ^ 2) + (K2 + K3 + 2)))
        * B ^ ((8 : ℝ) / 3) * (2 ^ 8 * Real.log B ^ 8)
      ≤ (Clc * (K2 + K3 + 2) ^ 2 * 2 ^ 20) * Real.log B ^ 16 * B ^ ((8 : ℝ) / 3) := by
    have h1 : (16 * Real.log B ^ 2 + 1) ≤ 17 * Real.log B ^ 2 := by nlinarith [hlogB1]
    have h2 : (1 : ℝ) ≤ Real.log B ^ 6 := one_le_pow₀ hlogB1
    have h3 : (17 : ℝ) * 2 ^ 8 ≤ 2 ^ 20 := by norm_num
    have h4 : (16 * Real.log B ^ 2 + 1) * 2 ^ 8 * Real.log B ^ 8 ≤ 2 ^ 20 * Real.log B ^ 16 := by
      have h1' : (16 * Real.log B ^ 2 + 1) * 2 ^ 8 * Real.log B ^ 8
          ≤ (17 * Real.log B ^ 2) * 2 ^ 8 * Real.log B ^ 8 := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
      have h2' : (17 * Real.log B ^ 2) * 2 ^ 8 * Real.log B ^ 8 ≤ 2 ^ 20 * Real.log B ^ 16 := by
        have h3' : (17 : ℝ) * 2 ^ 8 ≤ 2 ^ 20 * Real.log B ^ 6 := by
          have := mul_le_mul h3 h2 (by norm_num) (by positivity)
          simpa using this
        calc (17 * Real.log B ^ 2) * 2 ^ 8 * Real.log B ^ 8
            = (17 * 2 ^ 8) * Real.log B ^ 10 := by ring
          _ ≤ (2 ^ 20 * Real.log B ^ 6) * Real.log B ^ 10 :=
              mul_le_mul_of_nonneg_right h3' (by positivity)
          _ = 2 ^ 20 * Real.log B ^ 16 := by ring
      linarith [h1', h2']
    rw [show (Clc * (K2 + K3 + 2) * ((K2 + K3 + 2) * (16 * Real.log B ^ 2) + (K2 + K3 + 2)))
          * B ^ ((8 : ℝ) / 3) * (2 ^ 8 * Real.log B ^ 8)
        = Clc * (K2 + K3 + 2) ^ 2 * ((16 * Real.log B ^ 2 + 1) * 2 ^ 8 * Real.log B ^ 8)
          * B ^ ((8 : ℝ) / 3) by ring]
    calc Clc * (K2 + K3 + 2) ^ 2 * ((16 * Real.log B ^ 2 + 1) * 2 ^ 8 * Real.log B ^ 8)
          * B ^ ((8 : ℝ) / 3)
        ≤ Clc * (K2 + K3 + 2) ^ 2 * (2 ^ 20 * Real.log B ^ 16) * B ^ ((8 : ℝ) / 3) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hBpos.le _)
          apply mul_le_mul_of_nonneg_left h4 (by positivity)
      _ = (Clc * (K2 + K3 + 2) ^ 2 * 2 ^ 20) * Real.log B ^ 16 * B ^ ((8 : ℝ) / 3) := by ring
  -- assembling
  have hsum_pt : (∑ᶠ p ∈ Omega d n B, muXY n p.1 p.2 / detL (Gam d n p.1 p.2))
      = ∑ p ∈ S, muXY n p.1 p.2 / detL (Gam d n p.1 p.2) := by
    rw [finsum_mem_eq_finite_toFinset_sum _ (omega_finite d n B), ← hSdef]
  rw [hsum_pt]
  calc ∑ p ∈ S, muXY n p.1 p.2 / detL (Gam d n p.1 p.2)
      ≤ 3 * (n : ℝ) ^ 2 * Cdet * ((∑ p ∈ S, 1 / (dmin 2 {p.1, p.2} * dmin 3 {p.1, p.2} *
            eNorm p.1 ^ (d - 2) * eNorm p.2 ^ (d - 2)))
          + (∑ p ∈ S, 1 / (dmin 2 {p.1, p.2} * dmin 2 {p.1, p.2} *
            eNorm p.1 ^ (d - 2) * eNorm p.2 ^ (d - 2)))) := hpt
    _ ≤ 3 * (n : ℝ) ^ 2 * Cdet * ((Clc * (K2 + K3 + 2) *
            ((K2 + K3 + 2) * (16 * Real.log B ^ 2) + (K2 + K3 + 2)))
          * B ^ ((8 : ℝ) / 3) * (2 ^ 8 * Real.log B ^ 8)) :=
        mul_le_mul_of_nonneg_left hsum12 (by positivity)
    _ ≤ 3 * (n : ℝ) ^ 2 * Cdet * ((Clc * (K2 + K3 + 2) ^ 2 * 2 ^ 20) *
          Real.log B ^ 16 * B ^ ((8 : ℝ) / 3)) :=
        mul_le_mul_of_nonneg_left hfinal (by positivity)
    _ = 3 * (n : ℝ) ^ 2 * Cdet * Clc * (K2 + K3 + 2) ^ 2 * 2 ^ 20 *
          Real.log B ^ 16 * B ^ ((8 : ℝ) / 3) := by ring


/-- **The μ-random-variable estimate** (Browning--Le Boudec--Sawin, the `G_{d,n}(B)` term of the
second-moment computation): the μ-weighted average of the inverse determinants of `Γ_{x,y}` is at
most `A^{3/4}` times the unweighted average `E_{d,n}(B)`. -/
theorem mu_sum_bound (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2))
    (h33 : (d, n) ≠ (3, 3)) :
    ∃ K B₀ : ℝ, 0 < K ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      ∑ᶠ p ∈ Omega d n B, muXY n p.1 p.2 / detL (Gam d n p.1 p.2)
        ≤ K * A ^ ((3 : ℝ) / 4) * EE d n B := by
  have hn2 : 2 ≤ n := le_trans hd hdn
  obtain ⟨Cdet, hCdetpos, hdet⟩ := detGam_low d n hd hdn
  obtain ⟨K1, B1, hK1pos, h1⟩ := sum_bound d n hd hdn h22 h33 Cdet hCdetpos hdet
  obtain ⟨cee, Bee, hceepos, hBeepos, hEE⟩ := EE_lower d n hd hdn h22
  -- the elementary `log B` versus `B^ε` comparison
  have hloglim : ∀ᶠ B : ℝ in atTop,
      K1 * Real.log B ^ ((67 : ℝ) / 4) ≤ cee * B ^ ((1 : ℝ) / 12) := by
    have hbound := (isLittleO_log_rpow_rpow_atTop ((67 : ℝ) / 4)
      (by norm_num : (0 : ℝ) < 1 / 12)).bound (show (0 : ℝ) < cee / K1 by positivity)
    filter_upwards [hbound, eventually_ge_atTop (1 : ℝ)] with B hB' hBge
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg hBge) _),
        Real.norm_of_nonneg (Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ B) _)] at hB'
    have hmul : K1 * ((cee / K1) * B ^ ((1 : ℝ) / 12)) = cee * B ^ ((1 : ℝ) / 12) := by
      field_simp
    have h2 := mul_le_mul_of_nonneg_left hB' hK1pos.le
    linarith [hmul, h2]
  obtain ⟨B2, hB2⟩ := eventually_atTop.mp hloglim
  refine ⟨1, max (max B1 Bee) (max B2 4), one_pos, ?_⟩
  intro A B hB hA hA2
  have hBB1 : B1 ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hB
  have hBBee : Bee ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hB
  have hBB2 : B2 ≤ B := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hB
  have hB4 : (4 : ℝ) ≤ B := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hB
  have hBpos : 0 < B := by linarith
  have hlogB1 : 1 ≤ Real.log B := by
    rw [Real.le_log_iff_exp_le hBpos]
    linarith [Real.exp_one_lt_d9]
  have hlogBpos : 0 < Real.log B := by linarith
  have hApos : 0 < A := lt_of_lt_of_le (div_pos hBpos hlogBpos) hA
  have hsum := h1 B hBB1
  have hEE' := hEE B hBBee
  have hb2 : K1 * Real.log B ^ ((67 : ℝ) / 4) ≤ cee * B ^ ((1 : ℝ) / 12) := hB2 B hBB2
  -- `(B / log B)^{3/4} ≤ A^{3/4}`
  have hA34 : (B / Real.log B) ^ ((3 : ℝ) / 4) ≤ A ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow (div_nonneg hBpos.le hlogBpos.le) hA (by norm_num)
  -- the weighted sum is bounded by `A^{3/4} E_{d,n}(B)`
  have hkey : K1 * Real.log B ^ 16 * B ^ ((8 : ℝ) / 3)
      ≤ cee * B ^ ((11 : ℝ) / 4) / Real.log B ^ ((3 : ℝ) / 4) := by
    have h67 : Real.log B ^ ((67 : ℝ) / 4)
        = Real.log B ^ (16 : ℝ) * Real.log B ^ ((3 : ℝ) / 4) := by
      rw [show ((67 : ℝ) / 4) = (16 : ℝ) + (3 : ℝ) / 4 by norm_num]
      exact Real.rpow_add hlogBpos 16 ((3 : ℝ) / 4)
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hlogBpos _)]
    have hstep : K1 * Real.log B ^ ((67 : ℝ) / 4) * B ^ ((8 : ℝ) / 3)
        ≤ cee * B ^ ((11 : ℝ) / 4) := by
      calc K1 * Real.log B ^ ((67 : ℝ) / 4) * B ^ ((8 : ℝ) / 3)
          ≤ (cee * B ^ ((1 : ℝ) / 12)) * B ^ ((8 : ℝ) / 3) :=
            mul_le_mul_of_nonneg_right hb2 (Real.rpow_nonneg hBpos.le _)
        _ = cee * B ^ ((11 : ℝ) / 4) := by
            rw [mul_assoc, ← Real.rpow_add hBpos]
            norm_num
    calc (K1 * Real.log B ^ 16 * B ^ ((8 : ℝ) / 3)) * Real.log B ^ ((3 : ℝ) / 4)
        = K1 * Real.log B ^ ((67 : ℝ) / 4) * B ^ ((8 : ℝ) / 3) := by
          rw [show Real.log B ^ 16 = Real.log B ^ (16 : ℝ) from (Real.rpow_natCast _ 16).symm, h67]
          ring
      _ ≤ cee * B ^ ((11 : ℝ) / 4) := hstep
  have hEE'' : cee * B ^ ((11 : ℝ) / 4) / Real.log B ^ ((3 : ℝ) / 4)
      ≤ A ^ ((3 : ℝ) / 4) * EE d n B := by
    have hfac : cee * B ^ ((11 : ℝ) / 4) / Real.log B ^ ((3 : ℝ) / 4)
        = (B / Real.log B) ^ ((3 : ℝ) / 4) * (cee * B ^ 2) := by
      have hB11 : B ^ ((11 : ℝ) / 4) = B ^ ((3 : ℝ) / 4) * B ^ 2 := by
        have h2 : B ^ (2 : ℝ) = B ^ 2 := Real.rpow_natCast B 2
        rw [← h2, ← Real.rpow_add hBpos]
        norm_num
      rw [Real.div_rpow hBpos.le hlogBpos.le, hB11]
      ring
    rw [hfac]
    calc (B / Real.log B) ^ ((3 : ℝ) / 4) * (cee * B ^ 2)
        ≤ A ^ ((3 : ℝ) / 4) * (cee * B ^ 2) :=
          mul_le_mul_of_nonneg_right hA34 (by positivity)
      _ ≤ A ^ ((3 : ℝ) / 4) * EE d n B :=
          mul_le_mul_of_nonneg_left hEE' (Real.rpow_nonneg hApos.le _)
  linarith [hsum, hkey, hEE'']

end Work.HP.MDEstimates

