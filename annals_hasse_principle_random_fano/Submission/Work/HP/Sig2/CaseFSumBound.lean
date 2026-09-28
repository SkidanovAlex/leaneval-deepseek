import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDEstimates.muXY_le
import Submission.Work.HP.MDEstimates.mu_sum_aux
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.pair_counts
import Submission.Work.HP.Sig2.ellXY_pair_le

/-!
# `Σ_{Ω(B)} 𝔡₂^{-m} ≪ B^{2r/(n+1-d)}(log B+1)^3` — self-contained copy

This is a copy of `Submission/Work/HP/Sig2/sum_dmin_rpow_le.lean` (by the `sum_dmin_rpow_le`
author), with two changes: the stale identifier `MDEstimates.detL_ge_one` (that lemma now lives
in `Work.HP.Lat.detL_ge_one`) is replaced by `Lat.detL_ge_one`, and every top-level declaration is
prefixed with `cf_` so that this module can be used alongside the original without a name clash.
Used by `Submission/Work/HP/Sig2/Sigma2_caseF.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open scoped BigOperators
open Finset

namespace Work.HP.Sig2

open Work.HP

/-! ## Elementary facts about `dmin` -/

lemma cf_dmin_nonneg' {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) (S : Set (ι → ℤ)) :
    0 ≤ dmin r S := by
  have hdef : dmin r S =
      sInf {D : ℝ | ∃ L : Submodule ℤ (ι → ℤ), rk L = r ∧ S ⊆ L ∧ detL L = D} := rfl
  rw [hdef]
  by_cases h : ({D : ℝ | ∃ L : Submodule ℤ (ι → ℤ), rk L = r ∧ S ⊆ L ∧ detL L = D} : Set ℝ).Nonempty
  · exact le_csInf h (fun D hD => by obtain ⟨L, -, -, rfl⟩ := hD; exact detL_nonneg L)
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

/-- `𝔡_r(S) ∈ {0} ∪ [1,∞)`, so `𝔡_r(S)^{-m} ≤ (max 𝔡_r(S) 1)^{-m}`. -/
lemma cf_dmin_rpow_le_max {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) (S : Set (ι → ℤ))
    {m : ℝ} (hm : 0 < m) : dmin r S ^ (-m) ≤ (max (dmin r S) 1) ^ (-m) := by
  rcases MDEstimates.dmin_eq_zero_or_le r S (c := 1)
      (fun L _ _ => Lat.detL_ge_one L) with h | h
  · rw [h, max_eq_right (by norm_num : (0:ℝ) ≤ 1), Real.zero_rpow (by linarith : (-m) ≠ 0),
      Real.one_rpow]
    norm_num
  · rw [max_eq_left h]

/-- Each summand of the second-moment sum is at most one. -/
lemma cf_dmin_rpow_neg_le_one {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) (S : Set (ι → ℤ))
    {m : ℝ} (hm : 0 < m) : dmin r S ^ (-m) ≤ 1 := by
  refine le_trans (cf_dmin_rpow_le_max r S hm) ?_
  exact Real.rpow_le_one_of_one_le_of_nonpos (le_max_right _ _) (by linarith)

/-! ## Crude counts of primitive vectors -/

lemma cf_ncard_isPrim_enorm_le (n : ℕ) (X : ℝ) :
    (({x : Fin (n + 1) → ℤ | IsPrim x ∧ eNorm x ≤ X}).ncard : ℕ)
      ≤ (2 * ⌈X⌉₊ + 1) ^ (n + 1) := by
  classical
  have hsub : {x : Fin (n + 1) → ℤ | IsPrim x ∧ eNorm x ≤ X} ⊆
      ↑(Fintype.piFinset (fun _ : Fin (n + 1) => Finset.Icc (-(⌈X⌉₊ : ℤ)) (⌈X⌉₊ : ℤ))) := by
    intro x hx
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    have h1 : |((x i : ℤ) : ℝ)| ≤ X := le_trans (abs_apply_le_eNorm x i) hx.2
    obtain ⟨h2, h3⟩ := abs_le.mp h1
    rw [Finset.mem_Icc]
    refine ⟨?_, ?_⟩
    · have h4 : ((-(⌈X⌉₊ : ℤ) : ℤ) : ℝ) ≤ (x i : ℝ) := by
        push_cast; linarith [Nat.le_ceil X]
      exact_mod_cast h4
    · have h4 : (x i : ℝ) ≤ ((⌈X⌉₊ : ℤ) : ℝ) := by
        push_cast; linarith [Nat.le_ceil X]
      exact_mod_cast h4
  calc (({x : Fin (n + 1) → ℤ | IsPrim x ∧ eNorm x ≤ X}).ncard : ℕ)
      ≤ (Fintype.piFinset (fun _ : Fin (n + 1) => Finset.Icc (-(⌈X⌉₊ : ℤ)) (⌈X⌉₊ : ℤ))).card := by
        simpa only [Set.ncard_coe_finset] using
          Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (2 * ⌈X⌉₊ + 1) ^ (n + 1) := by
        rw [Fintype.card_piFinset]
        have hc : (Finset.Icc (-(⌈X⌉₊ : ℤ)) (⌈X⌉₊ : ℤ)).card = 2 * ⌈X⌉₊ + 1 := by
          rw [Int.card_Icc]
          have h2 : (⌈X⌉₊ : ℤ) + 1 - (-(⌈X⌉₊ : ℤ)) = ((2 * ⌈X⌉₊ + 1 : ℕ) : ℤ) := by
            push_cast; ring
          rw [h2, Int.toNat_natCast]
        rw [Finset.prod_congr rfl (fun i _ => hc), Finset.prod_const, Finset.card_univ,
          Fintype.card_fin]

lemma cf_ncard_Omega_le (d n : ℕ) (B : ℝ) :
    ((Omega d n B).ncard : ℕ)
      ≤ (2 * ⌈B ^ (1 / ((n : ℝ) + 1 - d))⌉₊ + 1) ^ (2 * (n + 1)) := by
  classical
  set X : ℝ := B ^ (1 / ((n : ℝ) + 1 - d)) with hXdef
  have hXfin : (Xi d n B).Finite := (MDBasic.finite_sets d n 0 B (fun _ => True)).2.1
  have hsub : Omega d n B ⊆ (Xi d n B) ×ˢ (Xi d n B) := fun p hp => ⟨hp.1, hp.2.1⟩
  have h1 : (Omega d n B).ncard ≤ (Xi d n B).ncard * (Xi d n B).ncard := by
    calc (Omega d n B).ncard ≤ ((Xi d n B) ×ˢ (Xi d n B)).ncard :=
          Set.ncard_le_ncard hsub (hXfin.prod hXfin)
      _ = _ := Set.ncard_prod
  have h2 : (Xi d n B).ncard ≤ (2 * ⌈X⌉₊ + 1) ^ (n + 1) := by
    show (({x : Fin (n + 1) → ℤ | IsPrim x ∧ eNorm x ≤ X}).ncard : ℕ) ≤ (2 * ⌈X⌉₊ + 1) ^ (n + 1)
    exact cf_ncard_isPrim_enorm_le n X
  calc (Omega d n B).ncard ≤ (Xi d n B).ncard * (Xi d n B).ncard := h1
    _ ≤ (2 * ⌈X⌉₊ + 1) ^ (n + 1) * (2 * ⌈X⌉₊ + 1) ^ (n + 1) := Nat.mul_le_mul h2 h2
    _ = (2 * ⌈X⌉₊ + 1) ^ (2 * (n + 1)) := by rw [← pow_add]; congr 1; omega

/-! ## The dyadic decomposition -/

lemma cf_dyadic_sum_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (D : ι → ℝ) (m : ℝ) (M : ℕ)
    (hm : 0 < m) (hD1 : ∀ i ∈ s, 1 ≤ D i) (hbd : ∀ i ∈ s, D i < (2 : ℝ) ^ (M + 1)) :
    ∑ i ∈ s, D i ^ (-m) ≤
      ∑ j ∈ Finset.range (M + 1),
        ((s.filter (fun i => D i < (2 : ℝ) ^ (j + 1))).card : ℝ) * (2 : ℝ) ^ (-(m * (j : ℝ))) := by
  classical
  have hpt : ∀ i ∈ s, D i ^ (-m) ≤ ∑ j ∈ Finset.range (M + 1),
      (if D i < (2 : ℝ) ^ (j + 1) then (1 : ℝ) else 0) * (2 : ℝ) ^ (-(m * (j : ℝ))) := by
    intro i hi
    obtain ⟨K, hKspec, hKle, hKge⟩ :
        ∃ K, D i < (2 : ℝ) ^ (K + 1) ∧ K ≤ M ∧ (2 : ℝ) ^ K ≤ D i := by
      have hex : ∃ j, D i < (2 : ℝ) ^ (j + 1) := ⟨M, hbd i hi⟩
      refine ⟨Nat.find hex, Nat.find_spec hex, Nat.find_min' hex (m := M) (hbd i hi), ?_⟩
      rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
      · rw [h0]; simpa using hD1 i hi
      · obtain ⟨K', hK'⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
        have hnot : ¬ (D i < (2 : ℝ) ^ (K' + 1)) :=
          Nat.find_min hex (m := K') (by rw [hK']; exact Nat.lt_succ_self K')
        rw [hK']; exact not_lt.mp hnot
    have hKmem : K ∈ Finset.range (M + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hKle)
    have hstep : D i ^ (-m) ≤ ((2 : ℝ) ^ K) ^ (-m) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hKge (by linarith)
    have hpow : ((2 : ℝ) ^ K) ^ (-m) = (2 : ℝ) ^ (-(m * (K : ℝ))) := by
      rw [← Real.rpow_natCast 2 K, ← Real.rpow_mul (show (0:ℝ) ≤ 2 by norm_num)]
      congr 1; ring
    calc D i ^ (-m) ≤ ((2 : ℝ) ^ K) ^ (-m) := hstep
      _ = (2 : ℝ) ^ (-(m * (K : ℝ))) := hpow
      _ = (if D i < (2 : ℝ) ^ (K + 1) then (1 : ℝ) else 0) * (2 : ℝ) ^ (-(m * (K : ℝ))) := by
          rw [if_pos hKspec, one_mul]
      _ ≤ ∑ j ∈ Finset.range (M + 1),
            (if D i < (2 : ℝ) ^ (j + 1) then (1 : ℝ) else 0) * (2 : ℝ) ^ (-(m * (j : ℝ))) :=
          Finset.single_le_sum (s := Finset.range (M + 1)) (a := K)
            (f := fun j : ℕ => (if D i < (2 : ℝ) ^ (j + 1) then (1 : ℝ) else 0)
              * (2 : ℝ) ^ (-(m * (j : ℝ)))) (fun j _ => by positivity) hKmem
  calc ∑ i ∈ s, D i ^ (-m)
      ≤ ∑ i ∈ s, ∑ j ∈ Finset.range (M + 1),
          (if D i < (2 : ℝ) ^ (j + 1) then (1 : ℝ) else 0) * (2 : ℝ) ^ (-(m * (j : ℝ))) :=
        Finset.sum_le_sum hpt
    _ = ∑ j ∈ Finset.range (M + 1), ∑ i ∈ s,
          (if D i < (2 : ℝ) ^ (j + 1) then (1 : ℝ) else 0) * (2 : ℝ) ^ (-(m * (j : ℝ))) :=
        Finset.sum_comm
    _ = ∑ j ∈ Finset.range (M + 1),
          (((s.filter (fun i => D i < (2 : ℝ) ^ (j + 1))).card : ℕ) : ℝ)
            * (2 : ℝ) ^ (-(m * (j : ℝ))) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [← Finset.sum_mul, ← Finset.sum_boole]

/-- `∑_{j≤M} (j+2)² ≤ (M+3)³`. -/
lemma cf_sum_sq_shift_le (M : ℕ) :
    ∑ j ∈ Finset.range (M + 1), ((j : ℝ) + 2) ^ 2 ≤ ((M : ℝ) + 3) ^ 3 := by
  have h1 : ∀ j ∈ Finset.range (M + 1), ((j : ℝ) + 2) ^ 2 ≤ ((M : ℝ) + 2) ^ 2 := by
    intro j hj
    have hj' : (j : ℝ) + 2 ≤ (M : ℝ) + 2 := by
      have : j ≤ M := by simpa [Nat.lt_succ_iff] using Finset.mem_range.mp hj
      have hcast : (j : ℝ) ≤ (M : ℝ) := by exact_mod_cast this
      linarith
    exact pow_le_pow_left₀ (by positivity) hj' 2
  have h2 : ∑ j ∈ Finset.range (M + 1), ((j : ℝ) + 2) ^ 2
      ≤ ((M : ℝ) + 1) * ((M : ℝ) + 2) ^ 2 := by
    refine le_trans (Finset.sum_le_sum h1) (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_range]
    simp only [nsmul_eq_mul]
    push_cast
    ring
  refine le_trans h2 ?_
  nlinarith [sq_nonneg ((M:ℝ) + 2), (Nat.cast_nonneg M : (0:ℝ) ≤ (M:ℝ))]

theorem cf_sum_dmin_rpow_le (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ (r : ℕ), 2 ≤ r → r ≤ n + 1 → ∀ (m B : ℝ), (n : ℝ) - 1 ≤ m → 1 ≤ B →
      (∑ᶠ p ∈ Omega d n B, (dmin r ({p.1, p.2} : Set (Fin (n + 1) → ℤ))) ^ (-m))
        ≤ K * B ^ (2 * (r : ℝ) / ((n : ℝ) + 1 - d)) * (Real.log B + 1) ^ 3 := by
  classical
  have hn2 : 2 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- uniform pair-count constant over all r ∈ [2, n+1]
  obtain ⟨C0, hC0pos, hC0⟩ : ∃ C0 : ℝ, 0 < C0 ∧ ∀ r : ℕ, 2 ≤ r → r ≤ n + 1 →
      ∀ X Δ : ℝ, 1 ≤ X → 1 ≤ Δ →
      (ellXY n r X X Δ : ℝ) ≤ C0 * X ^ (2 * r) * Δ ^ (n - 1) * Real.log (2 * Δ) ^ (2 * min (r - 2) 1) := by
    let g : ℕ → ℝ := fun r =>
      if h : 2 ≤ r ∧ r ≤ n + 1 then Classical.choose (ellXY_pair_le n hn2 r h.1 h.2) else 1
    have hg : ∀ r : ℕ, 2 ≤ r → r ≤ n + 1 → 0 < g r ∧ ∀ X Δ : ℝ, 1 ≤ X → 1 ≤ Δ →
        (ellXY n r X X Δ : ℝ) ≤ g r * X ^ (2 * r) * Δ ^ (n - 1) * Real.log (2 * Δ) ^ (2 * min (r - 2) 1) := by
      intro r hr hrn
      rw [show g r = Classical.choose (ellXY_pair_le n hn2 r hr hrn) from dif_pos ⟨hr, hrn⟩]
      exact Classical.choose_spec (ellXY_pair_le n hn2 r hr hrn)
    have hne : (Finset.Icc 2 (n + 1)).Nonempty :=
      ⟨2, by simp only [Finset.mem_Icc]; omega⟩
    refine ⟨(Finset.Icc 2 (n + 1)).sup' hne g, ?_, ?_⟩
    · refine lt_of_lt_of_le (hg 2 le_rfl (by omega)).1 ?_
      exact Finset.le_sup' g (by simp only [Finset.mem_Icc]; omega)
    · intro r hr hrn X Δ hX hΔ
      have hle : g r ≤ (Finset.Icc 2 (n + 1)).sup' hne g :=
        Finset.le_sup' g (by simp only [Finset.mem_Icc]; exact ⟨hr, hrn⟩)
      have hkey := (hg r hr hrn).2 X Δ hX hΔ
      have hK : (0:ℝ) ≤ X ^ (2 * r) * Δ ^ (n - 1) * Real.log (2 * Δ) ^ (2 * min (r - 2) 1) :=
        mul_nonneg (mul_nonneg (pow_nonneg (by linarith) _) (pow_nonneg (by linarith) _))
          (pow_nonneg (Real.log_nonneg (by linarith)) _)
      calc (ellXY n r X X Δ : ℝ)
          ≤ g r * X ^ (2*r) * Δ^(n-1) * Real.log (2*Δ)^(2*min (r-2) 1) := hkey
        _ = g r * (X ^ (2*r) * Δ^(n-1) * Real.log (2*Δ)^(2*min (r-2) 1)) := by ring
        _ ≤ (Finset.Icc 2 (n+1)).sup' hne g
              * (X ^ (2*r) * Δ^(n-1) * Real.log (2*Δ)^(2*min (r-2) 1)) :=
            mul_le_mul_of_nonneg_right hle hK
        _ = (Finset.Icc 2 (n+1)).sup' hne g * X ^ (2*r) * Δ^(n-1)
              * Real.log (2*Δ)^(2*min (r-2) 1) := by ring
  set A : ℝ := (2:ℝ) ^ (n - 1) * (Real.log 2 + 1) ^ 2 * (2 / Real.log 2 + 5) ^ 3 with hAdef
  set Kc : ℝ := C0 * A + (5:ℝ) ^ (2 * (n + 1)) + (3:ℝ) ^ (2 * (n + 1)) with hKcdef
  have hApos : 0 < A := by
    rw [hAdef]
    refine mul_pos (mul_pos (by positivity) (pow_pos (by linarith) 2)) (pow_pos ?_ 3)
    have := div_pos (by norm_num : (0:ℝ) < 2) hlog2pos
    linarith
  have hKcpos : 0 < Kc := by rw [hKcdef]; positivity
  refine ⟨Kc, hKcpos, ?_⟩
  intro r hr hrn m B hm hB
  have hm2 : 0 < m := by
    have : (2:ℝ) ≤ m := by
      have : (2:ℝ) ≤ (n:ℝ) - 1 := by
        have : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
        linarith
      linarith
    linarith
  have hB0 : (0:ℝ) ≤ B := le_trans zero_le_one hB
  -- ==== Case d ≤ n : main ====
  by_cases hdn : d ≤ n
  · have he1 : 1 ≤ (n:ℝ) + 1 - d := by
      have : (d:ℝ) ≤ (n:ℝ) := by exact_mod_cast hdn
      linarith
    set e : ℝ := (n:ℝ) + 1 - d with hedef
    set X : ℝ := B ^ (1 / e) with hXdef
    have hX1 : 1 ≤ X := by rw [hXdef]; exact Real.one_le_rpow hB (by positivity)
    have hX0 : 0 < X := lt_of_lt_of_le one_pos hX1
    have hOfin : (Omega d n B).Finite := (MDBasic.finite_sets d n 0 B (fun _ => True)).2.2
    set f : (Fin (n+1) → ℤ) × (Fin (n+1) → ℤ) → ℝ :=
      fun p => (dmin r ({p.1, p.2} : Set (Fin (n+1) → ℤ))) ^ (-m) with hfdef
    have hsupp : ((Omega d n B) ∩ Function.support f).Finite := hOfin.subset Set.inter_subset_left
    rw [finsum_mem_eq_sum f hsupp]
    set D : (Fin (n+1) → ℤ) × (Fin (n+1) → ℤ) → ℝ :=
      fun p => max (dmin r ({p.1, p.2} : Set (Fin (n+1) → ℤ))) 1 with hDdef
    have hD1 : ∀ p ∈ hsupp.toFinset, 1 ≤ D p := fun p _ => by rw [hDdef]; exact le_max_right _ _
    have hdmin_le_D : ∀ p ∈ hsupp.toFinset, f p ≤ D p ^ (-m) := by
      intro p hp
      rw [hfdef, hDdef]
      exact cf_dmin_rpow_le_max r _ hm2
    have hs_mem : ∀ p ∈ hsupp.toFinset, p ∈ Omega d n B := by
      intro p hp
      rw [Set.Finite.mem_toFinset] at hp
      exact hp.1
    -- the split point
    set M : ℕ := ⌈Real.logb 2 (X^2)⌉₊ + 1 with hMdef
    have hXM : X ^ 2 < (2:ℝ) ^ (M + 1) := by
      have hL : X ^ 2 ≤ (2:ℝ) ^ (⌈Real.logb 2 (X^2)⌉₊) := by
        have h1 := (Real.logb_le_iff_le_rpow (b := 2) (x := X^2)
          (y := ((⌈Real.logb 2 (X^2)⌉₊ : ℕ) : ℝ)) (by norm_num) (by positivity)).mp
          (Nat.le_ceil (Real.logb 2 (X^2)))
        rwa [Real.rpow_natCast] at h1
      rw [hMdef, show ⌈Real.logb 2 (X^2)⌉₊ + 1 + 1 = ⌈Real.logb 2 (X^2)⌉₊ + 2 from by omega,
        pow_add]
      nlinarith [hL, sq_pos_of_pos hX0]
    have hbd : ∀ p ∈ hsupp.toFinset.filter (fun p => D p ≤ X^2), D p < (2:ℝ) ^ (M + 1) := by
      intro p hp
      have hp2 : D p ≤ X^2 := (Finset.mem_filter.mp hp).2
      linarith
    have hdya := cf_dyadic_sum_le (hsupp.toFinset.filter (fun p => D p ≤ X^2)) D m M hm2
      (fun p hp => hD1 p (Finset.mem_of_mem_filter p hp)) hbd
    -- per-term bound
    have hterm : ∀ j ∈ Finset.range (M + 1),
        (((hsupp.toFinset.filter (fun p => D p ≤ X^2)).filter
            (fun p => D p < (2:ℝ) ^ (j + 1))).card : ℝ) * (2:ℝ) ^ (-(m * (j:ℝ)))
          ≤ (C0 * X ^ (2*r) * (2:ℝ) ^ (n - 1) * (Real.log 2 + 1) ^ 2) * ((j:ℝ) + 2) ^ 2 := by
      intro j hj
      set Fj : Finset ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ)) :=
        (hsupp.toFinset.filter (fun p => D p ≤ X^2)).filter (fun p => D p < (2:ℝ) ^ (j + 1)) with hFj
      have hsubE : (↑Fj : Set ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ))) ⊆
          {q : (Fin (n+1) → ℤ) × (Fin (n+1) → ℤ) | LinearIndependent ℤ ![q.1, q.2] ∧
            eNorm q.1 ≤ X ∧ eNorm q.2 ≤ X ∧ dmin r {q.1, q.2} ≤ (2:ℝ) ^ (j + 1)} := by
        intro q hq
        rw [Finset.mem_coe, hFj, Finset.mem_filter] at hq
        obtain ⟨hq1, hq2⟩ := hq
        rw [Finset.mem_filter] at hq1
        obtain ⟨hq1s, hq1D⟩ := hq1
        have hqO : q ∈ Omega d n B := hs_mem q hq1s
        have hxprim : IsPrim q.1 := hqO.1.1
        have hyprim : IsPrim q.2 := hqO.2.1.1
        have hne1 : q.1 ≠ q.2 := hqO.2.2.1
        have hne2 : q.1 ≠ -q.2 := hqO.2.2.2
        have hxn : eNorm q.1 ≤ X := by
          have h := hqO.1.2
          change eNorm q.1 ≤ B ^ (1 / e) at h
          rw [hXdef]; exact h
        have hyn : eNorm q.2 ≤ X := by
          have h := hqO.2.1.2
          change eNorm q.2 ≤ B ^ (1 / e) at h
          rw [hXdef]; exact h
        exact ⟨MDEstimates.linIndep_of_ne_pm hxprim hyprim hne1 hne2, hxn, hyn,
          le_trans (le_max_left _ _) (le_of_lt hq2)⟩
      have hfinE : ({q : (Fin (n+1) → ℤ) × (Fin (n+1) → ℤ) | LinearIndependent ℤ ![q.1, q.2] ∧
            eNorm q.1 ≤ X ∧ eNorm q.2 ≤ X ∧ dmin r {q.1, q.2} ≤ (2:ℝ) ^ (j + 1)} : Set _).Finite :=
        ((MDBasic.finite_eNorm_le X).prod (MDBasic.finite_eNorm_le X)).subset
          (fun q hq => ⟨hq.2.1, hq.2.2.1⟩)
      have hcard : ((Fj.card : ℕ) : ℝ) ≤ (ellXY n r X X ((2:ℝ) ^ (j + 1)) : ℝ) := by
        have h1 := Set.ncard_le_ncard hsubE hfinE
        rw [Set.ncard_coe_finset] at h1
        exact_mod_cast h1
      have hell : (ellXY n r X X ((2:ℝ) ^ (j + 1)) : ℝ)
          ≤ C0 * X ^ (2 * r) * ((2:ℝ) ^ (j + 1)) ^ (n - 1)
            * Real.log (2 * ((2:ℝ) ^ (j + 1))) ^ (2 * min (r - 2) 1) :=
        hC0 r hr hrn X ((2:ℝ) ^ (j + 1)) hX1 (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2))
      have harith : C0 * X ^ (2 * r) * ((2:ℝ) ^ (j + 1)) ^ (n - 1)
            * Real.log (2 * ((2:ℝ) ^ (j + 1))) ^ (2 * min (r - 2) 1)
            * (2:ℝ) ^ (-(m * (j:ℝ)))
          ≤ (C0 * X ^ (2*r) * (2:ℝ) ^ (n - 1) * (Real.log 2 + 1) ^ 2) * ((j:ℝ) + 2) ^ 2 := by
        have hlog2 : Real.log (2 * (2:ℝ) ^ (j + 1)) = ((j:ℝ) + 2) * Real.log 2 := by
          rw [show (2:ℝ) * (2:ℝ) ^ (j + 1) = (2:ℝ) ^ (j + 2) from by rw [pow_succ]; ring,
            Real.log_pow]
          push_cast; ring
        have hj2 : (1:ℝ) ≤ (j:ℝ) + 2 := by
          have : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
          linarith
        have hlogpow : Real.log (2 * (2:ℝ) ^ (j + 1)) ^ (2 * min (r - 2) 1)
            ≤ ((j:ℝ) + 2) ^ 2 * (Real.log 2 + 1) ^ 2 := by
          rw [hlog2]
          have hle1 : (((j:ℝ)+2) * Real.log 2) ^ 2 ≤ ((j:ℝ)+2)^2 * (Real.log 2 + 1)^2 := by
            have h1 : ((j:ℝ)+2) * Real.log 2 ≤ ((j:ℝ)+2) * (Real.log 2 + 1) :=
              mul_le_mul_of_nonneg_left (by linarith) (by linarith : (0:ℝ) ≤ (j:ℝ)+2)
            calc (((j:ℝ)+2) * Real.log 2)^2 ≤ (((j:ℝ)+2) * (Real.log 2+1))^2 :=
                  pow_le_pow_left₀ (by positivity) h1 2
              _ = ((j:ℝ)+2)^2 * (Real.log 2 + 1)^2 := by ring
          rcases Nat.eq_zero_or_pos (min (r - 2) 1) with h0 | hpos
          · rw [show 2 * min (r-2) 1 = 0 from by omega, pow_zero]
            have h4 : (1:ℝ) ≤ ((j:ℝ)+2)^2 * (Real.log 2+1)^2 := by
              have h6 : (1:ℝ) ≤ Real.log 2 + 1 := by linarith
              nlinarith [sq_nonneg ((j:ℝ)+2), sq_nonneg (Real.log 2+1), hj2, h6]
            exact h4
          · have hmin1 : min (r-2) 1 = 1 := by omega
            rw [hmin1]
            exact le_trans (le_of_eq (by ring : (((j:ℝ)+2) * Real.log 2)^2
              = (((j:ℝ)+2) * Real.log 2)^(2:ℕ))) hle1
        have h2pow : ((2:ℝ) ^ (j + 1)) ^ (n - 1) * (2:ℝ) ^ (-(m * (j:ℝ))) ≤ (2:ℝ) ^ (n - 1) := by
          rw [← pow_mul, ← Real.rpow_natCast 2 ((j+1)*(n-1)),
            ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
          have hexp : ((((j+1)*(n-1) : ℕ) : ℝ)) + (-(m * (j:ℝ))) ≤ ((n:ℝ) - 1) := by
            have h1 : ((((j+1)*(n-1) : ℕ) : ℝ)) = ((j:ℝ)+1) * ((n:ℝ)-1) := by
              rw [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_sub hn1]
              push_cast; ring
            rw [h1]
            nlinarith [(Nat.cast_nonneg j : (0:ℝ) ≤ (j:ℝ)), hm]
          have h2 : (2:ℝ) ^ (n - 1) = (2:ℝ) ^ ((n:ℝ) - 1) := by
            rw [← Real.rpow_natCast 2 (n-1), Nat.cast_sub hn1]; push_cast; ring
          rw [h2]
          exact (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mpr hexp
        calc C0 * X ^ (2 * r) * ((2:ℝ) ^ (j + 1)) ^ (n - 1)
              * Real.log (2 * ((2:ℝ) ^ (j + 1))) ^ (2 * min (r - 2) 1) * (2:ℝ) ^ (-(m * (j:ℝ)))
            = (C0 * X ^ (2*r)) * (Real.log (2 * ((2:ℝ) ^ (j+1))) ^ (2*min (r-2) 1)
                * (((2:ℝ) ^ (j + 1)) ^ (n - 1) * (2:ℝ) ^ (-(m * (j:ℝ))))) := by ring
          _ ≤ (C0 * X ^ (2*r)) * ((((j:ℝ) + 2) ^ 2 * (Real.log 2 + 1) ^ 2) * (2:ℝ) ^ (n - 1)) := by
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact mul_le_mul hlogpow h2pow (by positivity) (by positivity)
          _ = (C0 * X ^ (2*r) * (2:ℝ) ^ (n - 1) * (Real.log 2 + 1) ^ 2) * ((j:ℝ) + 2) ^ 2 := by ring
      calc (((Fj.card : ℕ)) : ℝ) * (2:ℝ) ^ (-(m * (j:ℝ)))
          ≤ (ellXY n r X X ((2:ℝ) ^ (j + 1)) : ℝ) * (2:ℝ) ^ (-(m * (j:ℝ))) :=
            mul_le_mul_of_nonneg_right hcard (by positivity)
        _ ≤ (C0 * X ^ (2 * r) * ((2:ℝ) ^ (j + 1)) ^ (n - 1)
              * Real.log (2 * ((2:ℝ) ^ (j + 1))) ^ (2 * min (r - 2) 1)) * (2:ℝ) ^ (-(m * (j:ℝ))) :=
            mul_le_mul_of_nonneg_right hell (by positivity)
        _ ≤ (C0 * X ^ (2*r) * (2:ℝ) ^ (n - 1) * (Real.log 2 + 1) ^ 2) * ((j:ℝ) + 2) ^ 2 := harith
    have h4log : Real.log X ≤ Real.log B := by
      rw [hXdef, Real.log_rpow (lt_of_lt_of_le one_pos hB)]
      have h5 : 1 / e ≤ 1 := by rw [div_le_one (by linarith [he1])]; linarith [he1]
      nlinarith [Real.log_nonneg hB, h5]
    have hM3 : ((M:ℝ) + 3) ≤ (2 / Real.log 2 + 5) * (Real.log X + 1) := by
      have hlX2nn : (0:ℝ) ≤ Real.logb 2 (X^2) := Real.logb_nonneg (by norm_num) (by nlinarith [hX1])
      have h2 : ((⌈Real.logb 2 (X^2)⌉₊ : ℕ) : ℝ) < Real.logb 2 (X^2) + 1 :=
        Nat.ceil_lt_add_one hlX2nn
      have h1 : ((M:ℝ)) ≤ Real.logb 2 (X^2) + 2 := by
        rw [hMdef]; push_cast; linarith
      have h3 : Real.logb 2 (X^2) = 2 * Real.log X / Real.log 2 := by
        rw [Real.logb, Real.log_pow]; ring
      rw [h3] at h1
      have hL0 : (0:ℝ) ≤ Real.log X := Real.log_nonneg hX1
      have key : 2 * Real.log X / Real.log 2 + 5 ≤ (2 / Real.log 2 + 5) * (Real.log X + 1) := by
        have h2' : (2 / Real.log 2 + 5) * (Real.log X + 1)
            = 2 * Real.log X / Real.log 2 + 5 + (5 * Real.log X + 2 / Real.log 2) := by ring
        rw [h2']
        have h3' : (0:ℝ) ≤ 5 * Real.log X := by linarith
        have h4' : (0:ℝ) ≤ 2 / Real.log 2 := by positivity
        linarith
      linarith
    have hfirst : ∑ p ∈ hsupp.toFinset.filter (fun p => D p ≤ X^2), D p ^ (-m)
        ≤ C0 * A * (Real.log B + 1) ^ 3 * X ^ (2*r) := by
      refine le_trans hdya ?_
      have hsum : (∑ j ∈ Finset.range (M + 1),
            (((hsupp.toFinset.filter (fun p => D p ≤ X^2)).filter
              (fun p => D p < (2:ℝ) ^ (j+1))).card : ℝ) * (2:ℝ) ^ (-(m * (j:ℝ))))
          ≤ (C0 * X ^ (2*r) * (2:ℝ) ^ (n - 1) * (Real.log 2 + 1) ^ 2)
            * ∑ j ∈ Finset.range (M + 1), ((j:ℝ) + 2) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum (fun j hj => ?_)
        exact hterm j hj
      have hstep : (C0 * X ^ (2*r) * (2:ℝ) ^ (n - 1) * (Real.log 2 + 1) ^ 2)
            * ((M:ℝ) + 3) ^ 3
          ≤ C0 * A * (Real.log B + 1) ^ 3 * X ^ (2*r) := by
        have hcube : ((M:ℝ) + 3) ^ 3 ≤ ((2 / Real.log 2 + 5) * (Real.log B + 1)) ^ 3 := by
          refine pow_le_pow_left₀ (by positivity) ?_ 3
          have h5 : (2 / Real.log 2 + 5) * (Real.log X + 1)
              ≤ (2 / Real.log 2 + 5) * (Real.log B + 1) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            linarith [h4log]
          linarith
        calc (C0 * X ^ (2*r) * (2:ℝ) ^ (n - 1) * (Real.log 2 + 1) ^ 2) * ((M:ℝ) + 3) ^ 3
            ≤ (C0 * X ^ (2*r) * (2:ℝ) ^ (n - 1) * (Real.log 2 + 1) ^ 2)
              * ((2 / Real.log 2 + 5) * (Real.log B + 1)) ^ 3 :=
              mul_le_mul_of_nonneg_left hcube (by positivity)
          _ = C0 * A * (Real.log B + 1) ^ 3 * X ^ (2*r) := by
              rw [hAdef]; ring
      refine le_trans hsum ?_
      refine le_trans (mul_le_mul_of_nonneg_left (cf_sum_sq_shift_le M) (by positivity)) ?_
      exact hstep
    have hsecond : ∑ p ∈ hsupp.toFinset.filter (fun p => ¬ (D p ≤ X^2)), D p ^ (-m)
        ≤ (5:ℝ) ^ (2 * (n + 1)) * X ^ (2*r) * (Real.log B + 1) ^ 3 := by
      have hcardO : ((hsupp.toFinset.card : ℕ) : ℝ) ≤ ((Omega d n B).ncard : ℝ) := by
        have hsub : (↑hsupp.toFinset : Set ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ))) ⊆ Omega d n B := by
          rw [Set.Finite.coe_toFinset hsupp]; exact Set.inter_subset_left
        have h2 := Set.ncard_le_ncard hsub hOfin
        rw [Set.ncard_coe_finset] at h2
        exact_mod_cast h2
      have hcard5 : ((hsupp.toFinset.card : ℕ) : ℝ) ≤ (5 * X) ^ (2 * (n + 1)) := by
        refine le_trans hcardO ?_
        have hXceil : B ^ (1 / ((n:ℝ) + 1 - d)) = X := by rw [hXdef, ← hedef]
        have h2 : ((Omega d n B).ncard : ℝ)
            ≤ (2 * ⌈B ^ (1 / ((n:ℝ) + 1 - d))⌉₊ + 1) ^ (2 * (n + 1)) := by
          exact_mod_cast cf_ncard_Omega_le d n B
        refine le_trans h2 ?_
        rw [hXceil]
        have h4 : (2 * (⌈X⌉₊ : ℝ) + 1) ≤ 5 * X := by
          have h5 : (⌈X⌉₊ : ℝ) ≤ X + 1 := le_of_lt (Nat.ceil_lt_add_one (le_of_lt hX0))
          linarith
        exact pow_le_pow_left₀ (by positivity) h4 _
      have hsum2 : ∑ p ∈ hsupp.toFinset.filter (fun p => ¬ (D p ≤ X^2)), D p ^ (-m)
          ≤ ((hsupp.toFinset.filter (fun p => ¬ (D p ≤ X^2))).card : ℝ) * (X^2) ^ (-m) := by
        calc ∑ p ∈ hsupp.toFinset.filter (fun p => ¬ (D p ≤ X^2)), D p ^ (-m)
            ≤ ∑ p ∈ hsupp.toFinset.filter (fun p => ¬ (D p ≤ X^2)), (X^2) ^ (-m) := by
              refine Finset.sum_le_sum (fun p hp => ?_)
              have hp2 : ¬ (D p ≤ X^2) := (Finset.mem_filter.mp hp).2
              exact Real.rpow_le_rpow_of_nonpos (by positivity) (le_of_lt (not_le.mp hp2)) (by linarith)
          _ = ((hsupp.toFinset.filter (fun p => ¬ (D p ≤ X^2))).card : ℝ) * (X^2) ^ (-m) := by
              rw [Finset.sum_const]
              simp only [nsmul_eq_mul]
      have hcard2 : (((hsupp.toFinset.filter (fun p => ¬ (D p ≤ X^2))).card : ℕ) : ℝ)
          ≤ (5 * X) ^ (2 * (n + 1)) :=
        le_trans (by exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)) hcard5
      have hfinal2 : (5 * X) ^ (2 * (n + 1)) * (X^2) ^ (-m)
          ≤ (5:ℝ) ^ (2 * (n + 1)) * X ^ (2*r) * (Real.log B + 1) ^ 3 := by
        have hX2m : (X^2) ^ (-m) = X ^ (-(2*m)) := by
          rw [← Real.rpow_natCast X 2, ← Real.rpow_mul hX0.le]
          congr 1; ring
        have h5X : (5 * X) ^ (2 * (n + 1)) = (5:ℝ) ^ (2 * (n + 1)) * X ^ (2 * (n + 1)) := by
          rw [mul_pow]
        have hr3 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
        have hexp : (2:ℝ) * ((n:ℝ) + 1) + (-(2*m)) ≤ (2:ℝ) * r := by
          have h' : (2:ℝ) * ((n:ℝ) + 1) - 2 * m ≤ (2:ℝ) * r := by
            nlinarith [hm, hr3, (Nat.cast_nonneg n : (0:ℝ) ≤ (n:ℝ))]
          linarith
        have hXp : X ^ (2 * (n + 1)) * X ^ (-(2*m))
            = X ^ ((2:ℝ) * ((n:ℝ) + 1) + (-(2*m))) := by
          rw [← Real.rpow_natCast X (2 * (n+1)), ← Real.rpow_add hX0]
          congr 1
          push_cast; ring
        have hXr : X ^ ((2:ℝ) * ((n:ℝ) + 1) + (-(2*m))) ≤ X ^ ((2:ℝ) * r) := by
          rcases lt_or_eq_of_le hX1 with hlt | heq
          · exact (Real.rpow_le_rpow_left_iff hlt).mpr hexp
          · rw [← heq, Real.one_rpow, Real.one_rpow]
        have hX2r : X ^ ((2:ℝ) * r) = X ^ (2 * r) := by
          rw [← Real.rpow_natCast X (2*r)]; congr 1; push_cast; ring
        rw [hX2r] at hXr
        have hlog1 : (1:ℝ) ≤ (Real.log B + 1) ^ 3 := by
          have := Real.log_nonneg hB
          nlinarith [sq_nonneg (Real.log B + 1)]
        rw [h5X, hX2m]
        calc (5:ℝ) ^ (2 * (n + 1)) * X ^ (2 * (n + 1)) * X ^ (-(2*m))
            = (5:ℝ) ^ (2 * (n + 1)) * (X ^ (2 * (n + 1)) * X ^ (-(2*m))) := by ring
          _ = (5:ℝ) ^ (2 * (n + 1)) * X ^ ((2:ℝ) * ((n:ℝ) + 1) + (-(2*m))) := by rw [hXp]
          _ ≤ (5:ℝ) ^ (2 * (n + 1)) * X ^ (2 * r) := mul_le_mul_of_nonneg_left hXr (by positivity)
          _ ≤ (5:ℝ) ^ (2 * (n + 1)) * X ^ (2 * r) * (Real.log B + 1) ^ 3 :=
              le_mul_of_one_le_right (by positivity) hlog1
      calc ∑ p ∈ hsupp.toFinset.filter (fun p => ¬ (D p ≤ X^2)), D p ^ (-m)
          ≤ ((hsupp.toFinset.filter (fun p => ¬ (D p ≤ X^2))).card : ℝ) * (X^2) ^ (-m) := hsum2
        _ ≤ (5 * X) ^ (2 * (n + 1)) * (X^2) ^ (-m) :=
            mul_le_mul_of_nonneg_right hcard2 (by positivity)
        _ ≤ (5:ℝ) ^ (2 * (n + 1)) * X ^ (2*r) * (Real.log B + 1) ^ 3 := hfinal2
    have hXpow : X ^ (2 * r) = B ^ (2 * (r:ℝ) / e) := by
      rw [hXdef, ← Real.rpow_natCast (B ^ (1/e)) (2*r), ← Real.rpow_mul hB0]
      congr 1
      push_cast
      ring
    have hsplit : ∑ p ∈ hsupp.toFinset, D p ^ (-m)
        = ∑ p ∈ hsupp.toFinset.filter (fun p => D p ≤ X^2), D p ^ (-m)
          + ∑ p ∈ hsupp.toFinset.filter (fun p => ¬ (D p ≤ X^2)), D p ^ (-m) :=
      (Finset.sum_filter_add_sum_filter_not (s := hsupp.toFinset) (p := fun p => D p ≤ X^2)
        (f := fun p => D p ^ (-m))).symm
    calc ∑ p ∈ hsupp.toFinset, f p
        ≤ ∑ p ∈ hsupp.toFinset, D p ^ (-m) := Finset.sum_le_sum hdmin_le_D
      _ = _ := hsplit
      _ ≤ C0 * A * (Real.log B + 1) ^ 3 * X ^ (2*r)
            + (5:ℝ) ^ (2 * (n + 1)) * X ^ (2*r) * (Real.log B + 1) ^ 3 := add_le_add hfirst hsecond
      _ = (C0 * A + (5:ℝ) ^ (2 * (n + 1))) * X ^ (2*r) * (Real.log B + 1) ^ 3 := by ring
      _ ≤ Kc * B ^ (2 * (r:ℝ) / e) * (Real.log B + 1) ^ 3 := by
          have hKcAB : C0 * A + (5:ℝ) ^ (2 * (n + 1)) ≤ Kc := by
            rw [hKcdef]
            have h6 : (0:ℝ) ≤ (3:ℝ) ^ (2 * (n + 1)) := by positivity
            linarith
          have hlog1 : (0:ℝ) ≤ (Real.log B + 1) ^ 3 :=
            pow_nonneg (by have := Real.log_nonneg hB; linarith) 3
          rw [← hXpow]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hKcAB (by positivity)) hlog1
  -- ==== Case d > n ====
  · have hle0 : (n:ℝ) + 1 - d ≤ 0 := by
      have h : (n:ℝ) + 1 ≤ (d:ℝ) := by exact_mod_cast (by omega : n + 1 ≤ d)
      linarith
    have hXle1 : B ^ (1 / ((n:ℝ) + 1 - d)) ≤ 1 := by
      refine Real.rpow_le_one_of_one_le_of_nonpos hB ?_
      rcases lt_or_eq_of_le hle0 with hlt | heq
      · exact le_of_lt (div_neg_of_pos_of_neg one_pos hlt)
      · rw [heq, one_div, inv_zero]
    have hLHS_le : (∑ᶠ p ∈ Omega d n B, (dmin r ({p.1, p.2} : Set (Fin (n+1) → ℤ))) ^ (-m))
        ≤ (3:ℝ) ^ (2 * (n + 1)) := by
      have hOfin : (Omega d n B).Finite := (MDBasic.finite_sets d n 0 B (fun _ => True)).2.2
      have hsupp : ((Omega d n B) ∩ Function.support (fun p : (Fin (n+1) → ℤ) × (Fin (n+1) → ℤ) =>
          (dmin r ({p.1, p.2} : Set (Fin (n+1) → ℤ))) ^ (-m))).Finite :=
        hOfin.subset Set.inter_subset_left
      rw [finsum_mem_eq_sum _ hsupp]
      have hcardO : ((hsupp.toFinset.card : ℕ) : ℝ) ≤ ((Omega d n B).ncard : ℝ) := by
        have hsub : (↑hsupp.toFinset : Set ((Fin (n+1) → ℤ) × (Fin (n+1) → ℤ))) ⊆ Omega d n B := by
          rw [Set.Finite.coe_toFinset hsupp]; exact Set.inter_subset_left
        have h2 := Set.ncard_le_ncard hsub hOfin
        rw [Set.ncard_coe_finset] at h2
        exact_mod_cast h2
      have hcard3 : ((Omega d n B).ncard : ℝ) ≤ (3:ℝ) ^ (2 * (n + 1)) := by
        have hceil : (⌈B ^ (1 / ((n:ℝ) + 1 - d))⌉₊ : ℝ) ≤ 1 := by
          have h2 : ⌈B ^ (1 / ((n:ℝ) + 1 - d))⌉₊ ≤ 1 :=
            le_trans (Nat.ceil_mono hXle1) (by norm_num)
          exact_mod_cast h2
        have hbase : (2 * ⌈B ^ (1 / ((n:ℝ) + 1 - d))⌉₊ + 1 : ℕ) ≤ 3 := by
          have h2 : ((2 * ⌈B ^ (1 / ((n:ℝ) + 1 - d))⌉₊ + 1 : ℕ) : ℝ) ≤ 3 := by push_cast; linarith
          exact_mod_cast h2
        calc ((Omega d n B).ncard : ℝ)
            ≤ ((2 * ⌈B ^ (1 / ((n:ℝ) + 1 - d))⌉₊ + 1 : ℕ) : ℝ) ^ (2 * (n + 1)) := by
              exact_mod_cast cf_ncard_Omega_le d n B
          _ ≤ (3:ℝ) ^ (2 * (n + 1)) := by
              refine pow_le_pow_left₀ (by positivity) ?_ _
              exact_mod_cast hbase
      calc ∑ p ∈ hsupp.toFinset, (dmin r ({p.1, p.2} : Set (Fin (n+1) → ℤ))) ^ (-m)
          ≤ ∑ p ∈ hsupp.toFinset, (1:ℝ) := by
            refine Finset.sum_le_sum (fun p hp => ?_)
            exact cf_dmin_rpow_neg_le_one r _ hm2
        _ = (hsupp.toFinset.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
        _ ≤ (3:ℝ) ^ (2 * (n + 1)) := le_trans hcardO hcard3
    rcases lt_or_eq_of_le hle0 with hlt | heq
    · by_cases hB1 : B = 1
      · subst hB1
        rw [Real.one_rpow, Real.log_one]
        norm_num
        refine le_trans hLHS_le ?_
        rw [hKcdef]
        have h5 : (0:ℝ) ≤ (5:ℝ) ^ (2 * (n + 1)) := by positivity
        have h6 : (0:ℝ) ≤ C0 * A := by positivity
        linarith
      · have hBgt : 1 < B := lt_of_le_of_ne hB (Ne.symm hB1)
        have hXlt1 : B ^ (1 / ((n:ℝ) + 1 - d)) < 1 := by
          refine (Real.rpow_lt_one_iff_of_pos (lt_of_lt_of_le one_pos hB)).mpr (Or.inl ⟨hBgt, ?_⟩)
          exact div_neg_of_pos_of_neg one_pos hlt
        have hXi_empty : Xi d n B = ∅ := by
          refine Set.not_nonempty_iff_eq_empty.mp ?_
          rintro ⟨x, hx⟩
          have h1 : (1:ℝ) ≤ eNorm x := one_le_eNorm_of_ne_zero (MDEstimates.isPrim_ne_zero hx.1)
          have h2 : eNorm x ≤ B ^ (1 / ((n:ℝ) + 1 - d)) := hx.2
          linarith
        have hOm_empty : Omega d n B = ∅ := by
          refine Set.not_nonempty_iff_eq_empty.mp ?_
          rintro ⟨p, hp⟩
          have hmem : p.1 ∈ (∅ : Set (Fin (n+1) → ℤ)) := hXi_empty ▸ hp.1
          simpa using hmem
        rw [hOm_empty, finsum_mem_empty]
        exact mul_nonneg (mul_nonneg hKcpos.le (Real.rpow_nonneg hB0 _))
          (pow_nonneg (by have := Real.log_nonneg hB; linarith) 3)
    · rw [heq]
      have h1 : B ^ (2 * (r:ℝ) / 0) = 1 := by rw [div_zero, Real.rpow_zero]
      rw [h1, mul_one]
      have hlogB1 : (1:ℝ) ≤ (Real.log B + 1) ^ 3 := by
        have := Real.log_nonneg hB
        nlinarith [sq_nonneg (Real.log B + 1)]
      refine le_trans hLHS_le ?_
      have h3 : (3:ℝ) ^ (2 * (n + 1)) ≤ Kc := by
        rw [hKcdef]
        have h5 : (0:ℝ) ≤ (5:ℝ) ^ (2 * (n + 1)) := by positivity
        have h6 : (0:ℝ) ≤ C0 * A := by positivity
        linarith
      nlinarith [hlogB1, h3, hKcpos.le]

end Work.HP.Sig2
