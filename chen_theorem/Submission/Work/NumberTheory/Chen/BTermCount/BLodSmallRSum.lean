import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodAssembly
import Submission.Work.NumberTheory.Chen.BTermCount.BLodCutSmallR
import Submission.Work.NumberTheory.Chen.BTermCount.semiPairCount_card_le
import Submission.Work.NumberTheory.Chen.BTermCount.sumThreePowInvTotientBound

open Finset Filter
open scoped BigOperators

namespace Work.NumberTheory.Chen.BTermCount

attribute [local instance] Classical.propDecidable

/-- For `t > x + 2` the `t`-divisible part of `B̄` is empty, so the character sum vanishes. -/
theorem bls_charSumDivSum_eq_zero {x M Y t r : ℕ} (ht : x + 2 < t) :
    bProdCharSumDivSum x M Y t r = 0 := by
  unfold bProdCharSumDivSum
  refine Finset.sum_eq_zero (fun ψ _ => ?_)
  have hempty : (bProdSet x M Y).filter (fun n => t ∣ n) = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    rintro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨hnB, hdvd⟩ := hn
    have hle : n ≤ x + 2 := (Finset.mem_Icc.mp (bProdSet_subset_Icc x M Y hnB)).2
    have hpos : 0 < n := bProdSet_pos hnB
    have : t ≤ n := Nat.le_of_dvd hpos hdvd
    omega
  rw [hempty, Finset.sum_empty, norm_zero]

/-- `bPairCount Y 1 = 0`. -/
theorem bls_bPairCount_one (Y : ℕ) : bPairCount Y 1 = 0 := by
  rw [bPairCount_eq_card, Finset.card_eq_zero, bPairSet]
  rw [Finset.eq_empty_iff_forall_notMem]
  rintro p hp
  rw [Finset.mem_filter] at hp
  obtain ⟨-, hp1, hp2, hle, hprod⟩ := hp
  have h4 : 4 ≤ p.1 * p.2 := by
    have := Nat.mul_le_mul hp1.two_le hp2.two_le
    simpa using this
  omega

/-- `log log (V+3) + 3 ≥ 0` for `V ≥ 1`. -/
theorem bls_loglog_nonneg (V : ℕ) (hV : 1 ≤ V) :
    0 ≤ Real.log (Real.log ((V:ℝ) + 3)) + 3 := by
  have h4 : (4:ℝ) ≤ (V:ℝ) + 3 := by
    have : (1:ℝ) ≤ (V:ℝ) := by exact_mod_cast hV
    linarith
  have hlog4 : (1:ℝ) < Real.log 4 := by
    rw [show (4:ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    linarith [Real.log_two_gt_d9]
  have h1 : (1:ℝ) < Real.log ((V:ℝ) + 3) :=
    lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) h4)
  have h2 : 0 < Real.log (Real.log ((V:ℝ) + 3)) := Real.log_pos h1
  linarith

/-- The `bPairCount` bound, valid for all `V ≥ 1` (the case `V = 1` being trivial since
`bPairCount Y 1 = 0`). -/
theorem bls_bPairCount_le (C₂ : ℝ) (hC₂nn : 0 ≤ C₂)
    (hC₂ : ∀ Y N : ℕ, 2 ≤ N →
      (bPairCount Y N : ℝ) ≤ C₂ * (N:ℝ) * (Real.log (Real.log ((N:ℝ)+3)) + 3))
    (Y V : ℕ) (hV : 1 ≤ V) :
    (bPairCount Y V : ℝ) ≤ C₂ * (V:ℝ) * (Real.log (Real.log ((V:ℝ)+3)) + 3) := by
  by_cases h : 2 ≤ V
  · exact hC₂ Y V h
  · have h1 : V = 1 := by omega
    subst h1
    rw [bls_bPairCount_one, Nat.cast_zero]
    exact mul_nonneg (mul_nonneg hC₂nn (by norm_num)) (bls_loglog_nonneg 1 (le_refl 1))

/-- **The block-sum bound.**  `S = Σ_j 4 Q_j (log x)^{-A'} bPairCount Y ((x+2)/Q_j + 1)` is at
most `(log₂(x+2)+1) · 8 C₂ (x+2)(log log (x+6)+3)/(log x)^{A'}`. -/
theorem bls_blockSumBound {x M Y : ℕ} (A' : ℝ) (hA' : 0 < A') (C₂ : ℝ) (hC₂nn : 0 ≤ C₂)
    (hC₂ : ∀ Y N : ℕ, 2 ≤ N →
      (bPairCount Y N : ℝ) ≤ C₂ * (N:ℝ) * (Real.log (Real.log ((N:ℝ)+3)) + 3))
    (hM1 : 1 ≤ M) (hlog0 : 0 ≤ Real.log (x:ℝ)) :
    (∑ j ∈ Finset.range (blockCount M Y),
        4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A' *
          (bPairCount Y ((x + 2) / blockStart M j + 1) : ℝ))
      ≤ ((Nat.log 2 (x + 2) : ℝ) + 1) *
          (8 * C₂ * ((x:ℝ) + 2) * (Real.log (Real.log ((x:ℝ) + 6)) + 3) /
            (Real.log (x:ℝ))^A') := by
  set C : ℝ := 8 * C₂ * ((x:ℝ) + 2) * (Real.log (Real.log ((x:ℝ) + 6)) + 3) /
    (Real.log (x:ℝ))^A' with hCdef
  have hloglog6 : 0 ≤ Real.log (Real.log ((x:ℝ) + 6)) + 3 := by
    have h := bls_loglog_nonneg (x+3) (by omega)
    have h' : ((x+3 : ℕ) : ℝ) + 3 = (x:ℝ) + 6 := by push_cast; ring
    rwa [h'] at h
  have hCnn : 0 ≤ C := by
    rw [hCdef]
    refine div_nonneg ?_ (Real.rpow_nonneg hlog0 A')
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₂nn) (by positivity)) hloglog6
  have hbound : ∀ j ∈ Finset.range (blockCount M Y),
      4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A' *
        (bPairCount Y ((x + 2) / blockStart M j + 1) : ℝ) ≤ C := by
    intro j hj
    by_cases hV2 : 2 ≤ (x + 2) / blockStart M j + 1
    · have hQ1 : 1 ≤ blockStart M j := by
        rw [blockStart]
        have h := Nat.mul_pos (by omega : 0 < M) (Nat.two_pow_pos j)
        omega
      have hQle : blockStart M j ≤ x + 2 := by
        by_contra hcon
        rw [not_le] at hcon
        have hd : (x + 2) / blockStart M j = 0 := Nat.div_eq_of_lt hcon
        rw [hd] at hV2
        omega
      have hV1 : 1 ≤ (x + 2) / blockStart M j + 1 := by omega
      have hbpc := bls_bPairCount_le C₂ hC₂nn hC₂ Y ((x + 2) / blockStart M j + 1) hV1
      have hVle : ((x + 2) / blockStart M j + 1) ≤ x + 3 := by
        have h := Nat.div_le_self (x + 2) (blockStart M j)
        omega
      have hlogmono : Real.log (Real.log ((((x + 2) / blockStart M j + 1 : ℕ):ℝ) + 3))
          ≤ Real.log (Real.log ((x:ℝ) + 6)) := by
        have hVV : ((((x + 2) / blockStart M j + 1 : ℕ):ℝ) + 3) ≤ (x:ℝ) + 6 := by
          have hc : (((x + 2) / blockStart M j + 1 : ℕ):ℝ) ≤ (x:ℝ) + 3 := by
            exact_mod_cast hVle
          linarith
        have hV3 : (1:ℝ) < ((((x + 2) / blockStart M j + 1 : ℕ):ℝ) + 3) := by
          have hc : (1:ℝ) ≤ ((((x + 2) / blockStart M j + 1 : ℕ):ℝ)) := by
            exact_mod_cast hV1
          linarith
        exact Real.log_le_log (Real.log_pos hV3) (Real.log_le_log (by linarith) hVV)
      have hprod : (blockStart M j : ℝ) * ((((x + 2) / blockStart M j + 1 : ℕ):ℝ))
          ≤ 2 * ((x:ℝ) + 2) := by
        have h3 : ((((x + 2) / blockStart M j + 1 : ℕ):ℝ))
            = (((x+2)/blockStart M j : ℕ):ℝ) + 1 := by push_cast; ring
        rw [h3, mul_add, mul_one]
        have h2 : (blockStart M j : ℝ) * ((((x + 2) / blockStart M j : ℕ):ℝ)) ≤ (x:ℝ) + 2 := by
          have h4 := Nat.div_mul_le_self (x + 2) (blockStart M j)
          have h5 : ((((x + 2) / blockStart M j) * (blockStart M j) : ℕ) : ℝ)
              ≤ ((x + 2 : ℕ) : ℝ) := by exact_mod_cast h4
          push_cast at h5
          linarith
        have h6 : (blockStart M j : ℝ) ≤ (x:ℝ) + 2 := by exact_mod_cast hQle
        linarith
      calc 4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A' *
              (bPairCount Y ((x + 2) / blockStart M j + 1) : ℝ)
          ≤ 4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A' *
              (C₂ * ((((x + 2) / blockStart M j + 1 : ℕ):ℝ)) *
                (Real.log (Real.log ((((x + 2) / blockStart M j + 1 : ℕ):ℝ) + 3)) + 3)) := by
            refine mul_le_mul_of_nonneg_left hbpc ?_
            exact div_nonneg (by positivity) (Real.rpow_nonneg hlog0 A')
        _ ≤ 4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A' *
              (C₂ * ((((x + 2) / blockStart M j + 1 : ℕ):ℝ)) *
                (Real.log (Real.log ((x:ℝ) + 6)) + 3)) := by
            refine mul_le_mul_of_nonneg_left ?_
              (div_nonneg (by positivity) (Real.rpow_nonneg hlog0 A'))
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hC₂nn (by positivity))
            linarith [hlogmono]
        _ = 4 * C₂ * ((blockStart M j : ℝ) * ((((x + 2) / blockStart M j + 1 : ℕ):ℝ))) *
              (Real.log (Real.log ((x:ℝ) + 6)) + 3) / (Real.log (x:ℝ))^A' := by ring
        _ ≤ 4 * C₂ * (2 * ((x:ℝ) + 2)) * (Real.log (Real.log ((x:ℝ) + 6)) + 3) /
              (Real.log (x:ℝ))^A' := by
            refine div_le_div_of_nonneg_right ?_ (Real.rpow_nonneg hlog0 A')
            refine mul_le_mul_of_nonneg_right ?_ hloglog6
            exact mul_le_mul_of_nonneg_left hprod (by positivity)
        _ = C := by rw [hCdef]; ring
    · have hVle1 : (x + 2) / blockStart M j + 1 = 1 := by
        have hlt : (x + 2) / blockStart M j + 1 < 2 := not_le.mp hV2
        have hle : (x + 2) / blockStart M j + 1 ≤ 1 := Nat.lt_succ_iff.mp hlt
        exact le_antisymm hle (Nat.le_add_left 1 _)
      rw [hVle1, bls_bPairCount_one, Nat.cast_zero, mul_zero]
      exact hCnn
  have hx2ne : x + 2 ≠ 0 := by omega
  have hvan : ∀ j ∈ Finset.range (blockCount M Y), Nat.log 2 (x + 2) + 1 ≤ j →
      4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A' *
        (bPairCount Y ((x + 2) / blockStart M j + 1) : ℝ) = 0 := by
    intro j hj hjge
    have hpow : x + 2 < 2 ^ j := by
      have h1 : Nat.log 2 (x + 2) < j := by omega
      exact (Nat.log_lt_iff_lt_pow (by norm_num : 1 < 2) hx2ne).mp h1
    have hQ : x + 2 < blockStart M j := by
      rw [blockStart]
      calc x + 2 < 2 ^ j := hpow
        _ = 1 * 2 ^ j := (one_mul _).symm
        _ ≤ M * 2 ^ j := Nat.mul_le_mul_right _ hM1
    have hdiv : (x + 2) / blockStart M j = 0 := Nat.div_eq_of_lt hQ
    have hV1 : (x + 2) / blockStart M j + 1 = 1 := by rw [hdiv]
    rw [hV1, bls_bPairCount_one, Nat.cast_zero, mul_zero]
  set T := (Finset.range (blockCount M Y)).filter (fun j => j < Nat.log 2 (x + 2) + 1)
    with hTdef
  have hTeq : ∑ j ∈ Finset.range (blockCount M Y),
        4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A' *
          (bPairCount Y ((x + 2) / blockStart M j + 1) : ℝ)
      = ∑ j ∈ T, 4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A' *
          (bPairCount Y ((x + 2) / blockStart M j + 1) : ℝ) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) (fun j hj hjT => ?_)).symm
    rw [Finset.mem_filter] at hjT
    push_neg at hjT
    exact hvan j hj (hjT hj)
  have hTcard : (T.card : ℝ) ≤ ((Nat.log 2 (x + 2) : ℝ) + 1) := by
    have hsub : T ⊆ Finset.range (Nat.log 2 (x + 2) + 1) := by
      intro j hj
      rw [hTdef, Finset.mem_filter] at hj
      rw [Finset.mem_range]
      exact hj.2
    have h1 : T.card ≤ Nat.log 2 (x + 2) + 1 := by
      calc T.card ≤ (Finset.range (Nat.log 2 (x + 2) + 1)).card := Finset.card_le_card hsub
        _ = Nat.log 2 (x + 2) + 1 := Finset.card_range _
    exact_mod_cast h1
  calc ∑ j ∈ Finset.range (blockCount M Y),
        4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A' *
          (bPairCount Y ((x + 2) / blockStart M j + 1) : ℝ)
      = ∑ j ∈ T, 4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A' *
          (bPairCount Y ((x + 2) / blockStart M j + 1) : ℝ) := hTeq
    _ ≤ ∑ j ∈ T, C := Finset.sum_le_sum (fun j hj => hbound j ((Finset.filter_subset _ _) hj))
    _ = (T.card : ℝ) * C := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ((Nat.log 2 (x + 2) : ℝ) + 1) * C := mul_le_mul_of_nonneg_right hTcard hCnn
    _ = ((Nat.log 2 (x + 2) : ℝ) + 1) *
          (8 * C₂ * ((x:ℝ) + 2) * (Real.log (Real.log ((x:ℝ) + 6)) + 3) /
            (Real.log (x:ℝ))^A') := by rw [hCdef]

/-- **The per-`(t,r)` bound.** -/
theorem bls_term_bound {x M Y R₀ : ℕ} (A' C' : ℝ)
    (hSWx : ∀ {r : ℕ}, 2 ≤ r → r ≤ ⌊(Real.log (x:ℝ))^C'⌋₊ →
      ∀ (ψ : DirichletCharacter ℂ r), ψ.IsPrimitive → ψ ≠ 1 →
      ∀ (M Y j t₁ t₂ : ℕ), (x:ℝ)^((1:ℝ)/14) ≤ M →
        ‖bilinForm (2 * blockStart M j) ((x + 2) / blockStart M j + 1) (x + 2)
            (aCut M Y j t₁) (bCut Y t₂) r ψ‖
          ≤ 4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A'
              * (bPairCount Y ((x + 2) / blockStart M j + 1) : ℝ))
    (hlog0 : 0 ≤ Real.log (x:ℝ))
    (hM : (x:ℝ)^((1:ℝ)/14) ≤ M) (hM1 : 1 ≤ M) (hR₀ : R₀ ≤ ⌊(Real.log (x:ℝ))^C'⌋₊)
    {t r : ℕ} (ht : 1 ≤ t) (hr : 2 ≤ r) (hrR : r ≤ R₀) :
    bProdCharSumDivSum x M Y t r ≤ (Nat.totient r : ℝ) *
      ∑ j ∈ Finset.range (blockCount M Y),
        4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A' *
          (bPairCount Y ((x + 2) / blockStart M j + 1) : ℝ) := by
  haveI : NeZero r := ⟨by omega⟩
  have ht0 : t ≠ 0 := by omega
  have hrC : r ≤ ⌊(Real.log (x:ℝ))^C'⌋₊ := le_trans hrR hR₀
  have hcard : ((Finset.univ.filter
      (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive)).card : ℝ) ≤ (r.totient : ℝ) := by
    have h1 : (Finset.univ.filter
        (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive)).card
        ≤ Fintype.card (DirichletCharacter ℂ r) := by
      rw [← Finset.card_univ]
      exact Finset.card_le_card (Finset.filter_subset _ _)
    have h2 : Fintype.card (DirichletCharacter ℂ r) = r.totient := by
      rw [← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ r
    rw [h2] at h1
    exact_mod_cast h1
  have hne1 : ∀ ψ : DirichletCharacter ℂ r, ψ.IsPrimitive → ψ ≠ 1 := by
    intro ψ hψ hcon
    rw [hcon, DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_one] at hψ
    omega
  calc bProdCharSumDivSum x M Y t r
      ≤ ∑ j ∈ Finset.range (blockCount M Y),
          ∑ ψ ∈ (Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive)),
            ‖bilinForm (2 * blockStart M j) ((x + 2) / blockStart M j + 1) (x + 2)
              (aCut M Y j (tSmall Y t)) (bCut Y (tLarge Y t)) r ψ‖ :=
        bProdCharSumDivSum_le_block x M Y t r ht0 hM1
    _ ≤ ∑ j ∈ Finset.range (blockCount M Y),
          ∑ ψ ∈ (Finset.univ.filter (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive)),
            4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A' *
              (bPairCount Y ((x + 2) / blockStart M j + 1) : ℝ) := by
        refine Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun ψ hψ => ?_))
        rw [Finset.mem_filter] at hψ
        exact hSWx hr hrC ψ hψ.2 (hne1 ψ hψ.2) M Y j (tSmall Y t) (tLarge Y t) hM
    _ = ∑ j ∈ Finset.range (blockCount M Y),
          ((Finset.univ.filter
            (fun ψ : DirichletCharacter ℂ r => ψ.IsPrimitive)).card : ℝ) *
            (4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A' *
              (bPairCount Y ((x + 2) / blockStart M j + 1) : ℝ)) := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ j ∈ Finset.range (blockCount M Y), (r.totient : ℝ) *
            (4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A' *
              (bPairCount Y ((x + 2) / blockStart M j + 1) : ℝ)) := by
        refine Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_right hcard ?_)
        exact mul_nonneg (div_nonneg (by positivity) (Real.rpow_nonneg hlog0 A'))
          (by positivity)
    _ = (r.totient : ℝ) * ∑ j ∈ Finset.range (blockCount M Y),
            4 * (blockStart M j : ℝ) / (Real.log (x:ℝ))^A' *
              (bPairCount Y ((x + 2) / blockStart M j + 1) : ℝ) := by
        rw [Finset.mul_sum]

theorem BLodSmallRSum :
    ∀ A' C' : ℝ, 0 < A' → 0 < C' → C' ≤ A' → ∃ C : ℝ, 0 < C ∧
      ∀ᶠ x : ℕ in Filter.atTop,
        ∀ (M Y D R₀ : ℕ), (x:ℝ)^((1:ℝ)/14) ≤ M → R₀ ≤ ⌊(Real.log (x:ℝ))^C'⌋₊ → 2 ≤ D →
          (∑ t ∈ Finset.Icc 1 D, ((3:ℝ)^(t.primeFactors.card) / (Nat.totient t : ℝ)) *
            ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
              ((3:ℝ)^(r.primeFactors.card) / (Nat.totient r : ℝ)) *
                bProdCharSumDivSum x M Y t r)
          ≤ C * (x:ℝ) * (Real.log (x:ℝ) + 2)^(2*C' + 20)
                * Real.log (Real.log (x:ℝ) + 3) / (Real.log (x:ℝ))^(A') := by
  intro A' C' hA' hC' hCA
  obtain ⟨C₂, hC₂pos, hC₂⟩ := semiPairCount_card_le
  obtain ⟨C₃, hC₃pos, hC₃⟩ := sumThreePowInvTotientBound
  have hC₂nn : 0 ≤ C₂ := le_of_lt hC₂pos
  have hC₃nn : 0 ≤ C₃ := le_of_lt hC₃pos
  refine ⟨1024 * C₃^2 * C₂ * C'^3, by positivity, ?_⟩
  have hSW := BLodCutSmallR A' C' hA' hC'
  have hbig : ∀ᶠ x : ℕ in Filter.atTop, 6 ≤ x ∧ 64 ≤ Real.log (x:ℝ) := by
    have h1 : Filter.Tendsto (fun x : ℕ => Real.log (x:ℝ)) Filter.atTop Filter.atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    filter_upwards [h1.eventually (Filter.eventually_ge_atTop 64),
      Filter.eventually_ge_atTop (6 : ℕ)] with x hx hx6
    exact ⟨hx6, hx⟩
  filter_upwards [hSW, hbig] with x hSWx hbig
  obtain ⟨hx6, hL64⟩ := hbig
  intro M Y D R₀ hM hR₀ hD
  set L : ℝ := Real.log (x:ℝ) with hLdef
  have hLpos : 0 < L := by rw [hLdef]; linarith
  have hL1 : 1 ≤ L := by rw [hLdef]; linarith
  have hLnn : 0 ≤ L := le_of_lt hLpos
  have hM1 : 1 ≤ M := by
    have h1 : (1:ℝ) ≤ (x:ℝ)^((1:ℝ)/14) :=
      Real.one_le_rpow (by exact_mod_cast (by omega : 1 ≤ x)) (by norm_num)
    exact_mod_cast (le_trans h1 hM)
  have hx2L : ((x:ℝ) + 2) ≤ 2 * (x:ℝ) := by
    have : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 2 ≤ x)
    linarith
  by_cases hR₀lt : R₀ < 2
  · have hempty : (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      rintro r hr
      rw [Finset.mem_filter] at hr
      omega
    have hzero : (∑ t ∈ Finset.Icc 1 D,
        ((3:ℝ)^(t.primeFactors.card) / (Nat.totient t : ℝ)) *
          ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
            ((3:ℝ)^(r.primeFactors.card) / (Nat.totient r : ℝ)) *
              bProdCharSumDivSum x M Y t r) = 0 := by
      refine Finset.sum_eq_zero (fun t _ => ?_)
      rw [hempty, Finset.sum_empty, mul_zero]
    rw [hzero]
    have hKpos : 0 < 1024 * C₃^2 * C₂ * C'^3 := by positivity
    have hxnn : (0:ℝ) < (x:ℝ) := by exact_mod_cast (by omega : 0 < x)
    have hApos : 0 < (Real.log (x:ℝ) + 2)^(2*C' + 20) :=
      Real.rpow_pos_of_pos (by linarith [hLpos]) _
    have hBpos : 0 < Real.log (Real.log (x:ℝ) + 3) := Real.log_pos (by linarith [hL64])
    have hCpos : 0 < (Real.log (x:ℝ))^(A') := Real.rpow_pos_of_pos (by linarith [hLpos]) _
    exact le_of_lt (div_pos (mul_pos (mul_pos (mul_pos hKpos hxnn) hApos) hBpos) hCpos)
  · have hR₀2 : 2 ≤ R₀ := by omega
    have hL3le : Real.log ((x:ℝ)+2) ≤ 2 * L := by
      rw [hLdef]
      have hlog2 : Real.log 2 ≤ Real.log (x:ℝ) := by
        refine Real.log_le_log (by norm_num) ?_
        exact_mod_cast (by omega : 2 ≤ x)
      have h2 : Real.log (2 * (x:ℝ)) = Real.log 2 + Real.log (x:ℝ) :=
        Real.log_mul (by norm_num) (by positivity)
      calc Real.log ((x:ℝ)+2) ≤ Real.log (2 * (x:ℝ)) :=
            Real.log_le_log (by linarith) hx2L
        _ = Real.log 2 + Real.log (x:ℝ) := h2
        _ ≤ 2 * Real.log (x:ℝ) := by linarith
    have hRpC : (0:ℝ) ≤ L^C' := Real.rpow_nonneg hLnn C'
    have hR₀le : (R₀:ℝ) ≤ L^C' := by
      have h1 : ((R₀:ℕ):ℝ) ≤ ((⌊L^C'⌋₊:ℕ):ℝ) := by
        rw [hLdef] at hR₀
        exact_mod_cast hR₀
      exact le_trans h1 (Nat.floor_le hRpC)
    have hR₀pos : (0:ℝ) < (R₀:ℝ) := by exact_mod_cast (by omega : 0 < R₀)
    have hlogR₀ : Real.log (R₀:ℝ) ≤ C' * Real.log L := by
      have h1 : Real.log (R₀:ℝ) ≤ Real.log (L^C') := Real.log_le_log hR₀pos hR₀le
      rwa [Real.log_rpow hLpos C'] at h1
    have hlognat : (Nat.log 2 (x+2) : ℝ) + 1 ≤ 4 * L := by
      rw [hLdef]
      have hLpos' : 0 < Real.log (x:ℝ) := by linarith
      have hx2ne : x + 2 ≠ 0 := by omega
      have hpow : (2:ℝ)^(Nat.log 2 (x+2)) ≤ ((x+2 : ℕ) : ℝ) := by
        have h := Nat.pow_log_le_self 2 hx2ne
        exact_mod_cast h
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hlog2half : (1:ℝ)/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
      have hkle1 : (Nat.log 2 (x+2) : ℝ) * Real.log 2 ≤ Real.log (((x+2:ℕ):ℝ)) := by
        rw [← Real.log_pow]
        exact Real.log_le_log (by norm_num) hpow
      have hcast : (((x+2:ℕ):ℝ)) = (x:ℝ) + 2 := by push_cast; ring
      rw [hcast] at hkle1
      have hlog3 : Real.log ((x:ℝ)+2) ≤ Real.log (2 * (x:ℝ)) := by
        refine Real.log_le_log (by linarith) ?_
        have : (2:ℝ) ≤ (x:ℝ) := by exact_mod_cast (by omega : 2 ≤ x)
        linarith
      have h2 : Real.log (2 * (x:ℝ)) = Real.log 2 + Real.log (x:ℝ) :=
        Real.log_mul (by norm_num) (by positivity)
      have hkle : (Nat.log 2 (x+2) : ℝ) ≤ 1 + Real.log (x:ℝ) / Real.log 2 := by
        have h1 : (Nat.log 2 (x+2) : ℝ) * Real.log 2 ≤ Real.log 2 + Real.log (x:ℝ) := by
          rw [← h2]; exact le_trans hkle1 hlog3
        rw [show (1:ℝ) + Real.log (x:ℝ) / Real.log 2
            = (Real.log 2 + Real.log (x:ℝ)) / Real.log 2 by field_simp]
        rw [le_div_iff₀ hlog2pos]
        linarith
      have hdiv : Real.log (x:ℝ) / Real.log 2 ≤ 2 * Real.log (x:ℝ) := by
        rw [div_le_iff₀ hlog2pos]; nlinarith [hL64, hlog2half]
      linarith
    have hloglog : Real.log (Real.log ((x:ℝ) + 6)) + 3 ≤ 2 * Real.log L := by
      rw [hLdef]
      have hLpos' : 0 < Real.log (x:ℝ) := by linarith
      have harg1 : (1:ℝ) < (x:ℝ)+6 := by
        have : (6:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx6
        linarith
      have hx6' : ((x:ℝ)+6) ≤ 2*(x:ℝ) := by
        have : (6:ℝ) ≤ (x:ℝ) := by exact_mod_cast hx6
        linarith
      have h2 : Real.log 2 ≤ Real.log (x:ℝ) := by
        refine Real.log_le_log (by norm_num) ?_
        exact_mod_cast (by omega : 2 ≤ x)
      have h1 : Real.log ((x:ℝ)+6) ≤ 2 * Real.log (x:ℝ) := by
        have h := Real.log_le_log (by linarith) hx6'
        rw [Real.log_mul (by norm_num) (by positivity)] at h
        linarith
      have h4 : Real.log (Real.log ((x:ℝ)+6)) ≤ Real.log (2 * Real.log (x:ℝ)) :=
        Real.log_le_log (Real.log_pos harg1) h1
      have h5 : Real.log (2 * Real.log (x:ℝ)) = Real.log 2 + Real.log (Real.log (x:ℝ)) :=
        Real.log_mul (by norm_num) (by linarith)
      have h6 : Real.log 2 + 3 ≤ Real.log (Real.log (x:ℝ)) := by
        have hlog64 : Real.log 64 ≤ Real.log (Real.log (x:ℝ)) :=
          Real.log_le_log (by norm_num) hL64
        have h64 : Real.log 64 = 6 * Real.log 2 := by
          rw [show (64:ℝ) = (2:ℝ)^6 by norm_num, Real.log_pow]
          norm_num
        rw [h64] at hlog64
        nlinarith [Real.log_two_gt_d9]
      rw [h5] at h4
      linarith
    have hL3pos : 0 < Real.log ((x:ℝ)+2) := Real.log_pos (by linarith)
    have hL3nn : 0 ≤ Real.log ((x:ℝ)+2) := le_of_lt hL3pos
    have hLRpos : 0 < Real.log (R₀:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < R₀))
    have hLRnn : 0 ≤ Real.log (R₀:ℝ) := le_of_lt hLRpos
    have hY6nn : 0 ≤ Real.log (Real.log ((x:ℝ) + 6)) + 3 := by
      have h := bls_loglog_nonneg (x+3) (by omega)
      have h' : ((x+3 : ℕ) : ℝ) + 3 = (x:ℝ) + 6 := by push_cast; ring
      rwa [h'] at h
    set S : ℝ := ∑ j ∈ Finset.range (blockCount M Y),
        4 * (blockStart M j : ℝ) / L^A' * (bPairCount Y ((x + 2) / blockStart M j + 1) : ℝ)
      with hSdef
    have hSnn : 0 ≤ S := by
      rw [hSdef]
      refine Finset.sum_nonneg (fun j _ => ?_)
      exact mul_nonneg (div_nonneg (by positivity) (Real.rpow_nonneg hLnn A')) (by positivity)
    have hSbound : S ≤ ((Nat.log 2 (x + 2) : ℝ) + 1) *
        (8 * C₂ * ((x:ℝ) + 2) * (Real.log (Real.log ((x:ℝ) + 6)) + 3) / L^A') := by
      rw [hSdef]
      simpa only [hLdef] using bls_blockSumBound A' hA' C₂ hC₂nn hC₂ hM1 hLnn
    have hper : ∀ t ∈ Finset.Icc 1 (x+2),
        ∀ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
        bProdCharSumDivSum x M Y t r ≤ (Nat.totient r : ℝ) * S := by
      intro t ht r hr
      have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
      obtain ⟨-, hr2, hrR⟩ := Finset.mem_filter.mp hr
      rw [hSdef]
      exact bls_term_bound A' C' hSWx hLnn hM hM1 hR₀ ht1 hr2 hrR
    have hG : ∀ t ∈ Finset.Icc 1 (x+2),
        (∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
            ((3:ℝ)^(r.primeFactors.card) / (Nat.totient r : ℝ)) * bProdCharSumDivSum x M Y t r)
          ≤ (∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
              (3:ℝ)^(r.primeFactors.card)) * S := by
      intro t ht
      calc (∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
              ((3:ℝ)^(r.primeFactors.card) / (Nat.totient r : ℝ)) * bProdCharSumDivSum x M Y t r)
          ≤ ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
              ((3:ℝ)^(r.primeFactors.card) / (Nat.totient r : ℝ)) * ((Nat.totient r : ℝ) * S) := by
            refine Finset.sum_le_sum (fun r hr => ?_)
            refine mul_le_mul_of_nonneg_left (hper t ht r hr) ?_
            exact div_nonneg (by positivity) (by positivity)
        _ = (∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
              (3:ℝ)^(r.primeFactors.card)) * S := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl (fun r hr => ?_)
            have hr2 : 2 ≤ r := (Finset.mem_filter.mp hr).2.1
            have hφpos : (0:ℝ) < (Nat.totient r : ℝ) := by
              exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < r)
            field_simp
    have hGzero : ∀ t, x + 2 < t →
        (∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
            ((3:ℝ)^(r.primeFactors.card) / (Nat.totient r : ℝ)) * bProdCharSumDivSum x M Y t r)
          = 0 := by
      intro t ht
      refine Finset.sum_eq_zero (fun r _ => ?_)
      rw [bls_charSumDivSum_eq_zero ht, mul_zero]
    have hwt : ∀ t ∈ Finset.Icc 1 (x+2),
        0 ≤ (3:ℝ)^(t.primeFactors.card) / (Nat.totient t : ℝ) :=
      fun t _ => div_nonneg (by positivity) (by positivity)
    have hP : (∑ t ∈ Finset.Icc 1 (x+2), (3:ℝ)^(t.primeFactors.card) / (Nat.totient t : ℝ))
        ≤ C₃ * (Real.log ((x:ℝ)+2))^3 := by
      have h := hC₃ (x+2) (by omega)
      have h' : ((x+2 : ℕ) : ℝ) = (x:ℝ) + 2 := by push_cast; ring
      rwa [h'] at h
    have hQ : (∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
          (3:ℝ)^(r.primeFactors.card)) ≤ R₀ * C₃ * (Real.log (R₀:ℝ))^3 := by
      have hsub : (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀) ⊆ Finset.Icc 1 R₀ := by
        intro r hr
        obtain ⟨hmem, -, hrR⟩ := Finset.mem_filter.mp hr
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hmem).1, hrR⟩
      calc (∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
              (3:ℝ)^(r.primeFactors.card))
          ≤ ∑ r ∈ Finset.Icc 1 R₀, (3:ℝ)^(r.primeFactors.card) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => by positivity)
        _ = ∑ r ∈ Finset.Icc 1 R₀,
              ((3:ℝ)^(r.primeFactors.card) / (Nat.totient r : ℝ)) * (Nat.totient r : ℝ) := by
            refine Finset.sum_congr rfl (fun r hr => ?_)
            have hr1 : 1 ≤ r := (Finset.mem_Icc.mp hr).1
            have hφpos : (0:ℝ) < (Nat.totient r : ℝ) := by
              exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < r)
            field_simp
        _ ≤ ∑ r ∈ Finset.Icc 1 R₀,
              ((3:ℝ)^(r.primeFactors.card) / (Nat.totient r : ℝ)) * (R₀:ℝ) := by
            refine Finset.sum_le_sum (fun r hr => ?_)
            have hrR : r ≤ R₀ := (Finset.mem_Icc.mp hr).2
            have h1 : (Nat.totient r : ℝ) ≤ (R₀:ℝ) := by
              have h2 := Nat.totient_le r
              exact_mod_cast le_trans h2 hrR
            exact mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (∑ r ∈ Finset.Icc 1 R₀,
              (3:ℝ)^(r.primeFactors.card) / (Nat.totient r : ℝ)) * R₀ := by
            rw [Finset.sum_mul]
        _ ≤ (C₃ * (Real.log (R₀:ℝ))^3) * R₀ :=
            mul_le_mul_of_nonneg_right (hC₃ R₀ hR₀2) (by positivity)
        _ = R₀ * C₃ * (Real.log (R₀:ℝ))^3 := by ring
    have hstep1 : (∑ t ∈ Finset.Icc 1 D,
          ((3:ℝ)^(t.primeFactors.card) / (Nat.totient t : ℝ)) *
            ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
              ((3:ℝ)^(r.primeFactors.card) / (Nat.totient r : ℝ)) * bProdCharSumDivSum x M Y t r)
        ≤ (∑ t ∈ Finset.Icc 1 (x+2), (3:ℝ)^(t.primeFactors.card) / (Nat.totient t : ℝ)) *
            ((∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
                (3:ℝ)^(r.primeFactors.card)) * S) := by
      have hsub : (Finset.Icc 1 D).filter (fun t => t ≤ x + 2) ⊆ Finset.Icc 1 (x + 2) := by
        intro t ht
        obtain ⟨hmem, htle⟩ := Finset.mem_filter.mp ht
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hmem).1, htle⟩
      have hsplit : (∑ t ∈ Finset.Icc 1 D,
            ((3:ℝ)^(t.primeFactors.card) / (Nat.totient t : ℝ)) *
              ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
                ((3:ℝ)^(r.primeFactors.card) / (Nat.totient r : ℝ)) *
                  bProdCharSumDivSum x M Y t r)
          = ∑ t ∈ (Finset.Icc 1 D).filter (fun t => t ≤ x + 2),
              ((3:ℝ)^(t.primeFactors.card) / (Nat.totient t : ℝ)) *
                ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
                  ((3:ℝ)^(r.primeFactors.card) / (Nat.totient r : ℝ)) *
                    bProdCharSumDivSum x M Y t r := by
        refine (Finset.sum_subset (Finset.filter_subset _ _) (fun t ht hnot => ?_)).symm
        have htgt : x + 2 < t := by
          by_contra hc
          exact hnot (Finset.mem_filter.mpr ⟨ht, not_lt.mp hc⟩)
        rw [hGzero t htgt, mul_zero]
      rw [hsplit]
      calc (∑ t ∈ (Finset.Icc 1 D).filter (fun t => t ≤ x + 2),
              ((3:ℝ)^(t.primeFactors.card) / (Nat.totient t : ℝ)) *
                ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
                  ((3:ℝ)^(r.primeFactors.card) / (Nat.totient r : ℝ)) *
                    bProdCharSumDivSum x M Y t r)
          ≤ ∑ t ∈ Finset.Icc 1 (x+2),
              ((3:ℝ)^(t.primeFactors.card) / (Nat.totient t : ℝ)) *
                ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
                  ((3:ℝ)^(r.primeFactors.card) / (Nat.totient r : ℝ)) *
                    bProdCharSumDivSum x M Y t r := by
            refine Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t ht _ => ?_)
            refine mul_nonneg (hwt t ht) ?_
            refine Finset.sum_nonneg (fun r _ => ?_)
            exact mul_nonneg (div_nonneg (by positivity) (by positivity))
              (bProdCharSumDivSum_nonneg x M Y t r)
        _ ≤ ∑ t ∈ Finset.Icc 1 (x+2),
              ((3:ℝ)^(t.primeFactors.card) / (Nat.totient t : ℝ)) *
                ((∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
                    (3:ℝ)^(r.primeFactors.card)) * S) := by
            refine Finset.sum_le_sum (fun t ht => mul_le_mul_of_nonneg_left (hG t ht) (hwt t ht))
        _ = (∑ t ∈ Finset.Icc 1 (x+2), (3:ℝ)^(t.primeFactors.card) / (Nat.totient t : ℝ)) *
              ((∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
                  (3:ℝ)^(r.primeFactors.card)) * S) :=
            (Finset.sum_mul (Finset.Icc 1 (x+2))
              (fun t => (3:ℝ)^(t.primeFactors.card) / (Nat.totient t : ℝ))
              ((∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
                  (3:ℝ)^(r.primeFactors.card)) * S)).symm
    have hQnn : 0 ≤ ∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
        (3:ℝ)^(r.primeFactors.card) := Finset.sum_nonneg (fun r _ => by positivity)
    have hPnn : 0 ≤ C₃ * (Real.log ((x:ℝ)+2))^3 :=
      mul_nonneg hC₃nn (by positivity)
    have hQ'nn : 0 ≤ R₀ * C₃ * (Real.log (R₀:ℝ))^3 := by positivity
    have hcomb : (∑ t ∈ Finset.Icc 1 (x+2), (3:ℝ)^(t.primeFactors.card) / (Nat.totient t : ℝ)) *
          ((∑ r ∈ (Finset.Icc 1 D).filter (fun r => 2 ≤ r ∧ r ≤ R₀),
              (3:ℝ)^(r.primeFactors.card)) * S)
        ≤ (C₃ * (Real.log ((x:ℝ)+2))^3) *
            ((R₀ * C₃ * (Real.log (R₀:ℝ))^3) *
              (((Nat.log 2 (x + 2) : ℝ) + 1) *
                (8 * C₂ * ((x:ℝ) + 2) * (Real.log (Real.log ((x:ℝ) + 6)) + 3) / L^A'))) := by
      have s1 := mul_le_mul_of_nonneg_right hP (mul_nonneg hQnn hSnn)
      have s2 := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hQ hSnn) hPnn
      have s3 := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hSbound hQ'nn) hPnn
      exact le_trans s1 (le_trans s2 s3)
    have hA1 : C₃ * (Real.log ((x:ℝ)+2))^3 ≤ C₃ * (2*L)^3 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL3nn hL3le 3) hC₃nn
    have hA2a : (R₀:ℝ) * C₃ ≤ L^C' * C₃ := mul_le_mul_of_nonneg_right hR₀le hC₃nn
    have hA2b : (Real.log (R₀:ℝ))^3 ≤ (C' * Real.log L)^3 :=
      pow_le_pow_left₀ hLRnn hlogR₀ 3
    have hA2 : (R₀:ℝ) * C₃ * (Real.log (R₀:ℝ))^3 ≤ (L^C' * C₃) * (C' * Real.log L)^3 :=
      mul_le_mul hA2a hA2b (by positivity) (mul_nonneg hRpC hC₃nn)
    have hA3 : ((Nat.log 2 (x + 2) : ℝ) + 1) *
          (8 * C₂ * ((x:ℝ) + 2) * (Real.log (Real.log ((x:ℝ) + 6)) + 3) / L^A')
        ≤ (4*L) * (8 * C₂ * (2*(x:ℝ)) * (2 * Real.log L) / L^A') := by
      refine mul_le_mul hlognat ?_ ?_ (by positivity)
      · refine div_le_div_of_nonneg_right ?_ (Real.rpow_nonneg hLnn A')
        refine mul_le_mul ?_ hloglog hY6nn ?_
        · exact mul_le_mul_of_nonneg_left hx2L (by positivity)
        · positivity
      · positivity
    have hfinal1 : (C₃ * (Real.log ((x:ℝ)+2))^3) *
            ((R₀ * C₃ * (Real.log (R₀:ℝ))^3) *
              (((Nat.log 2 (x + 2) : ℝ) + 1) *
                (8 * C₂ * ((x:ℝ) + 2) * (Real.log (Real.log ((x:ℝ) + 6)) + 3) / L^A')))
        ≤ 1024 * C₃^2 * C₂ * C'^3 * (x:ℝ) * L^4 * L^C' * (Real.log L)^4 / L^A' := by
      have hC'nn : 0 ≤ C' := le_of_lt hC'
      have hmm : 0 ≤ (L^C' * C₃) * (C' * Real.log L)^3 :=
        mul_nonneg (mul_nonneg hRpC hC₃nn)
          (pow_nonneg (mul_nonneg hC'nn (Real.log_nonneg hL1)) 3)
      have hs1 : (C₃ * (Real.log ((x:ℝ)+2))^3) *
            ((R₀ * C₃ * (Real.log (R₀:ℝ))^3) *
              (((Nat.log 2 (x + 2) : ℝ) + 1) *
                (8 * C₂ * ((x:ℝ) + 2) * (Real.log (Real.log ((x:ℝ) + 6)) + 3) / L^A')))
          ≤ (C₃ * (2*L)^3) *
            ((R₀ * C₃ * (Real.log (R₀:ℝ))^3) *
              (((Nat.log 2 (x + 2) : ℝ) + 1) *
                (8 * C₂ * ((x:ℝ) + 2) * (Real.log (Real.log ((x:ℝ) + 6)) + 3) / L^A'))) :=
        mul_le_mul_of_nonneg_right hA1 (by positivity)
      have hs2 : (C₃ * (2*L)^3) *
            ((R₀ * C₃ * (Real.log (R₀:ℝ))^3) *
              (((Nat.log 2 (x + 2) : ℝ) + 1) *
                (8 * C₂ * ((x:ℝ) + 2) * (Real.log (Real.log ((x:ℝ) + 6)) + 3) / L^A')))
          ≤ (C₃ * (2*L)^3) *
            (((L^C' * C₃) * (C' * Real.log L)^3) *
              (((Nat.log 2 (x + 2) : ℝ) + 1) *
                (8 * C₂ * ((x:ℝ) + 2) * (Real.log (Real.log ((x:ℝ) + 6)) + 3) / L^A'))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hA2 (by positivity))
          (by positivity)
      have hs3 : (C₃ * (2*L)^3) *
            (((L^C' * C₃) * (C' * Real.log L)^3) *
              (((Nat.log 2 (x + 2) : ℝ) + 1) *
                (8 * C₂ * ((x:ℝ) + 2) * (Real.log (Real.log ((x:ℝ) + 6)) + 3) / L^A')))
          ≤ (C₃ * (2*L)^3) *
            (((L^C' * C₃) * (C' * Real.log L)^3) *
              ((4*L) * (8 * C₂ * (2*(x:ℝ)) * (2 * Real.log L) / L^A'))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hA3 hmm)
          (by positivity)
      have hs4 : (C₃ * (2*L)^3) *
            (((L^C' * C₃) * (C' * Real.log L)^3) *
              ((4*L) * (8 * C₂ * (2*(x:ℝ)) * (2 * Real.log L) / L^A')))
          = 1024 * C₃^2 * C₂ * C'^3 * (x:ℝ) * L^4 * L^C' * (Real.log L)^4 / L^A' := by
        ring
      exact le_trans hs1 (le_trans hs2 (le_trans hs3 (le_of_eq hs4)))
    have hpowadd : L^4 * L^C' = L^(4 + C') := by
      rw [Real.rpow_add hLpos (4:ℝ) C']
      norm_num
    have hlogL4 : (Real.log L)^4 ≤ L^(C' + 16) := by
      have hlogLle : Real.log L ≤ L := by
        have h := Real.log_le_sub_one_of_pos hLpos
        linarith
      have h4 : (Real.log L)^4 ≤ L^4 :=
        pow_le_pow_left₀ (Real.log_nonneg hL1) hlogLle 4
      have h5 : L^4 ≤ L^(C' + 16) := by
        have h6 : L^(4:ℝ) ≤ L^(C' + 16) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
        simpa using h6
      exact le_trans h4 h5
    have hlogL3 : (1:ℝ) ≤ Real.log (L + 3) := by
      have h4 : (4:ℝ) ≤ L + 3 := by linarith
      have hlog4 : (1:ℝ) < Real.log 4 := by
        rw [show (4:ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
        linarith [Real.log_two_gt_d9]
      exact le_of_lt (lt_of_lt_of_le hlog4 (Real.log_le_log (by norm_num) h4))
    have hkey : L^4 * L^C' * (Real.log L)^4 ≤ (L+2)^(2*C' + 20) * Real.log (L + 3) := by
      rw [hpowadd]
      have hset : L^(4 + C') * (Real.log L)^4 ≤ L^(4 + C') * L^(C' + 16) :=
        mul_le_mul_of_nonneg_left hlogL4 (Real.rpow_nonneg hLnn _)
      have hadd : L^(4 + C') * L^(C' + 16) = L^(2*C' + 20) := by
        rw [← Real.rpow_add hLpos (4 + C') (C' + 16)]
        congr 1
        ring
      have hmono : L^(2*C' + 20) ≤ (L+2)^(2*C' + 20) :=
        Real.rpow_le_rpow hLnn (by linarith) (by linarith)
      calc L^(4 + C') * (Real.log L)^4
          ≤ L^(4 + C') * L^(C' + 16) := hset
        _ = L^(2*C' + 20) := hadd
        _ ≤ (L+2)^(2*C' + 20) := hmono
        _ ≤ (L+2)^(2*C' + 20) * Real.log (L + 3) := le_mul_of_one_le_right (by positivity) hlogL3
    have hfinal2 : 1024 * C₃^2 * C₂ * C'^3 * (x:ℝ) * L^4 * L^C' * (Real.log L)^4 / L^A'
        ≤ 1024 * C₃^2 * C₂ * C'^3 * (x:ℝ) * (L+2)^(2*C' + 20) * Real.log (L + 3) / L^A' := by
      have h2 : L^4 * L^C' * (Real.log L)^4 ≤ (L+2)^(2*C' + 20) * Real.log (L + 3) := hkey
      have h3 : 0 ≤ 1024 * C₃^2 * C₂ * C'^3 * (x:ℝ) / L^A' :=
        div_nonneg (by positivity) (Real.rpow_nonneg hLnn A')
      calc 1024 * C₃^2 * C₂ * C'^3 * (x:ℝ) * L^4 * L^C' * (Real.log L)^4 / L^A'
          = (1024 * C₃^2 * C₂ * C'^3 * (x:ℝ) / L^A') *
              (L^4 * L^C' * (Real.log L)^4) := by ring
        _ ≤ (1024 * C₃^2 * C₂ * C'^3 * (x:ℝ) / L^A') *
              ((L+2)^(2*C' + 20) * Real.log (L + 3)) := mul_le_mul_of_nonneg_left h2 h3
        _ = 1024 * C₃^2 * C₂ * C'^3 * (x:ℝ) * (L+2)^(2*C' + 20) * Real.log (L + 3) / L^A' := by
            ring
    refine le_trans hstep1 (le_trans hcomb (le_trans hfinal1 hfinal2))

end Work.NumberTheory.Chen.BTermCount
