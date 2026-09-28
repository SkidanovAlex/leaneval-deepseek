import Mathlib
import Submission.Work.HP.Q44Setup
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.kwin_spec
import Submission.Work.HP.Sig2.num_lattices_of
import Submission.Work.HP.Sig2.minkowski_prod
import Submission.Work.HP.Sig2.Tset_finite
import Submission.Work.HP.Q44Child.quartic_zero_bound
import Submission.Work.HP.Q44Child.lam_attained
import Submission.Work.HP.MDEstimates.q44_window_bounds
import Submission.Work.HP.Q44Main.latS_perlat_branch
import Submission.Work.HP.Q44Main.q44S_window_arith
import Submission.Work.HP.Q44Main.q44S_window_arith_b
import Submission.Work.HP.Q44Main.latS_window_count_red

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.HP.Q44Main

open Finset

/-! ## Elementary power identities for dyadic windows -/

private lemma pow2_sum_eq (k : Fin 3 → ℕ) :
    (2 : ℝ) ^ (2 * (∑ j : Fin 3, k j))
      = ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1) * (2 : ℝ) ^ (k 2)) ^ 2 := by
  have hsum : (∑ j : Fin 3, k j) = k 0 + k 1 + k 2 := by simp [Fin.sum_univ_three]
  rw [hsum, ← pow_add, ← pow_add, ← pow_mul]
  congr 1
  ring

private lemma pow2_4_eq (k : Fin 3 → ℕ) :
    (2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2)
      = ((2 : ℝ) ^ (k 0)) ^ 4 * ((2 : ℝ) ^ (k 1)) ^ 2 * ((2 : ℝ) ^ (k 2)) ^ 2 := by
  rw [← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  ring

private lemma pow2_c_eq (k : Fin 3 → ℕ) :
    (2 : ℝ) ^ (k 0 + k 1 + 3 * k 2)
      = (2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1) * ((2 : ℝ) ^ (k 2)) ^ 3 := by
  rw [← pow_mul, ← pow_add, ← pow_add]
  congr 1
  ring

/-! ## The two window-algebra estimates -/

private lemma alg_branchA {A0 A1 A2 Z CB KC : ℝ} (hA0 : 0 < A0) (hA02 : A0 ≤ A2)
    (hP1 : 1 ≤ A0 * A1 * A2) (hZ : 0 ≤ Z) (hCB : 0 < CB) (hKC : 0 < KC) :
    KC * (A0 ^ 6 * A1 ^ 4 * A2 ^ 2 + (A0 * A1 * A2) ^ 3)
        * (CB * Z ^ 3 / (A0 * A1 * A2)) ^ 2
      ≤ 2 * (CB ^ 2 * KC * (Z ^ 6 * (A0 * A1 * A2) ^ 2)) := by
  have hsq : A0 ^ 2 ≤ A2 ^ 2 := pow_le_pow_left₀ hA0.le hA02 2
  have h1 : A0 ^ 6 * A1 ^ 4 * A2 ^ 2 ≤ (A0 * A1 * A2) ^ 2 * (A0 * A1 * A2) ^ 2 := by
    have hA6 : A0 ^ 6 = A0 ^ 4 * A0 ^ 2 := by ring
    have hP4 : (A0 * A1 * A2) ^ 2 * (A0 * A1 * A2) ^ 2 = A0 ^ 4 * A1 ^ 4 * A2 ^ 4 := by ring
    rw [hA6, hP4]
    have hstep : A0 ^ 4 * A1 ^ 4 * A2 ^ 2 * A0 ^ 2 ≤ A0 ^ 4 * A1 ^ 4 * A2 ^ 2 * A2 ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    calc A0 ^ 4 * A0 ^ 2 * A1 ^ 4 * A2 ^ 2 = A0 ^ 4 * A1 ^ 4 * A2 ^ 2 * A0 ^ 2 := by ring
      _ ≤ A0 ^ 4 * A1 ^ 4 * A2 ^ 2 * A2 ^ 2 := hstep
      _ = A0 ^ 4 * A1 ^ 4 * A2 ^ 4 := by ring
  have h2 : (A0 * A1 * A2) ^ 3 ≤ (A0 * A1 * A2) ^ 2 * (A0 * A1 * A2) ^ 2 := by
    have h3 : (A0 * A1 * A2) ^ 3 * 1 ≤ (A0 * A1 * A2) ^ 3 * (A0 * A1 * A2) :=
      mul_le_mul_of_nonneg_left hP1 (by positivity)
    calc (A0 * A1 * A2) ^ 3 = (A0 * A1 * A2) ^ 3 * 1 := by ring
      _ ≤ (A0 * A1 * A2) ^ 3 * (A0 * A1 * A2) := h3
      _ = (A0 * A1 * A2) ^ 2 * (A0 * A1 * A2) ^ 2 := by ring
  have hsum : A0 ^ 6 * A1 ^ 4 * A2 ^ 2 + (A0 * A1 * A2) ^ 3
      ≤ 2 * ((A0 * A1 * A2) ^ 2 * (A0 * A1 * A2) ^ 2) := by linarith
  have hdiv : (CB * Z ^ 3 / (A0 * A1 * A2)) ^ 2 = CB ^ 2 * Z ^ 6 / (A0 * A1 * A2) ^ 2 := by
    rw [div_pow, mul_pow, ← pow_mul]
  rw [hdiv]
  have hkey : (A0 ^ 6 * A1 ^ 4 * A2 ^ 2 + (A0 * A1 * A2) ^ 3) / (A0 * A1 * A2) ^ 2
      ≤ 2 * (A0 * A1 * A2) ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    linarith [hsum]
  calc KC * (A0 ^ 6 * A1 ^ 4 * A2 ^ 2 + (A0 * A1 * A2) ^ 3) * (CB ^ 2 * Z ^ 6 / (A0 * A1 * A2) ^ 2)
      = (KC * CB ^ 2 * Z ^ 6)
          * ((A0 ^ 6 * A1 ^ 4 * A2 ^ 2 + (A0 * A1 * A2) ^ 3) / (A0 * A1 * A2) ^ 2) := by ring
    _ ≤ (KC * CB ^ 2 * Z ^ 6) * (2 * (A0 * A1 * A2) ^ 2) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = 2 * (CB ^ 2 * KC * (Z ^ 6 * (A0 * A1 * A2) ^ 2)) := by ring

private lemma alg_branchB {A0 A1 A2 Z CB KC : ℝ} (hA0 : 0 < A0) (hA1 : 0 < A1) (hA2 : 0 < A2)
    (hZ : 0 ≤ Z) (hCB : 0 < CB) (hKC : 0 < KC) :
    KC * (A0 ^ 6 * A1 ^ 4 * A2 ^ 2 + (A0 * A1 * A2) ^ 3) * (CB * Z ^ 2 / (A0 * A1)) ^ 2
      = CB ^ 2 * KC * (Z ^ 4 * (A0 ^ 4 * A1 ^ 2 * A2 ^ 2 + A0 * A1 * A2 ^ 3)) := by
  have h1 : (CB * Z ^ 2 / (A0 * A1)) ^ 2 = CB ^ 2 * Z ^ 4 / (A0 * A1) ^ 2 := by
    rw [div_pow, mul_pow, ← pow_mul]
  rw [h1]
  field_simp

theorem latS_sum_red :
    ∃ C : ℝ, 0 < C ∧ ∀ (Z Δ : ℝ), 1 ≤ Z → 1 ≤ Δ →
      ∀ (c : Mon 4 4 → ℤ), c ≠ 0 → ¬ Irreducible (formOf 4 4 c) →
      ∀ (T : Finset (Submodule ℤ (Fin 5 → ℤ))),
        (∀ L ∈ T, IsPrimLat L ∧ rk L = 3 ∧ detL L ≤ Δ + 1 ∧ lam L 1 ≤ Z ∧ lam L 2 ≤ Z
          ∧ c ∈ vanishOn L) →
        (∑ L ∈ T, (ballCount L Z : ℝ) ^ 2)
          ≤ C * (Z ^ 4 * Δ ^ 3 + Z ^ 6 * Δ ^ 2) * Real.log (2 * Δ) ^ 2 := by
  classical
  obtain ⟨Kmk0, hKmk0pos, hmink0⟩ := Sig2.minkowski_prod (ι := Fin 5)
  set Kmink : ℝ := max Kmk0 1 with hKminkdef
  have hKmink1 : 1 ≤ Kmink := le_max_right _ _
  have hmink : ∀ L : Submodule ℤ (Fin 5 → ℤ),
      (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ Kmink * detL L := by
    intro L
    refine (hmink0 L).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (detL_nonneg L)
  obtain ⟨CB, hCBpos, hCB⟩ := latS_perlat_branch
  obtain ⟨KC, hKCpos, hKC⟩ := latS_window_count_red
  obtain ⟨KarA, hKarApos, hArAall⟩ := q44S_window_arith Kmink hKmink1
  obtain ⟨KarB, hKarBpos, hArBall⟩ := q44S_window_arith_b Kmink hKmink1
  refine ⟨2 * CB ^ 2 * KC * (KarA + KarB) + 1, by positivity, ?_⟩
  intro Z Δ hZ hΔ c hc hred T hT
  have hZ0 : (0 : ℝ) ≤ Z := le_trans zero_le_one hZ
  have hΔ0 : (0 : ℝ) ≤ Δ := le_trans zero_le_one hΔ
  have hlogsq : (0 : ℝ) ≤ Real.log (2 * Δ) ^ 2 := sq_nonneg _
  obtain ⟨hArA, _⟩ := hArAall Δ hΔ
  obtain hArB := hArBall Δ hΔ
  set N : ℕ := ⌈Real.logb 2 (8 * Kmink * (Δ + 1))⌉₊ with hNdef
  set box : Finset (Fin 3 → ℕ) :=
    Fintype.piFinset (fun _ : Fin 3 => Finset.range (N + 1)) with hboxdef
  have hwin : ∀ L ∈ T, Monotone (kwin 3 L) ∧ (∑ j : Fin 3, kwin 3 L j) ≤ N ∧
      (∀ j : Fin 3, kwin 3 L j ≤ N) := by
    intro L hL
    obtain ⟨-, hrk, hdet, -, -, -⟩ := hT L hL
    exact MDEstimates.q44_window_bounds Kmink hKmink1 hmink Δ hΔ L hrk hdet
  have hfib : (∑ L ∈ T, (ballCount L Z : ℝ) ^ 2)
      = ∑ k ∈ box, ∑ L ∈ T.filter (fun L => kwin 3 L = k), (ballCount L Z : ℝ) ^ 2 := by
    refine (Finset.sum_fiberwise_of_maps_to ?_ (fun L => (ballCount L Z : ℝ) ^ 2)).symm
    intro L hL
    rw [hboxdef, Fintype.mem_piFinset]
    intro j
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le ((hwin L hL).2.2 j)
  -- ### per-fiber bound
  have key : ∀ k ∈ box,
      (∑ L ∈ T.filter (fun L => kwin 3 L = k), (ballCount L Z : ℝ) ^ 2)
        ≤ (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then
             (if (2 : ℝ) ^ (k 2) ≤ 2 * Z then
                2 * (CB ^ 2 * KC * (Z ^ 6 * (2 : ℝ) ^ (2 * (∑ j : Fin 3, k j))))
              else CB ^ 2 * KC * (Z ^ 4 * ((2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2)
                + (2 : ℝ) ^ (k 0 + k 1 + 3 * k 2))))
           else 0) := by
    intro k hk
    by_cases hM : Monotone k ∧ (∑ j : Fin 3, k j) ≤ N
    · rw [if_pos hM]
      set F : Finset (Submodule ℤ (Fin 5 → ℤ)) := T.filter (fun L => kwin 3 L = k) with hFdef
      have hFk : ∀ L ∈ F, kwin 3 L = k := fun L hL => (Finset.mem_filter.mp hL).2
      have hFT : ∀ L ∈ F, L ∈ T := fun L hL => (Finset.mem_filter.mp hL).1
      have hs0 : (1 : ℝ) ≤ (2 : ℝ) ^ (k 0) := one_le_pow₀ (by norm_num)
      have hs01 : (2 : ℝ) ^ (k 0) ≤ (2 : ℝ) ^ (k 1) :=
        pow_le_pow_right₀ (by norm_num) (hM.1 (by decide))
      have hs12 : (2 : ℝ) ^ (k 1) ≤ (2 : ℝ) ^ (k 2) :=
        pow_le_pow_right₀ (by norm_num) (hM.1 (by decide))
      -- cardinality of the fiber
      set S : Set (Submodule ℤ (Fin 5 → ℤ)) :=
        {L | IsPrimLat L ∧ rk L = 3 ∧ (∀ j : Fin 3, lam L (j.val + 1) ≤ (2 : ℝ) ^ (k j))
          ∧ c ∈ vanishOn L} with hSdef
      have hsub : (F : Set (Submodule ℤ (Fin 5 → ℤ))) ⊆ S := by
        intro L hL
        obtain ⟨hprim, hrk, -, h1, h2, hv⟩ := hT L (hFT L hL)
        have hkL : kwin 3 L = k := hFk L hL
        refine ⟨hprim, hrk, fun j => ?_, hv⟩
        have h := (kwin_spec (Fin 5) 3 L (by norm_num) hrk).1 j
        rw [hkL] at h
        exact h
      have hfin : S.Finite := by
        refine (Sig2.Tset_finite 3 (fun j : Fin 3 => (2 : ℝ) ^ (k j))).subset ?_
        intro L hL
        exact ⟨hL.1, hL.2.1, hL.2.2.1⟩
      have hcard1 : (F.card : ℝ) ≤ (S.ncard : ℝ) := by
        have h := Set.ncard_le_ncard hsub hfin
        rw [Set.ncard_coe_finset] at h
        exact_mod_cast h
      have hcard2 : (S.ncard : ℝ) ≤ KC * (((2 : ℝ) ^ (k 0)) ^ 6 * ((2 : ℝ) ^ (k 1)) ^ 4
          * ((2 : ℝ) ^ (k 2)) ^ 2 + ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1) * (2 : ℝ) ^ (k 2)) ^ 3) :=
        hKC c hc hred (fun j => (2 : ℝ) ^ (k j)) hs0 hs01 hs12
      have hcard : (F.card : ℝ) ≤ KC * (((2 : ℝ) ^ (k 0)) ^ 6 * ((2 : ℝ) ^ (k 1)) ^ 4
          * ((2 : ℝ) ^ (k 2)) ^ 2 + ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1) * (2 : ℝ) ^ (k 2)) ^ 3) :=
        hcard1.trans hcard2
      by_cases hcond : (2 : ℝ) ^ (k 2) ≤ 2 * Z
      · rw [if_pos hcond]
        set A0 : ℝ := (2 : ℝ) ^ (k 0) with hA0def
        set A1r : ℝ := (2 : ℝ) ^ (k 1) with hA1def
        set A2r : ℝ := (2 : ℝ) ^ (k 2) with hA2def
        have hA0pos : 0 < A0 := by rw [hA0def]; positivity
        have hA1pos : 0 < A1r := by rw [hA1def]; positivity
        have hA2pos : 0 < A2r := by rw [hA2def]; positivity
        have hA02 : A0 ≤ A2r := by
          rw [hA0def, hA2def]; exact hs01.trans hs12
        have hP1 : 1 ≤ A0 * A1r * A2r := by
          rw [hA0def, hA1def, hA2def]
          have h0 : (1 : ℝ) ≤ (2 : ℝ) ^ (k 0) := one_le_pow₀ (by norm_num)
          have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k 1) := one_le_pow₀ (by norm_num)
          have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (k 2) := one_le_pow₀ (by norm_num)
          have ha : (1 : ℝ) ≤ (2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1) := by
            calc (1 : ℝ) = 1 * 1 := by ring
              _ ≤ (2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1) :=
                  mul_le_mul h0 h1 (by norm_num) (by positivity)
          calc (1 : ℝ) = 1 * 1 := by ring
            _ ≤ ((2 : ℝ) ^ (k 0) * (2 : ℝ) ^ (k 1)) * (2 : ℝ) ^ (k 2) :=
                mul_le_mul ha h2 (by norm_num) (by positivity)
        have hcardA : (F.card : ℝ) ≤ KC * (A0 ^ 6 * A1r ^ 4 * A2r ^ 2 + (A0 * A1r * A2r) ^ 3) := by
          rw [hA0def, hA1def, hA2def] at hcard
          exact hcard
        have hper : ∀ L ∈ F, (ballCount L Z : ℝ) ^ 2 ≤
            (CB * Z ^ 3 / (A0 * A1r * A2r)) ^ 2 := by
          intro L hL
          obtain ⟨-, hrk, -, h1, h2, -⟩ := hT L (hFT L hL)
          have hkL : kwin 3 L = k := hFk L hL
          have hb := (hCB L hrk Z hZ h1 h2).1 (by rw [hkL]; exact hcond)
          rw [hkL] at hb
          have hb' : (ballCount L Z : ℝ) ≤ CB * Z ^ 3 / (A0 * A1r * A2r) := by
            rw [hA0def, hA1def, hA2def]
            exact hb
          exact pow_le_pow_left₀ (Nat.cast_nonneg _) hb' 2
        have hsum : (∑ L ∈ F, (ballCount L Z : ℝ) ^ 2) ≤
            (F.card : ℝ) * (CB * Z ^ 3 / (A0 * A1r * A2r)) ^ 2 := by
          calc (∑ L ∈ F, (ballCount L Z : ℝ) ^ 2)
              ≤ ∑ _L ∈ F, (CB * Z ^ 3 / (A0 * A1r * A2r)) ^ 2 := Finset.sum_le_sum hper
            _ = (F.card : ℝ) * (CB * Z ^ 3 / (A0 * A1r * A2r)) ^ 2 := by
                rw [Finset.sum_const, nsmul_eq_mul]
        calc (∑ L ∈ F, (ballCount L Z : ℝ) ^ 2)
            ≤ (F.card : ℝ) * (CB * Z ^ 3 / (A0 * A1r * A2r)) ^ 2 := hsum
          _ ≤ KC * (A0 ^ 6 * A1r ^ 4 * A2r ^ 2 + (A0 * A1r * A2r) ^ 3)
                * (CB * Z ^ 3 / (A0 * A1r * A2r)) ^ 2 :=
              mul_le_mul_of_nonneg_right hcardA (by positivity)
          _ ≤ 2 * (CB ^ 2 * KC * (Z ^ 6 * (A0 * A1r * A2r) ^ 2)) :=
              alg_branchA hA0pos hA02 hP1 hZ0 hCBpos hKCpos
          _ = 2 * (CB ^ 2 * KC * (Z ^ 6 * (2 : ℝ) ^ (2 * (∑ j : Fin 3, k j)))) := by
              rw [← pow2_sum_eq k]
      · rw [if_neg hcond]
        push_neg at hcond
        set A0 : ℝ := (2 : ℝ) ^ (k 0) with hA0def
        set A1r : ℝ := (2 : ℝ) ^ (k 1) with hA1def
        set A2r : ℝ := (2 : ℝ) ^ (k 2) with hA2def
        have hA0pos : 0 < A0 := by rw [hA0def]; positivity
        have hA1pos : 0 < A1r := by rw [hA1def]; positivity
        have hA2pos : 0 < A2r := by rw [hA2def]; positivity
        have hcardA : (F.card : ℝ) ≤ KC * (A0 ^ 6 * A1r ^ 4 * A2r ^ 2 + (A0 * A1r * A2r) ^ 3) := by
          rw [hA0def, hA1def, hA2def] at hcard
          exact hcard
        have hper : ∀ L ∈ F, (ballCount L Z : ℝ) ^ 2 ≤ (CB * Z ^ 2 / (A0 * A1r)) ^ 2 := by
          intro L hL
          obtain ⟨-, hrk, -, h1, h2, -⟩ := hT L (hFT L hL)
          have hkL : kwin 3 L = k := hFk L hL
          have hb := (hCB L hrk Z hZ h1 h2).2 (by rw [hkL]; exact hcond)
          rw [hkL] at hb
          have hb' : (ballCount L Z : ℝ) ≤ CB * Z ^ 2 / (A0 * A1r) := by
            rw [hA0def, hA1def]
            exact hb
          exact pow_le_pow_left₀ (Nat.cast_nonneg _) hb' 2
        have hsum : (∑ L ∈ F, (ballCount L Z : ℝ) ^ 2) ≤
            (F.card : ℝ) * (CB * Z ^ 2 / (A0 * A1r)) ^ 2 := by
          calc (∑ L ∈ F, (ballCount L Z : ℝ) ^ 2)
              ≤ ∑ _L ∈ F, (CB * Z ^ 2 / (A0 * A1r)) ^ 2 := Finset.sum_le_sum hper
            _ = (F.card : ℝ) * (CB * Z ^ 2 / (A0 * A1r)) ^ 2 := by
                rw [Finset.sum_const, nsmul_eq_mul]
        calc (∑ L ∈ F, (ballCount L Z : ℝ) ^ 2)
            ≤ (F.card : ℝ) * (CB * Z ^ 2 / (A0 * A1r)) ^ 2 := hsum
          _ ≤ KC * (A0 ^ 6 * A1r ^ 4 * A2r ^ 2 + (A0 * A1r * A2r) ^ 3)
                * (CB * Z ^ 2 / (A0 * A1r)) ^ 2 :=
              mul_le_mul_of_nonneg_right hcardA (by positivity)
          _ = CB ^ 2 * KC * (Z ^ 4 * (A0 ^ 4 * A1r ^ 2 * A2r ^ 2 + A0 * A1r * A2r ^ 3)) :=
              alg_branchB hA0pos hA1pos hA2pos hZ0 hCBpos hKCpos
          _ = CB ^ 2 * KC * (Z ^ 4 * ((2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2)
                + (2 : ℝ) ^ (k 0 + k 1 + 3 * k 2))) := by
              rw [← pow2_4_eq k, ← pow2_c_eq k]
    · rw [if_neg hM]
      have hemp : T.filter (fun L => kwin 3 L = k) = ∅ := by
        rw [← Finset.not_nonempty_iff_eq_empty]
        rintro ⟨L, hL⟩
        rw [Finset.mem_filter] at hL
        exact hM ⟨by rw [← hL.2]; exact (hwin L hL.1).1,
          by rw [← hL.2]; exact (hwin L hL.1).2.1⟩
      rw [hemp]
      simp
  -- ### summation over the windows
  have hsplit : (∑ k ∈ box, (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then
        (if (2 : ℝ) ^ (k 2) ≤ 2 * Z then
          2 * (CB ^ 2 * KC * (Z ^ 6 * (2 : ℝ) ^ (2 * (∑ j : Fin 3, k j))))
        else CB ^ 2 * KC * (Z ^ 4 * ((2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2)
          + (2 : ℝ) ^ (k 0 + k 1 + 3 * k 2)))) else 0))
      ≤ (∑ k ∈ box, (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then
          2 * (CB ^ 2 * KC * (Z ^ 6 * (2 : ℝ) ^ (2 * (∑ j : Fin 3, k j)))) else 0))
        + (∑ k ∈ box, (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then
          CB ^ 2 * KC * (Z ^ 4 * ((2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2)
            + (2 : ℝ) ^ (k 0 + k 1 + 3 * k 2))) else 0)) := by
    have hpt : ∀ k : Fin 3 → ℕ,
        (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then
          (if (2 : ℝ) ^ (k 2) ≤ 2 * Z then
            2 * (CB ^ 2 * KC * (Z ^ 6 * (2 : ℝ) ^ (2 * (∑ j : Fin 3, k j))))
          else CB ^ 2 * KC * (Z ^ 4 * ((2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2)
            + (2 : ℝ) ^ (k 0 + k 1 + 3 * k 2)))) else 0)
        ≤ (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then
            2 * (CB ^ 2 * KC * (Z ^ 6 * (2 : ℝ) ^ (2 * (∑ j : Fin 3, k j)))) else 0)
          + (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then
            CB ^ 2 * KC * (Z ^ 4 * ((2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2)
              + (2 : ℝ) ^ (k 0 + k 1 + 3 * k 2))) else 0) := by
      intro k
      by_cases hM : Monotone k ∧ (∑ j : Fin 3, k j) ≤ N
      · rw [if_pos hM, if_pos hM, if_pos hM]
        have h2 : (0 : ℝ) ≤ CB ^ 2 * KC * (Z ^ 4 * ((2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2)
            + (2 : ℝ) ^ (k 0 + k 1 + 3 * k 2))) := by positivity
        have h3 : (0 : ℝ) ≤ 2 * (CB ^ 2 * KC * (Z ^ 6 * (2 : ℝ) ^ (2 * (∑ j : Fin 3, k j)))) :=
          by positivity
        by_cases hc2 : (2 : ℝ) ^ (k 2) ≤ 2 * Z
        · rw [if_pos hc2]
          linarith
        · rw [if_neg hc2]
          linarith
      · rw [if_neg hM, if_neg hM, if_neg hM]
        simp
    calc (∑ k ∈ box, _)
        ≤ ∑ k ∈ box, ((if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then
              2 * (CB ^ 2 * KC * (Z ^ 6 * (2 : ℝ) ^ (2 * (∑ j : Fin 3, k j)))) else 0)
            + (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then
              CB ^ 2 * KC * (Z ^ 4 * ((2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2)
                + (2 : ℝ) ^ (k 0 + k 1 + 3 * k 2))) else 0)) :=
          Finset.sum_le_sum (fun k _ => hpt k)
      _ = (∑ k ∈ box, (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then
              2 * (CB ^ 2 * KC * (Z ^ 6 * (2 : ℝ) ^ (2 * (∑ j : Fin 3, k j)))) else 0))
            + (∑ k ∈ box, (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then
              CB ^ 2 * KC * (Z ^ 4 * ((2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2)
                + (2 : ℝ) ^ (k 0 + k 1 + 3 * k 2))) else 0)) :=
          Finset.sum_add_distrib
  -- rewrite the two arithmetic sums
  have hArA' : (∑ k ∈ box, (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then
        (2 : ℝ) ^ (2 * (∑ j : Fin 3, k j)) else 0)) ≤ KarA * Δ ^ 2 * Real.log (2 * Δ) ^ 2 := by
    rw [hboxdef, hNdef]
    exact hArA
  have hArB' : (∑ k ∈ box, (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then
        (2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2)
          + (2 : ℝ) ^ (k 0 + k 1 + 3 * k 2) else 0)) ≤ KarB * Δ ^ 3 * Real.log (2 * Δ) ^ 2 := by
    rw [hboxdef, hNdef]
    exact hArB
  have hsumA : (∑ k ∈ box, (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then
        2 * (CB ^ 2 * KC * (Z ^ 6 * (2 : ℝ) ^ (2 * (∑ j : Fin 3, k j)))) else 0))
      ≤ 2 * CB ^ 2 * KC * Z ^ 6 * (KarA * Δ ^ 2 * Real.log (2 * Δ) ^ 2) := by
    have : (∑ k ∈ box, (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then
        2 * (CB ^ 2 * KC * (Z ^ 6 * (2 : ℝ) ^ (2 * (∑ j : Fin 3, k j)))) else 0))
        = 2 * CB ^ 2 * KC * Z ^ 6 * (∑ k ∈ box, (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then
            (2 : ℝ) ^ (2 * (∑ j : Fin 3, k j)) else 0)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      by_cases hM : Monotone k ∧ (∑ j : Fin 3, k j) ≤ N
      · rw [if_pos hM, if_pos hM]; ring
      · rw [if_neg hM, if_neg hM]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hArA' (by positivity)
  have hsumB : (∑ k ∈ box, (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then
        CB ^ 2 * KC * (Z ^ 4 * ((2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2)
          + (2 : ℝ) ^ (k 0 + k 1 + 3 * k 2))) else 0))
      ≤ CB ^ 2 * KC * Z ^ 4 * (KarB * Δ ^ 3 * Real.log (2 * Δ) ^ 2) := by
    have : (∑ k ∈ box, (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then
        CB ^ 2 * KC * (Z ^ 4 * ((2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2)
          + (2 : ℝ) ^ (k 0 + k 1 + 3 * k 2))) else 0))
        = CB ^ 2 * KC * Z ^ 4 * (∑ k ∈ box, (if Monotone k ∧ (∑ j : Fin 3, k j) ≤ N then
            (2 : ℝ) ^ (4 * k 0 + 2 * k 1 + 2 * k 2) + (2 : ℝ) ^ (k 0 + k 1 + 3 * k 2) else 0)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      by_cases hM : Monotone k ∧ (∑ j : Fin 3, k j) ≤ N
      · rw [if_pos hM, if_pos hM]; ring
      · rw [if_neg hM, if_neg hM]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_left hArB' (by positivity)
  have hmain : (∑ L ∈ T, (ballCount L Z : ℝ) ^ 2)
      ≤ 2 * CB ^ 2 * KC * Z ^ 6 * (KarA * Δ ^ 2 * Real.log (2 * Δ) ^ 2)
        + CB ^ 2 * KC * Z ^ 4 * (KarB * Δ ^ 3 * Real.log (2 * Δ) ^ 2) :=
    le_trans (le_trans hfib.le (Finset.sum_le_sum (fun k hk => key k hk)))
      (le_trans hsplit (add_le_add hsumA hsumB))
  -- final arithmetic
  have hCB2 : (0 : ℝ) ≤ CB ^ 2 := by positivity
  have hKCn : (0 : ℝ) ≤ KC := hKCpos.le
  have hZ4 : (0 : ℝ) ≤ Z ^ 4 := by positivity
  have hZ6 : (0 : ℝ) ≤ Z ^ 6 := by positivity
  have hD2 : (0 : ℝ) ≤ Δ ^ 2 := by positivity
  have hD3 : (0 : ℝ) ≤ Δ ^ 3 := by positivity
  have hlog2n : (0 : ℝ) ≤ Real.log (2 * Δ) ^ 2 := hlogsq
  have e1 : 2 * CB ^ 2 * KC * Z ^ 6 * (KarA * Δ ^ 2 * Real.log (2 * Δ) ^ 2)
      ≤ 2 * CB ^ 2 * KC * (KarA + KarB) * (Z ^ 6 * Δ ^ 2) * Real.log (2 * Δ) ^ 2 := by
    have hle : KarA ≤ KarA + KarB := by linarith [hKarBpos]
    have h1 : KarA * Δ ^ 2 * Real.log (2 * Δ) ^ 2
        ≤ (KarA + KarB) * Δ ^ 2 * Real.log (2 * Δ) ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ hlog2n
      apply mul_le_mul_of_nonneg_right hle hD2
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * CB ^ 2 * KC * Z ^ 6)
    calc 2 * CB ^ 2 * KC * Z ^ 6 * (KarA * Δ ^ 2 * Real.log (2 * Δ) ^ 2)
        ≤ 2 * CB ^ 2 * KC * Z ^ 6 * ((KarA + KarB) * Δ ^ 2 * Real.log (2 * Δ) ^ 2) := h2
      _ = 2 * CB ^ 2 * KC * (KarA + KarB) * (Z ^ 6 * Δ ^ 2) * Real.log (2 * Δ) ^ 2 := by ring
  have e2 : CB ^ 2 * KC * Z ^ 4 * (KarB * Δ ^ 3 * Real.log (2 * Δ) ^ 2)
      ≤ 2 * CB ^ 2 * KC * (KarA + KarB) * (Z ^ 4 * Δ ^ 3) * Real.log (2 * Δ) ^ 2 := by
    have hle : KarB ≤ 2 * (KarA + KarB) := by
      have h0 : (0 : ℝ) ≤ KarA + KarB := by linarith [hKarApos, hKarBpos]
      have h1 : KarB ≤ KarA + KarB := by linarith [hKarApos]
      linarith
    have h1 : KarB * Δ ^ 3 * Real.log (2 * Δ) ^ 2
        ≤ 2 * ((KarA + KarB) * Δ ^ 3 * Real.log (2 * Δ) ^ 2) := by
      calc KarB * Δ ^ 3 * Real.log (2 * Δ) ^ 2
          = KarB * (Δ ^ 3 * Real.log (2 * Δ) ^ 2) := by ring
        _ ≤ (2 * (KarA + KarB)) * (Δ ^ 3 * Real.log (2 * Δ) ^ 2) :=
            mul_le_mul_of_nonneg_right hle (by positivity)
        _ = 2 * ((KarA + KarB) * Δ ^ 3 * Real.log (2 * Δ) ^ 2) := by ring
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ CB ^ 2 * KC * Z ^ 4)
    calc CB ^ 2 * KC * Z ^ 4 * (KarB * Δ ^ 3 * Real.log (2 * Δ) ^ 2)
        ≤ CB ^ 2 * KC * Z ^ 4 * (2 * ((KarA + KarB) * Δ ^ 3 * Real.log (2 * Δ) ^ 2)) := h2
      _ = 2 * CB ^ 2 * KC * (KarA + KarB) * (Z ^ 4 * Δ ^ 3) * Real.log (2 * Δ) ^ 2 := by ring
  have e3 : 2 * CB ^ 2 * KC * (KarA + KarB) * (Z ^ 6 * Δ ^ 2) * Real.log (2 * Δ) ^ 2
        + 2 * CB ^ 2 * KC * (KarA + KarB) * (Z ^ 4 * Δ ^ 3) * Real.log (2 * Δ) ^ 2
      ≤ (2 * CB ^ 2 * KC * (KarA + KarB) + 1) * (Z ^ 4 * Δ ^ 3 + Z ^ 6 * Δ ^ 2)
          * Real.log (2 * Δ) ^ 2 := by
    have hexp : (2 * CB ^ 2 * KC * (KarA + KarB) + 1) * (Z ^ 4 * Δ ^ 3 + Z ^ 6 * Δ ^ 2)
          * Real.log (2 * Δ) ^ 2
        = 2 * CB ^ 2 * KC * (KarA + KarB) * (Z ^ 4 * Δ ^ 3) * Real.log (2 * Δ) ^ 2
          + 2 * CB ^ 2 * KC * (KarA + KarB) * (Z ^ 6 * Δ ^ 2) * Real.log (2 * Δ) ^ 2
          + (Z ^ 4 * Δ ^ 3 + Z ^ 6 * Δ ^ 2) * Real.log (2 * Δ) ^ 2 := by ring
    rw [hexp]
    have hnn : (0 : ℝ) ≤ (Z ^ 4 * Δ ^ 3 + Z ^ 6 * Δ ^ 2) * Real.log (2 * Δ) ^ 2 := by positivity
    linarith [hnn]
  calc (∑ L ∈ T, (ballCount L Z : ℝ) ^ 2)
      ≤ 2 * CB ^ 2 * KC * Z ^ 6 * (KarA * Δ ^ 2 * Real.log (2 * Δ) ^ 2)
        + CB ^ 2 * KC * Z ^ 4 * (KarB * Δ ^ 3 * Real.log (2 * Δ) ^ 2) := hmain
    _ ≤ 2 * CB ^ 2 * KC * (KarA + KarB) * (Z ^ 6 * Δ ^ 2) * Real.log (2 * Δ) ^ 2
        + 2 * CB ^ 2 * KC * (KarA + KarB) * (Z ^ 4 * Δ ^ 3) * Real.log (2 * Δ) ^ 2 :=
        add_le_add e1 e2
    _ ≤ (2 * CB ^ 2 * KC * (KarA + KarB) + 1) * (Z ^ 4 * Δ ^ 3 + Z ^ 6 * Δ ^ 2)
          * Real.log (2 * Δ) ^ 2 := e3

end Work.HP.Q44Main
