import Mathlib
import Submission.Work.Prop36SW.chainMainA_glue
import Submission.Work.Prop36SW.reachEntryA
import Submission.Work.Prop36SW.reachStepA
import Submission.Work.Prop36SW.roundToNextStateS
import Submission.Work.Prop36SW.smallWindowConcl
import Submission.Work.Peluse.Prop36SW.uNormPowTransferTwo

/-!
# `Work.Peluse.prop36SW_body`: the non-degenerate branch of the node

`Work.Peluse.C46.Prop36SW P` is `∀ D, ∃ s, 2 ≤ s ∧ ∀ A₀, ...`.  This module proves the body of
that statement at a *fixed* index datum `D` with `2 ≤ Fintype.card (D.I (d-1))`, i.e. the
non-degenerate branch of `Work.Peluse.prop36SW_of_ladderA`, so that the node can be assembled from
it together with a treatment of the degenerate data (`card (D.I (d-1)) ≤ 1`).

The proof is the §5 chain of `NOTES_prop36SW_of_ladderA_SESSION12.md` plus the two-regime split on
the window `x = η^K δ'^d M^d / A`:

* `x ≤ 1`: the window `⌊max 1 x⌋` is `1`, and `Work.Prop36SW.smallWindowConcl` gives the claim
  directly from `η ≤ D.famAvg` (no chain);
* `x > 1`: the chain's constants give `Cs ≤ η^{M₀}H`, `(H+1)^d ≤ (2^d A₀) N`, and the chain's
  output `Lw₀ ≥ c₀η^{e₀}(H+1)^d` together with the ambient/level transfer
  `Work.Peluse.Prop36SW.uNormPowTransferTwo`.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

open scoped BigOperators
open Polynomial

namespace Work.Peluse

noncomputable section

open Work.Peluse.UControl
open Work.Prop36SW

/-- **The body of `Prop36SW` at a non-degenerate datum.** -/
theorem prop36SW_body (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (h : Work.Peluse.C46.PeluseLadderA) (D : IdxDatum)
    (hI : 2 ≤ Fintype.card (D.I (P.natDegree - 1))) :
    ∃ s : ℕ, 2 ≤ s ∧
      ∀ A₀ : ℝ, 1 ≤ A₀ → ∃ A : ℝ, 1 ≤ A ∧ ∃ K : ℕ, 1 ≤ K ∧
      ∀ (N M : ℕ) (f : ℤ → ℂ) (η δ' : ℝ),
        2 ≤ P.natDegree → 1 ≤ N → 1 ≤ M → (N : ℝ) ≤ A₀ * (M : ℝ) ^ P.natDegree →
        (M : ℝ) ^ P.natDegree ≤ A₀ * (N : ℝ) →
        0 < η → η ≤ 1 → 0 < δ' → A * δ' ≤ η ^ K →
        2 ≤ (⌊δ' * (M : ℝ)⌋).toNat →
        (∀ x : ℤ, ‖f x‖ ≤ 1) → SupportIn f N →
        A * (η * δ') ^ (-(K : ℤ)) ≤ (N : ℝ) →
        η ≤ D.famAvg P.natDegree (⌊δ' * (M : ℝ)⌋).toNat P.leadingCoeff N f →
        η ^ K ≤ A * uNormPow s
          (arithIcc (P.natDegree.factorial * P.leadingCoeff)
            (⌊max (1 : ℝ) (η ^ K * δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree / A)⌋).toNat)
          (symIcc N) f := by
  classical
  have hc : P.leadingCoeff ≠ 0 := by
    intro h0
    have h1 : P = 0 := Polynomial.leadingCoeff_eq_zero.mp h0
    rw [h1] at hd; simp at hd
  have hW : ∀ m : ℕ, Work.Peluse.Prop36SW.RoundStmtW (m + 1) := roundPeelAuxW h
  have hRound : Work.Prop36SW.RoundAll D P.natDegree P.leadingCoeff := fun m Λ kω hk hm hΛ =>
    roundToNextStateS hW D P.natDegree P.leadingCoeff m Λ kω hk hm hΛ
  have hLast : ∀ (Λ : ℕ) (kω : SlotSet (D.S 1) (fun _ => 1) → ℕ),
      Work.Prop36SW.LastStep D P.natDegree P.leadingCoeff Λ kω := fun Λ kω =>
    lastStep hW D P.natDegree P.leadingCoeff Λ kω
      (card_S_pos_of_card_I D P.natDegree hI (j := 1) (by omega)) hd
  obtain ⟨S, hS2, hmain⟩ := chainMainA_glue D P.natDegree P.leadingCoeff hd hc
    (reachEntryA D P.natDegree P.leadingCoeff hd hc)
    (reachStepA D P.natDegree P.leadingCoeff hd hc hRound) hLast hI
  obtain ⟨C₂, E₂, hC₂, hE₂, htrans⟩ :=
    Work.Peluse.Prop36SW.uNormPowTransferTwo
      (max S (Fintype.card (D.I (P.natDegree - 1)) + 1)) S hS2 (le_max_left _ _)
  refine ⟨max S (Fintype.card (D.I (P.natDegree - 1)) + 1), le_trans hS2 (le_max_left _ _), ?_⟩
  intro A₀ hA₀
  obtain ⟨C, E, c₀, e₀, M₀, Cs, hC, hc₀, he₀, hM₀, hCs, hchain⟩ :=
    hmain (max 1 ((2 : ℝ) ^ P.natDegree * A₀)) (le_max_left _ _)
  -- the constant `A` as the maximum of a finite list (so that every component bound is a
  -- one-liner `Finset.le_max'`)
  set CL : Finset ℝ := {1, A₀ + A₀, (2 * Cs) ^ P.natDegree, (2 : ℝ) ^ P.natDegree / c₀,
      (2 : ℝ) ^ (max S (Fintype.card (D.I (P.natDegree - 1)) + 1)), C₂ * C ^ E₂,
      (C₂ * C ^ E₂)⁻¹} with hCL
  set A : ℝ := CL.max' (by rw [hCL]; simp) with hA_def
  set KL : Finset ℕ := {2 ^ (max S (Fintype.card (D.I (P.natDegree - 1)) + 1)),
      P.natDegree * (M₀ + 1) + 1, e₀ + 1, Nat.ceil (E₂ * E) + 1} with hKL
  set KK : ℕ := KL.max' (by rw [hKL]; simp) with hK_def
  have hmem : ∀ y : ℝ, y ∈ CL → y ≤ A := by
    intro y hy; rw [hA_def]; exact Finset.le_max' CL y hy
  have hmemK : ∀ n : ℕ, n ∈ KL → n ≤ KK := by
    intro n hn; rw [hK_def]; exact Finset.le_max' KL n hn
  have hA1 : 1 ≤ A := hmem 1 (by rw [hCL]; simp)
  have hA_A0 : A₀ ≤ A :=
    le_trans (by linarith [hA₀] : A₀ ≤ A₀ + A₀) (hmem (A₀ + A₀) (by rw [hCL]; simp))
  have hA_2Cs : (2 * Cs) ^ P.natDegree ≤ A :=
    hmem ((2 * Cs) ^ P.natDegree) (by rw [hCL]; simp)
  have hA_2s : (2 : ℝ) ^ (max S (Fintype.card (D.I (P.natDegree - 1)) + 1)) ≤ A :=
    hmem ((2 : ℝ) ^ (max S (Fintype.card (D.I (P.natDegree - 1)) + 1))) (by rw [hCL]; simp)
  have hA_C2 : C₂ * C ^ E₂ ≤ A := hmem (C₂ * C ^ E₂) (by rw [hCL]; simp)
  have hA_C2inv : (C₂ * C ^ E₂)⁻¹ ≤ A := hmem ((C₂ * C ^ E₂)⁻¹) (by rw [hCL]; simp)
  have hA_c0inv : (1 : ℝ) / c₀ ≤ A := by
    have h2s1 : (1 : ℝ) ≤ (2 : ℝ) ^ P.natDegree := one_le_pow₀ (by norm_num)
    exact le_trans (div_le_div_of_nonneg_right h2s1 hc₀.le)
      (hmem ((2 : ℝ) ^ P.natDegree / c₀) (by rw [hCL]; simp))
  have hKK_2s : 2 ^ (max S (Fintype.card (D.I (P.natDegree - 1)) + 1)) ≤ KK :=
    hmemK (2 ^ (max S (Fintype.card (D.I (P.natDegree - 1)) + 1))) (by rw [hKL]; simp)
  have hKK_d : P.natDegree * (M₀ + 1) ≤ KK :=
    le_trans (by omega) (hmemK (P.natDegree * (M₀ + 1) + 1) (by rw [hKL]; simp))
  have hKK_e0 : e₀ ≤ KK := le_trans (by omega) (hmemK (e₀ + 1) (by rw [hKL]; simp))
  have hKK_ceil : Nat.ceil (E₂ * E) + 1 ≤ KK :=
    hmemK (Nat.ceil (E₂ * E) + 1) (by rw [hKL]; simp)
  refine ⟨A, hA1, KK, by omega, ?_⟩
  intro N M f η δ' h2d hN hM hNM1 hNM2 hη0 hη1 hδ' hAδ hH2 hf hsu hAη hfam
  set H : ℕ := (⌊δ' * (M : ℝ)⌋).toNat with hH_def
  set x : ℝ := η ^ KK * δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree / A with hx_def
  set LL : ℕ := (⌊max (1 : ℝ) x⌋).toNat with hLL_def
  -- elementary consequences of the hypotheses
  have hApos : 0 < A := lt_of_lt_of_le one_pos hA1
  have hδ1 : δ' ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have h2' : A * δ' ≤ 1 := le_trans hAδ (pow_le_one₀ hη0.le hη1)
    nlinarith [hApos, hA1, hcon, h2']
  have hηK1 : η ^ KK ≤ 1 := pow_le_one₀ hη0.le hη1
  have hMd : (0 : ℝ) ≤ (M : ℝ) ^ P.natDegree := by positivity
  have hδd1 : δ' ^ P.natDegree ≤ 1 := pow_le_one₀ hδ'.le hδ1
  by_cases hxle : x ≤ 1
  · -- ## the small window
    have hLL1 : LL = 1 := by
      rw [hLL_def, max_eq_left hxle]
      norm_num
    rw [hLL1]
    exact smallWindowConcl D P.natDegree P.leadingCoeff N H f η
      (P.natDegree.factorial * P.leadingCoeff)
      (max S (Fintype.card (D.I (P.natDegree - 1)) + 1)) KK A
      (by omega) hN hf hsu hη0 hη1 (by rw [hH_def]; exact hfam)
      (by omega) (by omega) hKK_2s hA1
  · -- ## the large window
    have hx' : 1 < x := not_le.mp hxle
    have hAlt : A < η ^ KK * δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree :=
      (one_lt_div hApos).mp hx'
    -- ## the floor bookkeeping for `H`
    have hfl : ((H : ℤ)) = ⌊δ' * (M : ℝ)⌋ := by
      rw [hH_def]
      exact Int.toNat_of_nonneg (Int.floor_nonneg.mpr (by positivity))
    have hHle : (H : ℝ) ≤ δ' * (M : ℝ) := by
      have h := Int.floor_le (δ' * (M : ℝ))
      rw [← hfl] at h
      simpa using h
    have hHlt : δ' * (M : ℝ) < (H : ℝ) + 1 := by
      have h := Int.lt_floor_add_one (δ' * (M : ℝ))
      rw [← hfl] at h
      simpa using h
    have hH1 : 1 ≤ H := by omega
    have hH1le : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH1
    have hδM1 : 1 ≤ δ' * (M : ℝ) := le_trans (by exact_mod_cast hH1) hHle
    -- ## the strict power bound
    have hpow_lt : δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree < ((H : ℝ) + 1) ^ P.natDegree := by
      rw [← mul_pow]
      exact pow_lt_pow_left₀ hHlt (by positivity) (by omega)
    have hAlt2 : A < η ^ KK * ((H : ℝ) + 1) ^ P.natDegree := by
      have h1 : η ^ KK * (δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree)
          < η ^ KK * ((H : ℝ) + 1) ^ P.natDegree :=
        mul_lt_mul_of_pos_left hpow_lt (pow_pos hη0 _)
      have h2 : η ^ KK * δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree
          = η ^ KK * (δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree) := by ring
      linarith [hAlt, h1, h2.le, h2.ge]
    -- ## the régime `Cs ≤ η^{M₀}H`
    have hη_pow_le : η ^ KK * ((H : ℝ) + 1) ^ P.natDegree
        ≤ (η ^ (M₀ + 1) * ((H : ℝ) + 1)) ^ P.natDegree := by
      rw [mul_pow]
      have h1 : η ^ KK ≤ η ^ (P.natDegree * (M₀ + 1)) :=
        pow_le_pow_of_le_one hη0.le hη1 hKK_d
      have h2 : η ^ (P.natDegree * (M₀ + 1)) = (η ^ (M₀ + 1)) ^ P.natDegree := by
        rw [← pow_mul]; ring_nf
      rw [h2] at h1
      exact mul_le_mul_of_nonneg_right h1 (by positivity)
    have h2Cs_lt : 2 * Cs < η ^ (M₀ + 1) * ((H : ℝ) + 1) := by
      have hle : (2 * Cs) ^ P.natDegree < η ^ KK * ((H : ℝ) + 1) ^ P.natDegree :=
        lt_of_le_of_lt hA_2Cs hAlt2
      have hlt : (2 * Cs) ^ P.natDegree < (η ^ (M₀ + 1) * ((H : ℝ) + 1)) ^ P.natDegree :=
        lt_of_lt_of_le hle hη_pow_le
      rwa [pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by omega)] at hlt
    have hreg : Cs ≤ η ^ M₀ * (H : ℝ) := by
      have h2 : (H : ℝ) + 1 ≤ 2 * (H : ℝ) := by linarith
      have h3 : (0 : ℝ) < η ^ (M₀ + 1) := pow_pos hη0 _
      have h1 : η ^ (M₀ + 1) * ((H : ℝ) + 1) ≤ 2 * (η ^ (M₀ + 1) * (H : ℝ)) := by
        nlinarith [h3, h2]
      have h4 : η ^ (M₀ + 1) * (H : ℝ) ≤ η ^ M₀ * (H : ℝ) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hη0.le hη1 (Nat.le_succ M₀))
          (Nat.cast_nonneg H)
      linarith
    -- ## the scale hypothesis
    have hscale : ((H : ℝ) + 1) ^ P.natDegree
        ≤ max 1 ((2 : ℝ) ^ P.natDegree * A₀) * (N : ℝ) := by
      have h1 : (H : ℝ) + 1 ≤ 2 * (δ' * (M : ℝ)) := by linarith
      have h2 : ((H : ℝ) + 1) ^ P.natDegree ≤ (2 * (δ' * (M : ℝ))) ^ P.natDegree :=
        pow_le_pow_left₀ (by positivity) h1 _
      have h3 : (2 * (δ' * (M : ℝ))) ^ P.natDegree
          = 2 ^ P.natDegree * (δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree) := by ring
      have h6 : δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree ≤ (M : ℝ) ^ P.natDegree :=
        by nlinarith [hδd1, hMd]
      have h8 : (2 : ℝ) ^ P.natDegree * (M : ℝ) ^ P.natDegree
          ≤ max 1 ((2 : ℝ) ^ P.natDegree * A₀) * (N : ℝ) := by
        have h9 : (2 : ℝ) ^ P.natDegree * A₀ ≤ max 1 ((2 : ℝ) ^ P.natDegree * A₀) :=
          le_max_right _ _
        have h10 : (0 : ℝ) ≤ (2 : ℝ) ^ P.natDegree := by positivity
        have h11 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        nlinarith [hNM2, h9, h10, h11]
      have h12 : (2 : ℝ) ^ P.natDegree * (δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree)
          ≤ (2 : ℝ) ^ P.natDegree * (M : ℝ) ^ P.natDegree := by
        have h10 : (0 : ℝ) ≤ (2 : ℝ) ^ P.natDegree := by positivity
        nlinarith [h6, h10]
      calc ((H : ℝ) + 1) ^ P.natDegree
          ≤ (2 * (δ' * (M : ℝ))) ^ P.natDegree := h2
        _ = 2 ^ P.natDegree * (δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree) := h3
        _ ≤ 2 ^ P.natDegree * (M : ℝ) ^ P.natDegree := h12
        _ ≤ max 1 ((2 : ℝ) ^ P.natDegree * A₀) * (N : ℝ) := h8
    -- ## the chain
    obtain ⟨Lw₀, N', hNN', hLw, hnorm⟩ :=
      hchain N H f η hN (by omega) hf hsu hη0 hη1 hreg hscale (by rw [hH_def]; exact hfam)
    -- ## the floor bookkeeping for `LL`
    have hflL : max (1 : ℝ) x = x := by
      apply max_eq_right
      exact le_of_lt hx'
    have hflL1 : (1 : ℤ) ≤ ⌊x⌋ := by
      rw [Int.le_floor]
      push_cast
      exact le_of_lt hx'
    have htoNat : ((⌊x⌋).toNat : ℝ) = (⌊x⌋ : ℝ) := by
      have h0 : (0 : ℤ) ≤ ⌊x⌋ := by omega
      exact_mod_cast Int.toNat_of_nonneg h0
    have hLLval : LL = (⌊x⌋).toNat := by rw [hLL_def, hflL]
    have hLx : (LL : ℝ) ≤ x := by
      rw [hLLval, htoNat]
      exact Int.floor_le x
    have hL1 : 1 ≤ LL := by
      rw [hLLval]
      simpa using Int.toNat_le_toNat hflL1
    -- ## `LL ≤ Lw₀`
    have hLw₀_le : LL ≤ Lw₀ := by
      have h0 : (LL : ℝ) ≤ (Lw₀ : ℝ) := by
        have h1 : x ≤ η ^ KK * ((H : ℝ) + 1) ^ P.natDegree / A := by
          rw [hx_def]
          have h2 : δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree ≤ ((H : ℝ) + 1) ^ P.natDegree :=
            hpow_lt.le
          have h4 : (0 : ℝ) ≤ η ^ KK := by positivity
          have h5 : η ^ KK * δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree
              = η ^ KK * (δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree) := by ring
          rw [h5]
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h2 h4) hApos.le
        have h5 : η ^ KK ≤ η ^ e₀ := pow_le_pow_of_le_one hη0.le hη1 (by omega)
        have h6 : (1 : ℝ) ≤ A * c₀ := by
          have h7 := mul_le_mul_of_nonneg_right hA_c0inv hc₀.le
          rw [one_div, inv_mul_cancel₀ (ne_of_gt hc₀)] at h7
          exact h7
        have h8 : η ^ e₀ ≤ A * c₀ * η ^ e₀ := by
          have h9 : (0 : ℝ) < η ^ e₀ := pow_pos hη0 _
          nlinarith [h6, h9]
        have h9 : (0 : ℝ) < ((H : ℝ) + 1) ^ P.natDegree := by positivity
        have h10 : η ^ KK * ((H : ℝ) + 1) ^ P.natDegree / A
            ≤ c₀ * η ^ e₀ * ((H : ℝ) + 1) ^ P.natDegree := by
          rw [div_le_iff₀ hApos]
          nlinarith [h5, h8, h9]
        linarith [hLx, h1, h10, hLw]
      exact_mod_cast h0
    -- ## `LL ≤ N`
    have hLN : LL ≤ N := by
      have hnum : η ^ KK * δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree
          ≤ (M : ℝ) ^ P.natDegree := by
        have h1 : η ^ KK * δ' ^ P.natDegree ≤ 1 :=
          mul_le_one₀ hηK1 (by positivity) hδd1
        nlinarith [h1, hMd]
      have hxM : x ≤ (M : ℝ) ^ P.natDegree / A := by
        rw [hx_def]
        have h2 : η ^ KK * δ' ^ P.natDegree * (M : ℝ) ^ P.natDegree
            = (η ^ KK * δ' ^ P.natDegree) * (M : ℝ) ^ P.natDegree := by ring
        rw [h2]
        exact div_le_div_of_nonneg_right hnum hApos.le
      have h2 : (LL : ℝ) ≤ (N : ℝ) := by
        have h3 : (M : ℝ) ^ P.natDegree / A ≤ (A₀ * (N : ℝ)) / A :=
          div_le_div_of_nonneg_right hNM2 hApos.le
        have h4 : (A₀ * (N : ℝ)) / A ≤ (N : ℝ) := by
          rw [div_le_iff₀ hApos]
          nlinarith [hA_A0, Nat.cast_nonneg (α := ℝ) N]
        linarith [hLx, hxM, h3, h4]
      exact_mod_cast h2
    -- ## the transfer
    have hκ : ((P.natDegree.factorial : ℤ) * P.leadingCoeff) ≠ 0 := by
      refine mul_ne_zero ?_ hc
      have hpos : (0 : ℤ) < (P.natDegree.factorial : ℤ) := by
        exact_mod_cast Nat.factorial_pos P.natDegree
      exact ne_of_gt hpos
    have htr := htrans ((P.natDegree.factorial : ℤ) * P.leadingCoeff) hκ LL Lw₀ N N' f
      hLN hL1 hLw₀_le hNN' hsu hf
    -- ## the constant arithmetic
    have hCη : 0 < C * η ^ E := mul_pos hC (pow_pos hη0 E)
    have hstep1 : (C * η ^ E) ^ E₂
        ≤ (uNormPow S (arithIcc ((P.natDegree.factorial : ℤ) * P.leadingCoeff) Lw₀)
            (symIcc N') f) ^ E₂ :=
      Real.rpow_le_rpow hCη.le hnorm hE₂.le
    have hfinal : C₂ * (C * η ^ E) ^ E₂
        ≤ uNormPow (max S (Fintype.card (D.I (P.natDegree - 1)) + 1))
            (arithIcc ((P.natDegree.factorial : ℤ) * P.leadingCoeff) LL) (symIcc N) f :=
      le_trans (mul_le_mul_of_nonneg_left hstep1 hC₂.le) htr
    have hKKge : (E : ℝ) * E₂ ≤ (KK : ℝ) := by
      have h1 : E₂ * (E : ℝ) ≤ (Nat.ceil (E₂ * (E : ℝ)) : ℝ) := Nat.le_ceil _
      have h2 : (Nat.ceil (E₂ * (E : ℝ)) : ℝ) ≤ (KK : ℝ) := by
        have := hKK_ceil
        exact_mod_cast (by omega : Nat.ceil (E₂ * (E : ℝ)) ≤ KK)
      linarith
    have hηKK : η ^ KK ≤ η ^ ((E : ℝ) * E₂) := by
      rw [← Real.rpow_natCast η KK]
      exact Real.rpow_le_rpow_of_exponent_ge hη0 hη1 hKKge
    have hrpow : (C * η ^ E) ^ E₂ = C ^ E₂ * η ^ ((E : ℝ) * E₂) := by
      rw [← Real.rpow_natCast η E, Real.mul_rpow hC.le (Real.rpow_nonneg hη0.le _),
        ← Real.rpow_mul hη0.le]
    have hAC2 : 1 ≤ A * C₂ * C ^ E₂ := by
      by_cases h1 : (1 : ℝ) ≤ C₂ * C ^ E₂
      · nlinarith [h1, hA_C2]
      · push_neg at h1
        have h3 : (0 : ℝ) < C₂ * C ^ E₂ := mul_pos hC₂ (Real.rpow_pos_of_pos hC E₂)
        have h4 := mul_le_mul_of_nonneg_right hA_C2inv h3.le
        rw [inv_mul_cancel₀ (ne_of_gt h3)] at h4
        linarith
    have hcomb : η ^ KK ≤ A * C₂ * (C * η ^ E) ^ E₂ := by
      rw [hrpow]
      have h1 : (1 : ℝ) ≤ A * C₂ * C ^ E₂ := hAC2
      have h2 : (0 : ℝ) ≤ η ^ ((E : ℝ) * E₂) := Real.rpow_nonneg hη0.le _
      calc η ^ KK ≤ η ^ ((E : ℝ) * E₂) := hηKK
        _ ≤ (A * C₂ * C ^ E₂) * η ^ ((E : ℝ) * E₂) := le_mul_of_one_le_left h2 h1
        _ = A * C₂ * (C ^ E₂ * η ^ ((E : ℝ) * E₂)) := by ring
    calc η ^ KK ≤ A * C₂ * (C * η ^ E) ^ E₂ := hcomb
      _ = A * (C₂ * (C * η ^ E) ^ E₂) := by ring
      _ ≤ A * uNormPow (max S (Fintype.card (D.I (P.natDegree - 1)) + 1))
            (arithIcc ((P.natDegree.factorial : ℤ) * P.leadingCoeff) LL) (symIcc N) f :=
          mul_le_mul_of_nonneg_left hfinal hApos.le

end

end Work.Peluse
