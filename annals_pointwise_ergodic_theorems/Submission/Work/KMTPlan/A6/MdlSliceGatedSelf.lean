import Mathlib
import Submission.Work.KMTPlan.A6.MdlSliceHelpers
import Submission.Work.KMTPlan.A6.MdlSliceBadPart
import Submission.Work.KMTPlan.A6.lossAbsorbTwo
import Submission.Work.KMTPlan.A6.vrSamplingDensity_one_unif
import Submission.Work.KMTPlan.A6Clean.MdlSliceNoGainAt
import Submission.Work.KMTPlan.A6Clean.adelicFormGated

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- The definitions `mdlSliceF` / `mdlSliceG` / `MdlSliceCoreGainMemLp` used below live in the
-- cycle-free definitions module `Submission.Work.A6Big.Defs` (the `KMTPlan/A6/MdlSliceCoreGainBig`
-- file, which used to declare them, is now the *target* of this file's consumer).  Importing
-- `MdlSliceCoreGainBig` here would be an import cycle (`MdlSliceCoreGainBig` proves the frozen-slice
-- estimate from `MdlSliceCoreGainMemLp_of_pieces_split`, declared below).
/-! A cycle-free copy of the A6Clean §8 consumers: the proofs of
`A6Clean/MdlSliceCoreGainMemLp_of_pieces_{rangeP,fromPos,split}.lean`, with their imports of
`Submission.Work.KMTPlan.A6.MdlSliceCoreGainAll` (present only for that file's helper lemmas)
replaced by `Submission.Work.KMTPlan.A6.MdlSliceHelpers`, which carries those lemmas.  The
statements are unchanged, so no import cycle arises with `MdlSliceCoreGainAll.lean`. -/

namespace Work.KMTPlan.A6Clean

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators Polynomial
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTAreas.A7
open Work.KMTPlan.A6


/-! ## The fixed-parameter adelic form -/

/-- **The §8 adelic form at *fixed* parameters.**  This is the body of
`Work.KMTPlan.A6Clean.AdelicFormPropRangeP` at `(r, R, C₀, j₁, j₂)`: the constants
`c, A, ρ₀, Cin` may depend on those parameters, but not on the datum
`(a, Λ, l₁, l₂, k₁, k₂, t, f, g)`. -/
def AdelicFormAtRangeP (P : ℤ[X]) (r : ℝ≥0) (R : ℝ) (C₀ : ℕ) (j₁ j₂ : ℤ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ Cin : ℝ≥0 → ℝ≥0,
      ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₁ = 0 → j₁ ≠ -1) → (k₂ = 0 → j₂ ≠ -1) →
        MemLp f 2 Measure.count → MemLp g 2 Measure.count →
        AdelicClausesAt P ρ R r a Λ l₁ l₂ k₁ k₂ t j₁ j₂ f g C₀ c A Cin

/-- **The assembly of `MdlSliceCoreGainMemLp` from the fixed-parameter adelic form, the bad part and
the loss absorption** (at the cutoff `C₀ ≥ 1`).

This is the proof of `Work.KMTPlan.A6.MdlSliceCoreGainMemLp_of_pieces_range` verbatim, with the use
of the adelic form adapted: the latter now supplies its constants `c, A, ρ₀, Cin` at the
*fixed* parameters `(r, 2, C₀, j₁, j₂)` (so `Cin` is available at `ρ` but not at a
varying `C₀'`), and the case `C₀ = 0` is delegated to `MdlSliceCoreGainMemLp_c₀_zero`. -/
theorem MdlSliceCoreGainMemLp_of_adelicFormAt (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P)
    {r : NNReal} {C₀ : ℕ} {j₁ j₂ : ℤ}
    (hAdel : AdelicFormAtRangeP P r 2 C₀ j₁ j₂) (hChain : ZModChainPropP)
    (hBad : BadPartProp P hd hA1 hI) (hAbs : LossAbsorbProp)
    (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
    (hr : 2 < r) (hC₀ : 1 ≤ C₀) :
    MdlSliceCoreGainMemLp P r C₀ j₁ j₂ := by
  classical
  obtain ⟨cA, hcA, AA, hAA, ρA, hρA, hAdel'⟩ := hAdel
  obtain ⟨cB, hcB, AB, hAB, ρB, hρB, hBad'⟩ := hBad
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  have hRr : (2 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  obtain ⟨Cs, hCs, hUnif'⟩ := vrSamplingDensity_one_unif r hr1
  obtain ⟨Cd, hCd, hChain'⟩ :=
    hChain (r := r) hr1 (R := 2) (by norm_num) hRr
  set cc : ℝ := min cA cB / 2 with hcc
  set AA' : ℝ := 2 * AA + AB + 1 with hAA'
  set ρρ : ℝ := min ρA ρB with hρρ
  have hccpos : 0 < cc := by rw [hcc]; exact half_pos (lt_min hcA hcB)
  have hAA'nn : 0 ≤ AA' := by rw [hAA']; positivity
  have hρρpos : 0 < ρρ := by rw [hρρ]; exact lt_min hρA hρB
  refine ⟨cc, hccpos, AA', hAA'nn, ρρ, hρρpos, ?_⟩
  intro ρ hρ hρle
  have hρρA : ρρ ≤ ρA := by rw [hρρ]; exact min_le_left _ _
  have hρρB : ρρ ≤ ρB := by rw [hρρ]; exact min_le_right _ _
  have hρA' : ρ ≤ ρA := le_trans hρle hρρA
  have hρB' : ρ ≤ ρB := le_trans hρle hρρB
  obtain ⟨Cin, hCin⟩ := hAdel' ρ hρ hρA'
  obtain ⟨KB, hKB⟩ := hBad' ρ hρ hρB'
  set Kf : ℝ≥0 → ℝ≥0 := fun Λ =>
    ⟨Cs * Cd * ((Cin Λ : ℝ)) ^ 3 + (KB Λ : ℝ) + 1, by
      have hX : (0 : ℝ) ≤ Cs * Cd * ((Cin Λ : ℝ)) ^ 3 := by
        have := (Cin Λ).coe_nonneg; positivity
      have hKBn : (0 : ℝ) ≤ (KB Λ : ℝ) := (KB Λ).coe_nonneg
      linarith⟩ with hKf
  refine ⟨Kf, ?_⟩
  -- ### the datum level
  intro a Λ l₁ l₂ k₁ k₂ t f g hΛ ha ha1 ht hk₁ hk₂ hf hg
  have step :
      eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
        1 Measure.count
        ≤ (Kf Λ : ENNReal)
          * ENNReal.ofReal (lossWeight AA' ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ)))))
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
    set Q : ℕ := arithQ ρ (max l₁ l₂) with hQdef
    set Lv : ℕ := lcL l₁ l₂ k₁ k₂ with hLvdef
    have hQ1 : 1 ≤ Q := by rw [hQdef]; exact one_le_arithQ ρ (max l₁ l₂)
    obtain ⟨F, u, v, M, Ku, Kv, hrest⟩ :=
      hCin a Λ l₁ l₂ k₁ k₂ t f g
        hΛ ha ha1 ht hk₁ hk₂ hf hg
    obtain ⟨hband, hdiag, hbilin, hrest⟩ := hrest
    obtain ⟨⟨hM0, hMbd⟩, hrest⟩ := hrest
    obtain ⟨⟨hKu0, hKubd⟩, hrest⟩ := hrest
    obtain ⟨⟨hKv0, hKvbd⟩, hrest⟩ := hrest
    obtain ⟨hSu, hSv, hrest⟩ := hrest
    obtain ⟨humeas, hvmeas, hrest⟩ := hrest
    obtain ⟨hbase, hB1, hB2⟩ := hrest
    -- the good/bad split of the family
    set J : ℕ → ℤ → ℂ := fun n x => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x with hJ
    set famG : ℕ → ℤ → ℂ := fun n x =>
      if goodScale Q Lv (Nat.floor (a n)) then J n x else 0 with hfamG
    set famB : ℕ → ℤ → ℂ := fun n x =>
      if ¬ goodScale Q Lv (Nat.floor (a n)) then J n x else 0 with hfamB
    have hsplitJ : ∀ n x, J n x = famG n x + famB n x := by
      intro n x
      have h1 : famG n x = if goodScale Q Lv (Nat.floor (a n)) then J n x else 0 := rfl
      have h2 : famB n x = if ¬ goodScale Q Lv (Nat.floor (a n)) then J n x else 0 := rfl
      rw [h1, h2]
      by_cases h : goodScale Q Lv (Nat.floor (a n)) <;> simp [h]
    -- the pointwise subadditivity, passed to the `tsum`s
    have hsplit : (∑' x : ℤ, variationalNorm r (fun n : ℕ => J n x))
        ≤ (∑' x : ℤ, variationalNorm r (fun n : ℕ => famG n x))
          + (∑' x : ℤ, variationalNorm r (fun n : ℕ => famB n x)) := by
      rw [← ENNReal.tsum_add]
      refine ENNReal.tsum_le_tsum fun x => ?_
      have h1 : (fun n : ℕ => J n x) = (fun n : ℕ => famG n x) + (fun n : ℕ => famB n x) := by
        funext n; exact hsplitJ n x
      rw [h1]
      exact variationalNorm_add_le hr1 _ _
    -- the bad part
    have hbadB : (∑' x : ℤ, variationalNorm r (fun n : ℕ => famB n x))
        ≤ (KB Λ : ENNReal)
          * ENNReal.ofReal (lossWeight AB ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(cB * (max (l₁ : ℝ) (l₂ : ℝ)))))
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
      rw [← eLpNorm_one_count_variationalNorm r famB]
      exact hKB r hr C₀ hC₀ a Λ l₁ l₂ k₁ k₂ t j₁ j₂ hj₁ hj₂ f g
        hΛ ha ha1 ht hk₁ hk₂ hf hg
    -- the sampling transfer
    have hβpos : (0 : ℝ) < 1 / (8 * (Q : ℝ)) := by positivity
    have hβlt : 1 / (8 * (Q : ℝ)) < 1 / 2 := by
      have hQ1R : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
      have h8 : (0 : ℝ) < 8 * (Q : ℝ) := by linarith
      rw [div_lt_iff₀ h8]
      nlinarith
    have hβQ : (1 / (8 * (Q : ℝ))) * (Q : ℝ) ≤ 1 / 4 := by
      have hQ1R : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
      have h8 : (0 : ℝ) < 8 * (Q : ℝ) := by linarith
      rw [one_div_mul_eq_div, div_le_iff₀ h8]
      nlinarith
    have hmeasF : ∀ ρ' : ℤ,
        Measurable (fun x : ℝ => variationalNorm r (fun n : ℕ => F n x ρ')) :=
      fun ρ' => measurable_variationalNorm_of_hasRealFreqSupport
        (lt_of_lt_of_le zero_lt_one hr1) (fun n x => F n x ρ') (fun n => hband n ρ')
    have hsliceF : ∀ ρ' : ℤ,
        (∑' N : ℤ, variationalNorm r
            (fun n : ℕ => F n ((ρ' : ℝ) + (Q : ℝ) * (N : ℝ)) ρ'))
          ≤ ENNReal.ofReal Cs * (Q : ENNReal)⁻¹
              * ∫⁻ x : ℝ, variationalNorm r (fun n : ℕ => F n x ρ') :=
      fun ρ' => hUnif' (1 / (8 * (Q : ℝ))) hβpos hβlt (fun n x => F n x ρ')
        (fun n => hband n ρ') Q (lt_of_lt_of_le Nat.zero_lt_one hQ1) hβQ ρ'
    have hcGF : ∀ n x, famG n x = F n (x : ℝ) (x % ((Q : ℕ) : ℤ)) := by
      intro n x
      have h1 : famG n x = (if goodScale Q Lv (Nat.floor (a n)) then
          mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x else 0) := rfl
      rw [h1]
      exact (hdiag n x).symm
    have htr : (∑' x : ℤ, variationalNorm r (fun n : ℕ => famG n x))
        ≤ ENNReal.ofReal Cs
            * ∫⁻ x : ℝ, (Q : ENNReal)⁻¹ * ∑ ρ' ∈ Finset.range Q,
                variationalNorm r (fun n : ℕ => F n x (ρ' : ℤ)) :=
      diagonalVrSampling_le (r := r) (Q := Q) hQ1 hCs (F := F) hmeasF hsliceF (c := famG) hcGF
    -- the `ZMod Q` chain
    have hchain := hChain' (Q := Q) hQ1 (M := M) (Ku := Ku) (Kv := Kv) hM0 hKu0 hKv0
      (B := fun e f' θ => zmodAvg (negReflect P) Q e f' θ)
      (fun e e' f' => zmodAvg_add₁ (negReflect P) Q e e' f')
      (fun e f' f'' => zmodAvg_add₂ (negReflect P) Q e f' f'')
      humeas hvmeas hbase hB1 hB2 hSu hSv
    -- rewrite the integral of the sampling transfer into the chain's integral
    have hIntEq : (∫⁻ x : ℝ, (Q : ENNReal)⁻¹ * ∑ ρ' ∈ Finset.range Q,
          variationalNorm r (fun n : ℕ => F n x (ρ' : ℤ)))
        = ∫⁻ X : ℝ, (Q : ENNReal)⁻¹ * ∑ ρ' ∈ Finset.range Q,
            variationalNorm r (fun n : ℕ =>
              zmodAvg (negReflect P) Q (u n X) (v n X) ((ρ' : ℤ) : ZMod Q)) := by
      refine MeasureTheory.lintegral_congr fun x => ?_
      congr 1
      refine Finset.sum_congr rfl fun ρ' _ => ?_
      congr 1
      funext n
      exact hbilin n x (ρ' : ℤ)
    have hgood1 : (∑' x : ℤ, variationalNorm r (fun n : ℕ => famG n x))
        ≤ ENNReal.ofReal Cs
            * (ENNReal.ofReal Cd * ENNReal.ofReal M * ENNReal.ofReal Ku
                * ENNReal.ofReal Kv) := by
      refine htr.trans ?_
      rw [hIntEq]
      exact mul_le_mul' le_rfl hchain
    -- the constant bookkeeping of the good part
    set Y₀ : ENNReal := ENNReal.ofReal ((2 : ℝ) ^ (-(cA * (max (l₁ : ℝ) (l₂ : ℝ))))) with hY₀
    set W : ENNReal := ENNReal.ofReal (lossWeight AA ρ l₁ l₂ k₁ k₂) with hW
    set Fn : ENNReal := eLpNorm f 2 Measure.count with hFn
    set Gn : ENNReal := eLpNorm g 2 Measure.count with hGn
    set Cl : ENNReal := (Cin Λ : ENNReal) with hCl
    set Kgood : ENNReal := ENNReal.ofReal Cs * ENNReal.ofReal Cd * Cl ^ 3 with hKgood
    set Y : ENNReal := ENNReal.ofReal (lossWeight AA' ρ l₁ l₂ k₁ k₂
        * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ))))) with hY
    have hY0nn : (0 : ℝ) ≤ (2 : ℝ) ^ (-(cA * (max (l₁ : ℝ) (l₂ : ℝ)))) := by positivity
    have hLWnn : (0 : ℝ) ≤ lossWeight AA ρ l₁ l₂ k₁ k₂ :=
      le_of_lt (lossWeight_pos_vr AA ρ hAA hρ.le l₁ l₂ k₁ k₂)
    have hexp : -(min cA cB / 2) * max (l₁ : ℝ) (l₂ : ℝ)
        = -(cc * max (l₁ : ℝ) (l₂ : ℝ)) := by
      rw [hcc]; ring
    -- the three bounds combine
    have h3 : ENNReal.ofReal M * ENNReal.ofReal Ku * ENNReal.ofReal Kv
        ≤ (Cl * Y₀) * (Cl * W * Fn) * (Cl * W * Gn) := by
      have h := mul_le_mul' (mul_le_mul' hMbd hKubd) hKvbd
      simpa only [hCl, hY₀, hW, hFn, hGn] using h
    have h4 : (Cl * Y₀) * (Cl * W * Fn) * (Cl * W * Gn)
        = Cl ^ 3 * (Y₀ * W * W) * Fn * Gn := by ring
    have h5 : Y₀ * W * W ≤ Y := by
      have h' : (2 : ℝ) ^ (-(cA * max (l₁ : ℝ) (l₂ : ℝ)))
            * (lossWeight AA ρ l₁ l₂ k₁ k₂) ^ 2
          ≤ (2 : ℝ) ^ (-(min cA cB / 2) * max (l₁ : ℝ) (l₂ : ℝ))
              * lossWeight (2 * AA + AB + 1) ρ l₁ l₂ k₁ k₂ :=
        (hAbs AA AB cA cB hAA hAB hcA hcB ρ hρ l₁ l₂ k₁ k₂).1
      have h'' : (2 : ℝ) ^ (-(min cA cB / 2) * max (l₁ : ℝ) (l₂ : ℝ))
              * lossWeight AA' ρ l₁ l₂ k₁ k₂
          = lossWeight AA' ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ)))) := by
        rw [hexp]; ring
      rw [hY₀, hW, hY]
      rw [← ENNReal.ofReal_mul hY0nn, ← ENNReal.ofReal_mul (mul_nonneg hY0nn hLWnn)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc (2 : ℝ) ^ (-(cA * max (l₁ : ℝ) (l₂ : ℝ)))
            * lossWeight AA ρ l₁ l₂ k₁ k₂ * lossWeight AA ρ l₁ l₂ k₁ k₂
          = (2 : ℝ) ^ (-(cA * max (l₁ : ℝ) (l₂ : ℝ)))
              * (lossWeight AA ρ l₁ l₂ k₁ k₂) ^ 2 := by ring
        _ ≤ (2 : ℝ) ^ (-(min cA cB / 2) * max (l₁ : ℝ) (l₂ : ℝ))
              * lossWeight AA' ρ l₁ l₂ k₁ k₂ := h'
        _ = lossWeight AA' ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ)))) := h''
    have h6 : Cl ^ 3 * (Y₀ * W * W) * Fn * Gn ≤ Cl ^ 3 * Y * Fn * Gn :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl h5) le_rfl) le_rfl
    have hgood : (∑' x : ℤ, variationalNorm r (fun n : ℕ => famG n x))
        ≤ Kgood * Y * Fn * Gn := by
      refine hgood1.trans ?_
      calc ENNReal.ofReal Cs
            * (ENNReal.ofReal Cd * ENNReal.ofReal M * ENNReal.ofReal Ku * ENNReal.ofReal Kv)
          = ENNReal.ofReal Cs * ENNReal.ofReal Cd
              * (ENNReal.ofReal M * ENNReal.ofReal Ku * ENNReal.ofReal Kv) := by ring
        _ ≤ ENNReal.ofReal Cs * ENNReal.ofReal Cd * (Cl ^ 3 * Y * Fn * Gn) := by
            refine mul_le_mul' le_rfl ?_
            exact (h3.trans (le_of_eq h4)).trans h6
        _ = Kgood * Y * Fn * Gn := by rw [hKgood]; ring
    -- the bad part in the same shape
    have hbadY : ENNReal.ofReal (lossWeight AB ρ l₁ l₂ k₁ k₂
          * (2 : ℝ) ^ (-(cB * (max (l₁ : ℝ) (l₂ : ℝ))))) ≤ Y := by
      have h : lossWeight AB ρ l₁ l₂ k₁ k₂ * (2 : ℝ) ^ (-(cB * max (l₁ : ℝ) (l₂ : ℝ)))
          ≤ (2 : ℝ) ^ (-(min cA cB / 2) * max (l₁ : ℝ) (l₂ : ℝ))
              * lossWeight (2 * AA + AB + 1) ρ l₁ l₂ k₁ k₂ :=
        (hAbs AA AB cA cB hAA hAB hcA hcB ρ hρ l₁ l₂ k₁ k₂).2
      rw [hY]
      refine ENNReal.ofReal_le_ofReal ?_
      calc lossWeight AB ρ l₁ l₂ k₁ k₂
            * (2 : ℝ) ^ (-(cB * (max (l₁ : ℝ) (l₂ : ℝ))))
          = lossWeight AB ρ l₁ l₂ k₁ k₂ * (2 : ℝ) ^ (-(cB * max (l₁ : ℝ) (l₂ : ℝ))) := by ring
        _ ≤ (2 : ℝ) ^ (-(min cA cB / 2) * max (l₁ : ℝ) (l₂ : ℝ))
              * lossWeight AA' ρ l₁ l₂ k₁ k₂ := h
        _ = lossWeight AA' ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ)))) := by
            rw [hexp]; ring
    have hbad : (∑' x : ℤ, variationalNorm r (fun n : ℕ => famB n x))
        ≤ (KB Λ : ENNReal) * Y * Fn * Gn := by
      refine hbadB.trans ?_
      calc (KB Λ : ENNReal) * ENNReal.ofReal (lossWeight AB ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(cB * (max (l₁ : ℝ) (l₂ : ℝ)))))
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count
          ≤ (KB Λ : ENNReal) * Y * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
            refine mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hbadY) le_rfl) le_rfl
        _ = (KB Λ : ENNReal) * Y * Fn * Gn := by rw [hFn, hGn]
    -- the two halves combine
    have hKBsum : Kgood + (KB Λ : ENNReal) ≤ (Kf Λ : ENNReal) := by
      have hXnn : (0 : ℝ) ≤ Cs * Cd * ((Cin Λ : ℝ)) ^ 3 := by
        have := (Cin Λ).coe_nonneg; positivity
      have hKBnn : (0 : ℝ) ≤ (KB Λ : ℝ) := (KB Λ).coe_nonneg
      have hcube : Cl ^ 3 = ENNReal.ofReal ((Cin Λ : ℝ) ^ 3) := by
        rw [hCl, ← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal]
        rw [NNReal.coe_pow]
      have hEq : Kgood = ENNReal.ofReal (Cs * Cd * ((Cin Λ : ℝ)) ^ 3) := by
        rw [hKgood, ← ENNReal.ofReal_mul (le_of_lt hCs), hcube,
          ← ENNReal.ofReal_mul (mul_nonneg (le_of_lt hCs) (le_of_lt hCd))]
      have hKfEq : (Kf Λ : ENNReal)
          = ENNReal.ofReal (Cs * Cd * ((Cin Λ : ℝ)) ^ 3 + (KB Λ : ℝ) + 1) := by
        rw [hKf]
        exact ENNReal.ofReal_coe_nnreal.symm
      rw [hEq, hKfEq, ← ENNReal.ofReal_coe_nnreal (p := KB Λ),
        ← ENNReal.ofReal_add hXnn hKBnn]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have hsum : (Kgood * Y * Fn * Gn) + ((KB Λ : ENNReal) * Y * Fn * Gn)
        ≤ Kf Λ * Y * Fn * Gn := by
      calc (Kgood * Y * Fn * Gn) + ((KB Λ : ENNReal) * Y * Fn * Gn)
          = (Kgood + (KB Λ : ENNReal)) * (Y * Fn * Gn) := by ring
        _ ≤ (Kf Λ : ENNReal) * (Y * Fn * Gn) := mul_le_mul' hKBsum le_rfl
        _ = Kf Λ * Y * Fn * Gn := by ring
    -- conclude
    have hmain : eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)) 1 Measure.count
        = ∑' x : ℤ, variationalNorm r (fun n : ℕ => J n x) :=
      eLpNorm_one_count_variationalNorm r J
    rw [hmain]
    exact hsplit.trans ((add_le_add hgood hbad).trans hsum)
  exact step

/-- **The case `C₀ = 0` of the target reduces to the case `C₀ = 1`.**  At the zero quadruple
`(l₁,l₂,k₁,k₂) = (0,0,0,0)` the core conditions of `C₀ = 0` and `C₀ = 1` agree
(`mdlCore_zero_of_eq_zero`) and off that quadruple the `C₀ = 0` core condition is never satisfied
(`not_inIndexSet_zero_of_ne`), so the slice family vanishes. -/
theorem MdlSliceCoreGainMemLp_c₀_zero (P : Polynomial ℤ) {r : NNReal} (hr1 : 1 ≤ r)
    {j₁ j₂ : ℤ} (h : MdlSliceCoreGainMemLp P r 1 j₁ j₂) :
    MdlSliceCoreGainMemLp P r 0 j₁ j₂ := by
  obtain ⟨c, hc, A, hA, ρ₀, hρ₀, hK⟩ := h
  refine ⟨c, hc, A, hA, ρ₀, hρ₀, ?_⟩
  intro ρ hρ hρle
  obtain ⟨K, hK'⟩ := hK ρ hρ hρle
  refine ⟨K, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t f g hΛ ha ha1 ht hk₁ hk₂ hf hg
  by_cases hquad : l₁ = 0 ∧ l₂ = 0 ∧ k₁ = 0 ∧ k₂ = 0
  · obtain ⟨e1, e2, e3, e4⟩ := hquad
    subst e1; subst e2; subst e3; subst e4
    have hcore : ∀ n, mdlCore ρ 0 a 0 0 0 0 n ↔ mdlCore ρ 1 a 0 0 0 0 n := fun n =>
      (mdlCore_zero_of_eq_zero ρ 0 a n).trans (mdlCore_zero_of_eq_zero ρ 1 a n).symm
    have hpt : ∀ (n : ℕ) (x : ℤ), mdlSliceJ ρ P 0 a f g 0 0 0 0 j₁ j₂ t n x
        = mdlSliceJ ρ P 1 a f g 0 0 0 0 j₁ j₂ t n x := by
      intro n x
      by_cases hc : mdlCore ρ 0 a 0 0 0 0 n
      · simp only [mdlSliceJ, if_pos hc, if_pos ((hcore n).mp hc)]
      · simp only [mdlSliceJ, if_neg hc, if_neg fun h1 => hc ((hcore n).mpr h1)]
    have heq : (fun x : ℤ => variationalNorm r
          (fun n : ℕ => mdlSliceJ ρ P 0 a f g 0 0 0 0 j₁ j₂ t n x))
        = fun x : ℤ => variationalNorm r
          (fun n : ℕ => mdlSliceJ ρ P 1 a f g 0 0 0 0 j₁ j₂ t n x) := by
      funext x
      congr 1
      funext n
      exact hpt n x
    rw [heq]
    exact hK' a Λ 0 0 0 0 t f g hΛ ha ha1 ht hk₁ hk₂ hf hg
  · have hpt : ∀ (n : ℕ) (x : ℤ),
        mdlSliceJ ρ P 0 a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x = 0 := by
      intro n x
      have hcore0 : ¬ mdlCore ρ 0 a l₁ l₂ k₁ k₂ n := fun hc =>
        not_inIndexSet_zero_of_ne l₁ l₂ k₁ k₂ hquad (Nat.floor (a n))
          ((mdlCore_iff ρ 0 a l₁ l₂ k₁ k₂ n).mp hc).1
      simp only [mdlSliceJ, if_neg hcore0]
    have heq : (fun x : ℤ => variationalNorm r
          (fun n : ℕ => mdlSliceJ ρ P 0 a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
        = fun _ : ℤ => variationalNorm r (fun _ : ℕ => (0 : ℂ)) := by
      funext x
      congr 1
      funext n
      exact hpt n x
    rw [heq, eLpNorm_variationalNorm_zero_local r hr1]
    exact bot_le

/-- **The assembly of `MdlSliceCoreGainMemLp` from the fixed-parameter adelic form at an
*arbitrary* variation exponent `R`.**  This is the proof of
`Work.KMTPlan.A6Clean.MdlSliceCoreGainMemLp_of_adelicFormAt` (which hard-codes `R = 2`) with the
variation exponent `R` left as a parameter; the adelic clauses at `R` are consumed by the chain
`ZModChainPropP` instantiated at the same `R`, so only the two uses of `2` (the hypothesis and the
chain call) change. -/
theorem MdlSliceCoreGainMemLp_of_adelicFormR (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P)
    {r : NNReal} {R : ℝ} {C₀ : ℕ} {j₁ j₂ : ℤ}
    (hAdel : AdelicFormAtRangeP P r R C₀ j₁ j₂) (hChain : ZModChainPropP)
    (hBad : BadPartProp P hd hA1 hI) (hAbs : LossAbsorbProp)
    (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
    (hr : 2 < r) (hR : 1 ≤ R) (hRr : R < (r : ℝ)) (hC₀ : 1 ≤ C₀) :
    MdlSliceCoreGainMemLp P r C₀ j₁ j₂ := by
  classical
  obtain ⟨cA, hcA, AA, hAA, ρA, hρA, hAdel'⟩ := hAdel
  obtain ⟨cB, hcB, AB, hAB, ρB, hρB, hBad'⟩ := hBad
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  obtain ⟨Cs, hCs, hUnif'⟩ := vrSamplingDensity_one_unif r hr1
  obtain ⟨Cd, hCd, hChain'⟩ :=
    hChain (r := r) hr1 (R := R) hR hRr
  set cc : ℝ := min cA cB / 2 with hcc
  set AA' : ℝ := 2 * AA + AB + 1 with hAA'
  set ρρ : ℝ := min ρA ρB with hρρ
  have hccpos : 0 < cc := by rw [hcc]; exact half_pos (lt_min hcA hcB)
  have hAA'nn : 0 ≤ AA' := by rw [hAA']; positivity
  have hρρpos : 0 < ρρ := by rw [hρρ]; exact lt_min hρA hρB
  refine ⟨cc, hccpos, AA', hAA'nn, ρρ, hρρpos, ?_⟩
  intro ρ hρ hρle
  have hρρA : ρρ ≤ ρA := by rw [hρρ]; exact min_le_left _ _
  have hρρB : ρρ ≤ ρB := by rw [hρρ]; exact min_le_right _ _
  have hρA' : ρ ≤ ρA := le_trans hρle hρρA
  have hρB' : ρ ≤ ρB := le_trans hρle hρρB
  obtain ⟨Cin, hCin⟩ := hAdel' ρ hρ hρA'
  obtain ⟨KB, hKB⟩ := hBad' ρ hρ hρB'
  set Kf : ℝ≥0 → ℝ≥0 := fun Λ =>
    ⟨Cs * Cd * ((Cin Λ : ℝ)) ^ 3 + (KB Λ : ℝ) + 1, by
      have hX : (0 : ℝ) ≤ Cs * Cd * ((Cin Λ : ℝ)) ^ 3 := by
        have := (Cin Λ).coe_nonneg; positivity
      have hKBn : (0 : ℝ) ≤ (KB Λ : ℝ) := (KB Λ).coe_nonneg
      linarith⟩ with hKf
  refine ⟨Kf, ?_⟩
  -- ### the datum level
  intro a Λ l₁ l₂ k₁ k₂ t f g hΛ ha ha1 ht hk₁ hk₂ hf hg
  have step :
      eLpNorm (fun x : ℤ => variationalNorm r
          (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x))
        1 Measure.count
        ≤ (Kf Λ : ENNReal)
          * ENNReal.ofReal (lossWeight AA' ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ)))))
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
    set Q : ℕ := arithQ ρ (max l₁ l₂) with hQdef
    set Lv : ℕ := lcL l₁ l₂ k₁ k₂ with hLvdef
    have hQ1 : 1 ≤ Q := by rw [hQdef]; exact one_le_arithQ ρ (max l₁ l₂)
    obtain ⟨F, u, v, M, Ku, Kv, hrest⟩ :=
      hCin a Λ l₁ l₂ k₁ k₂ t f g
        hΛ ha ha1 ht hk₁ hk₂ hf hg
    obtain ⟨hband, hdiag, hbilin, hrest⟩ := hrest
    obtain ⟨⟨hM0, hMbd⟩, hrest⟩ := hrest
    obtain ⟨⟨hKu0, hKubd⟩, hrest⟩ := hrest
    obtain ⟨⟨hKv0, hKvbd⟩, hrest⟩ := hrest
    obtain ⟨hSu, hSv, hrest⟩ := hrest
    obtain ⟨humeas, hvmeas, hrest⟩ := hrest
    obtain ⟨hbase, hB1, hB2⟩ := hrest
    -- the good/bad split of the family
    set J : ℕ → ℤ → ℂ := fun n x => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x with hJ
    set famG : ℕ → ℤ → ℂ := fun n x =>
      if goodScale Q Lv (Nat.floor (a n)) then J n x else 0 with hfamG
    set famB : ℕ → ℤ → ℂ := fun n x =>
      if ¬ goodScale Q Lv (Nat.floor (a n)) then J n x else 0 with hfamB
    have hsplitJ : ∀ n x, J n x = famG n x + famB n x := by
      intro n x
      have h1 : famG n x = if goodScale Q Lv (Nat.floor (a n)) then J n x else 0 := rfl
      have h2 : famB n x = if ¬ goodScale Q Lv (Nat.floor (a n)) then J n x else 0 := rfl
      rw [h1, h2]
      by_cases h : goodScale Q Lv (Nat.floor (a n)) <;> simp [h]
    -- the pointwise subadditivity, passed to the `tsum`s
    have hsplit : (∑' x : ℤ, variationalNorm r (fun n : ℕ => J n x))
        ≤ (∑' x : ℤ, variationalNorm r (fun n : ℕ => famG n x))
          + (∑' x : ℤ, variationalNorm r (fun n : ℕ => famB n x)) := by
      rw [← ENNReal.tsum_add]
      refine ENNReal.tsum_le_tsum fun x => ?_
      have h1 : (fun n : ℕ => J n x) = (fun n : ℕ => famG n x) + (fun n : ℕ => famB n x) := by
        funext n; exact hsplitJ n x
      rw [h1]
      exact variationalNorm_add_le hr1 _ _
    -- the bad part
    have hbadB : (∑' x : ℤ, variationalNorm r (fun n : ℕ => famB n x))
        ≤ (KB Λ : ENNReal)
          * ENNReal.ofReal (lossWeight AB ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(cB * (max (l₁ : ℝ) (l₂ : ℝ)))))
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
      rw [← eLpNorm_one_count_variationalNorm r famB]
      exact hKB r hr C₀ hC₀ a Λ l₁ l₂ k₁ k₂ t j₁ j₂ hj₁ hj₂ f g
        hΛ ha ha1 ht hk₁ hk₂ hf hg
    -- the sampling transfer
    have hβpos : (0 : ℝ) < 1 / (8 * (Q : ℝ)) := by positivity
    have hβlt : 1 / (8 * (Q : ℝ)) < 1 / 2 := by
      have hQ1R : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
      have h8 : (0 : ℝ) < 8 * (Q : ℝ) := by linarith
      rw [div_lt_iff₀ h8]
      nlinarith
    have hβQ : (1 / (8 * (Q : ℝ))) * (Q : ℝ) ≤ 1 / 4 := by
      have hQ1R : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
      have h8 : (0 : ℝ) < 8 * (Q : ℝ) := by linarith
      rw [one_div_mul_eq_div, div_le_iff₀ h8]
      nlinarith
    have hmeasF : ∀ ρ' : ℤ,
        Measurable (fun x : ℝ => variationalNorm r (fun n : ℕ => F n x ρ')) :=
      fun ρ' => measurable_variationalNorm_of_hasRealFreqSupport
        (lt_of_lt_of_le zero_lt_one hr1) (fun n x => F n x ρ') (fun n => hband n ρ')
    have hsliceF : ∀ ρ' : ℤ,
        (∑' N : ℤ, variationalNorm r
            (fun n : ℕ => F n ((ρ' : ℝ) + (Q : ℝ) * (N : ℝ)) ρ'))
          ≤ ENNReal.ofReal Cs * (Q : ENNReal)⁻¹
              * ∫⁻ x : ℝ, variationalNorm r (fun n : ℕ => F n x ρ') :=
      fun ρ' => hUnif' (1 / (8 * (Q : ℝ))) hβpos hβlt (fun n x => F n x ρ')
        (fun n => hband n ρ') Q (lt_of_lt_of_le Nat.zero_lt_one hQ1) hβQ ρ'
    have hcGF : ∀ n x, famG n x = F n (x : ℝ) (x % ((Q : ℕ) : ℤ)) := by
      intro n x
      have h1 : famG n x = (if goodScale Q Lv (Nat.floor (a n)) then
          mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x else 0) := rfl
      rw [h1]
      exact (hdiag n x).symm
    have htr : (∑' x : ℤ, variationalNorm r (fun n : ℕ => famG n x))
        ≤ ENNReal.ofReal Cs
            * ∫⁻ x : ℝ, (Q : ENNReal)⁻¹ * ∑ ρ' ∈ Finset.range Q,
                variationalNorm r (fun n : ℕ => F n x (ρ' : ℤ)) :=
      diagonalVrSampling_le (r := r) (Q := Q) hQ1 hCs (F := F) hmeasF hsliceF (c := famG) hcGF
    -- the `ZMod Q` chain
    have hchain := hChain' (Q := Q) hQ1 (M := M) (Ku := Ku) (Kv := Kv) hM0 hKu0 hKv0
      (B := fun e f' θ => zmodAvg (negReflect P) Q e f' θ)
      (fun e e' f' => zmodAvg_add₁ (negReflect P) Q e e' f')
      (fun e f' f'' => zmodAvg_add₂ (negReflect P) Q e f' f'')
      humeas hvmeas hbase hB1 hB2 hSu hSv
    -- rewrite the integral of the sampling transfer into the chain's integral
    have hIntEq : (∫⁻ x : ℝ, (Q : ENNReal)⁻¹ * ∑ ρ' ∈ Finset.range Q,
          variationalNorm r (fun n : ℕ => F n x (ρ' : ℤ)))
        = ∫⁻ X : ℝ, (Q : ENNReal)⁻¹ * ∑ ρ' ∈ Finset.range Q,
            variationalNorm r (fun n : ℕ =>
              zmodAvg (negReflect P) Q (u n X) (v n X) ((ρ' : ℤ) : ZMod Q)) := by
      refine MeasureTheory.lintegral_congr fun x => ?_
      congr 1
      refine Finset.sum_congr rfl fun ρ' _ => ?_
      congr 1
      funext n
      exact hbilin n x (ρ' : ℤ)
    have hgood1 : (∑' x : ℤ, variationalNorm r (fun n : ℕ => famG n x))
        ≤ ENNReal.ofReal Cs
            * (ENNReal.ofReal Cd * ENNReal.ofReal M * ENNReal.ofReal Ku
                * ENNReal.ofReal Kv) := by
      refine htr.trans ?_
      rw [hIntEq]
      exact mul_le_mul' le_rfl hchain
    -- the constant bookkeeping of the good part
    set Y₀ : ENNReal := ENNReal.ofReal ((2 : ℝ) ^ (-(cA * (max (l₁ : ℝ) (l₂ : ℝ))))) with hY₀
    set W : ENNReal := ENNReal.ofReal (lossWeight AA ρ l₁ l₂ k₁ k₂) with hW
    set Fn : ENNReal := eLpNorm f 2 Measure.count with hFn
    set Gn : ENNReal := eLpNorm g 2 Measure.count with hGn
    set Cl : ENNReal := (Cin Λ : ENNReal) with hCl
    set Kgood : ENNReal := ENNReal.ofReal Cs * ENNReal.ofReal Cd * Cl ^ 3 with hKgood
    set Y : ENNReal := ENNReal.ofReal (lossWeight AA' ρ l₁ l₂ k₁ k₂
        * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ))))) with hY
    have hY0nn : (0 : ℝ) ≤ (2 : ℝ) ^ (-(cA * (max (l₁ : ℝ) (l₂ : ℝ)))) := by positivity
    have hLWnn : (0 : ℝ) ≤ lossWeight AA ρ l₁ l₂ k₁ k₂ :=
      le_of_lt (lossWeight_pos_vr AA ρ hAA hρ.le l₁ l₂ k₁ k₂)
    have hexp : -(min cA cB / 2) * max (l₁ : ℝ) (l₂ : ℝ)
        = -(cc * max (l₁ : ℝ) (l₂ : ℝ)) := by
      rw [hcc]; ring
    -- the three bounds combine
    have h3 : ENNReal.ofReal M * ENNReal.ofReal Ku * ENNReal.ofReal Kv
        ≤ (Cl * Y₀) * (Cl * W * Fn) * (Cl * W * Gn) := by
      have h := mul_le_mul' (mul_le_mul' hMbd hKubd) hKvbd
      simpa only [hCl, hY₀, hW, hFn, hGn] using h
    have h4 : (Cl * Y₀) * (Cl * W * Fn) * (Cl * W * Gn)
        = Cl ^ 3 * (Y₀ * W * W) * Fn * Gn := by ring
    have h5 : Y₀ * W * W ≤ Y := by
      have h' : (2 : ℝ) ^ (-(cA * max (l₁ : ℝ) (l₂ : ℝ)))
            * (lossWeight AA ρ l₁ l₂ k₁ k₂) ^ 2
          ≤ (2 : ℝ) ^ (-(min cA cB / 2) * max (l₁ : ℝ) (l₂ : ℝ))
              * lossWeight (2 * AA + AB + 1) ρ l₁ l₂ k₁ k₂ :=
        (hAbs AA AB cA cB hAA hAB hcA hcB ρ hρ l₁ l₂ k₁ k₂).1
      have h'' : (2 : ℝ) ^ (-(min cA cB / 2) * max (l₁ : ℝ) (l₂ : ℝ))
              * lossWeight AA' ρ l₁ l₂ k₁ k₂
          = lossWeight AA' ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ)))) := by
        rw [hexp]; ring
      rw [hY₀, hW, hY]
      rw [← ENNReal.ofReal_mul hY0nn, ← ENNReal.ofReal_mul (mul_nonneg hY0nn hLWnn)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc (2 : ℝ) ^ (-(cA * max (l₁ : ℝ) (l₂ : ℝ)))
            * lossWeight AA ρ l₁ l₂ k₁ k₂ * lossWeight AA ρ l₁ l₂ k₁ k₂
          = (2 : ℝ) ^ (-(cA * max (l₁ : ℝ) (l₂ : ℝ)))
              * (lossWeight AA ρ l₁ l₂ k₁ k₂) ^ 2 := by ring
        _ ≤ (2 : ℝ) ^ (-(min cA cB / 2) * max (l₁ : ℝ) (l₂ : ℝ))
              * lossWeight AA' ρ l₁ l₂ k₁ k₂ := h'
        _ = lossWeight AA' ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ)))) := h''
    have h6 : Cl ^ 3 * (Y₀ * W * W) * Fn * Gn ≤ Cl ^ 3 * Y * Fn * Gn :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl h5) le_rfl) le_rfl
    have hgood : (∑' x : ℤ, variationalNorm r (fun n : ℕ => famG n x))
        ≤ Kgood * Y * Fn * Gn := by
      refine hgood1.trans ?_
      calc ENNReal.ofReal Cs
            * (ENNReal.ofReal Cd * ENNReal.ofReal M * ENNReal.ofReal Ku * ENNReal.ofReal Kv)
          = ENNReal.ofReal Cs * ENNReal.ofReal Cd
              * (ENNReal.ofReal M * ENNReal.ofReal Ku * ENNReal.ofReal Kv) := by ring
        _ ≤ ENNReal.ofReal Cs * ENNReal.ofReal Cd * (Cl ^ 3 * Y * Fn * Gn) := by
            refine mul_le_mul' le_rfl ?_
            exact (h3.trans (le_of_eq h4)).trans h6
        _ = Kgood * Y * Fn * Gn := by rw [hKgood]; ring
    -- the bad part in the same shape
    have hbadY : ENNReal.ofReal (lossWeight AB ρ l₁ l₂ k₁ k₂
          * (2 : ℝ) ^ (-(cB * (max (l₁ : ℝ) (l₂ : ℝ))))) ≤ Y := by
      have h : lossWeight AB ρ l₁ l₂ k₁ k₂ * (2 : ℝ) ^ (-(cB * max (l₁ : ℝ) (l₂ : ℝ)))
          ≤ (2 : ℝ) ^ (-(min cA cB / 2) * max (l₁ : ℝ) (l₂ : ℝ))
              * lossWeight (2 * AA + AB + 1) ρ l₁ l₂ k₁ k₂ :=
        (hAbs AA AB cA cB hAA hAB hcA hcB ρ hρ l₁ l₂ k₁ k₂).2
      rw [hY]
      refine ENNReal.ofReal_le_ofReal ?_
      calc lossWeight AB ρ l₁ l₂ k₁ k₂
            * (2 : ℝ) ^ (-(cB * (max (l₁ : ℝ) (l₂ : ℝ))))
          = lossWeight AB ρ l₁ l₂ k₁ k₂ * (2 : ℝ) ^ (-(cB * max (l₁ : ℝ) (l₂ : ℝ))) := by ring
        _ ≤ (2 : ℝ) ^ (-(min cA cB / 2) * max (l₁ : ℝ) (l₂ : ℝ))
              * lossWeight AA' ρ l₁ l₂ k₁ k₂ := h
        _ = lossWeight AA' ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ)))) := by
            rw [hexp]; ring
    have hbad : (∑' x : ℤ, variationalNorm r (fun n : ℕ => famB n x))
        ≤ (KB Λ : ENNReal) * Y * Fn * Gn := by
      refine hbadB.trans ?_
      calc (KB Λ : ENNReal) * ENNReal.ofReal (lossWeight AB ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(cB * (max (l₁ : ℝ) (l₂ : ℝ)))))
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count
          ≤ (KB Λ : ENNReal) * Y * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
            refine mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hbadY) le_rfl) le_rfl
        _ = (KB Λ : ENNReal) * Y * Fn * Gn := by rw [hFn, hGn]
    -- the two halves combine
    have hKBsum : Kgood + (KB Λ : ENNReal) ≤ (Kf Λ : ENNReal) := by
      have hXnn : (0 : ℝ) ≤ Cs * Cd * ((Cin Λ : ℝ)) ^ 3 := by
        have := (Cin Λ).coe_nonneg; positivity
      have hKBnn : (0 : ℝ) ≤ (KB Λ : ℝ) := (KB Λ).coe_nonneg
      have hcube : Cl ^ 3 = ENNReal.ofReal ((Cin Λ : ℝ) ^ 3) := by
        rw [hCl, ← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal]
        rw [NNReal.coe_pow]
      have hEq : Kgood = ENNReal.ofReal (Cs * Cd * ((Cin Λ : ℝ)) ^ 3) := by
        rw [hKgood, ← ENNReal.ofReal_mul (le_of_lt hCs), hcube,
          ← ENNReal.ofReal_mul (mul_nonneg (le_of_lt hCs) (le_of_lt hCd))]
      have hKfEq : (Kf Λ : ENNReal)
          = ENNReal.ofReal (Cs * Cd * ((Cin Λ : ℝ)) ^ 3 + (KB Λ : ℝ) + 1) := by
        rw [hKf]
        exact ENNReal.ofReal_coe_nnreal.symm
      rw [hEq, hKfEq, ← ENNReal.ofReal_coe_nnreal (p := KB Λ),
        ← ENNReal.ofReal_add hXnn hKBnn]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have hsum : (Kgood * Y * Fn * Gn) + ((KB Λ : ENNReal) * Y * Fn * Gn)
        ≤ Kf Λ * Y * Fn * Gn := by
      calc (Kgood * Y * Fn * Gn) + ((KB Λ : ENNReal) * Y * Fn * Gn)
          = (Kgood + (KB Λ : ENNReal)) * (Y * Fn * Gn) := by ring
        _ ≤ (Kf Λ : ENNReal) * (Y * Fn * Gn) := mul_le_mul' hKBsum le_rfl
        _ = Kf Λ * Y * Fn * Gn := by ring
    -- conclude
    have hmain : eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)) 1 Measure.count
        = ∑' x : ℤ, variationalNorm r (fun n : ℕ => J n x) :=
      eLpNorm_one_count_variationalNorm r J
    rw [hmain]
    exact hsplit.trans ((add_le_add hgood hbad).trans hsum)
  exact step
-- **(A6 §8) the case-splitting consumer of the adelic form.**
--
-- This is `Work.KMTPlan.A6Clean.MdlSliceCoreGainMemLp_of_pieces_fromPos`
-- (`A6Clean/MdlSliceCoreGainMemLp_of_pieces_fromPos.lean`, PROVED, 318 lines) with exactly two
-- changes, both at the *datum* level:
--
-- * its hypothesis `hAdel : AdelicFormPropRangePos P hd hA1 hI` is replaced by
--   `hAdel : AdelicFormPropRangePosB P hd hA1 hI B`, i.e. the same clause list demanded only on
--   the data with `B ρ ≤ lcL l₁ l₂ k₁ k₂` (the gate is *mathematically necessary*: the standard
--   band-`1/(8·arithQ ρ (max l₁ l₂))` lift of the frozen slice does not exist for bounded `lcL`;
--   see `NOTES_A6_adelicCaseB_OBSTRUCTION_SESSION.md`);
-- * on the complementary data (`¬ B ρ ≤ lcL`) the bound is taken from the new input `hNoGain`,
--   the loss-form (no-gain) slice bound `MdlSliceNoGainAt` (the A6 twin of the PROVED
--   `Work.KMTAreas.A7.ModelLargeBound` at `(p₁,p₂) = (2,2)`).
--
-- The proof: copy `…_fromPos` verbatim and
-- * in the datum block, after `intro a Λ l₁ l₂ k₁ k₂ t f g …`, insert
--   `by_cases hgate : B ρ ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂`;
-- * in the `true` branch use `hCin hgate a Λ …` (the gated clauses) and keep the existing proof
--   (sampling transfer `diagonalVrSampling_le` with `β = 1/(8·arithQ ρ (max l₁ l₂))`, the
--   `ZMod Q` chain `hChain`, the bad part `hBad`, the loss absorption `hAbs`);
-- * in the `false` branch apply `hNoGain C₀ hC₀ r hr j₁ j₂ hj₁ hj₂` and absorb: since
--   `lcL l₁ l₂ k₁ k₂ < B ρ`, all of `l₁,l₂,k₁,k₂` are `≤ B ρ`, so
--   `lossWeight cN ρ l₁ l₂ k₁ k₂ ≤ (1+Bρ)^{cN}·2^{cNρBρ}` (`lossWeight_le_const`) and
--   `2^{-cc·max(l₁,l₂)} ≥ 2^{-cc·Bρ}` are `ρ`-constants *at the datum level*; the exponent of the
--   loss weight therefore needs **no** change (`A := AA'` as in `…_fromPos`), and the finite
--   `ρ`-only ratio
--   `Rn := (1+Bρ)^{cN}·2^{cNρBρ} / 2^{-cc·Bρ}` (the "no-gain divisor", `div_mul_cancel₀`) is
--   folded into `K(Λ)` by `K := Kf + KN·Rn` — legitimate because `K` is chosen inside
--   `intro ρ hρ hρle`;
-- * combine the outer constants of the two branches (`c := min c_adelic c_bad/2`, `A := AA'`,
--   `ρ₀ := min (min ρ_adelic ρ_bad) ρ_nogain`, `K := …`) exactly as in the file being copied.
-- The `hrT : (r : ℝ) < adelicRTop P` hypothesis is kept as in `…_fromPos` (the caller `r`-reduces
-- with `Work.KMTPlan.A6.exists_range_le` + `MdlSliceCoreGainMemLp_of_le`, both proved).

/-- **The gated §8 adelic form at *fixed* parameters.**  The body of
`Work.KMTPlan.A6Clean.AdelicFormPropRangePosB` at `(r, R, C₀, j₁, j₂)`: the constants
`c, A, ρ₀, Cin` may depend on those parameters, but not on the datum
`(a, Λ, l₁, l₂, k₁, k₂, t, f, g)`; the clauses are demanded only on the data with
`B ρ ≤ lcL l₁ l₂ k₁ k₂`. -/
def AdelicFormAtRangePB (P : ℤ[X]) (r : ℝ≥0) (R : ℝ) (C₀ : ℕ) (j₁ j₂ : ℤ) (B : ℝ → ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ A : ℝ, 0 ≤ A ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
    ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ Cin : ℝ≥0 → ℝ≥0,
      ∀ (a : ℕ → ℝ≥0) (Λ : ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₁ = 0 → j₁ ≠ -1) → (k₂ = 0 → j₂ ≠ -1) →
        MemLp f 2 Measure.count → MemLp g 2 Measure.count →
        B ρ ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ →
        AdelicClausesAt P ρ R r a Λ l₁ l₂ k₁ k₂ t j₁ j₂ f g C₀ c A Cin

/-- **The loss weight at a bounded `lcL` is a `ρ`-constant.**  If `lcL l₁ l₂ k₁ k₂ ≤ M` then
`lossWeight c ρ l₁ l₂ k₁ k₂ ≤ (1+M)^c·2^{cρM}`; this is what lets the no-gain branch be absorbed
into `K(Λ)` on the data with `lcL l₁ l₂ k₁ k₂ < B ρ`. -/
lemma lossWeight_le_const {c ρ : ℝ} (hc : 0 ≤ c) (hρ : 0 ≤ ρ) {l₁ l₂ k₁ k₂ M : ℕ}
    (h : Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ M) :
    Work.KMTAreas.A7.lossWeight c ρ l₁ l₂ k₁ k₂
      ≤ (1 + (M : ℝ)) ^ c * (2 : ℝ) ^ (c * ρ * (M : ℝ)) := by
  have hx : Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ ≤ (M : ℝ) := by
    rw [Work.KMTAreas.A7.lmaxR, ← Work.KMTPlan.A6.lcL_eq]
    exact_mod_cast h
  have hx0 : (0 : ℝ) ≤ Work.KMTAreas.A7.lmaxR l₁ l₂ k₁ k₂ := by
    rw [Work.KMTAreas.A7.lmaxR, ← Work.KMTPlan.A6.lcL_eq]
    push_cast
    positivity
  unfold Work.KMTAreas.A7.lossWeight
  refine mul_le_mul ?_ ?_ (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by linarith) _)
  · exact Real.rpow_le_rpow (by linarith) (by linarith) hc
  · exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_left hx (mul_nonneg hc hρ))

/-- **The assembly of `MdlSliceCoreGainMemLp` from the *gated* adelic form and the loss-form
(no-gain) slice bound, at the fixed parameters `(r, R, C₀, j₁, j₂)`.**

This is `Work.KMTPlan.A6Clean.MdlSliceCoreGainMemLp_of_adelicFormR`
(`A6Clean/MdlSliceCoreGainMemLp_of_pieces_fromPos.lean`) with the datum-level case split on the
threshold `B ρ ≤ lcL l₁ l₂ k₁ k₂`: on the large-`lcL` data the gated adelic clauses run the
existing proof (Shannon sampling transfer + `ZMod Q` chain + bad part + loss absorption), and on
the bounded-`lcL` data the loss-form bound `hNoGain` applies, its weight being absorbed into
`K(Λ)` because `lcL < B ρ` makes both `lossWeight cN ρ l₁ l₂ k₁ k₂` and
`2^{-cc·max(l₁,l₂)}` `ρ`-constants at the datum level. -/
theorem MdlSliceCoreGainMemLp_of_adelicFormBR (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P)
    {r : NNReal} {R : ℝ} {C₀ : ℕ} {j₁ j₂ : ℤ} (B : ℝ → ℕ)
    (hAdel : AdelicFormAtRangePB P r R C₀ j₁ j₂ B)
    (hNoGain : MdlSliceNoGainAt P hd hA1 C₀ r j₁ j₂)
    (hChain : ZModChainPropP) (hBad : BadPartProp P hd hA1 hI) (hAbs : LossAbsorbProp)
    (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
    (hr : 2 < r) (hR : 1 ≤ R) (hRr : R < (r : ℝ)) (hC₀ : 1 ≤ C₀) :
    MdlSliceCoreGainMemLp P r C₀ j₁ j₂ := by
  classical
  obtain ⟨cA, hcA, AA, hAA, ρA, hρA, hAdel'⟩ := hAdel
  obtain ⟨cB, hcB, AB, hAB, ρB, hρB, hBad'⟩ := hBad
  obtain ⟨cN, hcN, ρN, hρN, hN'⟩ := hNoGain
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  obtain ⟨Cs, hCs, hUnif'⟩ := vrSamplingDensity_one_unif r hr1
  obtain ⟨Cd, hCd, hChain'⟩ :=
    hChain (r := r) hr1 (R := R) hR hRr
  set cc : ℝ := min cA cB / 2 with hcc
  set AA' : ℝ := 2 * AA + AB + 1 with hAA'
  set ρρ : ℝ := min (min ρA ρB) ρN with hρρ
  have hccpos : 0 < cc := by rw [hcc]; exact half_pos (lt_min hcA hcB)
  have hAA'nn : 0 ≤ AA' := by rw [hAA']; positivity
  have hρρpos : 0 < ρρ := by rw [hρρ]; exact lt_min (lt_min hρA hρB) hρN
  refine ⟨cc, hccpos, AA', hAA'nn, ρρ, hρρpos, ?_⟩
  intro ρ hρ hρle
  have hρρA : ρρ ≤ ρA := le_trans (min_le_left _ _) (min_le_left _ _)
  have hρρB : ρρ ≤ ρB := le_trans (min_le_left _ _) (min_le_right _ _)
  have hρρN : ρρ ≤ ρN := min_le_right _ _
  have hρA' : ρ ≤ ρA := le_trans hρle hρρA
  have hρB' : ρ ≤ ρB := le_trans hρle hρρB
  have hρN' : ρ ≤ ρN := le_trans hρle hρρN
  obtain ⟨Cin, hCin⟩ := hAdel' ρ hρ hρA'
  obtain ⟨KB, hKB⟩ := hBad' ρ hρ hρB'
  obtain ⟨KN, hKN⟩ := hN' ρ hρ hρN'
  -- the `ρ`-only absorption constant of the no-gain branch
  set M0 : ℕ := B ρ with hM0
  set Rn : ℝ := (1 + (M0 : ℝ)) ^ cN * (2 : ℝ) ^ (cN * ρ * (M0 : ℝ))
      / (2 : ℝ) ^ (-(cc * (M0 : ℝ))) with hRn
  have hRnn : 0 ≤ Rn := by
    rw [hRn]
    exact div_nonneg (by positivity)
      (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
  set Kf : ℝ≥0 → ℝ≥0 := fun Λ =>
    ⟨Cs * Cd * ((Cin Λ : ℝ)) ^ 3 + (KB Λ : ℝ) + 1, by
      have hX : (0 : ℝ) ≤ Cs * Cd * ((Cin Λ : ℝ)) ^ 3 := by
        have := (Cin Λ).coe_nonneg; positivity
      have hKBn : (0 : ℝ) ≤ (KB Λ : ℝ) := (KB Λ).coe_nonneg
      linarith⟩ with hKf
  set K : ℝ≥0 → ℝ≥0 := fun Λ => Kf Λ + KN Λ * Real.toNNReal Rn with hK
  refine ⟨K, ?_⟩
  -- ### the datum level
  intro a Λ l₁ l₂ k₁ k₂ t f g hΛ ha ha1 ht hk₁ hk₂ hf hg
  by_cases hgate : B ρ ≤ Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂
  · -- ### the gated branch: `B ρ ≤ lcL`, the §8 adelic clauses (proof of `…_fromPos`)
    set Q : ℕ := arithQ ρ (max l₁ l₂) with hQdef
    set Lv : ℕ := lcL l₁ l₂ k₁ k₂ with hLvdef
    have hQ1 : 1 ≤ Q := by rw [hQdef]; exact one_le_arithQ ρ (max l₁ l₂)
    obtain ⟨F, u, v, M, Ku, Kv, hrest⟩ :=
      hCin a Λ l₁ l₂ k₁ k₂ t f g
        hΛ ha ha1 ht hk₁ hk₂ hf hg hgate
    obtain ⟨hband, hdiag, hbilin, hrest⟩ := hrest
    obtain ⟨⟨hM0, hMbd⟩, hrest⟩ := hrest
    obtain ⟨⟨hKu0, hKubd⟩, hrest⟩ := hrest
    obtain ⟨⟨hKv0, hKvbd⟩, hrest⟩ := hrest
    obtain ⟨hSu, hSv, hrest⟩ := hrest
    obtain ⟨humeas, hvmeas, hrest⟩ := hrest
    obtain ⟨hbase, hB1, hB2⟩ := hrest
    -- the good/bad split of the family
    set J : ℕ → ℤ → ℂ := fun n x => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x with hJ
    set famG : ℕ → ℤ → ℂ := fun n x =>
      if goodScale Q Lv (Nat.floor (a n)) then J n x else 0 with hfamG
    set famB : ℕ → ℤ → ℂ := fun n x =>
      if ¬ goodScale Q Lv (Nat.floor (a n)) then J n x else 0 with hfamB
    have hsplitJ : ∀ n x, J n x = famG n x + famB n x := by
      intro n x
      have h1 : famG n x = if goodScale Q Lv (Nat.floor (a n)) then J n x else 0 := rfl
      have h2 : famB n x = if ¬ goodScale Q Lv (Nat.floor (a n)) then J n x else 0 := rfl
      rw [h1, h2]
      by_cases h : goodScale Q Lv (Nat.floor (a n)) <;> simp [h]
    -- the pointwise subadditivity, passed to the `tsum`s
    have hsplit : (∑' x : ℤ, variationalNorm r (fun n : ℕ => J n x))
        ≤ (∑' x : ℤ, variationalNorm r (fun n : ℕ => famG n x))
          + (∑' x : ℤ, variationalNorm r (fun n : ℕ => famB n x)) := by
      rw [← ENNReal.tsum_add]
      refine ENNReal.tsum_le_tsum fun x => ?_
      have h1 : (fun n : ℕ => J n x) = (fun n : ℕ => famG n x) + (fun n : ℕ => famB n x) := by
        funext n; exact hsplitJ n x
      rw [h1]
      exact variationalNorm_add_le hr1 _ _
    -- the bad part
    have hbadB : (∑' x : ℤ, variationalNorm r (fun n : ℕ => famB n x))
        ≤ (KB Λ : ENNReal)
          * ENNReal.ofReal (lossWeight AB ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(cB * (max (l₁ : ℝ) (l₂ : ℝ)))))
          * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
      rw [← eLpNorm_one_count_variationalNorm r famB]
      exact hKB r hr C₀ hC₀ a Λ l₁ l₂ k₁ k₂ t j₁ j₂ hj₁ hj₂ f g
        hΛ ha ha1 ht hk₁ hk₂ hf hg
    -- the sampling transfer
    have hβpos : (0 : ℝ) < 1 / (8 * (Q : ℝ)) := by positivity
    have hβlt : 1 / (8 * (Q : ℝ)) < 1 / 2 := by
      have hQ1R : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
      have h8 : (0 : ℝ) < 8 * (Q : ℝ) := by linarith
      rw [div_lt_iff₀ h8]
      nlinarith
    have hβQ : (1 / (8 * (Q : ℝ))) * (Q : ℝ) ≤ 1 / 4 := by
      have hQ1R : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ1
      have h8 : (0 : ℝ) < 8 * (Q : ℝ) := by linarith
      rw [one_div_mul_eq_div, div_le_iff₀ h8]
      nlinarith
    have hmeasF : ∀ ρ' : ℤ,
        Measurable (fun x : ℝ => variationalNorm r (fun n : ℕ => F n x ρ')) :=
      fun ρ' => measurable_variationalNorm_of_hasRealFreqSupport
        (lt_of_lt_of_le zero_lt_one hr1) (fun n x => F n x ρ') (fun n => hband n ρ')
    have hsliceF : ∀ ρ' : ℤ,
        (∑' N : ℤ, variationalNorm r
            (fun n : ℕ => F n ((ρ' : ℝ) + (Q : ℝ) * (N : ℝ)) ρ'))
          ≤ ENNReal.ofReal Cs * (Q : ENNReal)⁻¹
              * ∫⁻ x : ℝ, variationalNorm r (fun n : ℕ => F n x ρ') :=
      fun ρ' => hUnif' (1 / (8 * (Q : ℝ))) hβpos hβlt (fun n x => F n x ρ')
        (fun n => hband n ρ') Q (lt_of_lt_of_le Nat.zero_lt_one hQ1) hβQ ρ'
    have hcGF : ∀ n x, famG n x = F n (x : ℝ) (x % ((Q : ℕ) : ℤ)) := by
      intro n x
      have h1 : famG n x = (if goodScale Q Lv (Nat.floor (a n)) then
          mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x else 0) := rfl
      rw [h1]
      exact (hdiag n x).symm
    have htr : (∑' x : ℤ, variationalNorm r (fun n : ℕ => famG n x))
        ≤ ENNReal.ofReal Cs
            * ∫⁻ x : ℝ, (Q : ENNReal)⁻¹ * ∑ ρ' ∈ Finset.range Q,
                variationalNorm r (fun n : ℕ => F n x (ρ' : ℤ)) :=
      diagonalVrSampling_le (r := r) (Q := Q) hQ1 hCs (F := F) hmeasF hsliceF (c := famG) hcGF
    -- the `ZMod Q` chain
    have hchain := hChain' (Q := Q) hQ1 (M := M) (Ku := Ku) (Kv := Kv) hM0 hKu0 hKv0
      (B := fun e f' θ => zmodAvg (negReflect P) Q e f' θ)
      (fun e e' f' => zmodAvg_add₁ (negReflect P) Q e e' f')
      (fun e f' f'' => zmodAvg_add₂ (negReflect P) Q e f' f'')
      humeas hvmeas hbase hB1 hB2 hSu hSv
    -- rewrite the integral of the sampling transfer into the chain's integral
    have hIntEq : (∫⁻ x : ℝ, (Q : ENNReal)⁻¹ * ∑ ρ' ∈ Finset.range Q,
          variationalNorm r (fun n : ℕ => F n x (ρ' : ℤ)))
        = ∫⁻ X : ℝ, (Q : ENNReal)⁻¹ * ∑ ρ' ∈ Finset.range Q,
            variationalNorm r (fun n : ℕ =>
              zmodAvg (negReflect P) Q (u n X) (v n X) ((ρ' : ℤ) : ZMod Q)) := by
      refine MeasureTheory.lintegral_congr fun x => ?_
      congr 1
      refine Finset.sum_congr rfl fun ρ' _ => ?_
      congr 1
      funext n
      exact hbilin n x (ρ' : ℤ)
    have hgood1 : (∑' x : ℤ, variationalNorm r (fun n : ℕ => famG n x))
        ≤ ENNReal.ofReal Cs
            * (ENNReal.ofReal Cd * ENNReal.ofReal M * ENNReal.ofReal Ku
                * ENNReal.ofReal Kv) := by
      refine htr.trans ?_
      rw [hIntEq]
      exact mul_le_mul' le_rfl hchain
    -- the constant bookkeeping of the good part
    set Y₀ : ENNReal := ENNReal.ofReal ((2 : ℝ) ^ (-(cA * (max (l₁ : ℝ) (l₂ : ℝ))))) with hY₀
    set W : ENNReal := ENNReal.ofReal (lossWeight AA ρ l₁ l₂ k₁ k₂) with hW
    set Fn : ENNReal := eLpNorm f 2 Measure.count with hFn
    set Gn : ENNReal := eLpNorm g 2 Measure.count with hGn
    set Cl : ENNReal := (Cin Λ : ENNReal) with hCl
    set Kgood : ENNReal := ENNReal.ofReal Cs * ENNReal.ofReal Cd * Cl ^ 3 with hKgood
    set Y : ENNReal := ENNReal.ofReal (lossWeight AA' ρ l₁ l₂ k₁ k₂
        * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ))))) with hY
    have hY0nn : (0 : ℝ) ≤ (2 : ℝ) ^ (-(cA * (max (l₁ : ℝ) (l₂ : ℝ)))) := by positivity
    have hLWnn : (0 : ℝ) ≤ lossWeight AA ρ l₁ l₂ k₁ k₂ :=
      le_of_lt (lossWeight_pos_vr AA ρ hAA hρ.le l₁ l₂ k₁ k₂)
    have hexp : -(min cA cB / 2) * max (l₁ : ℝ) (l₂ : ℝ)
        = -(cc * max (l₁ : ℝ) (l₂ : ℝ)) := by
      rw [hcc]; ring
    -- the three bounds combine
    have h3 : ENNReal.ofReal M * ENNReal.ofReal Ku * ENNReal.ofReal Kv
        ≤ (Cl * Y₀) * (Cl * W * Fn) * (Cl * W * Gn) := by
      have h := mul_le_mul' (mul_le_mul' hMbd hKubd) hKvbd
      simpa only [hCl, hY₀, hW, hFn, hGn] using h
    have h4 : (Cl * Y₀) * (Cl * W * Fn) * (Cl * W * Gn)
        = Cl ^ 3 * (Y₀ * W * W) * Fn * Gn := by ring
    have h5 : Y₀ * W * W ≤ Y := by
      have h' : (2 : ℝ) ^ (-(cA * max (l₁ : ℝ) (l₂ : ℝ)))
            * (lossWeight AA ρ l₁ l₂ k₁ k₂) ^ 2
          ≤ (2 : ℝ) ^ (-(min cA cB / 2) * max (l₁ : ℝ) (l₂ : ℝ))
              * lossWeight (2 * AA + AB + 1) ρ l₁ l₂ k₁ k₂ :=
        (hAbs AA AB cA cB hAA hAB hcA hcB ρ hρ l₁ l₂ k₁ k₂).1
      have h'' : (2 : ℝ) ^ (-(min cA cB / 2) * max (l₁ : ℝ) (l₂ : ℝ))
              * lossWeight AA' ρ l₁ l₂ k₁ k₂
          = lossWeight AA' ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ)))) := by
        rw [hexp]; ring
      rw [hY₀, hW, hY]
      rw [← ENNReal.ofReal_mul hY0nn, ← ENNReal.ofReal_mul (mul_nonneg hY0nn hLWnn)]
      refine ENNReal.ofReal_le_ofReal ?_
      calc (2 : ℝ) ^ (-(cA * max (l₁ : ℝ) (l₂ : ℝ)))
            * lossWeight AA ρ l₁ l₂ k₁ k₂ * lossWeight AA ρ l₁ l₂ k₁ k₂
          = (2 : ℝ) ^ (-(cA * max (l₁ : ℝ) (l₂ : ℝ)))
              * (lossWeight AA ρ l₁ l₂ k₁ k₂) ^ 2 := by ring
        _ ≤ (2 : ℝ) ^ (-(min cA cB / 2) * max (l₁ : ℝ) (l₂ : ℝ))
              * lossWeight AA' ρ l₁ l₂ k₁ k₂ := h'
        _ = lossWeight AA' ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ)))) := h''
    have h6 : Cl ^ 3 * (Y₀ * W * W) * Fn * Gn ≤ Cl ^ 3 * Y * Fn * Gn :=
      mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl h5) le_rfl) le_rfl
    have hgood : (∑' x : ℤ, variationalNorm r (fun n : ℕ => famG n x))
        ≤ Kgood * Y * Fn * Gn := by
      refine hgood1.trans ?_
      calc ENNReal.ofReal Cs
            * (ENNReal.ofReal Cd * ENNReal.ofReal M * ENNReal.ofReal Ku * ENNReal.ofReal Kv)
          = ENNReal.ofReal Cs * ENNReal.ofReal Cd
              * (ENNReal.ofReal M * ENNReal.ofReal Ku * ENNReal.ofReal Kv) := by ring
        _ ≤ ENNReal.ofReal Cs * ENNReal.ofReal Cd * (Cl ^ 3 * Y * Fn * Gn) := by
            refine mul_le_mul' le_rfl ?_
            exact (h3.trans (le_of_eq h4)).trans h6
        _ = Kgood * Y * Fn * Gn := by rw [hKgood]; ring
    -- the bad part in the same shape
    have hbadY : ENNReal.ofReal (lossWeight AB ρ l₁ l₂ k₁ k₂
          * (2 : ℝ) ^ (-(cB * (max (l₁ : ℝ) (l₂ : ℝ))))) ≤ Y := by
      have h : lossWeight AB ρ l₁ l₂ k₁ k₂ * (2 : ℝ) ^ (-(cB * max (l₁ : ℝ) (l₂ : ℝ)))
          ≤ (2 : ℝ) ^ (-(min cA cB / 2) * max (l₁ : ℝ) (l₂ : ℝ))
              * lossWeight (2 * AA + AB + 1) ρ l₁ l₂ k₁ k₂ :=
        (hAbs AA AB cA cB hAA hAB hcA hcB ρ hρ l₁ l₂ k₁ k₂).2
      rw [hY]
      refine ENNReal.ofReal_le_ofReal ?_
      calc lossWeight AB ρ l₁ l₂ k₁ k₂
            * (2 : ℝ) ^ (-(cB * (max (l₁ : ℝ) (l₂ : ℝ))))
          = lossWeight AB ρ l₁ l₂ k₁ k₂ * (2 : ℝ) ^ (-(cB * max (l₁ : ℝ) (l₂ : ℝ))) := by ring
        _ ≤ (2 : ℝ) ^ (-(min cA cB / 2) * max (l₁ : ℝ) (l₂ : ℝ))
              * lossWeight AA' ρ l₁ l₂ k₁ k₂ := h
        _ = lossWeight AA' ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ)))) := by
            rw [hexp]; ring
    have hbad : (∑' x : ℤ, variationalNorm r (fun n : ℕ => famB n x))
        ≤ (KB Λ : ENNReal) * Y * Fn * Gn := by
      refine hbadB.trans ?_
      calc (KB Λ : ENNReal) * ENNReal.ofReal (lossWeight AB ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(cB * (max (l₁ : ℝ) (l₂ : ℝ)))))
            * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count
          ≤ (KB Λ : ENNReal) * Y * eLpNorm f 2 Measure.count * eLpNorm g 2 Measure.count := by
            refine mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hbadY) le_rfl) le_rfl
        _ = (KB Λ : ENNReal) * Y * Fn * Gn := by rw [hFn, hGn]
    -- the two halves combine
    have hKBsum : Kgood + (KB Λ : ENNReal) ≤ (Kf Λ : ENNReal) := by
      have hXnn : (0 : ℝ) ≤ Cs * Cd * ((Cin Λ : ℝ)) ^ 3 := by
        have := (Cin Λ).coe_nonneg; positivity
      have hKBnn : (0 : ℝ) ≤ (KB Λ : ℝ) := (KB Λ).coe_nonneg
      have hcube : Cl ^ 3 = ENNReal.ofReal ((Cin Λ : ℝ) ^ 3) := by
        rw [hCl, ← ENNReal.coe_pow, ← ENNReal.ofReal_coe_nnreal]
        rw [NNReal.coe_pow]
      have hEq : Kgood = ENNReal.ofReal (Cs * Cd * ((Cin Λ : ℝ)) ^ 3) := by
        rw [hKgood, ← ENNReal.ofReal_mul (le_of_lt hCs), hcube,
          ← ENNReal.ofReal_mul (mul_nonneg (le_of_lt hCs) (le_of_lt hCd))]
      have hKfEq : (Kf Λ : ENNReal)
          = ENNReal.ofReal (Cs * Cd * ((Cin Λ : ℝ)) ^ 3 + (KB Λ : ℝ) + 1) := by
        rw [hKf]
        exact ENNReal.ofReal_coe_nnreal.symm
      rw [hEq, hKfEq, ← ENNReal.ofReal_coe_nnreal (p := KB Λ),
        ← ENNReal.ofReal_add hXnn hKBnn]
      exact ENNReal.ofReal_le_ofReal (by linarith)
    have hsum : (Kgood * Y * Fn * Gn) + ((KB Λ : ENNReal) * Y * Fn * Gn)
        ≤ Kf Λ * Y * Fn * Gn := by
      calc (Kgood * Y * Fn * Gn) + ((KB Λ : ENNReal) * Y * Fn * Gn)
          = (Kgood + (KB Λ : ENNReal)) * (Y * Fn * Gn) := by ring
        _ ≤ (Kf Λ : ENNReal) * (Y * Fn * Gn) := mul_le_mul' hKBsum le_rfl
        _ = Kf Λ * Y * Fn * Gn := by ring
    -- conclude
    have hmain : eLpNorm (fun x : ℤ => variationalNorm r
        (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ j₁ j₂ t n x)) 1 Measure.count
        = ∑' x : ℤ, variationalNorm r (fun n : ℕ => J n x) :=
      eLpNorm_one_count_variationalNorm r J
    rw [hmain]
    have hKle : (Kf Λ : ENNReal) ≤ (K Λ : ENNReal) := by
      rw [hK, ENNReal.coe_add, ENNReal.coe_mul]
      exact le_add_right le_rfl
    exact (hsplit.trans ((add_le_add hgood hbad).trans hsum)).trans
      (mul_le_mul' (mul_le_mul' (mul_le_mul' hKle le_rfl) le_rfl) le_rfl)
  · -- ### the bounded-`lcL` branch: the loss-form (no-gain) bound for the whole family
    have hMlt : Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ < M0 := by
      rw [hM0]; exact not_le.mp hgate
    have hlcLle : Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂ ≤ M0 := le_of_lt hMlt
    have hmaxle : max l₁ l₂ ≤ M0 := by
      rw [Work.KMTPlan.A6.lcL] at hlcLle
      exact le_trans (le_max_left _ _) hlcLle
    have hmaxRle : max (l₁ : ℝ) (l₂ : ℝ) ≤ (M0 : ℝ) := by exact_mod_cast hmaxle
    -- the weight at the bounded `lcL` is a `ρ`-constant
    have hw1 : Work.KMTAreas.A7.lossWeight cN ρ l₁ l₂ k₁ k₂
        ≤ Rn * (2 : ℝ) ^ (-(cc * (M0 : ℝ))) := by
      have h1 : Work.KMTAreas.A7.lossWeight cN ρ l₁ l₂ k₁ k₂
          ≤ (1 + (M0 : ℝ)) ^ cN * (2 : ℝ) ^ (cN * ρ * (M0 : ℝ)) :=
        lossWeight_le_const hcN hρ.le hlcLle
      have h2 : (1 + (M0 : ℝ)) ^ cN * (2 : ℝ) ^ (cN * ρ * (M0 : ℝ))
          = Rn * (2 : ℝ) ^ (-(cc * (M0 : ℝ))) := by
        rw [hRn]
        exact (div_mul_cancel₀
          ((1 + (M0 : ℝ)) ^ cN * (2 : ℝ) ^ (cN * ρ * (M0 : ℝ)))
          (ne_of_gt (Real.rpow_pos_of_pos (by norm_num) _))).symm
      exact h1.trans (le_of_eq h2)
    -- the gain and the loss weight of the target are both `ρ`-constants on this datum
    have hwl : (2 : ℝ) ^ (-(cc * (M0 : ℝ)))
        ≤ Work.KMTAreas.A7.lossWeight AA' ρ l₁ l₂ k₁ k₂
          * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ)))) := by
      have hle1 : (2 : ℝ) ^ (-(cc * (M0 : ℝ)))
          ≤ (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ)))) := by
        refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
        have hccm : cc * (max (l₁ : ℝ) (l₂ : ℝ)) ≤ cc * (M0 : ℝ) :=
          mul_le_mul_of_nonneg_left hmaxRle hccpos.le
        linarith
      have hW1 : (1 : ℝ) ≤ Work.KMTAreas.A7.lossWeight AA' ρ l₁ l₂ k₁ k₂ :=
        Work.KMTAreas.A7Hi.one_le_lossWeight_of_nonneg AA' ρ hAA'nn hρ.le l₁ l₂ k₁ k₂
      have hb0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ)))) :=
        Real.rpow_nonneg (by norm_num) _
      calc (2 : ℝ) ^ (-(cc * (M0 : ℝ)))
          ≤ (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ)))) := hle1
        _ = 1 * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ)))) := (one_mul _).symm
        _ ≤ Work.KMTAreas.A7.lossWeight AA' ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ)))) :=
            mul_le_mul_of_nonneg_right hW1 hb0
    have hw : Work.KMTAreas.A7.lossWeight cN ρ l₁ l₂ k₁ k₂
        ≤ Rn * (Work.KMTAreas.A7.lossWeight AA' ρ l₁ l₂ k₁ k₂
            * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ))))) :=
      hw1.trans (mul_le_mul_of_nonneg_left hwl hRnn)
    -- pass to `ENNReal`
    have hof : ENNReal.ofReal (Work.KMTAreas.A7.lossWeight cN ρ l₁ l₂ k₁ k₂)
        ≤ ENNReal.ofReal Rn
          * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight AA' ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ))))) := by
      rw [← ENNReal.ofReal_mul hRnn]
      exact ENNReal.ofReal_le_ofReal hw
    have hKcoeeq : (K Λ : ENNReal)
        = (Kf Λ : ENNReal) + (KN Λ : ENNReal) * ENNReal.ofReal Rn := by
      rw [hK]
      push_cast
      rfl
    have hstep1 : (KN Λ : ENNReal)
          * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight cN ρ l₁ l₂ k₁ k₂)
        ≤ (K Λ : ENNReal)
          * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight AA' ρ l₁ l₂ k₁ k₂
              * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ))))) := by
      rw [hKcoeeq]
      calc (KN Λ : ENNReal)
            * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight cN ρ l₁ l₂ k₁ k₂)
          ≤ (KN Λ : ENNReal)
              * (ENNReal.ofReal Rn
                * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight AA' ρ l₁ l₂ k₁ k₂
                    * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ)))))) :=
            mul_le_mul' le_rfl hof
        _ = ((KN Λ : ENNReal) * ENNReal.ofReal Rn)
              * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight AA' ρ l₁ l₂ k₁ k₂
                  * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ))))) := by ring
        _ ≤ ((Kf Λ : ENNReal) + (KN Λ : ENNReal) * ENNReal.ofReal Rn)
              * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight AA' ρ l₁ l₂ k₁ k₂
                  * (2 : ℝ) ^ (-(cc * (max (l₁ : ℝ) (l₂ : ℝ))))) :=
            mul_le_mul' (le_add_left le_rfl) le_rfl
    exact (hKN a Λ l₁ l₂ k₁ k₂ t f g hΛ ha ha1 ht hk₁ hk₂ hf hg).trans
      (mul_le_mul' (mul_le_mul' hstep1 le_rfl) le_rfl)

/-- **The requested consumer**: the `ℓ²`-case of the frozen-slice estimate `MdlSliceCoreGainMemLp`
from the *gated* form of the §8 adelic form (variation exponent `2 < R`, constants inside the
parameters, cutoff `C₀ ≥ 1`, clauses only on the data with `B ρ ≤ lcL l₁ l₂ k₁ k₂`) together with
the loss-form (no-gain) slice bound on the complementary data.

The adelic form is instantiated at the *admissible* variation exponent `R := (2 + r)/2`, which
satisfies `2 < R` (as the producer of `AdelicFormPropRangePosB` requires) and `R < r` (as the chain
`ZModChainPropP` requires).  The assembly `MdlSliceCoreGainMemLp_of_adelicFormBR` is then run at
that `R`.  The cutoff `C₀ = 0` is reduced to `C₀ = 1` at the fixed exponent `r`
(`MdlSliceCoreGainMemLp_c₀_zero`). -/
theorem MdlSliceCoreGainMemLp_of_pieces_split (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hI : Work.KMTContract.ImprovKMT P)
    (B : ℝ → ℕ) (hAdel : Work.KMTPlan.A6Clean.AdelicFormPropRangePosB P hd hA1 hI B)
    (hNoGain : ∀ (C₀ : ℕ), 1 ≤ C₀ → ∀ (r : NNReal), 2 < r → ∀ (j₁ j₂ : ℤ),
      j₁ ∈ ({-1, 0, 1} : Finset ℤ) → j₂ ∈ ({-1, 0, 1} : Finset ℤ) →
      Work.KMTPlan.A6Clean.MdlSliceNoGainAt P hd hA1 C₀ r j₁ j₂)
    (hChain : Work.KMTPlan.A6.ZModChainPropP) (hBad : Work.KMTPlan.A6.BadPartProp P hd hA1 hI)
    (hAbs : Work.KMTPlan.A6.LossAbsorbProp)
    (r : NNReal) (hr : 2 < r) (hrT : (r : ℝ) < Work.KMTPlan.A6.adelicRTop P)
    (j₁ j₂ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) (hj₂ : j₂ ∈ ({-1, 0, 1} : Finset ℤ))
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) :
    Work.KMTPlan.A6.MdlSliceCoreGainMemLp P r C₀ j₁ j₂ := by
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  have hr2R : (2 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  set R : ℝ := (2 + (r : ℝ)) / 2 with hRdef
  have hR2 : 2 < R := by rw [hRdef]; linarith
  have hR1 : 1 ≤ R := by linarith
  have hRr : R < (r : ℝ) := by rw [hRdef]; linarith
  rcases Nat.eq_zero_or_pos C₀ with hC0 | hCpos
  · subst hC0
    refine MdlSliceCoreGainMemLp_c₀_zero P hr1 ?_
    exact MdlSliceCoreGainMemLp_of_adelicFormBR P hd hA1 hI B
      (hAdel r hr hrT R hR2 hRr 1 (le_refl 1) j₁ j₂ hj₁ hj₂)
      (hNoGain 1 (le_refl 1) r hr j₁ j₂ hj₁ hj₂) hChain hBad hAbs
      hj₁ hj₂ hr hR1 hRr (le_refl 1)
  · exact MdlSliceCoreGainMemLp_of_adelicFormBR P hd hA1 hI B
      (hAdel r hr hrT R hR2 hRr C₀ hCpos j₁ j₂ hj₁ hj₂)
      (hNoGain C₀ hCpos r hr j₁ j₂ hj₁ hj₂) hChain hBad hAbs
      hj₁ hj₂ hr hR1 hRr hCpos

end

end Work.KMTPlan.A6Clean
