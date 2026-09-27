import Submission.Work.EKLNonExc.Defs
import Submission.Work.EKLNonExc.MatrixFacts
import Submission.Work.EKLNonExc.Endgame
import Submission.Work.EKLNonExc.CloseReturn
import Submission.Work.EKLComp.USCBasic

/-!
# Assembly of the C9 component (`P_NonExc`)

Given the three inputs
* `hK_Dinj` (EKL L9.1: every compact set is contained in `Dinj δ` for some `δ > 0`),
* `hBad` (EKL Lemma 4.2/L9.2: the "bad `Lset`-returns" are null),
* `hV` (the `V`-arithmetic of the return sets),
* `noDiag` (EKL L9.3, `Work.EKLNonExc.NoDiag`),

we prove `NonExceptional μ hab c` for every `A`-invariant probability `μ`: the null set is the
countable union of the `Bad` sets, the return point comes from `exists_close_return`, and the
contradiction from `endgame`.
-/

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.EKLNonExc

open MeasureTheory Filter Topology
open Work.EKLContract

noncomputable section

/-- The `m`-fold iterate of the action of `aPrime c 1` is the action of `aPrime c m`. -/
lemma aPrime_one_iterate (c : Fin 3) (m : ℕ) (y : X3) :
    (fun x : X3 => aPrime c (1 : ℝ) • x)^[m] y = aPrime c (m : ℝ) • y := by
  induction m with
  | zero =>
    have hv : (fun i : Fin 3 => if i = c then -2 * (((0 : ℕ) : ℝ)) else (((0 : ℕ) : ℝ)))
        = (0 : Fin 3 → ℝ) := by
      funext i; by_cases h : i = c <;> simp [h]
    rw [Function.iterate_zero_apply, aPrime, hv, aDiag_zero, one_smul]
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, ← mul_smul, aPrime_one_mul c (k : ℝ),
      Nat.cast_add, Nat.cast_one]

theorem nonExceptional_of {a b c : Fin 3} (hab : a ≠ b) (hac : a ≠ c) (hcb : c ≠ b)
    (μ : Measure X3) [IsProbabilityMeasure μ] (hμ : IsAInvariant μ)
    (hK_Dinj : ∀ K : Set X3, IsCompact K → ∃ δ : ℝ, 0 < δ ∧ K ⊆ Dinj δ)
    (hBad : ∀ (ℓ ℓu n : ℕ) (ε : ℝ), 0 < ℓu → 3 * ℓu < ℓ → 0 < ε →
      μ (Bad a b c hab ℓ ℓu n ε) = 0)
    (hV : ∀ δ : ℝ, 0 < δ → ∃ ε : ℝ, 0 < ε ∧ ∀ g ∈ V ε, ∀ h ∈ V ε, h * g⁻¹ ∈ V δ)
    (noDiag : ∀ (lam : ℝ), 0 < lam → lam ≠ 1 → ∀ (x : X3) (h : SL3),
      toMat h = Matrix.diagonal (fun i => if i = c then (lam ^ 2)⁻¹ else lam) → h • x ≠ x) :
    NonExceptional μ hab c := by
  refine ⟨⋃ (ℓv : ℕ) (n : ℕ) (k : ℕ),
    Bad a b c hab (3 * (ℓv + 1) + 1) (ℓv + 1) n ((↑k + 1)⁻¹), ?_, ?_⟩
  · rw [measure_iUnion_null]
    intro ℓv
    rw [measure_iUnion_null]
    intro n
    rw [measure_iUnion_null]
    intro k
    exact hBad (3 * (ℓv + 1) + 1) (ℓv + 1) n (((k : ℝ) + 1)⁻¹) (Nat.succ_pos _)
      (by omega) (by positivity)
  · intro K hK hdisj hμK δ hδ
    obtain ⟨δu, hδu0, hKu⟩ := hK_Dinj K hK
    -- choose `ℓv` with `1/δu ≤ ℓv` and `1/(6δ) ≤ ℓv`, and put `ℓu = ℓv + 1`
    obtain ⟨ℓv, hℓv⟩ : ∃ ℓv : ℕ,
        (1 : ℝ) / δu ≤ (ℓv : ℝ) ∧ (1 : ℝ) / (6 * δ) ≤ (ℓv : ℝ) := by
      obtain ⟨m, hm⟩ := exists_nat_ge (max (1 / δu) (1 / (6 * δ)))
      exact ⟨m, le_trans (le_max_left _ _) hm, le_trans (le_max_right _ _) hm⟩
    set ℓu : ℕ := ℓv + 1 with hℓu_def
    set ℓ : ℕ := 3 * ℓu + 1 with hℓ
    have hℓu_pos_nat : 0 < ℓu := by omega
    have hℓu_pos : (0 : ℝ) < (ℓu : ℝ) := by positivity
    have hℓv_le : (ℓv : ℝ) ≤ (ℓu : ℝ) := by
      rw [hℓu_def]; push_cast; linarith
    have hℓpos : (0 : ℝ) < (ℓ : ℝ) := by positivity
    have hℓge : (1 : ℝ) ≤ (ℓ : ℝ) := by
      have : (1 : ℕ) ≤ ℓ := by omega
      exact_mod_cast this
    have hDinjK : K ⊆ Dinj ((ℓu : ℝ)⁻¹) := by
      refine Set.Subset.trans hKu (Dinj_anti ?_)
      have h2 : (1 : ℝ) ≤ δu * (ℓu : ℝ) := by
        have h := hℓv.1
        rw [div_le_iff₀ hδu0] at h
        nlinarith [h, hℓv_le]
      rw [inv_le_iff_one_le_mul₀ hℓu_pos]
      nlinarith [h2]
    have hscale : (2 * (ℓ : ℝ))⁻¹ ≤ δ := by
      have h2 : (1 : ℝ) ≤ δ * (2 * (ℓ : ℝ)) := by
        have h6 : (1 : ℝ) ≤ 6 * δ * (ℓv : ℝ) := by
          have h := hℓv.2
          rw [div_le_iff₀ (by positivity)] at h
          nlinarith [h]
        have hℓv2 : (2 : ℝ) * (ℓ : ℝ) = 6 * (ℓu : ℝ) + 2 := by
          rw [hℓ]; push_cast; ring
        nlinarith [h6, hδ, hℓv2, hℓv_le]
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      nlinarith [h2]
    have hhalf : (2 * (ℓ : ℝ))⁻¹ ≤ 1 / 2 := by
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      nlinarith [hℓge]
    -- the close return
    have hT : MeasurePreserving (fun x : X3 => aPrime c (1 : ℝ) • x) μ μ :=
      hμ (fun i => if i = c then -2 * (1 : ℝ) else 1)
    obtain ⟨hVε, hVεpos, hVε'⟩ := hV (2 * (ℓ : ℝ))⁻¹ (by positivity)
    obtain ⟨x, hxK, m, hmpos, hmK, g, hgV, hgx⟩ :=
      exists_close_return μ (fun x : X3 => aPrime c (1 : ℝ) • x) hT K hK hμK
        (by positivity : (0:ℝ) < (2 * (ℓ:ℝ))⁻¹)
        ⟨hVε, hVεpos, fun g hg h hh => hVε' g hg h hh⟩
    -- `aPrime c m • x = g • x`
    have hret : aPrime c (m : ℝ) • x = g • x := (aPrime_one_iterate c m x) ▸ hgx
    -- if the conclusion fails, the displacement lies in `Lset`
    by_contra hno
    push_neg at hno
    have hgL : g ∈ Lset hab := by
      refine hno x hxK (m : ℝ) g ?_ ?_ ?_
      · exact Work.EKLComp.V_mono hscale hgV
      · rw [← aPrime_one_iterate c m x]; exact hmK
      · exact hret
    -- the `fmax` of the displacement vanishes
    have hf0 : fmax a b c g = 0 := by
      by_contra hfne
      have hfnn : 0 ≤ fmax a b c g := by
        simp only [fmax]; positivity
      have hfpos : 0 < fmax a b c g := lt_of_le_of_ne hfnn (Ne.symm hfne)
      obtain ⟨k, hk⟩ : ∃ k : ℕ, (1 : ℝ) / ((k : ℝ) + 1) ≤ fmax a b c g := by
        obtain ⟨j, hj⟩ := exists_nat_ge (1 / fmax a b c g)
        refine ⟨j, ?_⟩
        have h1 : (1 : ℝ) ≤ (j : ℝ) * fmax a b c g := by
          have h2 : (1 : ℝ) / fmax a b c g * fmax a b c g ≤ (j : ℝ) * fmax a b c g :=
            mul_le_mul_of_nonneg_right hj (le_of_lt hfpos)
          rwa [div_mul_cancel₀ _ (ne_of_gt hfpos)] at h2
        rw [div_le_iff₀ (show (0 : ℝ) < ((j : ℝ) + 1) by positivity)]
        nlinarith [h1, hfpos, Nat.cast_nonneg (α := ℝ) j]
      have hmem : x ∈ Bad a b c hab ℓ ℓu m (((k : ℝ) + 1)⁻¹) := by
        refine ⟨hDinjK hxK, g, ?_, hgL, hret, ?_⟩
        · exact fun i j => le_of_lt (hgV i j)
        · simpa [one_div] using hk
      have hN : x ∈ ⋃ (ℓv' : ℕ) (n : ℕ) (k' : ℕ),
          Bad a b c hab (3 * (ℓv' + 1) + 1) (ℓv' + 1) n ((↑k' + 1)⁻¹) := by
        refine Set.mem_iUnion.mpr ⟨ℓv, Set.mem_iUnion.mpr ⟨m,
          Set.mem_iUnion.mpr ⟨k, ?_⟩⟩⟩
        simpa [← hℓu_def, ← hℓ] using hmem
      exact (Set.disjoint_left.mp hdisj hxK) hN
    -- contradiction via the endgame
    exact endgame hab hac hcb noDiag hmpos (by positivity) hhalf hgL
      (fun i j => le_of_lt (hgV i j)) hf0 hret

end

end Work.EKLNonExc
