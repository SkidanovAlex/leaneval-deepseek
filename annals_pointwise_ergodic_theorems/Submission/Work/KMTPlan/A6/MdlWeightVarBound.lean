import Mathlib
import Submission.Work.KMTPlan.A6.MdlCoreIndexMonotone
import Submission.Work.KMTPlan.A6.MdlWeightMonoBoundSelf

set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

/-! ## Elementary helpers -/

/-- A `Λ`-lacunary sequence with `Λ > 1` has monotone floors.  `Lacunary Λ a` says
`a (n+1) / a n > Λ`; in `ℝ≥0`, `a n = 0` would force `a (n+1) / a n = 0 > Λ`, impossible.  Hence
`a n > 0` and `a (n+1) > Λ * a n ≥ a n`, so `a` and therefore `⌊a ·⌋` are monotone. -/
lemma floor_monotone_of_lacunary {Λ : NNReal} {a : ℕ → NNReal} (hΛ : 1 < Λ)
    (ha : PointwiseErgodicTheorems.Lacunary Λ a) :
    Monotone fun n => Nat.floor (a n) := by
  have hpos : ∀ n, 0 < a n := by
    intro n
    rcases eq_zero_or_pos (a n) with h0 | hp
    · exfalso
      have h1 := ha n
      rw [h0, div_zero] at h1
      exact absurd h1 (not_lt.mpr (le_of_lt (lt_trans zero_lt_one hΛ)))
    · exact hp
  have hstep : ∀ n, a n ≤ a (n + 1) := by
    intro n
    have h1 : Λ * a n < a (n + 1) := (lt_div_iff₀ (hpos n)).mp (ha n)
    have h2 : a n ≤ Λ * a n := by
      calc a n = 1 * a n := (one_mul _).symm
        _ ≤ Λ * a n := mul_le_mul_of_nonneg_right (le_of_lt hΛ) (le_of_lt (hpos n))
    exact le_of_lt (lt_of_le_of_lt h2 h1)
  exact Nat.floor_mono.comp (NNReal.coe_mono.comp (monotone_nat_of_le_succ hstep))

/-- The `r`-variational norm of the zero sequence vanishes (`r ≥ 1`). -/
lemma variationalNorm_zero_nat {r : NNReal} (hr : 1 ≤ r) :
    PointwiseErgodicTheorems.variationalNorm r (0 : ℕ → ℂ) = 0 := by
  have h := Submission.PointwiseErgodicTheorems.variationalNorm_smul (r := r) hr (0 : ℂ)
    (0 : ℕ → ℂ)
  simpa using h

/-- `3 * ENNReal.ofReal C = ENNReal.ofReal (3 * C)`. -/
lemma three_mul_ofReal (C : ℝ) :
    (3 : ℝ≥0∞) * ENNReal.ofReal C = ENNReal.ofReal (3 * C) := by
  rw [show (3 : ℝ≥0∞) = ENNReal.ofReal (3 : ℝ) from (ENNReal.ofReal_natCast 3).symm,
    ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 3 by norm_num)]

/-- **Masking by an upward-closed set.**  If `p` is the tail `{n | n₀ ≤ n}`, then the variational
norm of `if p n then x n else 0` is at most `3` times that of the shifted sequence
`m ↦ x (m + n₀)`.  (The factor `3` is exactly `variationalNorm_prependZeros_le`.) -/
lemma masked_le_tail {r : NNReal} (hr : 1 ≤ r) {p : ℕ → Prop} [DecidablePred p] (n₀ : ℕ)
    (hp : ∀ n, p n ↔ n₀ ≤ n) (x : ℕ → ℂ) {C : ℝ}
    (hb : PointwiseErgodicTheorems.variationalNorm r (fun m => x (m + n₀))
      ≤ ENNReal.ofReal C) :
    PointwiseErgodicTheorems.variationalNorm r (fun n => if p n then x n else 0)
      ≤ ENNReal.ofReal (3 * C) := by
  have heq : (fun n : ℕ => if p n then x n else 0)
      = fun n : ℕ => if n < n₀ then (0 : ℂ) else x ((n - n₀) + n₀) := by
    funext n
    by_cases hn : n < n₀
    · have hnp : ¬ p n := fun h => absurd ((hp n).mp h) (not_le.mpr hn)
      rw [if_neg hnp, if_pos hn]
    · have hnp : p n := (hp n).mpr (le_of_not_gt hn)
      rw [if_pos hnp, if_neg hn, Nat.sub_add_cancel (le_of_not_gt hn)]
  rw [heq]
  refine (Submission.PointwiseErgodicTheorems.variationalNorm_prependZeros_le hr n₀
    (fun m => x (m + n₀))).trans ?_
  refine (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ≥0∞) ≤ 3)).trans ?_
  exact le_of_eq (three_mul_ofReal C)

/-! ## The target -/

theorem MdlWeightVarBound (P : Polynomial ℤ) (hdeg : 1 ≤ P.natDegree) (r : NNReal) (hr : 1 ≤ r) :
    ∃ B : ℝ, 0 < B ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (ρ : ℝ) (C₀ : ℕ) (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a →
        (∀ n : ℕ, Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n →
          B ≤ ((Nat.floor (a n) : ℕ) : ℝ)) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 →
        PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
              then Work.KMTPlan.A6.mdlW1 P (Nat.floor (a n)) t else 0) ≤ ENNReal.ofReal C ∧
        PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
              then Work.KMTPlan.A6.mdlW2 P (Nat.floor (a n)) t else 0) ≤ ENNReal.ofReal C ∧
        PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
              then Work.KMTPlan.A6.mdlW3 P (Nat.floor (a n)) t else 0) ≤ ENNReal.ofReal C := by
  obtain ⟨B₀, hB₀pos, C', hC'pos, hbound⟩ := MdlWeightMonoBoundSelf P hdeg r hr
  have hB₀posR : (0 : ℝ) < (B₀ : ℝ) := by exact_mod_cast hB₀pos
  refine ⟨(B₀ : ℝ), hB₀posR, 3 * C', mul_pos (by norm_num) hC'pos, ?_⟩
  intro ρ C₀ a Λ l₁ l₂ k₁ k₂ t hΛ hlac hcore ht
  have hmono : Monotone fun n => Nat.floor (a n) := floor_monotone_of_lacunary hΛ hlac
  by_cases hex : ∃ n, Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · set n₀ : ℕ := Nat.find hex with hn₀def
    have hcore₀ : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n₀ := Nat.find_spec hex
    have hiff : ∀ n, Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n ↔ n₀ ≤ n := fun n =>
      ⟨fun h => Nat.find_min' hex h, fun h =>
        MdlCoreIndexMonotone ρ C₀ a Λ l₁ l₂ k₁ k₂ hΛ hlac h hcore₀⟩
    have hmonoTail : Monotone fun m => Nat.floor (a (m + n₀)) :=
      hmono.comp (fun m k hmk => Nat.add_le_add_right hmk n₀)
    have hbig : ∀ m : ℕ, B₀ ≤ Nat.floor (a (m + n₀)) := fun m => by
      have h1 : Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ (m + n₀) :=
        MdlCoreIndexMonotone ρ C₀ a Λ l₁ l₂ k₁ k₂ hΛ hlac (Nat.le_add_left n₀ m) hcore₀
      have h2 : (B₀ : ℝ) ≤ ((Nat.floor (a (m + n₀)) : ℕ) : ℝ) := hcore (m + n₀) h1
      exact_mod_cast h2
    obtain ⟨hb1, hb2, hb3⟩ :=
      hbound (fun m => Nat.floor (a (m + n₀))) t hmonoTail hbig ht
    exact ⟨masked_le_tail hr n₀ hiff (fun n => Work.KMTPlan.A6.mdlW1 P (Nat.floor (a n)) t) hb1,
      masked_le_tail hr n₀ hiff (fun n => Work.KMTPlan.A6.mdlW2 P (Nat.floor (a n)) t) hb2,
      masked_le_tail hr n₀ hiff (fun n => Work.KMTPlan.A6.mdlW3 P (Nat.floor (a n)) t) hb3⟩
  · have hmask1 : (fun n : ℕ => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
        then Work.KMTPlan.A6.mdlW1 P (Nat.floor (a n)) t else 0) = (0 : ℕ → ℂ) := by
      funext n
      exact if_neg (fun h => hex ⟨n, h⟩)
    have hmask2 : (fun n : ℕ => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
        then Work.KMTPlan.A6.mdlW2 P (Nat.floor (a n)) t else 0) = (0 : ℕ → ℂ) := by
      funext n
      exact if_neg (fun h => hex ⟨n, h⟩)
    have hmask3 : (fun n : ℕ => if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
        then Work.KMTPlan.A6.mdlW3 P (Nat.floor (a n)) t else 0) = (0 : ℕ → ℂ) := by
      funext n
      exact if_neg (fun h => hex ⟨n, h⟩)
    rw [hmask1, hmask2, hmask3, variationalNorm_zero_nat hr]
    exact ⟨bot_le, bot_le, bot_le⟩

end

end Work.KMTPlan.A6
