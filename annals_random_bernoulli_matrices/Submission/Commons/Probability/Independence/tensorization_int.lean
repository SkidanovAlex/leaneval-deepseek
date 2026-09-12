import Mathlib.MeasureTheory.Measure.Real
import Submission.Commons.Nat.Choose.tail_choose_pow_le
import Submission.Commons.Nat.Choose.sum_powersetCard_pow
import Submission.Commons.Nat.Choose.sum_subtype_card_le_powersetCard
import Submission.Commons.Nat.Card.big_coords_le
import Submission.Commons.Measure.Independence.iIndepFun_meas_notMem_le_pow
import Submission.Commons.Measure.Independence.measure_iUnion_fintype_le_sum

namespace Commons.Probability.Independence

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped BigOperators

/-- Integer form of part (2) of the tensorization lemma (Tikhomirov 2020, Lemma 2.2(2)).

Let `ξ : Fin m → Ω → ℝ` be a family of mutually independent real random variables on the
probability space `(Ω, P)` (in the sense of `iIndepFun ξ P`), each satisfying the small-ball
bound `P.real {x | |ξ i x| ≤ η} ≤ τ` for real numbers `η ≥ 0` and `τ ∈ [0,1]`.  Then for any
integer `r` with `1 ≤ r ≤ m`,

`P.real {x | (∑ i : Fin m, (ξ i x)^2) ≤ η^2·r} ≤ (e·m/r)^r · τ^(m−r)`.

(Equivalently: the probability that `‖ξ x‖₂ ≤ η·√r` is at most `(e·m/r)^r·τ^(m−r)`.) -/
theorem tensorization_int {m r : ℕ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P] {ξ : Fin m → Ω → ℝ} (hξ : iIndepFun ξ P)
    {η τ : ℝ} (hη0 : 0 ≤ η) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hr : 0 < r) (hrm : r ≤ m)
    (hsmall : ∀ i : Fin m, P.real {x | |ξ i x| ≤ η} ≤ τ) :
    P.real {x | (∑ i : Fin m, (ξ i x) ^ 2) ≤ η ^ 2 * (r : ℝ)} ≤
      (Real.exp 1 * (m : ℝ) / (r : ℝ)) ^ r * τ ^ (m - r) := by
  classical
  let S : Set Ω := {x | (∑ i : Fin m, (ξ i x) ^ 2) ≤ η ^ 2 * (r : ℝ)}
  let E : Finset (Fin m) → Set Ω := fun B => {x | ∀ i : Fin m, i ∉ B → |ξ i x| ≤ η}
  let U : Set Ω := ⋃ B : {B : Finset (Fin m) // B.card ≤ r}, E (B : Finset (Fin m))
  change P.real S ≤ (Real.exp 1 * (m : ℝ) / (r : ℝ)) ^ r * τ ^ (m - r)

  -- The small-ball event for the complement of each ``B``, bounded in real numbers.
  have hE_real : ∀ B : Finset (Fin m),
      P.real (E B) ≤ τ ^ (m - B.card) := by
    intro B
    let τe : ℝ≥0∞ := ENNReal.ofReal τ
    have hτe0 : (0 : ℝ≥0∞) ≤ τe := zero_le
    have hτe1 : τe ≤ (1 : ℝ≥0∞) := by
      dsimp [τe]
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal hτ1
    have hsmall_e : ∀ i : Fin m, P {x | |ξ i x| ≤ η} ≤ τe := by
      intro i
      have hfin : P {x | |ξ i x| ≤ η} ≠ ∞ := by finiteness
      calc
        P {x | |ξ i x| ≤ η} = ENNReal.ofReal (P.real {x | |ξ i x| ≤ η}) := by
          exact (ofReal_measureReal (μ := P) (s := {x | |ξ i x| ≤ η}) (h := hfin)).symm
        _ ≤ τe := by
          dsimp [τe]
          exact ENNReal.ofReal_le_ofReal (hsmall i)
    have hE_enn : P (E B) ≤ τe ^ (m - B.card) := by
      dsimp [E]
      exact Commons.Measure.Independence.iIndepFun_meas_notMem_le_pow P hξ B τe hsmall_e
    have hpow_ne_top : τe ^ (m - B.card) ≠ ∞ := by
      have hle : τe ^ (m - B.card) ≤ (1 : ℝ≥0∞) := by
        exact pow_le_one₀ hτe0 hτe1
      exact ne_top_of_le_ne_top (by norm_num : (1 : ℝ≥0∞) ≠ ∞) hle
    have hto : P.real (E B) ≤ (τe ^ (m - B.card)).toReal := by
      simpa [measureReal_def] using
        (ENNReal.toReal_mono (a := P (E B)) (b := τe ^ (m - B.card)) hpow_ne_top hE_enn)
    calc
      P.real (E B) ≤ (τe ^ (m - B.card)).toReal := hto
      _ = τ ^ (m - B.card) := by
        rw [ENNReal.toReal_pow]
        rw [ENNReal.toReal_ofReal hτ0]

  -- S is covered by the union of the complement events over all small B.
  have hSU : S ⊆ U := by
    intro x hx
    dsimp [S] at hx
    let B : Finset (Fin m) := (Finset.univ : Finset (Fin m)).filter (fun i : Fin m => η < |ξ i x|)
    have hBcard : B.card ≤ r := by
      simpa [B] using
        (Commons.Nat.Card.big_coords_le (m := m) (r := r) (v := fun i : Fin m => ξ i x)
          (η := η) hη0 hx)
    have hmem : x ∈ E B := by
      dsimp [E]
      intro i hiB
      have hnot : ¬ η < |ξ i x| := by
        intro hlt
        exact hiB (by simp [B, hlt])
      exact le_of_not_gt hnot
    dsimp [U]
    exact Set.mem_iUnion.mpr ⟨⟨B, hBcard⟩, hmem⟩

  -- Union bound (real-valued) and the per-set bounds.
  have hmono : P.real S ≤ P.real U := by
    exact measureReal_mono hSU
  have hUU : P.real U ≤
      ∑ B : {B : Finset (Fin m) // B.card ≤ r}, P.real (E (B : Finset (Fin m))) := by
    simpa [U] using
      (measureReal_iUnion_fintype_le (μ := P)
        (f := fun B : {B : Finset (Fin m) // B.card ≤ r} => E (B : Finset (Fin m))))
  have hsum : (∑ B : {B : Finset (Fin m) // B.card ≤ r}, P.real (E (B : Finset (Fin m)))) ≤
      ∑ B : {B : Finset (Fin m) // B.card ≤ r}, τ ^ (m - (B : Finset (Fin m)).card) := by
    exact Finset.sum_le_sum (fun B _ => hE_real (B : Finset (Fin m)))

  -- Combinatorial part.
  have hcomb : (∑ B : {B : Finset (Fin m) // B.card ≤ r}, τ ^ (m - (B : Finset (Fin m)).card)) ≤
      (Real.exp 1 * (m : ℝ) / (r : ℝ)) ^ r * τ ^ (m - r) := by
    calc
      (∑ B : {B : Finset (Fin m) // B.card ≤ r}, τ ^ (m - (B : Finset (Fin m)).card))
          = ∑ ℓ ∈ Finset.range (r + 1),
              ∑ B ∈ (Finset.univ : Finset (Fin m)).powersetCard ℓ, τ ^ (m - B.card) := by
            exact Commons.Nat.Choose.sum_subtype_card_le_powersetCard τ
      _ = ∑ ℓ ∈ Finset.range (r + 1), (m.choose ℓ : ℝ) * τ ^ (m - ℓ) := by
            exact Commons.Nat.Choose.sum_powersetCard_pow τ
      _ ≤ (Real.exp 1 * (m : ℝ) / (r : ℝ)) ^ r * τ ^ (m - r) := by
            exact Commons.Nat.Choose.tail_choose_pow_le hr hrm hτ0 hτ1

  exact hmono.trans (hUU.trans (hsum.trans hcomb))

end Commons.Probability.Independence