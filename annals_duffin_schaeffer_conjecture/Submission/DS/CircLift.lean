import Submission.DS.CircAlign

open scoped Nat ENNReal NNReal
open Set Filter MeasureTheory
open DuffinSchaefferConjecture

/-!
# Limsup lift: `W ψ` on `(0,1)` is (a.e.) the preimage of `Eapprox ψ`

For `ψ` with all radii `ψ(q)/q ≤ 1/2`, the per-denominator ae-iff
(`ae_eq_approxAddOrderOf` + `ae_eq_approxAddOrderOf_radSeq`) holds for every `q`; the
finitely/countably many exceptional points per `q` form a countable null union.  Away
from that union, membership in `W ψ` (infinitely many `q` with `x ∈ Acopr ψ q`)
coincides with membership of `(x : AddCircle 1)` in `Eapprox ψ` (infinitely many `q`
with the class in the order-`q` set), via `mem_Eapprox_iff_pos`.

The bridge lemmas of `CircleBridge`/`CircAlign` provide all ingredients:
`W ψ = [0,1] ∩ limsupDenoms (Acopr ψ)`, `mem_Eapprox_iff_pos`, `ae_eq_approxAddOrderOf`.
-/

namespace Submission.DS

/-- The radius at the natural `q` equals the NNReal-coerced `ψ(q)/q`. -/
lemma radSeq_eq_coe (ψ : ℕ+ → ℝ≥0) (q : ℕ+) :
    radSeq ψ (q : ℕ) = ((ψ q / q : NNReal) : ℝ) := by
  simp [radSeq]
  exact congrArg ψ (Subtype.ext rfl)

/-- Per-`q` ae-iff in terms of `radSeq`. -/
lemma ae_eq_approxAddOrderOf_radSeq (ψ : ℕ+ → ℝ≥0) (q : ℕ+)
    (hδ : (ψ q / q : NNReal) ≤ (1 / 2 : NNReal)) :
    ∀ᵐ x ∂volume, x ∈ Set.Ioo (0 : ℝ) 1 →
      (x ∈ Acopr ψ q ↔ (x : AddCircle (1 : ℝ)) ∈
        approxAddOrderOf (AddCircle (1 : ℝ)) (q : ℕ) (radSeq ψ (q : ℕ))) := by
  rw [radSeq_eq_coe ψ q]
  exact ae_eq_approxAddOrderOf ψ q hδ

/-- Pointwise core: on `(0,1)`, membership in `W ψ` is per-`q` membership in `Acopr ψ q`
for infinitely many `q`, which (given the per-`q` iff for all `q`) is membership of the
circle class in `Eapprox ψ`. -/
lemma W_mem_iff_circle_mem_Eapprox {ψ : ℕ+ → ℝ≥0} (x : ℝ) (hxI : x ∈ Set.Ioo (0 : ℝ) 1)
    (hall : ∀ q : ℕ+, x ∈ Acopr ψ q ↔
        (x : AddCircle (1 : ℝ)) ∈
          approxAddOrderOf (AddCircle (1 : ℝ)) (q : ℕ) (radSeq ψ (q : ℕ))) :
    x ∈ W ψ ↔ (x : AddCircle (1 : ℝ)) ∈ Eapprox ψ := by
  have hxIcc : x ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hxI.1, le_of_lt hxI.2⟩
  have hS : {q : ℕ+ | x ∈ Acopr ψ q} = {q : ℕ+ |
      (x : AddCircle (1 : ℝ)) ∈
        approxAddOrderOf (AddCircle (1 : ℝ)) (q : ℕ) (radSeq ψ (q : ℕ))} := by
    ext q
    exact hall q
  rw [W]
  rw [Set.mem_inter_iff]
  simp [hxIcc, limsupDenoms]
  rw [hS]
  rw [mem_Eapprox_iff_pos]

/-- **Limsup lift**: for almost every `x ∈ (0,1)`, `x ∈ W ψ` iff its circle class lies in
`Eapprox ψ`. -/
lemma W_ae_eq_lift_Eapprox (ψ : ℕ+ → ℝ≥0) (hδ : ∀ q, (ψ q / q : NNReal) ≤ (1 / 2 : NNReal)) :
    ∀ᵐ x ∂volume, x ∈ Set.Ioo (0 : ℝ) 1 → (x ∈ W ψ ↔ (x : AddCircle (1 : ℝ)) ∈ Eapprox ψ) := by
  classical
  let I : Set ℝ := Set.Ioo (0 : ℝ) 1
  have hImeas : MeasurableSet I := by
    simp [I]
  -- Per-`q` ae iff, restricted to `I`
  have hq : ∀ q : ℕ+, ∀ᵐ x ∂(volume.restrict I),
      (x ∈ Acopr ψ q ↔ (x : AddCircle (1 : ℝ)) ∈
        approxAddOrderOf (AddCircle (1 : ℝ)) (q : ℕ) (radSeq ψ (q : ℕ))) := by
    intro q
    have hqae := ae_eq_approxAddOrderOf_radSeq ψ q (hδ q)
    exact (ae_restrict_iff' hImeas).mpr (by simpa [I] using hqae)
  -- all `q` simultaneously (countable)
  have hall : ∀ᵐ x ∂(volume.restrict I), ∀ q : ℕ+,
      (x ∈ Acopr ψ q ↔ (x : AddCircle (1 : ℝ)) ∈
        approxAddOrderOf (AddCircle (1 : ℝ)) (q : ℕ) (radSeq ψ (q : ℕ))) := by
    exact ae_all_iff.mpr hq
  -- `x ∈ I` almost everywhere under the restricted measure
  have hmem : ∀ᵐ x ∂(volume.restrict I), x ∈ I := ae_restrict_mem hImeas
  -- combine
  have hmain : ∀ᵐ x ∂(volume.restrict I), (x ∈ W ψ ↔ (x : AddCircle (1 : ℝ)) ∈ Eapprox ψ) := by
    filter_upwards [hall, hmem] with x hxall hxI
    exact W_mem_iff_circle_mem_Eapprox x (by simpa [I] using hxI) hxall
  exact (ae_restrict_iff' hImeas).mp hmain

end Submission.DS
