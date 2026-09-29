import Mathlib
import Submission.Work.TMC16Core.Core.uni_res5_aux

set_option linter.unusedVariables false

namespace Work.TMC16Core.Core

open Work.TMC16Core

noncomputable section

/-- Elementary block/interval counting for the resonant windows.

* `J1resG h = [-h, h-1]` has `2h` points;
* `J2resG qn h ℓ = [(ℓ-1)qn+h, (ℓ+1)qn-h-1]` has `2qn-2h` points whenever `h ≤ qn`;
* the two windows are disjoint for `ℓ ≥ 1`, so `resW` has `2qn` points;
* `resK qn h` splits as the two `q`-blocks `resB1 ∪ resB2` (disjoint, each of `qn` points). -/
theorem res_card {qn h ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hh : 3 * qn / 5 ≤ h) (hh' : h ≤ 5 * qn / 8) :
    (Work.TMC16Core.Core.J1resG h).card = 2 * h ∧
    (Work.TMC16Core.Core.J2resG qn h ℓ).card = 2 * qn - 2 * h ∧
    (Work.TMC16Core.Core.resW qn h ℓ).card = 2 * qn ∧
    Work.TMC16Core.Core.resK qn h = Work.TMC16Core.Core.resB1 qn h ∪ Work.TMC16Core.Core.resB2 qn h ∧
    Disjoint (Work.TMC16Core.Core.resB1 qn h) (Work.TMC16Core.Core.resB2 qn h) ∧
    (Work.TMC16Core.Core.resB1 qn h).card = qn ∧
    (Work.TMC16Core.Core.resB2 qn h).card = qn := by
  -- `h ≤ qn`, so that the second window is not truncated as a natural number.
  have hqn : h ≤ qn := by omega
  -- The first window `[-h, h-1]` has `2h` points.
  have hcard1 : (J1resG h).card = 2 * h := by
    rw [J1resG, Int.card_Icc]
    have e : ((h : ℤ) - 1 + 1 - (-(h : ℤ))) = (2 * h : ℕ) := by push_cast; ring
    rw [e, Int.toNat_natCast]
  -- The second window `[(ℓ-1)qn+h, (ℓ+1)qn-h-1]` has `2qn-2h` points.
  have hcard2 : (J2resG qn h ℓ).card = 2 * qn - 2 * h := by
    rw [J2resG, Int.card_Icc]
    have e : (((ℓ : ℤ) + 1) * (qn : ℤ) - (h : ℤ) - 1 + 1 -
        (((ℓ : ℤ) - 1) * (qn : ℤ) + (h : ℤ))) = 2 * ((qn : ℤ) - (h : ℤ)) := by ring
    rw [e]
    have e2 : 2 * ((qn : ℤ) - (h : ℤ)) = ((2 * (qn - h) : ℕ) : ℤ) := by
      rw [Nat.cast_mul, Nat.cast_sub hqn]; push_cast; ring
    rw [e2, Int.toNat_natCast]
    omega
  -- The two windows are disjoint for `ℓ ≥ 1`.
  have hdisj12 : Disjoint (J1resG h) (J2resG qn h ℓ) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [J1resG, Finset.mem_Icc] at hx1
    rw [J2resG, Finset.mem_Icc] at hx2
    obtain ⟨h1, h2⟩ := hx1
    obtain ⟨h3, h4⟩ := hx2
    have hmul : 0 ≤ ((ℓ : ℤ) - 1) * (qn : ℤ) :=
      mul_nonneg (by omega) (by positivity)
    omega
  -- Hence `resW` has `2h + (2qn-2h) = 2qn` points.
  have hcardW : (resW qn h ℓ).card = 2 * qn := by
    rw [resW, Finset.card_union_of_disjoint hdisj12, hcard1, hcard2]
    omega
  -- `resK` splits as the two adjacent `q`-blocks.
  have hK : resK qn h = resB1 qn h ∪ resB2 qn h := by
    ext x
    simp only [resK, resB1, resB2, Finset.mem_union, Finset.mem_Icc]
    constructor
    · rintro ⟨h1, h2⟩
      by_cases hb : x ≤ (qn : ℤ) - (h : ℤ) - 1
      · exact Or.inl ⟨h1, hb⟩
      · rw [not_le] at hb
        exact Or.inr ⟨by omega, by omega⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨h1, by omega⟩
      · exact ⟨by omega, h2⟩
  -- The two blocks are disjoint.
  have hdisjB : Disjoint (resB1 qn h) (resB2 qn h) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    simp only [resB1, Finset.mem_Icc] at hx1
    simp only [resB2, Finset.mem_Icc] at hx2
    omega
  -- Each block has `qn` points.
  have hcardB1 : (resB1 qn h).card = qn := by
    rw [resB1, Int.card_Icc]
    have e : ((qn : ℤ) - (h : ℤ) - 1 + 1 - (-(h : ℤ))) = (qn : ℕ) := by ring
    rw [e, Int.toNat_natCast]
  have hcardB2 : (resB2 qn h).card = qn := by
    rw [resB2, Int.card_Icc]
    have e : (2 * (qn : ℤ) - (h : ℤ) - 1 + 1 - ((qn : ℤ) - (h : ℤ))) = (qn : ℕ) := by ring
    rw [e, Int.toNat_natCast]
  exact ⟨hcard1, hcard2, hcardW, hK, hdisjB, hcardB1, hcardB2⟩

end

end Work.TMC16Core.Core
