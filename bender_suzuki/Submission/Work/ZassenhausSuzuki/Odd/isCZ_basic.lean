import Mathlib
import Submission.Work.ZassenhausSuzuki.Odd.OddDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.Odd

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}

theorem isCZ_basic (h : Work.ZassenhausSuzuki.Odd.SzOddHyp H Q t)
    {A : Subgroup G} (hA : Work.ZassenhausSuzuki.Odd.IsCZ A) :
    IsMulCommutative ↥A ∧ Odd (Nat.card ↥A) ∧
      ∀ a ∈ A, a ≠ 1 →
        Work.ZassenhausSuzuki.IsStronglyReal a ∧ Subgroup.centralizer ({a} : Set G) = A := by
  obtain ⟨x, hsr, _hx1, hx2, hAx⟩ := hA
  have hmain := Work.ZassenhausSuzuki.centralizer_abelian_of_strongly_real
      h.hsplit h.hzass h.h2 hx2 hsr
  exact ⟨by rw [← hAx]; exact hmain.1,
    by rw [← hAx]; exact hmain.2.1,
    fun a ha ha1 => by
      rw [← hAx] at ha ⊢
      exact hmain.2.2 a ha ha1⟩

end Work.ZassenhausSuzuki.Odd
