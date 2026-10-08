import Mathlib
import Submission.Work.BG.CharBridge

namespace Work.BG

open OddOrder.RepresentationTheory

/-- **A character that moves some element has an irreducible constituent that moves it.**

If `θ` is a genuine character of a finite group `H` and `θ x ≠ θ 1`, then among the
irreducible constituents `μ` of `θ` (those with `⟨θ, μ⟩ ≠ 0`) there is one with `μ x ≠ μ 1`.

Indeed `θ = ∑_{μ ∈ Irr H} m_μ · μ` with `m_μ = ⟨θ, μ⟩ ∈ ℕ`
(`IsCharacter.exists_natFinsupp_eq_sum`).  If every irreducible constituent took the same
value at `x` and at `1`, evaluating this decomposition at `x` and at `1` would give
`θ x = θ 1`, contrary to hypothesis. -/
theorem existsConstituentNontrivial {H : Type} [Group H] [Finite H] [Fintype H]
    [Invertible (Nat.card H : ℂ)] (θ : OddOrder.RepresentationTheory.ClassFunction H ℂ)
    (hθ : OddOrder.RepresentationTheory.IsCharacter θ) (x : H) (hx : θ x ≠ θ 1) :
    ∃ μ : OddOrder.RepresentationTheory.ClassFunction H ℂ,
      OddOrder.RepresentationTheory.IsIrreducibleCharacter μ ∧
      OddOrder.RepresentationTheory.ClassFunction.inner θ μ ≠ 0 ∧ μ x ≠ μ 1 := by
  classical
  obtain ⟨m, hsupp, hsum, hcoeff⟩ := hθ.exists_natFinsupp_eq_sum
  -- Evaluation of a finite sum of class functions at a point.
  have hsum_apply : ∀ (y : H) (s : Finset (ClassFunction H ℂ))
      (F : ClassFunction H ℂ → ClassFunction H ℂ),
      (∑ a ∈ s, F a) y = ∑ a ∈ s, (F a) y := by
    intro y s F
    induction s using Finset.cons_induction with
    | empty => simp
    | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, ClassFunction.add_apply, ih]
  -- The value of `θ` as the evaluated `ℕ`-decomposition.
  have hval : ∀ y : H, θ y = ∑ a ∈ m.support, (m a : ℂ) * (a y) := by
    intro y
    rw [hsum, hsum_apply y m.support (fun a => (m a : ℂ) • a)]
    exact Finset.sum_congr rfl fun a _ => ClassFunction.smul_apply _ _ _
  -- Some irreducible constituent does not take the same value at `x` as at `1`.
  have hex : ∃ μ ∈ m.support, μ x ≠ μ 1 := by
    by_contra h
    apply hx
    rw [hval x, hval 1]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hax : a x = a 1 := by
      by_contra hne
      exact h ⟨a, ha, hne⟩
    rw [hax]
  obtain ⟨μ, hμS, hμx⟩ := hex
  have hμirr : IsIrreducibleCharacter μ := hsupp (Finset.mem_coe.mpr hμS)
  refine ⟨μ, hμirr, ?_, hμx⟩
  -- The multiplicity of `μ` is the Fourier coefficient `⟨θ, μ⟩`, and it is nonzero on the
  -- support.
  have hinner : ClassFunction.inner θ μ = (m μ : ℂ) := (hcoeff μ hμirr).symm
  rw [hinner]
  exact_mod_cast (Finsupp.mem_support_iff.mp hμS)

end Work.BG
