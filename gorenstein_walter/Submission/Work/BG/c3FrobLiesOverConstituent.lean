import Mathlib
import Submission.Work.BG._c3frob_probe
import Submission.OddOrder.GroupTheory.RepresentationTheory.InducedCharacter

namespace Work.BG

open OddOrder.RepresentationTheory

/-- The restriction `Res^G_H φ` of a genuine character is a genuine character: the
witnessing representation `ρ` restricts to `ρ.comp H.subtype`. -/
theorem isCharacter_restrict_of_isCharacter {G : Type*} [Group G] {φ : ClassFunction G ℂ}
    (hφ : IsCharacter φ) (H : Subgroup G) :
    IsCharacter (ClassFunction.restrict H φ) := by
  obtain ⟨V, _, _, _, ρ, hρ⟩ := hφ
  have hφeq : φ = repCharacterClassFunction ρ := ClassFunction.ext fun g => by
    rw [repCharacterClassFunction_apply]; exact congrFun hρ g
  rw [hφeq, ClassFunction.restrict_repCharacterClassFunction H ρ]
  exact repCharacterClassFunction_isCharacter (ρ.comp H.subtype)

/-- **A character that moves some element has an irreducible constituent that moves it.**

If `θ` is a genuine character of a finite group `H` and `θ x ≠ θ 1`, then among the
irreducible constituents `μ` of `θ` (those with `⟨θ, μ⟩ ≠ 0`) there is one with `μ x ≠ μ 1`.

Indeed `θ = ∑_{μ ∈ Irr H} m_μ · μ` with `m_μ = ⟨θ, μ⟩ ∈ ℕ`
(`IsCharacter.exists_natFinsupp_eq_sum`).  If every irreducible constituent took the same
value at `x` and at `1`, evaluating this decomposition at `x` and at `1` would give
`θ x = θ 1`, contrary to hypothesis. -/
theorem exists_irreducible_constituent_ne_one {H : Type} [Group H] [Finite H] [Fintype H]
    [Invertible (Nat.card H : ℂ)] (θ : ClassFunction H ℂ)
    (hθ : IsCharacter θ) (x : H) (hx : θ x ≠ θ 1) :
    ∃ μ : ClassFunction H ℂ, IsIrreducibleCharacter μ ∧
      ClassFunction.inner θ μ ≠ 0 ∧ μ x ≠ μ 1 := by
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
    have haeq : a x = a 1 := by
      by_contra hne
      exact h ⟨a, ha, hne⟩
    rw [haeq]
  obtain ⟨μ, hμS, hμx⟩ := hex
  have hμirr : IsIrreducibleCharacter μ := hsupp (Finset.mem_coe.mpr hμS)
  refine ⟨μ, hμirr, ?_, hμx⟩
  -- The multiplicity of `μ` is the Fourier coefficient `⟨θ, μ⟩`, and it is nonzero on the
  -- support.
  rw [← hcoeff μ hμirr]
  exact_mod_cast Finsupp.mem_support_iff.mp hμS

/-- **A nontrivial irreducible character of `Y` has an irreducible constituent on a normal
subgroup `H` that is itself nontrivial on a normal subgroup `N ≤ H`.**

The restriction `R = Res^Y_H χ` is a genuine character of `H` and `R ⟨n, _⟩ ≠ R 1` for the
given `n ∈ N ⊆ H`, so `exists_irreducible_constituent_ne_one` produces an irreducible
constituent `μ` of `R` with `μ ⟨n, _⟩ ≠ μ 1`.  Packaging `μ` as an irreducible character `θ`
of `H` gives a character lying over `χ` (its multiplicity in `R` is nonzero) and nontrivial
on `N`. -/
theorem c3FrobLiesOverConstituent {Y : Type} [Group Y] [Finite Y] [Fintype Y]
    [Invertible (Nat.card Y : ℂ)] (H N : Subgroup Y) [H.Normal] (hN : N ≤ H)
    [Fintype ↥H] [Invertible (Nat.card ↥H : ℂ)]
    (χ : OddOrder.RepresentationTheory.IrreducibleCharacter Y)
    (hker : ∃ n : Y, n ∈ N ∧ (χ : OddOrder.RepresentationTheory.ClassFunction Y ℂ) n ≠
      (χ : OddOrder.RepresentationTheory.ClassFunction Y ℂ) 1) :
    ∃ θ : OddOrder.RepresentationTheory.IrreducibleCharacter ↥H,
      OddOrder.RepresentationTheory.IrreducibleCharacter.LiesOver H χ θ ∧
      ∃ m : ↥H, (m : Y) ∈ N ∧
        (θ : OddOrder.RepresentationTheory.ClassFunction ↥H ℂ) m ≠
          (θ : OddOrder.RepresentationTheory.ClassFunction ↥H ℂ) 1 := by
  classical
  obtain ⟨n, hnN, hnval⟩ := hker
  -- The restriction `R = Res^Y_H χ` is a genuine character of `H`, and its value at
  -- `⟨n, _⟩` differs from its value at `1` because these are `χ n` and `χ 1`.
  have hRchar : IsCharacter (ClassFunction.restrict H (χ : ClassFunction Y ℂ)) :=
    isCharacter_restrict_of_isCharacter χ.isIrreducible.isCharacter H
  have hRval : ClassFunction.restrict H (χ : ClassFunction Y ℂ) ⟨n, hN hnN⟩ ≠
      ClassFunction.restrict H (χ : ClassFunction Y ℂ) 1 := by
    simpa using hnval
  obtain ⟨μ, hμirr, hμinner, hμval⟩ :=
    exists_irreducible_constituent_ne_one (ClassFunction.restrict H (χ : ClassFunction Y ℂ))
      hRchar ⟨n, hN hnN⟩ hRval
  refine ⟨⟨μ, hμirr⟩, ?_, ⟨⟨n, hN hnN⟩, by simpa using hnN, ?_⟩⟩
  · -- `μ` occurs in `Res^Y_H χ` with nonzero multiplicity, i.e. `χ` lies over it.
    show ClassFunction.restrictionMultiplicity H (χ : ClassFunction Y ℂ) μ ≠ 0
    rw [ClassFunction.restrictionMultiplicity_def]
    exact hμinner
  · -- `(⟨μ, _⟩ : IrreducibleCharacter ↥H) = μ` as a class function.
    simpa using hμval

end Work.BG
