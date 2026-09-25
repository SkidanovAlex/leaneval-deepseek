import Mathlib
import Submission.Work.CFT.ShafarevichCore.Reduction
import Submission.Work.Tower.Shafarevich.Estimate

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The cutting of the Frobenius elements at a splitting set `T`

`Work.Tower.Shafarevich.H2Estimate` is stated for a finite level `K/F` of the class field tower
which is **maximal among the everywhere-unramified `3`-extensions in which a set `T` of primes
splits completely**, and the estimate carries the extra term `+ |T|`.  The mechanism is that `K` is
the quotient of the maximal everywhere-unramified pro-`3` group `G` of `F` by the (closed) normal
closure of the Frobenius elements at the primes of `T`, that those Frobenius elements lie in the
Frattini subgroup of `G` (this is exactly `IsFrobeniusTrivialInFrattini`, see
`Submission/Work/Tower/Shafarevich/Defs.lean`), and that killing `k` Frattini generators raises the
relation rank by at most `k` (Koch's transfer,
`Work.CFT.Kummer.finrank_H2Fp_quotient_le`).

Here the cutting is recorded as the named hypothesis `Work.CFT.ShafarevichCore.SplittingCut`,
which is the `∃ N` part of `Work.CFT.Kummer.UnramifiedPresentation`; the group-theoretic transfer
*from* the cutting data to the estimate is proved (sorry-free) in
`Submission/Work/CFT/ShafarevichCore/Target.lean`.

## Main definition

* `Work.CFT.ShafarevichCore.SplittingCut F G` — the cutting data at a splitting set `T`.
-/

open NumberField
open scoped Classical nonZeroDivisors

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Work.CFT.ShafarevichCore

/-- **The cutting data for the splitting set `T`.**  The abstract group `G` models the maximal
everywhere-unramified pro-`3` group `Gal(F_∅(3)/F)` of `F`, and *every* finite everywhere-unramified
Galois `3`-extension `K/F` which is maximal for complete splitting of a set `T` of primes with
trivial Frattini Frobenius class arises as `Gal(K/F) ≃* G ⧸ N` where `N` is the normal closure of at
most `|T|` elements, whose killing does not change the generator rank.

The group-theoretic facts behind this (`G` is the maximal group, the Frobenius classes of the
primes of `T` lie in `Φ(G)`, and killing Frattini generators preserves the generator rank) are the
content of `Work.Tower.Shafarevich` and `Work.CFT.Kummer`; the identification
`Gal(K/F) ≃* G ⧸ N` is the Galois correspondence for the maximal everywhere-unramified
pro-`3` extension. -/
def SplittingCut (F : Type*) [Field F] [NumberField F] (G : Type) [Group G] : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K],
    Work.Tower.IsUnramifiedExtension F K → IsPGroup 3 (Gal(K/F)) →
    ∀ (T : Finset (Ideal (𝓞 F))),
      Work.Tower.Shafarevich.IsFrobeniusTrivialInFrattini F T →
      Work.Tower.Shafarevich.IsMaximalSplittingExtension F K T →
      ∃ (N : Subgroup G) (_ : N.Normal) (k : ℕ) (g : Fin k → G), k ≤ T.card ∧
        N = Subgroup.normalClosure (Set.range g) ∧
        Module.finrank (ZMod 3) (H1Fp 3 (G ⧸ N)) = Module.finrank (ZMod 3) (H1Fp 3 G) ∧
        Nonempty (G ⧸ N ≃* Gal(K/F))

/-- The cutting data at `T = ∅`: a maximal everywhere-unramified `3`-extension of `F` is a
quotient of the maximal group by a normal closure of `|∅| = 0` elements, i.e. it *is* the maximal
group. -/
theorem SplittingCut.empty (F : Type*) [Field F] [NumberField F] {G : Type} [Group G]
    (h : SplittingCut F G) :
    ∀ (K : Type) [Field K] [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K],
      Work.Tower.IsUnramifiedExtension F K → IsPGroup 3 (Gal(K/F)) →
      Work.Tower.Shafarevich.IsMaximalSplittingExtension F K ∅ →
      Nonempty (Gal(K/F) ≃* G) := by
  intro K _ _ _ _ _ hKur h3 hmax
  obtain ⟨N, hN, k, g, hk, hNg, _hgen, ⟨e⟩⟩ :=
    h K hKur h3 ∅ (by intro 𝔭 hmem; simp at hmem) hmax
  rw [Finset.card_empty] at hk
  obtain rfl : k = 0 := Nat.eq_zero_of_le_zero hk
  rw [Set.range_eq_empty g, Subgroup.normalClosure_empty] at hNg
  subst hNg
  exact ⟨e.symm.trans QuotientGroup.quotientBot⟩

end Work.CFT.ShafarevichCore
