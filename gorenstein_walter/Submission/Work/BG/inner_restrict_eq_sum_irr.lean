import Mathlib
import Submission.Work.BG.lemma36Defs
import Submission.Work.BG.finsupp_sum_univ_eq_sum_support

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

/-- Restriction of a class function commutes with a finite `ℂ`-linear combination:
`Res^K_A (∑_{i ∈ s} c i • f i) = ∑_{i ∈ s} c i • Res^K_A (f i)`. -/
theorem restrict_finset_sum_smul {K : Type} [Group K] {ι : Type} (A : Subgroup K)
    (s : Finset ι) (c : ι → ℂ) (f : ι → ClassFunction K ℂ) :
    ClassFunction.restrict A (∑ i ∈ s, c i • f i) =
      ∑ i ∈ s, c i • ClassFunction.restrict A (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ClassFunction.restrict_add,
        ClassFunction.restrict_smul, ih]

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
/-- **Multiplicity expansion over `Irr K`.**  For a finite group `K`, a subgroup `A ≤ K`, a
genuine character `θ` of `K` and any class function `ψ` of `A`:
`⟨θ|_A, ψ⟩_A = Σ_{ν ∈ Irr K} ⟨θ, ν⟩_K · ⟨ν|_A, ψ⟩_A`.

Route: `IsCharacter.exists_natFinsupp_eq_sum` gives
`θ = ∑_{a ∈ m.support} (m a : ℂ) • a` with `m w = ⟨θ, w⟩` for irreducible `w` and
`↑m.support ⊆ irreducibleCharacters K`.  Reindex the `Finsupp` sum as a sum over
`IrreducibleCharacter K` (the coercion `IrreducibleCharacter K → ClassFunction K ℂ` is
injective; terms outside the support vanish because `m w = ⟨θ,w⟩ = 0` there), restrict along
`A` (`restrict_finset_sum_smul`) and use left-linearity of the pairing
(`inner_sum_left`, `ClassFunction.inner_smul_left`).  The reindexing itself is
`Work.BG.finsupp_sum_univ_eq_sum_support`. -/
theorem inner_restrict_eq_sum_irr {K : Type} [Group K] [Finite K] [Fintype K]
    [Invertible (Nat.card K : ℂ)] (A : Subgroup K) [Fintype ↥A]
    [Invertible (Nat.card ↥A : ℂ)] [Fintype (IrreducibleCharacter K)]
    {θ : ClassFunction K ℂ} (hθ : IsCharacter θ) (ψ : ClassFunction ↥A ℂ) :
    ClassFunction.inner (ClassFunction.restrict A θ) ψ =
      ∑ ν : IrreducibleCharacter K,
        ClassFunction.inner θ (ν : ClassFunction K ℂ) *
          ClassFunction.inner (ClassFunction.restrict A (ν : ClassFunction K ℂ)) ψ := by
  classical
  obtain ⟨m, hsupp, hsum, hcoeff⟩ := hθ.exists_natFinsupp_eq_sum
  -- `restrict A` of the `ℕ`-decomposition of `θ`.
  have hinner : ClassFunction.inner
      (∑ a ∈ m.support, (m a : ℂ) • ClassFunction.restrict A a) ψ
      = ∑ a ∈ m.support, (m a : ℂ) *
          ClassFunction.inner (ClassFunction.restrict A a) ψ := by
    rw [inner_sum_left]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [ClassFunction.inner_smul_left]
  have hL : ClassFunction.inner (ClassFunction.restrict A θ) ψ
      = ∑ a ∈ m.support, (m a : ℂ) *
          ClassFunction.inner (ClassFunction.restrict A a) ψ := by
    rw [hsum, restrict_finset_sum_smul, hinner]
  -- The right-hand side, with each `⟨θ, ν⟩` replaced by its multiplicity.
  have hR : (∑ ν : IrreducibleCharacter K,
        ClassFunction.inner θ (ν : ClassFunction K ℂ) *
          ClassFunction.inner (ClassFunction.restrict A (ν : ClassFunction K ℂ)) ψ)
      = ∑ ν : IrreducibleCharacter K, (m (ν : ClassFunction K ℂ) : ℂ) *
          ClassFunction.inner (ClassFunction.restrict A (ν : ClassFunction K ℂ)) ψ := by
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [hcoeff (ν : ClassFunction K ℂ) (IrreducibleCharacter.isIrreducible ν)]
  rw [hL, hR]
  -- The support of `m` lies in the range of the coercion `IrreducibleCharacter K → CF(K)`.
  have hsupp' : ↑m.support ⊆ Set.range (fun ν : IrreducibleCharacter K =>
      (ν : ClassFunction K ℂ)) := by
    intro a ha
    exact ⟨⟨a, hsupp ha⟩, rfl⟩
  exact (finsupp_sum_univ_eq_sum_support (fun ν : IrreducibleCharacter K =>
      (ν : ClassFunction K ℂ)) (fun a b hh => Subtype.ext hh) m hsupp'
      (fun a => ClassFunction.inner (ClassFunction.restrict A a) ψ)).symm

end Work.BG
