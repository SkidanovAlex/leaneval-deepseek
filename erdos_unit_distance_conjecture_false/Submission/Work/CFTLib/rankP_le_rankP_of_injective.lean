import Mathlib
import Submission.Work.CFT.ClassFormation.Defs
import Submission.Work.CFT.ClassFormation.Schur.finrank_homology_fp_eq

namespace Work.CFTLib

/-- **`rankP` is monotone under injective additive homomorphisms.**

For a prime `p` and an injective additive homomorphism `f : A →+ B` between finitely generated
abelian groups, `rankP p A ≤ rankP p B`.  Indeed `natCard_ker_eq_pow_rankP` identifies
`p ^ rankP p A` with the cardinality of the `p`-torsion subgroup `A[p] = ker (p ·)`; an injective
`f` maps `A[p]` into `B[p]`, so `|A[p]| ≤ |B[p]|`, and `p ^ ·` is strictly monotone. -/
theorem rankP_le_rankP_of_injective (p : ℕ) [Fact p.Prime] {A B : Type} [AddCommGroup A]
    [AddCommGroup B] [Finite A] [Finite B] [Module.Finite ℤ A] [Module.Finite ℤ B]
    (f : A →+ B) (hf : Function.Injective f) :
    Work.CFT.ClassFormation.rankP p A ≤ Work.CFT.ClassFormation.rankP p B := by
  have hA := Work.CFT.ClassFormation.Schur.natCard_ker_eq_pow_rankP p A
  have hB := Work.CFT.ClassFormation.Schur.natCard_ker_eq_pow_rankP p B
  -- an injective homomorphism carries the `p`-torsion of `A` into the `p`-torsion of `B`
  have hker : ∀ x : ↥(Work.CFT.ClassFormation.Schur.mulByP p A).ker,
      f x.1 ∈ (Work.CFT.ClassFormation.Schur.mulByP p B).ker := by
    intro x
    rw [LinearMap.mem_ker]
    calc Work.CFT.ClassFormation.Schur.mulByP p B (f x.1)
        = (p : ℤ) • f x.1 := by simp [Work.CFT.ClassFormation.Schur.mulByP]
      _ = f ((p : ℤ) • x.1) := (AddMonoidHom.map_zsmul f (p : ℤ) x.1).symm
      _ = f 0 := by
          congr 1
          simpa [Work.CFT.ClassFormation.Schur.mulByP] using x.2
      _ = 0 := f.map_zero
  let g : ↥(Work.CFT.ClassFormation.Schur.mulByP p A).ker →
      ↥(Work.CFT.ClassFormation.Schur.mulByP p B).ker := fun x => ⟨f x.1, hker x⟩
  have hg : Function.Injective g := by
    intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))
  have hcard : Nat.card ↥(Work.CFT.ClassFormation.Schur.mulByP p A).ker ≤
      Nat.card ↥(Work.CFT.ClassFormation.Schur.mulByP p B).ker :=
    Nat.card_le_card_of_injective g hg
  rw [hA, hB] at hcard
  exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hcard

end Work.CFTLib
