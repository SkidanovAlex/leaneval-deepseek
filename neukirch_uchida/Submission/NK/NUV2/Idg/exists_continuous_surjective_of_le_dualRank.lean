import Mathlib
import Submission.NK.RankTheoryDeep.IdeleRankDefs
import Submission.NK.NUV2.TowerRank.exists_surjective_of_le_dualRank

/-!
# A `ℤ_[2]^r`-quotient of a compact abelian group of dual rank `≥ r`

This is the packaging, in the form needed downstream, of the general-`ℓ` rank-to-quotient theorem
`NK.NUV2.TowerRank.exists_surjective_of_le_dualRank` (Shimizu's Lemma 4f.1, see
`Submission/Work/NUV2/TowerRank/NOTES.md` §1(b)): for a compact Hausdorff abelian group `G`, a
bound `r ≤ dim_{ℤ_[2]} Hom_cts(G, ℤ_[2])` on the `ℤ_[2]`-rank of the continuous dual produces `r`
continuous characters `χ_1, …, χ_r : G → ℤ_[2]` whose joint evaluation is surjective.

The present statement bundles the `r` characters into a single continuous surjective monoid
homomorphism `G →* Multiplicative (Fin r → ℤ_[2])`.
-/

namespace NK.NUV2.Idg

/-- **A surjection onto `(ℤ_[2])^r` from a rank bound on the continuous dual.**

If `r` is at most the `ℤ_[2]`-rank of `Hom_cts(G, ℤ_[2])` for a compact Hausdorff abelian `G`,
then `G` admits a continuous surjective homomorphism onto the multiplicative group
`Multiplicative (Fin r → ℤ_[2])`, i.e. onto `((ℤ_[2])^r, +)` rewritten multiplicatively. -/
theorem exists_continuous_surjective_of_le_dualRank {G : Type*} [CommGroup G]
    [TopologicalSpace G] [CompactSpace G] [T2Space G] (r : ℕ)
    (h : (r : Cardinal) ≤ NK.RankTheoryDeep.dualRank G 2) :
    ∃ Φ : G →* Multiplicative (Fin r → PadicInt 2), Continuous ⇑Φ ∧ Function.Surjective Φ := by
  obtain ⟨χ, hχ⟩ :=
    NK.NUV2.TowerRank.exists_surjective_of_le_dualRank (ℓ := 2) (r := r) h
  refine ⟨{ toFun := fun x =>
              Multiplicative.ofAdd
                (fun i => (χ i : Additive G →+ PadicInt 2) (Additive.ofMul x))
            map_one' := ?_
            map_mul' := ?_ }, ?_, ?_⟩
  · have h1 : (fun i => (χ i : Additive G →+ PadicInt 2) (Additive.ofMul (1 : G))) = 0 := by
      funext i
      exact map_zero _
    rw [h1, ofAdd_zero]
  · intro x y
    have h1 : (fun i => (χ i : Additive G →+ PadicInt 2) (Additive.ofMul (x * y)))
        = (fun i => (χ i : Additive G →+ PadicInt 2) (Additive.ofMul x))
          + (fun i => (χ i : Additive G →+ PadicInt 2) (Additive.ofMul y)) := by
      funext i
      exact map_add _ _ _
    rw [h1, ofAdd_add]
  · have hg : Continuous fun x : G =>
        (fun i => (χ i : Additive G →+ PadicInt 2) (Additive.ofMul x)) := by
      rw [continuous_pi_iff]
      intro i
      exact (χ i).2
    exact continuous_ofAdd.comp hg
  · intro y
    obtain ⟨x, hx⟩ := hχ (Multiplicative.toAdd y)
    have hx' : (fun i => (χ i : Additive G →+ PadicInt 2) (Additive.ofMul x))
        = Multiplicative.toAdd y := hx
    exact ⟨x, by
      show Multiplicative.ofAdd
          (fun i => (χ i : Additive G →+ PadicInt 2) (Additive.ofMul x)) = y
      rw [hx']
      exact ofAdd_toAdd y⟩

end NK.NUV2.Idg
