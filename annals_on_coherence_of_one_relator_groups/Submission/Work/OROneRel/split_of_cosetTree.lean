import Mathlib
import Submission.Work.OROneRel.winRhoRange_tree
import Submission.Work.OROneRel.generation_of_tree
import Submission.Work.OROneRel.hnnConjMap_injective_of_tree
import Submission.Work.OROneRel.hnnConjSplit

/-!
# A tree structure on the coset graph gives the HNN splitting

This module isolates (and thereby keeps dependency-clean) the assembly step

  `IsTree (GradedHNN.Coset V τ)`  ⟹  `V ⊔ ⟪τ⟫ = ⊤`  ∧  `hnnConjMap V τ` injective

of `Submission/Work/OROneRel/magnus_residual_winSplitting_v2.lean`, which it was moved out of in
order to keep the import closure of that file free of
`Submission.Work.OROneRel.twoLetter_cycle_decor` (whose declaration `decor_replicate_true` clashes
with the one of `Submission.Work.OROneRel.decor_wordOf_zpow_of`; see the header of
`Submission/Work/OROneRel/magnus_step_residual.lean`).  The theorem itself is unchanged.
-/

namespace Work.OROneRel

universe u

/-- **A tree stucture on the coset graph of `(V, τ)` gives the HNN splitting.** -/
theorem exists_split_of_cosetTree {G : Type u} [Group G] (V : Subgroup G) (τ : G)
    (φ : G →* Multiplicative ℤ) (hH : ∀ h : ↥V, φ (h : G) = 1)
    (ht : φ τ = Multiplicative.ofAdd 1)
    (hT : Work.ORBassSerre.IsTree (GradedHNN.Coset V τ)) :
    V ⊔ Subgroup.zpowers τ = ⊤ ∧ Function.Injective (hnnConjMap V τ) := by
  classical
  have hninv : Work.ORBassSerre.ActsWithoutInversions G (GradedHNN.Coset V τ) :=
    Work.OROneRel.actsWithoutInversions_coset V τ φ hH ht
  have hsmul : τ • (τ⁻¹ • GradedHNN.baseC V τ) = GradedHNN.baseC V τ := by
    rw [smul_inv_smul]
  have hcover : ∀ x : GradedHNN.Coset V τ, ∃ g : G, g • GradedHNN.baseC V τ = x := by
    intro x
    obtain ⟨g, hg⟩ := Quotient.exists_rep x
    refine ⟨g, ?_⟩
    rw [GradedHNN.smul_cmk, mul_one]
    exact hg
  have hedges : ∀ (x y : GradedHNN.Coset V τ) (f : x ⟶ y), ∃ g : G,
      g • Quiver.Total.mk (GradedHNN.baseC V τ) (τ⁻¹ • GradedHNN.baseC V τ)
          (GradedHNN.edgeArrowC V τ) = Quiver.Total.mk x y f ∨
      g • (Quiver.Total.mk (GradedHNN.baseC V τ) (τ⁻¹ • GradedHNN.baseC V τ)
          (GradedHNN.edgeArrowC V τ)).reverse = Quiver.Total.mk x y f := by
    intro x y f
    obtain ⟨h, hh | hh⟩ := f.down
    · -- `x = hV`, `y = hτV`
      have hgv : (h * τ) • GradedHNN.baseC V τ = y := by
        rw [GradedHNN.smul_cmk, mul_one, ← hh.2]
      have hgz : (h * τ) • (τ⁻¹ • GradedHNN.baseC V τ) = x := by
        rw [smul_smul, show (h * τ) * τ⁻¹ = h from by group, GradedHNN.smul_cmk, mul_one,
          ← hh.1]
      refine ⟨h * τ, Or.inr ?_⟩
      rw [Work.ORBassSerre.GraphAction.smul_reverse_apply]
      change Quiver.Total.mk ((h * τ) • (τ⁻¹ • GradedHNN.baseC V τ))
        ((h * τ) • GradedHNN.baseC V τ) _ = Quiver.Total.mk x y f
      exact GradedHNN.total_ext_coset V τ hgz hgv _ _
    · -- `y = hV`, `x = hτV`
      have hgv : (h * τ) • GradedHNN.baseC V τ = x := by
        rw [GradedHNN.smul_cmk, mul_one, ← hh.2]
      have hgz : (h * τ) • (τ⁻¹ • GradedHNN.baseC V τ) = y := by
        rw [smul_smul, show (h * τ) * τ⁻¹ = h from by group, GradedHNN.smul_cmk, mul_one,
          ← hh.1]
      refine ⟨h * τ, Or.inl ?_⟩
      change Quiver.Total.mk ((h * τ) • GradedHNN.baseC V τ)
        ((h * τ) • (τ⁻¹ • GradedHNN.baseC V τ)) _ = Quiver.Total.mk x y f
      exact GradedHNN.total_ext_coset V τ hgv hgz _ _
  have hstab : MulAction.stabilizer G (GradedHNN.baseC V τ) = V :=
    Work.OROneRel.stabilizer_baseC_eq V τ
  refine ⟨?_, ?_⟩
  · rw [← hstab]
    exact Work.OROneRel.generation_of_tree (G := G) (V := GradedHNN.Coset V τ) hT
      (GradedHNN.baseC V τ) τ (GradedHNN.edgeArrowC V τ) hsmul hcover hedges
  · have hkey := Work.OROneRel.hnnConjMap_injective_of_tree (G := G)
      (V := GradedHNN.Coset V τ) hT hninv (GradedHNN.baseC V τ) τ
      (GradedHNN.edgeArrowC V τ) hsmul
    rwa [hstab] at hkey

end Work.OROneRel
