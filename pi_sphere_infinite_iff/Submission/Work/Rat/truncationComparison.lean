import Mathlib
import Submission.Work.Rat.RankOneEMDefs
import Submission.Work.Serre.serrePostnikovTower
import Submission.Work.StemsB.rangeModel_ratH_iso
import Submission.Work.Serre.piMapN_monoidHom

/-!
# The Postnikov truncation of a rank-one range model

`Work.Rat.TruncationComparison`: a space `Z` whose homotopy groups vanish up to degree `M+1`
except in a degree `d ≥ 3` with `d ≤ M+1`, where `H_d(Z;ℚ) ≅ ℚ`, may be replaced by a space `P`
which is a range model of the same "rank-one" type through the *larger* top `M+1+d` (so that the
genuine Killing construction has room to run), still has `H_d(P;ℚ) ≅ ℚ`, and has the same rational
homology as `Z` in degrees `≤ M+1`.

The space `P` is the finite Postnikov truncation of `Z` at level `M+1`
(`Work.Serre.serrePostnikovTower`, proved): the map `g : Z → P` is a `π_i`-isomorphism for `i ≤ M+1`
and `π_i(P) = 0` for `M+1 < i ≤ M+1+d`.  Consequently `P` inherits the vanishing of `π_i` for
`i ≤ M+1`, `i ≠ d` from `Z`, and has the required vanishing above `M+1` by construction.  The two
spaces are range models of `K(A,d)` (`A = π_d(Z)`) through `M+1` — with the same coefficient group,
`π_d(P) ≅ π_d(Z)` because `d ≤ M+1` — so `Work.StemsB.rangeModel_ratH_iso` compares their rational
homology in degrees `≤ M+1`; in particular it identifies `H_d(P;ℚ)` with `H_d(Z;ℚ) ≅ ℚ`.
-/

namespace Work.Rat

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- The identity multiplicative equivalence `G ≃* Multiplicative (Additive G)`: the type copies
`Multiplicative` and `Additive` are the identity on the carriers, and the multiplication on
`Multiplicative (Additive G)` is that of `G`. -/
def addSelfMulEquiv (G : Type*) [Group G] : G ≃* Multiplicative (Additive G) where
  toFun g := Multiplicative.ofAdd (Additive.ofMul g)
  invFun m := Additive.ofMul.symm (Multiplicative.ofAdd.symm m)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem truncationComparison : Work.Rat.TruncationComparison := by
  intro d M hd hdM Z _ z₀ hZ hgen
  -- write `d` in the shape `d' + 2`, so that `π_d` (a commutative group) is available
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 2 := ⟨d - 2, by omega⟩
  -- the Postnikov truncation of `Z` at level `M+1`, with top `M+1+(d'+2)`
  obtain ⟨P, tP, g, hg1, hg2⟩ :=
    Work.Serre.serrePostnikovTower (M + 1) (M + 1 + (d' + 2)) Z z₀ (by omega)
  letI : TopologicalSpace P := tP
  -- the vanishing of the homotopy groups of `P` up to the large top
  have hPvan : ∀ j : ℕ, j ≤ M + 1 + (d' + 2) → j ≠ d' + 2 →
      Subsingleton (HomotopyGroup (Fin j) P (g z₀)) := by
    intro j hj hjne
    by_cases hle : j ≤ M + 1
    · haveI := hZ j hle hjne
      exact (hg1 j hle).2.subsingleton
    · exact hg2 j (Nat.lt_of_not_le hle) hj (g z₀)
  -- the range model structure of `Z` through `M+1`
  have hZem : Work.Serre.IsEMSpaceUpTo (Additive (HomotopyGroup (Fin (d' + 2)) Z z₀)) (d' + 2)
      (by omega) (M + 1) Z z₀ :=
    ⟨⟨addSelfMulEquiv (HomotopyGroup (Fin (d' + 2)) Z z₀)⟩,
      fun i hne hmem => hZ i (by rcases hmem with h | h <;> omega) hne⟩
  -- the Postnikov map is an isomorphism on `π_d`
  obtain ⟨F, hF⟩ := Work.Serre.piMapN_monoidHom g (d' + 2) z₀
  have hFfun : ⇑F = Work.Serre.piMapN g (d' + 2) z₀ := funext hF
  have hFbij : Function.Bijective F := by
    rw [hFfun]
    exact hg1 (d' + 2) (by omega)
  let e : HomotopyGroup (Fin (d' + 2)) Z z₀ ≃* HomotopyGroup (Fin (d' + 2)) P (g z₀) :=
    MulEquiv.ofBijective F hFbij
  -- the range model structure of `P` through `M+1` (the top `M+1+(d'+2)` weakened)
  have hPem : Work.Serre.IsEMSpaceUpTo (Additive (HomotopyGroup (Fin (d' + 2)) Z z₀)) (d' + 2)
      (by omega) (M + 1) P (g z₀) :=
    ⟨⟨e.symm.trans (addSelfMulEquiv (HomotopyGroup (Fin (d' + 2)) Z z₀))⟩,
      fun i hne hmem => hPvan i (by rcases hmem with h | h <;> omega) hne⟩
  -- the comparison of the two range models in degrees `≤ M+1`
  have hcmp : ∀ j : ℕ, j ≤ M + 1 →
      Nonempty (Work.Serre.ratH (TopCat.of Z) j ≅ Work.Serre.ratH (TopCat.of P) j) :=
    Work.StemsB.rangeModel_ratH_iso (Additive (HomotopyGroup (Fin (d' + 2)) Z z₀)) (d' + 2)
      (M + 1) (by omega) Z z₀ hZem P (g z₀) hPem
  -- the rank-one generation of `P` in degree `d`
  obtain ⟨e1⟩ := hgen
  obtain ⟨e2⟩ := hcmp (d' + 2) (by omega)
  exact ⟨P, tP, g z₀, hPvan, ⟨e2.symm ≪≫ e1⟩, hcmp⟩

end

end Work.Rat
