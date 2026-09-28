import Mathlib
import Submission.Work.Stems.RankOneClauses
import Submission.Work.Stems.HurewiczFirstDegree
import Submission.Work.RatHurewicz.hurewiczModTorsionFirstDegree
import Submission.Work.RatHurewicz.isZero_ratH_one_of_torsion
import Submission.Work.Serre.OneCell.RatAdditivity

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `π_k(X)` torsion forces `H_k(X;ℚ) = 0` in the first non-vanishing degree

Let `X` be a space whose homotopy groups vanish in degrees `< k` (`k ≥ 2`) and such that every
element of `π_k(X,x₀)` has finite order.  Then the rational homology of `X` vanishes in degree `k`.

This is the "trivial" half of the rational Hurewicz computation in the first non-vanishing degree:

* the integral Hurewicz theorem in degree `k` (`Work.Stems.hurewicz_first_degree`), applicable
  because `X` is `(k-1)`-connected and `k ≥ 2`, says that the Hurewicz map
  `π_k(X,x₀) → H_k(X;ℤ)` is bijective, so every class of `H_k(X;ℤ)` is the Hurewicz image `h(a)`
  of a homotopy class `a`;
* the Hurewicz map is additive in the form `h(a^N) = (N : ℤ) • h(a)`
  (`Work.RatHurewicz.hurewiczModTorsionFirstDegree_pow_aux`), so a torsion class `a` (with
  `a^N = 1`) has `N • h(a) = h(a^N) = h(1) = 0`: the integral homology `H_k(X;ℤ)` is a torsion
  group;
* the rational homology of a space is the rationalisation of its integral homology
  (`Work.Serre.OneCell.ratHomologyBaseChange`, flat base change along `ℤ → ℚ`), and the
  rationalisation of a torsion abelian group vanishes
  (`Work.RatHurewicz.subsingleton_ratTensor_of_torsion`).

This is the lemma a colleague needs for the rank-one Eilenberg--MacLane computation: applied to a
space with `H_k(X;ℚ) ≅ ℚ` it shows that `π_k(X,x₀)` must contain a class of infinite order.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Stems

noncomputable section

/-- **Torsion integral homology forces vanishing rational homology**, in every degree: the
rational singular chains are the integral ones with coefficients extended along `ℤ → ℚ`, and
`ℚ` is flat over `ℤ`, so `H_j(X;ℚ) ≅ H_j(X;ℤ) ⊗[ℤ] ℚ`, the rationalisation of a torsion
group. -/
private theorem isZero_ratH_of_torsion_aux {X : Type} [TopologicalSpace X] (j : ℕ)
    (h : ∀ b : (Work.Cohomology.singularChains ℤ (TopCat.of X)).homology j,
      ∃ N : ℕ, 0 < N ∧ N • b = 0) :
    IsZero ((Work.Cohomology.singularChains ℚ (TopCat.of X)).homology j) := by
  haveI : Subsingleton ↥(Work.Serre.OneCell.ratF.obj
      ((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology j)) :=
    Work.RatHurewicz.subsingleton_ratTensor_of_torsion _ h
  exact IsZero.of_iso
    (ModuleCat.isZero_of_subsingleton (Work.Serre.OneCell.ratF.obj
      ((Work.Cohomology.singularChains ℤ (TopCat.of X)).homology j)))
    (Work.Serre.OneCell.ratHomologyBaseChange (TopCat.of X) j)

theorem rankOne_hurewicz_torsion {k : ℕ} (hk : 2 ≤ k) [Nonempty (Fin k)] {X : Type} [TopologicalSpace X] (x₀ : X)
    (hconn : ∀ i : ℕ, i < k → Subsingleton (HomotopyGroup (Fin i) X x₀))
    (htors : ∀ α : HomotopyGroup (Fin k) X x₀, ∃ m : ℕ, 0 < m ∧ α ^ m = 1) :
    CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) k) := by
  -- write `k` as a literal successor, so that the Hurewicz statements apply in their stated form
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = m + 1 :=
    ⟨k - 1, (Nat.sub_add_cancel (by omega : 1 ≤ k)).symm⟩
  -- it suffices that every integral homology class in degree `k` is of finite order
  refine isZero_ratH_of_torsion_aux (X := X) (m + 1) ?_
  intro b
  -- Hurewicz: every class is the Hurewicz image of a homotopy class
  obtain ⟨a, ha⟩ := (Work.Stems.hurewicz_first_degree (m + 1) hk x₀ hconn).2 b
  obtain ⟨N, hN, hNa⟩ := htors a
  refine ⟨N, hN, ?_⟩
  rw [← ha]
  -- additivity of the Hurewicz map: `h(a^N) = N • h(a)`
  have hpow := Work.RatHurewicz.hurewiczModTorsionFirstDegree_pow_aux m X x₀ a N
  rw [hNa] at hpow
  have h1 : Work.Stems.hurewiczMapN (m + 1) (Nat.succ_le_succ (Nat.zero_le m)) x₀
      (1 : HomotopyGroup (Fin (m + 1)) X x₀) = 0 := by
    rw [Work.Stems.hurewiczMapN_eq_hurewiczMap]
    exact Work.Stems.hurewiczMap_one m
  rw [h1] at hpow
  simp only [natCast_zsmul] at hpow
  exact hpow.symm

end

end Work.Stems
