import Mathlib
import Submission.Work.Rat.hopfInterfaces
import Submission.Work.Rat.c2FreeMain
import Submission.Work.StemsB.FibreTransport
import Submission.Work.Stems.isHurewiczFibration_homotopyFibreFst
import Submission.Work.Stems.fibreOfHomeomorphLoopSpace
import Submission.Work.Stems.Engine.C2EvenRange
import Submission.Work.Serre.Models
import Submission.Work.Stems.isEMSpace_change_basepoint
import Submission.Work.Serre.serreS2OfC0C2oddS1

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The fibre data of the cover of an even sphere (Serre route)

`Work.Rat.coverProj e f s₀ : hofib f → SphModel n` is the projection of the homotopy fibre of
`f : Sⁿ → X` transported to the one-point model of the sphere along a homeomorphism
`e : SphModel n ≃ₜ Sⁿ` (`Work.Rat.hopfInterfaces`).  This file proves `Work.Rat.coverFibreDataSerre`:
for `n ≥ 2` even, `X` a range model of `K(ℤ,n)` through `N ≥ 4n` and `f` a `πₙ`-bijection,

* the projection is a Hurewicz fibration,
* the fibre over `∞` — i.e. the fibre of the homotopy-fibre projection over `e ∞`, hence the loop
  space `ΩX` up to homotopy — is rationally acyclic in degrees `0 < t ≤ 2n`, `t ≠ n-1`,
* and its rational homology in degree `n-1` is `ℚ`.

The computational input is the `C2` layer of the Serre blueprint: `X` is a range model of `K(ℤ,n)`,
so `ΩX` is a range model of `K(ℤ,n-1)` with `n-1` **odd**
(`Work.Stems.isEMSpaceUpTo_loop'`), and the odd clause `Work.Stems.Engine.C2oddFree 1` — which is
`Work.Rat.c2Free hE3b` — computes its rational homology as that of `S^{n-1}` through degree
`(N-1) - (n-1) = N - n ≥ 3n`.  The transport from the fibre over `e ∞` to the loop space `Path (f s₀)
(f s₀)` is base-point independence of the fibre homology of a Serre fibration
(`Work.Serre.ratH_fibre_iso_of_path`) followed by the homeomorphism
`Work.Stems.fibreOfHomeomorphLoopSpace`.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Rat

noncomputable section

/-- **A homeomorphism of spaces is a Hurewicz fibration.**  The lift of a homotopy `H` in the base
along `h : A ≃ₜ B` is `h.symm ∘ H`; the two endpoint conditions use the injectivity of `h`. -/
theorem homeomorph_isHurewiczFibration {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (h : A ≃ₜ B) : Work.StemsB.IsHurewiczFibration (⟨h, h.continuous⟩ : C(A, B)) := by
  intro Z _ f b H
  refine ⟨⟨fun z => h.symm (b z), h.symm.continuous.comp b.continuous⟩, ?_, ?_⟩
  · refine ContinuousMap.Homotopy.mk
      ⟨fun zt : unitInterval × Z => h.symm (H.toContinuousMap (zt.1, zt.2)),
        h.symm.continuous.comp
          (H.toContinuousMap.continuous.comp (continuous_fst.prodMk continuous_snd))⟩ ?_ ?_
    · intro z
      change h.symm (H (0, z)) = f z
      rw [H.apply_zero]
      exact h.symm_apply_apply (f z)
    · intro z
      change h.symm (H (1, z)) = h.symm (b z)
      rw [H.apply_one]
  · ext x
    show h (h.symm (H.toContinuousMap (x.1, x.2))) = H.toContinuousMap (x.1, x.2)
    exact h.apply_symm_apply _

/-- The identity map, as a homeomorphism between two subtypes whose underlying sets are equal. -/
def subtypeHomeoOfSetEq {X : Type} [TopologicalSpace X] {A B : Set X} (h : A = B) :
    ↥A ≃ₜ ↥B where
  toFun x := ⟨x.1, h ▸ x.2⟩
  invFun y := ⟨y.1, h.symm ▸ y.2⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  continuous_toFun := Continuous.subtype_mk continuous_subtype_val _
  continuous_invFun := Continuous.subtype_mk continuous_subtype_val _

/-- **The rational homology of the loop space of a range model of `K(ℤ,n)`** (`n ≥ 2` even,
`N ≥ 4n`): it is that of `S^{n-1}` through degree `2n`.

`ΩX = Path x₀ x₀` is a range model of `K(ℤ,n-1)` through degree `N-1`
(`Work.Stems.isEMSpaceUpTo_loop'`), and `n-1` is odd, so the odd clause of the `C2` layer
(`Work.Stems.Engine.C2oddFree 1`, available from Serre's Gysin statement `hE3b` as
`Work.Rat.c2Free hE3b`) applies: its rational homology is `ℚ` in degree `n-1` and vanishes in every
other positive degree below `(N-1) - (n-1) = N - n ≥ 3n > 2n`. -/
theorem loopSpaceRatH_rangeModel {n : ℕ} (hn : 2 ≤ n) (heven : Even n)
    (hE3b : Work.Serre.SerreE3b) (X : Type) [TopologicalSpace X] (x₀ : X) (N : ℕ)
    (hN : 4 * n ≤ N) (hX : Work.Serre.IsEMSpaceUpTo ℤ n (by omega) N X x₀) :
    (∀ t : ℕ, 0 < t → t ≠ n - 1 → t ≤ 2 * n →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Path x₀ x₀)) t)) ∧
    Nonempty (Work.Serre.ratH (TopCat.of (Path x₀ x₀)) (n - 1)
      ≅ ModuleCat.of ℚ ℚ) := by
  obtain ⟨k, hk⟩ := heven
  have hodd : Odd (n - 1) := ⟨k - 1, by omega⟩
  have hloop := Work.Stems.isEMSpaceUpTo_loop' hn x₀ hX
  obtain ⟨hgen, hvan⟩ :=
    (Work.Rat.c2Free hE3b).2 (n - 1) (by omega) hodd (N - 1)
      (Path x₀ x₀) (Path.refl x₀) hloop
  refine ⟨fun t ht0 htn ht2n => hvan t ht0 ?_ htn, hgen⟩
  simp only [one_mul]
  omega

/-- **The rational homology of the fibre of `coverProj` over `∞` is that of the loop space.**

The fibre of `coverProj e f s₀` over `∞` is the fibre of `homotopyFibreFst f s₀` over `e ∞`, which
is rationally isomorphic in every degree to the fibre over `s₀` because `Sⁿ` is path connected and
`homotopyFibreFst f s₀` is a Serre fibration (`Work.Serre.ratH_fibre_iso_of_path`); the latter
fibre is `Work.RatHurewicz.fibreOf f s₀`, homeomorphic to `Path (f s₀) (f s₀)`
(`Work.Stems.fibreOfHomeomorphLoopSpace`). -/
theorem coverFibreRatH_iso_path {n : ℕ} (hn : 1 ≤ n) {X : Type} [TopologicalSpace X]
    (s₀ : Work.Serre.Sph n) (f : C(Work.Serre.Sph n, X))
    (e : Work.StemsB.SphModel n ≃ₜ Work.Serre.Sph n) (j : ℕ) :
    Nonempty (Work.Serre.ratH (TopCat.of (Work.Rat.coverFibre e f s₀)) j ≅
      Work.Serre.ratH (TopCat.of (Path (f s₀) (f s₀))) j) := by
  have hpc : PathConnectedSpace (Work.Serre.Sph n) := Work.Serre.pathConnectedSpace_sph n hn
  obtain ⟨γ⟩ := hpc.joined (e OnePoint.infty) s₀
  let γc : C(unitInterval, Work.Serre.Sph n) := ⟨γ, γ.continuous⟩
  have h0 : γc 0 = e OnePoint.infty := γ.source
  have h1 : γc 1 = s₀ := γ.target
  obtain ⟨emid⟩ := Work.Serre.ratH_fibre_iso_of_path (Work.RatHurewicz.homotopyFibreFst f s₀)
    (Work.Stems.isHurewiczFibration_homotopyFibreFst f s₀).isSerreFibration γc j
  rw [h0, h1] at emid
  obtain ⟨e₀⟩ := Work.Stems.fibreOfHomeomorphLoopSpace f s₀
  obtain ⟨e₁⟩ := Work.Serre.OneCell.nonempty_ratH_iso_of_homeo e₀ j
  have h : (Work.Rat.coverProj e f s₀ ⁻¹' ({OnePoint.infty} : Set (Work.StemsB.SphModel n)))
      = ((Work.RatHurewicz.homotopyFibreFst f s₀) ⁻¹'
          ({e OnePoint.infty} : Set (Work.Serre.Sph n))) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Work.Rat.coverProj,
      ContinuousMap.comp_apply]
    exact Homeomorph.symm_apply_eq e
  obtain ⟨e₂⟩ := Work.Serre.OneCell.nonempty_ratH_iso_of_homeo (subtypeHomeoOfSetEq h) j
  exact ⟨e₂ ≪≫ emid ≪≫ e₁⟩

/-- **The fibre data of the cover of an even sphere.**  The statement `Work.Rat.coverFibreData`
with Serre's Gysin/Euler-class statement `SerreE3b` made explicit as a hypothesis (it is the input
of the `C2` layer, `Work.Rat.c2Free`). -/
theorem coverFibreDataSerre {n : ℕ} (hn : 2 ≤ n) (heven : Even n)
    (hE3b : Work.Serre.SerreE3b)
    {X : Type} [TopologicalSpace X] (pt : X) (N : ℕ) (hN : 4 * n ≤ N)
    (hX : Work.Serre.IsEMSpaceUpTo ℤ n (by omega) N X pt)
    (s₀ : Work.Serre.Sph n) (f : C(Work.Serre.Sph n, X))
    (hbij : Function.Bijective (Work.Serre.piMapN f n s₀))
    (e : Work.StemsB.SphModel n ≃ₜ Work.Serre.Sph n) :
    Work.StemsB.IsHurewiczFibration (Work.Rat.coverProj e f s₀) ∧
      (∀ t : ℕ, 0 < t → t ≠ n - 1 → t ≤ 2 * n →
        CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.Rat.coverFibre e f s₀)) t)) ∧
      Nonempty (Work.Serre.ratH (TopCat.of (Work.Rat.coverFibre e f s₀)) (n - 1)
        ≅ ModuleCat.of ℚ ℚ) := by
  -- ## The projection is a Hurewicz fibration: `e.symm` is a homeomorphism, the projection of the
  -- homotopy fibre is a Hurewicz fibration, and the composite of two of them is one.
  have hHur : Work.StemsB.IsHurewiczFibration (Work.Rat.coverProj e f s₀) :=
    (homeomorph_isHurewiczFibration e.symm).comp
      (Work.Stems.isHurewiczFibration_homotopyFibreFst f s₀)
  -- ## Transport the range-model hypothesis to the base point `f s₀` (`X` is path connected)
  have hpcX : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero pt
      (hX.2 0 (by omega) (Or.inl (by omega)))
  obtain ⟨γ₀⟩ := hpcX.joined pt (f s₀)
  have hX' : Work.Serre.IsEMSpaceUpTo ℤ n (by omega) N X (f s₀) :=
    Work.Stems.isEMSpaceUpTo_change_basepoint (by omega) γ₀ hX
  -- ## The rational homology of the fibre, through the loop space of `X`
  obtain ⟨hloopVan, hloopGen⟩ := loopSpaceRatH_rangeModel hn heven hE3b X (f s₀) N hN hX'
  refine ⟨hHur, ?_, ?_⟩
  · intro t ht0 htn ht2n
    obtain ⟨e'⟩ := coverFibreRatH_iso_path (by omega) s₀ f e t
    exact IsZero.of_iso (hloopVan t ht0 htn ht2n) e'
  · obtain ⟨e'⟩ := coverFibreRatH_iso_path (by omega) s₀ f e (n - 1)
    exact ⟨e' ≪≫ hloopGen.some⟩

end

end Work.Rat
