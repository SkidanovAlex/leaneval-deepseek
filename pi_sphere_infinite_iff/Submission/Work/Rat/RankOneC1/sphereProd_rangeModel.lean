import Mathlib
import Submission.Work.Rat.U.FamModel
import Submission.Work.RatHurewicz.isEMSpaceUpTo_pi_fin
import Submission.Work.Serre.C1SphOne
import Submission.Work.Serre.C1Loop
import Submission.Work.Serre.sphOneAspherical
import Submission.Work.Rat.RankOneC1.transferRangeTwo
import Submission.Work.Rat.RankOneC1.prodMapCovering
import Submission.Work.Rat.RankOneC1.sphOneProdVanishing

/-!
# A rank-one range model of `K(ℤ × F, 1)` which is rationally a circle in the range

For a finite abelian group `F` and every `N` we build a space `L` which is a model of
`K(ℤ × F, 1)` through degree `N` and whose rational homology vanishes in the degrees
`2, …, N` (degree `1` is the one where the circle lives, so it cannot vanish).

The model is the product `L = S¹ × M` of the circle with the rationally acyclic range model `M` of
`K(F,1)` built in `Submission/Work/Rat/U/FamModel.lean` (`M = E/G` is the quotient of a product
`E = ∏ᵢ S^{2N+3}` of highly connected spheres by the free action of `G = ∏ᵢ μ_{nᵢ}`).

* the range-model property is the product rule `isEMSpaceUpTo_prod`, applied to the circle as a
  range model of `K(ℤ,1)` (`Work.EMFG.torusFGandEM`'s argument, reproduced below) and to `M`;
* the rational vanishing reduces, via the **transfer** of the finite covering
  `S¹ × E → S¹ × M` of degree `|G|` (`Work.Rat.RankOneC1.transferRangeTwo`; only degrees `≥ 2` can
  be transferred, since the total space of a finite covering of a space with `H_1 ≠ 0` necessarily
  has `H_1 ≠ 0`), to the vanishing of `H_t(S¹ × E; ℚ)` for `2 ≤ t ≤ N`
  (`Work.Rat.RankOneC1.sphOneProdVanishing`, proved in the sibling file): the space `E` is
  `(2N+2)`-connected and the fibre of `Prod.snd : S¹ × E → E` is the circle, so the rational Serre
  pair comparison `Work.Serre.ratSerrePairComparison` identifies
  `H_t(S¹ × E, S¹ × {e₀}; ℚ)` with `H_t(E, {e₀}; ℚ) = 0` in the whole range `t < 2N+4`, and the
  long exact sequence of the pair finishes.  The product covering itself is
  `Work.Rat.RankOneC1.prodMapCovering`, and the constancy of the fibres is `prodMapFiberCard`.
-/

set_option linter.style.haveILetI false

namespace Work.Rat.RankOneC1

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## Auxiliary facts -/

/-- **The circle is a range model of `K(ℤ,1)`**: `π₁(S¹) ≅ ℤ` (`Work.Serre.pi1SphOne_addEquiv_int`),
`S¹` is path connected and `π_i(S¹) = 0` for `i ≥ 2` (`Work.Serre.sphOneAspherical`). -/
theorem sphOne_isEMSpaceUpTo (N : ℕ) :
    Work.Serre.IsEMSpaceUpTo ℤ 1 (by norm_num) N (Work.Serre.Sph 1) Work.Serre.sphOneBase := by
  refine ⟨?_, ?_⟩
  · obtain ⟨e⟩ := Work.Serre.pi1SphOne_addEquiv_int Work.Serre.sphOneBase
    exact ⟨(Work.Serre.multiplicativeAdditiveSelf _).symm.trans (AddEquiv.toMultiplicative e)⟩
  · intro i hi hc
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      haveI : PathConnectedSpace (Work.Serre.Sph 1) := Work.Serre.sphOnePathConnected
      exact (HomotopyGroup.pi0EquivZerothHomotopy (X := Work.Serre.Sph 1)
        (x := Work.Serre.sphOneBase)).subsingleton
    · exact Work.Serre.sphOneAspherical i (by omega) Work.Serre.sphOneBase

/-- **The product of a covering map with the identity has the same fibres.** -/
theorem prodMapFiberCard {E X Y : Type} [TopologicalSpace E] [TopologicalSpace X]
    [TopologicalSpace Y] (p : E → X) (m : ℕ)
    (hcard : ∀ x : X, Nat.card ↥(p ⁻¹' {x}) = m) :
    ∀ z : Y × X, Nat.card ↥((fun z : Y × E => (z.1, p z.2)) ⁻¹' {z}) = m := by
  intro z
  rw [← hcard z.2]
  refine Nat.card_congr ((Equiv.subtypeEquivRight (fun w : Y × E => Prod.ext_iff)).trans ?_)
  exact
    { toFun := fun w => ⟨w.1.2, w.2.2⟩
      invFun := fun e => ⟨(z.1, e.1), ⟨rfl, e.2⟩⟩
      left_inv := by intro w; exact Subtype.ext (Prod.ext w.2.1.symm rfl)
      right_inv := by intro e; exact Subtype.ext rfl }

/-! ## The target -/

theorem sphereProd_rangeModel (F : Type) [AddCommGroup F] [Fintype F] (N : ℕ) :
    ∃ (L : Type) (_ : TopologicalSpace L) (l₀ : L),
      Work.Serre.IsEMSpaceUpTo (ℤ × F) 1 (by norm_num) N L l₀ ∧
      (∀ t : ℕ, 0 < t → t ≤ N → t ≠ 1 →
        CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of L) t)) := by
  classical
  -- the structure theorem: `F = ∏ᵢ ℤ/nᵢ`
  obtain ⟨ι, hι, n, hn, ⟨eF⟩⟩ := Work.RatHurewicz.finiteAbelianProdZmod F
  letI := hι
  haveI hne : ∀ i, NeZero (n i) := fun i => ⟨hn i⟩
  -- the finite model `M = E/G` of `K(F,1)` and the total space `E` of its covering
  refine ⟨Work.Serre.Sph 1 × Work.RatHurewicz.famSpace ι n N, inferInstance,
    (Work.Serre.sphOneBase, Work.RatHurewicz.famProjCM ι n N (Work.RatHurewicz.famBase ι N)),
    ?_, ?_⟩
  · -- the range model property
    have hprod : Work.Serre.IsEMSpaceUpTo (ℤ × ((i : ι) → ZMod (n i))) 1 (by norm_num) N
        (Work.Serre.Sph 1 × Work.RatHurewicz.famSpace ι n N)
        (Work.Serre.sphOneBase,
          Work.RatHurewicz.famProjCM ι n N (Work.RatHurewicz.famBase ι N)) :=
      Work.RatHurewicz.isEMSpaceUpTo_prod (by norm_num) _ _
        (sphOne_isEMSpaceUpTo N) (Work.RatHurewicz.famIsEMSpaceUpTo)
    exact Work.RatHurewicz.isEMSpaceUpTo_of_addEquiv (by norm_num) _
      hprod (AddEquiv.prodCongr (AddEquiv.refl ℤ) eF.symm)
  · -- the rational vanishing, by the transfer of the covering `S¹ × E → S¹ × M`
    intro t ht0 htN ht1
    have ht2 : 2 ≤ t := by omega
    -- the total space `S¹ × E` is rationally acyclic in the range
    have htot : ∀ t : ℕ, 2 ≤ t → t ≤ N → CategoryTheory.Limits.IsZero
        (Work.Serre.ratH (TopCat.of (Work.Serre.Sph 1 × Work.RatHurewicz.famTotal ι N)) t) :=
      sphOneProdVanishing (Work.RatHurewicz.famBase ι N) N (Work.RatHurewicz.famConn)
    -- the covering map `S¹ × E → S¹ × M`
    haveI hpcS : PathConnectedSpace (Work.Serre.Sph 1) := Work.Serre.sphOnePathConnected
    haveI hpcM : PathConnectedSpace (Work.RatHurewicz.famSpace ι n N) :=
      Work.RatHurewicz.famPathConnected
    let q : C(Work.Serre.Sph 1 × Work.RatHurewicz.famTotal ι N,
        Work.Serre.Sph 1 × Work.RatHurewicz.famSpace ι n N) :=
      ⟨fun z => (z.1, Work.RatHurewicz.famProjCM ι n N z.2),
        continuous_fst.prodMk ((Work.RatHurewicz.famProjCM ι n N).continuous.comp continuous_snd)⟩
    have hqfun : ⇑q = (fun z : Work.Serre.Sph 1 × Work.RatHurewicz.famTotal ι N =>
        (z.1, (⇑(Work.RatHurewicz.famProjCM ι n N)) z.2)) := rfl
    have hq : IsCoveringMap ⇑q := by
      rw [hqfun]
      exact prodMapCovering (Work.RatHurewicz.famIsCoveringMap (ι := ι) (n := n) (N := N))
    have hcard : ∀ z : Work.Serre.Sph 1 × Work.RatHurewicz.famSpace ι n N,
        Nat.card ↥(⇑q ⁻¹' {z}) = ∏ i, n i := by
      intro z
      rw [hqfun]
      exact prodMapFiberCard (⇑(Work.RatHurewicz.famProjCM ι n N)) (∏ i, n i)
        (fun x => Work.RatHurewicz.famCardFibre x) z
    exact transferRangeTwo q hq (∏ i, n i)
      (Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (NeZero.ne (n i))) hcard N htot t ht2 htN

end

end Work.Rat.RankOneC1
