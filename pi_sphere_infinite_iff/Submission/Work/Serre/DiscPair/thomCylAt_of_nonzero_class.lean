import Mathlib
import Submission.Work.Serre.DiscPair.thomCylAt_of_contractible
import Submission.Work.Serre.ThomCylDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Serre.DiscPair

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- **The Thom isomorphism for the mapping cylinder pair, for any nonzero class.**

Let `q : X → B` be a Serre fibration whose base is path connected and weakly contractible and whose
fibre `F = q⁻¹{b₀}` is path connected with rational homology concentrated in degree `r`, equal to
`ℚ` there (through degree `N`).  Then *every* nonzero relative class
`V ∈ H^{r+1}(cyl q, range (cylIncl q); ℚ)` is a Thom class: its mixed cup product with the pullback
along the retraction of the mapping cylinder is an isomorphism in the range `m + r + 1 ≤ N + 1`.

The two ingredients are the concentration of the pair `(cyl q, range (cylIncl q))` proved in
`Work.Serre.DiscPair.cylPair_concentrated` (which exhibits `H^{r+1}` of the pair as a line, and
makes all other degrees in the range vanish) and the connectedness of `B` (so that `H^0(B;ℚ) ≅ ℚ`
and `H^m(B;ℚ) = 0` for `m > 0`).  In degree `m = 0` the composite is a nonzero linear map between
one-dimensional `ℚ`-vector spaces (it sends the unit class of `B` to `V`, up to the degree cast
`mixedCupC_oneH_zeroQ`, hence is nonzero since `V ≠ 0`); in degrees `m ≥ 1` both source and target
vanish. -/
theorem thomCylAt_of_nonzero_class {B : Type} [TopologicalSpace B] {X : Type} [TopologicalSpace X]
    (q : C(X, B)) (b₀ : B) (r N : ℕ) (hr : 1 ≤ r)
    (hq : Work.StemsB.IsSerreFibration q)
    (hB : PathConnectedSpace B)
    (hBc : ∀ i : ℕ, Subsingleton (HomotopyGroup (Fin i) B b₀))
    (hX : PathConnectedSpace X)
    (hpc : PathConnectedSpace (Work.StemsB.fibre q b₀))
    (hvan : ∀ t : ℕ, 0 < t → t ≠ r → t ≤ N →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b₀)) t))
    (hgen : Nonempty (Work.Serre.ratH (TopCat.of (Work.StemsB.fibre q b₀)) r ≅ ModuleCat.of ℚ ℚ))
    (V : Work.Thom.RelCoh ℚ (r + 1) (Work.Serre.cyl q) (Set.range (Work.Serre.cylIncl q)))
    (hV : V ≠ 0) :
    ∀ m : ℕ, m + r + 1 ≤ N + 1 → CategoryTheory.IsIso (ModuleCat.ofHom
      (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl q)) m (r + 1))).flip V ∘ₗ
        (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ m).hom)) := by
  classical
  rcases Nat.lt_or_ge N r with hNr | hrN
  · -- nothing to prove: the range condition is empty
    intro m hm
    exfalso
    omega
  · -- the fibre data pass to the total space, and the pair of the cylinder is concentrated
    obtain ⟨hXvan, hXgen⟩ :=
      ratH_of_contractible_base q b₀ r N hr hrN hq hB hBc hX hpc hvan hgen
    have hBacyc : Work.Serre.RatAcyclic B := ratAcyclic_of_weaklyContractible_base b₀ hB hBc
    obtain ⟨hMvan, hMgen⟩ := cylPair_concentrated q r N hr hBacyc hX hXvan hXgen
    -- `H^{r+1}` of the pair is a line
    obtain ⟨eU⟩ := hMgen
    -- `H⁰` of the base is a line (the base is path connected)
    have hB0 : Nonempty (Work.Thom.Coh ℚ 0 B ≅ ModuleCat.of ℚ ℚ) :=
      (Work.Serre.ratCoh_ratH_iso_rat (TopCat.of B) 0).mpr
        (Work.Serre.ratH_zero_of_pathConnected B)
    -- and so is `H^{0 + (r+1)}` of the pair, by the degree cast
    have hgen0 : Nonempty (Work.Thom.RelCoh ℚ (0 + (r + 1)) (Work.Serre.cyl q)
        (Set.range (Work.Serre.cylIncl q)) ≅ ModuleCat.of ℚ ℚ) :=
      ⟨eqToIso (congrArg (fun n => Work.Thom.RelCoh ℚ n (Work.Serre.cyl q)
        (Set.range (Work.Serre.cylIncl q))) (Nat.zero_add (r + 1))) ≪≫ eU⟩
    -- a class that is carried to a nonzero class by a degree cast is nonzero
    have cast_ne : ∀ {a b : ℕ} (h : a = b) (x : Work.Thom.RelCoh ℚ a (Work.Serre.cyl q)
        (Set.range (Work.Serre.cylIncl q))), x ≠ 0 → (h ▸ x) ≠ 0 := by
      intro a b h x hx
      cases h
      exact hx
    intro m hm
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · -- ## degree `0`: a nonzero map between lines
      subst hm0
      have hφne : (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl q)) 0 (r + 1)).flip V) ∘ₗ
          (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ 0).hom) ≠ 0 := by
        intro h0
        have hh0 : ((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl q)) 0 (r + 1)).flip V)
            ((Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ 0).hom
              (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of B)))) = 0 :=
          LinearMap.congr_fun h0 _
        rw [CohMap_oneH_rat (Work.Serre.cylRetract q)] at hh0
        have hh1 : (Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl q)) 0 (r + 1))
            (Work.Cohomology.oneH ℚ (TopCat.toSSet.obj (TopCat.of (Work.Serre.cyl q))))
            V = 0 := hh0
        rw [Work.StemsB.Rat.mixedCupC_oneH_zeroQ (Set.range (Work.Serre.cylIncl q)) (r + 1) V]
          at hh1
        exact cast_ne (Nat.zero_add (r + 1)).symm V hV hh1
      exact isIso_ofHom_of_linearEquiv_rat
        (V := ↥(Work.Thom.Coh ℚ 0 B))
        (W := ↥(Work.Thom.RelCoh ℚ (0 + (r + 1)) (Work.Serre.cyl q)
          (Set.range (Work.Serre.cylIncl q))))
        (Classical.choice hB0).toLinearEquiv (Classical.choice hgen0).toLinearEquiv
        (((Work.Thom.mixedCupC ℚ (Set.range (Work.Serre.cylIncl q)) 0 (r + 1)).flip V) ∘ₗ
          (Work.Thom.CohMap (Work.Serre.cylRetract q) ℚ 0).hom) hφne
    · -- ## degrees `≥ 1`: both sides vanish
      haveI hz1 : Subsingleton ↥(Work.Thom.Coh ℚ m B) :=
        ModuleCat.subsingleton_of_isZero (Work.Serre.isZero_ratCoh_of_isZero_ratH
          (Work.Serre.serreE0Range B b₀ m (fun k _ => hBc k) m hmpos (by omega)))
      haveI hz2 : Subsingleton ↥(Work.Thom.RelCoh ℚ (m + (r + 1)) (Work.Serre.cyl q)
          (Set.range (Work.Serre.cylIncl q))) :=
        ModuleCat.subsingleton_of_isZero (hMvan (m + (r + 1)) (by omega) (by omega))
      exact isIso_ofHom_of_subsingleton _

end

end Work.Serre.DiscPair
