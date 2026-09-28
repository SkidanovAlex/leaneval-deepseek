import Mathlib
import Submission.Work.Rat.RankOneEMDefs
import Submission.Work.Rat.RankOneC1.extendsAlongTowerB
import Submission.Work.Rat.RankOneC1.sphereProd_rangeModel
import Submission.Work.Rat.RankOneC1.fgCase
import Submission.Work.Rat.RankOneC1.cycleSupport
import Submission.Work.Stems.rangeModelRatAcyclicLocal
import Submission.Work.Rat.U.EMVanOne
import Submission.Work.Rat.RankOneC1.exists_killedModel_based
import Submission.Work.Rat.RankOneC1.fgSubgroup_rank_le_one_of
import Submission.Work.Rat.RankOneC1.hurewiczKerTorsion_one_abelian

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.Rat.RankOneC1Ab` — the rank-one `K(A,1)` vanishing

`Work.Rat.RankOneC1Ab` (see `Submission/Work/Rat/RankOneEMDefs.lean`): a space whose `π₀` is
trivial, whose `π₁` is abelian, with `H₁(-;ℚ) ≅ ℚ` and `π_i = 0` for `2 ≤ i ≤ N`, has vanishing
rational homology in degrees `1 < j ≤ N - 1`.

The proof reduces to the *finitely generated* rank-one case (`Work.Rat.c1Fg`): given a rational
`(m+1)`-cycle `x` on `X` with `1 < m+1 ≤ N-1`,

1. **Support** (`Work.Rat.exists_model_of_cycle_fg`): a space `Y`, a point `y₀`, a map
   `φ : Y → X` with `φ y₀ = x₀` and a cycle `w` on `Y` with `φ_# w = x`, `π₀(Y)` trivial and
   `π₁(Y,y₀)` finitely generated;
2. **Killing** (`Work.Rat.RankOneC1.exists_killedModel_based`): `W`, `w₀`, `ψ : W → X` and
   `κ : Y → W` with `ψ ∘ κ = φ`, `ψ w₀ = x₀`, `π₁(W,w₀)` finitely generated, `π₁(ψ)` injective and
   `π_i(W,w₀) = 0` for `2 ≤ i ≤ N`;
3. **Rank** (`Work.Rat.RankOneC1.fgSubgroup_rank_le_one_of`): the subgroup
   `H = im(π₁ ψ) ⊆ π₁(X,x₀)` is finitely generated and, since `H₁(X;ℚ) ≅ ℚ`, has torsion-free
   rank `≤ 1`: `H ≅ ℤ^r × F` with `r ≤ 1` and `F` finite;
4. **Conclusion**: `π₁(W,w₀) ≅ H` is either finite (then `Work.Serre.RangeEMVanOneFin` applies) or
   `ℤ × F` (then `Work.Rat.c1Fg` applies), so `H_{m+1}(W;ℚ) = 0`; the pulled back cycle `κ_# w` is
   a boundary in `W` and pushing it forward exhibits `x` as a boundary in `X`.
-/


namespace Work.Rat

open CategoryTheory CategoryTheory.Limits

/-- A path connected space has trivial `π₀`. -/
theorem subsingleton_pi_zero_of_pathConnected {X : Type} [TopologicalSpace X] (x : X)
    [PathConnectedSpace X] : Subsingleton (HomotopyGroup (Fin 0) X x) := by
  have hZ : Subsingleton (ZerothHomotopy X) :=
    (pathConnectedSpace_iff_zerothHomotopy).mp inferInstance |>.2
  exact ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (X := X) (x := x)).injective
    (Subsingleton.elim _ _)⟩

/-- **`IsEMSpaceUpTo` from a multiplicative equivalence of the coefficient group with `π₁`.** -/
theorem isEMSpaceUpTo_of_mulEquiv_piOne {A : Type} [AddCommGroup A] {W : Type} [TopologicalSpace W]
    (w₀ : W) (N : ℕ) (h0 : Subsingleton (HomotopyGroup (Fin 0) W w₀))
    (hvan : ∀ i : ℕ, 2 ≤ i → i ≤ N → Subsingleton (HomotopyGroup (Fin i) W w₀))
    (e : HomotopyGroup (Fin 1) W w₀ ≃* Multiplicative A) :
    Work.Serre.IsEMSpaceUpTo A 1 (by norm_num) N W w₀ := by
  haveI : Nonempty (Fin 1) := ⟨⟨0, by norm_num⟩⟩
  refine ⟨⟨e⟩, ?_⟩
  intro i hi hc
  rcases lt_or_ge i 2 with h2 | h2
  · have hi0 : i = 0 := by omega
    subst hi0
    exact h0
  · rcases hc with hc | hc
    · omega
    · exact hvan i h2 hc

/-- **The reduction, given the two remaining inputs.** -/
theorem rankOneC1Ab_of
    (hKill : ∀ {Y X : Type} [TopologicalSpace Y] [TopologicalSpace X]
      (y₀ : Y) (x₀ : X) (φ : C(Y, X)), φ y₀ = x₀ → ∀ (N : ℕ), PathConnectedSpace Y →
      (∀ i : ℕ, 2 ≤ i → i ≤ N → ∀ x : X, Subsingleton (HomotopyGroup (Fin i) X x)) →
      Group.FG (HomotopyGroup (Fin 1) Y y₀) →
      ∃ (W : Type) (_ : TopologicalSpace W) (w₀ : W) (ψ : C(W, X)) (κ : C(Y, W)),
        PathConnectedSpace W ∧ (∀ y : Y, ψ (κ y) = φ y) ∧ ψ w₀ = x₀ ∧
        Group.FG (HomotopyGroup (Fin 1) W w₀) ∧
        Function.Injective (Work.Serre.piMapN ψ 1 w₀) ∧
        (∀ i : ℕ, 2 ≤ i → i ≤ N → Subsingleton (HomotopyGroup (Fin i) W w₀)))
    (hRank : ∀ {X : Type} [TopologicalSpace X] [PathConnectedSpace X] (x₀ : X),
      (∀ a b : HomotopyGroup (Fin 1) X x₀, a * b = b * a) →
      Nonempty (Work.Serre.ratH (TopCat.of X) 1 ≅ ModuleCat.of ℚ ℚ) →
      ∀ (H : Subgroup (HomotopyGroup (Fin 1) X x₀)) [Group.FG H],
        ∃ (r : ℕ) (F : Type) (_ : AddCommGroup F) (_ : Finite F), r ≤ 1 ∧
          Nonempty (Additive H ≃+ (Fin r → ℤ) × F)) :
    Work.Rat.RankOneC1Ab := by
  intro N X _ x₀ h0 hcomm hgen hvan j hj1 hjN
  haveI : Nonempty (Fin 1) := ⟨⟨0, by norm_num⟩⟩
  -- Reindex: write `j = m + 1`, so that `j - 1` is definitionally `m`.
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  haveI hXpc : PathConnectedSpace X :=
    Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero x₀ h0
  have hXall : ∀ i : ℕ, 2 ≤ i → i ≤ N → ∀ x : X, Subsingleton (HomotopyGroup (Fin i) X x) := by
    intro i hi2 hiN x
    exact Work.Serre.RangeOne.subsingleton_homotopyGroup_of_joined'
      (PathConnectedSpace.joined x₀ x) i (by omega) (hvan i hi2 hiN)
  -- It suffices to show that every rational `(m+1)`-cycle is a boundary.
  set K := Work.Cohomology.singularChains ℚ (TopCat.of X) with hK
  have hprev : (ComplexShape.down ℕ).prev (m + 1) = m + 1 + 1 :=
    ComplexShape.prev_eq' _ (show (ComplexShape.down ℕ).Rel (m + 1 + 1) (m + 1) from rfl)
  have hnext : (ComplexShape.down ℕ).next (m + 1) = (m + 1) - 1 :=
    ComplexShape.next_eq' _ (show (ComplexShape.down ℕ).Rel (m + 1) ((m + 1) - 1) from by
      show ((m + 1) - 1) + 1 = m + 1
      omega)
  refine (HomologicalComplex.exactAt_iff_isZero_homology K (m + 1)).mp ?_
  refine (HomologicalComplex.exactAt_iff' K (m + 1 + 1) (m + 1) ((m + 1) - 1)
    hprev hnext).mpr ?_
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  ext x
  constructor
  · rintro ⟨y, hy⟩
    show K.d (m + 1) m x = 0
    have hy' : K.d (m + 1 + 1) (m + 1) y = x := hy
    rw [← hy']
    have h := congrArg (fun (p : K.X (m + 1 + 1) ⟶ K.X ((m + 1) - 1)) => ModuleCat.Hom.hom p y)
      (HomologicalComplex.d_comp_d K (m + 1 + 1) (m + 1) ((m + 1) - 1))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact h
  · intro hx
    have hx0 : K.d (m + 1) m x = 0 := hx
    -- ## Step 1: a model `Y` of the cycle with finitely generated `π₁`
    obtain ⟨Y, instY, y₀, φ, w, hφy, hY0, hwd, hwmap, hYfg⟩ :=
      Work.Rat.exists_model_of_cycle_fg x₀ m h0 x hx0
    letI : TopologicalSpace Y := instY
    -- ## Step 2: kill `ker π₁(φ)` and `π₂, …, π_N`
    haveI hYpc : PathConnectedSpace Y :=
      Work.RatHurewicz.pathConnectedSpace_of_subsingleton_pi_zero y₀ hY0
    obtain ⟨W, instW, w₀, ψ, κ, hWpc, hψκ, hψw, hWfg, hψinj, hWvan⟩ :=
      hKill y₀ x₀ φ hφy N hYpc hXall hYfg
    letI : TopologicalSpace W := instW
    subst hψw
    -- ## Step 3: pull the cycle back along `κ`
    set w' : (Work.Cohomology.singularChains ℚ (TopCat.of W)).X (m + 1) :=
      (Work.Cohomology.chainMap ℚ (TopCat.of Y) (TopCat.of W) (TopCat.ofHom κ)).f (m + 1) w
      with hw'def
    have hw'cyc : (Work.Cohomology.singularChains ℚ (TopCat.of W)).d (m + 1) m w' = 0 := by
      rw [hw'def, ← Work.Stems.rmlChainMap_d_apply κ (m + 1) m w, hwd]
      exact map_zero _
    have hmap : (Work.Cohomology.chainMap ℚ (TopCat.of W) (TopCat.of X)
        (TopCat.ofHom ψ)).f (m + 1) w' = x := by
      rw [hw'def, ← hwmap]
      have hfun : ψ.comp κ = φ := ContinuousMap.ext hψκ
      have hcomp : Work.Cohomology.chainMap ℚ (TopCat.of Y) (TopCat.of X) (TopCat.ofHom φ)
          = Work.Cohomology.chainMap ℚ (TopCat.of Y) (TopCat.of W) (TopCat.ofHom κ)
            ≫ Work.Cohomology.chainMap ℚ (TopCat.of W) (TopCat.of X) (TopCat.ofHom ψ) := by
        rw [← Work.Stems.rmlChainMap_comp κ ψ, hfun]
      rw [hcomp, HomologicalComplex.comp_f]
      rfl
    -- ## Step 4: the finitely generated subgroup `H = im(π₁ ψ) ⊆ π₁(X, ψ w₀)`
    haveI : Group.FG (HomotopyGroup (Fin 1) W w₀) := hWfg
    obtain ⟨F, hF⟩ := Work.Serre.piMapN_monoidHom ψ 1 w₀
    have hinjF : Function.Injective F := by
      intro a b hab
      apply hψinj
      rw [← hF a, ← hF b, hab]
    haveI : Group.FG ↥F.range := Group.fg_of_surjective F.rangeRestrict_surjective
    obtain ⟨r, Ff, instFf, hFinFf, hr1, heH⟩ := hRank (ψ w₀) hcomm hgen F.range
    letI : AddCommGroup Ff := instFf
    haveI : Finite Ff := hFinFf
    obtain ⟨eH⟩ := heH
    have hinjR : Function.Injective F.rangeRestrict := by
      intro a b hab
      refine hinjF ?_
      simpa using congrArg Subtype.val hab
    have eW : HomotopyGroup (Fin 1) W w₀ ≃* ↥F.range :=
      MulEquiv.ofBijective F.rangeRestrict
        ⟨hinjR, MonoidHom.rangeRestrict_surjective F⟩
    have hW0 : Subsingleton (HomotopyGroup (Fin 0) W w₀) :=
      subsingleton_pi_zero_of_pathConnected w₀
    -- ## Step 5: `π₁(W,w₀) ≅ H` is finite or `ℤ × F`, so `H_{m+1}(W;ℚ) = 0`
    have hzero : IsZero (Work.Serre.ratH (TopCat.of W) (m + 1)) := by
      interval_cases r
      · -- `r = 0`: `π₁(W,w₀)` is finite
        haveI : Subsingleton (Fin 0 → ℤ) := ⟨fun f g => funext fun i => i.elim0⟩
        have eTot : Additive (HomotopyGroup (Fin 1) W w₀)
            ≃+ (Fin 0 → ℤ) × Ff := (MulEquiv.toAdditive eW).trans eH
        haveI : Finite (HomotopyGroup (Fin 1) W w₀) :=
          Finite.of_equiv ((Fin 0 → ℤ) × Ff) eTot.toEquiv.symm
        haveI : Fintype (HomotopyGroup (Fin 1) W w₀) :=
          Fintype.ofFinite (HomotopyGroup (Fin 1) W w₀)
        have hWcomm : ∀ a b : HomotopyGroup (Fin 1) W w₀, a * b = b * a := by
          intro a b
          refine eW.injective ?_
          rw [map_mul, map_mul]
          exact Subtype.ext (by simpa using hcomm (eW a) (eW b))
        exact Work.Serre.serreRangeEMVanOneFin_noC0 Work.Serre.serreC3Finite N W w₀ hW0
          hWcomm ⟨inferInstance⟩ hWvan (m + 1) (by omega) (by omega)
      · -- `r = 1`: `π₁(W,w₀) ≅ ℤ × F`
        haveI : Fintype Ff := Fintype.ofFinite Ff
        have hE : HomotopyGroup (Fin 1) W w₀ ≃* Multiplicative ((Fin 1 → ℤ) × Ff) :=
          eW.trans (AddEquiv.toMultiplicative eH)
        have hWEM0 : Work.Serre.IsEMSpaceUpTo ((Fin 1 → ℤ) × Ff) 1 (by norm_num) N W w₀ :=
          isEMSpaceUpTo_of_mulEquiv_piOne w₀ N hW0 hWvan hE
        have hWEM : Work.Serre.IsEMSpaceUpTo (ℤ × Ff) 1 (by norm_num) N W w₀ :=
          Work.RatHurewicz.isEMSpaceUpTo_of_addEquiv (by norm_num) w₀ hWEM0
            (AddEquiv.prodCongr (AddEquiv.funUnique (Fin 1) ℤ) (AddEquiv.refl Ff))
        exact Work.Rat.c1Fg (F := Ff) N w₀ hWEM (m + 1) (by omega) (by omega)
    -- ## Step 6: `w'` is a boundary in `W`, hence `x` is a boundary in `X`
    obtain ⟨u, hu⟩ := Work.Stems.rml_exists_boundary_of_isZero_homology
      (Work.Cohomology.singularChains ℚ (TopCat.of W)) (m + 1) hprev hnext hzero w' hw'cyc
    refine ⟨(Work.Cohomology.chainMap ℚ (TopCat.of W) (TopCat.of X)
      (TopCat.ofHom ψ)).f (m + 2) u, ?_⟩
    show (Work.Cohomology.singularChains ℚ (TopCat.of X)).d (m + 1 + 1) (m + 1)
      ((Work.Cohomology.chainMap ℚ (TopCat.of W) (TopCat.of X) (TopCat.ofHom ψ)).f
        (m + 1 + 1) u) = x
    rw [← Work.Stems.rmlChainMap_d_apply ψ (m + 1 + 1) (m + 1) u, hu]
    exact hmap

/-- **Serre's rank-one `K(A,1)` vanishing**: the target of this file, obtained from the reduction
`rankOneC1Ab_of` by the killing step `Work.Rat.RankOneC1.exists_killedModel_based`, the rank bound
`Work.Rat.RankOneC1.fgSubgroup_rank_le_one_of` and the degree-one Hurewicz theorem modulo torsion
`Work.Rat.RankOneC1.hurewiczKerTorsion_one_abelian`. -/
theorem rankOneC1Ab : Work.Rat.RankOneC1Ab :=
  rankOneC1Ab_of
    (fun {Y X} instY instX y₀ x₀ φ hφy N hYpc hXall hYfg => by
      haveI : PathConnectedSpace Y := hYpc
      exact Work.Rat.RankOneC1.exists_killedModel_based y₀ x₀ φ hφy N hXall hYfg)
    (fun {X} instX hXpc x₀ hcomm hgen H hH => by
      haveI : Group.FG H := hH
      exact Work.Rat.RankOneC1.fgSubgroup_rank_le_one_of
        (fun {X} instX hXpc x₀ hcomm =>
          Work.Rat.RankOneC1.hurewiczKerTorsion_one_abelian x₀ hcomm)
        x₀ hcomm hgen H)

end Work.Rat
