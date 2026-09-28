import Mathlib
import Submission.Work.Stems.cycleLiftOfIso
import Submission.Work.RatHurewicz.S3Inputs
import Submission.Work.StemsB.killToFgModel
import Submission.Work.Cohomology.Pullback

/-!
# `RangeModelRatAcyclic` from its finitely generated case (local to area STEMS)

The main theorem of `Work.RatHurewicz.RangeModelRatAcyclic` — the rational homology of a range model
of `K(A,k)` vanishes in the degrees `k < j ≤ 2k-1` — is reduced here to its finitely generated case
`hfg`, using the *local* form `Work.Stems.CycleFiniteModelLocal` of the compactness input.

The argument is the one of `Work.StemsB.rangeModelRatAcyclic_of_fgCase`: a rational cycle `z` of the
range model `Z` is (up to a boundary) the pushforward of a cycle `w` of a finite model `W`
(`CycleFiniteModelLocal`); the map `W → Z` factors through a range model `Z'` of `K(A,k)` with `A`
finitely generated (`Work.StemsB.killToFgModel`); there `w` becomes a boundary (`hfg`), and pushing
that boundary back to `Z` exhibits `z` as a boundary.

The file is self-contained in area STEMS: the three bookkeeping lemmas about `chainMap` that the
assembly needs are proved here (they are restatements of lemmas living in the `StemsB` modules,
which have to be avoided because the import closure of `Submission.Work.StemsB.cycleFiniteModel`
does not build).
-/

namespace Work.Stems

open CategoryTheory CategoryTheory.Limits

noncomputable section

set_option maxHeartbeats 1000000

/-! ## Bookkeeping lemmas about the singular chain map -/

/-- `chainMap` is functorial. -/
theorem rmlChainMap_comp {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(X, Y)) (g : C(Y, Z)) :
    Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Z) (TopCat.ofHom (g.comp f))
      = Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)
        ≫ Work.Cohomology.chainMap ℚ (TopCat.of Y) (TopCat.of Z) (TopCat.ofHom g) := by
  simp only [Work.Cohomology.chainMap]
  rw [show TopCat.ofHom (g.comp f) = TopCat.ofHom f ≫ TopCat.ofHom g from rfl]
  exact CategoryTheory.Functor.map_comp _ _ _

/-- `chainMap` commutes with the differential (on elements). -/
theorem rmlChainMap_d_apply {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (i j : ℕ) (x : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X i) :
    (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)).f j
      ((Work.Cohomology.singularChains ℚ (TopCat.of X)).d i j x)
    = (Work.Cohomology.singularChains ℚ (TopCat.of Y)).d i j
      ((Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)).f i x) := by
  have h := congrArg (fun (m : (Work.Cohomology.singularChains ℚ (TopCat.of X)).X i ⟶
      (Work.Cohomology.singularChains ℚ (TopCat.of Y)).X j) => ModuleCat.Hom.hom m x)
    (HomologicalComplex.Hom.comm (Work.Cohomology.chainMap ℚ (TopCat.of X) (TopCat.of Y)
      (TopCat.ofHom f)) i j)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h.symm

/-- A cycle in degree `j` is a boundary as soon as `H_j` vanishes. -/
theorem rml_exists_boundary_of_isZero_homology (K : ChainComplex (ModuleCat ℚ) ℕ) (j : ℕ)
    (hprev : (ComplexShape.down ℕ).prev j = j + 1)
    (hnext : (ComplexShape.down ℕ).next j = j - 1)
    (h : IsZero (K.homology j)) (x : K.X j) (hx : K.d j (j - 1) x = 0) :
    ∃ u : K.X (j + 1), K.d (j + 1) j u = x := by
  have : K.HasHomology j := inferInstance
  have hex : K.ExactAt j := (HomologicalComplex.exactAt_iff_isZero_homology K j).mpr h
  have hex' : (K.sc' (j + 1) j (j - 1)).Exact :=
    (HomologicalComplex.exactAt_iff' K (j + 1) j (j - 1) hprev hnext).mp hex
  have hrange := (ShortComplex.moduleCat_exact_iff_range_eq_ker (K.sc' (j + 1) j (j - 1))).mp hex'
  have hxker : x ∈ LinearMap.ker (ModuleCat.Hom.hom (K.sc' (j + 1) j (j - 1)).g) := by
    show ModuleCat.Hom.hom (K.sc' (j + 1) j (j - 1)).g x = 0
    show K.d j (j - 1) x = 0
    exact hx
  rw [← hrange] at hxker
  obtain ⟨u, hu⟩ := hxker
  exact ⟨u, hu⟩

/-- **The rational homology of a range model of `K(A,k)` vanishes below `2k`**, from its finitely
generated case `hfg` and the compactness input `hcycle` (the local form
`Work.Stems.CycleFiniteModelLocal` of `Work.StemsB.CycleFiniteModel`). -/
theorem rangeModelRatAcyclicLocal
    (hcycle : Work.Stems.CycleFiniteModelLocal)
    (hfg : ∀ (A : Type) [AddCommGroup A] [Module.Finite ℤ A] (k N : ℕ) (hk : 2 ≤ k)
      (hN : 2 * k - 1 ≤ N) (X : Type) [TopologicalSpace X] (pt : X),
      Work.Serre.IsEMSpaceUpTo A k (by omega) N X pt →
      ∀ i : ℕ, k < i → i ≤ 2 * k - 1 →
        CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) i)) :
    Work.RatHurewicz.RangeModelRatAcyclic := by
  intro k hk Z _ z₀ hmodel j hkj hj
  have hZ : ∀ i : ℕ, i ≤ 2 * k - 1 → i ≠ k → Subsingleton (HomotopyGroup (Fin i) Z z₀) := hmodel
  have hprev : (ComplexShape.down ℕ).prev j = j + 1 :=
    ComplexShape.prev_eq' _ (show (ComplexShape.down ℕ).Rel (j + 1) j from rfl)
  have hnext : (ComplexShape.down ℕ).next j = j - 1 :=
    ComplexShape.next_eq' _ (show (ComplexShape.down ℕ).Rel j (j - 1) from by
      show (j - 1) + 1 = j
      omega)
  refine (HomologicalComplex.exactAt_iff_isZero_homology
    (Work.Cohomology.singularChains ℚ (TopCat.of Z)) j).mp ?_
  refine (HomologicalComplex.exactAt_iff'
    (Work.Cohomology.singularChains ℚ (TopCat.of Z)) (j + 1) j (j - 1) hprev hnext).mpr ?_
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  ext x
  constructor
  · rintro ⟨y, hy⟩
    show (Work.Cohomology.singularChains ℚ (TopCat.of Z)).d j (j - 1) x = 0
    have hy' : (Work.Cohomology.singularChains ℚ (TopCat.of Z)).d (j + 1) j y = x := hy
    rw [← hy']
    have h := congrArg (fun (m : (Work.Cohomology.singularChains ℚ (TopCat.of Z)).X (j + 1) ⟶
        (Work.Cohomology.singularChains ℚ (TopCat.of Z)).X (j - 1)) => ModuleCat.Hom.hom m y)
      (HomologicalComplex.d_comp_d (Work.Cohomology.singularChains ℚ (TopCat.of Z)) (j + 1) j
        (j - 1))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
    exact h
  · intro hx
    -- a cycle of `Z`, pushed from a cycle of a finite model `W` (up to a boundary in `Z`)
    have hx0 : (Work.Cohomology.singularChains ℚ (TopCat.of Z)).d j (j - 1) x = 0 := hx
    obtain ⟨W, instW, w₀, φ, w, b, hwcyc, hwmap, hW0, hWk⟩ :=
      hcycle k j hk hkj hj Z z₀ hZ x hx0
    -- the finite model maps through a range model with finitely generated `π_k`
    obtain ⟨A, instA, instFin, Z', instZ', z₀', ψ, χ, hfac, hEM⟩ :=
      Work.StemsB.killToFgModel k hk Z z₀ hZ W w₀ φ hW0 hWk
    have hzero : IsZero (Work.Serre.ratH (TopCat.of Z') j) :=
      @hfg A instA instFin k (2 * k - 1) hk le_rfl Z' instZ' z₀' hEM j hkj hj
    have hχψ : Work.Cohomology.chainMap ℚ (TopCat.of W) (TopCat.of Z) (TopCat.ofHom φ)
        = Work.Cohomology.chainMap ℚ (TopCat.of W) (TopCat.of Z') (TopCat.ofHom χ)
          ≫ Work.Cohomology.chainMap ℚ (TopCat.of Z') (TopCat.of Z) (TopCat.ofHom ψ) := by
      rw [← hfac]
      exact rmlChainMap_comp χ ψ
    have hwcyc' : (Work.Cohomology.singularChains ℚ (TopCat.of Z')).d j (j - 1)
        ((Work.Cohomology.chainMap ℚ (TopCat.of W) (TopCat.of Z') (TopCat.ofHom χ)).f j w) = 0 := by
      rw [← rmlChainMap_d_apply χ j (j - 1) w, hwcyc]
      exact map_zero _
    -- the pushed cycle is a boundary in the finitely generated model
    obtain ⟨u, hu⟩ := rml_exists_boundary_of_isZero_homology
      (Work.Cohomology.singularChains ℚ (TopCat.of Z')) j hprev hnext hzero
      ((Work.Cohomology.chainMap ℚ (TopCat.of W) (TopCat.of Z') (TopCat.ofHom χ)).f j w) hwcyc'
    -- push the boundary back down to `Z`
    refine ⟨(Work.Cohomology.chainMap ℚ (TopCat.of Z') (TopCat.of Z) (TopCat.ofHom ψ)).f (j + 1) u
      - b, ?_⟩
    show (Work.Cohomology.singularChains ℚ (TopCat.of Z)).d (j + 1) j
      ((Work.Cohomology.chainMap ℚ (TopCat.of Z') (TopCat.of Z) (TopCat.ofHom ψ)).f (j + 1) u
        - b) = x
    rw [map_sub]
    have hψ : (Work.Cohomology.singularChains ℚ (TopCat.of Z)).d (j + 1) j
        ((Work.Cohomology.chainMap ℚ (TopCat.of Z') (TopCat.of Z) (TopCat.ofHom ψ)).f (j + 1) u)
        = (Work.Cohomology.chainMap ℚ (TopCat.of W) (TopCat.of Z) (TopCat.ofHom φ)).f j w := by
      rw [← rmlChainMap_d_apply ψ (j + 1) j u, hu]
      rw [show (Work.Cohomology.chainMap ℚ (TopCat.of Z') (TopCat.of Z) (TopCat.ofHom ψ)).f j
          ((Work.Cohomology.chainMap ℚ (TopCat.of W) (TopCat.of Z') (TopCat.ofHom χ)).f j w)
          = (Work.Cohomology.chainMap ℚ (TopCat.of W) (TopCat.of Z) (TopCat.ofHom φ)).f j w from by
        rw [hχψ, HomologicalComplex.comp_f]
        rfl]
    rw [hψ, hwmap]
    abel

end

end Work.Stems
