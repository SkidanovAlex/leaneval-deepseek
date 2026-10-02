import Mathlib
import Submission.Work.Orient.Boundary
import Submission.Work.Orient.Boundary.HalfVanishing
import Submission.Work.Orient.Boundary.HalfRestrictIso
import Submission.Work.Orient.Boundary.HalfCover
import Submission.Work.Orient.Port.Hatcher

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Uniqueness of a relative class over a compact set of the interior (half-space model)

This file proves `Work.Orient.HalfCompactZeroProp` and, in the form in which it was requested, the
theorem `Work.Orient.Boundary.HalfCompactZero`: for a compact `C^1` manifold `W` with boundary
modelled on the half-space, a compact subset `A` of the interior and a relative class
`β ∈ H_{n+1}(W, W∖A)` whose localisation vanishes at every point of `A`, one has `β = 0`.  This is
the half-space analogue of Hatcher 3.27 (a) (uniqueness), whose Euclidean version is
`Work.Orient.Port.compactZero`.

The route is the literal translation of the Euclidean proof:

1. `Work.Orient.Port.relChain_lift` (generic, no chart) lifts `β` to a chain whose boundary is
   supported in a compact set `S ⊆ Aᶜ`;
2. `Work.Orient.Boundary.HalfCover` covers `A` by finitely many coordinate half-balls centred at
   points of `A` and avoiding the closed set `S ∪ ∂W` — the second part forces every piece to lie in
   the *interior* of `W`, which is exactly the side condition of
   `Work.Orient.Boundary.HalfRestrictIso`, and lets the chain be viewed in the relative complex of
   the union;
3. `halfUnionZero` is the finite-union case, by Mayer–Vietoris (`Work.ThomBordism.excludedMV`), the
   localisation isomorphism out of a half-ball of the interior
   (`Work.Orient.Boundary.HalfRestrictIso`) and the vanishing above the dimension
   (`Work.Orient.Boundary.HalfVanishing`);
4. `halfExistsLift` assembles 1.–3. into the lift of `β` to the union of the pieces;
5. `HalfCompactZero` concludes `β = 0` by `halfUnionZero`, using that the centre of each piece
   belongs to `A`, where `β` (hence the lift) dies.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.Orient.Boundary

noncomputable section

/-! ## The generic restriction maps, in the ORIENT names -/

private theorem resRelH_self (W : TopCat) (m : ℕ) {A : Set W} (h : A ⊆ A) :
    resRelH W m h = LinearMap.id :=
  Work.Orient.Port.RelHmap_self W m h

private theorem resRelH_comp' (W : TopCat) (m : ℕ) {A B C : Set W} (h₁ : A ⊆ B) (h₂ : B ⊆ C)
    (h₃ : A ⊆ C) : (resRelH W m h₁).comp (resRelH W m h₂) = resRelH W m h₃ :=
  Work.Orient.Port.RelHmap_comp' W m h₁ h₂ h₃

private theorem resRelH_point_fac (W : TopCat) (m : ℕ) {A B : Set W} (h : A ⊆ B) {x : W}
    (hxA : x ∈ A) :
    resRelH W m (Set.singleton_subset_iff.mpr (h hxA))
      = (resRelH W m (Set.singleton_subset_iff.mpr hxA)).comp (resRelH W m h) :=
  Work.Orient.Port.RelHmap_point_fac W m h hxA

private theorem RelH_empty_isZero (W : TopCat) (m : ℕ) : IsZero (RelH W m (∅ : Set W)) :=
  Work.Orient.Port.RelH_empty_isZero W m

/-! ## Uniqueness over a finite union of coordinate half-balls of the interior -/

/-- **Uniqueness for a finite union of coordinate half-balls of the interior** (Hatcher 3.27 (a),
finite-union case, half-space model): a class of `H_{n+1}(W, W∖⋃_{i∈s} K_i)` whose localisation
vanishes at the *centre* of each piece is zero.

The pieces are the coordinate half-balls `halfBallPiece (n+1) W (z i) (r i)`; they all lie in the
interior of `W` (`hint`), so that `Work.Orient.Boundary.HalfRestrictIso` applies at their centres. -/
theorem halfUnionZero (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    {ι : Type} (s : Finset ι) (z : ι → W) (r : ι → ℝ)
    (hr : ∀ i, 0 < r i) (hgood : ∀ i, halfBallGood (n + 1) W (z i) (r i))
    (hint : ∀ i, ∀ y ∈ halfBallPiece (n + 1) W (z i) (r i),
      y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (u : RelH W (n + 1) (⋃ i ∈ s, halfBallPiece (n + 1) W (z i) (r i)))
    (hu : ∀ i (hi : i ∈ s),
      resRelH W (n + 1) (Set.singleton_subset_iff.mpr
        (Set.mem_iUnion₂.mpr ⟨i, hi, mem_halfBallPiece_center (hr i)⟩)) u = 0) :
    u = 0 := by
  classical
  have key : ∀ t : Finset ι,
      ∀ u : RelH W (n + 1) (⋃ i ∈ t, halfBallPiece (n + 1) W (z i) (r i)),
        (∀ i (hi : i ∈ t),
          resRelH W (n + 1) (Set.singleton_subset_iff.mpr
            (Set.mem_iUnion₂.mpr ⟨i, hi, mem_halfBallPiece_center (hr i)⟩)) u = 0) → u = 0 := by
    intro t
    refine Finset.induction_on t ?base ?step
    · intro u _
      have heq : (⋃ i ∈ (∅ : Finset ι), halfBallPiece (n + 1) W (z i) (r i)) = (∅ : Set W) := by
        simp
      have hI : IsZero (RelH W (n + 1)
          (⋃ i ∈ (∅ : Finset ι), halfBallPiece (n + 1) W (z i) (r i))) :=
        IsZero.of_iso (RelH_empty_isZero W (n + 1))
          (eqToIso (congrArg (fun S : Set W =>
            (Work.Cohomology.relChains W Sᶜ).homology (n + 1)) heq))
      exact (ModuleCat.subsingleton_of_isZero hI).elim u 0
    · intro a t ha ih u hu
      let Ka : Set W := halfBallPiece (n + 1) W (z a) (r a)
      let L : Set W := ⋃ i ∈ t, halfBallPiece (n + 1) W (z i) (r i)
      let U : Set W := ⋃ i ∈ insert a t, halfBallPiece (n + 1) W (z i) (r i)
      have hKacpt : IsCompact Ka :=
        halfBallPiece_isCompact (n := n + 1) (z a) (r a) (hr a) (hgood a)
      have hLcpt : IsCompact L := by
        exact Finset.isCompact_biUnion t
          (fun i _ => halfBallPiece_isCompact (n := n + 1) (z i) (r i) (hr i) (hgood i))
      have hzero : IsZero (RelH W ((n + 1) + 1) (Ka ∩ L)) :=
        HalfVanishing n W (Ka ∩ L) (hKacpt.inter hLcpt) ((n + 1) + 1) (by omega)
      have hMV := (Work.ThomBordism.excludedMV (n + 1) W Ka L hKacpt.isClosed hLcpt.isClosed
        hzero).1
      have hWU : (Ka ∪ L) ⊆ U := by
        rintro y (hy | hy)
        · exact Set.mem_iUnion₂.mpr ⟨a, Finset.mem_insert_self a t, hy⟩
        · obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
          exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_insert_of_mem hi, hyi⟩
      have hUW : U ⊆ (Ka ∪ L) := by
        intro y hy
        obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.mp hy
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact Or.inl hyi
        · exact Or.inr (Set.mem_iUnion₂.mpr ⟨i, hi, hyi⟩)
      have hKaw : Ka ⊆ (Ka ∪ L) := Set.subset_union_left
      have hLw : L ⊆ (Ka ∪ L) := Set.subset_union_right
      have hKaU : Ka ⊆ U := hKaw.trans hWU
      have hLU : L ⊆ U := hLw.trans hWU
      have h₁ : resRelH W (n + 1) hKaw (resRelH W (n + 1) hWU u) = 0 := by
        have hstep : resRelH W (n + 1) hKaw (resRelH W (n + 1) hWU u)
            = resRelH W (n + 1) hKaU u :=
          LinearMap.congr_fun (resRelH_comp' W (n + 1) hKaw hWU hKaU) u
        have hker : resRelH W (n + 1)
              (Set.singleton_subset_iff.mpr (mem_halfBallPiece_center (hr a)))
              (resRelH W (n + 1) hKaU u) = 0 := by
          rw [← LinearMap.comp_apply,
            ← resRelH_point_fac W (n + 1) hKaU (mem_halfBallPiece_center (hr a))]
          rw [show Set.singleton_subset_iff.mpr (hKaU (mem_halfBallPiece_center (hr a)))
                = Set.singleton_subset_iff.mpr
                  (Set.mem_iUnion₂.mpr ⟨a, Finset.mem_insert_self a t,
                    mem_halfBallPiece_center (hr a)⟩) from Subsingleton.elim _ _]
          exact hu a (Finset.mem_insert_self a t)
        haveI : IsIso (HomologicalComplex.homologyMap (Work.Cohomology.relCokerMap W Kaᶜ
            ({z a} : Set W)ᶜ (Set.compl_subset_compl.mpr
              (Set.singleton_subset_iff.mpr (mem_halfBallPiece_center (hr a))))) (n + 1)) :=
          HalfRestrictIso n W (z a) (r a) (hr a) (hgood a) (hint a)
        have hinj : Function.Injective (resRelH W (n + 1)
            (Set.singleton_subset_iff.mpr (mem_halfBallPiece_center (hr a)))) :=
          (ModuleCat.mono_iff_injective (HomologicalComplex.homologyMap
            (Work.Cohomology.relCokerMap W Kaᶜ ({z a} : Set W)ᶜ
              (Set.compl_subset_compl.mpr
                (Set.singleton_subset_iff.mpr (mem_halfBallPiece_center (hr a))))) (n + 1))).mp
            inferInstance
        have hzero2 : resRelH W (n + 1) hKaU u = 0 := hinj (by rw [hker, map_zero])
        rw [hstep, hzero2]
      have h₂ : resRelH W (n + 1) hLw (resRelH W (n + 1) hWU u) = 0 := by
        have hstep : resRelH W (n + 1) hLw (resRelH W (n + 1) hWU u)
            = resRelH W (n + 1) hLU u :=
          LinearMap.congr_fun (resRelH_comp' W (n + 1) hLw hWU hLU) u
        rw [hstep]
        refine ih (resRelH W (n + 1) hLU u) ?_
        intro i hi
        rw [← LinearMap.comp_apply, ← resRelH_point_fac W (n + 1) hLU
          (Set.mem_iUnion₂.mpr ⟨i, hi, mem_halfBallPiece_center (hr i)⟩)]
        rw [show Set.singleton_subset_iff.mpr
              (hLU (Set.mem_iUnion₂.mpr ⟨i, hi, mem_halfBallPiece_center (hr i)⟩))
              = Set.singleton_subset_iff.mpr (Set.mem_iUnion₂.mpr
                ⟨i, Finset.mem_insert_of_mem hi, mem_halfBallPiece_center (hr i)⟩)
              from Subsingleton.elim _ _]
        exact hu i (Finset.mem_insert_of_mem hi)
      have huW0 : resRelH W (n + 1) hWU u = 0 := hMV (resRelH W (n + 1) hWU u) h₁ h₂
      have hback : resRelH W (n + 1) hUW (resRelH W (n + 1) hWU u) = u := by
        rw [← LinearMap.comp_apply, resRelH_comp' W (n + 1) hUW hWU (hUW.trans hWU),
          resRelH_self W (n + 1) (hUW.trans hWU), LinearMap.id_apply]
      rw [← hback, huW0, map_zero]
  exact key s u hu

/-! ## The lift of a relative class to a union of coordinate half-balls -/

open scoped Simplicial in
/-- **The lift of a relative class to a fine union of coordinate half-balls of the interior.**

For a compact set `A` of the interior of `W` and `β ∈ H_{n+1}(W, W∖A)` there is a finite family of
coordinate half-balls centred at points of `A`, covering `A`, avoiding `∂W`, such that `β` is the
restriction of a class on their union.  This is the half-space analogue of
`Work.Orient.Port.existsLift`.

The union of the pieces is written in the form `⋃ i ∈ Finset.univ, K i` so that the conclusion
matches `halfUnionZero` at `s = Finset.univ` syntactically. -/
theorem halfExistsLift (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    (hBdry : IsClosed ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W))
    {A : Set W} (hA : IsCompact A)
    (hAint : ∀ x ∈ A, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (β : RelH W (n + 1) A) :
    ∃ (m : ℕ) (z : Fin m → W) (r : Fin m → ℝ)
      (hr : ∀ i, 0 < r i) (hgood : ∀ i, halfBallGood (n + 1) W (z i) (r i))
      (hzA : ∀ i, z i ∈ A)
      (hint : ∀ i, ∀ y ∈ halfBallPiece (n + 1) W (z i) (r i),
        y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
      (hcov : A ⊆ ⋃ i ∈ Finset.univ, halfBallPiece (n + 1) W (z i) (r i)),
      ∃ γ : RelH W (n + 1)
          (⋃ i ∈ Finset.univ, halfBallPiece (n + 1) W (z i) (r i)),
        resRelH W (n + 1) hcov γ = β := by
  classical
  obtain ⟨x₀, hbdry, hcycA, hclA⟩ :=
    Work.Orient.Port.relChain_lift (n + 1) (by omega) W A β
  obtain ⟨y, hy⟩ := hbdry
  obtain ⟨S, hSA, hScpt, hSr⟩ := Work.Cohomology.exists_compact_support_image (Aᶜ) n y
  have hSbdry : (Work.Cohomology.singularChains ℤ W).d (n + 1) ((n + 1) - 1) x₀
      ∈ LinearMap.range ((Work.Cohomology.inclChains W S).f ((n + 1) - 1)).hom := by
    rw [← hy]
    exact hSr
  have hSc : IsClosed S := hScpt.isClosed
  have hAS : Disjoint A S := Set.disjoint_left.mpr (fun a ha hS => hSA hS ha)
  have hAS' : Disjoint A (S ∪ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :=
    Set.disjoint_left.mpr (fun a ha hx =>
      hx.elim (fun hxS => (Set.disjoint_left.mp hAS ha) hxS) (fun hxb => hAint a ha hxb))
  have hS' : IsClosed (S ∪ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :=
    hSc.union hBdry
  obtain ⟨m, z, r, hr, hgood, hzA, hcov, hdisj⟩ := HalfCover n W hA hAS' hS'
  let K : Fin m → Set W := fun i => halfBallPiece (n + 1) W (z i) (r i)
  -- the cover in the `Finset.univ` form
  have hcovU : A ⊆ ⋃ i ∈ (Finset.univ : Finset (Fin m)), K i := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov hx)
    exact Set.mem_iUnion₂.mpr ⟨i, Finset.mem_univ i, hi⟩
  have hdisjU : Disjoint (S ∪ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
      (⋃ i ∈ (Finset.univ : Finset (Fin m)), K i) := by
    rw [Set.disjoint_left] at hdisj ⊢
    intro x hxS hxU
    obtain ⟨i, -, hi⟩ := Set.mem_iUnion₂.mp hxU
    exact hdisj hxS (Set.mem_iUnion.mpr ⟨i, hi⟩)
  have hnot : ∀ x : W, x ∈ ⋃ i ∈ (Finset.univ : Finset (Fin m)), K i →
      x ∉ S ∪ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W :=
    Set.disjoint_right.mp hdisjU
  have hSK : S ⊆ (⋃ i ∈ (Finset.univ : Finset (Fin m)), K i)ᶜ :=
    fun x hxS hxK => hnot x hxK (Or.inl hxS)
  have hint : ∀ i, ∀ y ∈ halfBallPiece (n + 1) W (z i) (r i),
      y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W :=
    fun i y hy hyb => hnot y (Set.mem_iUnion₂.mpr ⟨i, Finset.mem_univ i, hy⟩) (Or.inr hyb)
  have hbdry' : (Work.Cohomology.singularChains ℤ W).d (n + 1) ((n + 1) - 1) x₀
      ∈ LinearMap.range ((Work.Cohomology.inclChains W
          (⋃ i ∈ (Finset.univ : Finset (Fin m)), K i)ᶜ).f ((n + 1) - 1)).hom :=
    Work.Cohomology.mem_range_inclChains_of_subset hSK hSbdry
  have h0K : (CategoryTheory.Limits.cokernel.π
        (Work.Cohomology.inclChains W
          (⋃ i ∈ (Finset.univ : Finset (Fin m)), K i)ᶜ)).f ((n + 1) - 1)
      ((Work.Cohomology.singularChains ℤ W).d (n + 1) ((n + 1) - 1) x₀) = 0 := by
    obtain ⟨y', hy'⟩ := hbdry'
    rw [← hy']
    exact Work.Cohomology.cokernel_π_f_apply_eq_zero ((n + 1) - 1) y'
  have hcomm : (CategoryTheory.Limits.cokernel.π
          (Work.Cohomology.inclChains W
            (⋃ i ∈ (Finset.univ : Finset (Fin m)), K i)ᶜ)).f (n + 1)
        ≫ (CategoryTheory.Limits.cokernel
            (Work.Cohomology.inclChains W
              (⋃ i ∈ (Finset.univ : Finset (Fin m)), K i)ᶜ)).d (n + 1) ((n + 1) - 1)
      = (Work.Cohomology.singularChains ℤ W).d (n + 1) ((n + 1) - 1)
        ≫ (CategoryTheory.Limits.cokernel.π
            (Work.Cohomology.inclChains W
              (⋃ i ∈ (Finset.univ : Finset (Fin m)), K i)ᶜ)).f ((n + 1) - 1) :=
    HomologicalComplex.Hom.comm _ (n + 1) ((n + 1) - 1)
  have hcycK : (CategoryTheory.Limits.cokernel
        (Work.Cohomology.inclChains W
          (⋃ i ∈ (Finset.univ : Finset (Fin m)), K i)ᶜ)).d (n + 1) ((n + 1) - 1)
      ((CategoryTheory.Limits.cokernel.π
        (Work.Cohomology.inclChains W
          (⋃ i ∈ (Finset.univ : Finset (Fin m)), K i)ᶜ)).f (n + 1) x₀) = 0 := by
    rw [← CategoryTheory.ConcreteCategory.comp_apply, hcomm,
      CategoryTheory.ConcreteCategory.comp_apply, h0K]
  refine ⟨m, z, r, hr, hgood, hzA, hint, hcovU, (HomologicalComplex.homologyπ
    (CategoryTheory.Limits.cokernel (Work.Cohomology.inclChains W
      (⋃ i ∈ (Finset.univ : Finset (Fin m)), K i)ᶜ)) (n + 1))
    (Work.Cohomology.cycleOf (n + 1) _ hcycK), ?_⟩
  rw [Work.Orient.Port.chainClass_restrict (n + 1) (by omega) W hcovU x₀ hcycK,
    Work.Orient.Port.cyclesMap_cycleOf (n + 1) (by omega) W hcovU x₀ hcycK hcycA, hclA]

/-! ## Uniqueness over a compact set of the interior -/

theorem HalfCompactZero (n : ℕ) (W : TopCat) [CompactSpace W] [T2Space W]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) W]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 W]
    {A : Set W} (hA : IsCompact A)
    (hAint : ∀ x ∈ A, x ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary W)
    (β : Work.Orient.RelH W (n + 1) A)
    (hβ : ∀ (x : W) (hx : x ∈ A),
      Work.Orient.resRelH W (n + 1) (Set.singleton_subset_iff.mpr hx) β = 0) :
    β = 0 := by
  classical
  have hBdry : IsClosed ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary W) :=
    ModelWithCorners.isClosed_boundary (M := W) one_ne_zero
  obtain ⟨m, z, r, hr, hgood, hzA, hint, hcov, γ, hγ⟩ :=
    halfExistsLift n W hBdry hA hAint β
  have hγ0 : γ = 0 := by
    refine halfUnionZero n W Finset.univ z r hr hgood hint γ ?_
    intro i _
    have h1 : resRelH W (n + 1) (Set.singleton_subset_iff.mpr (hcov (hzA i))) γ
        = resRelH W (n + 1) (Set.singleton_subset_iff.mpr (hzA i))
            (resRelH W (n + 1) hcov γ) := by
      rw [← LinearMap.comp_apply, ← resRelH_point_fac W (n + 1) hcov (hzA i)]
    rw [show (Set.singleton_subset_iff.mpr
          (Set.mem_iUnion₂.mpr ⟨i, Finset.mem_univ i, mem_halfBallPiece_center (hr i)⟩))
        = Set.singleton_subset_iff.mpr (hcov (hzA i)) from Subsingleton.elim _ _,
      h1, hγ]
    exact hβ (z i) (hzA i)
  rw [← hγ, hγ0, map_zero]

end

end Work.Orient.Boundary
