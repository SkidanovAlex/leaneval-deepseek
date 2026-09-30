import Mathlib
import Submission.Work.KeyLemma.Curve.genericSum
import Submission.Work.KeyLemma.Curve.ordBaseBaseField
import Submission.Work.KeyLemma.Curve.BranchSum.Core
import Submission.Work.KeyLemma.Curve.BranchSum.center_loc_fix
import Submission.Work.KeyLemma.Curve.card_branches_fixed
import Submission.Work.KeyLemma.Sum
import Submission.Work.KeyLemma.Sum.toDiv_injective
import Submission.Work.KeyLemma.Curve.pencilAssembly
import Submission.Work.CurveBasics.Order.Setup
import Submission.Work.Charts.place_degree_eq_one_of_isAlgClosed
import Submission.Work.KeyLemma.Curve.BranchSum.specMap_closedPoint
import Submission.Work.KeyLemma.Curve.BranchSum.multiset_eq_posPart
import Submission.Work.KeyLemma.Curve.BranchSum.residueFieldIsoC

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.KeyLemma.Curve

set_option synthInstance.maxHeartbeats 16000000
set_option synthInstance.maxSize 1000000
set_option maxHeartbeats 16000000

open CategoryTheory AlgebraicGeometry Limits
open scoped Classical MonObj MonoidalCategory CartesianMonoidalCategory

universe u

/-- The type of `k(h)`-embeddings of `K(C)` into `N`. -/
abbrev GalEmb (k : Type u) [Field k] (C : Work.CurveBasics.Curve k) (h : C.functionField)
    (N : Type u) [Field N] [Algebra ↥(Work.KeyLemma.Curve.baseField C h) N] : Type u :=
  ↥C.functionField →ₐ[↥(Work.KeyLemma.Curve.baseField C h)] N

/-- The numbers of indices mapping into each `b ∈ S` add up to the total number of indices,
provided every value of `f` lies in `S`. -/
private lemma card_fiber_sum {J β : Type*} [Fintype J] [DecidableEq β]
    (g : J → β) (S : Finset β) (hS : ∀ i, g i ∈ S) :
    ∑ b ∈ S, ((Finset.univ.filter (fun i => g i = b)).card : ℤ) = (Fintype.card J : ℤ) := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset J)) (t := S) (f := g)
    (fun i _ => hS i)
  rw [Finset.card_univ] at h
  have h' : (∑ b ∈ S, (Finset.univ.filter (fun i => g i = b)).card) = Fintype.card J := h.symm
  rw [← Nat.cast_sum, h']

/-- If `c`, `o : β → ℤ` have the same total sum over `S`, resp. over `Z ⊆ S`, if `c` is
non-negative and `o` is bounded above by `c` on `Z`, then `c = o` on `Z` and `c` vanishes
on `S \ Z`. -/
private lemma finset_combination {β : Type*} [DecidableEq β]
    (c o : β → ℤ) (Z S : Finset β) (T : ℤ) (hZS : Z ⊆ S)
    (hsumS : ∑ b ∈ S, c b = T) (hsumZ : ∑ b ∈ Z, o b = T)
    (hc0 : ∀ b, 0 ≤ c b) (hle : ∀ b ∈ Z, o b ≤ c b) :
    (∀ b ∈ Z, c b = o b) ∧ (∀ b ∈ S \ Z, c b = 0) := by
  have h1 := Finset.sum_le_sum_of_subset_of_nonneg hZS (fun b _ _ => hc0 b)
  have h1' : ∑ b ∈ Z, c b ≤ T := by rwa [hsumS] at h1
  have h2 : ∑ b ∈ Z, o b ≤ ∑ b ∈ Z, c b := Finset.sum_le_sum (fun b hb => hle b hb)
  have hle1 : ∑ b ∈ Z, c b ≤ ∑ b ∈ Z, o b := h1'.trans (le_of_eq hsumZ.symm)
  have hEq : ∑ b ∈ Z, c b = ∑ b ∈ Z, o b := le_antisymm hle1 h2
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · exact ((Finset.sum_eq_sum_iff_of_le (fun b hb => hle b hb)).mp hEq.symm b hb).symm
  · have hsd := Finset.sum_sdiff hZS (f := c)
    have h0 : ∑ b ∈ S \ Z, c b = 0 := by linarith [hsd, hsumS, hEq, hsumZ]
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => hc0 b)).mp h0 b hb

/-- **The branch sum: specialisation of the generic-fibre sum of the pencil at a zero of `h`.**

Setting: `k = k̄`, `C` a curve over `k`, `h ∈ K(C)^*` transcendental over `k` with `K(C)/k(h)`
finite separable of degree `n`, `N/k(h)` a finite Galois extension into which `K(C)` embeds over
`k(h)` (the last condition being carried by the two explicit equations `hKE`, `hAE`).  Let
`A₀ := k[h] = C.ordBase h`, `C' := A₀^{int}_N`, `P` a prime of `C'` over `(h)`, `R' := (C')_P`,
and let `s : SumDiv C` be a multiset of `k`-points presenting `div₀ h = posPart C h`.

The hypothesis `[IsLocalization.AtPrime (Localization.AtPrime P) P]` is NOT redundant: it pins
`algebraMap ↥C' R'` to be the canonical localisation map, which (together with
`IsScalarTower ↥C' R' N` and `IsFractionRing R' N`) pins `algebraMap R' N`, because every element
of `R'` is `a/s`.  Without it the algebra structures are arbitrary and can be twisted by a field
automorphism so that the conclusion fails.

Then there is a morphism `ρ : Spec R' ⟶ A` such that

* `ρ` is a morphism over `Spec k` (`Spec.map (ofHom (algebraMap k R')) = ρ ≫ A.hom`);
* `ρ` restricted to the generic point `Spec N` (via `algebraMap R' N`) is the generic-fibre sum
  `genericSum = ∏_{σ : K(C) →ₐ[k(h)] N} (Spec σ ≫ genericPt C ≫ f) ∈ A(N)`; and
* the closed point of `Spec R'`, read in `A(k)` through an isomorphism
  `e : ResidueField R' ≃+* k` with `e (residue (algebraMap k R' c)) = c`, maps to
  `Σ f(s) = SumDiv.sumOfPoints C f s`.

Proof strategy (full recipe):

1. `R'` is a DVR (`IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain`, with
   `IsDedekindDomain C'` from `IsIntegralClosure.isDedekindDomain`), `P` is maximal (it lies over
   the maximal ideal `(h) = C.ordIdeal h` of `A₀`), `IsFractionRing R' N` is a hypothesis.
2. For each `σ : K(C) →ₐ[k(h)] N` let `γ_σ := Work.KeyLemma.Curve.branch (C := C) (h := h) σ`
   (`Submission/Work/KeyLemma/Curve/BranchSum/Defs.lean`), with `branch_spec` giving that
   `specOfMap (algebraMap R' N) ≫ γ_σ = conjPtOverC C h σ`.  Put
   `ρ_over := ∏ σ, (γ_σ ≫ f)` in the group `(specOf k R' ⟶ A)` and `ρ := ρ_over.left`.
3. `ρ ≫ A.hom = Spec.map (ofHom (algebraMap k R'))`: each `γ_σ` is a morphism over `Spec k`
   (`conjPtOverC`'s `w` field), and a product of morphisms over `Spec k` is over `Spec k`.
4. `Spec.map (ofHom (algebraMap R' N)) ≫ ρ = genericSum f`: use
   `Work.KeyLemma.Curve.comp_prod` (post-composition preserves finite products) with
   `branch_spec` and the definition of `genericSumOver`.
5. The existence of `e : ResidueField R' ≃+* k` with `e (residue (algebraMap k R' c)) = c`:
   `C'` is finite over `k[h]`, so `C'/P` is a finite-dimensional domain over `k = k[h]/(h)`,
   hence a finite extension field of the algebraically closed `k`, i.e. `k`; take `e` to be the
   inverse of the canonical `k → ResidueField R'`.
6. Closed value: `Spec.map (ofHom (e ∘ residue)) ≫ ρ = ∏ σ, (x_σ ≫ f)` where
   `x_σ : Pt k C.toOver` is the `k`-point `Spec.map (ofHom (e ∘ residue)) ≫ γ_σ.left`, again by
   `comp_prod`.  Then prove `∑ σ, Finsupp.single x_σ 1 = s` in `SumDiv C`: by
   `Work.KeyLemma.Curve.SumDiv.toDiv_injective` it suffices that
   `toDiv C (∑ σ, single x_σ 1) = posPart C h = toDiv C s`; for each place `Q` the multiplicity of
   `Q` in the left hand side is `Nat.card {σ // placeOfPoint C x_σ = Q}`, which equals `ord_Q h`
   for `0 < ord_Q h` (the dictionary "the branch through `σ` specialises to `Q` iff
   `σ(q_Q) ⊆ P`", `q_Q = kxPrimeOfPlace C h Q`, combined with `card_branches_fixed` and
   `sum_ord_pos_eq_finrank_general`; see also the statement `card_branch_closedPoints` and
   `residueFieldIso` if the modules
   `Submission.Work.KeyLemma.Curve.BranchSum.card_branch_closedPoints` and
   `Submission.Work.KeyLemma.Curve.BranchSum.residueFieldIso` build — they state exactly these two
   steps and may be imported and used; otherwise prove them privately here) and `0` for
   `ord_Q h ≤ 0` (if the closed point of `γ_σ` were `Q` then the induced map on stalks would give
   `σ (h⁻¹) ∈ R'`, but `σ` fixes `k(h) ∋ h⁻¹` and `h⁻¹ ∉ R'` because `h ∈ P`).  Finally
   `SumDiv.sumOfPoints_of_toDiv_eq` converts this into the value of `sumOfPoints`. -/
theorem branch_sum {k : Type u} [Field k] [IsAlgClosed k]
    (C : Work.CurveBasics.Curve k) (h : C.functionField) (hht : Transcendental k h)
    {A : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of k))}
    [CategoryTheory.GrpObj A] [CategoryTheory.IsCommMonObj A]
    [AlgebraicGeometry.IsProper A.hom] (f : C.toOver ⟶ A)
    [FiniteDimensional ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField]
    [Algebra.IsSeparable ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField]
    {N : Type u} [Field N] [Algebra ↥(Work.KeyLemma.Curve.baseField C h) N] [Algebra k N]
    [IsScalarTower k ↥(Work.KeyLemma.Curve.baseField C h) N]
    [IsGalois ↥(Work.KeyLemma.Curve.baseField C h) N]
    [Algebra ↥C.functionField N]
    [IsScalarTower ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField N]
    [FiniteDimensional ↥(Work.KeyLemma.Curve.baseField C h) N]
    [Algebra ↥(Work.CurveBasics.Curve.ordBase C h) N]
    [IsScalarTower ↥(Work.CurveBasics.Curve.ordBase C h) ↥(Work.KeyLemma.Curve.baseField C h) N]
    (hKE : (algebraMap ↥(Work.KeyLemma.Curve.baseField C h) N)
      = (algebraMap ↥C.functionField N).comp
        (algebraMap ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField))
    (hAE : (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) N)
      = (algebraMap ↥C.functionField N).comp
        (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) ↥C.functionField))
    [IsFractionRing ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) N]
    (P : Ideal ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)) [P.IsPrime]
    [P.LiesOver (Work.CurveBasics.Curve.ordIdeal C h)]
    [Algebra k (Localization.AtPrime P)]
    [Algebra ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) (Localization.AtPrime P)]
    [IsLocalization.AtPrime (Localization.AtPrime P) P]
    [Algebra (Localization.AtPrime P) N]
    [IsScalarTower ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
      (Localization.AtPrime P) N]
    [IsScalarTower k (Localization.AtPrime P) N]
    [IsFractionRing (Localization.AtPrime P) N]
    (s : Work.KeyLemma.Curve.SumDiv C)
    (hs : Work.KeyLemma.Curve.SumDiv.toDiv C s = Work.KeyLemma.Curve.posPart C h) :
    ∃ (ρ : AlgebraicGeometry.Spec (CommRingCat.of (Localization.AtPrime P)) ⟶ A.left)
      (e : IsLocalRing.ResidueField (Localization.AtPrime P) ≃+* k),
      (ρ ≫ A.hom = AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap k (Localization.AtPrime P)))) ∧
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime P) N)) ≫ ρ
        = Work.KeyLemma.Curve.genericSum (C := C) (h := h) (N := N) f) ∧
      (AlgebraicGeometry.Spec.map
          (CommRingCat.ofHom (e.toRingHom.comp (IsLocalRing.residue _))) ≫ ρ
        = (Work.KeyLemma.Curve.SumDiv.sumOfPoints C f s).left) := by
  classical
  -- ## Step 0: instance repairs.
  haveI hSTAK := IsScalarTower.of_algebraMap_eq
      (R := ↥(Work.CurveBasics.Curve.ordBase C h))
      (S := ↥(Work.KeyLemma.Curve.baseField C h)) (A := N) (fun x => by
    show algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) N x
      = algebraMap ↥(Work.KeyLemma.Curve.baseField C h) N
          (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
            ↥(Work.KeyLemma.Curve.baseField C h) x)
    rw [hAE, hKE]
    simp only [RingHom.comp_apply]
    congr 1)
  -- ## Step 1: `R' = (C')_P` is a valuation ring.
  haveI hFDcan : @FiniteDimensional ↥(Work.KeyLemma.Curve.baseField C h) N _ _
      (@Algebra.toModule ↥(Work.KeyLemma.Curve.baseField C h) N _ _
        ‹Algebra ↥(Work.KeyLemma.Curve.baseField C h) N›) :=
    Work.KeyLemma.Curve.BranchSum.finiteDimensional_canon (k := k) (L := ↥C.functionField)
      (akL := inferInstance) (K := Work.KeyLemma.Curve.baseField C h)
      (algK := ‹Algebra ↥(Work.KeyLemma.Curve.baseField C h) N›)
      (algL := ‹Algebra ↥C.functionField N›) (hKE := hKE) (finKN := ‹_›)
  haveI hDed : IsDedekindDomain ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) :=
    @integralClosure.isDedekindDomain ↥(Work.CurveBasics.Curve.ordBase C h)
      ↥(Work.KeyLemma.Curve.baseField C h) inferInstance inferInstance inferInstance inferInstance
      N inferInstance inferInstance inferInstance hSTAK hFDcan inferInstance
      (IsGalois.to_isSeparable (E := N)) inferInstance
  haveI hDomR' : IsDomain (Localization.AtPrime P) :=
    Function.Injective.isDomain (algebraMap (Localization.AtPrime P) N)
      (IsFractionRing.injective (Localization.AtPrime P) N)
  have hodIdeal_ne : Work.CurveBasics.Curve.ordIdeal C h ≠ ⊥ := by
    intro h1
    have h2 : (⟨h, Algebra.subset_adjoin (Set.mem_singleton h)⟩ :
        Work.CurveBasics.Curve.ordBase C h) = 0 :=
      Ideal.span_singleton_eq_bot.mp (by rw [← h1])
    exact hht.ne_zero (Subtype.ext_iff.mp h2)
  have hPne : P ≠ ⊥ := by
    intro h0
    set hg : ↥(Work.CurveBasics.Curve.ordBase C h) :=
      ⟨h, Algebra.subset_adjoin (Set.mem_singleton h)⟩ with hgdef
    have hgmem : hg ∈ Work.CurveBasics.Curve.ordIdeal C h := by
      rw [Work.CurveBasics.Curve.ordIdeal]
      exact Ideal.mem_span_singleton_self hg
    have hgenP : algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
        ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) hg ∈ P :=
      (Ideal.mem_of_liesOver P (Work.CurveBasics.Curve.ordIdeal C h) hg).mp hgmem
    have hz : algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
        ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) hg = 0 := by
      rw [h0] at hgenP
      exact Ideal.mem_bot.mp hgenP
    have h1 : (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) N) hg = 0 := by
      rw [IsScalarTower.algebraMap_apply ↥(Work.CurveBasics.Curve.ordBase C h)
        ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) N hg, hz, map_zero]
    have hval : (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) N) hg
        = (algebraMap ↥C.functionField N)
            ((algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) ↥C.functionField) hg) :=
      congrFun (congrArg DFunLike.coe hAE) hg
    rw [hval] at h1
    have h3 : (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) ↥C.functionField) hg = h := rfl
    rw [h3] at h1
    exact hht.ne_zero
      (FaithfulSMul.algebraMap_injective ↥C.functionField N (h1.trans (map_zero _).symm))
  haveI hDVRR' : IsDiscreteValuationRing (Localization.AtPrime P) :=
    @IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) inferInstance hDed P hPne
      inferInstance (Localization.AtPrime P) inferInstance hDomR' inferInstance inferInstance
  haveI hVRR' : ValuationRing (Localization.AtPrime P) := inferInstance
  -- ## Step 2: the residue field of `R'` is `k`.
  obtain ⟨e, he⟩ : ∃ e : IsLocalRing.ResidueField (Localization.AtPrime P) ≃+* k,
      ∀ c : k, e (IsLocalRing.residue _ (algebraMap k (Localization.AtPrime P) c)) = c :=
    Work.KeyLemma.Curve.BranchSum.residueFieldIsoKE (C := C) (h := h) (hht := hht)
      (N := N) (hKE := hKE) (hAE := hAE) (P := P)
  -- ## Step 3: the branch product.
  have hcomp : (e.toRingHom.comp (IsLocalRing.residue (Localization.AtPrime P))).comp
      (algebraMap k (Localization.AtPrime P)) = RingHom.id k := by
    ext c
    exact he c
  -- the `k`-point of `Spec R'` given by `e ∘ residue`
  let u : (𝟙_ (Over (Spec (CommRingCat.of k)))) ⟶
      Work.SpecLin.specOf (K := k) (Localization.AtPrime P) :=
    Over.homMk (Spec.map (CommRingCat.ofHom
        (e.toRingHom.comp (IsLocalRing.residue (Localization.AtPrime P)))))
      (by
        show Spec.map (CommRingCat.ofHom
            (e.toRingHom.comp (IsLocalRing.residue (Localization.AtPrime P))))
            ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Localization.AtPrime P)))
          = 𝟙 (Spec (CommRingCat.of k))
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
        exact Spec.map_id (CommRingCat.of k))
  let x : GalEmb k C h N → Work.KeyLemma.Curve.Point C := fun σ =>
    u ≫ Work.KeyLemma.Curve.branch (C := C) (h := h) (R' := Localization.AtPrime P) σ
  have hγ : ∀ σ : GalEmb k C h N, Work.SpecLin.specOfMap (K := k)
      (IsScalarTower.toAlgHom k (Localization.AtPrime P) N)
      ≫ Work.KeyLemma.Curve.branch (C := C) (h := h) (R' := Localization.AtPrime P) σ
      = Work.KeyLemma.Curve.conjPtOverC C h σ :=
    fun σ => Work.KeyLemma.Curve.branch_spec (C := C) (h := h)
      (R' := Localization.AtPrime P) σ
  refine ⟨(∏ σ : GalEmb k C h N, (Work.KeyLemma.Curve.branch (C := C) (h := h)
      (R' := Localization.AtPrime P) σ ≫ f)).left, e, ?_, ?_, ?_⟩
  · -- ρ is a morphism over `Spec k`
    exact (∏ σ : GalEmb k C h N, (Work.KeyLemma.Curve.branch (C := C) (h := h)
      (R' := Localization.AtPrime P) σ ≫ f)).w
  · -- the generic fibre is the generic-fibre sum
    have hcomp2 := congrArg Over.Hom.left (Work.KeyLemma.Curve.comp_prod_univ
      (u := Work.SpecLin.specOfMap (K := k) (IsScalarTower.toAlgHom k (Localization.AtPrime P) N))
      (g := fun σ : GalEmb k C h N => Work.KeyLemma.Curve.branch (C := C) (h := h)
        (R' := Localization.AtPrime P) σ ≫ f))
    simp only [Over.comp_left] at hcomp2
    have hprod : (∏ σ : GalEmb k C h N,
          (Work.SpecLin.specOfMap (K := k)
            (IsScalarTower.toAlgHom k (Localization.AtPrime P) N)
            ≫ (Work.KeyLemma.Curve.branch (C := C) (h := h)
                (R' := Localization.AtPrime P) σ ≫ f)))
        = Work.KeyLemma.Curve.genericSumOver (C := C) (h := h) (N := N) f := by
      rw [Work.KeyLemma.Curve.genericSumOver]
      refine Finset.prod_congr rfl (fun σ _ => ?_)
      rw [← Category.assoc, hγ σ]
      rfl
    change Spec.map (CommRingCat.ofHom (algebraMap (Localization.AtPrime P) N))
        ≫ Over.Hom.left (∏ σ : GalEmb k C h N, (Work.KeyLemma.Curve.branch (C := C) (h := h)
            (R' := Localization.AtPrime P) σ ≫ f))
      = (Work.KeyLemma.Curve.genericSumOver (C := C) (h := h) (N := N) f).left
    rw [← hprod]
    simpa only [Work.SpecLin.specOfMap, Work.SpecLin.specOfMapHom, Over.homMk_left,
      Work.SpecLin.toAlgHom_toRingHom] using hcomp2
  · -- ## Step 4: the value at the closed point.
    have hker : RingHom.ker (e.toRingHom.comp (IsLocalRing.residue (Localization.AtPrime P)))
        = IsLocalRing.maximalIdeal (Localization.AtPrime P) := by
      rw [RingHom.ker_comp_of_injective
        (IsLocalRing.residue (Localization.AtPrime P)) e.injective, IsLocalRing.ker_residue]
    have hu : u.left = Spec.map (CommRingCat.ofHom
        (e.toRingHom.comp (IsLocalRing.residue (Localization.AtPrime P)))) := rfl
    have hu' : u.left (IsLocalRing.closedPoint k)
        = IsLocalRing.closedPoint (Localization.AtPrime P) := by
      rw [hu]
      exact Work.KeyLemma.Curve.BranchSum.specMap_closedPoint
        (e.toRingHom.comp (IsLocalRing.residue (Localization.AtPrime P))) hker
    let Qσ : GalEmb k C h N → C.Place := fun σ => Work.KeyLemma.Curve.placeOfPoint C (x σ)
    have hQσ : ∀ (σ : GalEmb k C h N) (Q : C.Place) (hQ : 0 < C.ordAt h Q),
        (∀ x ∈ Work.CurveBasics.kxPrimeOfPlace C h Q hQ.le, ∃ c ∈ P,
          algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) N c
            = σ (algebraMap ↥(C.ordClosure h) ↥C.functionField x)) → Qσ σ = Q := by
      intro σ Q hQ hσ
      letI : Algebra ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
          (Localization.AtPrime P) := OreLocalization.instAlgebra
      haveI : IsLocalization.AtPrime (Localization.AtPrime P) P := inferInstance
      have hSTalg : ∀ r : ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N),
          algebraMap (Localization.AtPrime P) N
            (algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
              (Localization.AtPrime P) r)
          = algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) N r :=
        fun r => (IsScalarTower.algebraMap_apply
          ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
          (Localization.AtPrime P) N r).symm
      obtain ⟨χ, hχloc, hχcompat⟩ :=
        Work.KeyLemma.Curve.BranchSum.center_loc_of_isLocalizationAtPrime (C := C) (h := h)
          (hht := hht) (N := N) (P := P) (hKE := hKE) (hAE := hAE) (hSTalg := hSTalg)
          (σ := σ) (Q := Q) (hQ := hQ.le) hσ
      have hbc := Work.KeyLemma.Curve.branch_closed_point_of_center (C := C) (h := h) (N := N)
        (R' := Localization.AtPrime P) σ χ hχloc hχcompat
      apply Subtype.ext
      show (Work.KeyLemma.Curve.placeOfPoint C (x σ)).point = Q.point
      rw [Work.KeyLemma.Curve.placeOfPoint_point]
      show (Work.KeyLemma.Curve.branch (C := C) (h := h) (R' := Localization.AtPrime P) σ).left
        (u.left (IsLocalRing.closedPoint k)) = Q.point
      rw [hu']
      exact hbc
    have hcount : (∑ σ : GalEmb k C h N, Finsupp.single (Qσ σ) 1)
        = Work.KeyLemma.Curve.posPart C h :=
      Work.KeyLemma.Curve.BranchSum.multiset_eq_posPart (C := C) (h := h) (hht := hht) (N := N)
        (hKE := hKE) (hAE := hAE) (P := P) (Qσ := Qσ) hQσ
    have hSumEq : (∑ σ : GalEmb k C h N, Finsupp.single (x σ) 1) = s := by
      apply Work.KeyLemma.Sum.toDiv_injective C
      have h1 : Work.KeyLemma.Curve.SumDiv.toDiv C
            (∑ σ : GalEmb k C h N, Finsupp.single (x σ) 1)
          = ∑ σ : GalEmb k C h N, Finsupp.single (Qσ σ) 1 := by
        rw [← Work.KeyLemma.Curve.SumDiv.toDivAddHom_apply, map_sum]
        refine Finset.sum_congr rfl (fun σ _ => ?_)
        rw [Work.KeyLemma.Curve.SumDiv.toDivAddHom_apply, Work.KeyLemma.Curve.toDiv_single]
      rw [h1, hcount, hs]
    have hsumOfPoints : Work.KeyLemma.Curve.SumDiv.sumOfPoints C f s
        = u ≫ (∏ σ : GalEmb k C h N, (Work.KeyLemma.Curve.branch (C := C) (h := h)
            (R' := Localization.AtPrime P) σ ≫ f)) := by
      rw [← hSumEq]
      rw [Work.KeyLemma.Curve.sumOfPoints_finsetSum (C := C) (A := A) f Finset.univ x]
      rw [Work.KeyLemma.Curve.comp_prod_univ (A := A) u (fun σ : GalEmb k C h N =>
        Work.KeyLemma.Curve.branch (C := C) (h := h) (R' := Localization.AtPrime P) σ ≫ f)]
      refine Finset.prod_congr rfl (fun σ _ => ?_)
      show (u ≫ Work.KeyLemma.Curve.branch (C := C) (h := h)
            (R' := Localization.AtPrime P) σ) ≫ f
          = u ≫ (Work.KeyLemma.Curve.branch (C := C) (h := h)
            (R' := Localization.AtPrime P) σ ≫ f)
      rw [Category.assoc]
    have h2 := congrArg Over.Hom.left hsumOfPoints.symm
    simp only [Over.comp_left] at h2
    rw [hu] at h2
    exact h2

end Work.KeyLemma.Curve
