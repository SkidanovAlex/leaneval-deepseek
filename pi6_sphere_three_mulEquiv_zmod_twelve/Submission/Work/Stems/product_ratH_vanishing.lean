import Mathlib
import Submission.Work.StemsB.SerreExact
import Submission.Work.Serre.StableExact
import Submission.Work.Serre.Basic
import Submission.Work.StemsB.RelChainsBaseChangeRat
import Submission.Work.StemsB.sphRatHomology
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv
import Submission.Work.ThomBordism.TwoSet.TraceAux
import Submission.Work.ThomBordism.TwoSet.subsingleton_piZero_of_homeomorph

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Stems

open CategoryTheory CategoryTheory.Limits

set_option linter.style.haveILetI false

noncomputable section

/-! ## Auxiliary tools

The proof of `product_ratH_vanishing` below needs a handful of small tools, proved here:

* `isHurewiczFibration_fst` — the first projection of a product is a Hurewicz fibration (used to
  feed `Work.Serre.SerreExactRangeCorrected`, SERRE's engine);
* `fibreHomeo` — the fibre of that projection is homeomorphic to the second factor;
* `subsingleton_homotopyGroup_fin_of_homeomorph` — triviality of `π_i` transports along a
  homeomorphism (for all `i`, `i = 0` included);
* `isZero_ratH_of_homeomorph` — vanishing of rational homology transports along a homeomorphism;
* `isZero_ratH_singleton` — the rational (co)homology of a one-point space vanishes in positive
  degrees;
* `isZero_relChainsR_homology_of_isZero_abs` — the relative term of the long exact sequence of a
  pair vanishes in degree `n` if the absolute terms in degrees `n` and `n - 1` do;
* `isZero_relChainsR_rat_of_isIso_relPairMap` — the rational relative homology of the domain of a
  pair map vanishes if the (isomorphic) rational relative homology of its target does.
-/

/-- **The first projection of a product is a Hurewicz fibration.**  The lift of a homotopy is
`(t, z) ↦ (H (t, z), (f z).2)`. -/
theorem isHurewiczFibration_fst (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    Work.StemsB.IsHurewiczFibration (ContinuousMap.fst : C(X × Y, X)) := by
  intro Z _ f b H
  refine ⟨b.prodMk (ContinuousMap.snd.comp f), ?_, ?_⟩
  · refine ContinuousMap.Homotopy.mk
      (H.toContinuousMap.prodMk ((ContinuousMap.snd.comp f).comp ContinuousMap.snd)) ?_ ?_
    · intro z
      ext <;> simp [ContinuousMap.Homotopy.apply_zero]
    · intro z
      ext <;> simp [ContinuousMap.Homotopy.apply_one]
  · ext x
    simp

/-- **The fibre of the first projection is homeomorphic to the second factor**:
`(x₀, y) ↦ y`. -/
def fibreHomeo (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (x₀ : X) :
    ↥(Prod.fst ⁻¹' ({x₀} : Set X) : Set (X × Y)) ≃ₜ Y where
  toFun z := z.1.2
  invFun y := ⟨(x₀, y), rfl⟩
  left_inv z := by
    refine Subtype.ext (Prod.ext ?_ rfl)
    have h : z.1.1 = x₀ := by
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using z.2
    exact h.symm
  right_inv y := rfl
  continuous_toFun := continuous_snd.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_const.prodMk continuous_id

/-- **Triviality of a homotopy group transports along a homeomorphism** (all indices `i`,
`i = 0` included, where the statement is about path components). -/
theorem subsingleton_homotopyGroup_fin_of_homeomorph {A B : Type} [TopologicalSpace A]
    [TopologicalSpace B] (e : A ≃ₜ B) {a : A} {b : B} (hab : e a = b) (i : ℕ)
    (h : Subsingleton (HomotopyGroup (Fin i) B b)) :
    Subsingleton (HomotopyGroup (Fin i) A a) := by
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    exact Work.ThomBordism.TwoSet.subsingleton_piZero_of_homeomorph e hab h
  · haveI : Nonempty (Fin i) := ⟨⟨0, hpos⟩⟩
    exact Work.ThomBordism.TwoSet.subsingleton_of_homeomorph e hab (Fin i) h

/-- **Vanishing of rational singular homology transports along a homeomorphism.** -/
theorem isZero_ratH_of_homeomorph {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (e : A ≃ₜ B) (j : ℕ) (h : IsZero (Work.Serre.ratH (TopCat.of B) j)) :
    IsZero (Work.Serre.ratH (TopCat.of A) j) := by
  haveI : IsIso (Work.Serre.ratHomologyMap e.toHomotopyEquiv.toFun j) :=
    Work.Serre.IsRatHomologyIso.of_homotopyEquiv e.toHomotopyEquiv j
  exact IsZero.of_iso h (asIso (Work.Serre.ratHomologyMap e.toHomotopyEquiv.toFun j))

/-- **The rational homology of a one-point space vanishes in positive degrees.** -/
theorem isZero_ratH_singleton (X : Type) [TopologicalSpace X] (x₀ : X) {j : ℕ} (hj : 0 < j) :
    IsZero (Work.Serre.ratH (TopCat.of ↥({x₀} : Set X)) j) := by
  haveI : Nonempty ↥({x₀} : Set X) := ⟨⟨x₀, rfl⟩⟩
  haveI : Subsingleton ↥({x₀} : Set X) :=
    ⟨fun a b =>
      Subtype.ext ((Set.mem_singleton_iff.mp a.2).trans (Set.mem_singleton_iff.mp b.2).symm)⟩
  exact (Work.Serre.ratAcyclic_of_contractible ↥({x₀} : Set X)).isZero_ratH hj

/-- **The relative term of the long exact sequence of a pair vanishes** if the absolute terms in
degrees `n` and `n - 1` do.  This is the exactness chase in
`H_{n+1}(X) → H_{n+1}(X,A) → H_n(A)`: with the two outer terms zero, the middle one is zero. -/
theorem isZero_relChainsR_homology_of_isZero_abs (R : Type) [CommRing R] (X : TopCat) (A : Set X)
    (n : ℕ) (hn : 1 ≤ n)
    (hX : IsZero ((Work.Cohomology.singularChains R X).homology n))
    (hA : IsZero ((Work.Cohomology.singularChains R (TopCat.of A)).homology (n - 1))) :
    IsZero ((Work.StemsB.relChainsR R X A).homology n) := by
  have hS := Work.StemsB.relChainsR_exact₃ R X A (n - 1)
  have hXn : IsZero ((Work.Cohomology.singularChains R X).homology ((n - 1) + 1)) :=
    IsZero.of_iso hX (eqToIso (congrArg
      (fun i => (Work.Cohomology.singularChains R X).homology i) (Nat.sub_add_cancel hn)))
  have hmid : IsZero ((Work.StemsB.relChainsR R X A).homology ((n - 1) + 1)) :=
    hS.isZero_X₂
      (hXn.eq_zero_of_src (HomologicalComplex.homologyMap
        (cokernel.π (Work.StemsB.relChainsRIncl R X A)) ((n - 1) + 1)))
      (hA.eq_zero_of_tgt (Work.StemsB.relChainsRδ R X A (n - 1)))
  exact IsZero.of_iso hmid (eqToIso (congrArg
    (fun i => (Work.StemsB.relChainsR R X A).homology i) (Nat.sub_add_cancel hn).symm))

/-- **The rational relative homology of the domain of a pair map vanishes** if the rational
relative homology of its target does (and the integral pair map is an isomorphism on homology in
the degree in question).

The proof works over `ℤ` (`Work.StemsB.SerreExactRange` produces integral isomorphisms) and then
transfers to `ℚ` by the flat base change `- ⊗[ℤ] ℚ`, which preserves homology. -/
theorem isZero_relChainsR_rat_of_isIso_relPairMap {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (b₀ : B) (j : ℕ)
    (hiso : IsIso (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) j))
    (hB : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of B) ({b₀} : Set B)).homology j)) :
    IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of E) (p ⁻¹' {b₀})).homology j) := by
  haveI hflat : (Int.castRingHom ℚ).Flat := by rw [RingHom.Flat]; infer_instance
  haveI : PreservesFiniteLimits Work.StemsB.IntRatF :=
    ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  haveI : PreservesFiniteColimits Work.StemsB.IntRatF := inferInstance
  haveI : Work.StemsB.IntRatF.PreservesHomology := inferInstance
  let K₁ := Work.Cohomology.relChains (TopCat.of E) (p ⁻¹' {b₀})
  let K₂ := Work.Cohomology.relChains (TopCat.of B) ({b₀} : Set B)
  obtain ⟨β₁⟩ := Work.StemsB.relChainsBaseChangeRat (TopCat.of E) (p ⁻¹' {b₀})
  obtain ⟨β₂⟩ := Work.StemsB.relChainsBaseChangeRat (TopCat.of B) ({b₀} : Set B)
  have α₁ : (Work.StemsB.relChainsR ℚ (TopCat.of E) (p ⁻¹' {b₀})).homology j ≅
      Work.StemsB.IntRatF.obj (K₁.homology j) :=
    (HomologicalComplex.homologyMapIso β₁ j).symm ≪≫
      (Work.StemsB.SphRat.homologyMapBaseChange Work.StemsB.IntRatF K₁ j).some
  have α₂ : (Work.StemsB.relChainsR ℚ (TopCat.of B) ({b₀} : Set B)).homology j ≅
      Work.StemsB.IntRatF.obj (K₂.homology j) :=
    (HomologicalComplex.homologyMapIso β₂ j).symm ≪≫
      (Work.StemsB.SphRat.homologyMapBaseChange Work.StemsB.IntRatF K₂ j).some
  haveI : IsIso (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) j) := hiso
  have hser : K₁.homology j ≅ K₂.homology j :=
    asIso (HomologicalComplex.homologyMap (Work.StemsB.relPairMap p b₀) j)
  exact IsZero.of_iso (IsZero.of_iso (IsZero.of_iso hB α₂.symm)
    (Work.StemsB.IntRatF.mapIso hser)) α₁

end

/-- **The product step of the free part of `EMVan`** (Künneth, only in the vanishing range).

Let `k ≥ 2`, let `X` and `Y` be `(k-1)`-connected (`Work.Serre.Conn`, base points `x₀`, `y₀`), and
suppose that both have vanishing rational reduced homology in the range `k < j ≤ 2k-1`.  Then so
does the product `X × Y`.

This is the `ℤ^r` step of the Eilenberg–MacLane input `EMVan(k)` assigned to area STEMS: iterating
it gives `H̃_j((K(ℤ,k))^r;ℚ) = 0` for `k < j ≤ 2k-1` from the `C2` statement for `K(ℤ,k)`; no full
Künneth formula is needed because only the *vanishing* is required, and the range `(k, 2k-1]`
contains no nontrivial sum of two degrees `> k`.

Route: the projection `Prod.fst : X × Y → X` is a Hurewicz fibration with fibre `{x₀} × Y ≅ Y`;
`b = f = k` (both `X` and the fibre are `(k-1)`-connected), so `Work.StemsB.SerreExactRange`
(consumed as a hypothesis, SERRE's engine) gives
`H_i(X × Y, {x₀} × Y; ℤ) ≅ H_i(X, {x₀}; ℤ)` for every `i < 2k`; over `ℚ` (the transfers
`Work.StemsB.relChainsBaseChangeRat`, `Work.Stems.Engine.isZero_relChainsR_rat_of_isZero_relChains`,
`Work.StemsB.SphLoopTools.isZero_homology_rat_of_isZero_homology_int`) the long exact sequence of the
pair `(X × Y, {x₀} × Y)` (the rational pair sequence `Work.StemsB.relChainsR_exact₁/₂/₃`) reads
`H̃_j(Y) → H̃_j(X × Y) → H̃_j(X)` with the two outer terms zero for `k < j ≤ 2k-1`, forcing
`H̃_j(X × Y;ℚ) = 0` — note that only the vanishing of `H̃_j`, not of `H̃_{j-1}`, is used.-/
theorem product_ratH_vanishing (k : ℕ) (hk : 2 ≤ k) {X Y : Type} [TopologicalSpace X]
    [TopologicalSpace Y] (x₀ : X) (y₀ : Y) (hXc : Work.Serre.Conn X x₀ k)
    (hYc : Work.Serre.Conn Y y₀ k)
    (hX : ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of X) j))
    (hY : ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of Y) j))
    (hSerre : Work.Serre.SerreExactRangeCorrected) :
    ∀ j : ℕ, k < j → j ≤ 2 * k - 1 →
      CategoryTheory.Limits.IsZero (Work.Serre.ratH (TopCat.of (X × Y)) j) := by
  intro j hj1 hj2
  have hjpos : 1 ≤ j := by omega
  have h2k : j < k + k := by omega
  -- the fibre of the projection and its connectivity
  have hfib : ∀ i < k,
      Subsingleton (HomotopyGroup (Fin i) (↥(Prod.fst ⁻¹' ({x₀} : Set X))) ⟨(x₀, y₀), rfl⟩) :=
    fun i hi => subsingleton_homotopyGroup_fin_of_homeomorph (fibreHomeo X Y x₀) rfl i (hYc i hi)
  -- SERRE's exact sequence in the stable range, applied to the projection
  haveI hiso : IsIso (HomologicalComplex.homologyMap
      (Work.StemsB.relPairMap (ContinuousMap.fst : C(X × Y, X)) x₀) j) :=
    hSerre (X × Y) X (ContinuousMap.fst : C(X × Y, X)) (isHurewiczFibration_fst X Y)
      (x₀, y₀) x₀ rfl k k (by omega) hXc hfib j h2k
  -- the relative homology of `(X, {x₀})` vanishes in degree `j` over `ℚ`
  have hXrel : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of X) ({x₀} : Set X)).homology j) :=
    isZero_relChainsR_homology_of_isZero_abs ℚ (TopCat.of X) ({x₀} : Set X) j hjpos
      (hX j hj1 hj2) (isZero_ratH_singleton X x₀ (j := j - 1) (by omega))
  -- the relative homology of `(X × Y, {x₀} × Y)` vanishes in degree `j` over `ℚ`
  have hrelProd : IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of (X × Y))
      (Prod.fst ⁻¹' ({x₀} : Set X))).homology j) :=
    isZero_relChainsR_rat_of_isIso_relPairMap (ContinuousMap.fst : C(X × Y, X)) x₀ j hiso hXrel
  -- the absolute homology of the fibre `{x₀} × Y ≅ Y` vanishes in degree `j`
  have hfibH : IsZero ((Work.Cohomology.singularChains ℚ
      (TopCat.of ↥(Prod.fst ⁻¹' ({x₀} : Set X)))).homology j) :=
    isZero_ratH_of_homeomorph (fibreHomeo X Y x₀) j (hY j hj1 hj2)
  -- the long exact sequence of the pair `(X × Y, {x₀} × Y)` finishes the job
  have hS := Work.StemsB.relChainsR_exact₂ ℚ (TopCat.of (X × Y))
    (Prod.fst ⁻¹' ({x₀} : Set X)) j
  exact hS.isZero_X₂ (hfibH.eq_zero_of_src _) (hrelProd.eq_zero_of_tgt _)

end Work.Stems
