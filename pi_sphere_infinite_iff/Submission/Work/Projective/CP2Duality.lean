import Mathlib
import Submission.Work.Projective.CPn
import Submission.Work.Projective.Model
import Submission.Work.Projective.t2Space_CP
import Submission.Work.Projective.CP2Concrete
import Submission.Work.Projective.Interface
import Submission.Work.Cohomology.pd_middleDegree_of_good
import Submission.Work.Cohomology.kronH_isIso
import Submission.Work.Cohomology.reducedH0OfTwoPoints
import Submission.Work.Projective.cp2_homology_free

set_option synthInstance.maxHeartbeats 400000

/-!
# The middle intersection form of `ℂP²`, and its numbers, from Poincaré duality

`Submission/Work/Projective/CP2Cohomology.lean` computes the cohomology of the *concrete* manifold
`ℂP²` additively (`H⁰ = H² = H⁴ = ℤ`, odd degrees `0`), and `CP2Concrete.lean` attaches the
hyperplane class `h = cp2H`, the fundamental class `c = cp2C` and the Pontryagin class
`p₁ = 3·(h ⌣ h)` to the workspace's cochain model, leaving as its only geometric input the middle
self-intersection number `m = ⟨h ⌣ h, [ℂP²]⟩`.

This module removes the *specific* input "`m = ±1`" and replaces it by the classical theorem that
computes it, **Poincaré duality in the middle degree**, in the sharp form in which the workspace's
Poincaré-duality project states it (`Work.Cohomology.pd_middleDegree_of_good`, whose input is the
predicate `Work.Cohomology.Good 4 cp2C Set.univ`):

* `Work.Projective.cp2CapMap_bijective` — from `Good 4 cp2C Set.univ` the cap product
  `y ↦ y ⌢ [ℂP²] : H²(ℂP²) → H₂(ℂP²)` is bijective (`pd_middleDegree_of_good`);
* `Work.Projective.cp2SelfIntersection_pm_one_of_good` — **the self-intersection is `±1`**.  The
  proof is the linear algebra of a perfect pairing: `interForm` is
  `(y,z) ↦ ⟨z, y ⌢ c⟩` (`Work.SignatureBordism.interForm_apply_eq_kronH_capPair`), the Kronecker
  pairing `kronH : H² → (H₂ →ₗ ℤ)` is bijective (`Work.Cohomology.kronH_isIso`, for a space whose
  homology is free — `cp2_homology_free`), and the cap product is bijective by duality; hence
  `ℤ⟨h⟩ ⊗ ℤ⟨h⟩ → ℤ` is a perfect pairing, so its `1 × 1` Gram matrix `(m)` is unimodular.

Everything is conditional on the single predicate `Good 4 cp2C Set.univ`, i.e. on Poincaré
duality.  `Work.Projective.cp2_good_univ` shows how that predicate follows from
`pd_good_univ`, whose inputs are the general *gluing step* of Poincaré–Lefschetz duality
(Hatcher's five lemma, the piece currently being proved in
`Submission/Work/Cohomology/pd_good_union.lean`) together with the statement that `cp2C` is a
fundamental class (`hc`) — nothing about `ℂP²` remains.

## Main results

* `Work.Projective.cp2CapMap`, `Work.Projective.cp2CapMap_bijective`;
* `Work.Projective.cp2SelfIntersection_pm_one_of_good`;
* `Work.Projective.cp2Model_of_good` — **an inhabited `CP2Model cp2SSet`**;
* `Work.Projective.cp2_hirzebruchFour_of_good` — `45 · 1 = 3 · 3 · ...`, i.e. the dimension-`4`
  Hirzebruch identity `σ(ℂP²) = p₁(ℂP²)/3` for the concrete manifold, from duality.
-/

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace Work.Projective

open CategoryTheory Limits Work.Cohomology Work.SignatureBordism

noncomputable section

/-! ## Instances for the `TopCat` used by the duality project

`Work.Projective.CPSpace 2 = TopCat.of (CP 2)`; the manifold instances of `Work.Projective.Model`
and `Work.Projective.t2Space_CP` are stated for the type `CP 2`, and the duck-typing of
`TopCat.of` is not used by instance search, so they are re-registered for the type synonym. -/

instance instT2SpaceCPSpaceTwo : T2Space ↥(CPSpace 2) := t2Space_CP 2

instance instCompactSpaceCPSpaceTwo : CompactSpace ↥(CPSpace 2) := compactSpace_CP 2

/-! ## Elementary linear algebra over `ℤ` -/

/-- The image of a generator under a surjective `ℤ`-linear map is a generator. -/
lemma span_singleton_map_eq_top' {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Surjective f)
    (x : M) (hx : Submodule.span ℤ {x} = ⊤) : Submodule.span ℤ {f x} = ⊤ := by
  have h1 : Submodule.map f (Submodule.span ℤ {x}) = Submodule.span ℤ {f x} := by
    rw [Submodule.map_span]; simp
  rw [← h1, hx, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr hf

/-- If `v` generates a `ℤ`-module `N` isomorphic to `ℤ`, there is a linear functional on `N` with
`f v = 1` (normalise the isomorphism so that `v ↦ 1`). -/
lemma dual_eq_one_of_span_top' {N : Type*} [AddCommGroup N] [Module ℤ N]
    (e : N ≃ₗ[ℤ] ℤ) (v : N) (hv : Submodule.span ℤ {v} = ⊤) :
    ∃ f : N →ₗ[ℤ] ℤ, f v = 1 := by
  have hspan : Submodule.span ℤ {(e : N →ₗ[ℤ] ℤ) v} = ⊤ :=
    span_singleton_map_eq_top' (e : N →ₗ[ℤ] ℤ) e.surjective v hv
  have hmem : (1 : ℤ) ∈ Submodule.span ℤ {(e : N →ₗ[ℤ] ℤ) v} := by rw [hspan]; trivial
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨m, hm⟩ := hmem
  have h2 : m * ((e : N →ₗ[ℤ] ℤ) v) = 1 := by simpa [smul_eq_mul] using hm
  have h3 : (e : N →ₗ[ℤ] ℤ) v = 1 ∨ (e : N →ₗ[ℤ] ℤ) v = -1 :=
    Int.eq_one_or_neg_one_of_mul_eq_one (by rw [mul_comm]; exact h2)
  rcases h3 with h | h
  · exact ⟨(e : N →ₗ[ℤ] ℤ), h⟩
  · exact ⟨-(e : N →ₗ[ℤ] ℤ), by rw [LinearMap.neg_apply, h]; norm_num⟩

/-- **A surjective Kronecker-type pairing of generators evaluates to `±1`.**  If
`L : A →ₗ (B →ₗ ℤ)` is surjective, `u` generates `A` and `v` generates `B ≅ ℤ`, then
`(L u) v = ±1`. -/
lemma eval_eq_pm_one_of_generator' {A B : Type*} [AddCommGroup A] [Module ℤ A]
    [AddCommGroup B] [Module ℤ B] (L : A →ₗ[ℤ] (B →ₗ[ℤ] ℤ))
    (hL : Function.Surjective L) (u : A) (hu : Submodule.span ℤ {u} = ⊤)
    (v : B) (f : B →ₗ[ℤ] ℤ) (hf : f v = 1) :
    (L u) v = 1 ∨ (L u) v = -1 := by
  have hspan : Submodule.span ℤ {L u} = ⊤ := span_singleton_map_eq_top' L hL u hu
  have hmem : f ∈ Submodule.span ℤ {L u} := by rw [hspan]; trivial
  rw [Submodule.mem_span_singleton] at hmem
  obtain ⟨m, hm⟩ := hmem
  have hval : (L u) v * m = 1 := by
    have h := congrArg (fun g : B →ₗ[ℤ] ℤ => g v) hm
    rw [LinearMap.smul_apply] at h
    simp only [smul_eq_mul, hf] at h
    rw [mul_comm]; exact h
  exact Int.eq_one_or_neg_one_of_mul_eq_one hval

/-! ## The cap product with the fundamental class of `ℂP²` -/

/-- **The cap product with the fundamental class of `ℂP²`**, as a `ℤ`-linear map
`H²(ℂP²;ℤ) ⟶ H₂(ℂP²;ℤ)`, `y ↦ y ⌢ [ℂP²]`. -/
noncomputable def cp2CapMap :
    (cochainC ℤ cp2SSet).homology 2 →ₗ[ℤ] (chainC ℤ cp2SSet).homology 2 where
  toFun y := (capPair ℤ cp2SSet 2 2) y cp2C
  map_add' y z := by simp
  map_smul' a y := by simp

/-- **Poincaré duality in the middle degree of `ℂP²`**: if the predicate
`Good 4 cp2C Set.univ` of the workspace's duality project holds, then the cap product with the
fundamental class is bijective.  This is `Work.Cohomology.pd_middleDegree_of_good` for `ℂP²`. -/
theorem cp2CapMap_bijective (h : Good 4 cp2C (Set.univ : Set (CPSpace 2)) isOpen_univ) :
    Function.Bijective cp2CapMap := by
  haveI : ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) ↥(CPSpace 2) :=
    instChartedSpaceEuclidean 2
  exact pd_middleDegree_of_good 2 (CPSpace 2) cp2C h

/-- The Kronecker pairing `H²(ℂP²;ℤ) → (H₂(ℂP²;ℤ) →ₗ ℤ)` is bijective: the homology of `ℂP²` is
free in every degree (`Work.Projective.cp2_homology_free`), so the universal-coefficient
identification of the cohomology with the dual of the homology holds
(`Work.Cohomology.kronH_isIso`). -/
theorem cfkronH_two_cp2_bijective :
    Function.Bijective (fun α : (cochainC ℤ cp2SSet).homology 2 => kronH ℤ cp2SSet 2 α) :=
  kronH_isIso (CPSpace 2) (fun n => cp2_homology_free n) 2

/-- The Kronecker pairing in degree `4`, bijective by the same argument. -/
theorem cfkronH_four_cp2_bijective :
    Function.Bijective (fun α : (cochainC ℤ cp2SSet).homology 4 => kronH ℤ cp2SSet 4 α) :=
  kronH_isIso (CPSpace 2) (fun n => cp2_homology_free n) 4

/-! ## The self-intersection of the hyperplane class -/

/-- The self-intersection number `⟨h ⌣ h, [ℂP²]⟩` written with the cap product and the Kronecker
pairing. -/
theorem cp2SelfIntersection_eq_kronH' :
    cp2SelfIntersection
      = kronH ℤ cp2SSet 2 cp2H ((capPair ℤ cp2SSet 2 2) cp2H cp2C) :=
  interForm_apply_eq_kronH_capPair ℤ cp2SSet 2 2 cp2C cp2H cp2H

/-- The top class `h ⌣ h` paired with `cp2C` is the self-intersection number, by definition. -/
theorem h4_cup_self_eq_selfIntersection :
    kronH ℤ cp2SSet 4 (cupH' ℤ cp2SSet 2 2 cp2H cp2H) cp2C = cp2SelfIntersection := rfl

/-- The self-intersection number `⟨h ⌣ h, [ℂP²]⟩` written with the cap product and the Kronecker
pairing. -/
theorem cp2SelfIntersection_eq_kronH :
    cp2SelfIntersection = kronH ℤ cp2SSet 2 cp2H ((capPair ℤ cp2SSet 2 2) cp2H cp2C) :=
  interForm_apply_eq_kronH_capPair ℤ cp2SSet 2 2 cp2C cp2H cp2H

/-- **The middle self-intersection of `ℂP²` is `±1`**, from Poincaré duality.

The intersection form `B(y,z) = ⟨y ⌣ z, [ℂP²]⟩` is `(y,z) ↦ ⟨z, y ⌢ [ℂP²]⟩`: the cap product is
bijective by duality and the Kronecker pairing `H² → (H₂ →ₗ ℤ)` is bijective because the homology
of `ℂP²` is free.  Hence multiplying by `m = B(h,h)` is an automorphism of `ℤ`, i.e. `m = ±1`,
which is exactly the statement that `h ⌣ h` is a generator of `H⁴(ℂP²;ℤ) ≅ ℤ` and that the
intersection form on `H²(ℂP²;ℤ) = ℤ⟨h⟩` is the unimodular form `(m)` with `m = ±1`. -/
theorem cp2SelfIntersection_pm_one_of_good
    (h : Good 4 cp2C (Set.univ : Set (CPSpace 2)) isOpen_univ) :
    cp2SelfIntersection = 1 ∨ cp2SelfIntersection = -1 := by
  have hφ : Function.Bijective cp2CapMap := cp2CapMap_bijective h
  have hψ : Function.Bijective
      (fun α : (cochainC ℤ cp2SSet).homology 2 => kronH ℤ cp2SSet 2 α) :=
    cfkronH_two_cp2_bijective
  -- `H₂(ℂP²;ℤ) ≅ ℤ`, since `H²(ℂP²;ℤ) ≅ ℤ` and the cap product is a bijection
  have eN : (chainC ℤ cp2SSet).homology 2 ≃ₗ[ℤ] ℤ :=
    (LinearEquiv.ofBijective cp2CapMap hφ).symm.trans (redH0_linEquivOfIso cp2CohIso)
  -- `cp2CapMap cp2H` generates `H₂(ℂP²;ℤ)`
  have he : Submodule.span ℤ {cp2CapMap cp2H} = ⊤ :=
    span_singleton_map_eq_top' cp2CapMap hφ.2 cp2H cp2H_span
  obtain ⟨f, hf⟩ := dual_eq_one_of_span_top' eN (cp2CapMap cp2H) he
  have hres := eval_eq_pm_one_of_generator' (kronH ℤ cp2SSet 2) hψ.2 cp2H cp2H_span
    (cp2CapMap cp2H) f hf
  rw [cp2SelfIntersection_eq_kronH]
  exact hres

/-! ## The multiplicative structure: `h ⌣ h` generates `H⁴(ℂP²;ℤ)`

The same perfect-pairing argument, in the form that produces the *ring* statement: the pairing with
the fundamental class, `y ↦ ⟨y, [ℂP²]⟩`, is injective (the fundamental class generates `H₄`) and
surjective (a functional is determined by its value at a generator, and every value is attained),
hence an isomorphism `H⁴(ℂP²;ℤ) ≅ ℤ`.  So a class whose pairing with `[ℂP²]` is `±1` is a
generator; by `cp2SelfIntersection_pm_one_of_good` this applies to `h ⌣ h`. -/

/-- **Evaluation of a functional on `H₄(ℂP²;ℤ)` at the fundamental class.** -/
noncomputable def cp2EvalFun : ((chainC ℤ cp2SSet).homology 4 →ₗ[ℤ] ℤ) →ₗ[ℤ] ℤ where
  toFun f := f cp2C
  map_add' f g := by simp
  map_smul' a f := by simp

/-- **The pairing with the fundamental class**, `y ↦ ⟨y, [ℂP²]⟩ : H⁴(ℂP²;ℤ) → ℤ`. -/
noncomputable def cp2EvalMap : (cochainC ℤ cp2SSet).homology 4 →ₗ[ℤ] ℤ :=
  cp2EvalFun.comp (kronH ℤ cp2SSet 4)

/-- The pairing of `H⁴(ℂP²;ℤ)` with the fundamental class is an isomorphism: injective because
`[ℂP²]` generates `H₄(ℂP²;ℤ)`, surjective because a `ℤ`-linear functional on the cyclic module
`ℤ·[ℂP²]` is determined by, and arbitrary at, its value on the generator. -/
theorem cp2EvalMap_bijective : Function.Bijective cp2EvalMap := by
  refine ⟨?_, ?_⟩
  · intro y z hyz
    have hyz' : (kronH ℤ cp2SSet 4 y) cp2C = (kronH ℤ cp2SSet 4 z) cp2C := hyz
    refine cfkronH_four_cp2_bijective.1 (LinearMap.ext fun w => ?_)
    obtain ⟨a, rfl⟩ := (span_singleton_eq_top_iff' cp2C).mp cp2C_span w
    rw [map_zsmul, map_zsmul, hyz']
  · intro k
    obtain ⟨f₀, hf₀⟩ := dual_eq_one_of_span_top' (redH0_linEquivOfIso cp2HomIso) cp2C cp2C_span
    obtain ⟨z, hz⟩ := cfkronH_four_cp2_bijective.2 (k • f₀)
    have hz' : (kronH ℤ cp2SSet 4) z = k • f₀ := hz
    refine ⟨z, ?_⟩
    show (kronH ℤ cp2SSet 4 z) cp2C = k
    rw [hz', LinearMap.smul_apply, hf₀, smul_eq_mul, mul_one]

/-- **`h ⌣ h` generates `H⁴(ℂP²;ℤ)`**: the multiplicative statement for the cohomology of the
concrete manifold `ℂP²`, from Poincaré duality (`Good 4 cp2C Set.univ`). -/
theorem cp2H_cup_generates_of_good
    (h : Good 4 cp2C (Set.univ : Set (CPSpace 2)) isOpen_univ) :
    Submodule.span ℤ {cupH' ℤ cp2SSet 2 2 cp2H cp2H} = ⊤ := by
  have hm : cp2EvalMap (cupH' ℤ cp2SSet 2 2 cp2H cp2H) = 1 ∨
      cp2EvalMap (cupH' ℤ cp2SSet 2 2 cp2H cp2H) = -1 :=
    cp2SelfIntersection_pm_one_of_good h
  have hsp : Submodule.span ℤ {(1 : ℤ)} = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro z
    rw [show z = z • (1 : ℤ) from (mul_one z).symm]
    exact Submodule.smul_mem _ z (Submodule.subset_span (Set.mem_singleton 1))
  set e : (cochainC ℤ cp2SSet).homology 4 ≃ₗ[ℤ] ℤ :=
    LinearEquiv.ofBijective cp2EvalMap cp2EvalMap_bijective with he
  have hgen : Submodule.span ℤ {e.symm (1 : ℤ)} = ⊤ :=
    span_singleton_map_eq_top' (e.symm : ℤ →ₗ[ℤ] (cochainC ℤ cp2SSet).homology 4)
      e.symm.surjective 1 hsp
  have hneg : Submodule.span ℤ {-(e.symm (1 : ℤ))} = ⊤ := by
    rw [span_singleton_eq_top_iff'] at hgen ⊢
    intro z
    obtain ⟨a, ha⟩ := hgen z
    exact ⟨-a, by rw [ha]; simp⟩
  rcases hm with hm | hm
  · have hx : cupH' ℤ cp2SSet 2 2 cp2H cp2H = e.symm 1 := by
      apply e.injective
      rw [e.apply_symm_apply]
      exact hm
    rw [hx]; exact hgen
  · have hx : cupH' ℤ cp2SSet 2 2 cp2H cp2H = -(e.symm 1) := by
      apply e.injective
      rw [map_neg, e.apply_symm_apply]
      exact hm
    rw [hx]; exact hneg

/-! ## The numbers of `ℂP²` and the inhabited model -/

/-- **The generator check for the concrete manifold `ℂP²`**, from Poincaré duality:
`⟨p₁(TℂP²), [ℂP²]⟩ = 3 · σ(ℂP²)`. -/
theorem cp2_hirzebruchFour_of_good
    (h : Good 4 cp2C (Set.univ : Set (CPSpace 2)) isOpen_univ) :
    HirzebruchFour (sigma 2 cp2SSet cp2C) (p₁Number cp2SSet cp2C cp2P1) :=
  cp2_hirzebruchFour (cp2SelfIntersection_pm_one_of_good h)

/-- **An inhabited `CP2Model` for the concrete manifold `ℂP²`**: the hyperplane class `cp2H`, the
fundamental class `±cp2C` (chosen so that the pairing with `h ⌣ h` is `1`, i.e. `cp2C` with the
orientation for which the intersection form is `(1)`), and `p₁ = 3·(h ⌣ h)`.

The orientation choice is the only freedom: Poincaré duality gives `⟨h ⌣ h, cp2C⟩ = ±1`, so one of
`cp2C`, `-cp2C` satisfies the normalisation `⟨h ⌣ h, c⟩ = 1` of the interface. -/
theorem cp2Model_of_good
    (h : Good 4 cp2C (Set.univ : Set (CPSpace 2)) isOpen_univ) :
    Nonempty (CP2Model cp2SSet) := by
  rcases cp2SelfIntersection_pm_one_of_good h with hm | hm
  · refine ⟨⟨cp2H, cp2C, cp2P1, cp2H_span, rfl, ?_⟩⟩
    rw [h4_cup_self_eq_selfIntersection]
    exact hm
  · refine ⟨⟨cp2H, -cp2C, cp2P1, cp2H_span, rfl, ?_⟩⟩
    show kronH ℤ cp2SSet 4 (cupH' ℤ cp2SSet 2 2 cp2H cp2H) (-cp2C) = 1
    rw [map_neg, h4_cup_self_eq_selfIntersection, hm]
    norm_num

/-- **The dimension-`4` Hirzebruch identity for the inhabited model of `ℂP²`.** -/
theorem cp2Model_hirzebruchFour_of_good
    (h : Good 4 cp2C (Set.univ : Set (CPSpace 2)) isOpen_univ) :
    ∃ M : CP2Model cp2SSet,
      HirzebruchFour (sigma 2 cp2SSet M.c) (p₁Number cp2SSet M.c M.p₁) := by
  obtain ⟨M⟩ := cp2Model_of_good h
  exact ⟨M, CP2Model.hirzebruchFour cp2SSet M⟩

/-- **The numbers of `ℂP²`**: for the model produced by `cp2Model_of_good`, the signature is `1`
and the `p₁`-number is `3` — the pair `(1, 3)` of the dimension-`4` generator. -/
theorem cp2_numbers_of_good (h : Good 4 cp2C (Set.univ : Set (CPSpace 2)) isOpen_univ) :
    ∃ M : CP2Model cp2SSet,
      Work.SignatureBordism.sigma 2 cp2SSet M.c = 1 ∧
      Work.SignatureBordism.p₁Number cp2SSet M.c M.p₁ = 3 := by
  obtain ⟨M⟩ := cp2Model_of_good h
  exact ⟨M, CP2Model.sigma cp2SSet M, CP2Model.p1Number cp2SSet M⟩

end

end Work.Projective
