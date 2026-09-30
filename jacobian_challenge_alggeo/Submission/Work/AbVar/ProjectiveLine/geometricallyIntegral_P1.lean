/-
Area AV: the projective line is geometrically integral.

`Work.AbVar.P1 k = Proj k[X₀,X₁]` (standard grading), and `GeometricallyIntegral (P1 k).hom` says
that for every field extension `K/k` the fibre product `P1 k ×_k Spec K` is integral.

The route taken here avoids Mathlib's missing base change theorem for `Proj`:  we prove
`GeometricallyIntegral (Proj.toSpecZero 𝒜)` for `𝒜 = k[X₀,X₁]` graded by total degree, then
transfer to `(P1 k).hom = Proj.toSpecZero 𝒜 ≫ Spec.map (p1BaseEquiv k)` (an isomorphism).

`Proj 𝒜` is covered by the two standard charts `D₊(X₀)`, `D₊(X₁)`, both of which are
isomorphic to `𝔸¹`, and they meet (the zero ideal is a point of `Proj  𝒜` lying in both).
Base changing along `Spec K ⟶ Spec (𝒜 0)` turns the charts into
`Spec (Away 𝒜 (X i) ⊗[𝒜 0] K)`, which is a domain since `Away 𝒜 (X i) ≃ 𝒜 0[T]`.
-/
import Mathlib
import Submission.Work.AbVar.Basic
import Submission.Work.AbVar.ProjectiveLine
import Submission.Work.AbVar.ProjectiveLine.awayTensorIsDomain

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.AbVar.ProjectiveLine

open CategoryTheory Limits AlgebraicGeometry
open HomogeneousLocalization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Two elementary topological lemmas -/

theorem inter_nonempty_of_isOpen_of_subset_chart {X : Type*} [TopologicalSpace X]
    {W : Set X} [IrreducibleSpace W] {s t : Set X}
    (hs : IsOpen s) (ht : IsOpen t) (hsne : (s ∩ W).Nonempty) (htne : (t ∩ W).Nonempty) :
    (s ∩ t ∩ W).Nonempty := by
  have hs' : IsOpen ((Subtype.val : W → X) ⁻¹' s) := hs.preimage continuous_subtype_val
  have ht' : IsOpen ((Subtype.val : W → X) ⁻¹' t) := ht.preimage continuous_subtype_val
  obtain ⟨x, hxs, hxW⟩ := hsne
  obtain ⟨y, hyt, hyW⟩ := htne
  have hx' : ((Subtype.val : W → X) ⁻¹' s).Nonempty := ⟨⟨x, hxW⟩, hxs⟩
  have hy' : ((Subtype.val : W → X) ⁻¹' t).Nonempty := ⟨⟨y, hyW⟩, hyt⟩
  obtain ⟨z, hzs, hzt⟩ := nonempty_preirreducible_inter hs' ht' hx' hy'
  simp only [Set.mem_preimage] at hzs hzt
  exact ⟨z.1, ⟨hzs, hzt⟩, z.2⟩

/-- A topological space covered by two irreducible open subsets with nonempty intersection is
irreducible. -/
theorem irreducibleSpace_of_two_opens {X : Type*} [TopologicalSpace X]
    {U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = Set.univ)
    [IrreducibleSpace U] [IrreducibleSpace V] (hne : (U ∩ V).Nonempty) :
    IrreducibleSpace X := by
  obtain ⟨p, hpU, hpV⟩ := hne
  have hdecomp : ∀ s : Set X, s.Nonempty → (s ∩ U).Nonempty ∨ (s ∩ V).Nonempty := by
    intro s ⟨x, hx⟩
    rcases (show x ∈ U ∪ V from hcov ▸ Set.mem_univ x) with h | h
    · exact Or.inl ⟨x, hx, h⟩
    · exact Or.inr ⟨x, hx, h⟩
  have hpre : PreirreducibleSpace X := PreirreducibleSpace.of_forall_nonempty_inter (by
    intro s t hs ht hsne htne
    rcases hdecomp s hsne with h1 | h1
    · rcases hdecomp t htne with h2 | h2
      · obtain ⟨x, ⟨hxs, hxt⟩, -⟩ := inter_nonempty_of_isOpen_of_subset_chart (W := U) hs ht h1 h2
        exact ⟨x, hxs, hxt⟩
      · obtain ⟨x, ⟨hxs, hxV⟩, hxU⟩ :=
          inter_nonempty_of_isOpen_of_subset_chart (W := U) hs hV h1 ⟨p, hpV, hpU⟩
        obtain ⟨y, ⟨hyt, hys⟩, -⟩ :=
          inter_nonempty_of_isOpen_of_subset_chart (W := V) ht hs h2 ⟨x, hxs, hxV⟩
        exact ⟨y, hys, hyt⟩
    · rcases hdecomp t htne with h2 | h2
      · obtain ⟨x, ⟨hxs, hxU⟩, hxV⟩ :=
          inter_nonempty_of_isOpen_of_subset_chart (W := V) hs hU h1 ⟨p, hpU, hpV⟩
        obtain ⟨y, ⟨hyt, hys⟩, -⟩ :=
          inter_nonempty_of_isOpen_of_subset_chart (W := U) ht hs h2 ⟨x, hxs, hxU⟩
        exact ⟨y, hys, hyt⟩
      · obtain ⟨x, ⟨hxs, hxt⟩, -⟩ := inter_nonempty_of_isOpen_of_subset_chart (W := V) hs ht h1 h2
        exact ⟨x, hxs, hxt⟩)
  exact IrreducibleSpace.mk (toPreirreducibleSpace := hpre) ⟨p⟩

/-! ## The standard charts of `Proj k[X₀,X₁]` -/

section Chart

variable (k : Type*) [Field k]

/-- The `i`-th coordinate of `k[X₀,X₁]` is homogeneous of degree one. -/
lemma X_mem_grading (k : Type*) [Field k] (i : Fin 2) :
    (MvPolynomial.X i : MvPolynomial (Fin 2) k) ∈ P1Grading k 1 :=
  (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X k i)

/-- The structure morphism of `Proj k[X₀,X₁]` restricted to the chart `D₊(Xᵢ)` is `Spec` of the
structure map of the chart ring. -/
lemma awayι_toSpecZero_eq (i : Fin 2) :
    Proj.awayι (P1Grading k) (MvPolynomial.X i) (X_mem_grading k i) Nat.one_pos ≫
        Proj.toSpecZero (P1Grading k) =
      Spec.map (CommRingCat.ofHom (algebraMap ↥(P1Grading k 0)
        (Away (P1Grading k) (MvPolynomial.X i)))) := by
  rw [Proj.awayι_toSpecZero]

/-- The coordinates span the irrelevant ideal of the standard grading. -/
lemma irrelevant_le_span_X (k : Type*) [Field k] :
    (HomogeneousIdeal.irrelevant (P1Grading k)).toIdeal ≤
      Ideal.span (Set.range (fun i : Fin 2 => (MvPolynomial.X i : MvPolynomial (Fin 2) k))) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro m hm p hp
  have hp' : p ∈ P1Grading k m := hp
  change p ∈ Ideal.span (Set.range (fun i : Fin 2 => (MvPolynomial.X i : MvPolynomial (Fin 2) k)))
  rw [← Set.image_univ (f := fun i : Fin 2 => (MvPolynomial.X i : MvPolynomial (Fin 2) k))]
  rw [MvPolynomial.mem_ideal_span_X_image]
  intro d hd
  by_contra h
  push Not at h
  have hdeg : Finsupp.degree d ≠ m := by
    rw [show d = 0 from Finsupp.ext (fun i => h i (Set.mem_univ i)),
      show Finsupp.degree (0 : Fin 2 →₀ ℕ) = 0 by simp]
    omega
  exact (MvPolynomial.mem_support_iff.mp hd) (MvPolynomial.IsHomogeneous.coeff_eq_zero hp' hdeg)

/-- The two standard charts of `P¹` cover it. -/
theorem iSup_basicOpen_X_eq_top (k : Type*) [Field k] :
    (⨆ i : Fin 2, Proj.basicOpen (P1Grading k) (MvPolynomial.X i)) = ⊤ :=
  Proj.iSup_basicOpen_eq_top (P1Grading k) (fun i : Fin 2 => MvPolynomial.X i)
    (irrelevant_le_span_X k)

/-- The two standard charts of `P¹` meet: the zero ideal is a point of `Proj k[X₀,X₁]` belonging
to both charts. -/
theorem basicOpen_X_inf_ne_bot (k : Type*) [Field k] :
    (Proj.basicOpen (P1Grading k) (MvPolynomial.X 0) ⊓
      Proj.basicOpen (P1Grading k) (MvPolynomial.X 1)) ≠ ⊥ := by
  intro hbot
  let x : ProjectiveSpectrum (P1Grading k) :=
    ⟨⊥, by rw [HomogeneousIdeal.toIdeal_bot]; exact Ideal.isPrime_bot, by
      intro h
      have hX : (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ∈
          (⊥ : HomogeneousIdeal (P1Grading k)) :=
        h (HomogeneousIdeal.mem_irrelevant_of_mem (P1Grading k) Nat.one_pos (X_mem_grading k 0))
      have hX' : (MvPolynomial.X 0 : MvPolynomial (Fin 2) k) ∈
          (⊥ : Ideal (MvPolynomial (Fin 2) k)) := hX
      exact MvPolynomial.X_ne_zero 0 (Ideal.mem_bot.mp hX')⟩
  have hmem : x ∈ Proj.basicOpen (P1Grading k) (MvPolynomial.X 0) ⊓
      Proj.basicOpen (P1Grading k) (MvPolynomial.X 1) := by
    constructor
    · exact (Proj.mem_basicOpen (P1Grading k) (MvPolynomial.X 0) x).mpr
        (fun h => MvPolynomial.X_ne_zero 0 h)
    · exact (Proj.mem_basicOpen (P1Grading k) (MvPolynomial.X 1) x).mpr
        (fun h => MvPolynomial.X_ne_zero 1 h)
  rw [hbot] at hmem
  exact hmem

end Chart


/-! ## Integrality of the base changed projective line -/

section Integrality

variable (k : Type u) [Field k]

/-- The chart ring of `P¹`, tensored with a field extension of `𝒜 0`, is a domain. -/
theorem isDomain_chart_tensor (i : Fin 2) (K : Type u) [Field K]
    [Algebra ↥(P1Grading k 0) K] :
    IsDomain (TensorProduct ↥(P1Grading k 0) (Away (P1Grading k) (MvPolynomial.X i)) K) :=
  Work.AbVar.ProjectiveLine.awayTensorIsDomain k i K

/-- `Spec (𝒜 0)` is a one point scheme, so every morphism from `Spec K` to it is surjective. -/
theorem subsingleton_spec_base (k : Type u) [Field k] :
    Subsingleton ↥(Spec (CommRingCat.of ↥(P1Grading k 0))) := by
  have : IsIso (CommRingCat.ofHom (Work.AbVar.p1BaseEquiv k).toRingHom) :=
    (Work.AbVar.p1BaseEquiv k).toCommRingCatIso.isIso_hom
  haveI : IsIso (Spec.map (CommRingCat.ofHom (Work.AbVar.p1BaseEquiv k).toRingHom)) :=
    inferInstance
  exact ((Scheme.homeoOfIso (asIso (Spec.map
      (CommRingCat.ofHom (Work.AbVar.p1BaseEquiv k).toRingHom)))).toEquiv.subsingleton_congr).mpr
    inferInstance

/-- The supremum of a two element family in a complete lattice. -/
theorem iSup_fin_two {α : Type u} [CompleteLattice α] (f : Fin 2 → α) :
    (⨆ i : Fin 2, f i) = f 0 ⊔ f 1 := by
  refine le_antisymm (iSup_le ?_) (sup_le (le_iSup f 0) (le_iSup f 1))
  intro i
  fin_cases i <;> simp

/-- The base change of `Proj k[X₀,X₁]` along `Spec K ⟶ Spec (𝒜 0)` is integral. -/
theorem isIntegral_pullback_toSpecZero (K : Type u) [Field K]
    [Algebra ↥(P1Grading k 0) K] :
    IsIntegral (Limits.pullback (Proj.toSpecZero (P1Grading k))
      (Spec.map (CommRingCat.ofHom (algebraMap ↥(P1Grading k 0) K)))) := by
  set Z : Scheme := Limits.pullback (Proj.toSpecZero (P1Grading k))
    (Spec.map (CommRingCat.ofHom (algebraMap ↥(P1Grading k 0) K))) with hZ
  set t : Proj (P1Grading k) ⟶ Spec (CommRingCat.of ↥(P1Grading k 0)) :=
    Proj.toSpecZero (P1Grading k) with ht
  set y : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ↥(P1Grading k 0)) :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥(P1Grading k 0) K)) with hy
  haveI : Subsingleton ↥(Spec (CommRingCat.of ↥(P1Grading k 0))) := subsingleton_spec_base k
  have hfsurj : Surjective (pullback.fst t y) :=
    have : Surjective y := ⟨fun x => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
    inferInstance
  -- the two chart pullbacks are integral
  have hpiece (i : Fin 2) : IsIntegral (Limits.pullback
      (Proj.awayι (P1Grading k) (MvPolynomial.X i) (X_mem_grading k i) Nat.one_pos)
      (pullback.fst t y)) := by
    have h1 : IsIntegral (Limits.pullback
        (Proj.awayι (P1Grading k) (MvPolynomial.X i) (X_mem_grading k i) Nat.one_pos ≫ t) y) := by
      rw [ht, hy, awayι_toSpecZero_eq k i]
      haveI : IsIntegral (Spec (CommRingCat.of (TensorProduct ↥(P1Grading k 0)
          (Away (P1Grading k) (MvPolynomial.X i)) K))) :=
        (affine_isIntegral_iff _).mpr (isDomain_chart_tensor k (i := i) K)
      exact IsIntegral.of_isIso (pullbackSpecIso ↥(P1Grading k 0)
        (Away (P1Grading k) (MvPolynomial.X i)) K).inv
    exact IsIntegral.of_isIso (pullbackRightPullbackFstIso t y
      (Proj.awayι (P1Grading k) (MvPolynomial.X i) (X_mem_grading k i) Nat.one_pos)).inv
  -- the ranges of the chart maps
  have hrange (i : Fin 2) : (pullback.snd
        (Proj.awayι (P1Grading k) (MvPolynomial.X i) (X_mem_grading k i) Nat.one_pos)
        (pullback.fst t y)).opensRange =
      (pullback.fst t y) ⁻¹ᵁ Proj.basicOpen (P1Grading k) (MvPolynomial.X i) := by
    rw [Scheme.Hom.opensRange_pullbackSnd, Proj.opensRange_awayι]
  -- the chart ranges are integral, hence irreducible
  haveI hInt (i : Fin 2) : IsIntegral (((pullback.snd (Proj.awayι (P1Grading k)
      (MvPolynomial.X i) (X_mem_grading k i) Nat.one_pos)
      (pullback.fst t y)).opensRange).toScheme) := by
    haveI : IsIntegral (Limits.pullback (Proj.awayι (P1Grading k) (MvPolynomial.X i)
        (X_mem_grading k i) Nat.one_pos) (pullback.fst t y)) := hpiece i
    exact IsIntegral.of_isIso (IsOpenImmersion.isoOfRangeEq (pullback.snd
      (Proj.awayι (P1Grading k) (MvPolynomial.X i) (X_mem_grading k i) Nat.one_pos)
      (pullback.fst t y)) ((pullback.snd (Proj.awayι (P1Grading k) (MvPolynomial.X i)
      (X_mem_grading k i) Nat.one_pos) (pullback.fst t y)).opensRange).ι
      (by simp [Scheme.Hom.coe_opensRange])).hom
  haveI hIrr (i : Fin 2) : IrreducibleSpace ↥((pullback.snd (Proj.awayι (P1Grading k)
      (MvPolynomial.X i) (X_mem_grading k i) Nat.one_pos) (pullback.fst t y)).opensRange) := by
    show IrreducibleSpace ↥(((pullback.snd (Proj.awayι (P1Grading k) (MvPolynomial.X i)
      (X_mem_grading k i) Nat.one_pos) (pullback.fst t y)).opensRange).toScheme)
    have := hInt i
    exact inferInstance
  -- the chart ranges cover
  have hcov : (⨆ i : Fin 2, (pullback.snd (Proj.awayι (P1Grading k) (MvPolynomial.X i)
      (X_mem_grading k i) Nat.one_pos) (pullback.fst t y)).opensRange) = ⊤ := by
    rw [show (⨆ i : Fin 2, (pullback.snd (Proj.awayι (P1Grading k) (MvPolynomial.X i)
        (X_mem_grading k i) Nat.one_pos) (pullback.fst t y)).opensRange) =
        ⨆ i : Fin 2, (pullback.fst t y) ⁻¹ᵁ Proj.basicOpen (P1Grading k) (MvPolynomial.X i)
      from iSup_congr fun i => hrange i]
    rw [← Scheme.Hom.preimage_iSup, iSup_basicOpen_X_eq_top k, Scheme.Hom.preimage_top]
  haveI : IsReduced Z := by
    let Ufam : Fin 2 → Z.Opens := fun i => (pullback.snd (Proj.awayι (P1Grading k) (MvPolynomial.X i)
      (X_mem_grading k i) Nat.one_pos) (pullback.fst t y)).opensRange
    let 𝒰 : Z.OpenCover := Z.openCoverOfIsOpenCover Ufam hcov
    haveI : ∀ i : 𝒰.I₀, IsReduced (𝒰.X i) := by
      intro i
      show IsReduced ((Ufam i).toScheme)
      have := hInt i
      exact inferInstance
    exact IsReduced.of_openCover Z 𝒰
  -- the charts cover and meet
  have hcover : (↑((pullback.snd (Proj.awayι (P1Grading k) (MvPolynomial.X 0)
        (X_mem_grading k 0) Nat.one_pos) (pullback.fst t y)).opensRange) : Set Z) ∪
      ↑((pullback.snd (Proj.awayι (P1Grading k) (MvPolynomial.X 1)
        (X_mem_grading k 1) Nat.one_pos) (pullback.fst t y)).opensRange) = Set.univ := by
    ext z
    constructor
    · intro _; trivial
    · intro _
      have hz : pullback.fst t y z ∈ (⨆ i : Fin 2,
          Proj.basicOpen (P1Grading k) (MvPolynomial.X i)) := by
        rw [iSup_basicOpen_X_eq_top k]; trivial
      change pullback.fst t y z ∈ ((⨆ i : Fin 2, Proj.basicOpen (P1Grading k)
        (MvPolynomial.X i) : (Proj (P1Grading k)).Opens) : Set (Proj (P1Grading k))) at hz
      rw [TopologicalSpace.Opens.coe_iSup, Set.mem_iUnion] at hz
      obtain ⟨i, hi⟩ := hz
      fin_cases i
      · exact Or.inl (by rw [hrange 0]; exact hi)
      · exact Or.inr (by rw [hrange 1]; exact hi)
  have hne : (((pullback.snd (Proj.awayι (P1Grading k) (MvPolynomial.X 0)
        (X_mem_grading k 0) Nat.one_pos) (pullback.fst t y)).opensRange ⊓
      (pullback.snd (Proj.awayι (P1Grading k) (MvPolynomial.X 1)
        (X_mem_grading k 1) Nat.one_pos) (pullback.fst t y)).opensRange : Z.Opens) :
      Set Z).Nonempty := by
    rw [hrange 0, hrange 1, ← Scheme.Hom.preimage_inf]
    have hmem : ((Proj.basicOpen (P1Grading k) (MvPolynomial.X 0) ⊓
        Proj.basicOpen (P1Grading k) (MvPolynomial.X 1) : (Proj (P1Grading k)).Opens) :
        Set (Proj (P1Grading k))).Nonempty := by
      by_contra hempty
      exact basicOpen_X_inf_ne_bot k
        (le_antisymm (fun x hx => absurd ⟨x, hx⟩ hempty) bot_le)
    obtain ⟨z, hz⟩ := hmem
    change z ∈ ((Proj.basicOpen (P1Grading k) (MvPolynomial.X 0) ⊓
      Proj.basicOpen (P1Grading k) (MvPolynomial.X 1) : (Proj (P1Grading k)).Opens) :
      Set (Proj (P1Grading k))) at hz
    rw [TopologicalSpace.Opens.coe_inf] at hz
    obtain ⟨w, hw⟩ := hfsurj.1 z
    refine ⟨w, ?_, ?_⟩
    · show pullback.fst t y w ∈ Proj.basicOpen (P1Grading k) (MvPolynomial.X 0)
      rw [hw]; exact hz.1
    · show pullback.fst t y w ∈ Proj.basicOpen (P1Grading k) (MvPolynomial.X 1)
      rw [hw]; exact hz.2
  haveI : IrreducibleSpace Z :=
    irreducibleSpace_of_two_opens
      (U := ↑((pullback.snd (Proj.awayι (P1Grading k) (MvPolynomial.X 0)
        (X_mem_grading k 0) Nat.one_pos) (pullback.fst t y)).opensRange))
      (V := ↑((pullback.snd (Proj.awayι (P1Grading k) (MvPolynomial.X 1)
        (X_mem_grading k 1) Nat.one_pos) (pullback.fst t y)).opensRange))
      (TopologicalSpace.Opens.isOpen _) (TopologicalSpace.Opens.isOpen _) hcover hne
  exact isIntegral_of_irreducibleSpace_of_isReduced Z

end Integrality

/-- `Proj k[X₀,X₁]` is geometrically integral over `Spec (𝒜 0)`. -/
theorem geometricallyIntegral_toSpecZero (k : Type u) [Field k] :
    GeometricallyIntegral (Proj.toSpecZero (P1Grading k)) := by
  refine ⟨fun {K} _ y Z fst snd h => ?_⟩
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective y
  subst hψ
  letI : Algebra ↥(P1Grading k 0) K := ψ.hom.toAlgebra
  have hy : Spec.map ψ = Spec.map (CommRingCat.ofHom (algebraMap ↥(P1Grading k 0) K)) := rfl
  rw [hy] at h
  suffices IsIntegral (Limits.pullback (Proj.toSpecZero (P1Grading k))
      (Spec.map (CommRingCat.ofHom (algebraMap ↥(P1Grading k 0) K)))) from
    IsIntegral.of_isIso h.isoPullback.inv
  exact isIntegral_pullback_toSpecZero k K

/-- Composing a geometrically integral morphism with an isomorphism of the target keeps it
geometrically integral. -/
theorem geometricallyIntegral_comp_iso {X Y Z : Scheme.{u}} {f : X ⟶ Y} (e : Y ⟶ Z) [IsIso e]
    (hf : GeometricallyIntegral f) : GeometricallyIntegral (f ≫ e) := by
  refine ⟨fun {K} _ g W fst snd h => ?_⟩
  have hbot : IsPullback (g ≫ inv e) (𝟙 (Spec (CommRingCat.of K))) e ((g ≫ inv e) ≫ e) :=
    IsPullback.of_vert_isIso ⟨by simp⟩
  have hcomm : fst ≫ f = snd ≫ (g ≫ inv e) := by
    rw [← cancel_mono e]
    rw [Category.assoc, h.w]
    simp [Category.assoc]
  have hL : IsPullback fst (snd ≫ 𝟙 (Spec (CommRingCat.of K))) (f ≫ e) ((g ≫ inv e) ≫ e) := by
    simpa using h
  exact GeometricallyIntegral.geometrically_isIntegral (f := f) (g ≫ inv e) fst snd
    ((IsPullback.paste_vert_iff hbot hcomm).mp hL)

/- `Proj k[X₀,X₁]` is the projective line, and `(P1 k).hom` is `Proj.toSpecZero` composed with
an isomorphism; hence `(P1 k).hom` is geometrically integral. -/
open CategoryTheory in
theorem geometricallyIntegral_P1 (k : Type*) [Field k] :
    AlgebraicGeometry.GeometricallyIntegral (Work.AbVar.P1 k).hom := by
  haveI : IsIso (CommRingCat.ofHom (Work.AbVar.p1BaseEquiv k).toRingHom) :=
    (Work.AbVar.p1BaseEquiv k).toCommRingCatIso.isIso_hom
  haveI : IsIso (Spec.map (CommRingCat.ofHom (Work.AbVar.p1BaseEquiv k).toRingHom)) :=
    inferInstance
  rw [Work.AbVar.p1_hom k]
  exact geometricallyIntegral_comp_iso _ (geometricallyIntegral_toSpecZero k)

end Work.AbVar.ProjectiveLine
