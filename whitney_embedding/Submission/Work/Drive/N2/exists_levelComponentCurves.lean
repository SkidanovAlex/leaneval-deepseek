import Mathlib
import Submission.Work.Drive.N2.regularLevelCircles
import Submission.Work.Drive.N2.levelTangentIdentification
import Submission.Work.Drive.N2.mfderiv_restrict_opens
import Submission.Work.Drive.Morse
import Submission.Work.OneDim.classify_connected_one_manifold
import Submission.Work.OneDim.assembly_of_components

/-!
# The connected components of a regular level set of a function on a compact surface

Let `M` be a compact smooth surface, `f : M → ℝ` a smooth function and `a` a regular value of `f`
which is attained.  Then `f ⁻¹' {a}` is a finite disjoint union of smoothly embedded circles, and the
target `Work.Drive.N2.exists_levelComponentCurves` packages them as finitely many `C^∞` curves
`γ : Fin n → ℝ → M` which are `1`-periodic, injective on `[0,1)`, lie on the level set, are
immersive, whose derivative spans `ker (df)`, and whose ranges are exactly the level set.

The starting point is `Work.Drive.N2.exists_circleMap_component` (`regularLevelCircles.lean`): each
connected component of `LevelSet f a` — a compact connected smooth `1`-manifold — is the image of a
smooth injective map `Circle → M`.  The extra information needed here is that this map is an
*immersion* (`Work.Drive.N2.levelTangent_subtypeVal_ne_zero`), and that the standard wrapping
`ℝ → Circle`, `x ↦ exp (2π x I)`, is a `1`-periodic immersion (this file,
`circExp_mfderiv_ne_zero`).
-/

set_option backward.isDefEq.respectTransparency false

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Function

noncomputable section

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-! ### The standard `1`-periodic immersion `ℝ → Circle` -/

/-- The standard wrapping of the real line onto the circle, `x ↦ exp (2π x I)`.  It is
`1`-periodic and has nowhere vanishing derivative. -/
def circExp (x : ℝ) : Circle := Circle.exp (2 * Real.pi * x)

lemma circExp_contMDiff : ContMDiff 𝓘(ℝ, ℝ) (𝓡 1) ∞ circExp := by
  have h : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (fun x : ℝ => 2 * Real.pi * x) :=
    (contDiff_const.mul contDiff_id).contMDiff
  exact contMDiff_circleExp.comp h

lemma circExp_add_one (x : ℝ) : circExp (x + 1) = circExp x := by
  simp only [circExp]
  rw [show 2 * Real.pi * (x + 1) = 2 * Real.pi * x + 2 * Real.pi by ring]
  exact Circle.exp_add_two_pi _

lemma circExp_surjective : Surjective circExp := by
  intro z
  obtain ⟨s, hs⟩ := Circle.exp_surjective z
  refine ⟨s / (2 * Real.pi), ?_⟩
  rw [circExp]
  have h2 : 2 * Real.pi * (s / (2 * Real.pi)) = s := by field_simp
  rw [h2, hs]

lemma circExp_eq_iff {x y : ℝ} : circExp x = circExp y ↔ ∃ k : ℤ, x = y + k := by
  simp only [circExp]
  rw [Circle.exp_eq_exp]
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    have h2 : (2 * Real.pi) ≠ 0 := by positivity
    refine mul_left_cancel₀ h2 ?_
    rw [hm]; ring
  · rintro ⟨k, hk⟩
    subst hk
    refine ⟨k, ?_⟩
    ring

lemma circExp_injOn_Ico : InjOn circExp (Ico 0 1) := by
  intro x hx y hy hxy
  simp only [circExp] at hxy
  have hx' : 2 * Real.pi * x ∈ Ico 0 (2 * Real.pi) :=
    ⟨by nlinarith [Real.pi_pos, hx.1], by nlinarith [Real.pi_pos, hx.2]⟩
  have hy' : 2 * Real.pi * y ∈ Ico 0 (2 * Real.pi) :=
    ⟨by nlinarith [Real.pi_pos, hy.1], by nlinarith [Real.pi_pos, hy.2]⟩
  have h := Circle.exp_injOn_Ico (a := 0) (b := 2 * Real.pi) (by rw [sub_zero]) hx' hy' hxy
  exact mul_left_cancel₀ (by positivity : (2 * Real.pi) ≠ 0) h

lemma circExp_mfderiv_ne_zero (t : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) (𝓡 1) circExp t ≠ 0 := by
  haveI : Fact (Module.finrank ℝ ℂ = 1 + 1) := ⟨by rw [Complex.finrank_real_complex]⟩
  have hcoe : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) ∞ (fun z : Circle => (z : ℂ)) := contMDiff_coe_sphere
  have hfun : ((fun z : Circle => (z : ℂ)) ∘ circExp)
      = fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) := by
    funext x
    exact Circle.coe_exp (2 * Real.pi * x)
  have hchain : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ((fun z : Circle => (z : ℂ)) ∘ circExp) t
      = (mfderiv (𝓡 1) 𝓘(ℝ, ℂ) (fun z : Circle => (z : ℂ)) (circExp t)).comp
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) circExp t) :=
    mfderiv_comp t (hcoe.contMDiffAt.mdifferentiableAt (by simp))
      (circExp_contMDiff.contMDiffAt.mdifferentiableAt (by simp))
  have htarget : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ)
      (fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)) t ≠ 0 := by
    rw [mfderiv_eq_fderiv]
    have h1 : HasDerivAt (fun w : ℂ => w * Complex.I) (Complex.I)
        (((2 * Real.pi * t : ℝ)) : ℂ) := by
      simpa using (hasDerivAt_id ((((2 * Real.pi * t : ℝ)) : ℂ))).mul_const Complex.I
    have hA := (Complex.hasDerivAt_exp ((((2 * Real.pi * t : ℝ)) : ℂ) * Complex.I)).comp
        ((((2 * Real.pi * t : ℝ)) : ℂ)) h1
    have hg : HasDerivAt (fun y : ℝ => ((2 * Real.pi * y : ℝ) : ℂ))
        (((2 * Real.pi : ℝ)) : ℂ) t := by
      have h0 : HasDerivAt (fun x : ℝ => 2 * Real.pi * x) (2 * Real.pi) t := by
        simpa using (hasDerivAt_id (𝕜 := ℝ) t).const_mul (2 * Real.pi)
      exact h0.ofReal_comp
    have hC := HasDerivAt.comp (𝕜 := ℝ) (𝕜' := ℂ) t hA hg
    have hfl : (fun x : ℝ => Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))
        = ((Complex.exp ∘ fun w : ℂ => w * Complex.I) ∘
            fun y : ℝ => ((2 * Real.pi * y : ℝ) : ℂ)) := by
      funext x; rfl
    rw [hfl, hC.hasFDerivAt.fderiv]
    intro hz
    have h2 : Complex.exp ((↑(2 * Real.pi * t) : ℂ) * Complex.I) * Complex.I
        * ((2 * Real.pi : ℝ) : ℂ) = 0 := by
      have h3 := congrArg (fun L : ℝ →L[ℝ] ℂ => L 1) hz
      simpa [ContinuousLinearMap.toSpanSingleton_apply] using h3
    exact (mul_ne_zero (mul_ne_zero (Complex.exp_ne_zero _) Complex.I_ne_zero)
      (Complex.ofReal_ne_zero.mpr (by positivity))) h2
  intro h0
  have hthis : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℂ) ((fun z : Circle => (z : ℂ)) ∘ circExp) t = 0 := by
    rw [hchain, h0, ContinuousLinearMap.comp_zero]
  rw [hfun] at hthis
  exact htarget hthis

/-! ### Small linear-algebra lemmas -/

/-- If `B` is surjective then `A ∘ B = 0` forces `A = 0`. -/
lemma eq_zero_of_comp_eq_zero_of_surjective {E F G : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] {A : E →L[ℝ] F} {B : G →L[ℝ] E} (hB : Surjective B) (h : A.comp B = 0) :
    A = 0 := by
  ext x
  obtain ⟨y, rfl⟩ := hB x
  have := congrArg (fun L : G →L[ℝ] F => L y) h
  simpa using this

/-- A nonzero linear map between `1`-dimensional normed spaces is surjective. -/
lemma surjective_of_ne_zero_of_finrank_eq_one {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (hF : Module.finrank ℝ F = 1)
    (L : E →L[ℝ] F) (hL : L ≠ 0) : Surjective L := by
  have hnebot : (L : E →ₗ[ℝ] F).range ≠ ⊥ := by
    intro h
    exact hL (ContinuousLinearMap.ext fun z => by
      have hz : (L : E →ₗ[ℝ] F) z ∈ (⊥ : Submodule ℝ F) := by
        rw [← h]; exact LinearMap.mem_range_self _ z
      simpa using hz)
  have htop : (L : E →ₗ[ℝ] F).range = ⊤ := by
    have hle : Module.finrank ℝ (L : E →ₗ[ℝ] F).range ≤ 1 := by
      have hmono := Submodule.finrank_mono (le_top : (L : E →ₗ[ℝ] F).range ≤ ⊤)
      rwa [finrank_top, hF] at hmono
    have hne0 : Module.finrank ℝ (L : E →ₗ[ℝ] F).range ≠ 0 := by
      intro h
      exact hnebot (Submodule.finrank_eq_zero.mp h)
    have hfin : Module.finrank ℝ (L : E →ₗ[ℝ] F).range = 1 := by omega
    exact Submodule.eq_top_of_finrank_eq (by rw [hfin, hF])
  intro y
  have : y ∈ (L : E →ₗ[ℝ] F).range := by rw [htop]; trivial
  exact this

/-- The kernel of a nonzero functional on a `2`-dimensional space is `1`-dimensional. -/
lemma finrank_ker_eq_one_of_ne_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 2) (g : E →L[ℝ] ℝ) (hg : g ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (g : E →ₗ[ℝ] ℝ)) = 1 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker (g : E →ₗ[ℝ] ℝ)
  have hrange : Module.finrank ℝ (LinearMap.range (g : E →ₗ[ℝ] ℝ)) = 1 := by
    have hnebot : (LinearMap.range (g : E →ₗ[ℝ] ℝ)) ≠ ⊥ := by
      intro h
      exact hg (ContinuousLinearMap.ext fun z => by
        have hz : (g : E →ₗ[ℝ] ℝ) z ∈ (⊥ : Submodule ℝ ℝ) := by
          rw [← h]; exact LinearMap.mem_range_self _ z
        simpa using hz)
    have hle : Module.finrank ℝ (LinearMap.range (g : E →ₗ[ℝ] ℝ)) ≤ 1 := by
      have hmono := Submodule.finrank_mono (le_top : (LinearMap.range (g : E →ₗ[ℝ] ℝ)) ≤ ⊤)
      rwa [finrank_top, Module.finrank_self] at hmono
    have hne0 : Module.finrank ℝ (LinearMap.range (g : E →ₗ[ℝ] ℝ)) ≠ 0 := by
      intro h
      exact hnebot (Submodule.finrank_eq_zero.mp h)
    omega
  omega

/-! ### The component curves -/

/-- **Each connected component of a regular level set is the image of an immersive circle.**  The
map `Circle → M` produced by the classification of `1`-manifolds is not only smooth and injective
with the expected image, but also an immersion: its derivative at every point is nonzero. -/
lemma exists_componentCurve (f : M → ℝ) (t : ℝ) [LevelHyp f t]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (i : ConnectedComponents (LevelSet f t)) :
    ∃ Φ : Circle → M, ContMDiff (𝓡 1) (𝓡 2) ∞ Φ ∧ Function.Injective Φ ∧
      Set.range Φ = compSet f t i ∧
      (∀ z, mfderiv (𝓡 1) (𝓡 2) Φ z ≠ 0) := by
  classical
  haveI hLC : LocallyConnectedSpace (LevelSet f t) := levelSet_locallyConnectedSpace f t
  haveI hC : CompactSpace (LevelSet f t) := levelSet_compactSpace f t
  haveI hC' : CompactSpace (compOf f t i) :=
    isCompact_iff_compactSpace.mp isClosed_connectedComponent.isCompact
  haveI hSC : SecondCountableTopology (LevelSet f t) :=
    TopologicalSpace.secondCountableTopology_induced (LevelSet f t) M Subtype.val
  haveI hSC' : SecondCountableTopology (compOf f t i) :=
    TopologicalSpace.secondCountableTopology_induced (compOf f t i) (LevelSet f t) Subtype.val
  haveI hConn : ConnectedSpace (compOf f t i) :=
    isConnected_iff_connectedSpace.mp isConnected_connectedComponent
  obtain ⟨ψ⟩ := circleDiffeomorphCompactConnected (C := compOf f t i)
  have hψc : ContMDiff (𝓡 1) (𝓡 1) ∞ (⇑ψ) := ψ.contMDiff_toFun
  have hincl : ContMDiff (𝓡 1) (𝓡 2) ∞
      ((Subtype.val : LevelSet f t → M) ∘ (Subtype.val : compOf f t i → LevelSet f t)) :=
    (subtypeVal_contMDiff f t).comp contMDiff_subtype_val
  set Φ : Circle → M := ((Subtype.val : LevelSet f t → M) ∘
    (Subtype.val : compOf f t i → LevelSet f t)) ∘ (⇑ψ) with hΦ
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · rw [hΦ]; exact hincl.comp hψc
  · rw [hΦ]
    exact Subtype.val_injective.comp (Subtype.val_injective.comp ψ.toHomeomorph.injective)
  · show Set.range Φ = Subtype.val '' (↑(compOf f t i) : Set (LevelSet f t))
    have hsurjψ : Set.range (⇑ψ) = Set.univ := ψ.toEquiv.surjective.range_eq
    rw [hΦ, Set.range_comp, Set.image_comp, hsurjψ, Set.image_univ, Subtype.range_coe]
  · intro z
    have hψcAt : ContMDiffAt (𝓡 1) (𝓡 1) ∞ (⇑ψ) z := hψc.contMDiffAt
    have hincAt : ContMDiffAt (𝓡 1) (𝓡 2) ∞
        ((Subtype.val : LevelSet f t → M) ∘ (Subtype.val : compOf f t i → LevelSet f t))
        (ψ z) := hincl.contMDiffAt
    have hsub2At : ContMDiffAt (𝓡 1) (𝓡 2) ∞ (Subtype.val : LevelSet f t → M)
        (Subtype.val (ψ z)) := (subtypeVal_contMDiff f t).contMDiffAt
    have hsub1At : ContMDiffAt (𝓡 1) (𝓡 1) ∞
        (Subtype.val : compOf f t i → LevelSet f t) (ψ z) :=
      (contMDiff_subtype_val (I := 𝓡 1) (U := compOf f t i)).contMDiffAt
    have hψmd := hψcAt.mdifferentiableAt (by simp)
    have hinclmd := hincAt.mdifferentiableAt (by simp)
    have hsub2md := hsub2At.mdifferentiableAt (by simp)
    have hsub1md := hsub1At.mdifferentiableAt (by simp)
    have hid : ∀ v : TangentSpace (𝓡 1) (ψ z),
        (mfderiv (𝓡 1) (𝓡 1) (Subtype.val : compOf f t i → LevelSet f t) (ψ z)) v = v := by
      intro v
      rw [Work.OneDim.mfderiv_subtypeVal_eq_one (U := compOf f t i) (ψ z)]
      exact ContinuousLinearMap.id_apply v
    have hinc_app : ∀ v : TangentSpace (𝓡 1) (ψ z),
        (mfderiv (𝓡 1) (𝓡 2)
          ((Subtype.val : LevelSet f t → M) ∘ (Subtype.val : compOf f t i → LevelSet f t))
          (ψ z)) v
          = (mfderiv (𝓡 1) (𝓡 2) (Subtype.val : LevelSet f t → M) (↑(ψ z))) v := by
      intro v
      have h := mfderiv_comp_apply (f := (Subtype.val : compOf f t i → LevelSet f t))
        (g := (Subtype.val : LevelSet f t → M)) (x := ψ z) hsub2md hsub1md v
      rw [h, hid v]
    have hsurj : Surjective (mfderiv (𝓡 1) (𝓡 1) (⇑ψ) z) :=
      (ψ.mfderivToContinuousLinearEquiv (by simp) z).surjective
    have happ : ∀ v : TangentSpace (𝓡 1) z,
        (mfderiv (𝓡 1) (𝓡 2) Φ z) v
          = (mfderiv (𝓡 1) (𝓡 2) (Subtype.val : LevelSet f t → M) (↑(ψ z)))
              ((mfderiv (𝓡 1) (𝓡 1) (⇑ψ) z) v) := by
      intro v
      have h := mfderiv_comp_apply (f := (⇑ψ)) (g := ((Subtype.val : LevelSet f t → M) ∘
        (Subtype.val : compOf f t i → LevelSet f t))) (x := z) hinclmd hψmd v
      rw [← hΦ] at h
      rw [h, hinc_app ((mfderiv (𝓡 1) (𝓡 1) (⇑ψ) z) v)]
    intro hv
    obtain ⟨w₀, hw₀⟩ : ∃ w : TangentSpace (𝓡 1) (↑(ψ z)),
        mfderiv (𝓡 1) (𝓡 2) (Subtype.val : LevelSet f t → M) (↑(ψ z)) w ≠ 0 := by
      by_contra h
      refine (levelTangent_subtypeVal_ne_zero f t (↑(ψ z))) (ContinuousLinearMap.ext fun w => ?_)
      by_contra hw
      exact h ⟨w, hw⟩
    obtain ⟨v, rfl⟩ := hsurj w₀
    have h1 : (mfderiv (𝓡 1) (𝓡 2) Φ z) v = 0 := by rw [hv]; rfl
    rw [happ v] at h1
    exact hw₀ h1

/-! ### The level set as a union of components -/

lemma compSet_subset_levelSet (f : M → ℝ) (t : ℝ) [LevelHyp f t]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (i : ConnectedComponents (LevelSet f t)) : compSet f t i ⊆ {x : M | f x = t} := by
  rintro x ⟨w, -, rfl⟩
  exact w.2

lemma iUnion_compSet (f : M → ℝ) (t : ℝ) [LevelHyp f t]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M] :
    (⋃ i, compSet f t i) = {x : M | f x = t} := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact compSet_subset_levelSet f t i hi
  · intro hx
    refine Set.mem_iUnion.mpr
      ⟨ConnectedComponents.mk (⟨x, hx⟩ : LevelSet f t), ?_⟩
    refine ⟨(⟨x, hx⟩ : LevelSet f t), ?_, rfl⟩
    show (⟨x, hx⟩ : LevelSet f t) ∈
      connectedComponent (compRep f t (ConnectedComponents.mk (⟨x, hx⟩ : LevelSet f t)))
    have hcc : connectedComponent (compRep f t (ConnectedComponents.mk (⟨x, hx⟩ : LevelSet f t)))
        = connectedComponent (⟨x, hx⟩ : LevelSet f t) :=
      ConnectedComponents.coe_eq_coe.mp (coe_compRep f t _)
    rw [hcc]
    exact mem_connectedComponent

end


/-! ### The target: the level set is a finite disjoint union of periodic circles -/

theorem exists_levelComponentCurves {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ENat) : WithTop ENat) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    (f : M → ℝ) (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ENat) : WithTop ENat) f) (a : ℝ)
    (hreg : ∀ x : M, f x = a → ¬ Work.Drive.Morse.IsCritical f x)
    (hne : ∃ x : M, f x = a) :
    ∃ (n : ℕ) (γ : Fin n → ℝ → M),
      (∀ i, ContMDiff (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ENat) : WithTop ENat) (γ i)) ∧
      (∀ i x, γ i (x + 1) = γ i x) ∧
      (∀ i, Set.InjOn (γ i) (Set.Ico 0 1)) ∧
      (∀ i x, f (γ i x) = a) ∧
      (∀ i x, mfderiv (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (γ i) x ≠ 0) ∧
      (∀ i x v, mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
        (modelWithCornersSelf ℝ ℝ) f (γ i x) v = 0 →
        ∃ t : ℝ, mfderiv (modelWithCornersSelf ℝ ℝ)
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (γ i) x t = v) ∧
      (⋃ i, Set.range (γ i) = {x : M | f x = a}) ∧
      (∀ i j, i ≠ j → Disjoint (Set.range (γ i)) (Set.range (γ j))) ∧
      (∀ i, IsClosed (Set.range (γ i))) ∧
      (∀ (i : Fin n) (x y : ℝ), γ i x = γ i y → ∃ k : ℤ, x = y + k) := by
  classical
  haveI hLH : LevelHyp f a := ⟨hf, hreg⟩
  haveI hLC : LocallyConnectedSpace (LevelSet f a) := levelSet_locallyConnectedSpace f a
  haveI hC : CompactSpace (LevelSet f a) := levelSet_compactSpace f a
  haveI hFt : Fintype (ConnectedComponents (LevelSet f a)) := Fintype.ofFinite _
  obtain ⟨Φ, hΦspec⟩ : ∃ Φ : ConnectedComponents (LevelSet f a) → Circle → M,
      ∀ i, ContMDiff (𝓡 1) (𝓡 2) ∞ (Φ i) ∧ Function.Injective (Φ i) ∧
        Set.range (Φ i) = compSet f a i ∧ (∀ z, mfderiv (𝓡 1) (𝓡 2) (Φ i) z ≠ 0) :=
    ⟨fun i => Classical.choose (exists_componentCurve f a i),
      fun i => Classical.choose_spec (exists_componentCurve f a i)⟩
  let ee : ConnectedComponents (LevelSet f a) ≃
      Fin (Fintype.card (ConnectedComponents (LevelSet f a))) := Fintype.equivFin _
  let γ : Fin (Fintype.card (ConnectedComponents (LevelSet f a))) → ℝ → M :=
    fun i => Φ (ee.symm i) ∘ circExp
  have h1 : ∀ i, ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ (γ i) := fun i =>
    (hΦspec (ee.symm i)).1.comp circExp_contMDiff
  have h2 : ∀ i x, γ i (x + 1) = γ i x := by
    intro i x
    exact congrArg (Φ (ee.symm i)) (circExp_add_one x)
  have h3 : ∀ i, Set.InjOn (γ i) (Set.Ico 0 1) := fun i => by
    change Set.InjOn (Φ (ee.symm i) ∘ circExp) (Set.Ico 0 1)
    exact ((hΦspec (ee.symm i)).2.1.injOn).comp circExp_injOn_Ico
      (fun x _ => Set.mem_univ (circExp x))
  have h4 : ∀ i x, f (γ i x) = a := by
    intro i x
    refine compSet_subset_levelSet f a (ee.symm i) ?_
    rw [← (hΦspec (ee.symm i)).2.2.1]
    exact Set.mem_range_self (circExp x)
  have h5 : ∀ i x, mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (γ i) x ≠ 0 := by
    intro i x
    have hΦcAt : ContMDiffAt (𝓡 1) (𝓡 2) ∞ (Φ (ee.symm i)) (circExp x) :=
      (hΦspec (ee.symm i)).1.contMDiffAt
    have hcircAt : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 1) ∞ circExp x := circExp_contMDiff.contMDiffAt
    have hΦmd := hΦcAt.mdifferentiableAt (by simp)
    have hcircmd := hcircAt.mdifferentiableAt (by simp)
    have hsurj : Surjective (mfderiv 𝓘(ℝ, ℝ) (𝓡 1) circExp x) :=
      surjective_of_ne_zero_of_finrank_eq_one (E := ℝ) (F := E1)
        (by rw [finrank_euclideanSpace]; simp) _ (circExp_mfderiv_ne_zero x)
    have happ : ∀ v : TangentSpace 𝓘(ℝ, ℝ) x,
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (γ i) x) v
          = (mfderiv (𝓡 1) (𝓡 2) (Φ (ee.symm i)) (circExp x))
              ((mfderiv 𝓘(ℝ, ℝ) (𝓡 1) circExp x) v) := by
      intro v
      exact mfderiv_comp_apply (f := circExp) (g := (Φ (ee.symm i))) (x := x) hΦmd hcircmd v
    intro hv
    obtain ⟨w₀, hw₀⟩ : ∃ w, mfderiv (𝓡 1) (𝓡 2) (Φ (ee.symm i)) (circExp x) w ≠ 0 := by
      by_contra h
      refine (hΦspec (ee.symm i)).2.2.2 (circExp x) (ContinuousLinearMap.ext fun w => ?_)
      by_contra hw
      exact h ⟨w, hw⟩
    obtain ⟨v, rfl⟩ := hsurj w₀
    have h1 : (mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (γ i) x) v = 0 := by rw [hv]; rfl
    rw [happ v] at h1
    exact hw₀ h1
  have h6 : ∀ i x v, mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (γ i x) v = 0 →
      ∃ t : ℝ, mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (γ i) x t = v := by
    intro i x v hv
    set g : E2 →L[ℝ] ℝ := mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (γ i x) with hg
    set L : ℝ →L[ℝ] E2 := mfderiv 𝓘(ℝ, ℝ) (𝓡 2) (γ i) x with hL
    have hγAt : ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 2) ∞ (γ i) x := (h1 i).contMDiffAt
    have hfAt : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ f (γ i x) := hLH.contMDiff.contMDiffAt
    have hγmd := hγAt.mdifferentiableAt (by simp)
    have hfmd := hfAt.mdifferentiableAt (by simp)
    have hconst : (f ∘ (γ i)) = fun _ => a := funext fun y => h4 i y
    have hcomp := mfderiv_comp x hfmd hγmd
    rw [hconst, mfderiv_const] at hcomp
    have hgle : g.comp L = 0 := by
      rw [hg, hL]
      exact hcomp.symm
    have hle : L.range ≤ g.ker := by
      intro w hw
      obtain ⟨u, rfl⟩ := LinearMap.mem_range.mp hw
      rw [LinearMap.mem_ker]
      have h1' := congrArg (fun M : ℝ →L[ℝ] ℝ => M u) hgle
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply] at h1'
      exact h1'
    have hgv : v ∈ g.ker := by
      rw [LinearMap.mem_ker, hg]
      exact hv
    have hgne : g ≠ 0 := by
      rw [hg]
      exact hLH.regular (γ i x) (h4 i x)
    have hker : Module.finrank ℝ g.ker = 1 :=
      finrank_ker_eq_one_of_ne_zero (E := E2) (by rw [finrank_euclideanSpace]; simp) g hgne
    have hLne : L ≠ 0 := by rw [hL]; exact h5 i x
    have hLrange : L.range ≠ ⊥ := by
      intro h
      exact hLne (ContinuousLinearMap.ext fun u => by
        have hu : L u ∈ (⊥ : Submodule ℝ E2) := by
          rw [← h]; exact LinearMap.mem_range_self _ u
        simpa using hu)
    have hfinL : Module.finrank ℝ L.range = 1 := by
      have hle1 : Module.finrank ℝ L.range ≤ 1 := by
        have hmono := Submodule.finrank_mono hle
        omega
      have hne0 : Module.finrank ℝ L.range ≠ 0 := by
        intro h
        exact hLrange (Submodule.finrank_eq_zero.mp h)
      omega
    have heq : L.range = g.ker := Submodule.eq_of_le_of_finrank_eq hle (by rw [hfinL, hker])
    have hv' : v ∈ L.range := by rw [heq]; exact hgv
    obtain ⟨t, ht⟩ := LinearMap.mem_range.mp hv'
    exact ⟨t, ht⟩
  have h7 : (⋃ i, Set.range (γ i)) = {x : M | f x = a} := by
    rw [← iUnion_compSet f a]
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      refine Set.mem_iUnion.mpr ⟨ee.symm i, ?_⟩
      have h2 : x ∈ Set.range (Φ (ee.symm i) ∘ circExp) := hi
      rw [Set.range_comp, circExp_surjective.range_eq, Set.image_univ] at h2
      rwa [← (hΦspec (ee.symm i)).2.2.1]
    · intro hx
      obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hx
      refine Set.mem_iUnion.mpr ⟨ee j, ?_⟩
      have h2 : x ∈ Set.range (Φ j) := by rwa [(hΦspec j).2.2.1]
      have h3 : x ∈ Set.range (Φ (ee.symm (ee j)) ∘ circExp) := by
        rw [ee.symm_apply_apply, Set.range_comp, circExp_surjective.range_eq, Set.image_univ]
        exact h2
      exact h3
  have h8 : ∀ i j : Fin (Fintype.card (ConnectedComponents (LevelSet f a))), i ≠ j →
      Disjoint (Set.range (γ i)) (Set.range (γ j)) := by
    intro i j hij
    have hij' : ee.symm i ≠ ee.symm j := fun h => hij (by
      rw [← ee.apply_symm_apply i, ← ee.apply_symm_apply j, h])
    rw [Set.range_comp, Set.range_comp, circExp_surjective.range_eq, Set.image_univ,
      Set.image_univ, (hΦspec (ee.symm i)).2.2.1, (hΦspec (ee.symm j)).2.2.1]
    exact disjoint_compSet f a _ _ hij'
  have h9 : ∀ i : Fin (Fintype.card (ConnectedComponents (LevelSet f a))),
      IsClosed (Set.range (γ i)) := by
    intro i
    have hcont : Continuous (Φ (ee.symm i)) := (hΦspec (ee.symm i)).1.continuous
    have hkomp : IsCompact (Set.range (Φ (ee.symm i))) := isCompact_range hcont
    rw [Set.range_comp, circExp_surjective.range_eq, Set.image_univ]
    exact hkomp.isClosed
  have h10 : ∀ (i : Fin (Fintype.card (ConnectedComponents (LevelSet f a)))) (x y : ℝ),
      γ i x = γ i y → ∃ k : ℤ, x = y + k := by
    intro i x y hxy
    have h1' : Φ (ee.symm i) (circExp x) = Φ (ee.symm i) (circExp y) := hxy
    exact circExp_eq_iff.mp ((hΦspec (ee.symm i)).2.1 h1')
  exact ⟨Fintype.card (ConnectedComponents (LevelSet f a)), γ, h1, h2, h3, h4, h5, h6, h7,
    h8, h9, h10⟩

end Work.Drive.N2
