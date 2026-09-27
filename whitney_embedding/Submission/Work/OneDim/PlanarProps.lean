import Mathlib
import Submission.Work.OneDim.PlanarModel

/-!
# The planar model maps are smooth proper embeddings

This file provides the analytic properties of the planar model maps `planarLine`, `planarCircle`
and `planarPlace` of `Submission.Work.OneDim.PlanarModel`: smoothness, injectivity, injectivity of
the derivative and properness.
-/

open scoped Manifold ContDiff
open Topology Set Function

namespace Work.OneDim

noncomputable section

theorem planarLine_eq (c : ℝ) :
    planarLine c = fun t : ℝ => t • lineDir + heightVec c := rfl

theorem planarLine_contMDiff (c : ℝ) :
    ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (planarLine c) := by
  rw [planarLine_eq c]
  rw [contMDiff_iff_contDiff]
  exact (contDiff_smul_const lineDir).add contDiff_const

theorem planarLine_continuous (c : ℝ) : Continuous (planarLine c) :=
  (planarLine_contMDiff c).continuous

theorem planarLine_injective (c : ℝ) : Function.Injective (planarLine c) := by
  intro a b h
  have h' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h
  simpa using h'

theorem fderiv_planarLine_injective (c : ℝ) (t : ℝ) :
    Function.Injective (fderiv ℝ (planarLine c) t) := by
  have hfun : planarLine c = fun y : ℝ =>
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) lineDir) y + heightVec c := by
    funext s
    rw [ContinuousLinearMap.smulRight_apply, one_apply_eq_self]
    exact congrFun (planarLine_eq c) s
  rw [hfun]
  show Function.Injective (fderiv ℝ
    (fun y : ℝ => (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) lineDir) y + heightVec c) t)
  rw [fderiv_add_const]
  show Function.Injective (fderiv ℝ
    (⇑(ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) lineDir)) t)
  rw [ContinuousLinearMap.fderiv]
  intro a b hab
  have h : a • lineDir = b • lineDir := by
    simpa [ContinuousLinearMap.smulRight_apply, one_apply_eq_self] using hab
  have h2 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w.ofLp 0) h
  simpa [PiLp.smul_apply, lineDir] using h2

theorem planarLine_mfderiv_injective (c : ℝ) (t : ℝ) :
    Function.Injective (mfderiv (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (planarLine c) t) := by
  rw [mfderiv_eq_fderiv]
  exact fderiv_planarLine_injective c t

theorem range_planarLine (c : ℝ) :
    Set.range (planarLine c) = {p : EuclideanSpace ℝ (Fin 2) | p 1 = c} := by
  ext p
  constructor
  · rintro ⟨t, rfl⟩
    simp
  · intro hp
    refine ⟨p 0, ?_⟩
    ext i
    fin_cases i
    · simp [planarLine]
    · simpa [planarLine] using hp.symm

theorem planarLine_isEmbedding (c : ℝ) : IsEmbedding (planarLine c) := by
  refine IsEmbedding.of_comp (f := planarLine c)
    (g := fun p : EuclideanSpace ℝ (Fin 2) => p 0) (planarLine_continuous c) (by fun_prop) ?_
  have h : (fun p : EuclideanSpace ℝ (Fin 2) => p 0) ∘ planarLine c = id := by
    funext t
    simp
  rw [h]
  exact IsEmbedding.id

theorem planarLine_isClosedEmbedding (c : ℝ) : IsClosedEmbedding (planarLine c) := by
  refine ⟨planarLine_isEmbedding c, ?_⟩
  rw [range_planarLine c]
  exact isClosed_eq (by fun_prop) continuous_const

theorem planarLine_isProperMap (c : ℝ) : IsProperMap (planarLine c) :=
  (planarLine_isClosedEmbedding c).isProperMap

/-- The circle of radius `1/4` is an affine image of the standard inclusion `Circle → ℂ → ℝ²`. -/
theorem planarCircle_eq (c : ℝ) :
    planarCircle c = fun z : Circle => (1 / 4 : ℝ) • (Complex.orthonormalBasisOneI.repr (z : ℂ))
      + (c : ℝ) • (Complex.orthonormalBasisOneI.repr 1) := by
  funext z
  ext i
  fin_cases i <;> simp [planarCircle, Complex.orthonormalBasisOneI_repr_apply, add_comm]

theorem planarCircle_contMDiff (c : ℝ) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (planarCircle c) := by
  haveI : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  rw [planarCircle_eq c]
  let r : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr
  have hcoe : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) 𝓘(ℝ, ℂ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Circle => (z : ℂ)) :=
    contMDiff_coe_sphere (E := ℂ) (n := 1)
  have hrepr : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
      ((⊤ : ℕ∞) : WithTop ℕ∞) r := ContinuousLinearMap.contMDiff r
  have hconst : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) 𝓘(ℝ, ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun _ : Circle => (1 / 4 : ℝ)) := contMDiff_const
  exact (hconst.smul (hrepr.comp hcoe)).add contMDiff_const

theorem planarCircle_continuous (c : ℝ) : Continuous (planarCircle c) :=
  (planarCircle_contMDiff c).continuous

theorem planarCircle_injective (c : ℝ) : Function.Injective (planarCircle c) := by
  intro z y h
  have h1 : ((z : ℂ)).re = ((y : ℂ)).re := by
    have h' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 0) h
    simpa using h'
  have h2 : ((z : ℂ)).im = ((y : ℂ)).im := by
    have h' := congrArg (fun p : EuclideanSpace ℝ (Fin 2) => p 1) h
    simpa using h'
  exact Subtype.ext (Complex.ext h1 h2)

theorem planarCircle_mfderiv_injective (c : ℝ) (z : Circle) :
    Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (planarCircle c) z) := by
  haveI : Fact (Module.finrank ℝ ℂ = 1 + 1) := finrank_real_complex_fact'
  let r : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 2) := Complex.orthonormalBasisOneI.repr
  have hcoe : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) 𝓘(ℝ, ℂ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : Circle => (z : ℂ)) :=
    contMDiff_coe_sphere (E := ℂ) (n := 1)
  set F : Circle → EuclideanSpace ℝ (Fin 2) := fun z => r (z : ℂ) with hF
  have hFsm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ((⊤ : ℕ∞) : WithTop ℕ∞) F :=
    (ContinuousLinearMap.contMDiff r).comp hcoe
  set A : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) :=
    fun p => (1 / 4 : ℝ) • p + (c : ℝ) • r 1 with hA
  have hsplit : A = (fun p : EuclideanSpace ℝ (Fin 2) => (1 / 4 : ℝ) • p)
      + (fun _ : EuclideanSpace ℝ (Fin 2) => (c : ℝ) • r 1) := by
    funext p
    rw [hA, Pi.add_apply]
  have hAsm : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
      ((⊤ : ℕ∞) : WithTop ℕ∞) A := by
    rw [hsplit, contMDiff_iff_contDiff]
    exact (ContDiff.const_smul (1 / 4 : ℝ) contDiff_id).add contDiff_const
  have hdecomp : planarCircle c = A ∘ F := by
    funext w
    rw [planarCircle_eq c, hA, hF]
    rfl
  have hAderiv : fderiv ℝ (fun y : EuclideanSpace ℝ (Fin 2) => (1 / 4 : ℝ) • y) (F z)
      = (1 / 4 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2)) := by
    have hfl : (fun y : EuclideanSpace ℝ (Fin 2) => (1 / 4 : ℝ) • y)
        = (1 / 4 : ℝ) • (id : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2)) := by
      funext y
      rfl
    rw [hfl, fderiv_const_smul differentiableAt_id (1 / 4 : ℝ), fderiv_id]
  have hAinj : Function.Injective (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
      𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) A (F z)) := by
    rw [mfderiv_eq_fderiv, hsplit]
    show Function.Injective (fderiv ℝ
      (fun y : EuclideanSpace ℝ (Fin 2) => (1 / 4 : ℝ) • y + (c : ℝ) • r 1) (F z))
    rw [fderiv_add_const]
    show Function.Injective (fderiv ℝ
      (fun y : EuclideanSpace ℝ (Fin 2) => (1 / 4 : ℝ) • y) (F z))
    rw [hAderiv]
    intro a b hab
    have hab' : (1 / 4 : ℝ) • a = (1 / 4 : ℝ) • b := by
      simpa using hab
    have e1 : (4 : ℝ) • ((1 / 4 : ℝ) • a) = a := by
      rw [smul_smul, show (4 : ℝ) * (1 / 4) = 1 by norm_num, one_smul]
    have e2 : (4 : ℝ) • ((1 / 4 : ℝ) • b) = b := by
      rw [smul_smul, show (4 : ℝ) * (1 / 4) = 1 by norm_num, one_smul]
    have h4 : (4 : ℝ) • ((1 / 4 : ℝ) • a) = (4 : ℝ) • ((1 / 4 : ℝ) • b) := congrArg _ hab'
    rw [e1, e2] at h4
    exact h4
  have hFinj : Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) F z) := by
    have hchain := mfderiv_comp (f := fun z : Circle => (z : ℂ))
      (g := fun w : ℂ => r w) z
      (ContinuousLinearMap.mdifferentiableAt r)
      (hcoe.mdifferentiableAt (by simp))
    have hrd : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
        (fun w : ℂ => r w) (z : ℂ) = r := by
      rw [mfderiv_eq_fderiv]
      exact ContinuousLinearMap.fderiv r (x := (z : ℂ))
    rw [hF]
    rw [show (fun z : Circle => r (z : ℂ))
      = (fun w : ℂ => r w) ∘ (fun z : Circle => (z : ℂ)) from rfl]
    rw [hchain, hrd]
    intro v w hvw
    exact (injective_mvfderiv_subtypeVal_sphere (E := ℂ) (n := 1) z)
      (Complex.orthonormalBasisOneI.repr.injective hvw)
  have hA_diff : MDifferentiableAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 2))
      𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) A (F z) := hAsm.mdifferentiableAt (by simp)
  have hF_diff : MDifferentiableAt (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) F z := hFsm.mdifferentiableAt (by simp)
  rw [hdecomp, mfderiv_comp z hA_diff hF_diff]
  intro v w hvw
  exact hFinj (hAinj hvw)

theorem planarCircle_isClosedEmbedding (c : ℝ) : IsClosedEmbedding (planarCircle c) :=
  (planarCircle_continuous c).isClosedEmbedding (planarCircle_injective c)

theorem planarCircle_isProperMap (c : ℝ) : IsProperMap (planarCircle c) :=
  (planarCircle_isClosedEmbedding c).isProperMap

theorem planarPlace_contMDiff {C : Type*} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) C]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ((⊤ : ℕ∞) : WithTop ℕ∞) C]
    (j : ℕ) (d : PlanarPlaceData C) :
    ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (planarPlace j d) := by
  rcases d with φ | ψ
  · exact (planarLine_contMDiff (j + 1 / 2 : ℝ)).comp φ.symm.contMDiff_toFun
  · exact (planarCircle_contMDiff (j : ℝ)).comp ψ.symm.contMDiff_toFun

theorem planarPlace_injective {C : Type*} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) C]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ((⊤ : ℕ∞) : WithTop ℕ∞) C]
    (j : ℕ) (d : PlanarPlaceData C) : Function.Injective (planarPlace j d) := by
  rcases d with φ | ψ
  · exact (planarLine_injective (j + 1 / 2 : ℝ)).comp φ.symm.injective
  · exact (planarCircle_injective (j : ℝ)).comp ψ.symm.injective

theorem planarPlace_mfderiv_injective {C : Type*} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) C]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ((⊤ : ℕ∞) : WithTop ℕ∞) C]
    (j : ℕ) (d : PlanarPlaceData C) (y : C) :
    Function.Injective (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (planarPlace j d) y) := by
  rcases d with φ | ψ
  · have hchain := mfderiv_comp (f := (⇑φ.symm : C → ℝ)) (g := planarLine (j + 1 / 2 : ℝ)) y
      ((planarLine_contMDiff (j + 1 / 2 : ℝ)).mdifferentiableAt (by simp))
      (φ.symm.contMDiff_toFun.mdifferentiableAt (by simp))
    rw [show (planarPlace j (Sum.inl φ) : C → EuclideanSpace ℝ (Fin 2))
        = planarLine (j + 1 / 2 : ℝ) ∘ (⇑φ.symm : C → ℝ) from rfl, hchain]
    exact (planarLine_mfderiv_injective _ _).comp
      (φ.symm.mfderivToContinuousLinearEquiv (by simp) y).injective
  · have hchain := mfderiv_comp (f := (⇑ψ.symm : C → Circle)) (g := planarCircle (j : ℝ)) y
      ((planarCircle_contMDiff (j : ℝ)).mdifferentiableAt (by simp))
      (ψ.symm.contMDiff_toFun.mdifferentiableAt (by simp))
    rw [show (planarPlace j (Sum.inr ψ) : C → EuclideanSpace ℝ (Fin 2))
        = planarCircle (j : ℝ) ∘ (⇑ψ.symm : C → Circle) from rfl, hchain]
    exact (planarCircle_mfderiv_injective _ _).comp
      (ψ.symm.mfderivToContinuousLinearEquiv (by simp) y).injective

theorem planarPlace_isProperMap {C : Type*} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) C]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1))) ((⊤ : ℕ∞) : WithTop ℕ∞) C]
    (j : ℕ) (d : PlanarPlaceData C) : IsProperMap (planarPlace j d) := by
  rcases d with φ | ψ
  · exact (planarLine_isProperMap (j + 1 / 2 : ℝ)).comp
      (by simpa [Diffeomorph.coe_toHomeomorph] using φ.symm.toHomeomorph.isProperMap)
  · exact (planarCircle_isProperMap (j : ℝ)).comp
      (by simpa [Diffeomorph.coe_toHomeomorph] using ψ.symm.toHomeomorph.isProperMap)

/-- If two placed points are equal, their slot indices are equal: the second coordinate equals
`j + 1/2` on a line slot and is bounded by `1/4` in absolute value on a circle slot, while
distinct circle slots are centred more than `1/2` apart. -/
theorem planarPlace_slot_eq {C C' : Type*} [TopologicalSpace C]
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) C] [TopologicalSpace C']
    [ChartedSpace (EuclideanSpace ℝ (Fin 1)) C']
    (j j' : ℕ) (d : PlanarPlaceData C) (d' : PlanarPlaceData C') (z : C) (z' : C')
    (h : planarPlace j d z = planarPlace j' d' z') : j = j' := by
  rcases d with φ | ψ <;> rcases d' with φ' | ψ'
  · have h1 : (planarPlace j (Sum.inl φ) z).ofLp 1 = (j : ℝ) + 1 / 2 := by
      simp [planarPlace]
    have h2 : (planarPlace j' (Sum.inl φ') z').ofLp 1 = (j' : ℝ) + 1 / 2 := by
      simp [planarPlace]
    have h3 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w.ofLp 1) h
    rw [h1, h2] at h3
    have h4 : (j : ℝ) = (j' : ℝ) := by linarith
    exact_mod_cast h4
  · have h1 : (planarPlace j (Sum.inl φ) z).ofLp 1 = (j : ℝ) + 1 / 2 := by
      simp [planarPlace]
    have h2 : |(planarPlace j' (Sum.inr ψ') z').ofLp 1| ≤ 1 / 4 := by
      simpa [planarPlace] using planarCircle_abs_apply_one (j' : ℝ) (ψ'.symm z')
    have h3 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w.ofLp 1) h
    rw [h1] at h3
    have h4 : |(j : ℝ) + 1 / 2| ≤ 1 / 4 := by
      rw [h3]
      exact h2
    have h5 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith [le_abs_self ((j : ℝ) + 1 / 2)]
  · have h1 : |(planarPlace j (Sum.inr ψ) z).ofLp 1| ≤ 1 / 4 := by
      simpa [planarPlace] using planarCircle_abs_apply_one (j : ℝ) (ψ.symm z)
    have h2 : (planarPlace j' (Sum.inl φ') z').ofLp 1 = (j' : ℝ) + 1 / 2 := by
      simp [planarPlace]
    have h3 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w.ofLp 1) h
    rw [h2] at h3
    have h4 : |(j' : ℝ) + 1 / 2| ≤ 1 / 4 := by
      rw [← h3]
      exact h1
    have h5 : (0 : ℝ) ≤ (j' : ℝ) := Nat.cast_nonneg j'
    linarith [le_abs_self ((j' : ℝ) + 1 / 2)]
  · have hb1 : |(planarPlace j (Sum.inr ψ) z).ofLp 0 - (j : ℝ)| ≤ 1 / 4 := by
      have hh := planarCircle_apply_zero_mem (j : ℝ) (ψ.symm z)
      simp only [Set.mem_Icc] at hh
      have hh' : |(planarCircle (j : ℝ) (ψ.symm z)).ofLp 0 - (j : ℝ)| ≤ 1 / 4 :=
        abs_le.mpr ⟨by linarith [hh.1], by linarith [hh.2]⟩
      simpa only [planarPlace, Sum.elim_inr] using hh'
    have hb2 : |(planarPlace j' (Sum.inr ψ') z').ofLp 0 - (j' : ℝ)| ≤ 1 / 4 := by
      have hh := planarCircle_apply_zero_mem (j' : ℝ) (ψ'.symm z')
      simp only [Set.mem_Icc] at hh
      have hh' : |(planarCircle (j' : ℝ) (ψ'.symm z')).ofLp 0 - (j' : ℝ)| ≤ 1 / 4 :=
        abs_le.mpr ⟨by linarith [hh.1], by linarith [hh.2]⟩
      simpa only [planarPlace, Sum.elim_inr] using hh'
    have h3 := congrArg (fun w : EuclideanSpace ℝ (Fin 2) => w.ofLp 0) h
    have h4 : |(j : ℝ) - (j' : ℝ)| ≤ 1 / 2 := by
      have h4a : (j : ℝ) - (j' : ℝ)
          = -((planarPlace j (Sum.inr ψ) z).ofLp 0 - (j : ℝ))
            + ((planarPlace j' (Sum.inr ψ') z').ofLp 0 - (j' : ℝ)) := by
        rw [← h3]; ring
      rw [h4a, abs_le]
      constructor <;>
        linarith [(abs_le.mp hb1).1, (abs_le.mp hb1).2, (abs_le.mp hb2).1, (abs_le.mp hb2).2]
    by_contra hne
    have hlt : ((j : ℝ) + 1 ≤ (j' : ℝ)) ∨ ((j' : ℝ) + 1 ≤ (j : ℝ)) := by
      rcases lt_or_gt_of_ne (fun hh : (j : ℝ) = (j' : ℝ) => hne (Nat.cast_injective hh)) with hc | hc
      · left
        have : j < j' := (Nat.cast_lt (α := ℝ)).mp hc
        exact_mod_cast Nat.succ_le_of_lt this
      · right
        have : j' < j := (Nat.cast_lt (α := ℝ)).mp hc
        exact_mod_cast Nat.succ_le_of_lt this
    rcases hlt with hlt | hlt
    · have : (1 : ℝ) ≤ |(j : ℝ) - (j' : ℝ)| := by
        rw [abs_of_nonpos (by linarith)]
        linarith
      linarith
    · have : (1 : ℝ) ≤ |(j : ℝ) - (j' : ℝ)| := by
        rw [abs_of_nonneg (by linarith)]
        linarith
      linarith

end

end Work.OneDim
