import Mathlib
import Submission.Work.ThomBordism.KeyLocal.tubeSets
import Submission.Work.ThomBordism.KeyLocal.pairSignGauss
import Submission.Work.ThomBordism.KeyLocal.tcmRelCup_stdModelGen

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

open scoped BigOperators

namespace Work.ThomBordism.KeyLocal

open Work.ThomBordism.PontryaginThom
open Work.ThomBordism.OrthFrame

noncomputable section

variable {k : ℕ}

/-! ## The frame combination map

`combFrame v a = ∑ j, a j • v j` is the combination map of the frame `v`, written on plain
coordinate vectors; it is `Work.ThomBordism.Grassmann.coeffMap` composed with the canonical
identification `ℝ^{n} ≃ (Fin n → ℝ)`. -/

/-- The coefficient combination `a ↦ ∑ j, a j • v j` of a frame. -/
def combFrame {ι : Type*} [Fintype ι] (v : ι → EuclideanSpace ℝ (Fin (8 + k))) :
    (ι → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin (8 + k)) :=
  Fintype.linearCombination ℝ v

theorem combFrame_apply {ι : Type*} [Fintype ι] (v : ι → EuclideanSpace ℝ (Fin (8 + k)))
    (a : ι → ℝ) : combFrame v a = ∑ j, a j • v j :=
  Fintype.linearCombination_apply ℝ v a

theorem combFrame_single {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → EuclideanSpace ℝ (Fin (8 + k)))
    (j : ι) : combFrame v (Pi.single j 1) = v j := by
  rw [combFrame_apply, Finset.sum_eq_single j]
  · simp
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_smul]
  · intro h; exact absurd (Finset.mem_univ j) h

theorem combFrame_zero {ι : Type*} [Fintype ι] (v : ι → EuclideanSpace ℝ (Fin (8 + k))) :
    combFrame v 0 = 0 := by
  rw [combFrame_apply]; simp

theorem eucToFun_injective (n : ℕ) : Function.Injective (eucToFun n) := by
  intro x y h
  have := congrArg (funToEuc n) h
  rwa [funToEuc_eucToFun, funToEuc_eucToFun] at this

/-- **The coordinate map of a frame is its combination map read through the canonical
identification `ℝⁿ ≃ (Fin n → ℝ)`.** -/
theorem coeffMap_apply_eucToFun (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (a : Fin 8 → ℝ) :
    Work.ThomBordism.Grassmann.coeffMap T a = eucToFun (8 + k) (combFrame T a) := by
  funext x
  rw [Work.ThomBordism.Grassmann.coeffMap_apply, combFrame_apply, eucToFun_apply,
    WithLp.ofLp_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  simp

/-- **The combination map of a linearly independent frame is injective.** -/
theorem combFrame_injective (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (hT : LinearIndependent ℝ T) : Function.Injective (combFrame T) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro a ha
  have h0 : ∑ j, a j • T j = 0 := by simpa [combFrame_apply] using ha
  funext j
  exact (Fintype.linearIndependent_iff.mp hT) a h0 j

/-! ## The two pinning equations

From the two identities of the tube chart (`coeffMap T (eucToFun 8 (L1 u)) + eucToFun (8+k) (L2 u)
= eucToFun (8+k) u` and `L2 u ⊥ T`) we read off the two linear maps: `L2` is the orthogonal
projection onto the plane spanned by `G`, and `L1` the coordinate map of `T` in the dual basis. -/

/-- **The differentiated identity of the tube chart, in `Euc`-form.** -/
theorem combFrame_T_add_L2 {k : ℕ} (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (L1 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin 8))
    (L2 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (h1 : ∀ u, Work.ThomBordism.Grassmann.coeffMap T (eucToFun 8 (L1 u))
      + eucToFun (8 + k) (L2 u) = eucToFun (8 + k) u)
    (u : EuclideanSpace ℝ (Fin (8 + k))) :
    combFrame T (eucToFun 8 (L1 u)) + L2 u = u := by
  have h := h1 u
  rw [coeffMap_apply_eucToFun T (eucToFun 8 (L1 u))] at h
  apply eucToFun_injective
  rw [map_add]
  exact h

/-- **The normality of `vec` forces `L2` to vanish on the tangent frame.** -/
theorem L2_apply_T {k : ℕ} (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (L1 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin 8))
    (L2 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (h1 : ∀ u, Work.ThomBordism.Grassmann.coeffMap T (eucToFun 8 (L1 u))
      + eucToFun (8 + k) (L2 u) = eucToFun (8 + k) u)
    (h2 : ∀ u a, inner ℝ (T a) (L2 u) = 0) (a : Fin 8) : L2 (T a) = 0 := by
  have h := combFrame_T_add_L2 T L1 L2 h1 (T a)
  have hsub : L2 (T a) = T a - combFrame T (eucToFun 8 (L1 (T a))) := eq_sub_of_add_eq' h
  have hTa : inner ℝ (L2 (T a)) (T a) = 0 := by
    rw [real_inner_comm]; exact h2 (T a) a
  have hTc : inner ℝ (L2 (T a)) (combFrame T (eucToFun 8 (L1 (T a)))) = 0 := by
    have key : ∀ j : Fin 8, inner ℝ (L2 (T a)) (T j) = 0 := fun j => by
      rw [real_inner_comm]; exact h2 (T a) j
    rw [combFrame_apply, inner_sum]
    refine Finset.sum_eq_zero fun j _ => by rw [inner_smul_right, key j, mul_zero]
  have hself : inner ℝ (L2 (T a)) (L2 (T a)) = 0 := by
    nth_rewrite 2 [hsub]
    rw [inner_sub_right, hTa, hTc, sub_zero]
  exact inner_self_eq_zero.mp hself

/-- **`L1` on the tangent frame: the dual coordinates.** -/
theorem L1_apply_T {k : ℕ} (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (L1 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin 8))
    (L2 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (hT : LinearIndependent ℝ T)
    (h1 : ∀ u, Work.ThomBordism.Grassmann.coeffMap T (eucToFun 8 (L1 u))
      + eucToFun (8 + k) (L2 u) = eucToFun (8 + k) u)
    (h2 : ∀ u a, inner ℝ (T a) (L2 u) = 0) (a : Fin 8) :
    L1 (T a) = EuclideanSpace.single a 1 := by
  have hcomb : combFrame T (eucToFun 8 (L1 (T a))) = T a := by
    have h := combFrame_T_add_L2 T L1 L2 h1 (T a)
    rw [L2_apply_T T L1 L2 h1 h2 a, add_zero] at h
    exact h
  have hs1 : (∑ j, (eucToFun 8 (L1 (T a))) j • T j) = T a := by
    rw [← combFrame_apply]; exact hcomb
  have hs2 : (∑ j, (Pi.single a (1 : ℝ) : Fin 8 → ℝ) j • T j) = T a := by
    rw [Finset.sum_eq_single a]
    · rw [Pi.single_eq_same, one_smul]
    · intro b _ hb; rw [Pi.single_eq_of_ne hb, zero_smul]
    · intro h; exact absurd (Finset.mem_univ a) h
  have hsum : ∑ j, ((eucToFun 8 (L1 (T a))) j - (Pi.single a (1 : ℝ) : Fin 8 → ℝ) j) • T j
      = 0 := by
    rw [Finset.sum_congr rfl (fun j _ => sub_smul ((eucToFun 8 (L1 (T a))) j)
      ((Pi.single a (1 : ℝ) : Fin 8 → ℝ) j) (T j)), Finset.sum_sub_distrib, hs1, hs2, sub_self]
  have hv : eucToFun 8 (L1 (T a)) = Pi.single a 1 := by
    funext b
    have hb := (Fintype.linearIndependent_iff.mp hT)
      (fun j => (eucToFun 8 (L1 (T a))) j - (Pi.single a (1 : ℝ) : Fin 8 → ℝ) j) hsum b
    exact sub_eq_zero.mp hb
  apply eucToFun_injective
  rw [hv]
  rfl

/-- **`L1` vanishes on the normal frame, and `L2` is the identity there.**  Both come from the
orthogonality relation: a combination of the tangent frame orthogonal to the whole tangent frame is
zero. -/
theorem L1_apply_G {k : ℕ} (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (G : Fin k → EuclideanSpace ℝ (Fin (8 + k)))
    (L1 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin 8))
    (L2 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (hT : LinearIndependent ℝ T)
    (h1 : ∀ u, Work.ThomBordism.Grassmann.coeffMap T (eucToFun 8 (L1 u))
      + eucToFun (8 + k) (L2 u) = eucToFun (8 + k) u)
    (h2 : ∀ u a, inner ℝ (T a) (L2 u) = 0)
    (horth : ∀ a b, inner ℝ (T a) (G b) = 0) (b : Fin k) : L1 (G b) = 0 := by
  have hEq := combFrame_T_add_L2 T L1 L2 h1 (G b)
  have horthL2 : ∀ c : Fin 8, inner ℝ (T c) (combFrame T (eucToFun 8 (L1 (G b)))) = 0 := by
    intro c
    have h := congrArg (fun z => inner ℝ (T c) z) hEq
    rw [inner_add_right, h2 (G b) c, horth c b, add_zero] at h
    exact h
  have hsub : combFrame T (eucToFun 8 (L1 (G b))) = G b - L2 (G b) :=
    eq_sub_of_add_eq hEq
  have hA : inner ℝ (combFrame T (eucToFun 8 (L1 (G b)))) (G b) = 0 := by
    rw [combFrame_apply, sum_inner]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [inner_smul_left, horth j b, mul_zero]
  have hB : inner ℝ (combFrame T (eucToFun 8 (L1 (G b)))) (L2 (G b)) = 0 := by
    rw [combFrame_apply, sum_inner]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [inner_smul_left, h2 (G b) j, mul_zero]
  have hself : inner ℝ (combFrame T (eucToFun 8 (L1 (G b))))
      (combFrame T (eucToFun 8 (L1 (G b)))) = 0 := by
    nth_rewrite 2 [hsub]
    rw [inner_sub_right, hA, hB, sub_zero]
  have hzero : combFrame T (eucToFun 8 (L1 (G b))) = 0 := inner_self_eq_zero.mp hself
  have hv : eucToFun 8 (L1 (G b)) = 0 := combFrame_injective T hT (by rw [hzero, combFrame_zero])
  apply eucToFun_injective
  rw [hv]
  rfl

/-- **`L2` is the identity on the normal frame.** -/
theorem L2_apply_G {k : ℕ} (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (G : Fin k → EuclideanSpace ℝ (Fin (8 + k)))
    (L1 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin 8))
    (L2 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (hT : LinearIndependent ℝ T)
    (h1 : ∀ u, Work.ThomBordism.Grassmann.coeffMap T (eucToFun 8 (L1 u))
      + eucToFun (8 + k) (L2 u) = eucToFun (8 + k) u)
    (h2 : ∀ u a, inner ℝ (T a) (L2 u) = 0)
    (horth : ∀ a b, inner ℝ (T a) (G b) = 0) (b : Fin k) : L2 (G b) = G b := by
  have h := combFrame_T_add_L2 T L1 L2 h1 (G b)
  simpa [L1_apply_G T G L1 L2 hT h1 h2 horth b] using h

/-! ## The coordinate splitting of `tcmSumLin` -/

/-- **The first coordinate of the inverse coordinate identification.** -/
theorem tcmSumLin_symm_fst (p q : ℕ) (u : EuclideanSpace ℝ (Fin (p + q))) (i : Fin p) :
    ((Work.Whitney.tcmSumLin p q).symm u).1 i = u (Fin.castAdd q i) := by
  simp only [Work.Whitney.tcmSumLin, ContinuousLinearEquiv.symm_symm, EuclideanSpace.finAddEquivProd,
    EuclideanSpace.sumEquivProd, ContinuousLinearEquiv.trans_apply,
    PiLp.sumPiLpEquivProdLpPiLp_apply_ofLp, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    WithLp.prodContinuousLinearEquiv_apply]
  rfl

/-- **The second coordinate of the inverse coordinate identification.** -/
theorem tcmSumLin_symm_snd (p q : ℕ) (u : EuclideanSpace ℝ (Fin (p + q))) (i : Fin q) :
    ((Work.Whitney.tcmSumLin p q).symm u).2 i = u (Fin.natAdd p i) := by
  simp only [Work.Whitney.tcmSumLin, ContinuousLinearEquiv.symm_symm, EuclideanSpace.finAddEquivProd,
    EuclideanSpace.sumEquivProd, ContinuousLinearEquiv.trans_apply,
    PiLp.sumPiLpEquivProdLpPiLp_apply_ofLp, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    WithLp.prodContinuousLinearEquiv_apply]
  rfl

/-- **The standard basis expansion of a coordinate vector.** -/
theorem sum_smul_single {n : ℕ} (f : Fin n → ℝ) :
    (∑ i, f i • EuclideanSpace.single i (1 : ℝ)) = funToEuc n f := by
  apply WithLp.ofLp_injective
  funext j
  rw [WithLp.ofLp_sum, funToEuc_apply, WithLp.ofLp_toLp]
  rw [Finset.sum_apply]
  rw [Finset.sum_eq_single j]
  · rw [WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, PiLp.ofLp_single, Pi.single_eq_same, mul_one]
  · intro b _ hb
    rw [WithLp.ofLp_smul, Pi.smul_apply, PiLp.ofLp_single, Pi.single_eq_of_ne (Ne.symm hb),
      smul_eq_mul, mul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-! ## The combination lemmas -/

/-- **`L1` on a tangent combination is the identity.** -/
theorem L1_comb_T {k : ℕ} (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (L1 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin 8))
    (L2 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (hT : LinearIndependent ℝ T)
    (h1 : ∀ u, Work.ThomBordism.Grassmann.coeffMap T (eucToFun 8 (L1 u))
      + eucToFun (8 + k) (L2 u) = eucToFun (8 + k) u)
    (h2 : ∀ u a, inner ℝ (T a) (L2 u) = 0) (a : Fin 8 → ℝ) :
    L1 (combFrame T a) = funToEuc 8 a := by
  rw [combFrame_apply, map_sum]
  rw [Finset.sum_congr rfl (fun j _ => by rw [map_smul, L1_apply_T T L1 L2 hT h1 h2 j])]
  exact sum_smul_single a

/-- **`L1` vanishes on a normal combination.** -/
theorem L1_comb_G {k : ℕ} (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (G : Fin k → EuclideanSpace ℝ (Fin (8 + k)))
    (L1 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin 8))
    (L2 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (hT : LinearIndependent ℝ T)
    (h1 : ∀ u, Work.ThomBordism.Grassmann.coeffMap T (eucToFun 8 (L1 u))
      + eucToFun (8 + k) (L2 u) = eucToFun (8 + k) u)
    (h2 : ∀ u a, inner ℝ (T a) (L2 u) = 0)
    (horth : ∀ a b, inner ℝ (T a) (G b) = 0) (b : Fin k → ℝ) :
    L1 (combFrame G b) = 0 := by
  rw [combFrame_apply, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, L1_apply_G T G L1 L2 hT h1 h2 horth j, smul_zero]

/-- **`L2` vanishes on a tangent combination.** -/
theorem L2_comb_T {k : ℕ} (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (L1 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin 8))
    (L2 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (h1 : ∀ u, Work.ThomBordism.Grassmann.coeffMap T (eucToFun 8 (L1 u))
      + eucToFun (8 + k) (L2 u) = eucToFun (8 + k) u)
    (h2 : ∀ u a, inner ℝ (T a) (L2 u) = 0) (a : Fin 8 → ℝ) :
    L2 (combFrame T a) = 0 := by
  rw [combFrame_apply, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_smul, L2_apply_T T L1 L2 h1 h2 j, smul_zero]

/-- **`L2` is the identity on a normal combination.** -/
theorem L2_comb_G {k : ℕ} (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (G : Fin k → EuclideanSpace ℝ (Fin (8 + k)))
    (L1 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin 8))
    (L2 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (hT : LinearIndependent ℝ T)
    (h1 : ∀ u, Work.ThomBordism.Grassmann.coeffMap T (eucToFun 8 (L1 u))
      + eucToFun (8 + k) (L2 u) = eucToFun (8 + k) u)
    (h2 : ∀ u a, inner ℝ (T a) (L2 u) = 0)
    (horth : ∀ a b, inner ℝ (T a) (G b) = 0) (b : Fin k → ℝ) :
    L2 (combFrame G b) = combFrame G b := by
  rw [combFrame_apply, map_sum]
  rw [Finset.sum_congr rfl (fun j _ => by rw [map_smul, L2_apply_G T G L1 L2 hT h1 h2 horth j])]

/-- **The coordinate reading of a normal combination.** -/
theorem readFrame_comb_G {k : ℕ} (G : Fin k → EuclideanSpace ℝ (Fin (8 + k)))
    (hG : Orthonormal ℝ G) (b : Fin k → ℝ) :
    readFrame G (combFrame G b) = funToEuc k b := by
  rw [show readFrame G (combFrame G b)
      = Work.Tubular.funToEuc k (fun j => inner ℝ (G j) (combFrame G b)) from
    readFrame_apply G (combFrame G b)]
  rw [combFrame_apply]
  rw [show (fun j => inner ℝ (G j) (∑ i, b i • G i)) = b from
    funext fun j => hG.inner_right_fintype b j]
  rfl

/-! ## The product coordinate map and its inverse -/

/-- The composite `tcmSumLin 8 k ∘ (L1, readFrame G ∘ L2)` of the statement. -/
def Phi {k : ℕ} (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (G : Fin k → EuclideanSpace ℝ (Fin (8 + k)))
    (L1 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin 8))
    (L2 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k))) :
    EuclideanSpace ℝ (Fin (8 + k)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (8 + k)) :=
  (Work.Whitney.tcmSumLin 8 k).toLinearMap ∘ₗ (L1.prod ((readFrame G).comp L2)).toLinearMap

theorem Phi_apply {k : ℕ} (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (G : Fin k → EuclideanSpace ℝ (Fin (8 + k)))
    (L1 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin 8))
    (L2 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (u : EuclideanSpace ℝ (Fin (8 + k))) :
    Phi T G L1 L2 u = Work.Whitney.tcmSumLin 8 k (L1 u, readFrame G (L2 u)) := rfl

/-- The candidate inverse of the product coordinate map: the coordinate reading of a vector in the
pair frame `(T, G)`. -/
def Sig {k : ℕ} (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (G : Fin k → EuclideanSpace ℝ (Fin (8 + k))) :
    EuclideanSpace ℝ (Fin (8 + k)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (8 + k)) :=
  (combFrame T).comp ((eucToFun 8).toLinearMap.comp ((LinearMap.fst ℝ (EuclideanSpace ℝ (Fin 8))
      (EuclideanSpace ℝ (Fin k))).comp (Work.Whitney.tcmSumLin 8 k).symm.toLinearMap))
  + (combFrame G).comp ((eucToFun k).toLinearMap.comp ((LinearMap.snd ℝ (EuclideanSpace ℝ (Fin 8))
      (EuclideanSpace ℝ (Fin k))).comp (Work.Whitney.tcmSumLin 8 k).symm.toLinearMap))

theorem Sig_apply {k : ℕ} (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (G : Fin k → EuclideanSpace ℝ (Fin (8 + k))) (z : EuclideanSpace ℝ (Fin (8 + k))) :
    Sig T G z = combFrame T (eucToFun 8 ((Work.Whitney.tcmSumLin 8 k).symm z).1)
      + combFrame G (eucToFun k ((Work.Whitney.tcmSumLin 8 k).symm z).2) := rfl

/-- **The composite on a pair-frame combination is the coordinate vector.** -/
theorem Phi_sigma {k : ℕ} (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (G : Fin k → EuclideanSpace ℝ (Fin (8 + k)))
    (L1 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin 8))
    (L2 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (hT : LinearIndependent ℝ T)
    (h1 : ∀ u, Work.ThomBordism.Grassmann.coeffMap T (eucToFun 8 (L1 u))
      + eucToFun (8 + k) (L2 u) = eucToFun (8 + k) u)
    (h2 : ∀ u a, inner ℝ (T a) (L2 u) = 0) (hG : Orthonormal ℝ G)
    (horth : ∀ a b, inner ℝ (T a) (G b) = 0) (a : Fin 8 → ℝ) (b : Fin k → ℝ) :
    Phi T G L1 L2 (combFrame T a + combFrame G b)
      = Work.Whitney.tcmSumLin 8 k (funToEuc 8 a, funToEuc k b) := by
  rw [Phi_apply]
  simp only [map_add, L1_comb_T T L1 L2 hT h1 h2 a, L1_comb_G T G L1 L2 hT h1 h2 horth b,
    L2_comb_T T L1 L2 h1 h2 a, L2_comb_G T G L1 L2 hT h1 h2 horth b,
    readFrame_comb_G G hG b, zero_add, add_zero]

/-- **The product coordinate map is a left inverse of the coordinate reading in the pair frame.** -/
theorem Phi_comp_Sig {k : ℕ} (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (G : Fin k → EuclideanSpace ℝ (Fin (8 + k)))
    (L1 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin 8))
    (L2 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (hT : LinearIndependent ℝ T)
    (h1 : ∀ u, Work.ThomBordism.Grassmann.coeffMap T (eucToFun 8 (L1 u))
      + eucToFun (8 + k) (L2 u) = eucToFun (8 + k) u)
    (h2 : ∀ u a, inner ℝ (T a) (L2 u) = 0) (hG : Orthonormal ℝ G)
    (horth : ∀ a b, inner ℝ (T a) (G b) = 0) :
    Phi T G L1 L2 ∘ₗ Sig T G = LinearMap.id := by
  apply LinearMap.ext
  intro z
  rw [LinearMap.comp_apply, LinearMap.id_apply, Sig_apply,
    Phi_sigma T G L1 L2 hT h1 h2 hG horth _ _]
  rw [funToEuc_eucToFun, funToEuc_eucToFun]
  exact (Work.Whitney.tcmSumLin 8 k).apply_symm_apply z

/-- **Determinant multiplicativity of the inverse relation.** -/
theorem det_Phi_mul_det_Sig {k : ℕ} (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (G : Fin k → EuclideanSpace ℝ (Fin (8 + k)))
    (L1 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin 8))
    (L2 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (hT : LinearIndependent ℝ T)
    (h1 : ∀ u, Work.ThomBordism.Grassmann.coeffMap T (eucToFun 8 (L1 u))
      + eucToFun (8 + k) (L2 u) = eucToFun (8 + k) u)
    (h2 : ∀ u a, inner ℝ (T a) (L2 u) = 0) (hG : Orthonormal ℝ G)
    (horth : ∀ a b, inner ℝ (T a) (G b) = 0) :
    LinearMap.det (Phi T G L1 L2) * LinearMap.det (Sig T G) = 1 := by
  have h := LinearMap.det_comp (Phi T G L1 L2) (Sig T G)
  rw [Phi_comp_Sig T G L1 L2 hT h1 h2 hG horth, LinearMap.det_id] at h
  exact h.symm

/-! ## The determinant of the coordinate reading

The matrix of `Sig` in the standard basis is the pair matrix `pairMat T G` reindexed along
`finSumFinEquiv`; reindexing does not change the determinant. -/

/-- **`Sig` of a standard basis vector is the corresponding vector of the pair frame.** -/
theorem Sig_single_inl {k : ℕ} (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (G : Fin k → EuclideanSpace ℝ (Fin (8 + k))) (i : Fin 8) :
    Sig T G (EuclideanSpace.single (finSumFinEquiv (Sum.inl i)) 1) = T i := by
  rw [Sig_apply]
  have hfirst : eucToFun 8 ((Work.Whitney.tcmSumLin 8 k).symm
      (EuclideanSpace.single (finSumFinEquiv (Sum.inl i)) 1)).1 = Pi.single i 1 := by
    funext j
    rw [eucToFun_apply, tcmSumLin_symm_fst 8 k _ j, PiLp.single_apply, finSumFinEquiv_apply_left]
    by_cases h : j = i
    · rw [if_pos (Fin.castAdd_inj.mpr h), h, Pi.single_eq_same]
    · rw [if_neg (fun hh => h (Fin.castAdd_inj.mp hh)), Pi.single_eq_of_ne h]
  have hsecond : eucToFun k ((Work.Whitney.tcmSumLin 8 k).symm
      (EuclideanSpace.single (finSumFinEquiv (Sum.inl i)) 1)).2 = 0 := by
    funext l
    rw [eucToFun_apply, tcmSumLin_symm_snd 8 k _ l, PiLp.single_apply, finSumFinEquiv_apply_left]
    have hne : Fin.natAdd 8 l ≠ Fin.castAdd k i := by
      intro hh
      have h := congrArg Fin.val hh
      rw [Fin.val_natAdd, Fin.val_castAdd] at h
      omega
    rw [if_neg hne]
    rfl
  rw [hfirst, hsecond, combFrame_single, combFrame_zero, add_zero]

/-- **`Sig` of a standard basis vector is the corresponding vector of the pair frame.** -/
theorem Sig_single_inr {k : ℕ} (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (G : Fin k → EuclideanSpace ℝ (Fin (8 + k))) (l : Fin k) :
    Sig T G (EuclideanSpace.single (finSumFinEquiv (Sum.inr l)) 1) = G l := by
  rw [Sig_apply]
  have hfirst : eucToFun 8 ((Work.Whitney.tcmSumLin 8 k).symm
      (EuclideanSpace.single (finSumFinEquiv (Sum.inr l)) 1)).1 = 0 := by
    funext j
    rw [eucToFun_apply, tcmSumLin_symm_fst 8 k _ j, PiLp.single_apply, finSumFinEquiv_apply_right]
    have hne : Fin.castAdd k j ≠ Fin.natAdd 8 l := by
      intro hh
      have h := congrArg Fin.val hh
      rw [Fin.val_castAdd, Fin.val_natAdd] at h
      omega
    rw [if_neg hne]
    rfl
  have hsecond : eucToFun k ((Work.Whitney.tcmSumLin 8 k).symm
      (EuclideanSpace.single (finSumFinEquiv (Sum.inr l)) 1)).2 = Pi.single l 1 := by
    funext j
    rw [eucToFun_apply, tcmSumLin_symm_snd 8 k _ j, PiLp.single_apply, finSumFinEquiv_apply_right]
    by_cases h : j = l
    · rw [if_pos ((Fin.natAdd_inj 8).mpr h), h, Pi.single_eq_same]
    · rw [if_neg (fun hh => h ((Fin.natAdd_inj 8).mp hh)), Pi.single_eq_of_ne h]
  rw [hfirst, hsecond, combFrame_zero, combFrame_single, zero_add]

/-- **`Sig` reads a standard basis vector as the corresponding vector of the pair frame.** -/
theorem Sig_single {k : ℕ} (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (G : Fin k → EuclideanSpace ℝ (Fin (8 + k))) (j : Fin (8 + k)) :
    Sig T G (EuclideanSpace.single j 1) = pairFrame T G (finSumFinEquiv.symm j) := by
  obtain ⟨s, rfl⟩ : ∃ s : Fin 8 ⊕ Fin k, finSumFinEquiv s = j :=
    ⟨finSumFinEquiv.symm j, finSumFinEquiv.apply_symm_apply j⟩
  cases s with
  | inl i => rw [Sig_single_inl]; simp
  | inr l => rw [Sig_single_inr]; simp

/-- **The determinant of the coordinate reading in the pair frame is the pair determinant.** -/
theorem det_Sig {k : ℕ} (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (G : Fin k → EuclideanSpace ℝ (Fin (8 + k))) :
    LinearMap.det (Sig T G) = (pairMat T G).det := by
  let e : EuclideanSpace ℝ (Fin (8 + k)) ≃ₗ[ℝ] (Fin (8 + k) → ℝ) :=
    (EuclideanSpace.equiv (Fin (8 + k)) ℝ).toLinearEquiv
  let F : (Fin (8 + k) → ℝ) →ₗ[ℝ] (Fin (8 + k) → ℝ) :=
    (e : EuclideanSpace ℝ (Fin (8 + k)) →ₗ[ℝ] (Fin (8 + k) → ℝ)) ∘ₗ Sig T G
      ∘ₗ (e.symm : (Fin (8 + k) → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
  have hconj : LinearMap.det F = LinearMap.det (Sig T G) := LinearMap.det_conj (Sig T G) e
  have hmat : LinearMap.toMatrix' F
      = (pairMat T G).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
    ext i j
    rw [LinearMap.toMatrix'_apply, Matrix.submatrix_apply, pairMat_apply]
    show e (Sig T G (e.symm (Pi.single j 1))) i
      = eucToFun (8 + k) (pairFrame T G (finSumFinEquiv.symm j))
          (finSumFinEquiv (finSumFinEquiv.symm i))
    rw [show e.symm (Pi.single j 1) = EuclideanSpace.single j 1 from rfl, Sig_single T G j,
      Equiv.apply_symm_apply]
    rfl
  rw [← hconj, ← LinearMap.det_toMatrix', hmat]
  exact Matrix.det_submatrix_equiv_self finSumFinEquiv.symm (pairMat T G)

/-- **The determinant sign of the product coordinate map of the tube.**

Let `T : Fin 8 → ℝ^{8+k}` be a linearly independent frame, `G : Fin k → ℝ^{8+k}` an orthonormal frame
orthogonal to `T` (with `1 ≤ k`), and let `L1, L2` be the derivative of the tube coordinates pinned
by the two identities

* `coeffMap T (eucToFun 8 (L1 u)) + eucToFun (8+k) (L2 u) = eucToFun (8+k) u` (the differentiated
  identity `E.e (foot y) + vec y = y` of the tube chart), and
* `inner ℝ (T a) (L2 u) = 0` (the differentiated normality of `vec`).

Then the composite `tcmSumLin 8 k ∘ (L1, readFrame G ∘ L2) : ℝ^{8+k} → ℝ^{8+k}` (the "product
coordinate map" whose pullback of `stdModelGen (8+k)` is compared with the ambient reading in step
(GM) of the last-mile plan) has determinant sign exactly `pairSign T G`.

Content: the two clauses force `L1 = (coeffMap T)^{-1} ∘ pr_T` and `L2 = pr_ν`, and
`readFrame G ∘ pr_ν = readFrame G` (since `G ⊥ T`); so the matrix of the composite is
`P · [T, G]^{-1}` with `P` the standard reindexing permutation, while
`pairMat T G = P · [T, G]`; the two `P`-signs coincide (`det (Pᵀ) = det P`), so
`sign (det Φ) = sign (det [T,G])^{-1} = sign (det [T,G]) = pairSign T G`.  In particular the
reindexing constant cancels and no extra convention constant appears. -/
theorem gmSign {k : ℕ} (hk : 1 ≤ k)
    (T : Fin 8 → EuclideanSpace ℝ (Fin (8 + k)))
    (G : Fin k → EuclideanSpace ℝ (Fin (8 + k)))
    (L1 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin 8))
    (L2 : EuclideanSpace ℝ (Fin (8 + k)) →L[ℝ] EuclideanSpace ℝ (Fin (8 + k)))
    (hT : LinearIndependent ℝ T) (hG : Orthonormal ℝ G)
    (horth : ∀ a b, inner ℝ (T a) (G b) = 0)
    (h1 : ∀ u, Work.ThomBordism.Grassmann.coeffMap T
        (Work.ThomBordism.PontryaginThom.eucToFun 8 (L1 u))
      + Work.ThomBordism.PontryaginThom.eucToFun (8 + k) (L2 u)
      = Work.ThomBordism.PontryaginThom.eucToFun (8 + k) u)
    (h2 : ∀ u a, inner ℝ (T a) (L2 u) = 0) :
    Real.sign (LinearMap.det ((Work.Whitney.tcmSumLin 8 k).toLinearMap.comp
        ((L1.prod ((Work.ThomBordism.readFrame G).comp L2)).toLinearMap)))
      = Work.ThomBordism.OrthFrame.pairSign T G := by
  have hdet := det_Phi_mul_det_Sig T G L1 L2 hT h1 h2 hG horth
  rw [det_Sig T G] at hdet
  show Real.sign (LinearMap.det (Phi T G L1 L2)) = Work.ThomBordism.OrthFrame.pairSign T G
  rw [pairSign]
  have hb : (pairMat T G).det = (LinearMap.det (Phi T G L1 L2))⁻¹ :=
    eq_inv_of_mul_eq_one_right hdet
  rw [hb, Real.sign_inv]

end

end Work.ThomBordism.KeyLocal
