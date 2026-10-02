import Mathlib
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.Realified
import Submission.Work.Whitney.ConjDefs
import Submission.Work.Whitney.sumFibreC_cxOfReal
import Submission.Work.Whitney.sumFibre_cxTrans

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The gauge `P` of the splitting `E_ℝ ⊗_ℝ ℂ ≅ E ⊕ Ē`

For the complex bundle `E` with model fibre `ℂ^m`, the complexification of its underlying real
bundle, `E_ℝ ⊗_ℝ ℂ = complexificationCore (realifiedCore E)`, is isomorphic to `E ⊕ Ē =
whitneySum E (conjCore E)`.  The isomorphism is the *constant* gauge

  `gaugePC m : ℂ^{m+m} →L[ℂ] ℂ^{m+m}`,  `gaugePC m = sumFibreC m m ∘ P₀ ∘ (sumFibreC m m)⁻¹`

in the `ℂ^m ⊕ ℂ^m` coordinates, where `P₀ (a, b) = (a + i b, a - i b)`, i.e. the classical
eigenvector gauge `(a ⊗ 1 + b ⊗ i) ↦ (a + i b, a - i b)`.

This module defines the gauge (`Work.Whitney.pairGaugeL`, `Work.Whitney.pairGauge`,
`Work.Whitney.gaugePE`, `Work.Whitney.gaugePC`) together with the two computations that make it a
bundle isomorphism:

* `Work.Whitney.gaugePC_cxOfReal_reIm` — the gauge on the real part of a complexified vector;
* `Work.Whitney.gaugePC_cxTrans` — **the gauge identity**: for a complex-linear `g` on `ℂ^m` with
  realified map `Work.Whitney.reImify m g` on `ℝ^{m+m}` and conjugate `Work.Thom.conjCLM m g`,

  `gaugePC m ∘ cxTrans (reImify m g) = transportEnd (sumFibreC m m) g (conjCLM m g) ∘ gaugePC m`.

The right-hand side is the transition function of `E ⊕ Ē` in the `ℂ^m ⊕ ℂ^m` coordinates and the
left-hand side that of `E_ℝ ⊗_ℝ ℂ` (see `Submission/Work/Whitney/nonempty_bundleIso_...`).
-/

namespace Work.Whitney

open Work.TangentClasses Work.Thom

noncomputable section

variable {m : ℕ}

/-! ## Multiplication by `i` as a `ℂ`-linear map -/

/-- Multiplication by `Complex.I` on `ℂ^m`, as a `ℂ`-linear map. -/
def mulIL (m : ℕ) : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m) :=
  Complex.I • (1 : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin m))

theorem mulIL_apply (m : ℕ) (v : EuclideanSpace ℂ (Fin m)) : mulIL m v = Complex.I • v := rfl

theorem mulIL_cxMulI (m : ℕ) (v : EuclideanSpace ℂ (Fin m)) : mulIL m v = cxMulI v :=
  (cxMulI_eq_smul m v).symm

theorem mulIL_mulIL (m : ℕ) (v : EuclideanSpace ℂ (Fin m)) : mulIL m (mulIL m v) = -v := by
  rw [mulIL_apply, mulIL_apply, smul_smul, Complex.I_mul_I, neg_one_smul]

/-! ## The pair gauge `(a, b) ↦ (a + i b, a - i b)` on `ℂ^m × ℂ^m` -/

/-- **The pair gauge** `ℂ^m × ℂ^m → ℂ^m × ℂ^m`, `(a, b) ↦ (a + i b, a - i b)`. -/
def pairGaugeL (m : ℕ) :
    (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) :=
  LinearMap.prod ((LinearMap.fst ℂ _ _) + (mulIL m).comp (LinearMap.snd ℂ _ _))
    ((LinearMap.fst ℂ _ _) - (mulIL m).comp (LinearMap.snd ℂ _ _))

/-- **Its two-sided inverse** `(u, w) ↦ ((u + w)/2, i (w - u)/2)`. -/
def pairGaugeInvL (m : ℕ) :
    (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) →ₗ[ℂ]
      (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) :=
  LinearMap.prod (((2:ℂ)⁻¹) • ((LinearMap.fst ℂ _ _) + (LinearMap.snd ℂ _ _)))
    (((2:ℂ)⁻¹) • ((mulIL m).comp ((LinearMap.snd ℂ _ _) - (LinearMap.fst ℂ _ _))))

theorem pairGaugeL_apply (m : ℕ) (v : EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) :
    pairGaugeL m v = (v.1 + mulIL m v.2, v.1 - mulIL m v.2) := by
  simp [pairGaugeL]

theorem pairGaugeInvL_apply (m : ℕ)
    (w : EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) :
    pairGaugeInvL m w = ((2:ℂ)⁻¹ • (w.1 + w.2), (2:ℂ)⁻¹ • (mulIL m (w.2 - w.1))) := by
  simp [pairGaugeInvL]

theorem two_inv_mul : ((2:ℂ)⁻¹ * 2) = 1 := by norm_num

theorem two_inv_smul_two (m : ℕ) (x : EuclideanSpace ℂ (Fin m)) :
    (2:ℂ)⁻¹ • ((2:ℂ) • x) = x := by
  rw [smul_smul, two_inv_mul, one_smul]

theorem pairGaugeInvL_pairGaugeL (m : ℕ)
    (v : EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) :
    pairGaugeInvL m (pairGaugeL m v) = v := by
  rw [pairGaugeL_apply, pairGaugeInvL_apply]
  refine Prod.ext ?_ ?_
  · show (2:ℂ)⁻¹ • ((v.1 + mulIL m v.2) + (v.1 - mulIL m v.2)) = v.1
    rw [show (v.1 + mulIL m v.2) + (v.1 - mulIL m v.2) = (2:ℂ) • v.1 from by
      rw [two_smul]; abel]
    exact two_inv_smul_two m v.1
  · show (2:ℂ)⁻¹ • (mulIL m ((v.1 - mulIL m v.2) - (v.1 + mulIL m v.2))) = v.2
    rw [show (v.1 - mulIL m v.2) - (v.1 + mulIL m v.2) = -((2:ℂ) • (mulIL m v.2)) from by
      rw [two_smul]; abel]
    rw [map_neg, map_smul, mulIL_mulIL, smul_neg, smul_smul, two_inv_mul, one_smul, neg_neg]

theorem pairGaugeL_pairGaugeInvL (m : ℕ)
    (v : EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) :
    pairGaugeL m (pairGaugeInvL m v) = v := by
  rw [pairGaugeInvL_apply, pairGaugeL_apply]
  refine Prod.ext ?_ ?_
  · show ((2:ℂ)⁻¹ • (v.1 + v.2)) + mulIL m ((2:ℂ)⁻¹ • (mulIL m (v.2 - v.1))) = v.1
    rw [map_smul, mulIL_mulIL, smul_neg, ← sub_eq_add_neg, ← smul_sub]
    rw [show (v.1 + v.2) - (v.2 - v.1) = (2:ℂ) • v.1 from by rw [two_smul]; abel]
    exact two_inv_smul_two m v.1
  · show ((2:ℂ)⁻¹ • (v.1 + v.2)) - mulIL m ((2:ℂ)⁻¹ • (mulIL m (v.2 - v.1))) = v.2
    rw [map_smul, mulIL_mulIL, smul_neg, sub_neg_eq_add, ← smul_add]
    rw [show (v.1 + v.2) + (v.2 - v.1) = (2:ℂ) • v.2 from by rw [two_smul]; abel]
    exact two_inv_smul_two m v.2

/-- The pair gauge as a **linear equivalence** of `ℂ^m × ℂ^m`. -/
def pairGauge (m : ℕ) :
    (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) ≃ₗ[ℂ]
      (EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) :=
  LinearEquiv.ofBijective (pairGaugeL m)
    (Function.bijective_iff_has_inverse.mpr
      ⟨pairGaugeInvL m, fun v => pairGaugeInvL_pairGaugeL m v,
        fun v => pairGaugeL_pairGaugeInvL m v⟩)

@[simp] theorem pairGauge_apply (m : ℕ)
    (v : EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) :
    pairGauge m v = pairGaugeL m v := rfl

/-! ## The gauge on `ℂ^{m+m}` -/

/-- **The gauge `P` of the splitting `E_ℝ ⊗_ℝ ℂ ≅ E ⊕ Ē`**, as a continuous linear equivalence of
`ℂ^{m+m} = ℂ^m ⊗_ℝ ℂ`: in the `ℂ^m ⊕ ℂ^m` coordinates of `Work.Whitney.sumFibreC m m` it is
`(a, b) ↦ (a + i b, a - i b)`. -/
def gaugePE (m : ℕ) :
    EuclideanSpace ℂ (Fin (m + m)) ≃L[ℂ] EuclideanSpace ℂ (Fin (m + m)) :=
  ((sumFibreC m m).symm).trans
    (((pairGauge m).toContinuousLinearEquiv).trans (sumFibreC m m))

/-- The underlying continuous linear map of the gauge. -/
def gaugePC (m : ℕ) :
    EuclideanSpace ℂ (Fin (m + m)) →L[ℂ] EuclideanSpace ℂ (Fin (m + m)) :=
  gaugePE m

theorem gaugePE_coe (m : ℕ) : (gaugePE m : EuclideanSpace ℂ (Fin (m + m)) →L[ℂ] _) = gaugePC m :=
  rfl

theorem gaugePC_apply (m : ℕ) (v : EuclideanSpace ℂ (Fin (m + m))) :
    gaugePC m v = sumFibreC m m (pairGaugeL m ((sumFibreC m m).symm v)) := by
  rw [gaugePC, gaugePE]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.trans_apply]
  rfl

theorem gaugePC_apply_pair (m : ℕ)
    (w : EuclideanSpace ℂ (Fin m) × EuclideanSpace ℂ (Fin m)) :
    gaugePC m (sumFibreC m m w) = sumFibreC m m (pairGaugeL m w) := by
  rw [gaugePC_apply, ContinuousLinearEquiv.symm_apply_apply]

/-! ## The gauge on the real part of a complexified vector -/

theorem conjC_decomp (m : ℕ) (w : EuclideanSpace ℂ (Fin m)) :
    conjC m w = cxOfReal (cxRePart w) - cxMulI (cxOfReal (cxImPart w)) := by
  conv_lhs => rw [← cxOfReal_cxRePart_add_cxMulI_cxImPart w]
  rw [map_add, conjC_cxOfReal, conjC_cxMulI, conjC_cxOfReal]
  rw [sub_eq_add_neg]

theorem cxOfReal_reImCore (m : ℕ) (w : EuclideanSpace ℂ (Fin m)) :
    cxOfReal (reImCore m w)
      = sumFibreC m m (cxOfReal (cxRePart w), cxOfReal (cxImPart w)) := by
  rw [reImCore_apply, sumFibreC_cxOfReal]

/-- **The gauge on the real part**: for `w : ℂ^m`, the gauge sends the realification
`cxOfReal (reImCore m w)` of `w` to the pair `(w, conj w)` of the `ℂ^m ⊕ ℂ^m` coordinates. -/
theorem gaugePC_cxOfReal_reIm (m : ℕ) (w : EuclideanSpace ℂ (Fin m)) :
    gaugePC m (cxOfReal (reImCore m w)) = sumFibreC m m (w, conjC m w) := by
  rw [cxOfReal_reImCore m w, gaugePC_apply_pair, pairGaugeL_apply, mulIL_cxMulI, conjC_decomp,
    cxOfReal_cxRePart_add_cxMulI_cxImPart]

/-! ## The realification of a complex-linear endomorphism, in the `ℝ^{m+m}` presentation -/

/-- **The realification of a complex-linear endomorphism `g` of `ℂ^m` in the `ℝ^{m+m}`
presentation**: `reImEquiv m ∘ g_ℝ ∘ (reImEquiv m)⁻¹`.  It is the transition function of
`Work.Whitney.realifiedCore Z` at a point, written in terms of the transition function of `Z`. -/
def reImify (m : ℕ) (g : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)) :
    EuclideanSpace ℝ (Fin (m + m)) →L[ℝ] EuclideanSpace ℝ (Fin (m + m)) :=
  ((reImEquiv m : EuclideanSpace ℂ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin (m + m)))).comp
    ((ContinuousLinearMap.restrictScalars ℝ g).comp
      ((reImEquiv m).symm : EuclideanSpace ℝ (Fin (m + m)) →L[ℝ] EuclideanSpace ℂ (Fin m)))

theorem reImify_apply (m : ℕ) (g : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m))
    (v : EuclideanSpace ℝ (Fin (m + m))) :
    reImify m g v = reImCore m (g (pairCxCore m v)) := by
  simp [reImify, reImEquiv_apply, reImEquiv_symm_apply]

theorem reImify_apply_reImCore (m : ℕ)
    (g : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)) (w : EuclideanSpace ℂ (Fin m)) :
    reImify m g (reImCore m w) = reImCore m (g w) := by
  rw [reImify_apply, pairCxCore_reImCore]

/-! ## The gauge identity -/

/-- **The gauge identity.**  For a complex-linear endomorphism `g` of `ℂ^m`, conjugating its
realification `cxTrans (reImify m g)` in the `E_ℝ ⊗_ℝ ℂ` coordinates into the `E ⊕ Ē` coordinates is
the same as conjugating `g ⊕ ḡ` there:

`gaugePC m ∘ cxTrans (reImify m g) = transportEnd (sumFibreC m m) g (conjCLM m g) ∘ gaugePC m`. -/
theorem gaugePC_cxTrans (m : ℕ) (g : EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)) :
    (gaugePC m).comp (cxTrans (reImify m g))
      = (transportEnd (sumFibreC m m) g (conjCLM m g)).comp (gaugePC m) := by
  have key : ∀ w : EuclideanSpace ℂ (Fin m),
      gaugePC m (cxTrans (reImify m g) (cxOfReal (reImCore m w)))
        = transportEnd (sumFibreC m m) g (conjCLM m g)
            (gaugePC m (cxOfReal (reImCore m w))) := by
    intro w
    rw [cxTrans_cxOfReal, reImify_apply_reImCore, gaugePC_cxOfReal_reIm]
    rw [transportEnd]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply, gaugePC_cxOfReal_reIm]
    rw [ContinuousLinearMap.coe_prodMap', Prod.map_apply, conjCLM_apply, conjC_involutive]
  apply ext_of_cxOfReal
  intro u
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
  have h := key (pairCxCore m u)
  rw [reImCore_pairCxCore] at h
  exact h

end

end Work.Whitney
