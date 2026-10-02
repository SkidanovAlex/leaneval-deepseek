import Mathlib
import Submission.Work.Agree.S4Bundle
import Submission.Work.Whitney.Basic
import Submission.Work.Whitney.nonempty_bundleIso_whitneySum_comm
import Submission.Work.Thom.complexification
import Submission.Work.Thom.realification
import Submission.Work.Gen.EulerToolkit
import Submission.Work.Agree.crux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

/-!
# The complex line bundles `V_a` over `S⁴` whose realification is `L^a R^0`

This module builds the *complex* half of the Bott normalisation `Work.Agree.BottHopf`: for the
quaternionic line bundle `L^a R^0 = Work.Agree.clutchBundle a 0` over `S⁴` (clutching `v ↦ q^a v`,
`q = uDir p` a unit quaternion) we construct a rank-`2` complex bundle `V_a` with

* `Work.Agree.realification_cLine_iso_clutchBundle` -- the underlying real bundle of `V_a` is
  `L^a R^0`;
* `Work.Agree.key` -- the complexified transition of `ℂ ⊗_ℝ L^a R^0` is the diagonal action of the
  transition of `V_a` in the eigenbasis of `J = id_ℂ ⊗ R_i`, i.e. the splitting
  `ℂ ⊗_ℝ L^a R^0 ≅ V_a ⊕ V̄_a` (and `V̄_a ≅ V_a` for a quaternionic line bundle, right
  multiplication by `j` being the `ℂ`-linear identification).

Together with the degree-`2` Whitney formula (`Work.Agree.whitneyTwoTwo`) this reduces the target
`c₂(ℂ ⊗ L^a R^0) = ± 2a·G` to `c₂(V_a) = ± a·G`, i.e. to the Euler class of the quaternionic Hopf
bundle -- the transgression/Gysin input (`Work.Agree.eulerClutch`).

## The construction

Write an element of `ℂ ⊗_ℝ ℍ` in the tensor basis `1⊗1, 1⊗i, 1⊗j, 1⊗k` with coordinates
`(z₁,z₂,z₃,z₄)`; right multiplication by `i` is a complex structure `J`, with eigenprojections
`(1 ± iJ)/2` (`Work.Agree.Pplus`, `Work.Agree.Pminus`).  Writing `q = q_ℂ + q_P j`
(`Work.Agree.qC`, `Work.Agree.qP`), left multiplication by `q` acts on the `+i`-eigenspace in the
coordinates `(z₁,z₃)` by the matrix `M_q = [[q_ℂ, -q_P],[conj q_P, conj q_ℂ]] ∈ SU(2)`
(`Work.Agree.Mmat`, multiplicative: `Mmat_mul`, `Mmat_one`), and on the `-i`-eigenspace by
`conj M_q`; the two are interchanged by the constant gauge `(u,v) ↦ (-v,u)` (`Work.Agree.gg`), which
is multiplication by `j` (`Work.Agree.Ppair_key`, `Work.Agree.key`).

`V_a` is the two-chart complex bundle with clutching `M_{uDir p ^ a}` (`Work.Agree.cLine`); its
realification is `L^a R^0` via the real-linear gauge `(z₀,z₁) ↦ z₀ + conj(z₁) j`
(`Work.Agree.eFlatLin`, `Work.Agree.qTwist_comp_eFlat`).

## Status

Everything here is proved and sorry-free, including the splitting isomorphism
**`Work.Agree.complexificationCore_iso_whitneySum a`**: `ℂ ⊗_ℝ L^a R^0 ≅ V_a ⊕ V_a`.  It is
assembled from the chart-wise matrix `Work.Agree.splitGauge` of the identity map (pointwise forms
`splitGauge_eq`, `splitGaugeInv_eq`), the transition compatibility `Work.Agree.Ycomp_X`, and the
general gauge lemma `Work.Thom.nonempty_bundleIso_of_gauge`
(`Submission/Work/Gen/EulerToolkit.lean`); the eight obligations are `splitGauge_continuousOn`,
`splitGaugeInv_continuousOn`, `splitGauge_htgt`, `splitGauge_hsrc`, `splitGauge_htgtinv`,
`splitGauge_hsrcinv`, `splitGauge_hleft`, `splitGauge_hright`.

The class-level consequence `Work.Agree.chernClass_complexification_clutch` and the final assembly
`Work.Agree.bottHopf_of_bricks` are also proved here: the latter derives `Work.Agree.BottHopf` from

* `hW`: the degree-`2` Whitney formula for sums of two rank-`2` complex bundles over `S⁴`
  (the delegated brick `Work.Agree.whitneyTwoTwo`), and
* `hE`: `c₂(V_a) = ± a·G`, the canonical (Euler-class) form of the delegated brick
  `Work.Agree.eulerClutch` -- `Work.Thom.chernClass_succ_top'` converts
  `chernClass 2 2 (cLine a)` into `(thomClassRank 2 _ (cLine a)).eulerClass`.

Both `hW` and `hE` are reviewed and approved requests that still await a free prover.
-/

namespace Work.Agree

open Work.TangentClasses
open Classical

noncomputable section

/-! ## §1. The `2 × 2` matrix of a quaternion -/

/-- The `ℂ`-component `a + b I` of a quaternion `a + b i + c j + d k`. -/
def qC (q : Quaternion ℝ) : ℂ := ⟨q.re, q.imI⟩

/-- The `ℂj`-component `c + d I` of a quaternion `a + b i + c j + d k` (so the quaternion is
`qC q + qP q * j`). -/
def qP (q : Quaternion ℝ) : ℂ := ⟨q.imJ, q.imK⟩

@[simp] lemma qC_one : qC (1 : Quaternion ℝ) = 1 := by
  apply Complex.ext <;> simp [qC, Quaternion.re_one, Quaternion.imI_one]

@[simp] lemma qP_one : qP (1 : Quaternion ℝ) = 0 := by
  apply Complex.ext <;> simp [qP, Quaternion.imJ_one, Quaternion.imK_one]

@[simp] lemma qC_add (q q' : Quaternion ℝ) : qC (q + q') = qC q + qC q' := by
  apply Complex.ext <;> simp [qC, Quaternion.re_add, Quaternion.imI_add]

@[simp] lemma qP_add (q q' : Quaternion ℝ) : qP (q + q') = qP q + qP q' := by
  apply Complex.ext <;> simp [qP, Quaternion.imJ_add, Quaternion.imK_add]

@[simp] lemma qC_smul (r : ℝ) (q : Quaternion ℝ) : qC (r • q) = r • qC q := by
  apply Complex.ext <;> simp [qC, Quaternion.re_smul, Quaternion.imI_smul]

@[simp] lemma qP_smul (r : ℝ) (q : Quaternion ℝ) : qP (r • q) = r • qP q := by
  apply Complex.ext <;> simp [qP, Quaternion.imJ_smul, Quaternion.imK_smul]

@[simp] lemma I_sq : Complex.I ^ 2 = (-1 : ℂ) := by
  rw [pow_two, Complex.I_mul_I]

@[simp] lemma starC_re (z : ℂ) : (star z).re = z.re := Complex.conj_re z

@[simp] lemma starC_im (z : ℂ) : (star z).im = -z.im := Complex.conj_im z

lemma star_real_smul (r : ℝ) (z : ℂ) : star (r • z) = r • star z := by
  apply Complex.ext <;> simp [Complex.conj_re, Complex.conj_im, Complex.smul_re, Complex.smul_im]

/-- **The quaternionic multiplication in `ℂj`-coordinates**: `(q q')_ℂ = q_ℂ q'_ℂ - q_P conj(q'_P)`. -/
lemma qC_mul (q q' : Quaternion ℝ) :
    qC (q * q') = qC q * qC q' - qP q * star (qP q') := by
  apply Complex.ext <;>
    simp only [qC, qP, Quaternion.re_mul, Quaternion.imI_mul, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, starC_re, starC_im,
      Complex.neg_re, Complex.neg_im]
  · ring
  · ring

/-- **The quaternionic multiplication in `ℂj`-coordinates**: `(q q')_j = q_ℂ q'_j + q_P conj(q'_ℂ)`. -/
lemma qP_mul (q q' : Quaternion ℝ) :
    qP (q * q') = qC q * qP q' + qP q * star (qC q') := by
  apply Complex.ext <;>
    simp only [qC, qP, Quaternion.imJ_mul, Quaternion.imK_mul, Complex.mul_re, Complex.mul_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, starC_re, starC_im,
      Complex.neg_re, Complex.neg_im]
  · ring
  · ring

/-- The raw matrix formula, as a function `ℂ² → (Fin 2 → ℂ)`. -/
def Mfun (q : Quaternion ℝ) (v : EuclideanSpace ℂ (Fin 2)) : Fin 2 → ℂ :=
  ![qC q * v.ofLp 0 - qP q * v.ofLp 1,
    star (qP q) * v.ofLp 0 + star (qC q) * v.ofLp 1]

lemma Mfun_add (q : Quaternion ℝ) (v w : EuclideanSpace ℂ (Fin 2)) :
    Mfun q (v + w) = Mfun q v + Mfun q w := by
  funext i
  fin_cases i <;> simp [Mfun, mul_add, add_mul] <;> ring

lemma Mfun_smul (q : Quaternion ℝ) (c : ℂ) (v : EuclideanSpace ℂ (Fin 2)) :
    Mfun q (c • v) = c • Mfun q v := by
  funext i
  fin_cases i <;> simp [Mfun] <;> ring

lemma Mfun_add_param (q q' : Quaternion ℝ) (v : EuclideanSpace ℂ (Fin 2)) :
    Mfun (q + q') v = Mfun q v + Mfun q' v := by
  funext i
  fin_cases i <;> simp [Mfun] <;> ring

lemma Mfun_smul_param (r : ℝ) (q : Quaternion ℝ) (v : EuclideanSpace ℂ (Fin 2)) :
    Mfun (r • q) v = r • Mfun q v := by
  funext i
  fin_cases i <;> simp [Mfun] <;> ring

/-- The `ℂ`-linear endomorphism of `ℂ²` with matrix `[[q_ℂ, -q_P], [conj q_P, conj q_ℂ]]`. -/
def Mmat (q : Quaternion ℝ) : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (Mfun q v)
      map_add' := by
        intro v w
        rw [Mfun_add, WithLp.toLp_add]
      map_smul' := by
        intro c v
        rw [Mfun_smul, WithLp.toLp_smul, RingHom.id_apply] }

@[simp] lemma Mmat_ofLp (q : Quaternion ℝ) (v : EuclideanSpace ℂ (Fin 2)) :
    (Mmat q v).ofLp = Mfun q v := by
  simp [Mmat]

@[simp] lemma Mmat_apply_zero (q : Quaternion ℝ) (v : EuclideanSpace ℂ (Fin 2)) :
    (Mmat q v).ofLp 0 = qC q * v.ofLp 0 - qP q * v.ofLp 1 := by
  rw [Mmat_ofLp]; simp [Mfun]

@[simp] lemma Mmat_apply_one (q : Quaternion ℝ) (v : EuclideanSpace ℂ (Fin 2)) :
    (Mmat q v).ofLp 1 = star (qP q) * v.ofLp 0 + star (qC q) * v.ofLp 1 := by
  rw [Mmat_ofLp]; simp [Mfun]

lemma Mmat_ext {f g : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)}
    (h0 : ∀ v, (f v).ofLp 0 = (g v).ofLp 0) (h1 : ∀ v, (f v).ofLp 1 = (g v).ofLp 1) : f = g := by
  apply ContinuousLinearMap.ext
  intro v
  apply WithLp.ofLp_injective
  funext i
  fin_cases i
  · exact h0 v
  · exact h1 v

@[simp] lemma Mmat_one : Mmat (1 : Quaternion ℝ) = 1 := by
  refine Mmat_ext (fun v => ?_) (fun v => ?_) <;> simp [Mmat_apply_zero]

lemma Mmat_mul (q q' : Quaternion ℝ) : (Mmat q).comp (Mmat q') = Mmat (q * q') := by
  refine Mmat_ext (fun v => ?_) (fun v => ?_)
  · simp only [ContinuousLinearMap.comp_apply, Mmat_apply_zero, Mmat_apply_one, qC_mul, qP_mul,
      star_mul, star_add, star_sub, star_star]
    ring
  · simp only [ContinuousLinearMap.comp_apply, Mmat_apply_one, Mmat_apply_zero, Mmat_apply_one,
      Mmat_apply_one, qC_mul, qP_mul, star_mul, star_add, star_sub, star_star]
    ring

lemma Mmat_add (q q' : Quaternion ℝ) : Mmat (q + q') = Mmat q + Mmat q' := by
  refine Mmat_ext (fun v => ?_) (fun v => ?_)
  · rw [ContinuousLinearMap.add_apply, WithLp.ofLp_add, Pi.add_apply, Mmat_apply_zero,
      Mmat_apply_zero, Mmat_apply_zero, qC_add, qP_add]
    ring
  · rw [ContinuousLinearMap.add_apply, WithLp.ofLp_add, Pi.add_apply, Mmat_apply_one,
      Mmat_apply_one, Mmat_apply_one, qP_add, qC_add, star_add, star_add]
    ring

lemma Mmat_smul (r : ℝ) (q : Quaternion ℝ) : Mmat (r • q) = r • Mmat q := by
  refine Mmat_ext (fun v => ?_) (fun v => ?_)
  · rw [ContinuousLinearMap.smul_apply, WithLp.ofLp_smul, Pi.smul_apply, Mmat_apply_zero,
      Mmat_apply_zero, qC_smul, qP_smul]
    simp only [Complex.real_smul]
    ring
  · rw [ContinuousLinearMap.smul_apply, WithLp.ofLp_smul, Pi.smul_apply, Mmat_apply_one,
      Mmat_apply_one, qP_smul, qC_smul, star_real_smul, star_real_smul]
    simp only [Complex.real_smul]
    ring

/-- `Mmat` depends `ℝ`-linearly on the quaternion. -/
def Mlin : Quaternion ℝ →ₗ[ℝ]
    (EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2)) where
  toFun := Mmat
  map_add' := Mmat_add
  map_smul' := Mmat_smul

lemma continuous_Mmat : Continuous Mmat := Mlin.continuous_of_finiteDimensional

/-! ## §2. The complex line bundle `V_a` -/

/-- The four transition functions of `V_a` over the two-chart cover of `S⁴`. -/
def cLineCT (a : ℤ) (i j : Bool) (p : S4) :
    EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  match i, j with
  | false, false => 1
  | false, true => Mmat (uDir p ^ a)
  | true, false => Mmat (uDir p ^ (-a))
  | true, true => 1

lemma cLineCT_false_true (a : ℤ) (p : S4) : cLineCT a false true p = Mmat (uDir p ^ a) := rfl
lemma cLineCT_true_false (a : ℤ) (p : S4) : cLineCT a true false p = Mmat (uDir p ^ (-a)) := rfl
lemma cLineCT_self (a : ℤ) (i : Bool) (p : S4) : cLineCT a i i p = 1 := by cases i <;> rfl

/-- **The rank-`2` complex vector bundle `V_a` over `S⁴`**, in the two-chart description: trivial
over the two hemispheres with clutching `M_{uDir p ^ a}` on the overlap.  As a real bundle it is
Milnor's quaternionic line bundle `L^a R^0 = clutchBundle a 0`. -/
def cLine (a : ℤ) : VectorBundleCore ℂ S4 (EuclideanSpace ℂ (Fin 2)) Bool where
  baseSet i := if i then hemi1 else hemi0
  isOpen_baseSet i := by cases i <;> simp [isOpen_hemi0, isOpen_hemi1]
  indexAt p := if p = OnePoint.infty then true else false
  mem_baseSet_at p := by
    by_cases hp : p = OnePoint.infty
    · rw [hp]; simp [hemi1]
    · simp [hemi0, hp]
  coordChange i j p := cLineCT a i j p
  coordChange_self i p hp v := by rw [cLineCT_self]; rfl
  continuousOn_coordChange i j := by
    cases i <;> cases j
    · exact continuousOn_const
    · exact continuous_Mmat.comp_continuousOn
        (continuousOn_uDir.zpow₀ a (fun p _ => Or.inl (uDir_ne_zero p)))
    · change ContinuousOn (fun p : S4 => Mmat (uDir p ^ ((-a : ℤ)))) (hemi1 ∩ hemi0)
      exact continuous_Mmat.comp_continuousOn
        ((continuousOn_uDir.mono (le_of_eq (Set.inter_comm hemi0 hemi1).symm)).zpow₀ (-a)
          (fun p _ => Or.inl (uDir_ne_zero p)))
    · exact continuousOn_const
  coordChange_comp i j l p hp v := by
    have hq : uDir p ≠ 0 := uDir_ne_zero p
    have h1 : ∀ w, cLineCT a true false p (cLineCT a false true p w) = w := by
      intro w
      rw [cLineCT_true_false, cLineCT_false_true, ← ContinuousLinearMap.comp_apply, Mmat_mul,
        show uDir p ^ (-a) * uDir p ^ a = 1 from by
          rw [← zpow_add₀ hq, neg_add_cancel, zpow_zero]]
      simp
    have h2 : ∀ w, cLineCT a false true p (cLineCT a true false p w) = w := by
      intro w
      rw [cLineCT_true_false, cLineCT_false_true, ← ContinuousLinearMap.comp_apply, Mmat_mul,
        show uDir p ^ a * uDir p ^ (-a) = 1 from by
          rw [← zpow_add₀ hq, add_neg_cancel, zpow_zero]]
      simp
    cases i <;> cases j <;> cases l <;> first | rfl | exact h1 v | exact h2 v

@[simp] lemma cLine_baseSet (a : ℤ) (i : Bool) :
    (cLine a).baseSet i = if i then hemi1 else hemi0 := rfl

@[simp] lemma cLine_coordChange (a : ℤ) (i j : Bool) (p : S4) :
    (cLine a).coordChange i j p = cLineCT a i j p := rfl

/-! ## §3. Comparison with `L^a R^0`: the real-linear isomorphism `ℂ² ≅ ℍ` -/

/-- The real-linear map `ℂ² → ℍ = ℝ⁴`, `(z₀, z₁) ↦ z₀ + conj(z₁) j`, i.e. in coordinates
`(Re z₀, Im z₀, Re z₁, - Im z₁)`. -/
def eFlat : EuclideanSpace ℂ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 4) where
  toFun z := WithLp.toLp 2 ![(z.ofLp 0).re, (z.ofLp 0).im, (z.ofLp 1).re, -(z.ofLp 1).im]
  map_add' z z' := by
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;> simp [Complex.add_re, Complex.add_im] <;> ring
  map_smul' r z := by
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;> simp [Complex.smul_re, Complex.smul_im] <;> ring

/-- The inverse of `Work.Agree.eFlat`: `x ↦ (x₀ + i x₁, x₂ - i x₃)`. -/
def eFlatInv : EuclideanSpace ℝ (Fin 4) →ₗ[ℝ] EuclideanSpace ℂ (Fin 2) where
  toFun x := WithLp.toLp 2 ![Complex.mk (x.ofLp 0) (x.ofLp 1), Complex.mk (x.ofLp 2) (-(x.ofLp 3))]
  map_add' x y := by
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;> apply Complex.ext <;> simp <;> ring
  map_smul' r x := by
    apply WithLp.ofLp_injective
    funext i
    fin_cases i <;> apply Complex.ext <;> simp <;> ring

lemma eFlat_inv_left (z : EuclideanSpace ℂ (Fin 2)) : eFlatInv (eFlat z) = z := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;> apply Complex.ext <;> simp [eFlat, eFlatInv]

lemma eFlat_inv_right (x : EuclideanSpace ℝ (Fin 4)) : eFlat (eFlatInv x) = x := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;> simp [eFlat, eFlatInv]

/-- **The real-linear isomorphism `ℂ² ≅ ℍ`.** -/
noncomputable def eFlatEquiv : EuclideanSpace ℂ (Fin 2) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 4) :=
  { toFun := eFlat
    invFun := eFlatInv
    map_add' := eFlat.map_add
    map_smul' := eFlat.map_smul
    left_inv := eFlat_inv_left
    right_inv := eFlat_inv_right }

/-- **The gauge**: the continuous `ℝ`-linear isomorphism `ℂ² ≅ ℍ`. -/
noncomputable def eFlatLin : EuclideanSpace ℂ (Fin 2) ≃L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  eFlatEquiv.toContinuousLinearEquiv

@[simp] lemma eFlatLin_apply (z : EuclideanSpace ℂ (Fin 2)) : eFlatLin z = eFlat z := rfl

@[simp] lemma eFlat_apply (z : EuclideanSpace ℂ (Fin 2)) :
    eFlat z = WithLp.toLp 2 ![(z.ofLp 0).re, (z.ofLp 0).im, (z.ofLp 1).re, -(z.ofLp 1).im] := rfl

/-- `leftMult` in coordinates: `qTwist 1 0 m` is left multiplication by `m`. -/
@[simp] lemma qTwist_one_zero_apply (m : Quaternion ℝ) (v : EuclideanSpace ℝ (Fin 4)) :
    qTwist 1 0 m v = ofQ (m * toQ v) := by
  simp [qTwist_apply]

lemma qTwist_eq (a : ℤ) (q : Quaternion ℝ) : qTwist a 0 q = qTwist 1 0 (q ^ a) := by
  ext v
  simp [qTwist_apply]

@[simp] lemma toQ_re (v : EuclideanSpace ℝ (Fin 4)) : (toQ v).re = v.ofLp 0 := rfl
@[simp] lemma toQ_imI (v : EuclideanSpace ℝ (Fin 4)) : (toQ v).imI = v.ofLp 1 := rfl
@[simp] lemma toQ_imJ (v : EuclideanSpace ℝ (Fin 4)) : (toQ v).imJ = v.ofLp 2 := rfl
@[simp] lemma toQ_imK (v : EuclideanSpace ℝ (Fin 4)) : (toQ v).imK = v.ofLp 3 := rfl
@[simp] lemma ofQ_re (q : Quaternion ℝ) : (ofQ q).ofLp 0 = q.re := rfl
@[simp] lemma ofQ_imI (q : Quaternion ℝ) : (ofQ q).ofLp 1 = q.imI := rfl
@[simp] lemma ofQ_imJ (q : Quaternion ℝ) : (ofQ q).ofLp 2 = q.imJ := rfl
@[simp] lemma ofQ_imK (q : Quaternion ℝ) : (ofQ q).ofLp 3 = q.imK := rfl

/-- **The key computation of the comparison `ℂ² ≅ ℍ`**: the transition `Mmat m` of `V_a` is the
restriction of left multiplication by `m` along the real-linear gauge `eFlat`. -/
lemma qTwist_comp_eFlat (m : Quaternion ℝ) :
    (qTwist 1 0 m).comp (eFlatLin : EuclideanSpace ℂ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 4))
      = (eFlatLin : EuclideanSpace ℂ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 4)).comp
        ((Mmat m).restrictScalars ℝ) := by
  apply ContinuousLinearMap.ext
  intro z
  change qTwist 1 0 m (eFlat z) = eFlat (Mmat m z)
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    simp [eFlat, qTwist_one_zero_apply, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
      Quaternion.imK_mul, qC, qP, Complex.mul_re, Complex.mul_im, starC_re, starC_im] <;>
    ring

/-- The pointwise form of `qTwist_comp_eFlat`. -/
lemma qTwist_eFlat (m : Quaternion ℝ) (z : EuclideanSpace ℂ (Fin 2)) :
    qTwist 1 0 m (eFlat z) = eFlat (Mmat m z) := by
  have h := congrArg (fun f : EuclideanSpace ℂ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 4) => f z)
    (qTwist_comp_eFlat m)
  simpa using h

/-- The index maps of `clutchBundle a 0` and of `cLine a` agree. -/
lemma cLine_indexAt_eq (a : ℤ) (p : S4) :
    (cLine a).indexAt p = (clutchBundle a 0).indexAt p := rfl

/-- **The conjugation identity** of the gauge `eFlatLin` with the transitions. -/
lemma eFlat_conj (a : ℤ) (i : Bool) (p : S4) :
    ((clutchBundle a 0).coordChange ((clutchBundle a 0).indexAt p) i p).comp
        (eFlatLin : EuclideanSpace ℂ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 4))
      = (eFlatLin : EuclideanSpace ℂ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 4)).comp
        ((Work.Thom.realification (cLine a)).coordChange
          ((Work.Thom.realification (cLine a)).indexAt p) i p) := by
  have hidx : (Work.Thom.realification (cLine a)).indexAt p = (clutchBundle a 0).indexAt p :=
    (congrFun (Work.Thom.realification_indexAt (cLine a)) p).trans (cLine_indexAt_eq a p).symm
  rw [hidx]
  generalize hk : (clutchBundle a 0).indexAt p = k
  cases k <;> cases i
  all_goals
    apply ContinuousLinearMap.ext
    intro z
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    simp only [clutchBundle_coordChange, cLine_coordChange, Work.Thom.realification_coordChange,
      cLineCT_false_true, cLineCT_true_false, cLineCT_self, ct_false_true, ct_true_false,
      ct_self, neg_zero, one_apply_eq_self, eFlatLin_apply] <;>
      first
        | rfl
        | (rw [qTwist_eq]; exact qTwist_eFlat _ z)

/-- **The realification of `V_a` is Milnor's quaternionic line bundle `L^a R^0`.** -/
theorem realification_cLine_iso_clutchBundle (a : ℤ) :
    Nonempty (Work.Thom.BundleIso (Work.Thom.realification (cLine a)) (clutchBundle a 0)) := by
  refine Work.Whitney.nonempty_bundleIso_of_gauge_fibre (Work.Thom.realification (cLine a))
    (clutchBundle a 0) eFlatLin (Equiv.refl Bool) ?_ ?_ ?_
  · intro i
    change (clutchBundle a 0).baseSet i = (Work.Thom.realification (cLine a)).baseSet i
    rw [Work.Thom.realification_baseSet, clutchBundle_baseSet, cLine_baseSet]
  · intro p
    change (clutchBundle a 0).indexAt p = (Work.Thom.realification (cLine a)).indexAt p
    rw [Work.Thom.realification_indexAt, cLine_indexAt_eq]
  · intro i p
    rw [Equiv.refl_apply]
    exact eFlat_conj a i p


end

end Work.Agree

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-! ## §4. The splitting `ℂ ⊗_ℝ ℍ ≅ ℂ² ⊕ ℂ²` -/

/-- The `+i`-eigenprojection of `J = id_ℂ ⊗ R_i` on `ℂ ⊗_ℝ ℍ = ℂ⁴`. -/
def Pplus : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2
        ![(w.ofLp 0 + Complex.I * w.ofLp 1) / 2, (w.ofLp 2 - Complex.I * w.ofLp 3) / 2]
      map_add' := by
        intro v w
        apply WithLp.ofLp_injective
        funext i
        fin_cases i <;> simp [add_mul, mul_add] <;> ring
      map_smul' := by
        intro c v
        apply WithLp.ofLp_injective
        funext i
        fin_cases i <;> simp [mul_assoc, mul_left_comm, mul_comm] <;> ring }

/-- The `-i`-eigenprojection of `J = id_ℂ ⊗ R_i` on `ℂ ⊗_ℝ ℍ = ℂ⁴`. -/
def Pminus : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun w => WithLp.toLp 2
        ![(w.ofLp 0 - Complex.I * w.ofLp 1) / 2, (w.ofLp 2 + Complex.I * w.ofLp 3) / 2]
      map_add' := by
        intro v w
        apply WithLp.ofLp_injective
        funext i
        fin_cases i <;> simp [add_mul, mul_add] <;> ring
      map_smul' := by
        intro c v
        apply WithLp.ofLp_injective
        funext i
        fin_cases i <;> simp [mul_assoc, mul_left_comm, mul_comm] <;> ring }

/-- The multiplication by `j` on `ℂ²`, `(z₀,z₁) ↦ (-z₁,z₀)`. -/
def gg : EuclideanSpace ℂ (Fin 2) →L[ℂ] EuclideanSpace ℂ (Fin 2) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 ![- z.ofLp 1, z.ofLp 0]
      map_add' := by
        intro v w
        apply WithLp.ofLp_injective
        funext i
        fin_cases i <;> simp <;> ring
      map_smul' := by
        intro c v
        apply WithLp.ofLp_injective
        funext i
        fin_cases i <;> simp [mul_comm] }

@[simp] lemma Pplus_apply_zero (w : EuclideanSpace ℂ (Fin 4)) :
    (Pplus w).ofLp 0 = (w.ofLp 0 + Complex.I * w.ofLp 1) / 2 := by
  simp [Pplus]

@[simp] lemma Pplus_apply_one (w : EuclideanSpace ℂ (Fin 4)) :
    (Pplus w).ofLp 1 = (w.ofLp 2 - Complex.I * w.ofLp 3) / 2 := by
  simp [Pplus]

@[simp] lemma Pminus_apply_zero (w : EuclideanSpace ℂ (Fin 4)) :
    (Pminus w).ofLp 0 = (w.ofLp 0 - Complex.I * w.ofLp 1) / 2 := by
  simp [Pminus]

@[simp] lemma Pminus_apply_one (w : EuclideanSpace ℂ (Fin 4)) :
    (Pminus w).ofLp 1 = (w.ofLp 2 + Complex.I * w.ofLp 3) / 2 := by
  simp [Pminus]

@[simp] lemma gg_apply_zero (z : EuclideanSpace ℂ (Fin 2)) :
    (gg z).ofLp 0 = - z.ofLp 1 := by
  simp [gg]

@[simp] lemma gg_apply_one (z : EuclideanSpace ℂ (Fin 2)) :
    (gg z).ofLp 1 = z.ofLp 0 := by
  simp [gg]

/-- The inverse of `(P₊, g ∘ P₋)`, in coordinates. -/
def Ginv : (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)) →L[ℂ]
    EuclideanSpace ℂ (Fin 4) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => WithLp.toLp 2
        ![u.1.ofLp 0 + u.2.ofLp 1, - Complex.I * (u.1.ofLp 0 - u.2.ofLp 1),
          u.1.ofLp 1 - u.2.ofLp 0, Complex.I * (u.1.ofLp 1 + u.2.ofLp 0)]
      map_add' := by
        intro v w
        apply WithLp.ofLp_injective
        funext i
        fin_cases i <;> simp [add_mul, mul_add, Prod.fst_add, Prod.snd_add] <;> ring
      map_smul' := by
        intro c v
        apply WithLp.ofLp_injective
        funext i
        fin_cases i <;> simp [mul_assoc, mul_left_comm, mul_comm] <;> ring }

@[simp] lemma Ginv_apply (u : EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)) :
    Ginv u = WithLp.toLp 2
      ![u.1.ofLp 0 + u.2.ofLp 1, - Complex.I * (u.1.ofLp 0 - u.2.ofLp 1),
        u.1.ofLp 1 - u.2.ofLp 0, Complex.I * (u.1.ofLp 1 + u.2.ofLp 0)] := by
  simp [Ginv]

lemma Ginv_Ppair (w : EuclideanSpace ℂ (Fin 4)) :
    Ginv (Pplus w, gg (Pminus w)) = w := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.div_re, Complex.div_im,
        Complex.I_re, Complex.I_im] <;> ring

lemma Ppair_Ginv (u : EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)) :
    (Pplus (Ginv u), gg (Pminus (Ginv u))) = u := by
  apply Prod.ext <;> (apply WithLp.ofLp_injective; funext i; fin_cases i <;>
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.sub_re,
        Complex.sub_im, Complex.neg_re, Complex.neg_im, Complex.div_re, Complex.div_im,
        Complex.I_re, Complex.I_im] <;> ring)

/-- **The gauge of the splitting**: the `ℂ`-linear isomorphism `ℂ ⊗_ℝ ℍ ≅ ℂ² ⊕ ℂ²` given by the
eigenprojections of `J = id_ℂ ⊗ R_i` (the second block conjugated by the multiplication by `j`). -/
noncomputable def eGaugeEquiv :
    EuclideanSpace ℂ (Fin 4) ≃ₗ[ℂ]
      (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)) where
  toFun w := (Pplus w, gg (Pminus w))
  invFun u := Ginv u
  map_add' v w := by
    apply Prod.ext <;> simp [map_add]
  map_smul' c v := by
    apply Prod.ext <;> simp [map_smul]
  left_inv w := Ginv_Ppair w
  right_inv u := Ppair_Ginv u

/-- The gauge, as a continuous linear equivalence into the standard fibre of the Whitney sum. -/
noncomputable def eGauge :
    EuclideanSpace ℂ (Fin 4) ≃L[ℂ] EuclideanSpace ℂ (Fin (2 + 2)) :=
  (LinearEquiv.toContinuousLinearEquiv eGaugeEquiv).trans (Whitney.sumFibreC 2 2)

@[simp] lemma eGauge_apply (w : EuclideanSpace ℂ (Fin 4)) :
    eGauge w = Whitney.sumFibreC 2 2 (Pplus w, gg (Pminus w)) := by
  simp [eGauge, eGaugeEquiv]

/-- The diagonal action of `Mmat m` on the sum `ℂ² ⊕ ℂ²`. -/
noncomputable def pairM (m : Quaternion ℝ) :
    (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)) →L[ℂ]
      (EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u => (Mmat m u.1, Mmat m u.2)
      map_add' := fun u v => by ext <;> simp [map_add]
      map_smul' := fun c u => by ext <;> simp [map_smul] }

@[simp] lemma pairM_apply (m : Quaternion ℝ)
    (u : EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)) :
    pairM m u = (Mmat m u.1, Mmat m u.2) := by
  simp [pairM]

/-- The diagonal action of `Mmat m` on the standard fibre `ℂ^{2+2}` of the Whitney sum. -/
noncomputable def diagM (m : Quaternion ℝ) :
    EuclideanSpace ℂ (Fin (2 + 2)) →L[ℂ] EuclideanSpace ℂ (Fin (2 + 2)) :=
  (Whitney.sumFibreC 2 2).toContinuousLinearMap.comp
    ((pairM m).comp ((Whitney.sumFibreC 2 2).symm).toContinuousLinearMap)

lemma diagM_apply (m : Quaternion ℝ)
    (u : EuclideanSpace ℂ (Fin 2) × EuclideanSpace ℂ (Fin 2)) :
    diagM m (Whitney.sumFibreC 2 2 u) = Whitney.sumFibreC 2 2 (Mmat m u.1, Mmat m u.2) := by
  simp [diagM]



/-! ## §5. The splitting identity -/

@[simp] lemma cxOfReal_ofQ_apply_zero (q : Quaternion ℝ) :
    (Work.Thom.cxOfReal (ofQ q)).ofLp 0 = (q.re : ℂ) := by
  simp [Work.Thom.cxOfReal]

@[simp] lemma cxOfReal_ofQ_apply_one (q : Quaternion ℝ) :
    (Work.Thom.cxOfReal (ofQ q)).ofLp 1 = (q.imI : ℂ) := by
  simp [Work.Thom.cxOfReal]

@[simp] lemma cxOfReal_ofQ_apply_two (q : Quaternion ℝ) :
    (Work.Thom.cxOfReal (ofQ q)).ofLp 2 = (q.imJ : ℂ) := by
  simp [Work.Thom.cxOfReal]

@[simp] lemma cxOfReal_ofQ_apply_three (q : Quaternion ℝ) :
    (Work.Thom.cxOfReal (ofQ q)).ofLp 3 = (q.imK : ℂ) := by
  simp [Work.Thom.cxOfReal]

lemma Pplus_cxOfReal_ofQ (q : Quaternion ℝ) :
    Pplus (Work.Thom.cxOfReal (ofQ q)) = WithLp.toLp 2 ![qC q / 2, star (qP q) / 2] := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    (apply Complex.ext <;>
      simp [qC, qP, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im, Complex.conj_re,
        Complex.conj_im] <;> ring)

lemma Pminus_cxOfReal_ofQ (q : Quaternion ℝ) :
    Pminus (Work.Thom.cxOfReal (ofQ q)) = WithLp.toLp 2 ![star (qC q) / 2, qP q / 2] := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;>
    (apply Complex.ext <;>
      simp [qC, qP, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im, Complex.conj_re,
        Complex.conj_im] <;> ring)

lemma gg_pair (a b : ℂ) : gg (WithLp.toLp 2 ![a, b]) = WithLp.toLp 2 ![-b, a] := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;> simp [gg]

/-- **The splitting identity, pointwise.**  The complexified transition of `L^a R^0` acts on the
two eigenbundles of `J = id_ℂ ⊗ R_i` by the same matrix `Mmat m`. -/
lemma key_point (m : Quaternion ℝ) (w : EuclideanSpace ℂ (Fin 4)) :
    (Pplus (Work.Thom.cxTrans (qTwist 1 0 m) w),
        gg (Pminus (Work.Thom.cxTrans (qTwist 1 0 m) w)))
      = (Mmat m (Pplus w), Mmat m (gg (Pminus w))) := by
  apply Prod.ext <;>
    · apply WithLp.ofLp_injective
      funext i
      fin_cases i <;>
        · apply Complex.ext <;>
            simp [Work.Thom.cxTrans_apply, Work.Thom.cxOfReal, Work.Thom.cxMulI,
              Work.Thom.cxRePart, Work.Thom.cxImPart, qC, qP, Mmat_apply_zero, Mmat_apply_one,
              Pplus_apply_zero, Pplus_apply_one, Pminus_apply_zero, Pminus_apply_one,
              gg_apply_zero, gg_apply_one, qTwist_apply, ofQ_re, ofQ_imI, ofQ_imJ, ofQ_imK,
              toQ_re, toQ_imI, toQ_imJ, toQ_imK, Quaternion.re_mul, Quaternion.imI_mul,
              Quaternion.imJ_mul, Quaternion.imK_mul, Complex.add_re, Complex.add_im,
              Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.neg_re,
              Complex.neg_im, Complex.div_re, Complex.div_im, Complex.I_re, Complex.I_im,
              Complex.conj_re, Complex.conj_im] <;>
            ring

/-- **The splitting identity, as an identity of transition functions.** -/
lemma Ppair_key (m : Quaternion ℝ) :
    (Pplus.prod (gg.comp Pminus)).comp (Work.Thom.cxTrans (qTwist 1 0 m))
      = (pairM m).comp (Pplus.prod (gg.comp Pminus)) := by
  apply ContinuousLinearMap.ext
  intro w
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.prod_apply, pairM_apply]
  exact key_point m w

/-- **The splitting identity**: the complexification of `L^a R^0` splits as `V_a ⊕ V_a`. -/
lemma key (m : Quaternion ℝ) :
    (eGauge : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin (2 + 2))).comp
        (Work.Thom.cxTrans (qTwist 1 0 m))
      = (diagM m).comp
        (eGauge : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin (2 + 2))) := by
  have h := Ppair_key m
  apply ContinuousLinearMap.ext
  intro w
  have hw : (Pplus (Work.Thom.cxTrans (qTwist 1 0 m) w),
        gg (Pminus (Work.Thom.cxTrans (qTwist 1 0 m) w)))
      = (Mmat m (Pplus w), Mmat m (gg (Pminus w))) :=
    congrFun (congrArg DFunLike.coe h) w
  change Whitney.sumFibreC 2 2 (Pplus ((Work.Thom.cxTrans (qTwist 1 0 m)) w),
        gg (Pminus ((Work.Thom.cxTrans (qTwist 1 0 m)) w)))
      = diagM m (Whitney.sumFibreC 2 2 (Pplus w, gg (Pminus w)))
  rw [hw, diagM_apply]


lemma pairM_eq_prodMap (m : Quaternion ℝ) : pairM m = (Mmat m).prodMap (Mmat m) := by
  apply ContinuousLinearMap.ext
  rintro ⟨u, v⟩
  simp [pairM_apply]

/-- The quaternion attached to the pair of chart indices `(k, i)` at the point `p`: the matrix `M`
of the corresponding transition. -/
def clutchQuat (a : ℤ) (k i : Bool) (p : S4) : Quaternion ℝ :=
  if k = i then 1 else if k then uDir p ^ (-a) else uDir p ^ a

@[simp] lemma qTwist_one_zero_one : qTwist 1 0 (1 : Quaternion ℝ) = 1 := by
  ext v
  simp [qTwist_one_zero_apply]

@[simp] lemma quat_one_zpow_one : (1 : Quaternion ℝ) ^ (1 : ℤ) = 1 := by simp

@[simp] lemma quat_one_zpow_zero : (1 : Quaternion ℝ) ^ (0 : ℤ) = 1 := by simp

lemma diagM_transition (a : ℤ) (k i : Bool) (p : S4) :
    (Whitney.whitneySum (cLine a) (cLine a)).coordChange (k, k) (i, i) p
      = diagM (clutchQuat a k i p) := by
  cases k <;> cases i <;>
    simp [clutchQuat, diagM, pairM_eq_prodMap, Whitney.whitneySum_coordChange,
      cLine_coordChange, cLineCT_self, cLineCT_false_true, cLineCT_true_false]

lemma cxTrans_transition (a : ℤ) (k i : Bool) (p : S4) :
    (Work.Thom.complexificationCore (clutchBundle a 0)).coordChange k i p
      = Work.Thom.cxTrans (qTwist 1 0 (clutchQuat a k i p)) := by
  rw [show (Work.Thom.complexificationCore (clutchBundle a 0)).coordChange k i p
      = Work.Thom.cxTrans ((clutchBundle a 0).coordChange k i p) from rfl]
  congr 1
  cases k <;> cases i
  · rw [clutchBundle_coordChange, ct_self, show clutchQuat a false false p = 1 from rfl,
      qTwist_one_zero_one]
  · rw [clutchBundle_coordChange, ct_false_true, qTwist_eq,
      show clutchQuat a false true p = uDir p ^ a from rfl]
  · rw [clutchBundle_coordChange, ct_true_false, neg_zero, qTwist_eq,
      show clutchQuat a true false p = uDir p ^ (-a) from rfl]
  · rw [clutchBundle_coordChange, ct_self, show clutchQuat a true true p = 1 from rfl,
      qTwist_one_zero_one]


end

end Work.Agree

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-! ## §6. The splitting isomorphism -/

local notation "Xc" => Work.Thom.complexificationCore (clutchBundle 0 0)

/-- The conjugation identity between the transitions of the two presentations. -/
lemma Ycomp_X (a : ℤ) (k i : Bool) (p : S4) :
    ((Whitney.whitneySum (cLine a) (cLine a)).coordChange (k, k) (i, i) p).comp
        (eGauge : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin (2 + 2)))
      = (eGauge : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin (2 + 2))).comp
        ((Work.Thom.complexificationCore (clutchBundle a 0)).coordChange k i p) := by
  rw [diagM_transition a k i p, cxTrans_transition a k i p]
  exact (key (clutchQuat a k i p)).symm

/-- The chart-wise matrix of the identity `ℂ ⊗_ℝ L^a R^0 ≅ V_a ⊕ V_a`. -/
noncomputable def splitGauge (a : ℤ) (i : Bool) (t : Bool × Bool) (b : S4) :
    EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin (2 + 2)) :=
  ((Whitney.whitneySum (cLine a) (cLine a)).coordChange
      ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) t b).comp
    ((eGauge : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin (2 + 2))).comp
      ((Work.Thom.complexificationCore (clutchBundle a 0)).coordChange i
        ((clutchBundle a 0).indexAt b) b))

/-- The chart-wise matrix of the inverse. -/
noncomputable def splitGaugeInv (a : ℤ) (i : Bool) (t : Bool × Bool) (b : S4) :
    EuclideanSpace ℂ (Fin (2 + 2)) →L[ℂ] EuclideanSpace ℂ (Fin 4) :=
  ((Work.Thom.complexificationCore (clutchBundle a 0)).coordChange
      ((clutchBundle a 0).indexAt b) i b).comp
    (((eGauge : EuclideanSpace ℂ (Fin 4) ≃L[ℂ] EuclideanSpace ℂ (Fin (2 + 2))).symm :
        EuclideanSpace ℂ (Fin (2 + 2)) →L[ℂ] EuclideanSpace ℂ (Fin 4)).comp
      ((Whitney.whitneySum (cLine a) (cLine a)).coordChange t
        ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) b))

lemma Ybase_eq (a : ℤ) (i : Bool) :
    (Whitney.whitneySum (cLine a) (cLine a)).baseSet (i, i)
      = (Work.Thom.complexificationCore (clutchBundle a 0)).baseSet i := by
  change (cLine a).baseSet i ∩ (cLine a).baseSet i = (clutchBundle a 0).baseSet i
  rw [Set.inter_self, cLine_baseSet, clutchBundle_baseSet]

lemma YindexAt_eq (a : ℤ) (b : S4) :
    (Whitney.whitneySum (cLine a) (cLine a)).indexAt b
      = ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) := by
  simp [Whitney.whitneySum_indexAt, cLine_indexAt_eq]

/-- The pointwise form of `Work.Agree.splitGauge` on the intersection of the two charts. -/
lemma splitGauge_eq (a : ℤ) (i : Bool) (t : Bool × Bool) (b : S4)
    (hb : b ∈ (Work.Thom.complexificationCore (clutchBundle a 0)).baseSet i ∩
      (Whitney.whitneySum (cLine a) (cLine a)).baseSet t) :
    splitGauge a i t b
      = ((Whitney.whitneySum (cLine a) (cLine a)).coordChange (i, i) t b).comp
        (eGauge : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin (2 + 2))) := by
  have hbY1 : b ∈ (Whitney.whitneySum (cLine a) (cLine a)).baseSet (i, i) := by
    rw [Ybase_eq]; exact hb.1
  have hbkY : b ∈ (Whitney.whitneySum (cLine a) (cLine a)).baseSet
      ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) := by
    rw [← YindexAt_eq]; exact (Whitney.whitneySum (cLine a) (cLine a)).mem_baseSet_at b
  have hbkX : b ∈ (Work.Thom.complexificationCore (clutchBundle a 0)).baseSet
      ((clutchBundle a 0).indexAt b) :=
    (Work.Thom.complexificationCore (clutchBundle a 0)).mem_baseSet_at b
  have hbXi : b ∈ (Work.Thom.complexificationCore (clutchBundle a 0)).baseSet i := hb.1
  have hcocY := (Whitney.whitneySum (cLine a) (cLine a)).coordChange_linear_comp
    ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) (i, i) t b
    ⟨⟨hbkY, hbY1⟩, hb.2⟩
  have hconj := Ycomp_X a ((clutchBundle a 0).indexAt b) i b
  have hcocX := (Work.Thom.complexificationCore (clutchBundle a 0)).coordChange_linear_comp
    i ((clutchBundle a 0).indexAt b) i b ⟨⟨hbXi, hbkX⟩, hbXi⟩
  have hXii : (Work.Thom.complexificationCore (clutchBundle a 0)).coordChange i i b = 1 :=
    ContinuousLinearMap.ext fun v =>
      (Work.Thom.complexificationCore (clutchBundle a 0)).coordChange_self i b hbXi v
  show ((Whitney.whitneySum (cLine a) (cLine a)).coordChange
        ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) t b).comp
      ((eGauge : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin (2 + 2))).comp
        ((Work.Thom.complexificationCore (clutchBundle a 0)).coordChange i
          ((clutchBundle a 0).indexAt b) b))
    = _
  calc ((Whitney.whitneySum (cLine a) (cLine a)).coordChange
          ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) t b).comp
        ((eGauge : _ →L[ℂ] _).comp
          ((Work.Thom.complexificationCore (clutchBundle a 0)).coordChange i
            ((clutchBundle a 0).indexAt b) b))
      = (((Whitney.whitneySum (cLine a) (cLine a)).coordChange (i, i) t b).comp
          ((Whitney.whitneySum (cLine a) (cLine a)).coordChange
            ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) (i, i) b)).comp
        ((eGauge : _ →L[ℂ] _).comp
          ((Work.Thom.complexificationCore (clutchBundle a 0)).coordChange i
            ((clutchBundle a 0).indexAt b) b)) := by rw [hcocY]
    _ = ((Whitney.whitneySum (cLine a) (cLine a)).coordChange (i, i) t b).comp
          (((Whitney.whitneySum (cLine a) (cLine a)).coordChange
            ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) (i, i) b).comp
            ((eGauge : _ →L[ℂ] _).comp
              ((Work.Thom.complexificationCore (clutchBundle a 0)).coordChange i
                ((clutchBundle a 0).indexAt b) b))) := by
          rw [ContinuousLinearMap.comp_assoc]
    _ = ((Whitney.whitneySum (cLine a) (cLine a)).coordChange (i, i) t b).comp
          ((((Whitney.whitneySum (cLine a) (cLine a)).coordChange
            ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) (i, i) b).comp
            (eGauge : _ →L[ℂ] _)).comp
            ((Work.Thom.complexificationCore (clutchBundle a 0)).coordChange i
              ((clutchBundle a 0).indexAt b) b)) := by
          rw [ContinuousLinearMap.comp_assoc]
    _ = ((Whitney.whitneySum (cLine a) (cLine a)).coordChange (i, i) t b).comp
          (((eGauge : _ →L[ℂ] _).comp
            ((Work.Thom.complexificationCore (clutchBundle a 0)).coordChange
              ((clutchBundle a 0).indexAt b) i b)).comp
            ((Work.Thom.complexificationCore (clutchBundle a 0)).coordChange i
              ((clutchBundle a 0).indexAt b) b)) := by rw [hconj]
    _ = ((Whitney.whitneySum (cLine a) (cLine a)).coordChange (i, i) t b).comp
          ((eGauge : _ →L[ℂ] _).comp
            (((Work.Thom.complexificationCore (clutchBundle a 0)).coordChange
              ((clutchBundle a 0).indexAt b) i b).comp
              ((Work.Thom.complexificationCore (clutchBundle a 0)).coordChange i
                ((clutchBundle a 0).indexAt b) b))) := by
          rw [ContinuousLinearMap.comp_assoc]
    _ = ((Whitney.whitneySum (cLine a) (cLine a)).coordChange (i, i) t b).comp
          ((eGauge : _ →L[ℂ] _).comp
            ((Work.Thom.complexificationCore (clutchBundle a 0)).coordChange i i b)) := by
          rw [hcocX]
    _ = ((Whitney.whitneySum (cLine a) (cLine a)).coordChange (i, i) t b).comp
          ((eGauge : _ →L[ℂ] _).comp 1) := by rw [hXii]
    _ = ((Whitney.whitneySum (cLine a) (cLine a)).coordChange (i, i) t b).comp
          (eGauge : _ →L[ℂ] _) := by
          rw [show (1 : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4))
              = ContinuousLinearMap.id ℂ _ from rfl, ContinuousLinearMap.comp_id]

end

end Work.Agree

namespace Work.Agree

open Work.TangentClasses

noncomputable section


lemma eGauge_symm_apply' (z : EuclideanSpace ℂ (Fin 4)) :
    ((eGauge.symm : EuclideanSpace ℂ (Fin (2 + 2)) →L[ℂ] EuclideanSpace ℂ (Fin 4)))
      ((eGauge : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin (2 + 2))) z) = z :=
  ContinuousLinearEquiv.symm_apply_apply eGauge z

lemma eGauge_apply_symm' (z : EuclideanSpace ℂ (Fin (2 + 2))) :
    ((eGauge : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin (2 + 2))))
      ((eGauge.symm : EuclideanSpace ℂ (Fin (2 + 2)) →L[ℂ] EuclideanSpace ℂ (Fin 4)) z) = z :=
  ContinuousLinearEquiv.apply_symm_apply eGauge z

/-- The pointwise form of `Work.Agree.splitGaugeInv` on the intersection of the two charts. -/
lemma splitGaugeInv_eq (a : ℤ) (i : Bool) (t : Bool × Bool) (b : S4)
    (hb : b ∈ (Work.Thom.complexificationCore (clutchBundle a 0)).baseSet i ∩
      (Whitney.whitneySum (cLine a) (cLine a)).baseSet t) :
    splitGaugeInv a i t b
      = (((eGauge : EuclideanSpace ℂ (Fin 4) ≃L[ℂ] EuclideanSpace ℂ (Fin (2 + 2))).symm :
            EuclideanSpace ℂ (Fin (2 + 2)) →L[ℂ] EuclideanSpace ℂ (Fin 4))).comp
        ((Whitney.whitneySum (cLine a) (cLine a)).coordChange t (i, i) b) := by
  have hbY1 : b ∈ (Whitney.whitneySum (cLine a) (cLine a)).baseSet (i, i) := by
    rw [Ybase_eq]; exact hb.1
  have hbkY : b ∈ (Whitney.whitneySum (cLine a) (cLine a)).baseSet
      ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) := by
    rw [← YindexAt_eq]; exact (Whitney.whitneySum (cLine a) (cLine a)).mem_baseSet_at b
  have hconj := Ycomp_X a ((clutchBundle a 0).indexAt b) i b
  have Xcc : ∀ y, (Work.Thom.complexificationCore (clutchBundle a 0)).coordChange
        ((clutchBundle a 0).indexAt b) i b y
      = ((eGauge.symm : EuclideanSpace ℂ (Fin (2 + 2)) →L[ℂ] EuclideanSpace ℂ (Fin 4)))
          (((Whitney.whitneySum (cLine a) (cLine a)).coordChange
            ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) (i, i) b)
            ((eGauge : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin (2 + 2))) y)) := by
    intro y
    have h := congrArg (fun (L : _ →L[ℂ] _) => L y) hconj
    simp only [ContinuousLinearMap.comp_apply] at h
    have h2 := congrArg
      (fun z => ((eGauge.symm : EuclideanSpace ℂ (Fin (2 + 2)) →L[ℂ]
        EuclideanSpace ℂ (Fin 4))) z) h
    rw [eGauge_symm_apply'] at h2
    exact h2.symm
  have Ycoc := (Whitney.whitneySum (cLine a) (cLine a)).coordChange_linear_comp
    t ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) (i, i) b
    ⟨⟨hb.2, hbkY⟩, hbY1⟩
  apply ContinuousLinearMap.ext
  intro x
  show (Work.Thom.complexificationCore (clutchBundle a 0)).coordChange
      ((clutchBundle a 0).indexAt b) i b
      (((eGauge.symm : EuclideanSpace ℂ (Fin (2 + 2)) →L[ℂ] EuclideanSpace ℂ (Fin 4)))
        (((Whitney.whitneySum (cLine a) (cLine a)).coordChange t
          ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) b) x))
    = ((eGauge.symm : EuclideanSpace ℂ (Fin (2 + 2)) →L[ℂ] EuclideanSpace ℂ (Fin 4)))
        (((Whitney.whitneySum (cLine a) (cLine a)).coordChange t (i, i) b) x)
  rw [Xcc, eGauge_apply_symm']
  congr 1
  simpa using congrArg (fun (L : EuclideanSpace ℂ (Fin (2 + 2)) →L[ℂ]
    EuclideanSpace ℂ (Fin (2 + 2))) => L x) Ycoc

end

end Work.Agree

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-! ## §7. Assembling the splitting isomorphism -/

/-- **Obligation 1** of `Work.Thom.nonempty_bundleIso_of_gauge`: the chart-wise matrix of the
identity map is continuous on the intersection of the two charts. -/
lemma splitGauge_continuousOn (a : ℤ) (i : Bool) (t : Bool × Bool) :
    ContinuousOn (fun b => splitGauge a i t b)
      ((Work.Thom.complexificationCore (clutchBundle a 0)).baseSet i
        ∩ (Whitney.whitneySum (cLine a) (cLine a)).baseSet t) := by
  refine ContinuousOn.congr
    (f := fun b => ((Whitney.whitneySum (cLine a) (cLine a)).coordChange (i, i) t b).comp
      (eGauge : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin (2 + 2)))) ?_ ?_
  · refine ContinuousOn.clm_comp ?_ continuousOn_const
    exact ((Whitney.whitneySum (cLine a) (cLine a)).continuousOn_coordChange (i, i) t).mono
      (fun b hb => ⟨by rw [Ybase_eq a i]; exact hb.1, hb.2⟩)
  · intro b hb
    exact splitGauge_eq a i t b hb

/-- **Obligation 2** of `Work.Thom.nonempty_bundleIso_of_gauge`: the chart-wise inverse is
continuous. -/
lemma splitGaugeInv_continuousOn (a : ℤ) (i : Bool) (t : Bool × Bool) :
    ContinuousOn (fun b => splitGaugeInv a i t b)
      ((Work.Thom.complexificationCore (clutchBundle a 0)).baseSet i
        ∩ (Whitney.whitneySum (cLine a) (cLine a)).baseSet t) := by
  refine ContinuousOn.congr
    (f := fun b => ((eGauge : EuclideanSpace ℂ (Fin 4) ≃L[ℂ] EuclideanSpace ℂ (Fin (2 + 2))).symm :
        EuclideanSpace ℂ (Fin (2 + 2)) →L[ℂ] EuclideanSpace ℂ (Fin 4)).comp
      ((Whitney.whitneySum (cLine a) (cLine a)).coordChange t (i, i) b)) ?_ ?_
  · refine ContinuousOn.clm_comp continuousOn_const ?_
    exact ((Whitney.whitneySum (cLine a) (cLine a)).continuousOn_coordChange t (i, i)).mono
      (fun b hb => ⟨hb.2, by rw [Ybase_eq a i]; exact hb.1⟩)
  · intro b hb
    exact splitGaugeInv_eq a i t b hb

/-- **Obligation 3** of `Work.Thom.nonempty_bundleIso_of_gauge` (compatibility with the target
transitions). -/
lemma splitGauge_htgt (a : ℤ) (i : Bool) (t t' : Bool × Bool) (b : S4)
    (hi : b ∈ (Work.Thom.complexificationCore (clutchBundle a 0)).baseSet i)
    (ht : b ∈ (Whitney.whitneySum (cLine a) (cLine a)).baseSet t)
    (ht' : b ∈ (Whitney.whitneySum (cLine a) (cLine a)).baseSet t') :
    ((Whitney.whitneySum (cLine a) (cLine a)).coordChange t t' b).comp (splitGauge a i t b)
      = splitGauge a i t' b := by
  have hbkY : b ∈ (Whitney.whitneySum (cLine a) (cLine a)).baseSet
      ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) := by
    rw [← YindexAt_eq]; exact (Whitney.whitneySum (cLine a) (cLine a)).mem_baseSet_at b
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, splitGauge]
  rw [(Whitney.whitneySum (cLine a) (cLine a)).coordChange_comp
      ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) t t' b ⟨⟨hbkY, ht⟩, ht'⟩]

/-- **Obligation 4** of `Work.Thom.nonempty_bundleIso_of_gauge` (compatibility with the source
transitions). -/
lemma splitGauge_hsrc (a : ℤ) (i : Bool) (t : Bool × Bool) (i' : Bool) (b : S4)
    (hi : b ∈ (Work.Thom.complexificationCore (clutchBundle a 0)).baseSet i)
    (hi' : b ∈ (Work.Thom.complexificationCore (clutchBundle a 0)).baseSet i')
    (ht : b ∈ (Whitney.whitneySum (cLine a) (cLine a)).baseSet t) :
    (splitGauge a i t b).comp
        ((Work.Thom.complexificationCore (clutchBundle a 0)).coordChange i' i b)
      = splitGauge a i' t b := by
  have hbkX : b ∈ (Work.Thom.complexificationCore (clutchBundle a 0)).baseSet
      ((clutchBundle a 0).indexAt b) :=
    (Work.Thom.complexificationCore (clutchBundle a 0)).mem_baseSet_at b
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, splitGauge]
  rw [(Work.Thom.complexificationCore (clutchBundle a 0)).coordChange_comp
      i' i ((clutchBundle a 0).indexAt b) b ⟨⟨hi', hi⟩, hbkX⟩]

/-- **Obligation 5** of `Work.Thom.nonempty_bundleIso_of_gauge`. -/
lemma splitGauge_htgtinv (a : ℤ) (i : Bool) (t t' : Bool × Bool) (b : S4)
    (hi : b ∈ (Work.Thom.complexificationCore (clutchBundle a 0)).baseSet i)
    (ht : b ∈ (Whitney.whitneySum (cLine a) (cLine a)).baseSet t)
    (ht' : b ∈ (Whitney.whitneySum (cLine a) (cLine a)).baseSet t') :
    (splitGaugeInv a i t b).comp
        ((Whitney.whitneySum (cLine a) (cLine a)).coordChange t' t b)
      = splitGaugeInv a i t' b := by
  have hbkY : b ∈ (Whitney.whitneySum (cLine a) (cLine a)).baseSet
      ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) := by
    rw [← YindexAt_eq]; exact (Whitney.whitneySum (cLine a) (cLine a)).mem_baseSet_at b
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, splitGaugeInv]
  rw [(Whitney.whitneySum (cLine a) (cLine a)).coordChange_comp
      t' t ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) b ⟨⟨ht', ht⟩, hbkY⟩]

/-- **Obligation 6** of `Work.Thom.nonempty_bundleIso_of_gauge`. -/
lemma splitGauge_hsrcinv (a : ℤ) (i : Bool) (t : Bool × Bool) (i' : Bool) (b : S4)
    (hi : b ∈ (Work.Thom.complexificationCore (clutchBundle a 0)).baseSet i)
    (hi' : b ∈ (Work.Thom.complexificationCore (clutchBundle a 0)).baseSet i')
    (ht : b ∈ (Whitney.whitneySum (cLine a) (cLine a)).baseSet t) :
    ((Work.Thom.complexificationCore (clutchBundle a 0)).coordChange i i' b).comp
        (splitGaugeInv a i t b)
      = splitGaugeInv a i' t b := by
  have hbkX : b ∈ (Work.Thom.complexificationCore (clutchBundle a 0)).baseSet
      ((clutchBundle a 0).indexAt b) :=
    (Work.Thom.complexificationCore (clutchBundle a 0)).mem_baseSet_at b
  apply ContinuousLinearMap.ext
  intro x
  simp only [ContinuousLinearMap.comp_apply, splitGaugeInv]
  rw [(Work.Thom.complexificationCore (clutchBundle a 0)).coordChange_comp
      ((clutchBundle a 0).indexAt b) i i' b ⟨⟨hbkX, hi⟩, hi'⟩]

/-- **Obligation 7** of `Work.Thom.nonempty_bundleIso_of_gauge`. -/
lemma splitGauge_hleft (a : ℤ) (i : Bool) (t : Bool × Bool) (b : S4)
    (hb : b ∈ (Work.Thom.complexificationCore (clutchBundle a 0)).baseSet i
      ∩ (Whitney.whitneySum (cLine a) (cLine a)).baseSet t)
    (x : EuclideanSpace ℂ (Fin 4)) :
    splitGaugeInv a i t b (splitGauge a i t b x) = x := by
  have hbX : b ∈ (Work.Thom.complexificationCore (clutchBundle a 0)).baseSet i := hb.1
  have hbY : b ∈ (Whitney.whitneySum (cLine a) (cLine a)).baseSet t := hb.2
  have hbkY : b ∈ (Whitney.whitneySum (cLine a) (cLine a)).baseSet
      ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) := by
    rw [← YindexAt_eq]; exact (Whitney.whitneySum (cLine a) (cLine a)).mem_baseSet_at b
  have hbkX : b ∈ (Work.Thom.complexificationCore (clutchBundle a 0)).baseSet
      ((clutchBundle a 0).indexAt b) :=
    (Work.Thom.complexificationCore (clutchBundle a 0)).mem_baseSet_at b
  simp only [splitGauge, splitGaugeInv, ContinuousLinearMap.comp_apply]
  rw [(Whitney.whitneySum (cLine a) (cLine a)).coordChange_comp
      ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) t
      ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) b ⟨⟨hbkY, hbY⟩, hbkY⟩,
    (Whitney.whitneySum (cLine a) (cLine a)).coordChange_self
      ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) b hbkY]
  rw [eGauge_symm_apply']
  rw [(Work.Thom.complexificationCore (clutchBundle a 0)).coordChange_comp
      i ((clutchBundle a 0).indexAt b) i b ⟨⟨hbX, hbkX⟩, hbX⟩,
    (Work.Thom.complexificationCore (clutchBundle a 0)).coordChange_self i b hbX]

/-- **Obligation 8** of `Work.Thom.nonempty_bundleIso_of_gauge`. -/
lemma splitGauge_hright (a : ℤ) (i : Bool) (t : Bool × Bool) (b : S4)
    (hb : b ∈ (Work.Thom.complexificationCore (clutchBundle a 0)).baseSet i
      ∩ (Whitney.whitneySum (cLine a) (cLine a)).baseSet t)
    (y : EuclideanSpace ℂ (Fin (2 + 2))) :
    splitGauge a i t b (splitGaugeInv a i t b y) = y := by
  have hbX : b ∈ (Work.Thom.complexificationCore (clutchBundle a 0)).baseSet i := hb.1
  have hbY : b ∈ (Whitney.whitneySum (cLine a) (cLine a)).baseSet t := hb.2
  have hbkY : b ∈ (Whitney.whitneySum (cLine a) (cLine a)).baseSet
      ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) := by
    rw [← YindexAt_eq]; exact (Whitney.whitneySum (cLine a) (cLine a)).mem_baseSet_at b
  have hbkX : b ∈ (Work.Thom.complexificationCore (clutchBundle a 0)).baseSet
      ((clutchBundle a 0).indexAt b) :=
    (Work.Thom.complexificationCore (clutchBundle a 0)).mem_baseSet_at b
  simp only [splitGauge, splitGaugeInv, ContinuousLinearMap.comp_apply]
  rw [(Work.Thom.complexificationCore (clutchBundle a 0)).coordChange_comp
      ((clutchBundle a 0).indexAt b) i ((clutchBundle a 0).indexAt b) b ⟨⟨hbkX, hbX⟩, hbkX⟩,
    (Work.Thom.complexificationCore (clutchBundle a 0)).coordChange_self
      ((clutchBundle a 0).indexAt b) b hbkX]
  rw [eGauge_apply_symm']
  rw [(Whitney.whitneySum (cLine a) (cLine a)).coordChange_comp
      t ((clutchBundle a 0).indexAt b, (clutchBundle a 0).indexAt b) t b ⟨⟨hbY, hbkY⟩, hbY⟩,
    (Whitney.whitneySum (cLine a) (cLine a)).coordChange_self t b hbY]

/-- **The splitting of the complexification of `L^a R^0` over `S⁴`**: the rank-`4` complex bundle
`ℂ ⊗_ℝ L^a R^0` is the Whitney sum of the rank-`2` bundle `V_a` with itself. -/
theorem complexificationCore_iso_whitneySum (a : ℤ) :
    Nonempty (Work.Thom.BundleIso (Work.Thom.complexificationCore (clutchBundle a 0))
      (Whitney.whitneySum (cLine a) (cLine a))) := by
  refine Work.Thom.nonempty_bundleIso_of_gauge
    (Work.Thom.complexificationCore (clutchBundle a 0))
    (Whitney.whitneySum (cLine a) (cLine a))
    (splitGauge a) (splitGaugeInv a) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i t
    exact splitGauge_continuousOn a i t
  · intro i t
    exact splitGaugeInv_continuousOn a i t
  · intro i t t' b hi ht ht'
    exact splitGauge_htgt a i t t' b hi ht ht'
  · intro i t i' b hi hi' ht
    exact splitGauge_hsrc a i t i' b hi hi' ht
  · intro i t t' b hi ht ht'
    exact splitGauge_htgtinv a i t t' b hi ht ht'
  · intro i t i' b hi hi' ht
    exact splitGauge_hsrcinv a i t i' b hi hi' ht
  · intro i t b x hb
    exact splitGauge_hleft a i t b hb x
  · intro i t b y hb
    exact splitGauge_hright a i t b hb y

/-- **The Chern class of the complexified quaternionic line bundle is that of the Whitney sum
`V_a ⊕ V_a`** — the class-level form of `Work.Agree.complexificationCore_iso_whitneySum`. -/
theorem chernClass_complexification_clutch (a : ℤ) :
    Work.Thom.chernClass 4 2 (Work.Thom.complexificationCore (clutchBundle a 0))
      = Work.Thom.chernClass 4 2 (Whitney.whitneySum (cLine a) (cLine a)) := by
  obtain ⟨e⟩ := complexificationCore_iso_whitneySum a
  exact Work.Thom.chernClass_BundleIso _ _ e

/-- **The final assembly modulo the two bricks.**  Given

* the degree-`2` Whitney formula for sums of two rank-`2` complex bundles over `S⁴`
  (`Work.Agree.whitneyTwoTwo`), and
* the Euler-class computation `c₂(V_a) = ± a·G` (the canonical form of
  `Work.Agree.eulerClutch`, converted by `Work.Thom.chernClass_succ_top'`),

the target `Work.Agree.BottHopf` follows: `c₂(ℂ ⊗ L^a R^0) = c₂(V_a) + c₂(V_a) = ± 2a·G`. -/
theorem bottHopf_of_bricks
    (hW : ∀ (U V : VectorBundleCore ℂ S4 (EuclideanSpace ℂ (Fin 2)) Bool),
      Work.Thom.chernClass 4 2 (Whitney.whitneySum U V)
        = Work.Thom.chernClass 2 2 U + Work.Thom.chernClass 2 2 V)
    (hE : ∀ (a : ℤ) (G : H 4 S4), (HMap discProj 4).hom G = Work.Milnor.tauD →
      Work.Thom.chernClass 2 2 (cLine a) = a • G ∨
      Work.Thom.chernClass 2 2 (cLine a) = -(a • G)) :
    Work.Agree.BottHopf := by
  intro a G hG
  have h1 := chernClass_complexification_clutch a
  have h2 := hW (cLine a) (cLine a)
  rcases hE a G hG with h | h
  · left
    rw [h1, h2, h, ← add_zsmul, show a + a = 2 * a from by ring]
  · right
    rw [h1, h2, h, ← neg_zsmul, ← neg_zsmul, ← add_zsmul,
      show -a + -a = -(2 * a) from by ring]

end

end Work.Agree
