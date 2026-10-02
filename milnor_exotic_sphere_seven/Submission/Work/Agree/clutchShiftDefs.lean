import Mathlib
import Submission.Work.Agree.S4Bundle
import Submission.Work.Thom.complexification
import Submission.Work.Thom.BundleIso_comap_exists

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
# The gauge of the `(a,b)`-shift: `ℂ(L^a R^b) ≅ ℂ(L^{a-b})`

This file sets up the *definitions* of the point-dependent gauge realising the isomorphism
`ℂ(L^aR^b) ≅ ℂ(L^{a-b})` of `Work.Agree.ComplexificationShift`.

The gauge is `b ↦ L_{q^b} · D_{σ(‖coord₀ b‖)} · L_{q^{-b}} · D_{σ(‖coord₀ b‖)}` where `q = uDir b`
and `D_t = (1+C)/2 + e^{iπt}(1-C)/2` is the path of complex-linear maps from `1` to `C` built from
the complexification `C = cxTrans conjCLM` of the quaternionic conjugation.

The three facts that make it work are

* `C · cxTrans (qTwist x y q) · C = cxTrans (qTwist (-y) (-x) q)` (the conjugation identity, the
  complexification of `conjCLM_qTwist`), which for `x = 0`, `y = -b` reads
  `C L_{q^{-b}} C = R_{q^b}`;
* `D_0 = 1`, `D_1 = C`, so the gauge is `1` near the origin of the first chart (its `σ = 0`;
  continuity at the origin) and `L_{q^b}R_{q^b} = cxTrans (qTwist b b q)` near infinity
  (its `σ = 1`; this makes the second chart's gauge expression the *identity* there, by
  `qTwist a b q · qTwist b b q · qTwist (-a) (-b) q = 1`);
* `cxTrans (qTwist a b q) = L_{q^a} · R_{q^b}`, and `L`/`R` commute, so all cancellations are
  multiplicative in the exponent.

Nothing here is specific to the two-chart model.
-/

namespace Work.Agree

open Work.TangentClasses

noncomputable section

/-! ## The quaternionic conjugation -/

lemma star_smul_real (r : ℝ) (q : Quaternion ℝ) : star (r • q) = r • star q := by
  apply Quaternion.ext
  · rw [Quaternion.re_star, Quaternion.re_smul, Quaternion.re_smul, Quaternion.re_star]
  · rw [Quaternion.imI_star, Quaternion.imI_smul, Quaternion.imI_smul, Quaternion.imI_star,
      smul_neg]
  · rw [Quaternion.imJ_star, Quaternion.imJ_smul, Quaternion.imJ_smul, Quaternion.imJ_star,
      smul_neg]
  · rw [Quaternion.imK_star, Quaternion.imK_smul, Quaternion.imK_smul, Quaternion.imK_star,
      smul_neg]

/-- The conjugation of the quaternions, as an `ℝ`-linear map. -/
noncomputable def starCLM : Quaternion ℝ →L[ℝ] Quaternion ℝ where
  toFun := star
  map_add' := star_add
  map_smul' := star_smul_real
  cont := continuous_star

@[simp] lemma starCLM_apply (q : Quaternion ℝ) : starCLM q = star q := rfl

/-- The conjugation of `ℝ⁴ ≅ ℍ`. -/
noncomputable def conjCLM : EuclideanSpace ℝ (Fin 4) →L[ℝ] EuclideanSpace ℝ (Fin 4) :=
  ofQ.comp (starCLM.comp toQ)

@[simp] lemma conjCLM_apply (v : EuclideanSpace ℝ (Fin 4)) :
    conjCLM v = ofQ (star (toQ v)) := rfl

lemma conjCLM_invol (v : EuclideanSpace ℝ (Fin 4)) : conjCLM (conjCLM v) = v := by
  simp only [conjCLM_apply, toQ_ofQ, star_star, ofQ_toQ]

lemma conjCLM_comp_self : conjCLM.comp conjCLM = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, one_apply_eq_self, conjCLM_invol]

/-- `uDir` is a unit quaternion. -/
lemma normSq_uDir (p : S4) : Quaternion.normSq (uDir p) = 1 := by
  have h : uDir p ∈ Metric.sphere (0 : Quaternion ℝ) 1 :=
    (Submission.Milnor.unitDir (coord0 p)).2
  have h1 := h
  rw [Metric.mem_sphere, dist_zero_right] at h1
  rw [Quaternion.normSq_eq_norm_mul_self, h1]
  norm_num

lemma star_of_normSq_one (q : Quaternion ℝ) (hq : Quaternion.normSq q = 1) : star q = q⁻¹ := by
  rw [Quaternion.inv_def, hq, inv_one, one_smul]

lemma star_zpow_of_normSq_one (q : Quaternion ℝ) (hq : Quaternion.normSq q = 1) (n : ℤ) :
    star (q ^ n) = q ^ (-n) := by
  rw [star_zpow₀, star_of_normSq_one q hq, inv_zpow']

/-- **The conjugation identity for the twisting maps.** -/
lemma conjCLM_qTwist (x y : ℤ) (q : Quaternion ℝ) (hq : Quaternion.normSq q = 1)
    (v : EuclideanSpace ℝ (Fin 4)) :
    conjCLM ((qTwist x y q) v) = (qTwist (-y) (-x) q) (conjCLM v) := by
  rw [qTwist_apply, qTwist_apply, conjCLM_apply, conjCLM_apply, toQ_ofQ,
    star_mul, star_mul, star_zpow_of_normSq_one q hq y, star_zpow_of_normSq_one q hq x,
    toQ_ofQ, mul_assoc]

/-- The conjugation identity as an identity of continuous linear maps. -/
lemma conjCLM_qTwist_clm (x y : ℤ) (q : Quaternion ℝ) (hq : Quaternion.normSq q = 1) :
    (qTwist (-y) (-x) q).comp conjCLM = conjCLM.comp (qTwist x y q) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply]
  exact (conjCLM_qTwist x y q hq v).symm

/-! ## The twisting maps multiply in the exponents -/

/-- Composition of two twists with the same (nonzero) quaternion: the exponents add. -/
lemma qTwist_comp_same (a b a' b' : ℤ) (q : Quaternion ℝ) (hq : q ≠ 0) :
    (qTwist a b q).comp (qTwist a' b' q) = qTwist (a + a') (b + b') q := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, qTwist_apply, toQ_ofQ]
  simp only [← mul_assoc]
  rw [← zpow_add₀ hq a a',
    mul_assoc (q ^ (a + a') * toQ v) (q ^ b') (q ^ b),
    ← zpow_add₀ hq b' b, add_comm b' b]

/-- The twist `a b` factors as the twist `a 0` followed by the twist `0 b`. -/
lemma qTwist_factor (a b : ℤ) (q : Quaternion ℝ) :
    qTwist a b q = (qTwist a 0 q).comp (qTwist 0 b q) := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, qTwist_apply, zpow_zero, one_mul, mul_one,
    toQ_ofQ]
  rw [mul_assoc]

/-- The twist at `(0,0)` is the identity. -/
@[simp] lemma qTwist_zero_zero (q : Quaternion ℝ) : qTwist 0 0 q = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [qTwist_apply, zpow_zero, one_mul, mul_one, ofQ_toQ]
  exact (one_apply_eq_self v).symm


/-! ## The complexified conjugation `C` -/

/-- **The complexification of the quaternionic conjugation**, the operator `C` of the gauge. -/
abbrev cxConj : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4) :=
  Work.Thom.cxTrans conjCLM

/-- `C` is an involution. -/
lemma cxConj_comp_cxConj : cxConj.comp cxConj = 1 := by
  rw [← Work.Thom.cxTrans_comp, conjCLM_comp_self, Work.Thom.cxTrans_one]

lemma cxConj_apply_apply (v : EuclideanSpace ℂ (Fin 4)) : cxConj (cxConj v) = v := by
  have h := congrArg (fun (f : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4))
    => f v) cxConj_comp_cxConj
  simpa only [ContinuousLinearMap.comp_apply, one_apply_eq_self] using h

/-- **The conjugation identity, complexified.** -/
lemma cxConj_qTwist (x y : ℤ) (q : Quaternion ℝ) (hq : Quaternion.normSq q = 1) :
    (Work.Thom.cxTrans (qTwist (-y) (-x) q)).comp cxConj =
      cxConj.comp (Work.Thom.cxTrans (qTwist x y q)) := by
  rw [← Work.Thom.cxTrans_comp, ← Work.Thom.cxTrans_comp,
    conjCLM_qTwist_clm x y q hq]

/-- **The conjugation of a complexified twist by `C`.** -/
lemma cxConj_qTwist_conj (x y : ℤ) (q : Quaternion ℝ) (hq : Quaternion.normSq q = 1) :
    cxConj.comp ((Work.Thom.cxTrans (qTwist x y q)).comp cxConj) =
      Work.Thom.cxTrans (qTwist (-y) (-x) q) := by
  rw [← ContinuousLinearMap.comp_assoc, ← cxConj_qTwist x y q hq,
    ContinuousLinearMap.comp_assoc, cxConj_comp_cxConj]
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply]

/-! ## The complexified twists multiply in the exponents -/

lemma cxTrans_qTwist_comp (a b c d : ℤ) (q : Quaternion ℝ) (hq : q ≠ 0) :
    (Work.Thom.cxTrans (qTwist a b q)).comp (Work.Thom.cxTrans (qTwist c d q)) =
      Work.Thom.cxTrans (qTwist (a + c) (b + d) q) := by
  rw [← Work.Thom.cxTrans_comp, qTwist_comp_same a b c d q hq]

lemma cxTrans_qTwist_comp_neg (a b : ℤ) (q : Quaternion ℝ) (hq : q ≠ 0) :
    (Work.Thom.cxTrans (qTwist a b q)).comp (Work.Thom.cxTrans (qTwist (-a) (-b) q)) = 1 := by
  rw [cxTrans_qTwist_comp a b (-a) (-b) q hq,
    show (a + -a) = 0 by ring, show (b + -b) = 0 by ring, qTwist_zero_zero,
    Work.Thom.cxTrans_one]

lemma cxConj_qTwist_conj_mul (x y : ℤ) (q : Quaternion ℝ) (hq : Quaternion.normSq q = 1) :
    cxConj * ((Work.Thom.cxTrans (qTwist x y q)) * cxConj) =
      Work.Thom.cxTrans (qTwist (-y) (-x) q) := by
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def]
  exact cxConj_qTwist_conj x y q hq

lemma cxTrans_qTwist_mul (a b c d : ℤ) (q : Quaternion ℝ) (hq : q ≠ 0) :
    (Work.Thom.cxTrans (qTwist a b q)) * (Work.Thom.cxTrans (qTwist c d q)) =
      Work.Thom.cxTrans (qTwist (a + c) (b + d) q) := by
  rw [ContinuousLinearMap.mul_def]
  exact cxTrans_qTwist_comp a b c d q hq

lemma cxTrans_qTwist_mul_neg (a b : ℤ) (q : Quaternion ℝ) (hq : q ≠ 0) :
    (Work.Thom.cxTrans (qTwist a b q)) * (Work.Thom.cxTrans (qTwist (-a) (-b) q)) = 1 := by
  rw [cxTrans_qTwist_mul a b (-a) (-b) q hq,
    show (a + -a) = 0 by ring, show (b + -b) = 0 by ring, qTwist_zero_zero,
    Work.Thom.cxTrans_one]

/-! ## The `-1`-eigenprojection `Q = (1-C)/2` -/

/-- The `-1`-eigenprojection of `C`. -/
noncomputable def cProjMinus : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4) :=
  (2⁻¹ : ℂ) • (1 - cxConj)

lemma cProjMinus_apply (v : EuclideanSpace ℂ (Fin 4)) :
    cProjMinus v = (2⁻¹ : ℂ) • (v - cxConj v) := by
  simp only [cProjMinus, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.one_apply, one_apply_eq_self]

lemma cProjMinus_apply_apply (v : EuclideanSpace ℂ (Fin 4)) :
    cProjMinus (cProjMinus v) = cProjMinus v := by
  rw [cProjMinus_apply, cProjMinus_apply]
  simp only [map_sub, map_smul, cxConj_apply_apply]
  module

lemma cProjMinus_comp_self : cProjMinus.comp cProjMinus = cProjMinus := by
  apply ContinuousLinearMap.ext
  intro v
  rw [ContinuousLinearMap.comp_apply, cProjMinus_apply_apply]

/-! ## The path `D_t = 1 + (e^{iπt}-1)Q` from `1` to `C` -/

/-- The path of complex-linear maps from `1` to `C`. -/
noncomputable def dOp (t : ℝ) : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4) :=
  1 + (Complex.exp ((t : ℂ) * ↑Real.pi * Complex.I) - 1) • cProjMinus

/-- The pointwise inverse of `dOp t`. -/
noncomputable def dOpInv (t : ℝ) : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4) :=
  1 + (Complex.exp (-((t : ℂ) * ↑Real.pi * Complex.I)) - 1) • cProjMinus

lemma dOp_zero : dOp 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [dOp, Complex.ofReal_zero, zero_mul, Complex.exp_zero, sub_self,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, one_apply_eq_self, zero_smul ℂ, add_zero]

lemma dOpInv_zero : dOpInv 0 = 1 := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [dOpInv, Complex.ofReal_zero, zero_mul, neg_zero, Complex.exp_zero, sub_self,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, one_apply_eq_self, zero_smul ℂ, add_zero]

lemma dOp_one : dOp 1 = cxConj := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [dOp, Complex.ofReal_one, one_mul, Complex.exp_pi_mul_I,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, one_apply_eq_self, cProjMinus_apply]
  module

lemma dOpInv_one : dOpInv 1 = cxConj := by
  apply ContinuousLinearMap.ext
  intro v
  simp only [dOpInv, Complex.ofReal_one, one_mul, Complex.exp_neg, Complex.exp_pi_mul_I,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, one_apply_eq_self, cProjMinus_apply]
  rw [show (-1 : ℂ)⁻¹ = -1 by norm_num]
  module

/-- The scalar identities behind the composition of the `dOp` path. -/
lemma dOp_scal (t : ℝ) :
    (Complex.exp ((t : ℂ) * ↑Real.pi * Complex.I) - 1) *
        (Complex.exp (-((t : ℂ) * ↑Real.pi * Complex.I)) - 1)
      + (Complex.exp ((t : ℂ) * ↑Real.pi * Complex.I) - 1)
      + (Complex.exp (-((t : ℂ) * ↑Real.pi * Complex.I)) - 1) = 0 := by
  have h : Complex.exp ((t : ℂ) * ↑Real.pi * Complex.I) *
      Complex.exp (-((t : ℂ) * ↑Real.pi * Complex.I)) = 1 := by
    rw [← Complex.exp_add,
      show (t : ℂ) * ↑Real.pi * Complex.I + -((t : ℂ) * ↑Real.pi * Complex.I) = 0 by ring,
      Complex.exp_zero]
  rw [show (Complex.exp ((t : ℂ) * ↑Real.pi * Complex.I) - 1) *
        (Complex.exp (-((t : ℂ) * ↑Real.pi * Complex.I)) - 1)
      + (Complex.exp ((t : ℂ) * ↑Real.pi * Complex.I) - 1)
      + (Complex.exp (-((t : ℂ) * ↑Real.pi * Complex.I)) - 1)
      = Complex.exp ((t : ℂ) * ↑Real.pi * Complex.I) *
          Complex.exp (-((t : ℂ) * ↑Real.pi * Complex.I)) - 1 by ring, h, sub_self]

/-- The composition rule for two `dOp`-shaped maps. -/
lemma proj_path_comp (Q : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4))
    (hQ : Q.comp Q = Q) (z w : ℂ) :
    (1 + z • Q).comp (1 + w • Q) = 1 + (z * w + z + w) • Q := by
  apply ContinuousLinearMap.ext
  intro v
  have hQv : Q (Q v) = Q v := by
    have h := congrArg (fun (f : EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4))
      => f v) hQ
    simpa only [ContinuousLinearMap.comp_apply] using h
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, one_apply_eq_self,
    map_add, map_smul]
  rw [hQv]
  module

lemma dOp_comp_dOpInv (t : ℝ) : (dOp t).comp (dOpInv t) = 1 := by
  have hsc := dOp_scal t
  simp only [dOp, dOpInv]
  rw [proj_path_comp cProjMinus cProjMinus_comp_self _ _, hsc]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, one_apply_eq_self, zero_smul ℂ, add_zero]

lemma dOpInv_comp_dOp (t : ℝ) : (dOpInv t).comp (dOp t) = 1 := by
  have hsc : (Complex.exp (-((t : ℂ) * ↑Real.pi * Complex.I)) - 1) *
        (Complex.exp ((t : ℂ) * ↑Real.pi * Complex.I) - 1)
      + (Complex.exp (-((t : ℂ) * ↑Real.pi * Complex.I)) - 1)
      + (Complex.exp ((t : ℂ) * ↑Real.pi * Complex.I) - 1) = 0 := by
    have h : Complex.exp (-((t : ℂ) * ↑Real.pi * Complex.I)) *
        Complex.exp ((t : ℂ) * ↑Real.pi * Complex.I) = 1 := by
      rw [← Complex.exp_add,
        show -((t : ℂ) * ↑Real.pi * Complex.I) + (t : ℂ) * ↑Real.pi * Complex.I = 0 by ring,
        Complex.exp_zero]
    rw [show (Complex.exp (-((t : ℂ) * ↑Real.pi * Complex.I)) - 1) *
          (Complex.exp ((t : ℂ) * ↑Real.pi * Complex.I) - 1)
        + (Complex.exp (-((t : ℂ) * ↑Real.pi * Complex.I)) - 1)
        + (Complex.exp ((t : ℂ) * ↑Real.pi * Complex.I) - 1)
        = Complex.exp (-((t : ℂ) * ↑Real.pi * Complex.I)) *
            Complex.exp ((t : ℂ) * ↑Real.pi * Complex.I) - 1 by ring, h, sub_self]
  simp only [dOp, dOpInv]
  rw [proj_path_comp cProjMinus cProjMinus_comp_self _ _, hsc]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, one_apply_eq_self, zero_smul ℂ, add_zero]

/-! ## The radial function and the gauge -/

/-- The radial cutoff `σ(r) = min 1 (max 0 (r-1))`. -/
noncomputable def sigFun (r : ℝ) : ℝ := min 1 (max 0 (r - 1))

lemma sigFun_of_le_one {r : ℝ} (h : r ≤ 1) : sigFun r = 0 := by
  have h1 : r - 1 ≤ 0 := by linarith
  rw [sigFun, max_eq_left h1, min_eq_right (by norm_num)]

lemma sigFun_of_two_le {r : ℝ} (h : 2 ≤ r) : sigFun r = 1 := by
  have h1 : (0:ℝ) ≤ r - 1 := by linarith
  have h2 : (1:ℝ) ≤ r - 1 := by linarith
  rw [sigFun, max_eq_right h1, min_eq_left h2]

lemma continuous_sigFun : Continuous sigFun := by unfold sigFun; fun_prop

/-- The radial parameter of the gauge on the base. -/
noncomputable def sigR (p : S4) : ℝ := sigFun ‖coord0 p‖

lemma sigR_of_le_one {p : S4} (h : ‖coord0 p‖ ≤ 1) : sigR p = 0 := sigFun_of_le_one h

lemma sigR_of_two_le {p : S4} (h : 2 ≤ ‖coord0 p‖) : sigR p = 1 := sigFun_of_two_le h

/-- The `A`-factor of the gauge: left multiplication by `q^b`. -/
noncomputable def gaugeA (b : ℤ) (p : S4) :
    EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4) :=
  Work.Thom.cxTrans (qTwist b 0 (uDir p))

/-- The `B`-factor of the gauge: left multiplication by `q^{-b}`. -/
noncomputable def gaugeB (b : ℤ) (p : S4) :
    EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4) :=
  Work.Thom.cxTrans (qTwist (-b) 0 (uDir p))

/-- **The gauge of the `(a,b)`-shift.** -/
noncomputable def gaugeOp (b : ℤ) (p : S4) :
    EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4) :=
  gaugeA b p * (dOp (sigR p) * (gaugeB b p * dOp (sigR p)))

/-- The pointwise inverse of `gaugeOp`. -/
noncomputable def gaugeInvOp (b : ℤ) (p : S4) :
    EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4) :=
  dOpInv (sigR p) * (gaugeA b p * (dOpInv (sigR p) * gaugeB b p))

lemma gaugeA_mul_gaugeB (b : ℤ) (p : S4) : gaugeA b p * gaugeB b p = 1 := by
  rw [gaugeA, gaugeB]
  exact cxTrans_qTwist_mul_neg b 0 (uDir p) (uDir_ne_zero p)

lemma gaugeB_mul_gaugeA (b : ℤ) (p : S4) : gaugeB b p * gaugeA b p = 1 := by
  rw [gaugeA, gaugeB, cxTrans_qTwist_mul (-b) 0 b 0 (uDir p) (uDir_ne_zero p),
    show ((-b) + b : ℤ) = 0 from by ring, show (0 + 0 : ℤ) = 0 from by ring,
    qTwist_zero_zero, Work.Thom.cxTrans_one]

/-- The `σ = 0` value of the gauge: the identity. -/
lemma gaugeOp_of_sigR_zero {b : ℤ} {p : S4} (h : sigR p = 0) : gaugeOp b p = 1 := by
  rw [gaugeOp, h, dOp_zero]
  simp only [mul_one, one_mul]
  exact gaugeA_mul_gaugeB b p

lemma gaugeInvOp_of_sigR_zero {b : ℤ} {p : S4} (h : sigR p = 0) : gaugeInvOp b p = 1 := by
  rw [gaugeInvOp, h, dOpInv_zero]
  simp only [mul_one, one_mul]
  exact gaugeA_mul_gaugeB b p

/-- The `σ = 1` value of the gauge: the twist `qTwist b b q`. -/
lemma gaugeOp_of_sigR_one {b : ℤ} {p : S4} (h : sigR p = 1) :
    gaugeOp b p = Work.Thom.cxTrans (qTwist b b (uDir p)) := by
  have hconj := cxConj_qTwist_conj_mul (-b) 0 (uDir p) (normSq_uDir p)
  simp only [neg_zero, neg_neg] at hconj
  rw [gaugeOp, h, dOp_one, gaugeA, gaugeB, hconj,
    cxTrans_qTwist_mul b 0 0 b (uDir p) (uDir_ne_zero p)]
  simp only [add_zero, zero_add]

lemma gaugeInvOp_of_sigR_one {b : ℤ} {p : S4} (h : sigR p = 1) :
    gaugeInvOp b p = Work.Thom.cxTrans (qTwist (-b) (-b) (uDir p)) := by
  have hconj := cxConj_qTwist_conj_mul b 0 (uDir p) (normSq_uDir p)
  simp only [neg_zero] at hconj
  rw [gaugeInvOp, h, dOpInv_one, gaugeA, gaugeB]
  rw [show cxConj * (Work.Thom.cxTrans (qTwist b 0 (uDir p)) *
        (cxConj * Work.Thom.cxTrans (qTwist (-b) 0 (uDir p))))
      = (cxConj * (Work.Thom.cxTrans (qTwist b 0 (uDir p)) * cxConj)) *
        Work.Thom.cxTrans (qTwist (-b) 0 (uDir p)) from by noncomm_ring]
  rw [hconj, cxTrans_qTwist_mul 0 (-b) (-b) 0 (uDir p) (uDir_ne_zero p)]
  simp only [add_zero, zero_add]

/-- **The gauge is a two-sided inverse pair.** -/
lemma gaugeOp_mul_gaugeInvOp (b : ℤ) (p : S4) : gaugeOp b p * gaugeInvOp b p = 1 := by
  have hD : dOp (sigR p) * dOpInv (sigR p) = 1 := by
    rw [ContinuousLinearMap.mul_def, dOp_comp_dOpInv]
  have hBA := gaugeB_mul_gaugeA b p
  have hAB := gaugeA_mul_gaugeB b p
  simp only [gaugeOp, gaugeInvOp]
  calc gaugeA b p * (dOp (sigR p) * (gaugeB b p * dOp (sigR p))) *
        (dOpInv (sigR p) * (gaugeA b p * (dOpInv (sigR p) * gaugeB b p)))
      = (gaugeA b p * dOp (sigR p) * gaugeB b p) * (dOp (sigR p) * dOpInv (sigR p)) *
          (gaugeA b p * dOpInv (sigR p) * gaugeB b p) := by noncomm_ring
    _ = (gaugeA b p * dOp (sigR p) * gaugeB b p) * 1 *
          (gaugeA b p * dOpInv (sigR p) * gaugeB b p) := by rw [hD]
    _ = (gaugeA b p * dOp (sigR p)) * (gaugeB b p * gaugeA b p) *
          (dOpInv (sigR p) * gaugeB b p) := by noncomm_ring
    _ = (gaugeA b p * dOp (sigR p)) * 1 * (dOpInv (sigR p) * gaugeB b p) := by rw [hBA]
    _ = gaugeA b p * (dOp (sigR p) * dOpInv (sigR p)) * gaugeB b p := by noncomm_ring
    _ = gaugeA b p * 1 * gaugeB b p := by rw [hD]
    _ = gaugeA b p * gaugeB b p := by noncomm_ring
    _ = 1 := hAB

lemma gaugeInvOp_mul_gaugeOp (b : ℤ) (p : S4) : gaugeInvOp b p * gaugeOp b p = 1 := by
  have hD' : dOpInv (sigR p) * dOp (sigR p) = 1 := by
    rw [ContinuousLinearMap.mul_def, dOpInv_comp_dOp]
  have hBA := gaugeB_mul_gaugeA b p
  have hAB := gaugeA_mul_gaugeB b p
  simp only [gaugeOp, gaugeInvOp]
  calc dOpInv (sigR p) * (gaugeA b p * (dOpInv (sigR p) * gaugeB b p)) *
        (gaugeA b p * (dOp (sigR p) * (gaugeB b p * dOp (sigR p))))
      = (dOpInv (sigR p) * gaugeA b p * dOpInv (sigR p)) * (gaugeB b p * gaugeA b p) *
          (dOp (sigR p) * gaugeB b p * dOp (sigR p)) := by noncomm_ring
    _ = (dOpInv (sigR p) * gaugeA b p * dOpInv (sigR p)) * 1 *
          (dOp (sigR p) * gaugeB b p * dOp (sigR p)) := by rw [hBA]
    _ = (dOpInv (sigR p) * gaugeA b p) * (dOpInv (sigR p) * dOp (sigR p)) *
          (gaugeB b p * dOp (sigR p)) := by noncomm_ring
    _ = (dOpInv (sigR p) * gaugeA b p) * 1 * (gaugeB b p * dOp (sigR p)) := by rw [hD']
    _ = dOpInv (sigR p) * (gaugeA b p * gaugeB b p) * dOp (sigR p) := by noncomm_ring
    _ = dOpInv (sigR p) * 1 * dOp (sigR p) := by rw [hAB]
    _ = dOpInv (sigR p) * dOp (sigR p) := by noncomm_ring
    _ = 1 := hD'

/-! ## The cancellation of the twist factors at `σ = 1` -/

/-- The real twist factors cancel at `σ = 1`. -/
lemma shift_cancel_real (a b : ℤ) (q : Quaternion ℝ) (hq : q ≠ 0) :
    (qTwist (a - b) 0 q).comp ((qTwist b b q).comp (qTwist (-a) (-b) q)) = 1 := by
  rw [qTwist_comp_same b b (-a) (-b) q hq,
    show (b + -a : ℤ) = b - a from by ring, show (b + -b : ℤ) = 0 from by ring,
    qTwist_comp_same (a - b) 0 (b - a) 0 q hq,
    show ((a - b) + (b - a) : ℤ) = 0 from by ring, show (0 + 0 : ℤ) = 0 from by ring,
    qTwist_zero_zero]

/-- The complexified twists cancel against the shifted one. -/
lemma shift_cancel (a b : ℤ) (q : Quaternion ℝ) (hq : q ≠ 0) :
    (Work.Thom.cxTrans (qTwist (a - b) 0 q)) *
      ((Work.Thom.cxTrans (qTwist b b q)) * (Work.Thom.cxTrans (qTwist (-a) (-b) q))) = 1 := by
  have h2 := congrArg Work.Thom.cxTrans (shift_cancel_real a b q hq)
  simp only [Work.Thom.cxTrans_comp, Work.Thom.cxTrans_one] at h2
  simpa only [← ContinuousLinearMap.mul_def] using h2

/-- The real twist factors cancel for the inverse gauge, at `σ = 1`. -/
lemma shift_cancel_inv_real (a b : ℤ) (q : Quaternion ℝ) (hq : q ≠ 0) :
    (qTwist a b q).comp ((qTwist (-b) (-b) q).comp (qTwist (b - a) 0 q)) = 1 := by
  rw [qTwist_comp_same (-b) (-b) (b - a) 0 q hq,
    show (-b + (b - a) : ℤ) = -a from by ring, show (-b + 0 : ℤ) = -b from by ring,
    qTwist_comp_same a b (-a) (-b) q hq,
    show (a + -a : ℤ) = 0 from by ring, show (b + -b : ℤ) = 0 from by ring,
    qTwist_zero_zero]

/-- The cancellation of the twist factors for the inverse gauge, at `σ = 1`. -/
lemma shift_cancel_inv (a b : ℤ) (q : Quaternion ℝ) (hq : q ≠ 0) :
    (Work.Thom.cxTrans (qTwist a b q)) *
      ((Work.Thom.cxTrans (qTwist (-b) (-b) q)) *
        (Work.Thom.cxTrans (qTwist (b - a) 0 q))) = 1 := by
  have h2 := congrArg Work.Thom.cxTrans (shift_cancel_inv_real a b q hq)
  simp only [Work.Thom.cxTrans_comp, Work.Thom.cxTrans_one] at h2
  simpa only [← ContinuousLinearMap.mul_def] using h2

/-! ## The bundles and the two families whose continuity is the content -/

/-- The complexification of `L^aR^b`, as a complex bundle over `S⁴`. -/
noncomputable abbrev ZZ (a b : ℤ) :
    VectorBundleCore ℂ S4 (EuclideanSpace ℂ (Fin 4)) Bool :=
  Work.Thom.complexificationCore (clutchBundle a b)

/-- The chart expression of the gauge, in the source chart `i₁` and target chart `i₂`. -/
noncomputable def hTex (a b : ℤ) (i₁ i₂ : Bool) (p : S4) :
    EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4) :=
  ((ZZ (a - b) 0).coordChange ((ZZ (a - b) 0).indexAt p) i₂ p).comp
    ((gaugeOp b p).comp ((ZZ a b).coordChange i₁ ((ZZ a b).indexAt p) p))

/-- The chart expression of the *inverse* gauge. -/
noncomputable def hTexInv (a b : ℤ) (i₁ i₂ : Bool) (p : S4) :
    EuclideanSpace ℂ (Fin 4) →L[ℂ] EuclideanSpace ℂ (Fin 4) :=
  ((ZZ a b).coordChange ((ZZ a b).indexAt p) i₁ p).comp
    ((gaugeInvOp b p).comp ((ZZ (a - b) 0).coordChange i₂ ((ZZ (a - b) 0).indexAt p) p))

end

end Work.Agree
