import Mathlib
import Submission.Work.Agree.cLine
import Submission.Work.Whitney.Basic
import Submission.Work.Thom.sumEps
import Submission.Work.Gen.EulerToolkit
import Submission.Work.Agree.clutchShiftDefs
import Submission.Work.Agree.clutchShift

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.Agree

open Work.TangentClasses

open scoped Topology

noncomputable section

/-!
# The rank-two shift `cLine a ⊕ cLine a ≅ cLine (2a) ⊕ ε²`

The two rank-`4` complex bundles over `S⁴ = ℝ⁴ ∪ {∞}` with the two-chart cover
(`hemi0 = S⁴ ∖ {∞}`, `hemi1 = S⁴ ∖ {0}`)

* `X a = cLine a ⊕ cLine a`, whose clutching is `diag(M_a, M_a)`, `M_a = Mmat (uDir p ^ a)`, and
* `Y a = cLine (2a) ⊕ ε²`, whose clutching is `diag(M_a ^ 2, 1)`,

have the same clutching class in `π₃(U(4)) = ℤ` (namely `2a`), hence are isomorphic.  The
isomorphism is exhibited here as an explicit gauge, in the `bundleSum` presentations
(`Work.Thom.bundleSum`, with fibre `Blk = ℂ² × ℂ²`, where the transitions are *block diagonal*):

`Ψ i t b = Y.chg 𝟘 t b ∘ H b ∘ X.chg i 𝟘 b`,  `Ψinv i t b = X.chg 𝟘 i b ∘ H⁻¹ b ∘ Y.chg t 𝟘 b`,

where the core `H b` is the explicit interpolation

`H b = R(σ b) · diag(1, M_a) · R(σ b)⁻¹ · diag(M_a⁻¹, 1)`,

with `R` the block rotation `[[cos(πθ/2), -sin(πθ/2)],[sin(πθ/2), cos(πθ/2)]]` and
`σ b = 1 - sigFun ‖coord0 b‖` (`σ = 1` near the origin `↑0`, `σ = 0` near `∞`).  Near `∞` the
interpolation has settled to `H = diag(M_a⁻¹, M_a)`, which is exactly the "compensator" making
`Y.chg 𝟘 𝟙 ∘ H ∘ X.chg 𝟙 𝟘 = 1`; near `↑0` we have `H = 1`.  The intermediate angle `σ` is what
makes `H` continuous on `hemi0` while its conjugate by the transitions is continuous on `hemi1`.
-/

/-! ## §0. The block fibre and the two presentations -/

/-- The standard fibre of a rank-`2` complex bundle. -/
abbrev E2 : Type := EuclideanSpace ℂ (Fin 2)

/-- The fibre of `Work.Thom.bundleSum (cLine a) (cLine a)`. -/
abbrev Blk : Type := E2 × E2

/-- The source presentation of `cLine a ⊕ cLine a`, in the block fibre. -/
abbrev srcB (a : ℤ) : VectorBundleCore ℂ S4 Blk (Bool × Bool) :=
  Work.Thom.bundleSum (cLine a) (cLine a)

/-- The target presentation of `cLine (2a) ⊕ ε²`, in the block fibre. -/
abbrev tgtB (a : ℤ) : VectorBundleCore ℂ S4 Blk (Bool × Bool) :=
  Work.Thom.bundleSum (cLine (2 * a))
    (trivialVectorBundleCore ℂ S4 E2 Bool)

/-! ## §1. The block composition law -/

/-- Block-diagonal maps compose componentwise. -/
lemma prodMap_comp_prodMapBlk (A₁ A₂ B₁ B₂ : E2 →L[ℂ] E2) :
    (A₁.prodMap A₂).comp (B₁.prodMap B₂) = (A₁.comp B₁).prodMap (A₂.comp B₂) := by
  ext x <;> simp [ContinuousLinearMap.coe_prodMap']

/-! ## §2. The global composition law of the transition functions of `cLine a` -/

lemma Mmat_zpow_mul_neg (a : ℤ) (b : S4) :
    (Mmat (uDir b ^ a)).comp (Mmat (uDir b ^ (-a))) = 1 := by
  rw [Mmat_mul]
  rw [show uDir b ^ a * uDir b ^ (-a) = uDir b ^ (a + (-a)) from
    (zpow_add₀ (uDir_ne_zero b) a (-a)).symm]
  rw [add_neg_cancel, zpow_zero, Mmat_one]

lemma Mmat_zpow_mul_neg' (a : ℤ) (b : S4) :
    (Mmat (uDir b ^ (-a))).comp (Mmat (uDir b ^ a)) = 1 := by
  rw [Mmat_mul]
  rw [show uDir b ^ (-a) * uDir b ^ a = uDir b ^ ((-a) + a) from
    (zpow_add₀ (uDir_ne_zero b) (-a) a).symm]
  rw [neg_add_cancel, zpow_zero, Mmat_one]

/-- **The global cocycle law of `cLine a`**: the transition functions compose, for *all* base points
(not only on the intersections of the two charts). -/
lemma cLineCT_comp (a : ℤ) (p q r : Bool) (b : S4) :
    (cLine a).coordChange q r b ∘SL (cLine a).coordChange p q b
      = (cLine a).coordChange p r b := by
  cases p <;> cases q <;> cases r <;>
    simp only [cLine_coordChange, cLineCT] <;>
    (first
      | rfl
      | rw [ContinuousLinearMap.comp_id]
      | rw [ContinuousLinearMap.id_comp]
      | exact Mmat_zpow_mul_neg a b
      | exact Mmat_zpow_mul_neg' a b)

/-! ## §3. The composition laws of the two presentations -/

lemma srcB_chg_comp (a : ℤ) (p q r : Bool × Bool) (b : S4) :
    (srcB a).coordChange q r b ∘SL (srcB a).coordChange p q b = (srcB a).coordChange p r b := by
  show ((cLine a).coordChange q.1 r.1 b).prodMap ((cLine a).coordChange q.2 r.2 b) ∘SL
      ((cLine a).coordChange p.1 q.1 b).prodMap ((cLine a).coordChange p.2 q.2 b)
    = ((cLine a).coordChange p.1 r.1 b).prodMap ((cLine a).coordChange p.2 r.2 b)
  rw [prodMap_comp_prodMapBlk, cLineCT_comp a p.1 q.1 r.1 b, cLineCT_comp a p.2 q.2 r.2 b]

lemma tgtB_chg_comp (a : ℤ) (p q r : Bool × Bool) (b : S4) :
    (tgtB a).coordChange q r b ∘SL (tgtB a).coordChange p q b = (tgtB a).coordChange p r b := by
  show ((cLine (2 * a)).coordChange q.1 r.1 b).prodMap (ContinuousLinearMap.id ℂ E2) ∘SL
      ((cLine (2 * a)).coordChange p.1 q.1 b).prodMap (ContinuousLinearMap.id ℂ E2)
    = ((cLine (2 * a)).coordChange p.1 r.1 b).prodMap (ContinuousLinearMap.id ℂ E2)
  rw [prodMap_comp_prodMapBlk, cLineCT_comp (2 * a) p.1 q.1 r.1 b]
  simp only [ContinuousLinearMap.id_comp]

lemma srcB_chg_self (a : ℤ) (p : Bool × Bool) (b : S4) :
    (srcB a).coordChange p p b = 1 := by
  show ((cLine a).coordChange p.1 p.1 b).prodMap ((cLine a).coordChange p.2 p.2 b) = 1
  rw [cLine_coordChange, cLine_coordChange, cLineCT_self, cLineCT_self]
  ext x <;> simp

lemma tgtB_chg_self (a : ℤ) (p : Bool × Bool) (b : S4) :
    (tgtB a).coordChange p p b = 1 := by
  show ((cLine (2 * a)).coordChange p.1 p.1 b).prodMap (ContinuousLinearMap.id ℂ E2) = 1
  rw [cLine_coordChange, cLineCT_self]
  ext x <;> simp

/-- The transition functions of the two presentations are mutually inverse. -/
lemma srcB_chg_inv (a : ℤ) (i : Bool × Bool) (b : S4) :
    (srcB a).coordChange (false, false) i b ∘SL (srcB a).coordChange i (false, false) b = 1 := by
  have h := srcB_chg_comp a i (false, false) i b
  rw [srcB_chg_self] at h
  exact h

lemma tgtB_chg_inv (a : ℤ) (t : Bool × Bool) (b : S4) :
    (tgtB a).coordChange (false, false) t b ∘SL (tgtB a).coordChange t (false, false) b = 1 := by
  have h := tgtB_chg_comp a t (false, false) t b
  rw [tgtB_chg_self] at h
  exact h

lemma srcB_chg_inv' (a : ℤ) (i : Bool × Bool) (b : S4) :
    (srcB a).coordChange i (false, false) b ∘SL (srcB a).coordChange (false, false) i b = 1 := by
  have h := srcB_chg_comp a (false, false) i (false, false) b
  rw [srcB_chg_self] at h
  exact h

lemma tgtB_chg_inv' (a : ℤ) (t : Bool × Bool) (b : S4) :
    (tgtB a).coordChange t (false, false) b ∘SL (tgtB a).coordChange (false, false) t b = 1 := by
  have h := tgtB_chg_comp a (false, false) t (false, false) b
  rw [tgtB_chg_self] at h
  exact h

/-- The composition law, in the "target first" orientation needed for the condition (A). -/
lemma srcB_chg_comp' (a : ℤ) (i i' : Bool × Bool) (b : S4) :
    (srcB a).coordChange i (false, false) b ∘SL (srcB a).coordChange i' i b
      = (srcB a).coordChange i' (false, false) b :=
  srcB_chg_comp a i' i (false, false) b

lemma tgtB_chg_comp' (a : ℤ) (t t' : Bool × Bool) (b : S4) :
    (tgtB a).coordChange t t' b ∘SL (tgtB a).coordChange (false, false) t b
      = (tgtB a).coordChange (false, false) t' b :=
  tgtB_chg_comp a (false, false) t t' b

lemma tgtB_chg_comp'' (a : ℤ) (t t' : Bool × Bool) (b : S4) :
    (tgtB a).coordChange t (false, false) b ∘SL (tgtB a).coordChange t' t b
      = (tgtB a).coordChange t' (false, false) b :=
  tgtB_chg_comp a t' t (false, false) b


/-! ## §4. The block rotation and the interpolated core `H` -/

/-- `t ↦ cos (π t / 2)`. -/
def rotC (t : ℝ) : ℝ := Real.cos (Real.pi * t / 2)

/-- `t ↦ sin (π t / 2)`. -/
def rotS (t : ℝ) : ℝ := Real.sin (Real.pi * t / 2)

lemma rotC_sq_add_rotS_sq (t : ℝ) : rotC t ^ 2 + rotS t ^ 2 = 1 := Real.cos_sq_add_sin_sq _

lemma rotC_zero : rotC 0 = 1 := by simp [rotC]
lemma rotS_zero : rotS 0 = 0 := by simp [rotS]
lemma rotC_one : rotC 1 = 0 := by rw [rotC, mul_one]; exact Real.cos_pi_div_two
lemma rotS_one : rotS 1 = 1 := by rw [rotS, mul_one]; exact Real.sin_pi_div_two

/-- The "quarter turn" `J (x,y) = (-y, x)` of the block fibre. -/
def blkJ : Blk →L[ℂ] Blk :=
  ((-1 : ℂ) • ContinuousLinearMap.snd ℂ E2 E2).prod (ContinuousLinearMap.fst ℂ E2 E2)

@[simp] lemma blkJ_apply (x y : E2) : blkJ (x, y) = (-y, x) := by
  simp [blkJ]

lemma blkJ_mul_self : blkJ * blkJ = -(1 : Blk →L[ℂ] Blk) := by
  rw [ContinuousLinearMap.mul_def]
  refine ContinuousLinearMap.ext (fun p => ?_)
  obtain ⟨x, y⟩ := p
  simp only [ContinuousLinearMap.comp_apply, blkJ_apply, ContinuousLinearMap.neg_apply,
    one_apply_eq_self]
  rfl

/-- The block rotation `R(c,s) = c·1 + s·J = [[c,-s],[s,c]]`. -/
def blkRot (c s : ℝ) : Blk →L[ℂ] Blk :=
  (c : ℂ) • (1 : Blk →L[ℂ] Blk) + (s : ℂ) • blkJ

@[simp] lemma blkRot_apply (c s : ℝ) (x y : E2) :
    blkRot c s (x, y) = ((c : ℂ) • x - (s : ℂ) • y, (s : ℂ) • x + (c : ℂ) • y) := by
  simp only [blkRot, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    one_apply_eq_self, blkJ_apply, Prod.smul_mk, smul_neg]
  refine Prod.ext ?_ ?_ <;> simp [sub_eq_add_neg, add_comm]

lemma blkRot_one_zero : blkRot 1 0 = (1 : Blk →L[ℂ] Blk) := by
  refine ContinuousLinearMap.ext (fun p => ?_)
  obtain ⟨x, y⟩ := p
  simp

lemma blkRot_zero_one : blkRot 0 1 = blkJ := by
  refine ContinuousLinearMap.ext (fun p => ?_)
  obtain ⟨x, y⟩ := p
  simp

lemma blkRot_zero_neg_one : blkRot 0 (-1) = -blkJ := by
  refine ContinuousLinearMap.ext (fun p => ?_)
  obtain ⟨x, y⟩ := p
  simp

/-- The scalar identity behind the rotation. -/
lemma ofReal_sq_add (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (c : ℂ) * (c : ℂ) + (s : ℂ) * (s : ℂ) = 1 := by
  have h' : c * c + s * s = 1 := by rw [← pow_two, ← pow_two, h]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_add, h', Complex.ofReal_one]

lemma ofReal_sq_eq (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (c : ℂ) * (c : ℂ) = 1 - (s : ℂ) * (s : ℂ) := by
  have h2 := ofReal_sq_add c s h
  calc (c : ℂ) * (c : ℂ) = ((c : ℂ) * (c : ℂ) + (s : ℂ) * (s : ℂ)) - (s : ℂ) * (s : ℂ) := by ring
    _ = 1 - (s : ℂ) * (s : ℂ) := by rw [h2]

/-- `R(c,s) · R(c,-s) = 1` when `c² + s² = 1`. -/
lemma blkRot_mul_inv (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    blkRot c s * blkRot c (-s) = 1 := by
  have hc := ofReal_sq_eq c s h
  rw [ContinuousLinearMap.mul_def]
  refine ContinuousLinearMap.ext (fun p => ?_)
  obtain ⟨x, y⟩ := p
  simp only [ContinuousLinearMap.comp_apply, blkRot_apply, ContinuousLinearMap.one_apply,
    Complex.ofReal_neg, neg_neg, smul_sub, smul_add, smul_neg, neg_smul, smul_smul, neg_sub,
    sub_neg_eq_add, Prod.fst_sub, Prod.snd_sub, Prod.fst_add, Prod.snd_add, Prod.fst_neg,
    Prod.snd_neg, Prod.fst_smul, Prod.snd_smul]
  refine Prod.ext ?_ ?_ <;>
    · rw [hc]
      module

lemma blkRot_comp_inv_left (t : ℝ) :
    blkRot (rotC t) (rotS t) * blkRot (rotC t) (-(rotS t)) = 1 :=
  blkRot_mul_inv _ _ (rotC_sq_add_rotS_sq t)

lemma blkRot_comp_inv_right (t : ℝ) :
    blkRot (rotC t) (-(rotS t)) * blkRot (rotC t) (rotS t) = 1 := by
  have h := blkRot_mul_inv (rotC t) (-(rotS t)) (by
    have := rotC_sq_add_rotS_sq t
    nlinarith [this])
  rwa [neg_neg] at h

/-! ### The diagonal factors -/

/-- `diag(1, Mmat (uDir b ^ a))`. -/
def blkD (a : ℤ) (b : S4) : Blk →L[ℂ] Blk :=
  (1 : E2 →L[ℂ] E2).prodMap (Mmat (uDir b ^ a))

/-- `diag(Mmat (uDir b ^ -a), 1)`. -/
def blkF (a : ℤ) (b : S4) : Blk →L[ℂ] Blk :=
  (Mmat (uDir b ^ (-a))).prodMap (1 : E2 →L[ℂ] E2)

/-- `diag(Mmat (uDir b ^ a), 1)`. -/
def blkFinv (a : ℤ) (b : S4) : Blk →L[ℂ] Blk :=
  (Mmat (uDir b ^ a)).prodMap (1 : E2 →L[ℂ] E2)

/-- `diag(1, Mmat (uDir b ^ -a))`. -/
def blkDinv (a : ℤ) (b : S4) : Blk →L[ℂ] Blk :=
  (1 : E2 →L[ℂ] E2).prodMap (Mmat (uDir b ^ (-a)))

lemma prodMap_one_one : (1 : E2 →L[ℂ] E2).prodMap (1 : E2 →L[ℂ] E2) = (1 : Blk →L[ℂ] Blk) := by
  refine ContinuousLinearMap.ext (fun p => ?_)
  obtain ⟨x, y⟩ := p
  simp [ContinuousLinearMap.coe_prodMap']

/-- The monoid form of the block composition law. -/
lemma prodMap_mul (A₁ A₂ B₁ B₂ : E2 →L[ℂ] E2) :
    (A₁.prodMap A₂) * (B₁.prodMap B₂) = (A₁ * B₁).prodMap (A₂ * B₂) := by
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def,
    prodMap_comp_prodMapBlk]

lemma Mmat_mul_neg_mul (a : ℤ) (b : S4) :
    Mmat (uDir b ^ a) * Mmat (uDir b ^ (-a)) = 1 := by
  rw [ContinuousLinearMap.mul_def]; exact Mmat_zpow_mul_neg a b

lemma Mmat_neg_mul_mul (a : ℤ) (b : S4) :
    Mmat (uDir b ^ (-a)) * Mmat (uDir b ^ a) = 1 := by
  rw [ContinuousLinearMap.mul_def]; exact Mmat_zpow_mul_neg' a b

section Diag

variable (a : ℤ) (b : S4)

lemma blkD_comp_blkDinv : blkD a b * blkDinv a b = 1 := by
  rw [blkD, blkDinv, prodMap_mul, mul_one, Mmat_mul_neg_mul a b, prodMap_one_one]

lemma blkDinv_comp_blkD : blkDinv a b * blkD a b = 1 := by
  rw [blkD, blkDinv, prodMap_mul, mul_one, Mmat_neg_mul_mul a b, prodMap_one_one]

lemma blkF_comp_blkFinv : blkF a b * blkFinv a b = 1 := by
  rw [blkF, blkFinv, prodMap_mul, mul_one, Mmat_neg_mul_mul a b, prodMap_one_one]

lemma blkFinv_comp_blkF : blkFinv a b * blkF a b = 1 := by
  rw [blkFinv, blkF, prodMap_mul, mul_one, Mmat_mul_neg_mul a b, prodMap_one_one]

/-- `J · diag(1,M) · J⁻¹ = diag(M,1)`. -/
lemma blkJ_conj_blkD : blkJ * blkD a b * (-blkJ) = blkFinv a b := by
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, blkJ, blkD, blkFinv]
  refine ContinuousLinearMap.ext (fun p => ?_)
  obtain ⟨x, y⟩ := p
  simp [ContinuousLinearMap.coe_prodMap']

/-- `J · diag(M⁻¹,1) · J⁻¹ = diag(1,M⁻¹)`. -/
lemma blkJ_conj_blkF : blkJ * blkF a b * (-blkJ) = blkDinv a b := by
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, blkJ, blkF, blkDinv]
  refine ContinuousLinearMap.ext (fun p => ?_)
  obtain ⟨x, y⟩ := p
  simp [ContinuousLinearMap.coe_prodMap']

/-- `J · diag(1,M⁻¹) · J⁻¹ = diag(M⁻¹,1)`. -/
lemma blkJ_conj_blkDinv : blkJ * blkDinv a b * (-blkJ) = blkF a b := by
  rw [ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def, blkJ, blkDinv, blkF]
  refine ContinuousLinearMap.ext (fun p => ?_)
  obtain ⟨x, y⟩ := p
  simp [ContinuousLinearMap.coe_prodMap']

end Diag

/-- The interpolation parameter: `1` near the origin `↑0`, `0` near `∞`. -/
def sigT (b : S4) : ℝ := 1 - sigR b

lemma sigT_of_le_one {p : S4} (h : ‖coord0 p‖ ≤ 1) : sigT p = 1 := by
  rw [sigT, sigR_of_le_one h, sub_zero]

lemma sigT_of_two_le {p : S4} (h : 2 ≤ ‖coord0 p‖) : sigT p = 0 := by
  rw [sigT, sigR_of_two_le h, sub_self]

/-- **The interpolated core gauge** `H b = R(σ b) · diag(1,M_a) · R(σ b)⁻¹ · diag(M_a⁻¹,1)`. -/
def blkH (a : ℤ) (b : S4) : Blk →L[ℂ] Blk :=
  blkRot (rotC (sigT b)) (rotS (sigT b)) *
    (blkD a b * (blkRot (rotC (sigT b)) (-(rotS (sigT b))) * blkF a b))

/-- **The inverse of the interpolated core gauge**. -/
def blkHinv (a : ℤ) (b : S4) : Blk →L[ℂ] Blk :=
  blkFinv a b *
    (blkRot (rotC (sigT b)) (rotS (sigT b)) *
      (blkDinv a b * blkRot (rotC (sigT b)) (-(rotS (sigT b)))))

lemma blkH_mul_blkHinv (a : ℤ) (b : S4) : blkH a b * blkHinv a b = 1 := by
  have hR : blkRot (rotC (sigT b)) (rotS (sigT b)) *
      blkRot (rotC (sigT b)) (-(rotS (sigT b))) = 1 := blkRot_comp_inv_left (sigT b)
  have hRi : blkRot (rotC (sigT b)) (-(rotS (sigT b))) *
      blkRot (rotC (sigT b)) (rotS (sigT b)) = 1 := blkRot_comp_inv_right (sigT b)
  have hF : blkF a b * blkFinv a b = 1 := blkF_comp_blkFinv a b
  have hD : blkD a b * blkDinv a b = 1 := blkD_comp_blkDinv a b
  simp only [blkH, blkHinv]
  calc (blkRot (rotC (sigT b)) (rotS (sigT b)) *
        (blkD a b * (blkRot (rotC (sigT b)) (-(rotS (sigT b))) * blkF a b))) *
        (blkFinv a b * (blkRot (rotC (sigT b)) (rotS (sigT b)) *
          (blkDinv a b * blkRot (rotC (sigT b)) (-(rotS (sigT b))))))
      = blkRot (rotC (sigT b)) (rotS (sigT b)) *
          (blkD a b * (blkRot (rotC (sigT b)) (-(rotS (sigT b))) * (blkF a b * blkFinv a b))) *
          (blkRot (rotC (sigT b)) (rotS (sigT b)) *
            (blkDinv a b * blkRot (rotC (sigT b)) (-(rotS (sigT b))))) := by
        noncomm_ring
    _ = blkRot (rotC (sigT b)) (rotS (sigT b)) *
          (blkD a b * (blkRot (rotC (sigT b)) (-(rotS (sigT b))) * 1)) *
          (blkRot (rotC (sigT b)) (rotS (sigT b)) *
            (blkDinv a b * blkRot (rotC (sigT b)) (-(rotS (sigT b))))) := by
        rw [hF]
    _ = blkRot (rotC (sigT b)) (rotS (sigT b)) *
          ((blkD a b * blkRot (rotC (sigT b)) (-(rotS (sigT b)))) *
            (blkRot (rotC (sigT b)) (rotS (sigT b)) *
              (blkDinv a b * blkRot (rotC (sigT b)) (-(rotS (sigT b)))))) := by
        rw [mul_one]
        noncomm_ring
    _ = blkRot (rotC (sigT b)) (rotS (sigT b)) *
          (blkD a b * ((blkRot (rotC (sigT b)) (-(rotS (sigT b))) *
            blkRot (rotC (sigT b)) (rotS (sigT b))) *
            (blkDinv a b * blkRot (rotC (sigT b)) (-(rotS (sigT b)))))) := by
        noncomm_ring
    _ = blkRot (rotC (sigT b)) (rotS (sigT b)) *
          (blkD a b * (1 * (blkDinv a b * blkRot (rotC (sigT b)) (-(rotS (sigT b)))))) := by
        rw [hRi]
    _ = blkRot (rotC (sigT b)) (rotS (sigT b)) * (blkD a b * blkDinv a b) *
          blkRot (rotC (sigT b)) (-(rotS (sigT b))) := by
        rw [one_mul]
        noncomm_ring
    _ = blkRot (rotC (sigT b)) (rotS (sigT b)) * 1 *
          blkRot (rotC (sigT b)) (-(rotS (sigT b))) := by rw [hD]
    _ = blkRot (rotC (sigT b)) (rotS (sigT b)) *
          blkRot (rotC (sigT b)) (-(rotS (sigT b))) := by noncomm_ring
    _ = 1 := hR

lemma blkHinv_mul_blkH (a : ℤ) (b : S4) : blkHinv a b * blkH a b = 1 := by
  have hR : blkRot (rotC (sigT b)) (rotS (sigT b)) *
      blkRot (rotC (sigT b)) (-(rotS (sigT b))) = 1 := blkRot_comp_inv_left (sigT b)
  have hRi : blkRot (rotC (sigT b)) (-(rotS (sigT b))) *
      blkRot (rotC (sigT b)) (rotS (sigT b)) = 1 := blkRot_comp_inv_right (sigT b)
  have hF : blkFinv a b * blkF a b = 1 := blkFinv_comp_blkF a b
  have hD : blkDinv a b * blkD a b = 1 := blkDinv_comp_blkD a b
  simp only [blkH, blkHinv]
  calc (blkFinv a b * (blkRot (rotC (sigT b)) (rotS (sigT b)) *
        (blkDinv a b * blkRot (rotC (sigT b)) (-(rotS (sigT b)))))) *
        (blkRot (rotC (sigT b)) (rotS (sigT b)) *
          (blkD a b * (blkRot (rotC (sigT b)) (-(rotS (sigT b))) * blkF a b)))
      = blkFinv a b * (blkRot (rotC (sigT b)) (rotS (sigT b)) *
          (blkDinv a b * (blkRot (rotC (sigT b)) (-(rotS (sigT b))) *
            blkRot (rotC (sigT b)) (rotS (sigT b)))) *
          (blkD a b * (blkRot (rotC (sigT b)) (-(rotS (sigT b))) * blkF a b))) := by
        noncomm_ring
    _ = blkFinv a b * (blkRot (rotC (sigT b)) (rotS (sigT b)) *
          (blkDinv a b * 1) *
          (blkD a b * (blkRot (rotC (sigT b)) (-(rotS (sigT b))) * blkF a b))) := by
        rw [hRi]
    _ = blkFinv a b * ((blkRot (rotC (sigT b)) (rotS (sigT b)) *
          blkDinv a b) * (blkD a b * blkRot (rotC (sigT b)) (-(rotS (sigT b))))) * blkF a b := by
        rw [mul_one]
        noncomm_ring
    _ = blkFinv a b * (blkRot (rotC (sigT b)) (rotS (sigT b)) *
          (blkDinv a b * blkD a b)) *
          (blkRot (rotC (sigT b)) (-(rotS (sigT b))) * blkF a b) := by noncomm_ring
    _ = blkFinv a b * (blkRot (rotC (sigT b)) (rotS (sigT b)) * 1) *
          (blkRot (rotC (sigT b)) (-(rotS (sigT b))) * blkF a b) := by rw [hD]
    _ = blkFinv a b * (blkRot (rotC (sigT b)) (rotS (sigT b)) *
          blkRot (rotC (sigT b)) (-(rotS (sigT b)))) * blkF a b := by
        rw [mul_one]
        noncomm_ring
    _ = blkFinv a b * 1 * blkF a b := by rw [hR]
    _ = blkFinv a b * blkF a b := by noncomm_ring
    _ = 1 := hF

/-- On the `σ = 1` locus (near the origin) the core is the identity. -/
lemma blkH_of_sigT_one (a : ℤ) {b : S4} (h : sigT b = 1) : blkH a b = 1 := by
  have hconj : blkJ * blkD a b * (-blkJ) = blkFinv a b := blkJ_conj_blkD a b
  have hF : blkFinv a b * blkF a b = 1 := blkFinv_comp_blkF a b
  rw [blkH, h, rotC_one, rotS_one, show -(1 : ℝ) = -1 from rfl, blkRot_zero_one,
    blkRot_zero_neg_one]
  calc blkJ * (blkD a b * (-blkJ * blkF a b))
      = (blkJ * blkD a b * (-blkJ)) * blkF a b := by noncomm_ring
    _ = blkFinv a b * blkF a b := by rw [hconj]
    _ = 1 := hF

/-- On the `σ = 1` locus the inverse core is the identity. -/
lemma blkHinv_of_sigT_one (a : ℤ) {b : S4} (h : sigT b = 1) : blkHinv a b = 1 := by
  have hconj : blkJ * blkDinv a b * (-blkJ) = blkF a b := blkJ_conj_blkDinv a b
  have hF : blkFinv a b * blkF a b = 1 := blkFinv_comp_blkF a b
  rw [blkHinv, h, rotC_one, rotS_one, show -(1 : ℝ) = -1 from rfl, blkRot_zero_one,
    blkRot_zero_neg_one]
  calc blkFinv a b * (blkJ * (blkDinv a b * -blkJ))
      = blkFinv a b * (blkJ * blkDinv a b * (-blkJ)) := by noncomm_ring
    _ = blkFinv a b * blkF a b := by rw [hconj]
    _ = 1 := hF

/-- On the `σ = 0` locus (near `∞`) the core is the compensator `diag(M_a⁻¹, M_a)`. -/
lemma blkH_of_sigT_zero (a : ℤ) {b : S4} (h : sigT b = 0) : blkH a b = blkD a b * blkF a b := by
  rw [blkH, h, rotC_zero, rotS_zero, neg_zero, blkRot_one_zero]
  noncomm_ring

/-- On the `σ = 0` locus the inverse core is `diag(M_a, M_a⁻¹)`. -/
lemma blkHinv_of_sigT_zero (a : ℤ) {b : S4} (h : sigT b = 0) :
    blkHinv a b = blkFinv a b * blkDinv a b := by
  rw [blkHinv, h, rotC_zero, rotS_zero, neg_zero, blkRot_one_zero]
  noncomm_ring


/-! ## §6. The Mmat algebra at `∞`, and the two presentations of the gauge -/

lemma cLine_chg_false_true (a : ℤ) (b : S4) :
    (cLine a).coordChange false true b = Mmat (uDir b ^ a) := by
  rw [cLine_coordChange, cLineCT_false_true]

lemma cLine_chg_true_false (a : ℤ) (b : S4) :
    (cLine a).coordChange true false b = Mmat (uDir b ^ (-a)) := by
  rw [cLine_coordChange, cLineCT_true_false]

lemma Mmat_apply_mul (q : Quaternion ℝ) (hq : q ≠ 0) (m n : ℤ) (v : E2) :
    Mmat (q ^ m) (Mmat (q ^ n) v) = Mmat (q ^ (m + n)) v := by
  rw [← ContinuousLinearMap.comp_apply, Mmat_mul, zpow_add₀ hq]

lemma Mmat_apply_a_a (a : ℤ) (b : S4) (v : E2) :
    Mmat (uDir b ^ a) (Mmat (uDir b ^ a) v) = Mmat (uDir b ^ (2 * a)) v := by
  rw [Mmat_apply_mul (uDir b) (uDir_ne_zero b) a a v]
  congr 2
  ring_nf

lemma Mmat_apply_neg_a_neg_a (a : ℤ) (b : S4) (v : E2) :
    Mmat (uDir b ^ (-a)) (Mmat (uDir b ^ (-a)) v) = Mmat (uDir b ^ (-(2 * a))) v := by
  rw [Mmat_apply_mul (uDir b) (uDir_ne_zero b) (-a) (-a) v]
  congr 2
  ring_nf

lemma Mmat_apply_a_neg (a : ℤ) (b : S4) (v : E2) :
    Mmat (uDir b ^ a) (Mmat (uDir b ^ (-a)) v) = v := by
  rw [Mmat_apply_mul (uDir b) (uDir_ne_zero b) a (-a) v, add_neg_cancel, zpow_zero]
  simp

lemma Mmat_apply_neg_a_a (a : ℤ) (b : S4) (v : E2) :
    Mmat (uDir b ^ (-a)) (Mmat (uDir b ^ a) v) = v := by
  rw [Mmat_apply_mul (uDir b) (uDir_ne_zero b) (-a) a v, neg_add_cancel, zpow_zero]
  simp

lemma Mmat_apply_2a_neg (a : ℤ) (b : S4) (v : E2) :
    Mmat (uDir b ^ (2 * a)) (Mmat (uDir b ^ (-(2 * a))) v) = v := by
  rw [Mmat_apply_mul (uDir b) (uDir_ne_zero b) (2 * a) (-(2 * a)) v, add_neg_cancel, zpow_zero]
  simp

lemma coord0_infty : coord0 (OnePoint.infty : S4) = 0 := rfl

lemma uDir_infty : uDir (OnePoint.infty : S4) = 1 := by
  rw [uDir, coord0_infty]
  show (((Submission.Milnor.unitDir (0 : EuclideanSpace ℝ (Fin 4)) :
    Submission.Milnor.QS3) : Quaternion ℝ)) = 1
  rw [Submission.Milnor.unitDir]
  simp

lemma sigT_infty : sigT (OnePoint.infty : S4) = 1 :=
  sigT_of_le_one (by rw [coord0_infty, norm_zero]; norm_num)

/-- The gauge of the rank-two shift. -/
def Ψ (a : ℤ) (i t : Bool × Bool) (b : S4) : Blk →L[ℂ] Blk :=
  (tgtB a).coordChange (false, false) t b *
    (blkH a b * (srcB a).coordChange i (false, false) b)

/-- Its pointwise inverse. -/
def Ψinv (a : ℤ) (i t : Bool × Bool) (b : S4) : Blk →L[ℂ] Blk :=
  (srcB a).coordChange (false, false) i b *
    (blkHinv a b * (tgtB a).coordChange t (false, false) b)

lemma tgtB_chg_zero (a : ℤ) (t : Bool × Bool) (b : S4) :
    (tgtB a).coordChange (false, false) t b =
      ((cLine (2 * a)).coordChange false t.1 b).prodMap (1 : E2 →L[ℂ] E2) := by
  show ((cLine (2 * a)).coordChange false t.1 b).prodMap
      ((trivialVectorBundleCore ℂ S4 E2 Bool).coordChange false t.2 b) = _
  rw [show (trivialVectorBundleCore ℂ S4 E2 Bool).coordChange false t.2 b
      = ContinuousLinearMap.id ℂ E2 from rfl]
  rfl

lemma tgtB_chg_zero' (a : ℤ) (t : Bool × Bool) (b : S4) :
    (tgtB a).coordChange t (false, false) b =
      ((cLine (2 * a)).coordChange t.1 false b).prodMap (1 : E2 →L[ℂ] E2) := by
  show ((cLine (2 * a)).coordChange t.1 false b).prodMap
      ((trivialVectorBundleCore ℂ S4 E2 Bool).coordChange t.2 false b) = _
  rw [show (trivialVectorBundleCore ℂ S4 E2 Bool).coordChange t.2 false b
      = ContinuousLinearMap.id ℂ E2 from rfl]
  rfl

lemma srcB_chg_zero (a : ℤ) (i : Bool × Bool) (b : S4) :
    (srcB a).coordChange i (false, false) b =
      ((cLine a).coordChange i.1 false b).prodMap ((cLine a).coordChange i.2 false b) := rfl

lemma srcB_chg_zero' (a : ℤ) (i : Bool × Bool) (b : S4) :
    (srcB a).coordChange (false, false) i b =
      ((cLine a).coordChange false i.1 b).prodMap ((cLine a).coordChange false i.2 b) := rfl

/-- At a point of radius at least `2`, the `(1,1)`-gauge takes the value `1`. -/
lemma Ψ_eleven_of_two_le (a : ℤ) {t : Bool × Bool} (ht : t.1 = true) {b : S4}
    (hb : 2 ≤ ‖coord0 b‖) : Ψ a (true, true) t b = 1 := by
  rw [Ψ, tgtB_chg_zero, ht, srcB_chg_zero, blkH_of_sigT_zero a (sigT_of_two_le hb),
    blkD, blkF, cLine_chg_false_true (2 * a), cLine_chg_true_false a]
  refine ContinuousLinearMap.ext (fun p => ?_)
  obtain ⟨x, y⟩ := p
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply, ContinuousLinearMap.one_apply,
    Mmat_apply_a_a a b, Mmat_apply_neg_a_neg_a a b, Mmat_apply_2a_neg a b,
    Mmat_apply_a_neg a b]

/-- At `∞` the `(1,1)`-gauge takes the value `1`. -/
lemma Ψ_eleven_infty (a : ℤ) {t : Bool × Bool} (ht : t.1 = true) :
    Ψ a (true, true) t OnePoint.infty = 1 := by
  rw [Ψ, tgtB_chg_zero, ht, srcB_chg_zero, blkH_of_sigT_one a sigT_infty,
    cLine_chg_false_true (2 * a), cLine_chg_true_false a, uDir_infty]
  simp [prodMap_one_one]

/-- At a point of radius at least `2`, the `(1,1)`-inverse gauge takes the value `1`. -/
lemma Ψinv_eleven_of_two_le (a : ℤ) {t : Bool × Bool} (ht : t.1 = true) {b : S4}
    (hb : 2 ≤ ‖coord0 b‖) : Ψinv a (true, true) t b = 1 := by
  rw [Ψinv, srcB_chg_zero', tgtB_chg_zero', ht, blkHinv_of_sigT_zero a (sigT_of_two_le hb),
    blkFinv, blkDinv, cLine_chg_false_true a, cLine_chg_true_false (2 * a)]
  refine ContinuousLinearMap.ext (fun p => ?_)
  obtain ⟨x, y⟩ := p
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_prodMap', Prod.map_apply, ContinuousLinearMap.one_apply,
    Mmat_apply_a_a a b, Mmat_apply_2a_neg a b, Mmat_apply_a_neg a b,
    Mmat_apply_neg_a_a a b]

/-- At `∞` the `(1,1)`-inverse gauge takes the value `1`. -/
lemma Ψinv_eleven_infty (a : ℤ) {t : Bool × Bool} (ht : t.1 = true) :
    Ψinv a (true, true) t OnePoint.infty = 1 := by
  rw [Ψinv, srcB_chg_zero', tgtB_chg_zero', ht, blkHinv_of_sigT_one a sigT_infty,
    cLine_chg_false_true a, cLine_chg_true_false (2 * a), uDir_infty]
  simp [prodMap_one_one]


/-! ## §7. Continuity -/

lemma continuous_rotC : Continuous rotC := Real.continuous_cos.comp (by fun_prop)
lemma continuous_rotS : Continuous rotS := Real.continuous_sin.comp (by fun_prop)

/-- Composition of continuous families of endomorphisms of the block fibre. -/
lemma mul_clm {X : Type*} [TopologicalSpace X] {s : Set X}
    {f g : X → Blk →L[ℂ] Blk} (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => f x * g x) s := by
  simpa only [ContinuousLinearMap.mul_def] using hf.clm_comp hg

lemma continuousOn_sigT : ContinuousOn sigT hemi0 := by
  unfold sigT
  exact continuousOn_const.sub
    (continuous_sigFun.comp_continuousOn (continuous_norm.comp_continuousOn continuousOn_coord0))

lemma continuousOn_rotC_sigT : ContinuousOn (fun b => rotC (sigT b)) hemi0 :=
  continuous_rotC.comp_continuousOn continuousOn_sigT

lemma continuousOn_rotS_sigT : ContinuousOn (fun b => rotS (sigT b)) hemi0 :=
  continuous_rotS.comp_continuousOn continuousOn_sigT

lemma continuousOn_blkRot_sigT :
    ContinuousOn (fun b => blkRot (rotC (sigT b)) (rotS (sigT b))) hemi0 := by
  have h1 : ContinuousOn (fun b => ((rotC (sigT b) : ℝ) : ℂ)) hemi0 :=
    Complex.continuous_ofReal.comp_continuousOn continuousOn_rotC_sigT
  have h2 : ContinuousOn (fun b => ((rotS (sigT b) : ℝ) : ℂ)) hemi0 :=
    Complex.continuous_ofReal.comp_continuousOn continuousOn_rotS_sigT
  have h3 : ContinuousOn (fun b : S4 => ((rotC (sigT b) : ℝ) : ℂ) • (1 : Blk →L[ℂ] Blk)
      + ((rotS (sigT b) : ℝ) : ℂ) • blkJ) hemi0 :=
    (h1.smul continuousOn_const).add (h2.smul continuousOn_const)
  simpa only [blkRot] using h3

lemma continuousOn_blkRot_sigT_neg :
    ContinuousOn (fun b => blkRot (rotC (sigT b)) (-(rotS (sigT b)))) hemi0 := by
  have h1 : ContinuousOn (fun b => ((rotC (sigT b) : ℝ) : ℂ)) hemi0 :=
    Complex.continuous_ofReal.comp_continuousOn continuousOn_rotC_sigT
  have h2 : ContinuousOn (fun b => ((-(rotS (sigT b)) : ℝ) : ℂ)) hemi0 :=
    Complex.continuous_ofReal.comp_continuousOn continuousOn_rotS_sigT.neg
  have h3 : ContinuousOn (fun b : S4 => ((rotC (sigT b) : ℝ) : ℂ) • (1 : Blk →L[ℂ] Blk)
      + (((-(rotS (sigT b)) : ℝ) : ℂ)) • blkJ) hemi0 :=
    (h1.smul continuousOn_const).add (h2.smul continuousOn_const)
  simpa only [blkRot] using h3

lemma continuousOn_blkD (a : ℤ) : ContinuousOn (fun b => blkD a b) (hemi0 ∩ hemi1) := by
  exact (continuousOn_const : ContinuousOn (fun _ : S4 => (1 : E2 →L[ℂ] E2))
    (hemi0 ∩ hemi1)).prod_mapL ℂ (continuous_Mmat.comp_continuousOn
      (continuousOn_uDir.zpow₀ a (fun p _ => Or.inl (uDir_ne_zero p))))

lemma continuousOn_blkF (a : ℤ) : ContinuousOn (fun b => blkF a b) (hemi0 ∩ hemi1) := by
  exact (continuous_Mmat.comp_continuousOn
    (continuousOn_uDir.zpow₀ (-a) (fun p _ => Or.inl (uDir_ne_zero p)))).prod_mapL ℂ
      (continuousOn_const : ContinuousOn (fun _ : S4 => (1 : E2 →L[ℂ] E2)) (hemi0 ∩ hemi1))

lemma continuousOn_blkDinv (a : ℤ) : ContinuousOn (fun b => blkDinv a b) (hemi0 ∩ hemi1) := by
  exact (continuousOn_const : ContinuousOn (fun _ : S4 => (1 : E2 →L[ℂ] E2))
    (hemi0 ∩ hemi1)).prod_mapL ℂ (continuous_Mmat.comp_continuousOn
      (continuousOn_uDir.zpow₀ (-a) (fun p _ => Or.inl (uDir_ne_zero p))))

lemma continuousOn_blkFinv (a : ℤ) : ContinuousOn (fun b => blkFinv a b) (hemi0 ∩ hemi1) := by
  exact (continuous_Mmat.comp_continuousOn
    (continuousOn_uDir.zpow₀ a (fun p _ => Or.inl (uDir_ne_zero p)))).prod_mapL ℂ
      (continuousOn_const : ContinuousOn (fun _ : S4 => (1 : E2 →L[ℂ] E2)) (hemi0 ∩ hemi1))

lemma continuousOn_blkH_equator (a : ℤ) :
    ContinuousOn (fun b => blkH a b) (hemi0 ∩ hemi1) := by
  have hR := continuousOn_blkRot_sigT.mono
    (Set.inter_subset_left : hemi0 ∩ hemi1 ⊆ hemi0)
  have hRi := continuousOn_blkRot_sigT_neg.mono
    (Set.inter_subset_left : hemi0 ∩ hemi1 ⊆ hemi0)
  have h := mul_clm hR (mul_clm (continuousOn_blkD a)
    (mul_clm hRi (continuousOn_blkF a)))
  simpa only [blkH] using h

lemma continuousOn_blkHinv_equator (a : ℤ) :
    ContinuousOn (fun b => blkHinv a b) (hemi0 ∩ hemi1) := by
  have hR := continuousOn_blkRot_sigT.mono
    (Set.inter_subset_left : hemi0 ∩ hemi1 ⊆ hemi0)
  have hRi := continuousOn_blkRot_sigT_neg.mono
    (Set.inter_subset_left : hemi0 ∩ hemi1 ⊆ hemi0)
  have h := mul_clm (continuousOn_blkFinv a) (mul_clm hR
    (mul_clm (continuousOn_blkDinv a) hRi))
  simpa only [blkHinv] using h

lemma eventually_sigT_eq_one :
    ∀ᶠ b : S4 in 𝓝 (↑(0 : EuclideanSpace ℝ (Fin 4)) : S4), sigT b = 1 := by
  have hmem : (fun x : EuclideanSpace ℝ (Fin 4) => (x : S4)) ''
      Metric.ball (0 : EuclideanSpace ℝ (Fin 4)) 1 ∈
      𝓝 (↑(0 : EuclideanSpace ℝ (Fin 4)) : S4) :=
    OnePoint.isOpenEmbedding_coe.isOpenMap.image_mem_nhds
      (Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin 4)) one_pos)
  refine Filter.eventually_of_mem hmem ?_
  rintro b ⟨x, hx, rfl⟩
  refine sigT_of_le_one ?_
  rw [coord0_some]
  exact le_of_lt (by simpa [Metric.mem_ball, dist_zero_right] using hx)

lemma continuousOn_blkH_hemi0 (a : ℤ) : ContinuousOn (fun b => blkH a b) hemi0 := by
  intro b hb
  rcases eq_or_ne b (↑(0 : EuclideanSpace ℝ (Fin 4)) : S4) with rfl | hb0
  · have hev : (fun b : S4 => blkH a b) =ᶠ[𝓝[hemi0]
        (↑(0 : EuclideanSpace ℝ (Fin 4)) : S4)] (fun _ => 1) :=
      Filter.EventuallyEq.filter_mono
        (eventually_sigT_eq_one.mono (fun b hb => blkH_of_sigT_one a hb)) nhdsWithin_le_nhds
    have hx : blkH a (↑(0 : EuclideanSpace ℝ (Fin 4)) : S4) = 1 :=
      blkH_of_sigT_one a (sigT_of_le_one (by rw [coord0_some, norm_zero]; norm_num))
    exact ContinuousWithinAt.congr_of_eventuallyEq continuousWithinAt_const hev hx
  · have hmem : hemi0 ∩ hemi1 ∈ 𝓝 b :=
      IsOpen.mem_nhds (isOpen_hemi0.inter isOpen_hemi1) ⟨hb, hb0⟩
    exact ((continuousOn_blkH_equator a).continuousAt hmem).continuousWithinAt

lemma continuousOn_blkHinv_hemi0 (a : ℤ) : ContinuousOn (fun b => blkHinv a b) hemi0 := by
  intro b hb
  rcases eq_or_ne b (↑(0 : EuclideanSpace ℝ (Fin 4)) : S4) with rfl | hb0
  · have hev : (fun b : S4 => blkHinv a b) =ᶠ[𝓝[hemi0]
        (↑(0 : EuclideanSpace ℝ (Fin 4)) : S4)] (fun _ => 1) :=
      Filter.EventuallyEq.filter_mono
        (eventually_sigT_eq_one.mono (fun b hb => blkHinv_of_sigT_one a hb)) nhdsWithin_le_nhds
    have hx : blkHinv a (↑(0 : EuclideanSpace ℝ (Fin 4)) : S4) = 1 :=
      blkHinv_of_sigT_one a (sigT_of_le_one (by rw [coord0_some, norm_zero]; norm_num))
    exact ContinuousWithinAt.congr_of_eventuallyEq continuousWithinAt_const hev hx
  · have hmem : hemi0 ∩ hemi1 ∈ 𝓝 b :=
      IsOpen.mem_nhds (isOpen_hemi0.inter isOpen_hemi1) ⟨hb, hb0⟩
    exact ((continuousOn_blkHinv_equator a).continuousAt hmem).continuousWithinAt

/-- The set `{‖coord0 ·‖ > R} ∪ {∞}` is a neighbourhood of `∞`. -/
lemma nhds_infty_gt (R : ℝ) :
    ({b : S4 | R < ‖coord0 b‖} ∪ {OnePoint.infty}) ∈ 𝓝 (OnePoint.infty : S4) := by
  have hc : IsCompact (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) R) :=
    isCompact_closedBall _ _
  have hcl : IsClosed ((fun x : EuclideanSpace ℝ (Fin 4) => (x : S4)) ''
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) R : Set S4) :=
    (hc.image OnePoint.isOpenEmbedding_coe.continuous).isClosed
  refine Filter.mem_of_superset (hcl.isOpen_compl.mem_nhds ?_) ?_
  · rintro ⟨x, -, hx⟩
    exact Option.some_ne_none x hx
  · intro b hb
    rcases b with _ | x
    · exact Or.inr rfl
    · left
      have hx : ¬ (x ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 4)) R) :=
        fun h => hb ⟨x, h, rfl⟩
      rw [Metric.mem_closedBall, dist_zero_right] at hx
      change R < ‖coord0 (OnePoint.some x)‖
      rw [coord0_some]
      exact lt_of_not_ge hx

lemma Ψ_eleven_eventuallyEq (a : ℤ) (t : Bool × Bool) (ht : t.1 = true) :
    (fun b : S4 => Ψ a (true, true) t b) =ᶠ[𝓝 (OnePoint.infty : S4)] (fun _ => 1) := by
  refine Filter.eventually_of_mem (nhds_infty_gt 2) (fun b hb => ?_)
  rcases hb with hb | rfl
  · exact Ψ_eleven_of_two_le a ht (le_of_lt hb)
  · exact Ψ_eleven_infty a ht

lemma Ψinv_eleven_eventuallyEq (a : ℤ) (t : Bool × Bool) (ht : t.1 = true) :
    (fun b : S4 => Ψinv a (true, true) t b) =ᶠ[𝓝 (OnePoint.infty : S4)] (fun _ => 1) := by
  refine Filter.eventually_of_mem (nhds_infty_gt 2) (fun b hb => ?_)
  rcases hb with hb | rfl
  · exact Ψinv_eleven_of_two_le a ht (le_of_lt hb)
  · exact Ψinv_eleven_infty a ht

/-! ### The base sets of the two presentations -/

lemma srcB_baseSet (a : ℤ) (i : Bool × Bool) :
    (srcB a).baseSet i = (if i.1 then hemi1 else hemi0) ∩ (if i.2 then hemi1 else hemi0) := by
  rw [Work.Thom.bundleSum_baseSet, cLine_baseSet, cLine_baseSet]

lemma tgtB_baseSet (a : ℤ) (t : Bool × Bool) :
    (tgtB a).baseSet t = (if t.1 then hemi1 else hemi0) := by
  rw [Work.Thom.bundleSum_baseSet, cLine_baseSet]
  rw [show ((trivialVectorBundleCore ℂ S4 E2 Bool).baseSet t.2 : Set S4) = Set.univ from rfl]
  simp

/-- The equator is contained in every chart of the source presentation. -/
lemma equator_subset_srcB (a : ℤ) (i : Bool × Bool) :
    hemi0 ∩ hemi1 ⊆ (srcB a).baseSet i := by
  intro b hb
  rw [srcB_baseSet]
  refine ⟨?_, ?_⟩ <;>
    (cases i.1 <;> cases i.2 <;> simp only [Bool.false_eq_true, reduceIte] <;>
      first | exact hb.1 | exact hb.2)

/-- The equator is contained in every chart of the target presentation. -/
lemma equator_subset_tgtB (a : ℤ) (t : Bool × Bool) :
    hemi0 ∩ hemi1 ⊆ (tgtB a).baseSet t := by
  intro b hb
  rw [tgtB_baseSet]
  cases t.1 <;> simp only [Bool.false_eq_true, reduceIte] <;>
    (first | exact hb.1 | exact hb.2)

/-- `hemi0` is contained in the `(false,false)`-chart of the target presentation. -/
lemma hemi0_subset_tgtB_zero (a : ℤ) : hemi0 ⊆ (tgtB a).baseSet (false, false) := by
  intro b hb
  rw [tgtB_baseSet]
  exact hb

/-- `hemi0` is contained in the `(false,false)`-chart of the source presentation. -/
lemma hemi0_subset_srcB_zero (a : ℤ) : hemi0 ⊆ (srcB a).baseSet (false, false) := by
  intro b hb
  rw [srcB_baseSet]
  exact ⟨hb, hb⟩

lemma inter_hemi_subset (a1 a2 a3 : Bool) (h : ¬ (a1 = true ∧ a2 = true ∧ a3 = true)) :
    (((if a1 then hemi1 else hemi0) ∩ (if a2 then hemi1 else hemi0) ∩
      (if a3 then hemi1 else hemi0)) : Set S4) ⊆ hemi0 := by
  intro b hb
  obtain ⟨⟨h1, h2⟩, h3⟩ := hb
  cases a1 <;> cases a2 <;> cases a3 <;> simp_all [Set.mem_inter_iff]

lemma hemis_eq_hemi1 (a1 a2 a3 : Bool) (h1 : a1 = true) (h2 : a2 = true) (h3 : a3 = true) :
    (((if a1 then hemi1 else hemi0) ∩ (if a2 then hemi1 else hemi0) ∩
      (if a3 then hemi1 else hemi0)) : Set S4) = hemi1 := by
  rw [h1, h2, h3]
  simp [Set.inter_self]

lemma continuousOn_Ψ_equator (a : ℤ) (i t : Bool × Bool) :
    ContinuousOn (fun b => Ψ a i t b) (hemi0 ∩ hemi1) := by
  have hT : ContinuousOn (fun b => (tgtB a).coordChange (false, false) t b)
      (hemi0 ∩ hemi1) :=
    ((tgtB a).continuousOn_coordChange (false, false) t).mono (fun b hb =>
      ⟨hemi0_subset_tgtB_zero a hb.1, equator_subset_tgtB a t hb⟩)
  have hS : ContinuousOn (fun b => (srcB a).coordChange i (false, false) b)
      (hemi0 ∩ hemi1) :=
    ((srcB a).continuousOn_coordChange i (false, false)).mono (fun b hb =>
      ⟨equator_subset_srcB a i hb, hemi0_subset_srcB_zero a hb.1⟩)
  have hH := continuousOn_blkH_equator a
  have h := mul_clm hT (mul_clm hH hS)
  simpa only [Ψ] using h

lemma continuousOn_Ψinv_equator (a : ℤ) (i t : Bool × Bool) :
    ContinuousOn (fun b => Ψinv a i t b) (hemi0 ∩ hemi1) := by
  have hS : ContinuousOn (fun b => (srcB a).coordChange (false, false) i b)
      (hemi0 ∩ hemi1) :=
    ((srcB a).continuousOn_coordChange (false, false) i).mono (fun b hb =>
      ⟨hemi0_subset_srcB_zero a hb.1, equator_subset_srcB a i hb⟩)
  have hT : ContinuousOn (fun b => (tgtB a).coordChange t (false, false) b)
      (hemi0 ∩ hemi1) :=
    ((tgtB a).continuousOn_coordChange t (false, false)).mono (fun b hb =>
      ⟨equator_subset_tgtB a t hb, hemi0_subset_tgtB_zero a hb.1⟩)
  have hH := continuousOn_blkHinv_equator a
  have h := mul_clm hS (mul_clm hH hT)
  simpa only [Ψinv] using h

lemma continuousOn_Ψ_hemi1 (a : ℤ) (t : Bool × Bool) (ht : t.1 = true) :
    ContinuousOn (fun b => Ψ a (true, true) t b) hemi1 := by
  intro b hb
  rcases eq_or_ne b OnePoint.infty with rfl | hbne
  · have hev : (fun b : S4 => Ψ a (true, true) t b) =ᶠ[𝓝[hemi1] (OnePoint.infty : S4)]
        (fun _ => 1) :=
      (Ψ_eleven_eventuallyEq a t ht).filter_mono nhdsWithin_le_nhds
    exact ContinuousWithinAt.congr_of_eventuallyEq continuousWithinAt_const hev
      (Ψ_eleven_infty a ht)
  · have hmem : hemi0 ∩ hemi1 ∈ 𝓝 b :=
      IsOpen.mem_nhds (isOpen_hemi0.inter isOpen_hemi1) ⟨fun h => hbne h, hb⟩
    exact ((continuousOn_Ψ_equator a (true, true) t).continuousAt hmem).continuousWithinAt

lemma continuousOn_Ψinv_hemi1 (a : ℤ) (t : Bool × Bool) (ht : t.1 = true) :
    ContinuousOn (fun b => Ψinv a (true, true) t b) hemi1 := by
  intro b hb
  rcases eq_or_ne b OnePoint.infty with rfl | hbne
  · have hev : (fun b : S4 => Ψinv a (true, true) t b) =ᶠ[𝓝[hemi1] (OnePoint.infty : S4)]
        (fun _ => 1) :=
      (Ψinv_eleven_eventuallyEq a t ht).filter_mono nhdsWithin_le_nhds
    exact ContinuousWithinAt.congr_of_eventuallyEq continuousWithinAt_const hev
      (Ψinv_eleven_infty a ht)
  · have hmem : hemi0 ∩ hemi1 ∈ 𝓝 b :=
      IsOpen.mem_nhds (isOpen_hemi0.inter isOpen_hemi1) ⟨fun h => hbne h, hb⟩
    exact ((continuousOn_Ψinv_equator a (true, true) t).continuousAt hmem).continuousWithinAt

lemma continuousOn_Ψ_of_subset (a : ℤ) (i t : Bool × Bool)
    (h : (srcB a).baseSet i ∩ (tgtB a).baseSet t ⊆ hemi0) :
    ContinuousOn (fun b => Ψ a i t b) ((srcB a).baseSet i ∩ (tgtB a).baseSet t) := by
  have hT : ContinuousOn (fun b => (tgtB a).coordChange (false, false) t b)
      ((srcB a).baseSet i ∩ (tgtB a).baseSet t) :=
    ((tgtB a).continuousOn_coordChange (false, false) t).mono (fun b hb =>
      ⟨hemi0_subset_tgtB_zero a (h hb), hb.2⟩)
  have hS : ContinuousOn (fun b => (srcB a).coordChange i (false, false) b)
      ((srcB a).baseSet i ∩ (tgtB a).baseSet t) :=
    ((srcB a).continuousOn_coordChange i (false, false)).mono (fun b hb =>
      ⟨hb.1, hemi0_subset_srcB_zero a (h hb)⟩)
  have hH : ContinuousOn (fun b => blkH a b) ((srcB a).baseSet i ∩ (tgtB a).baseSet t) :=
    (continuousOn_blkH_hemi0 a).mono h
  have hh := mul_clm hT (mul_clm hH hS)
  simpa only [Ψ] using hh

lemma continuousOn_Ψinv_of_subset (a : ℤ) (i t : Bool × Bool)
    (h : (srcB a).baseSet i ∩ (tgtB a).baseSet t ⊆ hemi0) :
    ContinuousOn (fun b => Ψinv a i t b) ((srcB a).baseSet i ∩ (tgtB a).baseSet t) := by
  have hS : ContinuousOn (fun b => (srcB a).coordChange (false, false) i b)
      ((srcB a).baseSet i ∩ (tgtB a).baseSet t) :=
    ((srcB a).continuousOn_coordChange (false, false) i).mono (fun b hb =>
      ⟨hemi0_subset_srcB_zero a (h hb), hb.1⟩)
  have hT : ContinuousOn (fun b => (tgtB a).coordChange t (false, false) b)
      ((srcB a).baseSet i ∩ (tgtB a).baseSet t) :=
    ((tgtB a).continuousOn_coordChange t (false, false)).mono (fun b hb =>
      ⟨hb.2, hemi0_subset_tgtB_zero a (h hb)⟩)
  have hH : ContinuousOn (fun b => blkHinv a b) ((srcB a).baseSet i ∩ (tgtB a).baseSet t) :=
    (continuousOn_blkHinv_hemi0 a).mono h
  have hh := mul_clm hS (mul_clm hH hT)
  simpa only [Ψinv] using hh

lemma continuousOn_Ψ (a : ℤ) (i t : Bool × Bool) :
    ContinuousOn (fun b => Ψ a i t b) ((srcB a).baseSet i ∩ (tgtB a).baseSet t) := by
  by_cases h : i.1 = true ∧ i.2 = true ∧ t.1 = true
  · obtain ⟨h1, h2, h3⟩ := h
    have hi : i = (true, true) := by ext <;> simp_all
    have hset : (srcB a).baseSet (true, true) ∩ (tgtB a).baseSet t = hemi1 := by
      rw [srcB_baseSet, tgtB_baseSet, h3]
      simp [Set.inter_self]
    rw [hi, hset]
    exact continuousOn_Ψ_hemi1 a t h3
  · refine continuousOn_Ψ_of_subset a i t ?_
    rw [srcB_baseSet, tgtB_baseSet]
    exact inter_hemi_subset i.1 i.2 t.1 h

lemma continuousOn_Ψinv (a : ℤ) (i t : Bool × Bool) :
    ContinuousOn (fun b => Ψinv a i t b) ((srcB a).baseSet i ∩ (tgtB a).baseSet t) := by
  by_cases h : i.1 = true ∧ i.2 = true ∧ t.1 = true
  · obtain ⟨h1, h2, h3⟩ := h
    have hi : i = (true, true) := by ext <;> simp_all
    have hset : (srcB a).baseSet (true, true) ∩ (tgtB a).baseSet t = hemi1 := by
      rw [srcB_baseSet, tgtB_baseSet, h3]
      simp [Set.inter_self]
    rw [hi, hset]
    exact continuousOn_Ψinv_hemi1 a t h3
  · refine continuousOn_Ψinv_of_subset a i t ?_
    rw [srcB_baseSet, tgtB_baseSet]
    exact inter_hemi_subset i.1 i.2 t.1 h

/-! ## §8. The eight gauge conditions and the assembly -/

lemma apply_of_comp_eq {f g h : Blk →L[ℂ] Blk} (H : f ∘SL g = h) (v : Blk) : f (g v) = h v := by
  have hv := congrArg (fun (F : Blk →L[ℂ] Blk) => F v) H
  simpa only [ContinuousLinearMap.comp_apply] using hv

lemma apply_of_comp_one {f g : Blk →L[ℂ] Blk} (H : f ∘SL g = 1) (v : Blk) : f (g v) = v := by
  have hv := congrArg (fun (F : Blk →L[ℂ] Blk) => F v) H
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] using hv

lemma apply_of_mul_one {f g : Blk →L[ℂ] Blk} (H : f * g = 1) (v : Blk) : f (g v) = v := by
  rw [ContinuousLinearMap.mul_def] at H
  exact apply_of_comp_one H v

/-- The condition `(A)`: the gauge is compatible with the target transitions. -/
lemma Ψ_htgt (a : ℤ) (i t t' : Bool × Bool) (b : S4)
    (hi : b ∈ (srcB a).baseSet i) (ht : b ∈ (tgtB a).baseSet t)
    (ht' : b ∈ (tgtB a).baseSet t') :
    (tgtB a).coordChange t t' b * Ψ a i t b = Ψ a i t' b := by
  have happ := apply_of_comp_eq (tgtB_chg_comp' a t t' b)
  refine ContinuousLinearMap.ext (fun v => ?_)
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, Ψ]
  exact happ (blkH a b ((srcB a).coordChange i (false, false) b v))

/-- The condition `(B)`: the gauge is compatible with the source transitions. -/
lemma Ψ_hsrc (a : ℤ) (i t i' : Bool × Bool) (b : S4)
    (hi : b ∈ (srcB a).baseSet i) (hi' : b ∈ (srcB a).baseSet i')
    (ht : b ∈ (tgtB a).baseSet t) :
    Ψ a i t b * (srcB a).coordChange i' i b = Ψ a i' t b := by
  have happ := apply_of_comp_eq (srcB_chg_comp' a i i' b)
  refine ContinuousLinearMap.ext (fun v => ?_)
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, Ψ]
  rw [happ]

/-- The condition `(A')` for the inverse gauge. -/
lemma Ψinv_htgtinv (a : ℤ) (i t t' : Bool × Bool) (b : S4)
    (hi : b ∈ (srcB a).baseSet i) (ht : b ∈ (tgtB a).baseSet t)
    (ht' : b ∈ (tgtB a).baseSet t') :
    Ψinv a i t b * (tgtB a).coordChange t' t b = Ψinv a i t' b := by
  have happ := apply_of_comp_eq (tgtB_chg_comp'' a t t' b)
  refine ContinuousLinearMap.ext (fun v => ?_)
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, Ψinv]
  rw [happ]

/-- The condition `(B')` for the inverse gauge. -/
lemma Ψinv_hsrcinv (a : ℤ) (i t i' : Bool × Bool) (b : S4)
    (hi : b ∈ (srcB a).baseSet i) (hi' : b ∈ (srcB a).baseSet i')
    (ht : b ∈ (tgtB a).baseSet t) :
    (srcB a).coordChange i i' b * Ψinv a i t b = Ψinv a i' t b := by
  have happ := apply_of_comp_eq (srcB_chg_comp a (false, false) i i' b)
  refine ContinuousLinearMap.ext (fun v => ?_)
  simp only [ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply, Ψinv]
  rw [happ]

/-- The condition `(C)`: the inverse gauge is a left inverse. -/
lemma Ψ_hleft (a : ℤ) (i i' : Bool × Bool) (b : S4)
    (hb : b ∈ (srcB a).baseSet i ∩ (tgtB a).baseSet i') (x : Blk) :
    Ψinv a i i' b (Ψ a i i' b x) = x := by
  have h1 := apply_of_mul_one (blkHinv_mul_blkH a b)
  have h2 := apply_of_comp_one (tgtB_chg_inv' a i' b)
  have h3 := apply_of_comp_one (srcB_chg_inv a i b)
  simp only [Ψ, Ψinv, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  rw [h2, h1, h3]

/-- The condition `(D)`: the inverse gauge is a right inverse. -/
lemma Ψ_hright (a : ℤ) (i i' : Bool × Bool) (b : S4)
    (hb : b ∈ (srcB a).baseSet i ∩ (tgtB a).baseSet i') (y : Blk) :
    Ψ a i i' b (Ψinv a i i' b y) = y := by
  have h1 := apply_of_mul_one (blkH_mul_blkHinv a b)
  have h2 := apply_of_comp_one (tgtB_chg_inv a i' b)
  have h3 := apply_of_comp_one (srcB_chg_inv' a i b)
  simp only [Ψ, Ψinv, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]
  rw [h3, h1, h2]

/-- **The rank-two shift in the block presentation.** -/
theorem blockIso (a : ℤ) : Nonempty (Work.Thom.BundleIso (srcB a) (tgtB a)) :=
  Work.Thom.nonempty_bundleIso_of_gauge (srcB a) (tgtB a) (Ψ a) (Ψinv a)
    (fun i t => continuousOn_Ψ a i t) (fun i t => continuousOn_Ψinv a i t)
    (fun i t t' b hi ht ht' => Ψ_htgt a i t t' b hi ht ht')
    (fun i t i' b hi hi' ht => Ψ_hsrc a i t i' b hi hi' ht)
    (fun i t t' b hi ht ht' => Ψinv_htgtinv a i t t' b hi ht ht')
    (fun i t i' b hi hi' ht => Ψinv_hsrcinv a i t i' b hi hi' ht)
    (fun i i' b x hb => Ψ_hleft a i i' b hb x)
    (fun i i' b y hb => Ψ_hright a i i' b hb y)

/-! ## §9. Transport to the standard-fibre presentations -/

/-- The Whitney sum presentation of `cLine a ⊕ cLine a` is isomorphic to the block presentation. -/
theorem whitneySumIsoSrc (a : ℤ) :
    Nonempty (Work.Thom.BundleIso (Work.Whitney.whitneySum (cLine a) (cLine a)) (srcB a)) := by
  refine Work.Whitney.nonempty_bundleIso_of_gauge_fibre
    (Work.Whitney.whitneySum (cLine a) (cLine a)) (srcB a)
    ((Work.Whitney.sumFibreC 2 2).symm) (Equiv.refl _) ?_ ?_ ?_
  · intro i; rfl
  · intro b; rfl
  · intro i b
    rw [Work.Whitney.whitneySum_coordChange, Work.Thom.bundleSum_coordChange]
    refine ContinuousLinearMap.ext (fun x => ?_)
    refine Prod.ext ?_ ?_ <;>
      (simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply] <;> rfl)

/-- The Whitney sum presentation of `cLine (2a) ⊕ ε²` is isomorphic to the block presentation. -/
theorem whitneySumIsoTgt (a : ℤ) :
    Nonempty (Work.Thom.BundleIso (tgtB a)
      (Work.Whitney.whitneySum (cLine (2 * a)) (trivialVectorBundleCore ℂ S4 E2 Bool))) := by
  have hconj : ∀ (i : Bool × Bool) (b : S4),
      ((tgtB a).coordChange ((tgtB a).indexAt b) ((Equiv.refl (Bool × Bool)) i) b).comp
        (((Work.Whitney.sumFibreC 2 2).symm : EuclideanSpace ℂ (Fin (2 + 2)) →L[ℂ] Blk))
      = (((Work.Whitney.sumFibreC 2 2).symm : EuclideanSpace ℂ (Fin (2 + 2)) →L[ℂ] Blk)).comp
        ((Work.Whitney.whitneySum (cLine (2 * a))
            (trivialVectorBundleCore ℂ S4 E2 Bool)).coordChange
          ((Work.Whitney.whitneySum (cLine (2 * a))
            (trivialVectorBundleCore ℂ S4 E2 Bool)).indexAt b) i b) := by
    intro i b
    rw [Work.Whitney.whitneySum_coordChange, Work.Thom.bundleSum_coordChange]
    refine ContinuousLinearMap.ext (fun x => ?_)
    refine Prod.ext ?_ ?_ <;>
      (simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply] <;> rfl)
  obtain ⟨e⟩ := Work.Whitney.nonempty_bundleIso_of_gauge_fibre
    (Work.Whitney.whitneySum (cLine (2 * a)) (trivialVectorBundleCore ℂ S4 E2 Bool)) (tgtB a)
    ((Work.Whitney.sumFibreC 2 2).symm) (Equiv.refl _) (by intro i; rfl) (by intro b; rfl) hconj
  exact ⟨e.symm⟩

theorem rankTwoShiftIso (a : ℤ) :
    Nonempty (Work.Thom.BundleIso
      (Work.Whitney.whitneySum (Work.Agree.cLine a) (Work.Agree.cLine a))
      (Work.Whitney.whitneySum (Work.Agree.cLine (2 * a))
        (trivialVectorBundleCore ℂ Work.Agree.S4 (EuclideanSpace ℂ (Fin 2)) Bool))) := by
  obtain ⟨e1⟩ := whitneySumIsoSrc a
  obtain ⟨e2⟩ := blockIso a
  obtain ⟨e3⟩ := whitneySumIsoTgt a
  exact ⟨e1.trans (e2.trans e3)⟩

end

end Work.Agree
