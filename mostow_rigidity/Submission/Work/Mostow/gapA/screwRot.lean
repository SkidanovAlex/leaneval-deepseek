import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.gapA.geodFacts
import Submission.Work.Mostow.gapA.rotationFormula
import Submission.Work.Mostow.gapA.commutingRotation_eq_or_inv
import Submission.Work.Mostow.gapA.rotSetup
import Submission.Work.Mostow.gapA.axisNormDefs
import Submission.Work.Mostow.gapA.normSub_orthonormalBasis
import Submission.Work.Mostow.gapA.gcN_surjective
import Submission.Work.Mostow.gapA.screwPlane

/-!
# `screwRot`: the rotation orbit of the normal plane meets every equal-length vector

Let `a ≠ b` be distinct boundary points of `Sph 3`, let `geodSet a b` be the geodesic joining
them, and let `b₀ : PO 3 1` fix that geodesic pointwise, with the displacement formula
`hdist u (b₀ • u) = 2 arsinh (sinh (distGeod a b u) · sin (π/M))` — i.e. `b₀` acts on the normal
plane `NormSub a b` of the geodesic as the rotation of angle `2π/M`.

Then for any two vectors `u`, `w` of the normal plane of equal Minkowski length, some integral
power `b₀^j` of the rotation brings `u` to within angle `π/M` of `w`:

`cos (π/M) · ⟨u,u⟩ ≤ ⟨w, emat (b₀^j) u⟩`.

The proof has three parts.

* `scalar_identity_gen` — the quadratic-form identity
  `⟨emat b₀ Z, Z⟩ = cos (2π/M) ⟨Z,Z⟩` on the normal plane, obtained from the displacement
  formula (it is `Work.Mostow.gapA.scalar_identity` without the side condition `6 ≤ M`).
* `normRot` — the action of `emat b₀` on `NormSub a b` as a linear equivalence, together with
  `normRot_zpow_coe`: `(normRot^j u) = emat (b₀^j) *ᵥ u`.
* `planeRotMeet` — the plane statement for every `M ≥ 1`: a rotation by `2π/M` of a positive
  definite plane brings any `u` within angle `π/M` of any equal-length `w`.  For `M ≥ 3` this is
  `screwPlane_abstract`; for `M = 1, 2` the rotation is `±1` and Cauchy–Schwarz (positivity of
  the form) finishes.
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open _root_.Matrix

noncomputable section

variable {a b : E 3}

/-! ## The quadratic form of `emat b₀` on the normal plane -/

/-- The quadratic-form identity on the normal plane, with no restriction on `M`: a rotation
about `geodSet a b` whose displacement is given by `2 arsinh (sinh · sin (π/M))` acts on
`NormSub a b` by the scalar `cM M = cos (2π/M)` in the sense of the quadratic form. -/
theorem scalar_identity_gen (hA : POActionProp 3) (hI : HypIsometryProp 3)
    (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) (M : ℕ) (f : PO 3 1)
    (hfix : ∀ u : E 3, u ∈ geodSet a b → f • u = u)
    (hdisp : ∀ u : E 3, hdist u (f • u)
      = 2 * Real.arsinh (Real.sinh (distGeod a b u) * Real.sin (Real.pi / (M : ℝ))))
    (hsurj : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ NormSub a b → ∃ u : E 3, gcN a b u = Z) :
    ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ NormSub a b →
      mink (Matrix.mulVec (emat f) Z) Z = cM M * mink Z Z := by
  intro Z hZ
  obtain ⟨u, hu⟩ := hsurj Z hZ
  have h1 := mink_hlift_emat_hlift_rot hA hI ha hb hab f hfix u
  have h2 : Real.cosh (hdist u (f • u))
      = -mink (hlift u) (Matrix.mulVec (emat f) (hlift u)) := by
    rw [emat_hlift f u, mink_hlift_neg_cosh']
    ring
  have h3 : Real.cosh (hdist u (f • u))
      = 1 + 2 * Real.sin (Real.pi / (M : ℝ)) ^ 2 * mink (gcN a b u) (gcN a b u) := by
    rw [hdisp u, Real.cosh_two_mul, Real.cosh_arsinh, Real.sinh_arsinh,
      Real.sq_sqrt (by positivity), ← sinh_sq_distGeod a b u ha hb hab]
    ring
  rw [hu] at h1 h3
  rw [h2] at h3
  have key : mink Z (Matrix.mulVec (emat f) Z)
      = (1 - 2 * Real.sin (Real.pi / (M : ℝ)) ^ 2) * mink Z Z := by linarith
  rw [minkSeg_comm, key, cM]

/-! ## The induced linear equivalence of the normal plane -/

lemma emat_inv_fixes (hA : POActionProp 3) (b₀ : PO 3 1)
    (hMA : emat b₀ *ᵥ nvec a = nvec a) : emat b₀⁻¹ *ᵥ nvec a = nvec a := by
  have h : emat b₀⁻¹ *ᵥ (emat b₀ *ᵥ nvec a) = nvec a := by
    rw [Matrix.mulVec_mulVec, ← emat_mul hA, inv_mul_cancel, emat_one hA, Matrix.one_mulVec]
  rwa [hMA] at h

/-- The action of `emat b₀` (assumed to fix both null vectors `nvec a`, `nvec b`) on the normal
plane `NormSub a b`, as a linear equivalence. -/
noncomputable def normRot (hA : POActionProp 3) (b₀ : PO 3 1)
    (hMA : emat b₀ *ᵥ nvec a = nvec a) (hMB : emat b₀ *ᵥ nvec b = nvec b) :
    NormSub a b ≃ₗ[ℝ] NormSub a b where
  toFun Z := ⟨emat b₀ *ᵥ (Z : Fin 3 ⊕ Fin 1 → ℝ), emat_mulVec_mem_NormSub b₀ hMA hMB Z.2⟩
  invFun Z := ⟨emat b₀⁻¹ *ᵥ (Z : Fin 3 ⊕ Fin 1 → ℝ),
    emat_mulVec_mem_NormSub b₀⁻¹ (emat_inv_fixes hA b₀ hMA) (emat_inv_fixes hA b₀ hMB) Z.2⟩
  map_add' Z Z' := by
    ext i
    simp [Matrix.mulVec_add]
  map_smul' c Z := by
    ext i
    simp [Matrix.mulVec_smul]
  left_inv Z := by
    apply Subtype.ext
    show emat b₀⁻¹ *ᵥ (emat b₀ *ᵥ (Z : Fin 3 ⊕ Fin 1 → ℝ)) = (Z : Fin 3 ⊕ Fin 1 → ℝ)
    rw [Matrix.mulVec_mulVec, ← emat_mul hA, inv_mul_cancel, emat_one hA, Matrix.one_mulVec]
  right_inv Z := by
    apply Subtype.ext
    show emat b₀ *ᵥ (emat b₀⁻¹ *ᵥ (Z : Fin 3 ⊕ Fin 1 → ℝ)) = (Z : Fin 3 ⊕ Fin 1 → ℝ)
    rw [Matrix.mulVec_mulVec, ← emat_mul hA, mul_inv_cancel, emat_one hA, Matrix.one_mulVec]

lemma normRot_coe (hA : POActionProp 3) (b₀ : PO 3 1)
    (hMA : emat b₀ *ᵥ nvec a = nvec a) (hMB : emat b₀ *ᵥ nvec b = nvec b)
    (Z : NormSub a b) :
    ((normRot hA b₀ hMA hMB) Z : Fin 3 ⊕ Fin 1 → ℝ) = emat b₀ *ᵥ (Z : Fin 3 ⊕ Fin 1 → ℝ) := rfl

lemma normRot_inv_coe (hA : POActionProp 3) (b₀ : PO 3 1)
    (hMA : emat b₀ *ᵥ nvec a = nvec a) (hMB : emat b₀ *ᵥ nvec b = nvec b)
    (Z : NormSub a b) :
    (((normRot hA b₀ hMA hMB)⁻¹) Z : Fin 3 ⊕ Fin 1 → ℝ)
      = emat b₀⁻¹ *ᵥ (Z : Fin 3 ⊕ Fin 1 → ℝ) := by
  have hkey : emat b₀ *ᵥ (((normRot hA b₀ hMA hMB)⁻¹) Z : Fin 3 ⊕ Fin 1 → ℝ)
      = (Z : Fin 3 ⊕ Fin 1 → ℝ) := by
    have h2 := congrArg (fun x : NormSub a b => (x : Fin 3 ⊕ Fin 1 → ℝ))
      (LinearEquiv.apply_symm_apply (normRot hA b₀ hMA hMB) Z)
    rwa [normRot_coe hA b₀ hMA hMB] at h2
  rw [← hkey]
  rw [Matrix.mulVec_mulVec, ← emat_mul hA, inv_mul_cancel, emat_one hA, Matrix.one_mulVec]

lemma normRot_pow_coe (hA : POActionProp 3) (b₀ : PO 3 1)
    (hMA : emat b₀ *ᵥ nvec a = nvec a) (hMB : emat b₀ *ᵥ nvec b = nvec b)
    (k : ℕ) (Z : NormSub a b) :
    (((normRot hA b₀ hMA hMB) ^ k) Z : Fin 3 ⊕ Fin 1 → ℝ)
      = emat (b₀ ^ k) *ᵥ (Z : Fin 3 ⊕ Fin 1 → ℝ) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    show ((1 : NormSub a b ≃ₗ[ℝ] NormSub a b) Z : Fin 3 ⊕ Fin 1 → ℝ)
      = emat 1 *ᵥ (Z : Fin 3 ⊕ Fin 1 → ℝ)
    rw [LinearEquiv.one_eq_refl, LinearEquiv.refl_apply, emat_one hA, Matrix.one_mulVec]
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply, normRot_coe hA b₀ hMA hMB, ih,
      Matrix.mulVec_mulVec, ← emat_mul hA, ← pow_succ']

lemma normRot_inv_pow_coe (hA : POActionProp 3) (b₀ : PO 3 1)
    (hMA : emat b₀ *ᵥ nvec a = nvec a) (hMB : emat b₀ *ᵥ nvec b = nvec b)
    (k : ℕ) (Z : NormSub a b) :
    ((((normRot hA b₀ hMA hMB)⁻¹) ^ k) Z : Fin 3 ⊕ Fin 1 → ℝ)
      = emat ((b₀⁻¹) ^ k) *ᵥ (Z : Fin 3 ⊕ Fin 1 → ℝ) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    show ((1 : NormSub a b ≃ₗ[ℝ] NormSub a b) Z : Fin 3 ⊕ Fin 1 → ℝ)
      = emat 1 *ᵥ (Z : Fin 3 ⊕ Fin 1 → ℝ)
    rw [LinearEquiv.one_eq_refl, LinearEquiv.refl_apply, emat_one hA, Matrix.one_mulVec]
  | succ k ih =>
    rw [pow_succ', LinearEquiv.mul_apply, normRot_inv_coe hA b₀ hMA hMB, ih,
      Matrix.mulVec_mulVec, ← emat_mul hA, ← pow_succ']

/-- The transfer identity: the `j`-th power of the induced rotation is the action of
`emat (b₀^j)`. -/
lemma normRot_zpow_coe (hA : POActionProp 3) (b₀ : PO 3 1)
    (hMA : emat b₀ *ᵥ nvec a = nvec a) (hMB : emat b₀ *ᵥ nvec b = nvec b)
    (j : ℤ) (Z : NormSub a b) :
    (((normRot hA b₀ hMA hMB) ^ j) Z : Fin 3 ⊕ Fin 1 → ℝ)
      = emat (b₀ ^ j) *ᵥ (Z : Fin 3 ⊕ Fin 1 → ℝ) := by
  by_cases hj : 0 ≤ j
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, j = (k : ℤ) := ⟨j.toNat, (Int.toNat_of_nonneg hj).symm⟩
    rw [hk, zpow_natCast, zpow_natCast]
    exact normRot_pow_coe hA b₀ hMA hMB k Z
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, j = -((k : ℕ) : ℤ) := ⟨(-j).toNat, by omega⟩
    rw [hk, _root_.zpow_neg, zpow_natCast, ← inv_pow, _root_.zpow_neg, zpow_natCast, ← inv_pow]
    exact normRot_inv_pow_coe hA b₀ hMA hMB k Z

/-! ## The bilinear form on the normal plane -/

def minkBB (a b : E 3) (x : NormSub a b) : NormSub a b →ₗ[ℝ] ℝ where
  toFun y := mink (x : Fin 3 ⊕ Fin 1 → ℝ) (y : Fin 3 ⊕ Fin 1 → ℝ)
  map_add' y₁ y₂ := by
    simp only [Submodule.coe_add]
    rw [sn_mink_add_right]
  map_smul' r y := by
    simp only [Submodule.coe_smul]
    rw [sn_mink_smul_right, smul_eq_mul, RingHom.id_apply]

@[simp] lemma minkBB_apply (x y : NormSub a b) :
    minkBB a b x y = mink (x : Fin 3 ⊕ Fin 1 → ℝ) (y : Fin 3 ⊕ Fin 1 → ℝ) := rfl

def minkB (a b : E 3) : NormSub a b →ₗ[ℝ] NormSub a b →ₗ[ℝ] ℝ where
  toFun := minkBB a b
  map_add' x₁ x₂ := by
    ext y
    simp only [minkBB_apply, LinearMap.add_apply, Submodule.coe_add]
    rw [sn_mink_add_left]
  map_smul' r x := by
    ext y
    simp only [minkBB_apply, LinearMap.smul_apply, Submodule.coe_smul]
    rw [sn_mink_smul_left, smul_eq_mul, RingHom.id_apply]

@[simp] lemma minkB_apply (x y : NormSub a b) :
    minkB a b x y = mink (x : Fin 3 ⊕ Fin 1 → ℝ) (y : Fin 3 ⊕ Fin 1 → ℝ) := rfl

/-! ## The abstract plane statement for every `M ≥ 1` -/

theorem planeRotMeet {V : Type*} [AddCommGroup V] [Module ℝ V]
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (hsym : ∀ x y, B x y = B y x)
    (hpos : ∀ x, 0 ≤ B x x) (hdef : ∀ x, B x x = 0 → x = 0)
    (hdim : Module.finrank ℝ V = 2)
    (M : ℕ) (hM : 0 < M) (R : V ≃ₗ[ℝ] V)
    (hR : ∀ x y, B (R x) (R y) = B x y)
    (hRq : ∀ x, B (R x) x = Real.cos (2 * Real.pi / M) * B x x)
    (u w : V) (hwn : B w w = B u u) :
    ∃ j : ℤ, Real.cos (Real.pi / M) * B u u ≤ B w ((R ^ j) u) := by
  by_cases h3 : 3 ≤ M
  · exact screwPlane_abstract B hsym hpos hdef hdim M h3 R hR hRq u w hwn
  · have hM12 : M = 1 ∨ M = 2 := by omega
    have hsub2 : ∀ y z : V, B (y - z) (y - z) = B y y - 2 * B y z + B z z := by
      intro y z; rw [Bilin_sub_l, Bilin_sub_r, Bilin_sub_r, hsym z y]; ring
    have hadd2 : ∀ y z : V, B (y + z) (y + z) = B y y + 2 * B y z + B z z := by
      intro y z; rw [Bilin_add_l, Bilin_add_r, Bilin_add_r, hsym z y]; ring
    rcases hM12 with h1 | h2
    · subst h1
      have hfix1 : ∀ x : V, R x = x := by
        intro x
        have h1 : B (R x - x) (R x - x) = 0 := by
          rw [hsub2 (R x) x, hR x x, hRq x]
          have hc : Real.cos (2 * Real.pi / ((1 : ℕ) : ℝ)) = 1 := by
            rw [show 2 * Real.pi / ((1 : ℕ) : ℝ) = 2 * Real.pi by norm_num,
              Real.cos_two_pi]
          rw [hc]; ring
        exact sub_eq_zero.mp (hdef _ h1)
      refine ⟨0, ?_⟩
      have hc : Real.cos (Real.pi / ((1 : ℕ) : ℝ)) = -1 := by
        rw [show Real.pi / ((1 : ℕ) : ℝ) = Real.pi by norm_num, Real.cos_pi]
      rw [hc, _root_.zpow_zero, LinearEquiv.one_eq_refl, LinearEquiv.refl_apply]
      have h := hpos (w + u)
      rw [Bilin_add_l, Bilin_add_r, Bilin_add_r, hwn, hsym u w] at h
      linarith
    · subst h2
      have hfix2 : ∀ x : V, R x = -x := by
        intro x
        have h1 : B (R x + x) (R x + x) = 0 := by
          rw [hadd2 (R x) x, hR x x, hRq x]
          have hc : Real.cos (2 * Real.pi / ((2 : ℕ) : ℝ)) = -1 := by
            rw [show 2 * Real.pi / ((2 : ℕ) : ℝ) = Real.pi by norm_num, Real.cos_pi]
          rw [hc]; ring
        exact eq_neg_of_add_eq_zero_left (hdef _ h1)
      have hc : Real.cos (Real.pi / ((2 : ℕ) : ℝ)) = 0 := by
        rw [show Real.pi / ((2 : ℕ) : ℝ) = Real.pi / 2 by norm_num, Real.cos_pi_div_two]
      by_cases hwu : 0 ≤ B w u
      · refine ⟨0, ?_⟩
        rw [hc, zero_mul, _root_.zpow_zero, LinearEquiv.one_eq_refl, LinearEquiv.refl_apply]
        exact hwu
      · refine ⟨1, ?_⟩
        rw [hc, zero_mul, _root_.zpow_one, hfix2 u]
        show 0 ≤ B w (-u)
        rw [map_neg (B w) u]
        linarith [not_le.mp hwu]

/-! ## The target -/

theorem screwRot {a b : Submission.Mostow.E 3} (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3)
    (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3) (hab : a ≠ b)
    (M : ℕ) (hM : 0 < M) (b₀ : LeanEval.Geometry.MostowRigidity.PO 3 1)
    (hfix : ∀ u : Submission.Mostow.E 3, u ∈ geodSet a b → b₀ • u = u)
    (hdisp : ∀ u : Submission.Mostow.E 3, Submission.Mostow.hdist u (b₀ • u)
      = 2 * Real.arsinh (Real.sinh (distGeod a b u) * Real.sin (Real.pi / (M : ℝ))))
    (u w : Fin 3 ⊕ Fin 1 → ℝ) (hu : u ∈ NormSub a b) (hw : w ∈ NormSub a b)
    (hnorm : mink w w = mink u u) :
    ∃ j : ℤ, Real.cos (Real.pi / M) * mink u u
      ≤ mink w (_root_.Matrix.mulVec (Work.Mostow.emat (b₀ ^ j)) u) := by
  obtain ⟨hMA, hMB⟩ := emat_fixes_nvec hA hI b₀ a b ha hb hab hfix
  have hquad : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ NormSub a b →
      mink (Matrix.mulVec (emat b₀) Z) Z = Real.cos (2 * Real.pi / M) * mink Z Z := by
    intro Z hZ
    have h := scalar_identity_gen hA hI ha hb hab M b₀ hfix hdisp
      (gcN_surjective a b ha hb hab) Z hZ
    rwa [cM_eq_cos M] at h
  have hdim : Module.finrank ℝ (NormSub a b) = 2 := nsb_finrank_NormSub ha hb hab
  have hsym : ∀ x y : NormSub a b, minkB a b x y = minkB a b y x := by
    intro x y
    rw [minkB_apply, minkB_apply]
    exact minkSeg_comm _ _
  have hpos : ∀ x : NormSub a b, 0 ≤ minkB a b x x := by
    intro x
    rw [minkB_apply]
    exact mink_nonneg_of_mem_NormSub ha x.2
  have hdef : ∀ x : NormSub a b, minkB a b x x = 0 → x = 0 := by
    intro x hx
    rw [minkB_apply] at hx
    refine Subtype.ext ?_
    have h := eq_zero_of_mem_NormSub_of_mink_self_eq_zero ha hb hab x.2 hx
    simpa using h
  have hRform : ∀ x y : NormSub a b,
      minkB a b (normRot hA b₀ hMA hMB x) (normRot hA b₀ hMA hMB y) = minkB a b x y := by
    intro x y
    rw [minkB_apply, minkB_apply, normRot_coe hA b₀ hMA hMB, normRot_coe hA b₀ hMA hMB]
    exact mink_emat_emat b₀ _ _
  have hRquad : ∀ x : NormSub a b,
      minkB a b (normRot hA b₀ hMA hMB x) x = Real.cos (2 * Real.pi / M) * minkB a b x x := by
    intro x
    rw [minkB_apply, minkB_apply, normRot_coe hA b₀ hMA hMB]
    exact hquad (x : Fin 3 ⊕ Fin 1 → ℝ) x.2
  have hwn : minkB a b ⟨w, hw⟩ ⟨w, hw⟩ = minkB a b ⟨u, hu⟩ ⟨u, hu⟩ := by
    rw [minkB_apply, minkB_apply]
    simpa using hnorm
  obtain ⟨j, hj⟩ := planeRotMeet (minkB a b) hsym hpos hdef hdim M hM
    (normRot hA b₀ hMA hMB) hRform hRquad ⟨u, hu⟩ ⟨w, hw⟩ hwn
  refine ⟨j, ?_⟩
  rw [minkB_apply, minkB_apply] at hj
  rw [normRot_zpow_coe hA b₀ hMA hMB j ⟨u, hu⟩] at hj
  simpa using hj

end

end Work.Mostow.gapA
