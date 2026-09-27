import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.gapA.geodFacts
import Submission.Work.Mostow.gapA.mem_geodSet_iff_span
import Submission.Work.Mostow.gapA.rotationFormula
import Submission.Work.Mostow.gapA.axisNormDefs
import Submission.Work.Mostow.perpNullUnit
import Submission.Work.Mostow.ematSpec
import Submission.Work.Mostow.bdFixIff
import Submission.Work.Mostow.gapA.gcN_surjective
import Submission.Work.Mostow.gapA.normSub_orthonormalBasis

/-!
# Commuting rotations about (possibly different) geodesics of `ℍ³`

Main result: `Work.Mostow.gapA.commutingRotation_eq_or_inv`.

For `ξ : E 3` put `θ_ξ = nvec ξ = (ξ,1)` (a null vector for `ξ ∈ Sph 3`), and let `mink` be the
Minkowski form on `ℝ^{Fin 3 ⊕ Fin 1}`.  For two distinct boundary points `a ≠ b`:

* `Ax a b = span{θ_a, θ_b}` is the Minkowski plane of the geodesic `geodSet a b`;
* `NormSub a b = Ax a b^⊥` is its normal plane, on which `mink` is positive definite.

A rotation `f` of `PO 3 1` about `geodSet a b` by `±2π/M` (`M ≥ 6`) fixes `Ax a b` pointwise and
acts on `NormSub a b` as a rotation of the positive definite plane, so that

* every real eigenvalue of `emat f` is `1` and its `1`-eigenspace is `Ax a b`.

Using this for `f` and for `g`, the invariance of `Ax a' b'` under `emat f` and an elementary case
analysis force `Ax a b = Ax a' b'`; the two rotations of the common normal plane are then inverse
to each other, and the main theorem follows.
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open _root_.Matrix

noncomputable section

variable {a b a' b' : E 3}

/-! ## The Minkowski plane of a geodesic -/

/-- The Minkowski plane spanned by the two boundary null vectors `nvec a`, `nvec b`. -/
def Ax (a b : E 3) : Submodule ℝ (Fin 3 ⊕ Fin 1 → ℝ) :=
  Submodule.span ℝ ({nvec a, nvec b} : Set (Fin 3 ⊕ Fin 1 → ℝ))

lemma mem_Ax_iff (x : Fin 3 ⊕ Fin 1 → ℝ) :
    x ∈ Ax a b ↔ ∃ α β : ℝ, x = α • nvec a + β • nvec b := by
  rw [Ax, Submodule.mem_span_pair]
  exact ⟨fun ⟨α, β, h⟩ => ⟨α, β, h.symm⟩, fun ⟨α, β, h⟩ => ⟨α, β, h.symm⟩⟩

lemma nvec_a_mem_Ax (a b : E 3) : nvec a ∈ Ax a b := by
  rw [mem_Ax_iff]; exact ⟨1, 0, by rw [one_smul, zero_smul, add_zero]⟩

lemma nvec_b_mem_Ax (a b : E 3) : nvec b ∈ Ax a b := by
  rw [mem_Ax_iff]; exact ⟨0, 1, by rw [one_smul, zero_smul, zero_add]⟩

lemma mink_Ax_NormSub {x Z : Fin 3 ⊕ Fin 1 → ℝ} (hx : x ∈ Ax a b) (hZ : Z ∈ NormSub a b) :
    mink x Z = 0 := by
  obtain ⟨α, β, hx'⟩ := (mem_Ax_iff x).mp hx
  obtain ⟨hZa, hZb⟩ := mem_NormSub.mp hZ
  have h1 : mink (nvec a) Z = 0 := by rw [minkSeg_comm]; exact hZa
  have h2 : mink (nvec b) Z = 0 := by rw [minkSeg_comm]; exact hZb
  rw [hx', minkSeg_add_left, mink_smul_left'', mink_smul_left'', h1, h2]
  ring

lemma mink_NormSub_Ax {Z x : Fin 3 ⊕ Fin 1 → ℝ} (hZ : Z ∈ NormSub a b) (hx : x ∈ Ax a b) :
    mink Z x = 0 := by
  rw [minkSeg_comm]; exact mink_Ax_NormSub hx hZ

lemma Ax_inf_NormSub (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b)
    {x : Fin 3 ⊕ Fin 1 → ℝ} (hx : x ∈ Ax a b) (hZ : x ∈ NormSub a b) : x = 0 := by
  obtain ⟨α, β, hx'⟩ := (mem_Ax_iff x).mp hx
  obtain ⟨hZa, hZb⟩ := mem_NormSub.mp hZ
  have hne₁ : inner ℝ b a - 1 ≠ 0 := by
    have h : inner ℝ a b < 1 := inner_ab_lt_one a b ha hb hab
    rw [real_inner_comm]; linarith
  have hne₂ : inner ℝ a b - 1 ≠ 0 := by
    have h : inner ℝ a b < 1 := inner_ab_lt_one a b ha hb hab
    linarith
  have h1 : β * (inner ℝ b a - 1) = 0 := by
    have h := hZa
    rw [hx'] at h
    simp only [minkSeg_add_left, mink_smul_left'', mink_smul_left'', mink_nvec_self' ha,
      mul_zero, zero_add, mink_nvec_nvec'] at h
    exact h
  have h2 : α * (inner ℝ a b - 1) = 0 := by
    have h := hZb
    rw [hx'] at h
    simp only [minkSeg_add_left, mink_smul_left'', mink_smul_left'', mink_nvec_nvec',
      mink_nvec_self' hb, mul_zero, add_zero] at h
    exact h
  have hb0 : β = 0 := (mul_eq_zero.mp h1).resolve_right hne₁
  have ha0 : α = 0 := (mul_eq_zero.mp h2).resolve_right hne₂
  rw [hx', ha0, hb0, zero_smul, zero_smul, add_zero]

lemma emat_mulVec_mem_Ax (f : PO 3 1) (hfa : Matrix.mulVec (emat f) (nvec a) = nvec a)
    (hfb : Matrix.mulVec (emat f) (nvec b) = nvec b) {x : Fin 3 ⊕ Fin 1 → ℝ}
    (hx : x ∈ Ax a b) : Matrix.mulVec (emat f) x ∈ Ax a b := by
  obtain ⟨α, β, hx'⟩ := (mem_Ax_iff x).mp hx
  rw [hx', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hfa, hfb]
  exact (Ax a b).add_mem ((Ax a b).smul_mem α (nvec_a_mem_Ax a b))
    ((Ax a b).smul_mem β (nvec_b_mem_Ax a b))

lemma emat_mulVec_eq_self_of_mem_Ax (f : PO 3 1)
    (hfa : Matrix.mulVec (emat f) (nvec a) = nvec a)
    (hfb : Matrix.mulVec (emat f) (nvec b) = nvec b) {x : Fin 3 ⊕ Fin 1 → ℝ}
    (hx : x ∈ Ax a b) : Matrix.mulVec (emat f) x = x := by
  obtain ⟨α, β, hx'⟩ := (mem_Ax_iff x).mp hx
  rw [hx', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hfa, hfb]

lemma emat_mulVec_mem_NormSub (f : PO 3 1) (hfa : Matrix.mulVec (emat f) (nvec a) = nvec a)
    (hfb : Matrix.mulVec (emat f) (nvec b) = nvec b) {Z : Fin 3 ⊕ Fin 1 → ℝ}
    (hZ : Z ∈ NormSub a b) : Matrix.mulVec (emat f) Z ∈ NormSub a b := by
  obtain ⟨hZa, hZb⟩ := mem_NormSub.mp hZ
  refine mem_NormSub.mpr ⟨?_, ?_⟩
  · rw [← hfa, mink_emat_emat, hZa]
  · rw [← hfb, mink_emat_emat, hZb]

/-- `emat f` is an invertible matrix, hence has trivial kernel. -/
lemma emat_mulVec_eq_zero_iff (hA : POActionProp 3) (f : PO 3 1)
    {v : Fin 3 ⊕ Fin 1 → ℝ} : Matrix.mulVec (emat f) v = 0 ↔ v = 0 := by
  constructor
  · intro h
    have h1 : Matrix.mulVec (emat f⁻¹) (Matrix.mulVec (emat f) v) = v := by
      rw [Matrix.mulVec_mulVec, ← emat_mul hA, inv_mul_cancel, emat_one hA, Matrix.one_mulVec]
    rw [h] at h1
    simpa using h1.symm
  · intro h; rw [h]; simp

/-! ## The angle constant -/

/-- `cM M = 1 - 2 sin²(π/M) = cos (2π/M)`. -/
def cM (M : ℕ) : ℝ := 1 - 2 * Real.sin (Real.pi / (M : ℝ)) ^ 2

lemma cM_eq_cos (M : ℕ) : cM M = Real.cos (2 * Real.pi / (M : ℝ)) := by
  rw [cM, ← Real.cos_two_mul_eq_one_sub (Real.pi / (M : ℝ))]
  congr 1
  ring

lemma sin_pi_div_pos (M : ℕ) (hM : 6 ≤ M) : 0 < Real.sin (Real.pi / (M : ℝ)) := by
  apply Real.sin_pos_of_pos_of_lt_pi
  · positivity
  · have h1 : (1 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 1 < M)
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [Real.pi_pos]

lemma sin_pi_div_lt_one (M : ℕ) (hM : 6 ≤ M) : Real.sin (Real.pi / (M : ℝ)) < 1 := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by positivity
  have h2 : (2 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 2 < M)
  have hx1 : -(Real.pi / 2) ≤ Real.pi / (M : ℝ) := by
    have h3 : 0 < Real.pi / (M : ℝ) := div_pos Real.pi_pos hMpos
    have h4 : 0 < Real.pi / 2 := by positivity
    linarith
  have hlt : Real.pi / (M : ℝ) < Real.pi / 2 := by
    rw [div_lt_iff₀ hMpos]
    nlinarith [Real.pi_pos]
  have h := Real.sin_lt_sin_of_lt_of_le_pi_div_two hx1 (le_refl _) hlt
  rwa [Real.sin_pi_div_two] at h

lemma cM_sq_lt_one (M : ℕ) (hM : 6 ≤ M) : (cM M) ^ 2 < 1 := by
  have h0 := sin_pi_div_pos M hM
  have h2 : Real.sin (Real.pi / (M : ℝ)) ^ 2 < 1 := by
    have h1 := sin_pi_div_lt_one M hM
    nlinarith
  have h3 : 0 < Real.sin (Real.pi / (M : ℝ)) ^ 2 := sq_pos_of_pos h0
  have h4 : (1 - 2 * Real.sin (Real.pi / (M : ℝ)) ^ 2) ^ 2
      = 1 - 4 * (Real.sin (Real.pi / (M : ℝ)) ^ 2)
          * (1 - Real.sin (Real.pi / (M : ℝ)) ^ 2) := by ring
  rw [cM, h4]
  nlinarith [h2, h3]

lemma cM_ne_one (M : ℕ) (hM : 6 ≤ M) : cM M ≠ 1 := by
  have h0 := sin_pi_div_pos M hM
  rw [cM]
  intro h
  nlinarith [sq_pos_of_ne_zero (ne_of_gt h0)]

/-! ## The displacement identity -/

/-- Pairing of an "axis part + normal part" with another such pair. -/
lemma mink_axis_add_normal {S T Z W : Fin 3 ⊕ Fin 1 → ℝ} (hS : S ∈ Ax a b) (hT : T ∈ Ax a b)
    (hZ : Z ∈ NormSub a b) (hW : W ∈ NormSub a b) :
    mink (S + Z) (T + W) = mink S T + mink Z W := by
  simp only [minkSeg_add_left, minkSeg_add_right]
  rw [mink_Ax_NormSub hS hW, mink_NormSub_Ax hZ hT]
  ring

/-- The Minkowski pairing of `hlift u` with `emat f (hlift u)` in terms of the normal component,
for `f` a rotation about the geodesic `geodSet a b`. -/
lemma mink_hlift_emat_hlift_rot (hA : POActionProp 3) (hI : HypIsometryProp 3)
    (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) (f : PO 3 1)
    (hfix : ∀ u : E 3, u ∈ geodSet a b → f • u = u) (u : E 3) :
    mink (hlift u) (Matrix.mulVec (emat f) (hlift u))
      = -1 - mink (gcN a b u) (gcN a b u)
        + mink (gcN a b u) (Matrix.mulVec (emat f) (gcN a b u)) := by
  obtain ⟨hfa, hfb⟩ := emat_fixes_nvec hA hI f a b ha hb hab hfix
  have hZm : gcN a b u ∈ NormSub a b :=
    mem_NormSub.mpr ⟨mink_gcN_nvec_a a b ha hb hab u, mink_gcN_nvec_b a b ha hb hab u⟩
  have hSm : gcA a b u • nvec a + gcB a b u • nvec b ∈ Ax a b :=
    (Ax a b).add_mem ((Ax a b).smul_mem _ (nvec_a_mem_Ax a b))
      ((Ax a b).smul_mem _ (nvec_b_mem_Ax a b))
  have hFS : Matrix.mulVec (emat f) (gcA a b u • nvec a + gcB a b u • nvec b)
      = gcA a b u • nvec a + gcB a b u • nvec b :=
    emat_mulVec_eq_self_of_mem_Ax f hfa hfb hSm
  have hFZ := emat_mulVec_mem_NormSub f hfa hfb hZm
  have hhl : hlift u = gcA a b u • nvec a + gcB a b u • nvec b + gcN a b u :=
    (gcN_expand a b u).symm
  calc mink (hlift u) (Matrix.mulVec (emat f) (hlift u))
      = mink (gcA a b u • nvec a + gcB a b u • nvec b + gcN a b u)
            (gcA a b u • nvec a + gcB a b u • nvec b
              + Matrix.mulVec (emat f) (gcN a b u)) := by
        rw [hhl, Matrix.mulVec_add, hFS]
    _ = mink (gcA a b u • nvec a + gcB a b u • nvec b)
            (gcA a b u • nvec a + gcB a b u • nvec b)
          + mink (gcN a b u) (Matrix.mulVec (emat f) (gcN a b u)) :=
        mink_axis_add_normal hSm hSm hZm hFZ
    _ = -1 - mink (gcN a b u) (gcN a b u)
          + mink (gcN a b u) (Matrix.mulVec (emat f) (gcN a b u)) := by
        rw [mink_S0_self a b ha hb hab u]
        ring

/-- **The scalar identity on the normal plane.**  A rotation `f` about `geodSet a b` by
`±2π/M` satisfies `⟨emat f Z, Z⟩ = cos (2π/M) ⟨Z, Z⟩` for every `Z ∈ NormSub a b`. -/
lemma scalar_identity (hA : POActionProp 3) (hI : HypIsometryProp 3)
    (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) (M : ℕ) (hM : 6 ≤ M) (f : PO 3 1)
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

/-! ## The normal plane: an orthonormal basis and coordinates -/

lemma coord_of_basis (B : AxisBasis a b) {Z : Fin 3 ⊕ Fin 1 → ℝ} (hZ : Z ∈ NormSub a b) :
    Z = mink Z B.E1 • B.E1 + mink Z B.E2 • B.E2 := by
  obtain ⟨α, β, hαβ⟩ := B.span Z hZ
  have h1 : mink Z B.E1 = α := by
    rw [hαβ, minkSeg_add_left, mink_smul_left'', mink_smul_left'', B.n11,
      minkSeg_comm B.E2 B.E1, B.n12]
    ring
  have h2 : mink Z B.E2 = β := by
    rw [hαβ, minkSeg_add_left, mink_smul_left'', mink_smul_left'', B.n12, B.n22]
    ring
  rw [h1, h2, hαβ]

/-- The two basis vectors of `AxisBasis` are linearly independent. -/
lemma basis_indep_pair (B : AxisBasis a b) {s t : ℝ} (h : s • B.E1 + t • B.E2 = 0) :
    s = 0 ∧ t = 0 := by
  have h1 : mink (s • B.E1 + t • B.E2) B.E1 = 0 := by rw [h]; simp [mink]
  have h2 : mink (s • B.E1 + t • B.E2) B.E2 = 0 := by rw [h]; simp [mink]
  rw [minkSeg_add_left, mink_smul_left'', mink_smul_left''] at h1 h2
  rw [B.n11, minkSeg_comm B.E2 B.E1, B.n12] at h1
  rw [B.n12, B.n22] at h2
  constructor <;> linarith

/-- Every vector decomposes as a sum of an element of `Ax a b` and an element of `NormSub a b`. -/
lemma decomp_exists (B : AxisBasis a b) (x : Fin 3 ⊕ Fin 1 → ℝ) :
    ∃ w ∈ Ax a b, ∃ z ∈ NormSub a b, x = w + z := by
  obtain ⟨α, β, γ, δ, hx⟩ := B.spanV x
  refine ⟨α • nvec a + β • nvec b, ?_, γ • B.E1 + δ • B.E2, ?_, ?_⟩
  · exact (Ax a b).add_mem ((Ax a b).smul_mem _ (nvec_a_mem_Ax a b))
      ((Ax a b).smul_mem _ (nvec_b_mem_Ax a b))
  · exact (NormSub a b).add_mem ((NormSub a b).smul_mem _ B.mem1)
      ((NormSub a b).smul_mem _ B.mem2)
  · rw [hx]; abel

lemma decomp_unique (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b)
    {w₁ w₂ : Fin 3 ⊕ Fin 1 → ℝ} (hw₁ : w₁ ∈ Ax a b) (hw₂ : w₂ ∈ Ax a b)
    {z₁ z₂ : Fin 3 ⊕ Fin 1 → ℝ} (hz₁ : z₁ ∈ NormSub a b) (hz₂ : z₂ ∈ NormSub a b)
    (h : w₁ + z₁ = w₂ + z₂) : w₁ = w₂ ∧ z₁ = z₂ := by
  have hw : w₁ - w₂ ∈ Ax a b := (Ax a b).sub_mem hw₁ hw₂
  have hz : z₂ - z₁ ∈ NormSub a b := (NormSub a b).sub_mem hz₂ hz₁
  have h0 : w₁ - w₂ = z₂ - z₁ := by
    have key : w₁ - w₂ - (z₂ - z₁) = 0 := by
      have e : w₁ - w₂ - (z₂ - z₁) = (w₁ + z₁) - (w₂ + z₂) := by abel
      rw [e, h, sub_self]
    exact sub_eq_zero.mp key
  have hz0 : w₁ - w₂ = 0 := by
    have hw' : z₂ - z₁ ∈ Ax a b := by rw [← h0]; exact hw
    have hzero : z₂ - z₁ = 0 := Ax_inf_NormSub ha hb hab hw' hz
    rw [h0]; exact hzero
  have hw0 : w₁ = w₂ := sub_eq_zero.mp hz0
  have hz0' : z₂ - z₁ = 0 := by rw [← h0]; exact hz0
  exact ⟨hw0, (sub_eq_zero.mp hz0').symm⟩

/-! ## The normal action as a rotation matrix -/

/-- The action of `emat f` on the positive definite plane `NormSub a b` is a rotation matrix with
angle `± arccos c`. -/
lemma normal_action_matrix (B : AxisBasis a b) (f : PO 3 1) (c : ℝ)
    (hFmem : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ NormSub a b → Matrix.mulVec (emat f) Z ∈ NormSub a b)
    (hscal : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ NormSub a b →
      mink (Matrix.mulVec (emat f) Z) Z = c * mink Z Z) :
    ∃ q : ℝ, q ^ 2 = 1 - c ^ 2 ∧
      Matrix.mulVec (emat f) B.E1 = c • B.E1 + q • B.E2 ∧
      Matrix.mulVec (emat f) B.E2 = -q • B.E1 + c • B.E2 := by
  have hE12 : B.E1 + B.E2 ∈ NormSub a b := (NormSub a b).add_mem B.mem1 B.mem2
  have hc11 : mink (Matrix.mulVec (emat f) B.E1) B.E1 = c := by
    rw [hscal B.E1 B.mem1, B.n11, mul_one]
  have hc22 : mink (Matrix.mulVec (emat f) B.E2) B.E2 = c := by
    rw [hscal B.E2 B.mem2, B.n22, mul_one]
  have hsum := hscal (B.E1 + B.E2) hE12
  have hexp : mink (Matrix.mulVec (emat f) (B.E1 + B.E2)) (B.E1 + B.E2)
      = mink (Matrix.mulVec (emat f) B.E1) B.E1 + mink (Matrix.mulVec (emat f) B.E1) B.E2
        + mink (Matrix.mulVec (emat f) B.E2) B.E1 + mink (Matrix.mulVec (emat f) B.E2) B.E2 := by
    rw [Matrix.mulVec_add]
    simp only [minkSeg_add_left, minkSeg_add_right]
    ring
  have hexp2 : mink (B.E1 + B.E2) (B.E1 + B.E2) = 2 := by
    simp only [minkSeg_add_left, minkSeg_add_right, B.n11, B.n22,
      minkSeg_comm B.E2 B.E1, B.n12]
    ring
  have hcross : mink (Matrix.mulVec (emat f) B.E2) B.E1
      = - mink (Matrix.mulVec (emat f) B.E1) B.E2 := by
    rw [hexp, hexp2, hc11, hc22] at hsum
    linarith
  have hnorm : mink (Matrix.mulVec (emat f) B.E1) (Matrix.mulVec (emat f) B.E1) = 1 := by
    rw [mink_emat_emat, B.n11]
  have hcoord := coord_of_basis B (hFmem B.E1 B.mem1)
  have hcoord2 := coord_of_basis B (hFmem B.E2 B.mem2)
  have hcoord3 : Matrix.mulVec (emat f) B.E1
      = c • B.E1 + mink (Matrix.mulVec (emat f) B.E1) B.E2 • B.E2 := by
    conv_lhs => rw [hcoord]
    rw [hc11]
  have hcoord4 : Matrix.mulVec (emat f) B.E2
      = - mink (Matrix.mulVec (emat f) B.E1) B.E2 • B.E1 + c • B.E2 := by
    conv_lhs => rw [hcoord2]
    rw [hcross, hc22]
  have hnorm2 : mink (Matrix.mulVec (emat f) B.E1) (Matrix.mulVec (emat f) B.E1)
      = c ^ 2 + mink (Matrix.mulVec (emat f) B.E1) B.E2 ^ 2 := by
    conv_lhs => rw [hcoord3]
    rw [mink_expand2]
    simp only [B.n11, B.n22, minkSeg_comm B.E2 B.E1, B.n12]
    ring
  refine ⟨mink (Matrix.mulVec (emat f) B.E1) B.E2, ?_, hcoord3, hcoord4⟩
  linarith [hnorm, hnorm2]


/-! ## Eigenvectors of the normal action -/

lemma normal_action_coord (B : AxisBasis a b) (f : PO 3 1) (c q : ℝ)
    (h1 : Matrix.mulVec (emat f) B.E1 = c • B.E1 + q • B.E2)
    (h2 : Matrix.mulVec (emat f) B.E2 = -q • B.E1 + c • B.E2)
    {Z : Fin 3 ⊕ Fin 1 → ℝ} (hZ : Z ∈ NormSub a b) :
    Matrix.mulVec (emat f) Z
      = (c * mink Z B.E1 - q * mink Z B.E2) • B.E1
        + (q * mink Z B.E1 + c * mink Z B.E2) • B.E2 := by
  conv_lhs => rw [coord_of_basis B hZ]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h2]
  simp only [smul_add, smul_smul]
  module

/-- A real eigenvector of the normal action is zero. -/
lemma eq_zero_of_normal_eigen (B : AxisBasis a b) (f : PO 3 1) (c q ρ : ℝ)
    (hc : c ^ 2 < 1) (hq : q ^ 2 = 1 - c ^ 2)
    (h1 : Matrix.mulVec (emat f) B.E1 = c • B.E1 + q • B.E2)
    (h2 : Matrix.mulVec (emat f) B.E2 = -q • B.E1 + c • B.E2)
    {Z : Fin 3 ⊕ Fin 1 → ℝ} (hZ : Z ∈ NormSub a b)
    (h : Matrix.mulVec (emat f) Z = ρ • Z) : Z = 0 := by
  have hZc := coord_of_basis B hZ
  have hρZ : ρ • Z = (ρ * mink Z B.E1) • B.E1 + (ρ * mink Z B.E2) • B.E2 := by
    conv_lhs => rw [hZc]
    rw [smul_add, smul_smul, smul_smul]
  have hFZ := normal_action_coord B f c q h1 h2 hZ
  have heq : (c * mink Z B.E1 - q * mink Z B.E2) • B.E1
        + (q * mink Z B.E1 + c * mink Z B.E2) • B.E2
      = (ρ * mink Z B.E1) • B.E1 + (ρ * mink Z B.E2) • B.E2 := by
    rw [← hFZ, h, hρZ]
  have hsum : ((c * mink Z B.E1 - q * mink Z B.E2) - ρ * mink Z B.E1) • B.E1
      + ((q * mink Z B.E1 + c * mink Z B.E2) - ρ * mink Z B.E2) • B.E2 = 0 := by
    have e : ((c * mink Z B.E1 - q * mink Z B.E2) - ρ * mink Z B.E1) • B.E1
        + ((q * mink Z B.E1 + c * mink Z B.E2) - ρ * mink Z B.E2) • B.E2
        = ((c * mink Z B.E1 - q * mink Z B.E2) • B.E1
            + (q * mink Z B.E1 + c * mink Z B.E2) • B.E2)
          - ((ρ * mink Z B.E1) • B.E1 + (ρ * mink Z B.E2) • B.E2) := by module
    rw [e, heq, sub_self]
  obtain ⟨e1', e2'⟩ := basis_indep_pair B hsum
  have e1 : (c - ρ) * mink Z B.E1 - q * mink Z B.E2 = 0 := by linarith
  have e2 : q * mink Z B.E1 + (c - ρ) * mink Z B.E2 = 0 := by linarith
  have hdetne : (c - ρ) ^ 2 + q ^ 2 ≠ 0 := by
    intro h0
    have hq0 : q ^ 2 = 0 := by linarith [h0, sq_nonneg (c - ρ)]
    have hc2 : c ^ 2 = 1 := by linarith [hq, hq0]
    linarith [hc, hc2]
  have hx0 : mink Z B.E1 = 0 := by
    have h : ((c - ρ) ^ 2 + q ^ 2) * mink Z B.E1 = 0 := by
      have hh : (c - ρ) * ((c - ρ) * mink Z B.E1 - q * mink Z B.E2)
          + q * (q * mink Z B.E1 + (c - ρ) * mink Z B.E2) = 0 := by rw [e1, e2]; ring
      nlinarith [hh]
    exact (mul_eq_zero.mp h).resolve_left hdetne
  have hy0 : mink Z B.E2 = 0 := by
    have h : ((c - ρ) ^ 2 + q ^ 2) * mink Z B.E2 = 0 := by
      have hh : (c - ρ) * (q * mink Z B.E1 + (c - ρ) * mink Z B.E2)
          - q * ((c - ρ) * mink Z B.E1 - q * mink Z B.E2) = 0 := by rw [e1, e2]; ring
      nlinarith [hh]
    exact (mul_eq_zero.mp h).resolve_left hdetne
  rw [hZc, hx0, hy0, zero_smul, zero_smul, add_zero]

/-- A real eigenvector of `emat f` lies in the Minkowski plane of its axis. -/
lemma mem_Ax_of_eigen (B : AxisBasis a b) (f : PO 3 1) (c q ρ : ℝ)
    (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b)
    (hfa : Matrix.mulVec (emat f) (nvec a) = nvec a)
    (hfb : Matrix.mulVec (emat f) (nvec b) = nvec b)
    (hFmem : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ NormSub a b → Matrix.mulVec (emat f) Z ∈ NormSub a b)
    (hc : c ^ 2 < 1) (hq : q ^ 2 = 1 - c ^ 2)
    (h1 : Matrix.mulVec (emat f) B.E1 = c • B.E1 + q • B.E2)
    (h2 : Matrix.mulVec (emat f) B.E2 = -q • B.E1 + c • B.E2)
    {x : Fin 3 ⊕ Fin 1 → ℝ} (h : Matrix.mulVec (emat f) x = ρ • x) : x ∈ Ax a b := by
  obtain ⟨w, hw, z, hz, hxwz⟩ := decomp_exists B x
  have hFw : Matrix.mulVec (emat f) w = w := emat_mulVec_eq_self_of_mem_Ax f hfa hfb hw
  have hFx : Matrix.mulVec (emat f) x = w + Matrix.mulVec (emat f) z := by
    rw [hxwz, Matrix.mulVec_add, hFw]
  have hρx : ρ • x = ρ • w + ρ • z := by rw [hxwz, smul_add]
  have heq : w + Matrix.mulVec (emat f) z = ρ • w + ρ • z := by
    rw [← hFx, h, hρx]
  obtain ⟨-, hzeq⟩ := decomp_unique ha hb hab hw ((Ax a b).smul_mem ρ hw)
    (hFmem z hz) ((NormSub a b).smul_mem ρ hz) heq
  have hz0 : z = 0 := eq_zero_of_normal_eigen B f c q ρ hc hq h1 h2 hz hzeq
  rw [hxwz, hz0, add_zero]
  exact hw

/-- The only real eigenvalue of `emat f` is `1`, realised exactly on `Ax a b`. -/
lemma eq_zero_of_eigen_of_ne_one (B : AxisBasis a b) (f : PO 3 1) (c q ρ : ℝ)
    (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b)
    (hfa : Matrix.mulVec (emat f) (nvec a) = nvec a)
    (hfb : Matrix.mulVec (emat f) (nvec b) = nvec b)
    (hFmem : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ NormSub a b → Matrix.mulVec (emat f) Z ∈ NormSub a b)
    (hc : c ^ 2 < 1) (hq : q ^ 2 = 1 - c ^ 2)
    (h1 : Matrix.mulVec (emat f) B.E1 = c • B.E1 + q • B.E2)
    (h2 : Matrix.mulVec (emat f) B.E2 = -q • B.E1 + c • B.E2)
    (hρ : ρ ≠ 1) {x : Fin 3 ⊕ Fin 1 → ℝ} (h : Matrix.mulVec (emat f) x = ρ • x) : x = 0 := by
  have hxAx := mem_Ax_of_eigen B f c q ρ ha hb hab hfa hfb hFmem hc hq h1 h2 h
  have hfix := emat_mulVec_eq_self_of_mem_Ax f hfa hfb hxAx
  have hρx : ρ • x = x := by rw [← h, hfix]
  have hzero : (ρ - 1) • x = 0 := by rw [sub_smul, one_smul, hρx, sub_self]
  rcases smul_eq_zero.mp hzero with h' | h'
  · exact absurd (sub_eq_zero.mp h') hρ
  · exact h'

/-- `emat f` has no eigenvector with eigenvalue `-1`. -/
lemma eq_zero_of_eigen_neg (B : AxisBasis a b) (f : PO 3 1) (c q : ℝ)
    (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b)
    (hfa : Matrix.mulVec (emat f) (nvec a) = nvec a)
    (hfb : Matrix.mulVec (emat f) (nvec b) = nvec b)
    (hFmem : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ NormSub a b → Matrix.mulVec (emat f) Z ∈ NormSub a b)
    (hc : c ^ 2 < 1) (hq : q ^ 2 = 1 - c ^ 2)
    (h1 : Matrix.mulVec (emat f) B.E1 = c • B.E1 + q • B.E2)
    (h2 : Matrix.mulVec (emat f) B.E2 = -q • B.E1 + c • B.E2)
    {x : Fin 3 ⊕ Fin 1 → ℝ} (h : Matrix.mulVec (emat f) x = (-1 : ℝ) • x) : x = 0 :=
  eq_zero_of_eigen_of_ne_one B f c q (-1) ha hb hab hfa hfb hFmem hc hq h1 h2 (by norm_num) h

/-! ## The null vectors of `Ax a b`, and equality of Minkowski planes -/

/-- Two independent null vectors span a basis of the plane. -/
lemma nvec_pair_indep (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) {α β : ℝ}
    (h : α • nvec a + β • nvec b = 0) : α = 0 ∧ β = 0 := by
  have hκ : mink (nvec a) (nvec b) ≠ 0 := mink_nvec_pair_ne_zero ha hb hab
  have h1 : α * mink (nvec a) (nvec b) = 0 := by
    have hh : mink (α • nvec a + β • nvec b) (nvec b) = 0 := by rw [h]; simp [mink]
    rw [minkSeg_add_left, mink_smul_left'', mink_smul_left'', mink_nvec_self' hb,
      mul_zero, add_zero] at hh
    exact hh
  have h2 : β * mink (nvec a) (nvec b) = 0 := by
    have hh : mink (α • nvec a + β • nvec b) (nvec a) = 0 := by rw [h]; simp [mink]
    rw [minkSeg_add_left, mink_smul_left'', mink_smul_left'', mink_nvec_self' ha,
      mul_zero, zero_add, ← minkSeg_comm (nvec a) (nvec b)] at hh
    exact hh
  exact ⟨(mul_eq_zero.mp h1).resolve_right hκ, (mul_eq_zero.mp h2).resolve_right hκ⟩

/-- A null vector of the plane is a multiple of one of the two null generators. -/
lemma eq_smul_nvec_of_null (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b)
    {x : Fin 3 ⊕ Fin 1 → ℝ} (hx : x ∈ Ax a b) (h0 : mink x x = 0) :
    (∃ μ : ℝ, x = μ • nvec a) ∨ (∃ ν : ℝ, x = ν • nvec b) := by
  obtain ⟨α, β, hx'⟩ := (mem_Ax_iff x).mp hx
  have hκ : mink (nvec a) (nvec b) ≠ 0 := mink_nvec_pair_ne_zero ha hb hab
  have h2 : α * β = 0 := by
    have h := h0
    rw [hx'] at h
    rw [mink_expand2, mink_nvec_self' ha, mink_nvec_self' hb,
      ← minkSeg_comm (nvec a) (nvec b)] at h
    have h3 : (2 * (α * β)) * mink (nvec a) (nvec b) = 0 := by linarith
    rcases mul_eq_zero.mp h3 with h4 | h4
    · linarith
    · exact absurd h4 hκ
  rcases mul_eq_zero.mp h2 with hα | hβ
  · exact Or.inr ⟨β, by rw [hx', hα, zero_smul, zero_add]⟩
  · exact Or.inl ⟨α, by rw [hx', hβ, zero_smul, add_zero]⟩

/-- A nonzero vector of `NormSub a b` has positive Minkowski square. -/
lemma mink_pos_of_mem_NormSub (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b)
    {Z : Fin 3 ⊕ Fin 1 → ℝ} (hZ : Z ∈ NormSub a b) (h0 : Z ≠ 0) : 0 < mink Z Z := by
  rcases lt_or_eq_of_le (mink_nonneg_of_mem_NormSub ha hZ) with h | h
  · exact h
  · exact absurd (eq_zero_of_mem_NormSub_of_mink_self_eq_zero ha hb hab hZ h.symm) h0

/-- If a Minkowski plane contains the whole normal plane of another one, the two coincide. -/
lemma Ax_le_symm_of_le (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b)
    (ha' : a' ∈ Sph 3) (hb' : b' ∈ Sph 3) (hab' : a' ≠ b')
    (h : Ax a' b' ≤ Ax a b) : Ax a b ≤ Ax a' b' := by
  have h1 := eq_smul_nvec_of_null ha hb hab (h (nvec_a_mem_Ax a' b')) (mink_nvec_self' ha')
  have h2 := eq_smul_nvec_of_null ha hb hab (h (nvec_b_mem_Ax a' b')) (mink_nvec_self' hb')
  have ha'0 : nvec a' ≠ 0 := fun hh => by
    have := congrFun hh (Sum.inr 0); simp [nvec] at this
  have hb'0 : nvec b' ≠ 0 := fun hh => by
    have := congrFun hh (Sum.inr 0); simp [nvec] at this
  rcases h1 with ⟨μ, hμ⟩ | ⟨μ, hμ⟩ <;> rcases h2 with ⟨ν, hν⟩ | ⟨ν, hν⟩
  · -- both are multiples of `θ_a`: impossible
    exfalso
    have hind := nvec_pair_indep ha' hb' hab' (α := -ν) (β := μ)
      (by rw [hμ, hν]; module)
    rw [neg_eq_zero] at hind
    exact ha'0 (by rw [hμ, hind.2, zero_smul])
  · -- `θ_a` is a multiple of `θ_a'`, `θ_b` a multiple of `θ_b'`
    have hμ0 : μ ≠ 0 := fun hh => ha'0 (by rw [hμ, hh, zero_smul])
    have hν0 : ν ≠ 0 := fun hh => hb'0 (by rw [hν, hh, zero_smul])
    intro y hy
    obtain ⟨r, s, hy'⟩ := (mem_Ax_iff y).mp hy
    have hθa : nvec a ∈ Ax a' b' := by
      have : nvec a = μ⁻¹ • nvec a' := by rw [hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
      rw [this]; exact (Ax a' b').smul_mem _ (nvec_a_mem_Ax a' b')
    have hθb : nvec b ∈ Ax a' b' := by
      have : nvec b = ν⁻¹ • nvec b' := by rw [hν, smul_smul, inv_mul_cancel₀ hν0, one_smul]
      rw [this]; exact (Ax a' b').smul_mem _ (nvec_b_mem_Ax a' b')
    rw [hy']
    exact (Ax a' b').add_mem ((Ax a' b').smul_mem _ hθa) ((Ax a' b').smul_mem _ hθb)
  · have hμ0 : μ ≠ 0 := fun hh => ha'0 (by rw [hμ, hh, zero_smul])
    have hν0 : ν ≠ 0 := fun hh => hb'0 (by rw [hν, hh, zero_smul])
    intro y hy
    obtain ⟨r, s, hy'⟩ := (mem_Ax_iff y).mp hy
    have hθb : nvec b ∈ Ax a' b' := by
      have : nvec b = μ⁻¹ • nvec a' := by rw [hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
      rw [this]; exact (Ax a' b').smul_mem _ (nvec_a_mem_Ax a' b')
    have hθa : nvec a ∈ Ax a' b' := by
      have : nvec a = ν⁻¹ • nvec b' := by rw [hν, smul_smul, inv_mul_cancel₀ hν0, one_smul]
      rw [this]; exact (Ax a' b').smul_mem _ (nvec_b_mem_Ax a' b')
    rw [hy']
    exact (Ax a' b').add_mem ((Ax a' b').smul_mem _ hθa) ((Ax a' b').smul_mem _ hθb)
  · exfalso
    have hind := nvec_pair_indep ha' hb' hab' (α := -ν) (β := μ)
      (by rw [hμ, hν]; module)
    rw [neg_eq_zero] at hind
    exact ha'0 (by rw [hμ, hind.2, zero_smul])

/-! ## The main plane argument -/

/-- **The axis is determined.**  If `emat f` rotates the positive definite normal plane
`NormSub a b` by a non-trivial angle (`c² < 1`) and preserves the Minkowski plane `Ax a' b'`, then
the two Minkowski planes coincide. -/
theorem plane_eq_of_fixes (hA : POActionProp 3)
    (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b)
    (ha' : a' ∈ Sph 3) (hb' : b' ∈ Sph 3) (hab' : a' ≠ b')
    (f : PO 3 1) (c : ℝ) (hc : c ^ 2 < 1) (B : AxisBasis a b)
    (hfa : Matrix.mulVec (emat f) (nvec a) = nvec a)
    (hfb : Matrix.mulVec (emat f) (nvec b) = nvec b)
    (hFmem : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ NormSub a b → Matrix.mulVec (emat f) Z ∈ NormSub a b)
    (hscal : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ NormSub a b →
      mink (Matrix.mulVec (emat f) Z) Z = c * mink Z Z)
    (hFU : ∀ x : Fin 3 ⊕ Fin 1 → ℝ, x ∈ Ax a' b' → Matrix.mulVec (emat f) x ∈ Ax a' b') :
    Ax a' b' = Ax a b := by
  obtain ⟨q, hq, hmat1, hmat2⟩ := normal_action_matrix B f c hFmem hscal
  have hker : ∀ ρ : ℝ, ∀ x : Fin 3 ⊕ Fin 1 → ℝ,
      Matrix.mulVec (emat f) x = ρ • x → x ∈ Ax a b :=
    fun ρ x h => mem_Ax_of_eigen B f c q ρ ha hb hab hfa hfb hFmem hc hq hmat1 hmat2 h
  have hker_ne : ∀ ρ : ℝ, ρ ≠ 1 → ∀ x : Fin 3 ⊕ Fin 1 → ℝ,
      Matrix.mulVec (emat f) x = ρ • x → x = 0 :=
    fun ρ hρ x h =>
      eq_zero_of_eigen_of_ne_one B f c q ρ ha hb hab hfa hfb hFmem hc hq hmat1 hmat2 hρ h
  have hnz : ∀ ξ : E 3, nvec ξ ≠ 0 := fun ξ hh => by
    have := congrFun hh (Sum.inr 0); simp [nvec] at this
  have hκ' : mink (nvec a') (nvec b') ≠ 0 := mink_nvec_pair_ne_zero ha' hb' hab'
  have hFUa : Matrix.mulVec (emat f) (nvec a') ∈ Ax a' b' := hFU _ (nvec_a_mem_Ax a' b')
  have hFUb : Matrix.mulVec (emat f) (nvec b') ∈ Ax a' b' := hFU _ (nvec_b_mem_Ax a' b')
  have hnull_a : mink (Matrix.mulVec (emat f) (nvec a')) (Matrix.mulVec (emat f) (nvec a'))
      = 0 := by rw [mink_emat_emat, mink_nvec_self' ha']
  have hnull_b : mink (Matrix.mulVec (emat f) (nvec b')) (Matrix.mulVec (emat f) (nvec b'))
      = 0 := by rw [mink_emat_emat, mink_nvec_self' hb']
  have hcase_a := eq_smul_nvec_of_null ha' hb' hab' hFUa hnull_a
  have hcase_b := eq_smul_nvec_of_null ha' hb' hab' hFUb hnull_b
  have hindep_F : ∀ (α β : ℝ),
      α • Matrix.mulVec (emat f) (nvec a') + β • Matrix.mulVec (emat f) (nvec b') = 0 →
      α = 0 ∧ β = 0 := by
    intro α β h
    have h0 : Matrix.mulVec (emat f) (α • nvec a' + β • nvec b') = 0 := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h]
    have h1 : α • nvec a' + β • nvec b' = 0 := (emat_mulVec_eq_zero_iff hA f).mp h0
    exact nvec_pair_indep ha' hb' hab' h1
  rcases hcase_a with ⟨lam, hlam⟩ | ⟨lam, hlam⟩ <;> rcases hcase_b with ⟨mu, hmu⟩ | ⟨mu, hmu⟩
  · -- both images are multiples of `θ_{a'}`: impossible
    exfalso
    have hind := hindep_F mu (-lam) (by rw [hlam, hmu]; module)
    have hlam0 : lam = 0 := neg_eq_zero.mp hind.2
    have hz : Matrix.mulVec (emat f) (nvec a') = 0 := by rw [hlam, hlam0, zero_smul]
    exact hnz a' ((emat_mulVec_eq_zero_iff hA f).mp hz)
  · -- the `fix` case: `F θ_{a'} = lam θ_{a'}`, `F θ_{b'} = mu θ_{b'}`
    have hlamu : lam * mu = 1 := by
      have h : mink (Matrix.mulVec (emat f) (nvec a')) (Matrix.mulVec (emat f) (nvec b'))
          = mink (nvec a') (nvec b') := mink_emat_emat f _ _
      rw [hlam, hmu, minkSeg_smul] at h
      exact mul_right_cancel₀ hκ' (by linarith [h])
    by_cases hfixex : ∃ x : Fin 3 ⊕ Fin 1 → ℝ,
        x ∈ Ax a' b' ∧ x ≠ 0 ∧ Matrix.mulVec (emat f) x = x
    · -- a nonzero fixed vector of `U` exists: then `U ≤ W`
      obtain ⟨x, hxU, hx0, hxFx⟩ := hfixex
      obtain ⟨μ₀, ν₀, hx'⟩ := (mem_Ax_iff x).mp hxU
      have heq : (μ₀ * lam - μ₀) • nvec a' + (ν₀ * mu - ν₀) • nvec b' = 0 := by
        have h2 : (μ₀ * lam) • nvec a' + (ν₀ * mu) • nvec b' = μ₀ • nvec a' + ν₀ • nvec b' := by
          have hFx : Matrix.mulVec (emat f) x = (μ₀ * lam) • nvec a' + (ν₀ * mu) • nvec b' := by
            rw [hx', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hlam, hmu]
            module
          rw [← hFx, hxFx, hx']
        have e : (μ₀ * lam - μ₀) • nvec a' + (ν₀ * mu - ν₀) • nvec b'
            = ((μ₀ * lam) • nvec a' + (ν₀ * mu) • nvec b')
              - (μ₀ • nvec a' + ν₀ • nvec b') := by module
        rw [e, h2, sub_self]
      obtain ⟨hlam0, hmu0⟩ := nvec_pair_indep ha' hb' hab' heq
      have hlam0' : (lam - 1) * μ₀ = 0 := by linarith
      have hmu0' : (mu - 1) * ν₀ = 0 := by linarith
      have hlam1 : lam = 1 := by
        rcases mul_eq_zero.mp hlam0' with h | h
        · linarith
        · have hν0 : ν₀ ≠ 0 := fun hh => hx0 (by rw [hx', h, hh, zero_smul, zero_smul, add_zero])
          have hmu1 : mu = 1 := by
            rcases mul_eq_zero.mp hmu0' with h2 | h2
            · linarith
            · exact absurd h2 hν0
          rw [hmu1, mul_one] at hlamu
          exact hlamu
      have hmu1 : mu = 1 := by rw [← hlamu, hlam1, one_mul]
      have hidU : ∀ y ∈ Ax a' b', Matrix.mulVec (emat f) y = y := by
        intro y hy
        obtain ⟨r, s, hy'⟩ := (mem_Ax_iff y).mp hy
        rw [hy', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hlam, hmu, hlam1, hmu1]
        simp
      have hUle : Ax a' b' ≤ Ax a b := by
        intro y hy
        exact hker 1 y (by simpa using hidU y hy)
      exact le_antisymm hUle (Ax_le_symm_of_le ha hb hab ha' hb' hab' hUle)
    · -- no nonzero fixed vector in `U`: the scalar identity gives a contradiction
      exfalso
      push_neg at hfixex
      have hzex : ∃ z : Fin 3 ⊕ Fin 1 → ℝ, z ∈ Ax a' b' ∧ z ∈ NormSub a b ∧ z ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        have hUle : Ax a' b' ≤ Ax a b := by
          intro y hy
          obtain ⟨w, hw, z, hz, hy'⟩ := decomp_exists B y
          have hFy : Matrix.mulVec (emat f) y = w + Matrix.mulVec (emat f) z := by
            rw [hy', Matrix.mulVec_add, emat_mulVec_eq_self_of_mem_Ax f hfa hfb hw]
          have h1 : Matrix.mulVec (emat f) y - y ∈ Ax a' b' :=
            (Ax a' b').sub_mem (hFU y hy) hy
          have h2 : Matrix.mulVec (emat f) z - z = Matrix.mulVec (emat f) y - y := by
            rw [hFy, hy']; abel
          have hz1 : Matrix.mulVec (emat f) z - z ∈ Ax a' b' := by rwa [← h2] at h1
          have hz2 : Matrix.mulVec (emat f) z - z ∈ NormSub a b :=
            (NormSub a b).sub_mem (hFmem z hz) hz
          have hz0 : Matrix.mulVec (emat f) z - z = 0 := hcon _ hz1 hz2
          have hzfix : Matrix.mulVec (emat f) z = z := sub_eq_zero.mp hz0
          have hzzero : z = 0 := eq_zero_of_normal_eigen B f c q 1 hc hq hmat1 hmat2 hz
            (by rw [one_smul]; exact hzfix)
          rw [hy', hzzero, add_zero]
          exact hw
        exact hfixex (nvec a') (nvec_a_mem_Ax a' b') (hnz a')
          (emat_mulVec_eq_self_of_mem_Ax f hfa hfb (hUle (nvec_a_mem_Ax a' b')))
      obtain ⟨z, hzU, hzZP, hz0⟩ := hzex
      obtain ⟨μ₀, ν₀, hz'⟩ := (mem_Ax_iff z).mp hzU
      have hzz : mink z z = 2 * (μ₀ * ν₀ * mink (nvec a') (nvec b')) := by
        rw [hz', mink_expand2, mink_nvec_self' ha', mink_nvec_self' hb',
          ← minkSeg_comm (nvec a') (nvec b')]
        ring
      have hKpos : 0 < μ₀ * ν₀ * mink (nvec a') (nvec b') := by
        have h := mink_pos_of_mem_NormSub ha hb hab hzZP hz0
        rw [hzz] at h; linarith
      have hFz : Matrix.mulVec (emat f) z = (μ₀ * lam) • nvec a' + (ν₀ * mu) • nvec b' := by
        rw [hz', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hlam, hmu]
        module
      have hmm : mink (Matrix.mulVec (emat f) z) z
          = (μ₀ * ν₀ * mink (nvec a') (nvec b')) * (lam + mu) := by
        rw [hFz, hz', mink_expand2, mink_nvec_self' ha', mink_nvec_self' hb',
          ← minkSeg_comm (nvec a') (nvec b')]
        ring
      have hT : lam + mu = 2 * c := by
        have h := hscal z hzZP
        rw [hmm, hzz] at h
        have h' : (μ₀ * ν₀ * mink (nvec a') (nvec b')) * (lam + mu)
            = (μ₀ * ν₀ * mink (nvec a') (nvec b')) * (2 * c) := by
          rw [h]; ring
        exact mul_left_cancel₀ (ne_of_gt hKpos) h'
      have hcontra : (lam - mu) ^ 2 = 4 * c ^ 2 - 4 := by
        have h1 : (lam - mu) ^ 2 = (lam + mu) ^ 2 - 4 * (lam * mu) := by ring
        rw [h1, hT, hlamu]
        ring
      have hc2 : 4 * c ^ 2 - 4 < 0 := by nlinarith [hc]
      have hnn := sq_nonneg (lam - mu)
      rw [hcontra] at hnn
      linarith
  · -- the `swap` case: `F θ_{a'} = lam θ_{b'}`, `F θ_{b'} = mu θ_{a'}`
    exfalso
    have hlamu : lam * mu = 1 := by
      have h : mink (Matrix.mulVec (emat f) (nvec a')) (Matrix.mulVec (emat f) (nvec b'))
          = mink (nvec a') (nvec b') := mink_emat_emat f _ _
      rw [hlam, hmu, minkSeg_smul, ← minkSeg_comm (nvec a') (nvec b')] at h
      exact mul_right_cancel₀ hκ' (by linarith [h])
    have hF2 : ∀ y ∈ Ax a' b', Matrix.mulVec (emat f) (Matrix.mulVec (emat f) y) = y := by
      intro y hy
      obtain ⟨r, s, hy'⟩ := (mem_Ax_iff y).mp hy
      have hFy : Matrix.mulVec (emat f) y = (r * lam) • nvec b' + (s * mu) • nvec a' := by
        rw [hy', Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hlam, hmu]
        module
      have hFFy : Matrix.mulVec (emat f) (Matrix.mulVec (emat f) y)
          = ((r * lam) * mu) • nvec a' + ((s * mu) * lam) • nvec b' := by
        rw [hFy, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hlam, hmu]
        module
      rw [hFFy, hy', show (r * lam) * mu = r from by rw [mul_assoc, hlamu, mul_one],
        show (s * mu) * lam = s from by rw [mul_assoc, mul_comm mu lam, hlamu, mul_one]]
    by_cases hker2 : ∃ y ∈ Ax a' b', y ≠ 0 ∧ Matrix.mulVec (emat f) y = (-1 : ℝ) • y
    · obtain ⟨y, -, hy0, hyy⟩ := hker2
      exact hy0 (eq_zero_of_eigen_neg B f c q ha hb hab hfa hfb hFmem hc hq hmat1 hmat2 hyy)
    · push_neg at hker2
      have hid : ∀ y ∈ Ax a' b', Matrix.mulVec (emat f) y = y := by
        intro y hy
        have h1 : Matrix.mulVec (emat f) (Matrix.mulVec (emat f) y - y)
            = (-1 : ℝ) • (Matrix.mulVec (emat f) y - y) := by
          rw [Matrix.mulVec_sub, hF2 y hy, neg_smul, one_smul]
          abel
        have h2 : Matrix.mulVec (emat f) y - y ∈ Ax a' b' := (Ax a' b').sub_mem (hFU _ hy) hy
        by_contra hne
        have h3 : Matrix.mulVec (emat f) y - y ≠ 0 := sub_ne_zero.mpr hne
        exact (hker2 _ h2 h3) h1
      have hcontra : lam • nvec b' = nvec a' := by
        rw [← hlam, hid (nvec a') (nvec_a_mem_Ax a' b')]
      have hind := nvec_pair_indep ha' hb' hab' (α := -1) (β := lam) (by rw [hcontra]; module)
      exact (by norm_num : (-1 : ℝ) ≠ 0) hind.1
  · -- both images are multiples of `θ_{b'}`: impossible
    exfalso
    have hind := hindep_F mu (-lam) (by rw [hlam, hmu]; module)
    have hlam0 : lam = 0 := neg_eq_zero.mp hind.2
    have hz : Matrix.mulVec (emat f) (nvec a') = 0 := by rw [hlam, hlam0, zero_smul]
    exact hnz a' ((emat_mulVec_eq_zero_iff hA f).mp hz)


/-! ## An `AxisBasis` from the orthonormal basis of the normal plane -/

lemma exists_axisBasis (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b) :
    ∃ B : AxisBasis a b, True := by
  obtain ⟨E1, E2, hE1, hE2, h11, h22, h12, hcoord, hspanV⟩ :=
    normSub_orthonormalBasis a b ha hb hab
  exact ⟨⟨E1, E2, hE1, hE2, h11, h22, h12,
      fun Z hZ => ⟨mink Z E1, mink Z E2, hcoord Z hZ⟩, hspanV⟩, trivial⟩

/-! ## Two elementary module identities -/

lemma smul_rot_comp {V : Type*} [AddCommGroup V] [Module ℝ V] (c q : ℝ) (hq : c ^ 2 + q ^ 2 = 1)
    (x y : V) : c • (c • x + q • y) + (-q) • ((-q) • x + c • y) = x := by
  have h1 : c * c + (-q) * (-q) = 1 := by nlinarith [hq]
  have h2 : c * q + (-q) * c = 0 := by ring
  calc c • (c • x + q • y) + (-q) • ((-q) • x + c • y)
      = ((c * c) • x + (c * q) • y) + (((-q) * (-q)) • x + ((-q) * c) • y) := by
        rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    _ = x := by
        rw [show ((c * c) • x + (c * q) • y) + (((-q) * (-q)) • x + ((-q) * c) • y)
              = ((c * c) + ((-q) * (-q))) • x + ((c * q) + ((-q) * c)) • y from by module,
          h1, h2, one_smul, zero_smul, add_zero]

lemma smul_rot_comp' {V : Type*} [AddCommGroup V] [Module ℝ V] (c q : ℝ) (hq : c ^ 2 + q ^ 2 = 1)
    (x y : V) : q • (c • x + q • y) + c • ((-q) • x + c • y) = y := by
  have h1 : q * q + c * c = 1 := by nlinarith [hq]
  have h2 : q * c + c * (-q) = 0 := by ring
  calc q • (c • x + q • y) + c • ((-q) • x + c • y)
      = ((q * c) • x + (q * q) • y) + ((c * (-q)) • x + (c * c) • y) := by
        rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, smul_smul]
    _ = y := by
        rw [show ((q * c) • x + (q * q) • y) + ((c * (-q)) • x + (c * c) • y)
              = ((q * c) + (c * (-q))) • x + ((q * q) + (c * c)) • y from by module,
          h2, h1, zero_smul, one_smul, zero_add]

/-! ## The main theorem -/

/-- Two rotations by the same angle `2π/M` (`M ≥ 6`) about (possibly different) geodesics which
commute are equal up to inversion. -/
theorem commutingRotation_eq_or_inv (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3) (M : ℕ) (hM : 6 ≤ M)
    (a b a' b' : Submission.Mostow.E 3) (ha : a ∈ Submission.Mostow.Sph 3)
    (hb : b ∈ Submission.Mostow.Sph 3) (ha' : a' ∈ Submission.Mostow.Sph 3)
    (hb' : b' ∈ Submission.Mostow.Sph 3) (hab : a ≠ b) (hab' : a' ≠ b')
    (f g : LeanEval.Geometry.MostowRigidity.PO 3 1)
    (hf : Work.Mostow.IsRotationAbout f a b (2 * Real.pi / (M : ℝ)))
    (hg : Work.Mostow.IsRotationAbout g a' b' (2 * Real.pi / (M : ℝ)))
    (hcomm : f * g = g * f) :
    g = f ∨ g = f⁻¹ := by
  obtain ⟨B, -⟩ := exists_axisBasis (a := a) (b := b) ha hb hab
  obtain ⟨B', -⟩ := exists_axisBasis (a := a') (b := b') ha' hb' hab'
  have hfix_f : ∀ u : Submission.Mostow.E 3, u ∈ geodSet a b → f • u = u :=
    fun u hu => (hf.1 u).mpr hu
  have hfix_g : ∀ u : Submission.Mostow.E 3, u ∈ geodSet a' b' → g • u = u :=
    fun u hu => (hg.1 u).mpr hu
  have hdisp_f : ∀ u : Submission.Mostow.E 3, hdist u (f • u)
      = 2 * Real.arsinh (Real.sinh (distGeod a b u) * Real.sin (Real.pi / (M : ℝ))) := by
    intro u
    rw [hf.2 u, show (2 * Real.pi / (M : ℝ)) / 2 = Real.pi / (M : ℝ) from by ring]
  have hdisp_g : ∀ u : Submission.Mostow.E 3, hdist u (g • u)
      = 2 * Real.arsinh (Real.sinh (distGeod a' b' u) * Real.sin (Real.pi / (M : ℝ))) := by
    intro u
    rw [hg.2 u, show (2 * Real.pi / (M : ℝ)) / 2 = Real.pi / (M : ℝ) from by ring]
  obtain ⟨hfa, hfb⟩ := emat_fixes_nvec hA hI f a b ha hb hab hfix_f
  obtain ⟨hga, hgb⟩ := emat_fixes_nvec hA hI g a' b' ha' hb' hab' hfix_g
  have hFmem : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ,
      Z ∈ NormSub a b → Matrix.mulVec (emat f) Z ∈ NormSub a b :=
    fun Z hZ => emat_mulVec_mem_NormSub f hfa hfb hZ
  have hGmem : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ,
      Z ∈ NormSub a' b' → Matrix.mulVec (emat g) Z ∈ NormSub a' b' :=
    fun Z hZ => emat_mulVec_mem_NormSub g hga hgb hZ
  have hscal_f : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ NormSub a b →
      mink (Matrix.mulVec (emat f) Z) Z = cM M * mink Z Z :=
    scalar_identity hA hI ha hb hab M hM f hfix_f hdisp_f (gcN_surjective a b ha hb hab)
  have hscal_g : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ NormSub a' b' →
      mink (Matrix.mulVec (emat g) Z) Z = cM M * mink Z Z :=
    scalar_identity hA hI ha' hb' hab' M hM g hfix_g hdisp_g (gcN_surjective a' b' ha' hb' hab')
  have hcomm_mat : emat f * emat g = emat g * emat f := by
    rw [← emat_mul hA, hcomm, emat_mul hA]
  -- `G` fixes its axis plane `Ax a' b'` pointwise
  obtain ⟨q', hq', hmat1', hmat2'⟩ := normal_action_matrix B' g (cM M) hGmem hscal_g
  have hkerG : ∀ x : Fin 3 ⊕ Fin 1 → ℝ, Matrix.mulVec (emat g) x = x → x ∈ Ax a' b' :=
    fun x h => mem_Ax_of_eigen B' g (cM M) q' 1 ha' hb' hab' hga hgb hGmem
      (cM_sq_lt_one M hM) hq' hmat1' hmat2' (by rw [one_smul]; exact h)
  have hFU : ∀ x : Fin 3 ⊕ Fin 1 → ℝ, x ∈ Ax a' b' → Matrix.mulVec (emat f) x ∈ Ax a' b' := by
    intro x hx
    have h1 : Matrix.mulVec (emat g) (Matrix.mulVec (emat f) x) = Matrix.mulVec (emat f) x := by
      rw [Matrix.mulVec_mulVec, ← hcomm_mat, ← Matrix.mulVec_mulVec,
        emat_mulVec_eq_self_of_mem_Ax g hga hgb hx]
    exact hkerG _ h1
  have hplane : Ax a' b' = Ax a b :=
    plane_eq_of_fixes hA ha hb hab ha' hb' hab' f (cM M) (cM_sq_lt_one M hM) B
      hfa hfb hFmem hscal_f hFU
  -- symmetrically, `G` preserves `Ax a b`
  obtain ⟨q, hq, hmat1, hmat2⟩ := normal_action_matrix B f (cM M) hFmem hscal_f
  have hkerF : ∀ x : Fin 3 ⊕ Fin 1 → ℝ, Matrix.mulVec (emat f) x = x → x ∈ Ax a b :=
    fun x h => mem_Ax_of_eigen B f (cM M) q 1 ha hb hab hfa hfb hFmem
      (cM_sq_lt_one M hM) hq hmat1 hmat2 (by rw [one_smul]; exact h)
  have hGU : ∀ x : Fin 3 ⊕ Fin 1 → ℝ, x ∈ Ax a b → Matrix.mulVec (emat g) x ∈ Ax a b := by
    intro x hx
    have h1 : Matrix.mulVec (emat f) (Matrix.mulVec (emat g) x) = Matrix.mulVec (emat g) x := by
      rw [Matrix.mulVec_mulVec, hcomm_mat, ← Matrix.mulVec_mulVec,
        emat_mulVec_eq_self_of_mem_Ax f hfa hfb hx]
    exact hkerF _ h1
  have hplane2 : Ax a b = Ax a' b' :=
    plane_eq_of_fixes hA ha' hb' hab' ha hb hab g (cM M) (cM_sq_lt_one M hM) B'
      hga hgb hGmem hscal_g hGU
  -- the normal planes agree as well
  have hNS : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ NormSub a b ↔ Z ∈ NormSub a' b' := by
    intro Z
    constructor
    · intro hZ
      obtain ⟨h1, h2⟩ := mem_NormSub.mp hZ
      refine mem_NormSub.mpr ⟨?_, ?_⟩
      · have hθ : nvec a' ∈ Ax a b := hplane ▸ nvec_a_mem_Ax a' b'
        obtain ⟨c1, c2, hc⟩ := (mem_Ax_iff (nvec a')).mp hθ
        rw [hc, minkSeg_add_right, mink_smul_right'', mink_smul_right'', h1, h2]
        ring
      · have hθ : nvec b' ∈ Ax a b := hplane ▸ nvec_b_mem_Ax a' b'
        obtain ⟨c1, c2, hc⟩ := (mem_Ax_iff (nvec b')).mp hθ
        rw [hc, minkSeg_add_right, mink_smul_right'', mink_smul_right'', h1, h2]
        ring
    · intro hZ
      obtain ⟨h1, h2⟩ := mem_NormSub.mp hZ
      refine mem_NormSub.mpr ⟨?_, ?_⟩
      · have hθ : nvec a ∈ Ax a' b' := hplane2 ▸ nvec_a_mem_Ax a b
        obtain ⟨c1, c2, hc⟩ := (mem_Ax_iff (nvec a)).mp hθ
        rw [hc, minkSeg_add_right, mink_smul_right'', mink_smul_right'', h1, h2]
        ring
      · have hθ : nvec b ∈ Ax a' b' := hplane2 ▸ nvec_b_mem_Ax a b
        obtain ⟨c1, c2, hc⟩ := (mem_Ax_iff (nvec b)).mp hθ
        rw [hc, minkSeg_add_right, mink_smul_right'', mink_smul_right'', h1, h2]
        ring
  have hscal_g' : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ, Z ∈ NormSub a b →
      mink (Matrix.mulVec (emat g) Z) Z = cM M * mink Z Z :=
    fun Z hZ => hscal_g Z ((hNS Z).mp hZ)
  have hGmem2 : ∀ Z : Fin 3 ⊕ Fin 1 → ℝ,
      Z ∈ NormSub a b → Matrix.mulVec (emat g) Z ∈ NormSub a b :=
    fun Z hZ => (hNS _).mpr (hGmem Z ((hNS Z).mp hZ))
  obtain ⟨q, hq, hmat1, hmat2⟩ := normal_action_matrix B f (cM M) hFmem hscal_f
  obtain ⟨q', hq', hmat1', hmat2'⟩ := normal_action_matrix B g (cM M) hGmem2 hscal_g'
  have hGidW : ∀ x : Fin 3 ⊕ Fin 1 → ℝ, x ∈ Ax a b → Matrix.mulVec (emat g) x = x :=
    fun x hx => emat_mulVec_eq_self_of_mem_Ax g hga hgb (by rw [← hplane2]; exact hx)
  have hFidW : ∀ x : Fin 3 ⊕ Fin 1 → ℝ, x ∈ Ax a b → Matrix.mulVec (emat f) x = x :=
    fun x hx => emat_mulVec_eq_self_of_mem_Ax f hfa hfb hx
  have hq2 : q' ^ 2 = q ^ 2 := by rw [hq', hq]
  have hqsum : (cM M) ^ 2 + q ^ 2 = 1 := by linarith [hq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hq2 with hqq | hqq
  · -- `q' = q`: `G = F` on the normal plane, both are the identity on the axis plane
    left
    have hGE1 : Matrix.mulVec (emat g) B.E1 = Matrix.mulVec (emat f) B.E1 := by
      rw [hmat1', hmat1, hqq]
    have hGE2 : Matrix.mulVec (emat g) B.E2 = Matrix.mulVec (emat f) B.E2 := by
      rw [hmat2', hmat2, hqq]
    have hsame : ∀ v : Fin 3 ⊕ Fin 1 → ℝ, Matrix.mulVec (emat g) v = Matrix.mulVec (emat f) v := by
      intro v
      obtain ⟨α, β, γ, δ, hv⟩ := B.spanV v
      have hGv : Matrix.mulVec (emat g) (α • nvec a + β • nvec b + γ • B.E1 + δ • B.E2)
          = α • nvec a + β • nvec b + γ • Matrix.mulVec (emat g) B.E1
            + δ • Matrix.mulVec (emat g) B.E2 := by
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
        rw [hGidW _ (nvec_a_mem_Ax a b), hGidW _ (nvec_b_mem_Ax a b)]
      have hFv : Matrix.mulVec (emat f) (α • nvec a + β • nvec b + γ • B.E1 + δ • B.E2)
          = α • nvec a + β • nvec b + γ • Matrix.mulVec (emat f) B.E1
            + δ • Matrix.mulVec (emat f) B.E2 := by
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
        rw [hFidW _ (nvec_a_mem_Ax a b), hFidW _ (nvec_b_mem_Ax a b)]
      rw [hv, hGv, hFv, hGE1, hGE2]
    have hguf : ∀ u : Submission.Mostow.E 3, g • u = f • u := by
      intro u
      apply Submission.Mostow.Hyper.hlift_injective
      rw [← emat_hlift g u, ← emat_hlift f u, hsame]
    have hfinv : f⁻¹ * g = 1 := (POBasic.ofProp hA).faithful _ (by
      intro u
      rw [(POBasic.ofProp hA).mul_smul, hguf u, ← (POBasic.ofProp hA).mul_smul, inv_mul_cancel,
        (POBasic.ofProp hA).one_smul])
    calc g = f * (f⁻¹ * g) := by group
      _ = f * 1 := by rw [hfinv]
      _ = f := mul_one f
  · -- `q' = -q`: `emat g` is the inverse of `emat f` on the normal plane
    right
    have hG1 : Matrix.mulVec (emat g) B.E1 = cM M • B.E1 + (-q) • B.E2 := by
      rw [hmat1', hqq]
    have hG2 : Matrix.mulVec (emat g) B.E2 = q • B.E1 + cM M • B.E2 := by
      rw [hmat2', hqq]; simp
    have hFG_E1 : Matrix.mulVec (emat f) (Matrix.mulVec (emat g) B.E1) = B.E1 := by
      rw [hG1]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
      rw [hmat1, hmat2]
      exact smul_rot_comp (cM M) q hqsum B.E1 B.E2
    have hFG_E2 : Matrix.mulVec (emat f) (Matrix.mulVec (emat g) B.E2) = B.E2 := by
      rw [hG2]
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
      rw [hmat1, hmat2]
      exact smul_rot_comp' (cM M) q hqsum B.E1 B.E2
    have hsame : ∀ v : Fin 3 ⊕ Fin 1 → ℝ,
        Matrix.mulVec (emat f) (Matrix.mulVec (emat g) v) = v := by
      intro v
      obtain ⟨α, β, γ, δ, hv⟩ := B.spanV v
      have hGv : Matrix.mulVec (emat g) (α • nvec a + β • nvec b + γ • B.E1 + δ • B.E2)
          = α • nvec a + β • nvec b + γ • Matrix.mulVec (emat g) B.E1
            + δ • Matrix.mulVec (emat g) B.E2 := by
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
        rw [hGidW _ (nvec_a_mem_Ax a b), hGidW _ (nvec_b_mem_Ax a b)]
      have hFv : Matrix.mulVec (emat f)
            (α • nvec a + β • nvec b + γ • Matrix.mulVec (emat g) B.E1
              + δ • Matrix.mulVec (emat g) B.E2)
          = α • nvec a + β • nvec b + γ • B.E1 + δ • B.E2 := by
        simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
        rw [hFidW _ (nvec_a_mem_Ax a b), hFidW _ (nvec_b_mem_Ax a b), hFG_E1, hFG_E2]
      rw [hv, hGv, hFv]
    have hmat_eq : emat f * emat g = 1 := by
      refine Matrix.mulVec_injective (funext fun v => ?_)
      show (emat f * emat g) *ᵥ v = (1 : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℝ) *ᵥ v
      rw [← Matrix.mulVec_mulVec, hsame v, Matrix.one_mulVec]
    have hge : emat g = emat f⁻¹ := by
      have h1 : emat f⁻¹ * emat f = 1 := by rw [← emat_mul hA, inv_mul_cancel, emat_one hA]
      calc emat g = 1 * emat g := (one_mul _).symm
        _ = (emat f⁻¹ * emat f) * emat g := by rw [h1]
        _ = emat f⁻¹ * (emat f * emat g) := by rw [mul_assoc]
        _ = emat f⁻¹ * 1 := by rw [hmat_eq]
        _ = emat f⁻¹ := mul_one _
    exact emat_injective hA hge


end

end Work.Mostow.gapA
