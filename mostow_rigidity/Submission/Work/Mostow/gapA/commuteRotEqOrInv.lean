import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.gapA.geodFacts
import Submission.Work.Mostow.gapA.mem_geodSet_iff_span
import Submission.Work.Mostow.perpNullUnit
import Submission.Work.Mostow.pairStabDefs
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.StabLift

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

/-! ## Basic facts about the Minkowski form of the model -/

/-- The Minkowski pairing of the lift of `u` with the boundary null vector of `ξ`. -/
lemma mform_hlift_theta_neg (ξ u : E n) : mform (hlift u) (theta ξ) = -lev ξ u := by
  rw [mform_hlift_theta', lev]; ring

/-- `mform` of two hyperboloid lifts is minus the cosh of the hyperbolic distance. -/
lemma mform_hlift_hlift_cosh (u v : E n) :
    mform (hlift u) (hlift v) = -Real.cosh (hdist u v) := by
  rw [← mink_eq_mform]
  exact mink_hlift_neg_cosh' u v

/-- The null vector of a boundary point is null for `mform`. -/
lemma mform_nvec_self' {ξ : E n} (hξ : ξ ∈ Sph n) : mform (nvec ξ) (nvec ξ) = 0 :=
  mform_theta_theta_sph ξ hξ

/-- Pairing of two null vectors. -/
lemma mform_nvec_nvec' (ξ η : E n) : mform (nvec ξ) (nvec η) = inner ℝ ξ η - 1 :=
  mform_theta_theta_pair ξ η

/-- The two null vectors of distinct boundary points are linearly independent. -/
lemma nvec_pair_independent (a b : E n) (hab : a ≠ b) :
    ∀ α β : ℝ, α • nvec a + β • nvec b = 0 → α = 0 ∧ β = 0 := by
  intro α β h
  have h0 : α + β = 0 := by
    have h1 := congrFun h (Sum.inr 0)
    simpa [nvec, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h1
  have hsp : ∀ i : Fin n, α * a i + β * b i = 0 := by
    intro i
    have h1 := congrFun h (Sum.inl i)
    simpa [nvec, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h1
  have hβ : β = -α := by linarith
  have hα0 : α = 0 := by
    by_contra hα
    have hab' : a = b := by
      ext i
      have hi := hsp i
      rw [hβ] at hi
      have h2 : α * (a i - b i) = 0 := by linarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hα)
    exact hab hab'
  exact ⟨hα0, by rw [hα0] at hβ; linarith⟩

/-- The null vector of a boundary point is nonzero. -/
lemma nvec_ne_zero (ξ : E n) : nvec ξ ≠ 0 := by
  intro h
  have h1 := congrFun h (Sum.inr 0)
  simp [nvec] at h1

/-! ## The axis plane of a geodesic -/

/-- The plane spanned by the two null vectors of the geodesic with endpoints `a`, `b`. -/
def axisPlane (a b : E n) : Submodule ℝ (Fin n ⊕ Fin 1 → ℝ) :=
  Submodule.span ℝ ({nvec a, nvec b} : Set (Fin n ⊕ Fin 1 → ℝ))

lemma mem_axisPlane {a b : E n} {x : Fin n ⊕ Fin 1 → ℝ} :
    x ∈ axisPlane a b ↔ ∃ α β : ℝ, α • nvec a + β • nvec b = x :=
  Submodule.mem_span_pair

/-- The lift of a point of the geodesic `a`-`b` lies in the axis plane. -/
lemma hlift_mem_axisPlane {a b : E n} (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b)
    {u : E n} (hu : u ∈ geodSet a b) : hlift u ∈ axisPlane a b := by
  obtain ⟨α, β, h⟩ := (mem_geodSet_iff_span a b ha hb hab u).mp hu
  exact mem_axisPlane.mpr ⟨α, β, h.symm⟩

/-- The parametrised points of the geodesic lie in the axis plane. -/
lemma gcAxis_mem_axisPlane (a b : E n) (s : ℝ) : gcAxis a b s ∈ axisPlane a b := by
  rw [axisPlane, gcAxis]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
    (Submodule.smul_mem _ _ (Submodule.subset_span (by simp))))

/-- `γ_1 - e^{-1} γ_0` is a multiple of the first null vector. -/
lemma gcAxis_one_sub_inv_smul_zero (a b : E n) :
    gcAxis a b 1 - Real.exp (-1) • gcAxis a b 0
      = (gcK a b * (Real.exp 1 - Real.exp (-1))) • nvec a := by
  simp only [gcAxis, Real.exp_zero, neg_zero, one_smul]
  module

/-- `e · γ_0 - γ_1` is a multiple of the second null vector. -/
lemma gcAxis_exp_smul_zero_sub_one (a b : E n) :
    Real.exp 1 • gcAxis a b 0 - gcAxis a b 1
      = (gcK a b * (Real.exp 1 - Real.exp (-1))) • nvec b := by
  simp only [gcAxis, Real.exp_zero, neg_zero, one_smul]
  module

/-- The two null vectors lie in the span of (any two distinct) points of the geodesic. -/
lemma nvec_mem_span_gcAxis (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) :
    nvec a ∈ Submodule.span ℝ ({gcAxis a b 0, gcAxis a b 1} : Set (Fin n ⊕ Fin 1 → ℝ)) ∧
      nvec b ∈ Submodule.span ℝ ({gcAxis a b 0, gcAxis a b 1} : Set (Fin n ⊕ Fin 1 → ℝ)) := by
  have hK : gcK a b ≠ 0 := ne_of_gt (gcK_pos a b ha hb hab)
  have he' : Real.exp (-1) < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
  have hc : gcK a b * (Real.exp 1 - Real.exp (-1)) ≠ 0 :=
    mul_ne_zero hK (by linarith)
  constructor
  · rw [Submodule.mem_span_pair]
    refine ⟨-((gcK a b * (Real.exp 1 - Real.exp (-1)))⁻¹ * Real.exp (-1)),
      (gcK a b * (Real.exp 1 - Real.exp (-1)))⁻¹, ?_⟩
    have h1 : nvec a = (gcK a b * (Real.exp 1 - Real.exp (-1)))⁻¹ •
        (gcAxis a b 1 - Real.exp (-1) • gcAxis a b 0) := by
      rw [gcAxis_one_sub_inv_smul_zero a b, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [h1]
    module
  · rw [Submodule.mem_span_pair]
    refine ⟨(gcK a b * (Real.exp 1 - Real.exp (-1)))⁻¹ * Real.exp 1,
      -((gcK a b * (Real.exp 1 - Real.exp (-1)))⁻¹), ?_⟩
    have h1 : nvec b = (gcK a b * (Real.exp 1 - Real.exp (-1)))⁻¹ •
        (Real.exp 1 • gcAxis a b 0 - gcAxis a b 1) := by
      rw [gcAxis_exp_smul_zero_sub_one a b, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [h1]
    module

/-- The axis plane is spanned by the points of the geodesic. -/
lemma axisPlane_eq_span_gcAxis (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n) (hab : a ≠ b) :
    axisPlane a b = Submodule.span ℝ ({gcAxis a b 0, gcAxis a b 1} : Set (Fin n ⊕ Fin 1 → ℝ)) := by
  refine le_antisymm ?_ ?_
  · rw [axisPlane]
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with hx | hx
    · rw [hx]
      exact (nvec_mem_span_gcAxis a b ha hb hab).1
    · rw [hx]
      exact (nvec_mem_span_gcAxis a b ha hb hab).2
  · apply Submodule.span_le.mpr
    intro x hx
    rcases hx with hx | hx
    · rw [hx]
      exact gcAxis_mem_axisPlane a b 0
    · rw [hx]
      exact gcAxis_mem_axisPlane a b 1

/-! ## The lift maps / fixes axis planes -/

/-- If `g` maps the geodesic `a`-`b` into itself then its lift preserves the axis plane. -/
lemma emat_maps_axisPlane (g : PO n 1) (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n)
    (hab : a ≠ b) (hmap : ∀ u : E n, u ∈ geodSet a b → g • u ∈ geodSet a b) :
    ∀ x ∈ axisPlane a b, Matrix.mulVec (emat g) x ∈ axisPlane a b := by
  have hW0 : Matrix.mulVec (emat g) (gcAxis a b 0) ∈ axisPlane a b := by
    rw [← hlift_gcAxisPt a b ha hb hab 0, emat_hlift]
    exact hlift_mem_axisPlane ha hb hab (hmap _ (gcAxisPt_mem_geodSet a b ha hb hab 0))
  have hW1 : Matrix.mulVec (emat g) (gcAxis a b 1) ∈ axisPlane a b := by
    rw [← hlift_gcAxisPt a b ha hb hab 1, emat_hlift]
    exact hlift_mem_axisPlane ha hb hab (hmap _ (gcAxisPt_mem_geodSet a b ha hb hab 1))
  let W : Submodule ℝ (Fin n ⊕ Fin 1 → ℝ) :=
    { carrier := {x | Matrix.mulVec (emat g) x ∈ axisPlane a b}
      zero_mem' := by
        show Matrix.mulVec (emat g) 0 ∈ axisPlane a b
        rw [Matrix.mulVec_zero]
        exact (axisPlane a b).zero_mem
      add_mem' := by
        intro x y hx hy
        show Matrix.mulVec (emat g) (x + y) ∈ axisPlane a b
        rw [Matrix.mulVec_add]
        exact Submodule.add_mem _ hx hy
      smul_mem' := by
        intro c x hx
        show Matrix.mulVec (emat g) (c • x) ∈ axisPlane a b
        rw [Matrix.mulVec_smul]
        exact Submodule.smul_mem _ _ hx }
  have hle : axisPlane a b ≤ W := by
    rw [axisPlane_eq_span_gcAxis a b ha hb hab]
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with hx | hx
    · rw [hx]
      exact hW0
    · rw [hx]
      exact hW1
  intro x hx
  exact hle hx

/-- If `g` fixes the geodesic `a`-`b` pointwise then its lift fixes the axis plane pointwise. -/
lemma emat_fixes_axisPlane (g : PO n 1) (a b : E n) (ha : a ∈ Sph n) (hb : b ∈ Sph n)
    (hab : a ≠ b) (hfix : ∀ u : E n, u ∈ geodSet a b → g • u = u) :
    ∀ x ∈ axisPlane a b, Matrix.mulVec (emat g) x = x := by
  have hW0 : Matrix.mulVec (emat g) (gcAxis a b 0) = gcAxis a b 0 := by
    rw [← hlift_gcAxisPt a b ha hb hab 0, emat_hlift,
      hfix _ (gcAxisPt_mem_geodSet a b ha hb hab 0)]
  have hW1 : Matrix.mulVec (emat g) (gcAxis a b 1) = gcAxis a b 1 := by
    rw [← hlift_gcAxisPt a b ha hb hab 1, emat_hlift,
      hfix _ (gcAxisPt_mem_geodSet a b ha hb hab 1)]
  let W : Submodule ℝ (Fin n ⊕ Fin 1 → ℝ) :=
    { carrier := {x | Matrix.mulVec (emat g) x = x}
      zero_mem' := by
        show Matrix.mulVec (emat g) 0 = 0
        rw [Matrix.mulVec_zero]
      add_mem' := by
        intro x y hx hy
        show Matrix.mulVec (emat g) (x + y) = x + y
        rw [Matrix.mulVec_add, hx, hy]
      smul_mem' := by
        intro c x hx
        show Matrix.mulVec (emat g) (c • x) = c • x
        rw [Matrix.mulVec_smul, hx] }
  have hle : axisPlane a b ≤ W := by
    rw [axisPlane_eq_span_gcAxis a b ha hb hab]
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with hx | hx
    · rw [hx]
      exact hW0
    · rw [hx]
      exact hW1
  intro x hx
  exact hle hx

/-! ## The orthogonal complement of an axis plane is positive definite -/

/-- A nonzero vector orthogonal to the two null vectors of a geodesic is space-like. -/
lemma axisQ_posdef (c d : E 3) (hc : c ∈ Sph 3) (hd : d ∈ Sph 3) (hcd : c ≠ d)
    (z : Fin 3 ⊕ Fin 1 → ℝ) (hz : z ≠ 0)
    (hzc : mform z (nvec c) = 0) (hzd : mform z (nvec d) = 0) :
    0 < mform z z := by
  have hzc' : mform z (theta c) = 0 := hzc
  have hzd' : mform z (theta d) = 0 := hzd
  have hcd0 : mform (theta c) (theta d) ≠ 0 := by
    rw [mform_theta_theta_pair]
    intro h
    exact hcd ((inner_eq_one_iff_of_norm_eq_one ((mem_Sph_iff c).mp hc)
      ((mem_Sph_iff d).mp hd)).mp (sub_eq_zero.mp h))
  rw [mform_self_eq_hspat_horoProj hc hzc']
  have hne : hspat (horoProj c z) ≠ 0 := by
    intro h0
    have hs0 : horoProj c z = 0 := by
      rw [eq_elim_hspat_htime (horoProj c z), h0,
        htime_eq_zero_of_horoProj c hc (horoProj_idem c hc z)]
      ext k
      rcases k with i | j
      · simp
      · simp
    have hzq : z = (mform z (horoEta c) / 2) • theta c := by
      conv_lhs => rw [eq_horoProj_add hzc']
      rw [hs0, zero_add]
    have hq : mform z (horoEta c) / 2 = 0 := by
      have h := hzd'
      rw [hzq, mform_smul_left] at h
      exact (mul_eq_zero.mp h).resolve_right hcd0
    exact hz (by conv_lhs => rw [hzq]; rw [hq, zero_smul])
  exact pow_pos (norm_pos_iff.mpr hne) 2

/-! ## A point of `ℍ³` with prescribed normal direction to the axis -/

/-- For `v` a unit normal vector of the axis `c`-`d` (with nonnegative time coordinate) there is a
point `u` whose lift is `cosh S • γ_0 + sinh S • v` and which is at distance `S` from the axis. -/
lemma exists_pt_cosh_sinh (c d : E 3) (hc : c ∈ Sph 3) (hd : d ∈ Sph 3) (hcd : c ≠ d)
    (v : Fin 3 ⊕ Fin 1 → ℝ) (hv1 : mform v v = 1)
    (hvc : mform v (nvec c) = 0) (hvd : mform v (nvec d) = 0)
    (htv : 0 ≤ v (Sum.inr 0)) :
    ∃ (S : ℝ) (u : E 3), 0 < S ∧
      hlift u = Real.cosh S • hlift (gcAxisPt c d 0) + Real.sinh S • v ∧
      distGeod c d u = S := by
  have hvcθ : mform v (theta c) = 0 := hvc
  have hvdθ : mform v (theta d) = 0 := hvd
  have hp : hlift (gcAxisPt c d 0) = gcAxis c d 0 := hlift_gcAxisPt c d hc hd hcd 0
  have hp_span : hlift (gcAxisPt c d 0) = gcK c d • (nvec c + nvec d) := by
    rw [hp, gcAxis]; simp
  have hp_self : mform (hlift (gcAxisPt c d 0)) (hlift (gcAxisPt c d 0)) = -1 := by
    rw [← mink_eq_mform, hp, mink_gcAxis c d hc hd hcd 0 0, sub_self, Real.cosh_zero]
  have hpv : mform (hlift (gcAxisPt c d 0)) v = 0 := by
    rw [hp_span, mform_smul_left, mform_add_left, mform_comm (nvec c) v, mform_comm (nvec d) v,
      hvc, hvd, add_zero, mul_zero]
  have hpv' : mform v (hlift (gcAxisPt c d 0)) = 0 := by rw [mform_comm]; exact hpv
  have hptime : 1 ≤ hlift (gcAxisPt c d 0) (Sum.inr 0) := by
    rw [hlift_inr]
    exact one_le_tpart _
  set Y : Fin 3 ⊕ Fin 1 → ℝ :=
    Real.cosh 1 • hlift (gcAxisPt c d 0) + Real.sinh 1 • v with hY
  have hYself : mform Y Y = -1 := by
    rw [hY]
    simp only [mform_add_left, mform_add_right, mform_smul_left, mform_smul_right, hp_self,
      hpv, hpv', hv1, mul_zero, mul_one, mul_neg, add_zero, zero_add]
    nlinarith [Real.cosh_sq_sub_sinh_sq 1]
  have hYtime : 0 < Y (Sum.inr 0) := by
    rw [hY]
    have h3 : (Real.cosh 1 • hlift (gcAxisPt c d 0) + Real.sinh 1 • v) (Sum.inr 0)
        = Real.cosh 1 * hlift (gcAxisPt c d 0) (Sum.inr 0) + Real.sinh 1 * v (Sum.inr 0) := by
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [h3]
    have h4 : Real.cosh 1 * 1 ≤ Real.cosh 1 * hlift (gcAxisPt c d 0) (Sum.inr 0) :=
      mul_le_mul_of_nonneg_left hptime (le_of_lt (Real.cosh_pos 1))
    have h5 : 0 ≤ Real.sinh 1 * v (Sum.inr 0) :=
      mul_nonneg (le_of_lt (Real.sinh_pos_iff.mpr (by norm_num))) htv
    linarith [Real.cosh_pos 1]
  refine ⟨1, WithLp.toLp 2 (fun i => Y (Sum.inl i)), by norm_num, ?_, ?_⟩
  · rw [← eq_hlift_of_upper Y hYself hYtime, hY]
  · rw [distGeod_eq c d hc hd _]
    have hYh : hlift (WithLp.toLp 2 fun i => Y (Sum.inl i)) = Y :=
      (eq_hlift_of_upper Y hYself hYtime).symm
    have hL : gcL c d ≠ 0 := ne_of_gt (gcL_pos c d hc hd hcd)
    have hlevc : lev c (WithLp.toLp 2 fun i => Y (Sum.inl i))
        = Real.cosh 1 * (2 * gcK c d * gcL c d) := by
      have h1 : lev c (WithLp.toLp 2 fun i => Y (Sum.inl i))
          = -mform (hlift (WithLp.toLp 2 fun i => Y (Sum.inl i))) (theta c) := by
        rw [mform_hlift_theta_neg c _]; ring
      have h2 : mform (hlift (gcAxisPt c d 0)) (theta c) = -lev c (gcAxisPt c d 0) :=
        mform_hlift_theta_neg c _
      rw [h1, hYh, hY]
      simp only [mform_add_left, mform_smul_left, mform_smul_right, h2, hvcθ, mul_zero, add_zero]
      rw [lev_a_gcAxisPt c d hc hd hcd 0]
      simp only [neg_zero, Real.exp_zero, mul_one]
      ring
    have hlevd : lev d (WithLp.toLp 2 fun i => Y (Sum.inl i))
        = Real.cosh 1 * (2 * gcK c d * gcL c d) := by
      have h1 : lev d (WithLp.toLp 2 fun i => Y (Sum.inl i))
          = -mform (hlift (WithLp.toLp 2 fun i => Y (Sum.inl i))) (theta d) := by
        rw [mform_hlift_theta_neg d _]; ring
      have h2 : mform (hlift (gcAxisPt c d 0)) (theta d) = -lev d (gcAxisPt c d 0) :=
        mform_hlift_theta_neg d _
      rw [h1, hYh, hY]
      simp only [mform_add_left, mform_smul_left, mform_smul_right, h2, hvdθ, mul_zero, add_zero]
      rw [lev_b_gcAxisPt c d hc hd hcd 0]
      simp only [neg_zero, Real.exp_zero, mul_one]
      ring
    have hprod : lev c (WithLp.toLp 2 fun i => Y (Sum.inl i))
        * lev d (WithLp.toLp 2 fun i => Y (Sum.inl i)) / gcL c d = Real.cosh 1 ^ 2 := by
      rw [hlevc, hlevd, div_eq_iff hL]
      have h4 := gcK_sq_four c d hc hd hcd
      nlinarith [h4]
    rw [hprod, Real.sqrt_sq (le_of_lt (Real.cosh_pos 1)), Real.arcosh_cosh (by norm_num)]

/-! ## A matrix fixing the axis plane acts by `cos θ` on its complement -/

/-- If `g` fixes the geodesic `c`-`d` pointwise and satisfies the displacement formula with angle
`θ`, then the quadratic form associated with its lift on the normal plane is `cos θ` times the
Minkowski form. -/
lemma emat_cos_form_of_nonneg (g : PO 3 1) (c d : E 3) (hc : c ∈ Sph 3) (hd : d ∈ Sph 3)
    (hcd : c ≠ d) (θ : ℝ) (hg : IsRotationAbout g c d θ)
    (hfix : ∀ u : E 3, u ∈ geodSet c d → g • u = u)
    (v : Fin 3 ⊕ Fin 1 → ℝ) (hv0 : 0 ≤ v (Sum.inr 0))
    (hvc : mform v (nvec c) = 0) (hvd : mform v (nvec d) = 0) :
    mform v (Matrix.mulVec (emat g) v) = Real.cos θ * mform v v := by
  have hvcθ : mform v (theta c) = 0 := hvc
  have hvdθ : mform v (theta d) = 0 := hvd
  by_cases hvz : v = 0
  · subst hvz; simp
  have hpos : 0 < mform v v := axisQ_posdef c d hc hd hcd v hvz hvc hvd
  set sm : ℝ := Real.sqrt (mform v v) with hsm
  have hsmpos : 0 < sm := Real.sqrt_pos.mpr hpos
  have hsm2 : sm * sm = mform v v := by rw [hsm, ← sq, Real.sq_sqrt (le_of_lt hpos)]
  set w : Fin 3 ⊕ Fin 1 → ℝ := sm⁻¹ • v with hw
  have hw1 : mform w w = 1 := by
    rw [hw, mform_smul_left, mform_smul_right, ← hsm2]
    field_simp
  have hwc : mform w (nvec c) = 0 := by rw [hw, mform_smul_left, hvc, mul_zero]
  have hwd : mform w (nvec d) = 0 := by rw [hw, mform_smul_left, hvd, mul_zero]
  have hwsign : 0 ≤ w (Sum.inr 0) := by
    rw [hw]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_nonneg (le_of_lt (inv_pos.mpr hsmpos)) hv0
  obtain ⟨S, u, hSpos, hu, hdistS⟩ := exists_pt_cosh_sinh c d hc hd hcd w hw1 hwc hwd hwsign
  have hp : hlift (gcAxisPt c d 0) = gcAxis c d 0 := hlift_gcAxisPt c d hc hd hcd 0
  have hp_span : hlift (gcAxisPt c d 0) = gcK c d • (nvec c + nvec d) := by
    rw [hp, gcAxis]; simp
  have hp_self : mform (hlift (gcAxisPt c d 0)) (hlift (gcAxisPt c d 0)) = -1 := by
    rw [← mink_eq_mform, hp, mink_gcAxis c d hc hd hcd 0 0, sub_self, Real.cosh_zero]
  have hpw : mform (hlift (gcAxisPt c d 0)) w = 0 := by
    rw [hp_span, mform_smul_left, mform_add_left, mform_comm (nvec c) w, mform_comm (nvec d) w,
      hwc, hwd, add_zero, mul_zero]
  have hwp : mform w (hlift (gcAxisPt c d 0)) = 0 := by rw [mform_comm]; exact hpw
  have hMp : Matrix.mulVec (emat g) (hlift (gcAxisPt c d 0)) = hlift (gcAxisPt c d 0) := by
    rw [emat_hlift g (gcAxisPt c d 0), hfix _ (gcAxisPt_mem_geodSet c d hc hd hcd 0)]
  have hpMw : mform (hlift (gcAxisPt c d 0)) (Matrix.mulVec (emat g) w) = 0 := by
    rw [← hMp, mform_emat g, hpw]
  have hkey : Matrix.mulVec (emat g)
        (Real.cosh S • hlift (gcAxisPt c d 0) + Real.sinh S • w)
      = Real.cosh S • hlift (gcAxisPt c d 0) + Real.sinh S • Matrix.mulVec (emat g) w := by
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, hMp]
  have hA : mform (hlift u) (Matrix.mulVec (emat g) (hlift u))
      = -Real.cosh S ^ 2 + Real.sinh S ^ 2 * mform w (Matrix.mulVec (emat g) w) := by
    rw [hu, hkey]
    simp only [mform_add_left, mform_add_right, mform_smul_left, mform_smul_right, hp_self,
      hpw, hwp, hpMw, mul_zero, mul_one, mul_neg, add_zero, zero_add]
    ring
  have hB : mform (hlift u) (Matrix.mulVec (emat g) (hlift u))
      = -Real.cosh (2 * Real.arsinh (Real.sinh S * Real.sin (θ / 2))) := by
    rw [emat_hlift g u, mform_hlift_hlift_cosh, hg.2 u, hdistS]
  have hC : -Real.cosh S ^ 2 + Real.sinh S ^ 2 * mform w (Matrix.mulVec (emat g) w)
      = -Real.cosh (2 * Real.arsinh (Real.sinh S * Real.sin (θ / 2))) := by
    rw [← hA, hB]
  have hD : Real.cosh (2 * Real.arsinh (Real.sinh S * Real.sin (θ / 2)))
      = 1 + 2 * (Real.sinh S * Real.sin (θ / 2)) ^ 2 := by
    have h2 : (2 : ℝ) * Real.arsinh (Real.sinh S * Real.sin (θ / 2))
        = Real.arsinh (Real.sinh S * Real.sin (θ / 2))
          + Real.arsinh (Real.sinh S * Real.sin (θ / 2)) := by ring
    rw [h2, Real.cosh_add, Real.sinh_arsinh]
    have hc2 : Real.cosh (Real.arsinh (Real.sinh S * Real.sin (θ / 2))) ^ 2
        = 1 + (Real.sinh S * Real.sin (θ / 2)) ^ 2 := by
      rw [Real.cosh_sq, Real.sinh_arsinh]; ring
    rw [show Real.cosh (Real.arsinh (Real.sinh S * Real.sin (θ / 2)))
          * Real.cosh (Real.arsinh (Real.sinh S * Real.sin (θ / 2)))
        = Real.cosh (Real.arsinh (Real.sinh S * Real.sin (θ / 2))) ^ 2 from by ring, hc2]
    ring
  have hSsinh : Real.sinh S ≠ 0 := ne_of_gt (Real.sinh_pos_iff.mpr hSpos)
  have htrig : (1 : ℝ) - 2 * Real.sin (θ / 2) ^ 2 = Real.cos θ := by
    have h2 : Real.cos θ = Real.cos (2 * (θ / 2)) := by congr 1; ring
    rw [h2, Real.cos_two_mul, Real.cos_sq', Real.sin_sq]
    ring
  have hmw_val : mform w (Matrix.mulVec (emat g) w) = Real.cos θ := by
    have h1 : Real.sinh S ^ 2 * mform w (Matrix.mulVec (emat g) w)
        = Real.sinh S ^ 2 * Real.cos θ := by
      have hcS : Real.cosh S ^ 2 = 1 + Real.sinh S ^ 2 := Real.cosh_sq' S
      rw [hD] at hC
      nlinarith [hC, hcS, htrig]
    exact mul_left_cancel₀ (pow_ne_zero 2 hSsinh) h1
  have hscale : mform w (Matrix.mulVec (emat g) w)
      = sm⁻¹ * sm⁻¹ * mform v (Matrix.mulVec (emat g) v) := by
    rw [hw, Matrix.mulVec_smul, mform_smul_left, mform_smul_right]
    ring
  rw [hscale] at hmw_val
  have hsmne : sm ≠ 0 := ne_of_gt hsmpos
  have hfin : mform v (Matrix.mulVec (emat g) v) = sm * sm * Real.cos θ := by
    have h2 : sm * sm * (sm⁻¹ * sm⁻¹ * mform v (Matrix.mulVec (emat g) v))
        = mform v (Matrix.mulVec (emat g) v) := by field_simp
    rw [hmw_val] at h2
    exact h2.symm
  rw [hfin, ← hsm2, mul_comm]

/-- The same statement without the sign restriction on the time coordinate. -/
lemma emat_cos_form (g : PO 3 1) (c d : E 3) (hc : c ∈ Sph 3) (hd : d ∈ Sph 3)
    (hcd : c ≠ d) (θ : ℝ) (hg : IsRotationAbout g c d θ)
    (hfix : ∀ u : E 3, u ∈ geodSet c d → g • u = u)
    (v : Fin 3 ⊕ Fin 1 → ℝ) (hvc : mform v (nvec c) = 0) (hvd : mform v (nvec d) = 0) :
    mform v (Matrix.mulVec (emat g) v) = Real.cos θ * mform v v := by
  by_cases hv0 : 0 ≤ v (Sum.inr 0)
  · exact emat_cos_form_of_nonneg g c d hc hd hcd θ hg hfix v hv0 hvc hvd
  · have hv0' : 0 ≤ (-v) (Sum.inr 0) := by
      simpa using le_of_lt (lt_of_not_ge hv0)
    have hnegc : mform (-v) (nvec c) = 0 := by rw [mform_neg_left, hvc, neg_zero]
    have hnegd : mform (-v) (nvec d) = 0 := by rw [mform_neg_left, hvd, neg_zero]
    have h := emat_cos_form_of_nonneg g c d hc hd hcd θ hg hfix (-v) hv0' hnegc hnegd
    simpa [Matrix.mulVec_neg, mform_neg_left, mform_neg_right] using h


/-! ## The orthogonal complement of an axis plane, as a submodule -/

/-- `mform` is left-linear in the zero vector. -/
lemma mform_zero_left (y : Fin n ⊕ Fin 1 → ℝ) : mform (0 : Fin n ⊕ Fin 1 → ℝ) y = 0 := by
  simp only [mform_apply]
  simp

/-- The orthogonal complement of the axis plane of a geodesic. -/
def axisPerp (p q : E n) : Submodule ℝ (Fin n ⊕ Fin 1 → ℝ) where
  carrier := {x | mform x (nvec p) = 0 ∧ mform x (nvec q) = 0}
  zero_mem' := ⟨by rw [mform_zero_left], by rw [mform_zero_left]⟩
  add_mem' := by
    intro x y hx hy
    exact ⟨by rw [mform_add_left, hx.1, hy.1, add_zero],
      by rw [mform_add_left, hx.2, hy.2, add_zero]⟩
  smul_mem' := by
    intro c x hx
    exact ⟨by rw [mform_smul_left, hx.1, mul_zero],
      by rw [mform_smul_left, hx.2, mul_zero]⟩

lemma mem_axisPerp {p q : E n} {x : Fin n ⊕ Fin 1 → ℝ} :
    x ∈ axisPerp p q ↔ mform x (nvec p) = 0 ∧ mform x (nvec q) = 0 := Iff.rfl

/-- The two null vectors of distinct unit points are not orthogonal. -/
lemma mform_nvec_nvec_ne_zero (p q : E n) (hp : p ∈ Sph n) (hq : q ∈ Sph n) (hpq : p ≠ q) :
    mform (nvec p) (nvec q) ≠ 0 := by
  rw [mform_nvec_nvec']
  intro h
  exact hpq ((inner_eq_one_iff_of_norm_eq_one ((mem_Sph_iff p).mp hp) ((mem_Sph_iff q).mp hq)).mp
    (sub_eq_zero.mp h))

/-- Decomposition of a vector into an axis-plane part and an orthogonal part. -/
lemma exists_axis_decomp (p q : E n) (hp : p ∈ Sph n) (hq : q ∈ Sph n) (hpq : p ≠ q)
    (x : Fin n ⊕ Fin 1 → ℝ) :
    ∃ a v : Fin n ⊕ Fin 1 → ℝ, a ∈ axisPlane p q ∧ mform v (nvec p) = 0 ∧
      mform v (nvec q) = 0 ∧ x = a + v := by
  have hs : mform (nvec p) (nvec q) ≠ 0 := mform_nvec_nvec_ne_zero p q hp hq hpq
  have hsd : mform (nvec q) (nvec p) = mform (nvec p) (nvec q) := mform_comm _ _
  refine ⟨(mform x (nvec q) / mform (nvec p) (nvec q)) • nvec p
      + (mform x (nvec p) / mform (nvec p) (nvec q)) • nvec q,
    x - ((mform x (nvec q) / mform (nvec p) (nvec q)) • nvec p
      + (mform x (nvec p) / mform (nvec p) (nvec q)) • nvec q), ?_, ?_, ?_,
    by rw [add_comm]; exact (sub_add_cancel x _).symm⟩
  · exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · rw [mform_sub_left, mform_add_left, mform_smul_left, mform_smul_left, mform_nvec_self' hp,
      mform_comm (nvec q) (nvec p)]
    field_simp
    ring
  · rw [mform_sub_left, mform_add_left, mform_smul_left, mform_smul_left, mform_nvec_self' hq]
    field_simp
    ring

/-- The axis plane and its orthogonal complement meet only in `0`. -/
lemma axisPlane_inf_axisPerp_eq_bot (p q : E n) (hp : p ∈ Sph n) (hq : q ∈ Sph n)
    (hpq : p ≠ q) : axisPlane p q ⊓ axisPerp p q = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  obtain ⟨hyP, hyQ⟩ := hy
  obtain ⟨α, β, hαβ⟩ := mem_axisPlane.mp hyP
  have h1 : mform (α • nvec p + β • nvec q) (nvec p) = 0 := by rw [hαβ]; exact hyQ.1
  have h2 : mform (α • nvec p + β • nvec q) (nvec q) = 0 := by rw [hαβ]; exact hyQ.2
  have hsqp : inner ℝ q p - 1 ≠ 0 := by
    intro hh
    exact hpq.symm ((inner_eq_one_iff_of_norm_eq_one ((mem_Sph_iff q).mp hq)
      ((mem_Sph_iff p).mp hp)).mp (sub_eq_zero.mp hh))
  have hspq : inner ℝ p q - 1 ≠ 0 := by
    intro hh
    exact hpq ((inner_eq_one_iff_of_norm_eq_one ((mem_Sph_iff p).mp hp)
      ((mem_Sph_iff q).mp hq)).mp (sub_eq_zero.mp hh))
  have hβ : β = 0 := by
    rw [mform_add_left, mform_smul_left, mform_smul_left, mform_nvec_self' hp,
      mform_nvec_nvec'] at h1
    have : β * (inner ℝ q p - 1) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hsqp
  have hα : α = 0 := by
    rw [mform_add_left, mform_smul_left, mform_smul_left, mform_nvec_self' hq,
      mform_nvec_nvec'] at h2
    have : α * (inner ℝ p q - 1) = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_right hspq
  rw [← hαβ, hα, hβ]
  simp

/-- If a sum of an axis-plane vector and an orthogonal vector vanishes, both do. -/
lemma eq_zero_of_add_mem_axisPerp {p q : E n} (hp : p ∈ Sph n) (hq : q ∈ Sph n)
    (hpq : p ≠ q) {a v : Fin n ⊕ Fin 1 → ℝ} (ha : a ∈ axisPlane p q)
    (hv : v ∈ axisPerp p q) (h : a + v = 0) : a = 0 ∧ v = 0 := by
  have ha' : a ∈ axisPerp p q := by
    rw [(add_eq_zero_iff_eq_neg.mp h)]
    exact Submodule.neg_mem _ hv
  have hmem : a ∈ axisPlane p q ⊓ axisPerp p q := ⟨ha, ha'⟩
  rw [axisPlane_inf_axisPerp_eq_bot p q hp hq hpq] at hmem
  have ha0 : a = 0 := hmem
  exact ⟨ha0, by rw [ha0, zero_add] at h; exact h⟩

/-- The lift of a matrix that fixes an axis plane pointwise preserves its orthogonal complement. -/
lemma mulVec_mem_axisPerp_of_fixes {M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ}
    (hM : IsJOrth M) (p q : E n) (hfix : ∀ x ∈ axisPlane p q, Matrix.mulVec M x = x)
    {x : Fin n ⊕ Fin 1 → ℝ} (hx : x ∈ axisPerp p q) :
    Matrix.mulVec M x ∈ axisPerp p q := by
  have hθp : Matrix.mulVec M (nvec p) = nvec p :=
    hfix _ (Submodule.subset_span (by simp))
  have hθq : Matrix.mulVec M (nvec q) = nvec q :=
    hfix _ (Submodule.subset_span (by simp))
  constructor
  · rw [← hθp, mform_mulVec_mulVec hM]
    exact hx.1
  · rw [← hθq, mform_mulVec_mulVec hM]
    exact hx.2

/-- A null vector of the axis plane is a multiple of one of the two generators. -/
lemma eq_smul_of_mem_axisPlane_of_null {p q : E n} (hp : p ∈ Sph n) (hq : q ∈ Sph n)
    (hpq : p ≠ q) {y : Fin n ⊕ Fin 1 → ℝ} (hy : y ∈ axisPlane p q) (hnull : mform y y = 0) :
    (∃ c : ℝ, y = c • nvec p) ∨ (∃ c : ℝ, y = c • nvec q) := by
  have hs : mform (nvec p) (nvec q) ≠ 0 := mform_nvec_nvec_ne_zero p q hp hq hpq
  obtain ⟨α, β, hαβ⟩ := mem_axisPlane.mp hy
  have h0 : 2 * α * β * mform (nvec p) (nvec q) = 0 := by
    rw [← hαβ] at hnull
    simp only [mform_add_left, mform_add_right, mform_smul_left, mform_smul_right,
      mform_nvec_self' hp, mform_nvec_self' hq] at hnull
    rw [mform_comm (nvec q) (nvec p)] at hnull
    linarith
  have h2s : (2 : ℝ) * mform (nvec p) (nvec q) ≠ 0 := by
    intro h
    exact hs (by linarith)
  have hαβ0 : α * β = 0 := by
    have h1 : (α * β) * (2 * mform (nvec p) (nvec q)) = 0 := by linarith
    exact (mul_eq_zero.mp h1).resolve_right h2s
  rcases mul_eq_zero.mp hαβ0 with hα | hβ
  · refine Or.inr ⟨β, ?_⟩
    rw [← hαβ, hα]; simp
  · refine Or.inl ⟨α, ?_⟩
    rw [← hαβ, hβ]; simp

/-- Two vectors of the axis plane that are not proportional span it (with the other one). -/
lemma nvec_ne_smul_nvec (p q : E n) (hp : p ∈ Sph n) (hq : q ∈ Sph n) (hpq : p ≠ q)
    (c : ℝ) : nvec q ≠ c • nvec p := by
  intro h
  have hc : c = 1 := by
    have h' := congrFun h (Sum.inr 0)
    simpa [nvec, Pi.smul_apply, smul_eq_mul] using h'.symm
  have h2 : q = p := by
    ext i
    have h' := congrFun h (Sum.inl i)
    simp only [nvec, Pi.smul_apply, smul_eq_mul] at h'
    rw [hc, one_mul] at h'
    exact h'
  exact hpq h2.symm

/-- `Matrix.mulVec M` is injective for a `J`-orthogonal `M`. -/
lemma mulVec_injective_of_isJOrth {M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ}
    (hM : IsJOrth M) : Function.Injective (Matrix.mulVec M) := by
  have hpm : Function.Injective
      (Matrix.mulVec (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ))) := by
    intro a b hab
    ext k
    rcases k with i | j
    · have h' := congrFun hab (Sum.inl i)
      simpa [pmOneMat_mulVec_inl] using h'
    · obtain rfl : j = 0 := Subsingleton.elim _ _
      have h' := congrFun hab (Sum.inr 0)
      simp only [pmOneMat_mulVec_inr] at h'
      exact neg_injective h'
  intro x y hxy
  have hz : Matrix.mulVec M (x - y) = 0 := by
    rw [Matrix.mulVec_sub, hxy, sub_self]
  have h2 : Matrix.mulVec (M.transpose * (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) * M)
        (x - y)
      = Matrix.mulVec (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) (x - y) := by rw [hM]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hz, Matrix.mulVec_zero,
    Matrix.mulVec_zero] at h2
  have h3 : Matrix.mulVec (pmOneMat (p := Fin n) (q := Fin 1) (α := ℝ)) (x - y) = 0 := h2.symm
  exact sub_eq_zero.mp (hpm (by rw [h3, Matrix.mulVec_zero]))

lemma IsJOrth.mul {M N : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ} (hM : IsJOrth M)
    (hN : IsJOrth N) : IsJOrth (M * N) := by
  rw [IsJOrth] at *
  calc (M * N).transpose * pmOneMat * (M * N)
        = N.transpose * (M.transpose * pmOneMat * M) * N := by
        rw [Matrix.transpose_mul]; noncomm_ring
    _ = N.transpose * pmOneMat * N := by rw [hM]
    _ = pmOneMat := hN

/-- A null vector fixed by a matrix that fixes the axis plane pointwise lies in the axis plane. -/
lemma fixed_null_mem_axisPlane {M : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℝ} (hM : IsJOrth M)
    (p q : E 3) (hp : p ∈ Sph 3) (hq : q ∈ Sph 3) (hpq : p ≠ q) {cc : ℝ}
    (hfix : ∀ x ∈ axisPlane p q, Matrix.mulVec M x = x)
    (hQ : ∀ v, mform v (nvec p) = 0 → mform v (nvec q) = 0 →
      mform v (Matrix.mulVec M v) = cc * mform v v)
    (hc1 : cc ≠ 1)
    {z : Fin 3 ⊕ Fin 1 → ℝ} (hz : z ≠ 0) (hzfix : Matrix.mulVec M z = z) :
    z ∈ axisPlane p q := by
  obtain ⟨a, v, ha, hvp, hvq, hsum⟩ := exists_axis_decomp p q hp hq hpq z
  have hv : v ∈ axisPerp p q := ⟨hvp, hvq⟩
  have hMv : Matrix.mulVec M v ∈ axisPerp p q := mulVec_mem_axisPerp_of_fixes hM p q hfix hv
  have heq : a + Matrix.mulVec M v = a + v := by
    have h1 : Matrix.mulVec M z = a + Matrix.mulVec M v := by
      rw [hsum, Matrix.mulVec_add, hfix a ha]
    rw [h1, hsum] at hzfix
    exact hzfix
  have hMvv : Matrix.mulVec M v = v := add_left_cancel heq
  have hvv0 : v = 0 := by
    by_contra hne
    have hpos : 0 < mform v v := axisQ_posdef p q hp hq hpq v hne hvp hvq
    have h1 : mform v v = cc * mform v v := by
      have h := hQ v hvp hvq
      rwa [hMvv] at h
    have h2 : (1 - cc) * mform v v = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h | h
    · exact hc1 (by linarith)
    · exact absurd h (ne_of_gt hpos)
  rw [hsum, hvv0, add_zero]
  exact ha

/-- A null vector that is an eigenvector of a matrix fixing the axis plane pointwise has
eigenvalue `1`. -/
lemma eigen_null_eq_one {M : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℝ} (hM : IsJOrth M)
    (p q : E 3) (hp : p ∈ Sph 3) (hq : q ∈ Sph 3) (hpq : p ≠ q)
    (hfix : ∀ x ∈ axisPlane p q, Matrix.mulVec M x = x)
    {z : Fin 3 ⊕ Fin 1 → ℝ} (hz : z ≠ 0) (hnull : mform z z = 0) {ν : ℝ}
    (heig : Matrix.mulVec M z = ν • z) : ν = 1 := by
  by_contra hν
  obtain ⟨a, v, ha, hvp, hvq, hsum⟩ := exists_axis_decomp p q hp hq hpq z
  have hv : v ∈ axisPerp p q := ⟨hvp, hvq⟩
  have hMv : Matrix.mulVec M v ∈ axisPerp p q := mulVec_mem_axisPerp_of_fixes hM p q hfix hv
  have heq : a + Matrix.mulVec M v = ν • a + ν • v := by
    rw [hsum] at heig
    rw [Matrix.mulVec_add, hfix a ha, smul_add] at heig
    exact heig
  have h3 : a - ν • a + (Matrix.mulVec M v - ν • v) = 0 := by
    rw [show a - ν • a + (Matrix.mulVec M v - ν • v)
        = (a + Matrix.mulVec M v) - (ν • a + ν • v) from by abel, heq, sub_self]
  have h4 : a - ν • a ∈ axisPlane p q := Submodule.sub_mem _ ha (Submodule.smul_mem _ _ ha)
  have h5 : Matrix.mulVec M v - ν • v ∈ axisPerp p q :=
    Submodule.sub_mem _ hMv (Submodule.smul_mem _ _ hv)
  obtain ⟨h6, -⟩ := eq_zero_of_add_mem_axisPerp hp hq hpq h4 h5 h3
  have haν : a = ν • a := sub_eq_zero.mp h6
  have ha0 : a = 0 := by
    have h1 : (1 - ν) • a = 0 := by
      rw [sub_smul, one_smul]
      exact sub_eq_zero.mpr haν
    exact (smul_eq_zero.mp h1).resolve_left (by intro h; exact hν (by linarith))
  have hzv : z = v := by rw [hsum, ha0, zero_add]
  have hvvnull : mform v v = 0 := by rw [← hzv]; exact hnull
  have hvv0 : v = 0 := by
    by_contra hne
    exact absurd hvvnull (ne_of_gt (axisQ_posdef p q hp hq hpq v hne hvp hvq))
  exact hz (by rw [hzv, hvv0])

/-- The quadratic form of `M²` on the orthogonal complement of a fixed axis plane. -/
lemma cos_two_on_perp {M : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℝ} (hM : IsJOrth M)
    (p q : E 3) (hp : p ∈ Sph 3) (hq : q ∈ Sph 3) (hpq : p ≠ q) {cc : ℝ}
    (hfix : ∀ x ∈ axisPlane p q, Matrix.mulVec M x = x)
    (hQ : ∀ v, mform v (nvec p) = 0 → mform v (nvec q) = 0 →
      mform v (Matrix.mulVec M v) = cc * mform v v)
    (v : Fin 3 ⊕ Fin 1 → ℝ) (hvp : mform v (nvec p) = 0) (hvq : mform v (nvec q) = 0) :
    mform v (Matrix.mulVec M (Matrix.mulVec M v)) = (2 * cc ^ 2 - 1) * mform v v := by
  have hv : v ∈ axisPerp p q := ⟨hvp, hvq⟩
  have hw : Matrix.mulVec M v ∈ axisPerp p q := mulVec_mem_axisPerp_of_fixes hM p q hfix hv
  have h1 : mform v (Matrix.mulVec M v) = cc * mform v v := hQ v hvp hvq
  have h2 : mform (Matrix.mulVec M v) (Matrix.mulVec M (Matrix.mulVec M v))
      = cc * mform (Matrix.mulVec M v) (Matrix.mulVec M v) := hQ (Matrix.mulVec M v) hw.1 hw.2
  have h3 : mform (Matrix.mulVec M v) (Matrix.mulVec M v) = mform v v :=
    mform_mulVec_mulVec hM v v
  have h4 : mform (Matrix.mulVec M v) (Matrix.mulVec M (Matrix.mulVec M v))
      = mform v (Matrix.mulVec M v) := mform_mulVec_mulVec hM v (Matrix.mulVec M v)
  have h5 := hQ (v + Matrix.mulVec M v)
    (by rw [mform_add_left, hvp, hw.1, add_zero])
    (by rw [mform_add_left, hvq, hw.2, add_zero])
  simp only [Matrix.mulVec_add, mform_add_left, mform_add_right, mul_add] at h5
  have h6 : mform (Matrix.mulVec M v) v = mform v (Matrix.mulVec M v) := mform_comm _ _
  rw [h3, h4, h6] at h5
  rw [h1] at h5
  nlinarith [h5]

/-- The perp of the axis plane depends only on the plane. -/
lemma axisPerp_congr {p q p' q' : E n} (h : axisPlane p q = axisPlane p' q') :
    axisPerp p q = axisPerp p' q' := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · have h1 : nvec p' ∈ axisPlane p q := h ▸ Submodule.subset_span (by simp)
      obtain ⟨α, β, hαβ⟩ := mem_axisPlane.mp h1
      rw [← hαβ, mform_add_right, mform_smul_right, mform_smul_right, hx.1, hx.2]
      simp
    · have h1 : nvec q' ∈ axisPlane p q := h ▸ Submodule.subset_span (by simp)
      obtain ⟨α, β, hαβ⟩ := mem_axisPlane.mp h1
      rw [← hαβ, mform_add_right, mform_smul_right, mform_smul_right, hx.1, hx.2]
      simp
  · intro hx
    refine ⟨?_, ?_⟩
    · have h1 : nvec p ∈ axisPlane p' q' := h ▸ Submodule.subset_span (by simp)
      obtain ⟨α, β, hαβ⟩ := mem_axisPlane.mp h1
      rw [← hαβ, mform_add_right, mform_smul_right, mform_smul_right, hx.1, hx.2]
      simp
    · have h1 : nvec q ∈ axisPlane p' q' := h ▸ Submodule.subset_span (by simp)
      obtain ⟨α, β, hαβ⟩ := mem_axisPlane.mp h1
      rw [← hαβ, mform_add_right, mform_smul_right, mform_smul_right, hx.1, hx.2]
      simp

/-- The map recording the two `mform`-pairings with the null vectors of an axis plane. -/
def axisPerpMap (p q : E n) : (Fin n ⊕ Fin 1 → ℝ) →ₗ[ℝ] ℝ × ℝ where
  toFun x := (mform x (nvec p), mform x (nvec q))
  map_add' x y := by
    ext <;> simp [mform_add_left]
  map_smul' c x := by
    ext <;> simp [mform_smul_left]

/-- The orthogonal complement of an axis plane is two-dimensional. -/
lemma finrank_axisPerp (p q : E 3) (hp : p ∈ Sph 3) (hq : q ∈ Sph 3) (hpq : p ≠ q) :
    Module.finrank ℝ (axisPerp p q) = 2 := by
  have hs : mform (nvec p) (nvec q) ≠ 0 := mform_nvec_nvec_ne_zero p q hp hq hpq
  have hker : (axisPerpMap (p := p) (q := q)).ker = axisPerp p q := by
    ext x
    rw [LinearMap.mem_ker]
    constructor
    · intro hx
      exact ⟨congrArg Prod.fst hx, congrArg Prod.snd hx⟩
    · intro hx
      exact Prod.ext hx.1 hx.2
  have hsurj : Function.Surjective (axisPerpMap (p := p) (q := q)) := by
    rintro ⟨u, w⟩
    refine ⟨(u / mform (nvec p) (nvec q)) • nvec q
      + (w / mform (nvec p) (nvec q)) • nvec p, ?_⟩
    ext <;> simp only [axisPerpMap, LinearMap.coe_mk, AddHom.coe_mk]
    · rw [mform_add_left, mform_smul_left, mform_smul_left, mform_comm (nvec q) (nvec p),
        mform_nvec_self' hp, mul_zero, add_zero]
      field_simp [hs]
    · rw [mform_add_left, mform_smul_left, mform_smul_left, mform_nvec_self' hq, mul_zero,
        zero_add]
      field_simp [hs]
  have hfin : Module.finrank ℝ (ℝ × ℝ) = 2 := by
    simp [Module.finrank_prod]
  have hV : Module.finrank ℝ (Fin 3 ⊕ Fin 1 → ℝ) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unique]
  have hrange : Module.finrank ℝ (axisPerpMap (p := p) (q := q)).range = 2 := by
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top]
    exact hfin
  have h1 := LinearMap.finrank_range_add_finrank_ker (axisPerpMap (p := p) (q := q))
  rw [hrange, hker, hV] at h1
  omega

/-- `cos (2π/M) ≠ 1` for `M ≥ 6`. -/
lemma cos_two_pi_div_ne_one {M : ℕ} (hM : 6 ≤ M) : Real.cos (2 * Real.pi / (M : ℝ)) ≠ 1 := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by positivity
  have hθpos : 0 < 2 * Real.pi / (M : ℝ) := by positivity
  have h1 : -(2 * Real.pi) < 2 * Real.pi / (M : ℝ) := by linarith [Real.pi_pos]
  have h2 : 2 * Real.pi / (M : ℝ) < 2 * Real.pi := by
    rw [div_lt_iff₀ hMpos]
    have hM1 : (1 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 1 < M)
    nlinarith [Real.pi_pos]
  intro hcos
  have := (Real.cos_eq_one_iff_of_lt_of_lt h1 h2).mp hcos
  linarith

/-- `cos (4π/M) ≠ 1` for `M ≥ 6`. -/
lemma cos_four_pi_div_ne_one {M : ℕ} (hM : 6 ≤ M) :
    Real.cos (2 * (2 * Real.pi / (M : ℝ))) ≠ 1 := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by positivity
  have hθpos : 0 < 2 * Real.pi / (M : ℝ) := by positivity
  have h1 : -(2 * Real.pi) < 2 * (2 * Real.pi / (M : ℝ)) := by linarith [Real.pi_pos]
  have h2 : 2 * (2 * Real.pi / (M : ℝ)) < 2 * Real.pi := by
    have h4 : 2 * (2 * Real.pi / (M : ℝ)) = 4 * Real.pi / (M : ℝ) := by ring
    rw [h4, div_lt_iff₀ hMpos]
    have hM2 : (2 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 2 < M)
    nlinarith [Real.pi_pos]
  intro hcos
  have := (Real.cos_eq_one_iff_of_lt_of_lt h1 h2).mp hcos
  linarith

/-- `cos (2π/M) > 0` for `M ≥ 6`. -/
lemma cos_two_pi_div_pos {M : ℕ} (hM : 6 ≤ M) : 0 < Real.cos (2 * Real.pi / (M : ℝ)) := by
  apply Real.cos_pos_of_mem_Ioo
  constructor
  · have : 0 < 2 * Real.pi / (M : ℝ) := by positivity
    linarith [Real.pi_pos]
  · rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (M : ℝ))]
    have hM4 : (4 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 4 < M)
    nlinarith [Real.pi_pos]

/-- `sin (2π/M) ≠ 0` for `M ≥ 6`. -/
lemma sin_two_pi_div_ne_zero {M : ℕ} (hM : 6 ≤ M) : Real.sin (2 * Real.pi / (M : ℝ)) ≠ 0 := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by positivity
  have hθpos : 0 < 2 * Real.pi / (M : ℝ) := by positivity
  have hθpi : 2 * Real.pi / (M : ℝ) < Real.pi := by
    rw [div_lt_iff₀ hMpos]
    have hM2 : (2 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 2 < M)
    nlinarith [Real.pi_pos]
  exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hθpos hθpi)

/-- If `M` preserves the plane `P'` and fixes `P` pointwise then `P' ⊆ P`. -/
lemma axisPlane_le_of_preserves {M : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℝ} (hM : IsJOrth M)
    (p q p' q' : E 3) (hp : p ∈ Sph 3) (hq : q ∈ Sph 3) (hpq : p ≠ q)
    (hp' : p' ∈ Sph 3) (hq' : q' ∈ Sph 3) (hpq' : p' ≠ q') {cc : ℝ}
    (hfix : ∀ x ∈ axisPlane p q, Matrix.mulVec M x = x)
    (hpres : ∀ x ∈ axisPlane p' q', Matrix.mulVec M x ∈ axisPlane p' q')
    (hQ : ∀ v, mform v (nvec p) = 0 → mform v (nvec q) = 0 →
      mform v (Matrix.mulVec M v) = cc * mform v v)
    (hc1 : cc ≠ 1) (hcsq : cc ^ 2 ≠ 1) :
    ∀ x ∈ axisPlane p' q', x ∈ axisPlane p q := by
  have hinj : Function.Injective (Matrix.mulVec M) := mulVec_injective_of_isJOrth hM
  have hM2 : IsJOrth (M * M) := IsJOrth.mul hM hM
  have hfix2 : ∀ x ∈ axisPlane p q, Matrix.mulVec (M * M) x = x := by
    intro x hx
    rw [← Matrix.mulVec_mulVec, hfix x hx]
    exact hfix x hx
  have hQ2 : ∀ v, mform v (nvec p) = 0 → mform v (nvec q) = 0 →
      mform v (Matrix.mulVec (M * M) v) = (2 * cc ^ 2 - 1) * mform v v := by
    intro v hv1 hv2
    rw [← Matrix.mulVec_mulVec]
    exact cos_two_on_perp hM p q hp hq hpq hfix hQ v hv1 hv2
  have hc2 : (2 * cc ^ 2 - 1) ≠ 1 := by intro h; exact hcsq (by linarith)
  have hnull_θp' : mform (nvec p') (nvec p') = 0 := mform_nvec_self' hp'
  have hnull_θq' : mform (nvec q') (nvec q') = 0 := mform_nvec_self' hq'
  have hMp'mem : Matrix.mulVec M (nvec p') ∈ axisPlane p' q' :=
    hpres _ (Submodule.subset_span (by simp))
  have hMq'mem : Matrix.mulVec M (nvec q') ∈ axisPlane p' q' :=
    hpres _ (Submodule.subset_span (by simp))
  have hMp'null : mform (Matrix.mulVec M (nvec p')) (Matrix.mulVec M (nvec p')) = 0 := by
    rw [mform_mulVec_mulVec hM, hnull_θp']
  have hMq'null : mform (Matrix.mulVec M (nvec q')) (Matrix.mulVec M (nvec q')) = 0 := by
    rw [mform_mulVec_mulVec hM, hnull_θq']
  have hgoal : nvec p' ∈ axisPlane p q ∧ nvec q' ∈ axisPlane p q := by
    by_cases heigp : ∃ c : ℝ, Matrix.mulVec M (nvec p') = c • nvec p'
    · obtain ⟨c, hc⟩ := heigp
      have hc_eq : c = 1 := eigen_null_eq_one hM p q hp hq hpq hfix (nvec_ne_zero p')
        hnull_θp' hc
      have hpP : nvec p' ∈ axisPlane p q :=
        fixed_null_mem_axisPlane hM p q hp hq hpq hfix hQ hc1 (nvec_ne_zero p')
          (by rw [hc, hc_eq, one_smul])
      by_cases heigq : ∃ c : ℝ, Matrix.mulVec M (nvec q') = c • nvec q'
      · obtain ⟨c', hc'⟩ := heigq
        have hc'_eq : c' = 1 := eigen_null_eq_one hM p q hp hq hpq hfix (nvec_ne_zero q')
          hnull_θq' hc'
        have hqP : nvec q' ∈ axisPlane p q :=
          fixed_null_mem_axisPlane hM p q hp hq hpq hfix hQ hc1 (nvec_ne_zero q')
            (by rw [hc', hc'_eq, one_smul])
        exact ⟨hpP, hqP⟩
      · exfalso
        have hswap : ∃ c : ℝ, Matrix.mulVec M (nvec q') = c • nvec p' := by
          rcases eq_smul_of_mem_axisPlane_of_null hp' hq' hpq' hMq'mem hMq'null with
            ⟨c, hc⟩ | ⟨c, hc⟩
          · exact ⟨c, hc⟩
          · exact absurd ⟨c, hc⟩ heigq
        obtain ⟨c', hc'⟩ := hswap
        have hcne : c ≠ 0 := by
          intro h0
          rw [h0, zero_smul] at hc
          exact nvec_ne_zero p' (hinj (by rw [hc, Matrix.mulVec_zero]))
        have hz : nvec q' - (c' / c) • nvec p' = 0 := by
          apply hinj
          rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hc', hc, Matrix.mulVec_zero,
            smul_smul, div_mul_cancel₀ _ hcne, sub_self]
        exact nvec_ne_smul_nvec p' q' hp' hq' hpq' (c' / c) (sub_eq_zero.mp hz)
    · rcases eq_smul_of_mem_axisPlane_of_null hp' hq' hpq' hMp'mem hMp'null with
        ⟨c, hc⟩ | ⟨c, hc⟩
      · exact absurd ⟨c, hc⟩ heigp
      · have hcne : c ≠ 0 := by
          intro h0
          rw [h0, zero_smul] at hc
          exact nvec_ne_zero p' (hinj (by rw [hc, Matrix.mulVec_zero]))
        have hswap : ∃ c' : ℝ, Matrix.mulVec M (nvec q') = c' • nvec p' := by
          rcases eq_smul_of_mem_axisPlane_of_null hp' hq' hpq' hMq'mem hMq'null with
            ⟨c', hc'⟩ | ⟨c', hc'⟩
          · exact ⟨c', hc'⟩
          · exfalso
            have hc'ne : c' ≠ 0 := by
              intro h0
              rw [h0, zero_smul] at hc'
              exact nvec_ne_zero q' (hinj (by rw [hc', Matrix.mulVec_zero]))
            have hz : nvec p' - (c / c') • nvec q' = 0 := by
              apply hinj
              rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hc, hc', Matrix.mulVec_zero,
                smul_smul, div_mul_cancel₀ _ hc'ne, sub_self]
            exact nvec_ne_smul_nvec q' p' hq' hp' (Ne.symm hpq') (c / c')
              (sub_eq_zero.mp hz)
        obtain ⟨c', hc'⟩ := hswap
        have hc'ne : c' ≠ 0 := by
          intro h0
          rw [h0, zero_smul] at hc'
          exact nvec_ne_zero q' (hinj (by rw [hc', Matrix.mulVec_zero]))
        have h2p : Matrix.mulVec (M * M) (nvec p') = (c * c') • nvec p' := by
          rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_smul, hc', smul_smul]
        have hcc : c * c' = 1 := eigen_null_eq_one hM2 p q hp hq hpq hfix2 (nvec_ne_zero p')
          hnull_θp' h2p
        have hpP : nvec p' ∈ axisPlane p q :=
          fixed_null_mem_axisPlane hM2 p q hp hq hpq hfix2 hQ2 hc2 (nvec_ne_zero p')
            (by rw [h2p, hcc, one_smul])
        have h2q : Matrix.mulVec (M * M) (nvec q') = (c' * c) • nvec q' := by
          rw [← Matrix.mulVec_mulVec, hc', Matrix.mulVec_smul, hc, smul_smul]
        have hccq : c' * c = 1 := eigen_null_eq_one hM2 p q hp hq hpq hfix2 (nvec_ne_zero q')
          hnull_θq' h2q
        have hqP : nvec q' ∈ axisPlane p q :=
          fixed_null_mem_axisPlane hM2 p q hp hq hpq hfix2 hQ2 hc2 (nvec_ne_zero q')
            (by rw [h2q, hccq, one_smul])
        exact ⟨hpP, hqP⟩
  intro x hx
  obtain ⟨α, β, hαβ⟩ := mem_axisPlane.mp hx
  rw [← hαβ]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ hgoal.1) (Submodule.smul_mem _ _ hgoal.2)

/-- Two rotations by the same angle `2π/M` about (possibly different) geodesics which commute are
equal up to inversion.  Used in the final step of `conjCount3`. -/
theorem commuteRotEqOrInv (hA : Submission.Mostow.POActionProp 3)
    (hI : Submission.Mostow.HypIsometryProp 3) (M : ℕ) (hM : 6 ≤ M)
    (a b c d : Submission.Mostow.E 3) (ha : a ∈ Submission.Mostow.Sph 3)
    (hb : b ∈ Submission.Mostow.Sph 3) (hc : c ∈ Submission.Mostow.Sph 3)
    (hd : d ∈ Submission.Mostow.Sph 3) (hab : a ≠ b) (hcd : c ≠ d)
    (f g : LeanEval.Geometry.MostowRigidity.PO 3 1)
    (hf : Work.Mostow.IsRotationAbout f a b (2 * Real.pi / (M : ℝ)))
    (hg : Work.Mostow.IsRotationAbout g c d (2 * Real.pi / (M : ℝ)))
    (hcomm : f * g = g * f) :
    g = f ∨ g = f⁻¹ := by
  ------------------------------------------------------------------ --
  -- 0. group theory: equality of elements from equality of actions
  ------------------------------------------------------------------ --
  have hcomp : ∀ (x y : PO 3 1) (u : E 3), (x * y) • u = x • (y • u) := hA.2.2.2.2.1
  have hone : ∀ u : E 3, (1 : PO 3 1) • u = u := hA.2.2.2.1
  have hfaith : ∀ x : PO 3 1, (∀ u : E 3, x • u = u) → x = 1 := hA.2.2.2.2.2.1
  have heq_of_smul : ∀ x y : PO 3 1, (∀ u : E 3, x • u = y • u) → x = y := by
    intro x y huv
    have h1 : x⁻¹ * y = 1 := by
      apply hfaith
      intro u
      rw [hcomp x⁻¹ y u]
      have h2 : x⁻¹ • (x • u) = u := by
        rw [← hcomp x⁻¹ x u, inv_mul_cancel, hone u]
      rwa [huv u] at h2
    calc x = x * 1 := (mul_one x).symm
      _ = x * (x⁻¹ * y) := by rw [h1]
      _ = (x * x⁻¹) * y := by rw [mul_assoc]
      _ = 1 * y := by rw [mul_inv_cancel]
      _ = y := one_mul y
  have hemat_mul : ∀ x y : PO 3 1, emat (x * y) = emat x * emat y :=
    fun x y => LambdaMat_mul hA x y
  have hemat_one : emat (1 : PO 3 1) = 1 := LambdaMat_one hA
  have hemat_inj : ∀ x y : PO 3 1, emat x = emat y → x = y := by
    intro x y h
    apply heq_of_smul x y
    intro u
    apply hlift_injective
    have hx' : hlift (x • u) = Matrix.mulVec (emat x) (hlift u) := hlift_LambdaMat hA x u
    have hy' : hlift (y • u) = Matrix.mulVec (emat y) (hlift u) := hlift_LambdaMat hA y u
    rw [hx', hy', h]
  ------------------------------------------------------------------ --
  -- 1. the two commuting elements preserve each other's geodesics
  ------------------------------------------------------------------ --
  have hmul : ∀ u : E 3, f • (g • u) = g • (f • u) := by
    intro u
    have h1 : (f * g) • u = (g * f) • u := by rw [hcomm]
    rwa [hcomp f g u, hcomp g f u] at h1
  have hgmap : ∀ u : E 3, u ∈ geodSet a b → g • u ∈ geodSet a b := by
    intro u hu
    have h1 : f • u = u := (hf.1 u).mpr hu
    have h2 : f • (g • u) = g • u := by rw [hmul u, h1]
    exact (hf.1 (g • u)).mp h2
  have hfmap : ∀ u : E 3, u ∈ geodSet c d → f • u ∈ geodSet c d := by
    intro u hu
    have h1 : g • u = u := (hg.1 u).mpr hu
    have h2 : g • (f • u) = f • u := by rw [← hmul u, h1]
    exact (hg.1 (f • u)).mp h2
  have hffix : ∀ u : E 3, u ∈ geodSet a b → f • u = u := fun u hu => (hf.1 u).mpr hu
  have hgfix : ∀ u : E 3, u ∈ geodSet c d → g • u = u := fun u hu => (hg.1 u).mpr hu
  have hMffix : ∀ x ∈ axisPlane a b, Matrix.mulVec (emat f) x = x :=
    emat_fixes_axisPlane f a b ha hb hab hffix
  have hMgfix : ∀ x ∈ axisPlane c d, Matrix.mulVec (emat g) x = x :=
    emat_fixes_axisPlane g c d hc hd hcd hgfix
  have hMgmap : ∀ x ∈ axisPlane a b, Matrix.mulVec (emat g) x ∈ axisPlane a b :=
    emat_maps_axisPlane g a b ha hb hab hgmap
  have hMfmap : ∀ x ∈ axisPlane c d, Matrix.mulVec (emat f) x ∈ axisPlane c d :=
    emat_maps_axisPlane f c d hc hd hcd hfmap
  ------------------------------------------------------------------ --
  -- 2. the quadratic form of each lift on the normal plane
  ------------------------------------------------------------------ --
  have hc1 : Real.cos (2 * Real.pi / (M : ℝ)) ≠ 1 := cos_two_pi_div_ne_one hM
  have hccpos : 0 < Real.cos (2 * Real.pi / (M : ℝ)) := cos_two_pi_div_pos hM
  have hcsq : (Real.cos (2 * Real.pi / (M : ℝ))) ^ 2 ≠ 1 := by
    intro h
    rcases sq_eq_one_iff.mp h with h' | h'
    · exact hc1 h'
    · rw [h'] at hccpos; linarith
  have hQf : ∀ v, mform v (nvec a) = 0 → mform v (nvec b) = 0 →
      mform v (Matrix.mulVec (emat f) v) = Real.cos (2 * Real.pi / (M : ℝ)) * mform v v :=
    fun v h1 h2 => emat_cos_form f a b ha hb hab _ hf hffix v h1 h2
  have hQg : ∀ v, mform v (nvec c) = 0 → mform v (nvec d) = 0 →
      mform v (Matrix.mulVec (emat g) v) = Real.cos (2 * Real.pi / (M : ℝ)) * mform v v :=
    fun v h1 h2 => emat_cos_form g c d hc hd hcd _ hg hgfix v h1 h2
  ------------------------------------------------------------------ --
  -- 3. the two geodesics coincide
  ------------------------------------------------------------------ --
  have hle₁ : ∀ x ∈ axisPlane a b, x ∈ axisPlane c d :=
    axisPlane_le_of_preserves (emat_isJOrth g) c d a b hc hd hcd ha hb hab
      (cc := Real.cos (2 * Real.pi / (M : ℝ))) hMgfix hMgmap hQg hc1 hcsq
  have hle₂ : ∀ x ∈ axisPlane c d, x ∈ axisPlane a b :=
    axisPlane_le_of_preserves (emat_isJOrth f) a b c d ha hb hab hc hd hcd
      (cc := Real.cos (2 * Real.pi / (M : ℝ))) hMffix hMfmap hQf hc1 hcsq
  have hP12 : axisPlane a b = axisPlane c d := by
    refine le_antisymm (fun x hx => hle₁ x hx) (fun x hx => hle₂ x hx)
  ------------------------------------------------------------------ --
  -- 4. a normal vector `Z` and its image `W` under `emat f`
  ------------------------------------------------------------------ --
  have hfrk : Module.finrank ℝ (axisPerp a b) = 2 := finrank_axisPerp a b ha hb hab
  obtain ⟨Z, hZath, hZbth, hZZ⟩ := perpNullUnit (n := 3) (by norm_num) ha hb hab
  have hZa : mform Z (nvec a) = 0 := hZath
  have hZb : mform Z (nvec b) = 0 := hZbth
  set cc : ℝ := Real.cos (2 * Real.pi / (M : ℝ)) with hccdef
  set ss : ℝ := Real.sin (2 * Real.pi / (M : ℝ)) with hssdef
  have hccsq : cc ^ 2 + ss ^ 2 = 1 := by
    rw [hccdef, hssdef, add_comm]
    exact Real.sin_sq_add_cos_sq _
  have hssne : ss ≠ 0 := by rw [hssdef]; exact sin_two_pi_div_ne_zero hM
  have hsssq : ss ^ 2 ≠ 0 := pow_ne_zero 2 hssne
  have hccpos : 0 < cc := by rw [hccdef]; exact cos_two_pi_div_pos hM
  have hccne : cc ≠ 0 := ne_of_gt hccpos
  have hQf' : ∀ v, mform v (nvec a) = 0 → mform v (nvec b) = 0 →
      mform v (Matrix.mulVec (emat f) v) = cc * mform v v := by
    intro v h1 h2
    rw [hccdef]
    exact hQf v h1 h2
  have hperp_eq : axisPerp a b = axisPerp c d := axisPerp_congr hP12
  have hQg' : ∀ v, mform v (nvec a) = 0 → mform v (nvec b) = 0 →
      mform v (Matrix.mulVec (emat g) v) = cc * mform v v := by
    intro v h1 h2
    have hmem : v ∈ axisPerp c d := by
      rw [← hperp_eq]
      exact ⟨h1, h2⟩
    rw [hccdef]
    exact hQg v hmem.1 hmem.2
  set W : Fin 3 ⊕ Fin 1 → ℝ := Matrix.mulVec (emat f) Z - cc • Z with hWdef
  have hWmem : W ∈ axisPerp a b := by
    rw [hWdef]
    exact Submodule.sub_mem _
      (mulVec_mem_axisPerp_of_fixes (emat_isJOrth f) a b hMffix ⟨hZa, hZb⟩)
      (Submodule.smul_mem _ _ ⟨hZa, hZb⟩)
  have hMfZ : Matrix.mulVec (emat f) Z = cc • Z + W := by
    rw [hWdef, add_comm]
    exact (sub_add_cancel _ _).symm
  have hZW : mform Z W = 0 := by
    rw [hWdef, mform_sub_right, mform_smul_right, hQf' Z hZa hZb, hZZ, mul_one]
    ring
  have hWZ : mform W Z = 0 := by rw [mform_comm W Z]; exact hZW
  have hWW : mform W W = ss ^ 2 := by
    have h1 : mform (Matrix.mulVec (emat f) Z) (Matrix.mulVec (emat f) Z) = 1 := by
      rw [mform_mulVec_mulVec (emat_isJOrth f), hZZ]
    have h2 : mform (Matrix.mulVec (emat f) Z) Z = cc := by
      rw [mform_comm (Matrix.mulVec (emat f) Z) Z, hQf' Z hZa hZb, hZZ, mul_one]
    have h4 : mform Z (Matrix.mulVec (emat f) Z) = cc := by
      rw [hQf' Z hZa hZb, hZZ, mul_one]
    simp only [hWdef, mform_sub_left, mform_sub_right, mform_smul_left, mform_smul_right,
      h1, h2, h4, hZZ]
    nlinarith [hccsq]
  have hind : LinearIndependent ℝ ![Z, W] := by
    have hval0 : (![Z, W] : Fin 2 → Fin 3 ⊕ Fin 1 → ℝ) 0 = Z := rfl
    have hval1 : (![Z, W] : Fin 2 → Fin 3 ⊕ Fin 1 → ℝ) 1 = W := rfl
    rw [linearIndependent_fin2]
    constructor
    · rw [hval1]
      intro h
      have h' : mform W W = ss ^ 2 := hWW
      rw [h] at h'
      rw [mform_zero_left] at h'
      exact hsssq h'.symm
    · intro aa haa
      rw [hval1, hval0] at haa
      have h1 : mform Z W = aa * mform W W := by
        rw [← haa, mform_smul_left]
      rw [hZW, hWW] at h1
      have haa0 : aa = 0 := by
        rcases mul_eq_zero.mp h1.symm with h | h
        · exact h
        · exact absurd h hsssq
      have hZ0 : Z = 0 := by rw [← haa, haa0, zero_smul]
      have h' : mform Z Z = 0 := by rw [hZ0, mform_zero_left]
      rw [hZZ] at h'
      norm_num at h'
  have hrange : Set.range ![Z, W] = ({Z, W} : Set (Fin 3 ⊕ Fin 1 → ℝ)) := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · simp
      · simp
    · rintro (rfl | rfl)
      · exact ⟨0, by simp⟩
      · exact ⟨1, by simp⟩
  have hfrk_span : Module.finrank ℝ
      (Submodule.span ℝ ({Z, W} : Set (Fin 3 ⊕ Fin 1 → ℝ))) = 2 := by
    have h := finrank_span_eq_card (R := ℝ) hind
    rw [hrange] at h
    rw [h]
    simp
  have hspan_le : Submodule.span ℝ ({Z, W} : Set (Fin 3 ⊕ Fin 1 → ℝ)) ≤ axisPerp a b := by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with hx | hx
    · rw [hx]; exact ⟨hZa, hZb⟩
    · rw [hx]; exact hWmem
  have hQeq2 : Submodule.span ℝ ({Z, W} : Set (Fin 3 ⊕ Fin 1 → ℝ)) = axisPerp a b :=
    Submodule.eq_of_le_of_finrank_eq hspan_le (by rw [hfrk_span, hfrk])
  ------------------------------------------------------------------ --
  -- 5. the image of `Z` under `emat g`
  ------------------------------------------------------------------ --
  have hMgfix' : ∀ x ∈ axisPlane a b, Matrix.mulVec (emat g) x = x :=
    fun x hx => hMgfix x (hP12 ▸ hx)
  have hMgZmem : Matrix.mulVec (emat g) Z ∈ Submodule.span ℝ ({Z, W} : Set (Fin 3 ⊕ Fin 1 → ℝ)) := by
    rw [hQeq2]
    exact mulVec_mem_axisPerp_of_fixes (emat_isJOrth g) a b hMgfix' ⟨hZa, hZb⟩
  have hss2 : ss ^ 2 = 1 - cc ^ 2 := by linarith [hccsq]
  obtain ⟨p, q, hpq⟩ := Submodule.mem_span_pair.mp hMgZmem
  have hp : p = cc := by
    have h1 : mform (Matrix.mulVec (emat g) Z) Z = p := by
      rw [← hpq]
      simp only [mform_add_left, mform_smul_left, hZZ, hZW, mform_comm W Z, mul_one, mul_zero,
        add_zero]
    rw [← h1, mform_comm (Matrix.mulVec (emat g) Z) Z, hQg' Z hZa hZb, hZZ, mul_one]
  have hq2 : q ^ 2 = 1 := by
    have h1 : mform (Matrix.mulVec (emat g) Z) (Matrix.mulVec (emat g) Z) = 1 := by
      rw [mform_mulVec_mulVec (emat_isJOrth g), hZZ]
    rw [← hpq] at h1
    simp only [mform_add_left, mform_add_right, mform_smul_left, mform_smul_right, hZZ, hZW,
      mform_comm W Z, hWW, mul_one, mul_zero, add_zero, zero_add] at h1
    rw [hp] at h1
    have h2 : q ^ 2 * ss ^ 2 = ss ^ 2 := by nlinarith [h1, hccsq]
    have h3 : q ^ 2 * ss ^ 2 = 1 * ss ^ 2 := by rw [h2, one_mul]
    exact mul_right_cancel₀ hsssq h3
  have hMgZ' : Matrix.mulVec (emat g) Z = cc • Z + q • W := by
    rw [← hpq, hp]
  ------------------------------------------------------------------ --
  -- 6. the images of `W`
  ------------------------------------------------------------------ --
  have hMfW : Matrix.mulVec (emat f) W = (-(ss ^ 2)) • Z + cc • W := by
    have hmem : Matrix.mulVec (emat f) W ∈ Submodule.span ℝ ({Z, W} : Set (Fin 3 ⊕ Fin 1 → ℝ)) := by
      rw [hQeq2]
      exact mulVec_mem_axisPerp_of_fixes (emat_isJOrth f) a b hMffix hWmem
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hmem
    have hβ : β = cc := by
      have h1 : mform W (Matrix.mulVec (emat f) W) = mform W (α • Z + β • W) := by rw [← hαβ]
      rw [mform_add_right, mform_smul_right, mform_smul_right, hWZ, hWW] at h1
      rw [hQf' W hWmem.1 hWmem.2, hWW] at h1
      have h2 : β * ss ^ 2 = cc * ss ^ 2 := by linarith [h1]
      exact mul_right_cancel₀ hsssq h2
    have hα : α = -(ss ^ 2) := by
      have h1 : mform (Matrix.mulVec (emat f) Z) (Matrix.mulVec (emat f) W) = mform Z W :=
        mform_mulVec_mulVec (emat_isJOrth f) Z W
      rw [hMfZ, ← hαβ, hZW] at h1
      simp only [mform_add_left, mform_add_right, mform_smul_left, mform_smul_right, hZZ, hZW,
        hWZ, hWW, mul_one, mul_zero, add_zero, zero_add] at h1
      rw [hβ] at h1
      have h2 : cc * α + cc * ss ^ 2 = 0 := by nlinarith [h1]
      have h3 : cc * (α + ss ^ 2) = 0 := by nlinarith [h2]
      have h4 : α + ss ^ 2 = 0 := (mul_eq_zero.mp h3).resolve_left hccne
      linarith
    rw [← hαβ, hα, hβ]
  have hMgW : Matrix.mulVec (emat g) W = (-(q * ss ^ 2)) • Z + cc • W := by
    have hmem : Matrix.mulVec (emat g) W ∈ Submodule.span ℝ ({Z, W} : Set (Fin 3 ⊕ Fin 1 → ℝ)) := by
      rw [hQeq2]
      exact mulVec_mem_axisPerp_of_fixes (emat_isJOrth g) a b hMgfix' hWmem
    obtain ⟨α, β, hαβ⟩ := Submodule.mem_span_pair.mp hmem
    have hβ : β = cc := by
      have h1 : mform W (Matrix.mulVec (emat g) W) = mform W (α • Z + β • W) := by rw [← hαβ]
      rw [mform_add_right, mform_smul_right, mform_smul_right, hWZ, hWW] at h1
      rw [hQg' W hWmem.1 hWmem.2, hWW] at h1
      have h2 : β * ss ^ 2 = cc * ss ^ 2 := by linarith [h1]
      exact mul_right_cancel₀ hsssq h2
    have hα : α = -(q * ss ^ 2) := by
      have h1 : mform (Matrix.mulVec (emat g) Z) (Matrix.mulVec (emat g) W) = mform Z W :=
        mform_mulVec_mulVec (emat_isJOrth g) Z W
      rw [hMgZ', ← hαβ, hZW] at h1
      simp only [mform_add_left, mform_add_right, mform_smul_left, mform_smul_right, hZZ, hZW,
        hWZ, hWW, mul_one, mul_zero, add_zero, zero_add] at h1
      rw [hβ] at h1
      have h2 : cc * α + cc * (q * ss ^ 2) = 0 := by nlinarith [h1]
      have h3 : cc * (α + q * ss ^ 2) = 0 := by nlinarith [h2]
      have h4 : α + q * ss ^ 2 = 0 := (mul_eq_zero.mp h3).resolve_left hccne
      linarith
    rw [← hαβ, hα, hβ]
  ------------------------------------------------------------------ --
  -- 7. conclusion
  ------------------------------------------------------------------ --
  rcases sq_eq_one_iff.mp hq2 with hq | hq
  · -- `q = 1`: the two lifts agree
    have hMgZ'' : Matrix.mulVec (emat g) Z = Matrix.mulVec (emat f) Z := by
      rw [hMgZ', hq, hMfZ]
      module
    have hMgW' : Matrix.mulVec (emat g) W = Matrix.mulVec (emat f) W := by
      rw [hMgW, hMfW, hq]
      module
    have hext : Matrix.mulVec (emat g) = Matrix.mulVec (emat f) := by
      funext x
      obtain ⟨aa, vv, haa, hvp, hvq, hsum⟩ := exists_axis_decomp a b ha hb hab x
      obtain ⟨α, β, hαβ⟩ :=
        Submodule.mem_span_pair.mp (by
          rw [hQeq2]
          exact (show vv ∈ axisPerp a b from ⟨hvp, hvq⟩))
      simp only [hsum, Matrix.mulVec_add, ← hαβ, Matrix.mulVec_add, Matrix.mulVec_smul,
        hMgfix' aa haa, hMffix aa haa, hMgZ'', hMgW']
    exact Or.inl (hemat_inj g f (Matrix.ext_of_hlift (fun u => by rw [hext])))
  · -- `q = -1`: `emat g` is the inverse of `emat f`
    have hMgMfZ : Matrix.mulVec (emat g) (Matrix.mulVec (emat f) Z) = Z := by
      simp only [hMfZ, Matrix.mulVec_add, Matrix.mulVec_smul, hMgZ', hMgW, hq, hss2]
      module
    have hMgMfW : Matrix.mulVec (emat g) (Matrix.mulVec (emat f) W) = W := by
      simp only [hMfW, Matrix.mulVec_add, Matrix.mulVec_smul, hMgZ', hMgW, hq, hss2]
      module
    have hprod : Matrix.mulVec (emat g * emat f)
        = Matrix.mulVec (1 : Matrix (Fin 3 ⊕ Fin 1) (Fin 3 ⊕ Fin 1) ℝ) := by
      funext x
      obtain ⟨aa, vv, haa, hvp, hvq, hsum⟩ := exists_axis_decomp a b ha hb hab x
      obtain ⟨α, β, hαβ⟩ :=
        Submodule.mem_span_pair.mp (by
          rw [hQeq2]
          exact (show vv ∈ axisPerp a b from ⟨hvp, hvq⟩))
      simp only [← Matrix.mulVec_mulVec, Matrix.one_mulVec, hsum, Matrix.mulVec_add, ← hαβ,
        Matrix.mulVec_add, Matrix.mulVec_smul, hMffix aa haa, hMgMfZ, hMgMfW, hMgfix' aa haa]
    have hmat : emat g * emat f = 1 := Matrix.ext_of_hlift (fun u => by rw [hprod])
    have hgf : g * f = 1 := hemat_inj (g * f) 1 (by rw [hemat_mul, hmat, hemat_one])
    have hgf' : g = f⁻¹ := by
      calc g = g * (f * f⁻¹) := by rw [mul_inv_cancel, mul_one]
        _ = (g * f) * f⁻¹ := by rw [mul_assoc]
        _ = 1 * f⁻¹ := by rw [hgf]
        _ = f⁻¹ := one_mul _
    exact Or.inr hgf'

end

end Work.Mostow.gapA
