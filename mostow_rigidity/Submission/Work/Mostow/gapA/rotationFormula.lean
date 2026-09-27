import Mathlib
import Submission.Work.Mostow.gapA.defs
import Submission.Work.Mostow.gapA.geodFacts
import Submission.Work.Mostow.gapA.mem_geodSet_iff_span
import Submission.Work.Mostow.gapA.rotSetup

/-!
# The displacement formula of a rotation about a geodesic
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity
open Work.Mostow
open Matrix

noncomputable section

variable {n : ℕ}

/-- `emat g` preserves the Minkowski form, in `mink` form. -/
lemma mink_emat_emat (g : LeanEval.Geometry.MostowRigidity.PO n 1)
    (x y : Fin n ⊕ Fin 1 → ℝ) :
    mink (Matrix.mulVec (emat g) x) (Matrix.mulVec (emat g) y) = mink x y := by
  rw [mink_eq_mform, mink_eq_mform]
  exact mform_mulVec_mulVec (emat_isJOrth g) x y

/-- `mink (hlift u) (hlift u) = -1`. -/
lemma mink_hlift_self' (u : Submission.Mostow.E n) : mink (hlift u) (hlift u) = -1 := by
  rw [mink_hlift_hlift, real_inner_self_eq_norm_sq]
  have h := tpart_sq u
  nlinarith

/-- Cancelling a nonzero scalar. -/
lemma eq_of_smul_eq_smul {α : Type*} [AddCommMonoid α] [Module ℝ α] {c : ℝ} (hc : c ≠ 0)
    {x y : α} (h : c • x = c • y) : x = y := by
  have := congrArg (fun z => c⁻¹ • z) h
  simpa [smul_smul, inv_mul_cancel₀ hc] using this

/-- If `g` fixes `geodSet a b` pointwise, then `emat g` fixes the two boundary null vectors. -/
theorem emat_fixes_nvec (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (g : LeanEval.Geometry.MostowRigidity.PO n 1) (a b : Submission.Mostow.E n)
    (ha : a ∈ Submission.Mostow.Sph n) (hb : b ∈ Submission.Mostow.Sph n) (hab : a ≠ b)
    (hax : ∀ u : Submission.Mostow.E n, u ∈ Work.Mostow.geodSet a b → g • u = u) :
    Matrix.mulVec (emat g) (nvec a) = nvec a ∧
    Matrix.mulVec (emat g) (nvec b) = nvec b := by
  have hk : gcK a b ≠ 0 := ne_of_gt (gcK_pos a b ha hb hab)
  have e0 : gcK a b • (Matrix.mulVec (emat g) (Real.exp 0 • nvec a + Real.exp (-0) • nvec b))
      = gcK a b • (Real.exp 0 • nvec a + Real.exp (-0) • nvec b) := by
    have h := congrArg hlift (hax (gcAxisPt a b 0) (gcAxisPt_mem_geodSet a b ha hb hab 0))
    rw [← emat_hlift g (gcAxisPt a b 0), hlift_gcAxisPt a b ha hb hab 0] at h
    simp only [gcAxis] at h
    rw [Matrix.mulVec_smul] at h
    exact h
  have e1 : gcK a b • (Matrix.mulVec (emat g) (Real.exp 1 • nvec a + Real.exp (-1) • nvec b))
      = gcK a b • (Real.exp 1 • nvec a + Real.exp (-1) • nvec b) := by
    have h := congrArg hlift (hax (gcAxisPt a b 1) (gcAxisPt_mem_geodSet a b ha hb hab 1))
    rw [← emat_hlift g (gcAxisPt a b 1), hlift_gcAxisPt a b ha hb hab 1] at h
    simp only [gcAxis] at h
    rw [Matrix.mulVec_smul] at h
    exact h
  have f0 := eq_of_smul_eq_smul hk e0
  have f1 := eq_of_smul_eq_smul hk e1
  set P : Fin n ⊕ Fin 1 → ℝ := Matrix.mulVec (emat g) (nvec a) - nvec a with hP
  set Q : Fin n ⊕ Fin 1 → ℝ := Matrix.mulVec (emat g) (nvec b) - nvec b with hQ
  have hsum : P + Q = 0 := by
    have h := f0
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul] at h
    simp only [Real.exp_zero, one_smul, neg_zero] at h
    have h' : P + Q = (Matrix.mulVec (emat g) (nvec a) + Matrix.mulVec (emat g) (nvec b))
        - (nvec a + nvec b) := by rw [hP, hQ]; module
    rw [h', h, sub_self]
  have hcomb : Real.exp 1 • P + Real.exp (-1) • Q = 0 := by
    have h := f1
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul] at h
    have h' : Real.exp 1 • P + Real.exp (-1) • Q
        = (Real.exp 1 • Matrix.mulVec (emat g) (nvec a)
            + Real.exp (-1) • Matrix.mulVec (emat g) (nvec b))
          - (Real.exp 1 • nvec a + Real.exp (-1) • nvec b) := by
      rw [hP, hQ]; module
    rw [h', h, sub_self]
  have h3 : (Real.exp 1 - Real.exp (-1)) • P = 0 := by
    have h4 : Real.exp 1 • P + Real.exp (-1) • Q - Real.exp (-1) • (P + Q) = 0 := by
      rw [hcomb, hsum, smul_zero, sub_zero]
    have h5 : Real.exp 1 • P + Real.exp (-1) • Q - Real.exp (-1) • (P + Q)
        = (Real.exp 1 - Real.exp (-1)) • P := by
      rw [smul_add, smul_sub, sub_smul]; module
    rw [h5] at h4
    exact h4
  have hne : Real.exp 1 - Real.exp (-1) ≠ 0 := by
    have hlt : Real.exp (-1) < Real.exp 1 := Real.exp_lt_exp.mpr (by norm_num)
    linarith
  have hPz : P = 0 := by
    rcases smul_eq_zero.mp h3 with h | h
    · exact absurd h hne
    · exact h
  have hQz : Q = 0 := by rw [hPz, zero_add] at hsum; exact hsum
  refine ⟨?_, ?_⟩
  · rw [hP, sub_eq_zero] at hPz; exact hPz
  · rw [hQ, sub_eq_zero] at hQz; exact hQz

/-- The Minkowski square of the normal component is the `sinh`-square of the distance. -/
theorem sinh_sq_distGeod (a b u : Submission.Mostow.E n) (ha : a ∈ Submission.Mostow.Sph n)
    (hb : b ∈ Submission.Mostow.Sph n) (hab : a ≠ b) :
    Real.sinh (distGeod a b u) ^ 2 = mink (gcN a b u) (gcN a b u) := by
  have h1 : 1 ≤ Real.sqrt (lev a u * lev b u / gcL a b) := sqrt_levdiv_ge_one a b ha hb hab u
  have hnn : 0 ≤ lev a u * lev b u / gcL a b :=
    div_nonneg (mul_nonneg (le_of_lt (lev_pos a ha u)) (le_of_lt (lev_pos b hb u)))
      (le_of_lt (gcL_pos a b ha hb hab))
  have hcosh : Real.cosh (distGeod a b u) = Real.sqrt (lev a u * lev b u / gcL a b) := by
    rw [distGeod_eq a b ha hb u]; exact Real.cosh_arcosh h1
  rw [gcN_self_mink a b ha hb hab u, Real.sinh_sq, hcosh, Real.sq_sqrt hnn]

/-- The key algebraic computation. -/
theorem mink_hlift_emat_hlift (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (g : LeanEval.Geometry.MostowRigidity.PO n 1) (a b u : Submission.Mostow.E n)
    (ha : a ∈ Submission.Mostow.Sph n) (hb : b ∈ Submission.Mostow.Sph n) (hab : a ≠ b)
    (hMA : Matrix.mulVec (emat g) (nvec a) = nvec a)
    (hMB : Matrix.mulVec (emat g) (nvec b) = nvec b) (c : ℝ)
    (hparam : ∀ Z : Fin n ⊕ Fin 1 → ℝ, mink Z (nvec a) = 0 → mink Z (nvec b) = 0 →
      mink (Matrix.mulVec (emat g) Z) Z = c * mink Z Z) :
    mink (hlift u) (Matrix.mulVec (emat g) (hlift u))
      = -1 - (1 - c) * mink (gcN a b u) (gcN a b u) := by
  set Z : Fin n ⊕ Fin 1 → ℝ := gcN a b u with hZ
  set S : Fin n ⊕ Fin 1 → ℝ := gcA a b u • nvec a + gcB a b u • nvec b with hS
  have hX : S + Z = hlift u := gcN_expand a b u
  have hZa : mink Z (nvec a) = 0 := mink_gcN_nvec_a a b ha hb hab u
  have hZb : mink Z (nvec b) = 0 := mink_gcN_nvec_b a b ha hb hab u
  have haZ : mink (nvec a) Z = 0 := by rw [minkSeg_comm]; exact hZa
  have hbZ : mink (nvec b) Z = 0 := by rw [minkSeg_comm]; exact hZb
  have hMS : Matrix.mulVec (emat g) S = S := by
    rw [hS, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hMA, hMB]
  have hMZa : mink (nvec a) (Matrix.mulVec (emat g) Z) = 0 := by
    rw [← hMA, mink_emat_emat g (nvec a) Z, haZ]
  have hMZb : mink (nvec b) (Matrix.mulVec (emat g) Z) = 0 := by
    rw [← hMB, mink_emat_emat g (nvec b) Z, hbZ]
  have hMX : mink (hlift u) (Matrix.mulVec (emat g) (hlift u))
      = mink S S + mink S (Matrix.mulVec (emat g) Z) + mink Z S
        + mink Z (Matrix.mulVec (emat g) Z) := by
    rw [← hX]
    have hMSZ : Matrix.mulVec (emat g) (S + Z) = S + Matrix.mulVec (emat g) Z := by
      rw [Matrix.mulVec_add, hMS]
    rw [hMSZ]
    simp only [minkSeg_add_left, minkSeg_add_right]
    ring
  have hSZ : mink S Z = 0 := by
    rw [hS, minkSeg_add_left, mink_smul_left'', mink_smul_left'', haZ, hbZ]
    ring
  have hZS : mink Z S = 0 := by rw [minkSeg_comm]; exact hSZ
  have hSMZ : mink S (Matrix.mulVec (emat g) Z) = 0 := by
    rw [hS, minkSeg_add_left, mink_smul_left'', mink_smul_left'', hMZa, hMZb]
    ring
  have hZZ : mink Z (Matrix.mulVec (emat g) Z) = c * mink Z Z := by
    rw [minkSeg_comm, hparam Z hZa hZb]
  have hSS : mink S S = -1 - mink Z Z := by
    have h1 : mink (hlift u) (hlift u) = -1 := mink_hlift_self' u
    have h2 : mink (hlift u) (hlift u) = mink S S + mink Z Z := by
      rw [← hX]
      simp only [minkSeg_add_left, minkSeg_add_right, hSZ, hZS, add_zero, zero_add]
    linarith
  rw [hMX]
  simp only [hSMZ, hZS, hZZ, hSS, hSZ]
  try ring

/-- **The displacement formula.** -/
theorem isRotationAbout_of_param (hA : Submission.Mostow.POActionProp n)
    (hI : Submission.Mostow.HypIsometryProp n)
    (g : LeanEval.Geometry.MostowRigidity.PO n 1) (a b : Submission.Mostow.E n)
    (ha : a ∈ Submission.Mostow.Sph n) (hb : b ∈ Submission.Mostow.Sph n) (hab : a ≠ b)
    (hfix : ∀ u : Submission.Mostow.E n, g • u = u ↔ u ∈ Work.Mostow.geodSet a b)
    (c : ℝ)
    (hparam : ∀ Z : Fin n ⊕ Fin 1 → ℝ, mink Z (nvec a) = 0 → mink Z (nvec b) = 0 →
      mink (Matrix.mulVec (emat g) Z) Z = c * mink Z Z)
    (θ : ℝ) (hθ0 : 0 < θ) (hθπ : θ ≤ Real.pi) (hcos : Real.cos θ = c) :
    Work.Mostow.IsRotationAbout g a b θ := by
  obtain ⟨hMA, hMB⟩ := emat_fixes_nvec hA hI g a b ha hb hab (fun u hu => (hfix u).mpr hu)
  have hhalf : 2 * Real.sin (θ / 2) ^ 2 = 1 - c := by
    have h := Real.cos_two_mul_eq_one_sub (x := θ / 2)
    rw [show 2 * (θ / 2) = θ from by ring, hcos] at h
    linarith
  constructor
  · exact hfix
  · intro u
    have hcosh : Real.cosh (hdist u (g • u))
        = 1 + 2 * Real.sin (θ / 2) ^ 2 * Real.sinh (distGeod a b u) ^ 2 := by
      have h1 : Real.cosh (hdist u (g • u)) = -mink (hlift u) (hlift (g • u)) := by
        rw [mink_hlift_neg_cosh' u (g • u)]; ring
      have h2 : mink (hlift u) (hlift (g • u))
          = -1 - (1 - c) * Real.sinh (distGeod a b u) ^ 2 := by
        rw [← emat_hlift g u,
          mink_hlift_emat_hlift hA hI g a b u ha hb hab hMA hMB c hparam,
          ← sinh_sq_distGeod a b u ha hb hab]
      calc Real.cosh (hdist u (g • u))
          = -mink (hlift u) (hlift (g • u)) := h1
        _ = -(-1 - (1 - c) * Real.sinh (distGeod a b u) ^ 2) := by rw [h2]
        _ = 1 + 2 * Real.sin (θ / 2) ^ 2 * Real.sinh (distGeod a b u) ^ 2 := by
              rw [← hhalf]; ring
    have hsh : 0 ≤ Real.sinh (distGeod a b u) :=
      Real.sinh_nonneg_iff.mpr (distGeod_nonneg a b ha hb hab u)
    have hsin : 0 ≤ Real.sin (θ / 2) :=
      Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith)
    have hs : 0 ≤ Real.sinh (distGeod a b u) * Real.sin (θ / 2) := mul_nonneg hsh hsin
    have h2 : Real.cosh (hdist u (g • u))
        = Real.cosh (2 * Real.arsinh (Real.sinh (distGeod a b u) * Real.sin (θ / 2))) := by
      rw [Real.cosh_two_mul, Real.cosh_arsinh, Real.sinh_arsinh]
      rw [hcosh]
      rw [Real.sq_sqrt (by positivity)]
      ring
    have harsinh : 0 ≤ 2 * Real.arsinh (Real.sinh (distGeod a b u) * Real.sin (θ / 2)) := by
      have := Real.arsinh_nonneg_iff.mpr hs
      linarith
    have h3 := congrArg Real.arcosh h2
    rw [Real.arcosh_cosh (hI.1 u (g • u)), Real.arcosh_cosh harsinh] at h3
    exact h3

end

end Work.Mostow.gapA
