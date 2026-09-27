import Mathlib
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.BaryBase
import Submission.Work.Mostow.StabHoroForm
import Submission.Work.Mostow.ematSpec

open Matrix

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open Matrix
open scoped Matrix

variable {n : ℕ}

lemma inner_lt_one_of_ne_unit {x y : E n} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (h : x ≠ y) :
    inner ℝ x y < 1 := by
  have hle : inner ℝ x y ≤ 1 := by
    have h1 := real_inner_le_norm x y
    rwa [hx, hy, mul_one] at h1
  rcases lt_or_eq_of_le hle with h1 | h1
  · exact h1
  · exfalso
    apply h
    have hz : inner ℝ (x - y) (x - y) = 0 := by
      rw [inner_sub_left, inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq,
        real_inner_self_eq_norm_sq, real_inner_comm x y, hx, hy, h1]
      ring
    exact sub_eq_zero.1 (inner_self_eq_zero.1 hz)

lemma mform_hlift_zero_theta (ξ : E n) : mform (hlift (0 : E n)) (theta ξ) = -1 := by
  simp only [mform_eq, hspat_hlift', htime_hlift', hspat_theta, htime_theta, tpart_zero,
    inner_zero_left]
  norm_num

lemma mform_theta_theta_pair (ξ η : E n) : mform (theta ξ) (theta η) = inner ℝ ξ η - 1 := by
  simp only [mform_eq, hspat_theta, htime_theta]
  ring

lemma tpart_mul_sub_inner_eq_neg_mform (u v : E n) :
    tpart u * tpart v - inner ℝ u v = -mform (hlift u) (hlift v) := by
  simp only [mform_eq, hspat_hlift', htime_hlift']
  ring

lemma emat_isJOrth (g : PO n 1) : IsJOrth (emat g) := by
  rw [IsJOrth, emat, Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, tsign_sq, one_smul]
  exact O1_form_col (rep g)

lemma mform_emat (g : PO n 1) (x y : Fin n ⊕ Fin 1 → ℝ) :
    mform (emat g *ᵥ x) (emat g *ᵥ y) = mform x y := by
  simpa only [mink_eq_mform] using (ematSpec g).2.1 x y

lemma emat_hlift (g : PO n 1) (u : E n) : emat g *ᵥ hlift u = hlift (g • u) :=
  (ematSpec g).1 u

lemma emat_eigen_of_bd (g : PO n 1) {ξ : E n} (hξ : ξ ∈ Sph n) (h : bd g ξ = ξ) :
    ∃ lam : ℝ, lam ≠ 0 ∧ emat g *ᵥ theta ξ = lam • theta ξ := by
  obtain ⟨κ, hκ⟩ := ((ematSpec g).2.2 hξ).1 h
  have hκ' : mat (rep g) *ᵥ theta ξ = κ • theta ξ := hκ
  have hκne : κ ≠ 0 := by
    intro h0
    refine mat_mulVec_theta_ne_zero (rep g) hξ ?_
    rw [hκ', h0]
    simp
  exact ⟨tsign (rep g) * κ, mul_ne_zero (tsign_ne_zero (rep g)) hκne,
    by rw [emat, Matrix.smul_mulVec, hκ', smul_smul]⟩

lemma lev_emat_eigen (g : PO n 1) {ξ : E n} (hξ : ξ ∈ Sph n) {lam : ℝ}
    (hlam : emat g *ᵥ theta ξ = lam • theta ξ) :
    lev ξ (g • (0 : E n)) = lam⁻¹ ∧ 0 < lam ∧ busemann ξ (g • (0 : E n)) = -Real.log lam := by
  have hm : hlift (g • (0 : E n)) = emat g *ᵥ hlift (0 : E n) := (emat_hlift g 0).symm
  have hpair : mform (emat g *ᵥ hlift (0 : E n)) (emat g *ᵥ theta ξ) = -1 := by
    rw [mform_emat, mform_hlift_zero_theta]
  rw [hlam, mform_smul_right] at hpair
  have hlamne : lam ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hpair
    norm_num at hpair
  have hX : mform (emat g *ᵥ hlift (0 : E n)) (theta ξ) = -lam⁻¹ :=
    mul_left_cancel₀ hlamne (by rw [hpair, mul_neg, mul_inv_cancel₀ hlamne])
  have hlev : lev ξ (g • (0 : E n)) = lam⁻¹ := by
    have h1 : lev ξ (g • (0 : E n)) = -mform (hlift (g • (0 : E n))) (theta ξ) := by
      simp only [lev, mform_eq, hspat_hlift', htime_hlift', hspat_theta, htime_theta]
      ring
    rw [h1, hm, hX, neg_neg]
  refine ⟨hlev, ?_, ?_⟩
  · have h : 0 < lam⁻¹ := by rw [← hlev]; exact lev_pos ξ hξ (g • (0 : E n))
    rwa [inv_pos] at h
  · show Real.log (lev ξ (g • (0 : E n))) = -Real.log lam
    rw [hlev, Real.log_inv]

lemma eigen_mul_eq_one (g : PO n 1) {ξ η : E n} (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n)
    (hne : ξ ≠ η) {lam μ : ℝ} (hlam : emat g *ᵥ theta ξ = lam • theta ξ)
    (hμ : emat g *ᵥ theta η = μ • theta η) : lam * μ = 1 := by
  have hξη : inner ℝ ξ η < 1 :=
    inner_lt_one_of_ne_unit ((mem_Sph_iff ξ).1 hξ) ((mem_Sph_iff η).1 hη) hne
  have huv : mform (theta ξ) (theta η) ≠ 0 := by
    rw [mform_theta_theta_pair]; linarith
  have h := mform_emat g (theta ξ) (theta η)
  rw [hlam, hμ, mform_smul] at h
  have h' : (lam * μ - 1) * mform (theta ξ) (theta η) = 0 := by
    rw [sub_mul, one_mul, h, sub_self]
  rcases mul_eq_zero.1 h' with h2 | h2
  · linarith
  · exact absurd h2 huv

lemma eigen_eq_of_third (g : PO n 1) {ξ η ζ : E n} (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n)
    (hζ : ζ ∈ Sph n) (hζξ : ζ ≠ ξ) (hζη : ζ ≠ η) {lam μ ρ : ℝ}
    (hlam : emat g *ᵥ theta ξ = lam • theta ξ) (hμ : emat g *ᵥ theta η = μ • theta η)
    (hρ : emat g *ᵥ theta ζ = ρ • theta ζ) : lam = μ := by
  have hu : mform (theta ζ) (theta ξ) ≠ 0 := by
    rw [mform_theta_theta_pair]
    have h : inner ℝ ζ ξ < 1 :=
      inner_lt_one_of_ne_unit ((mem_Sph_iff ζ).1 hζ) ((mem_Sph_iff ξ).1 hξ) hζξ
    linarith
  have hv : mform (theta ζ) (theta η) ≠ 0 := by
    rw [mform_theta_theta_pair]
    have h : inner ℝ ζ η < 1 :=
      inner_lt_one_of_ne_unit ((mem_Sph_iff ζ).1 hζ) ((mem_Sph_iff η).1 hη) hζη
    linarith
  have h1 : ρ * lam = 1 := by
    have h := mform_emat g (theta ζ) (theta ξ)
    rw [hρ, hlam, mform_smul] at h
    have h' : (ρ * lam - 1) * mform (theta ζ) (theta ξ) = 0 := by
      rw [sub_mul, one_mul, h, sub_self]
    rcases mul_eq_zero.1 h' with h2 | h2
    · linarith
    · exact absurd h2 hu
  have h2 : ρ * μ = 1 := by
    have h := mform_emat g (theta ζ) (theta η)
    rw [hρ, hμ, mform_smul] at h
    have h' : (ρ * μ - 1) * mform (theta ζ) (theta η) = 0 := by
      rw [sub_mul, one_mul, h, sub_self]
    rcases mul_eq_zero.1 h' with h3 | h3
    · linarith
    · exact absurd h3 hv
  have hρne : ρ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    norm_num at h1
  exact mul_left_cancel₀ hρne (by rw [h1, h2])

lemma two_sub_inner_pos (ξ η : E n) (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n) (hne : ξ ≠ η) :
    0 < 2 * (1 - inner ℝ ξ η) := by
  have h := inner_lt_one_of_ne_unit ((mem_Sph_iff ξ).1 hξ) ((mem_Sph_iff η).1 hη) hne
  linarith

noncomputable def pairR (ξ η : E n) : ℝ := (Real.sqrt (2 * (1 - inner ℝ ξ η)))⁻¹

noncomputable def pairPoint (ξ η : E n) : E n := hspat (pairR ξ η • (theta ξ + theta η))

lemma pairR_pos (ξ η : E n) (h : 0 < 2 * (1 - inner ℝ ξ η)) : 0 < pairR ξ η := by
  rw [pairR]; exact inv_pos.2 (Real.sqrt_pos.2 h)

lemma pairR_mul_self (ξ η : E n) (h : 0 < 2 * (1 - inner ℝ ξ η)) :
    pairR ξ η * pairR ξ η = (2 * (1 - inner ℝ ξ η))⁻¹ := by
  rw [pairR, ← mul_inv, ← sq, Real.sq_sqrt (le_of_lt h)]

lemma hlift_pairPoint (ξ η : E n) (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n) (hne : ξ ≠ η) :
    hlift (pairPoint ξ η) = pairR ξ η • (theta ξ + theta η) := by
  have h2a := two_sub_inner_pos ξ η hξ hη hne
  have hm : mform (pairR ξ η • (theta ξ + theta η)) (pairR ξ η • (theta ξ + theta η)) = -1 := by
    have hv : mform (theta ξ + theta η) (theta ξ + theta η) = -(2 * (1 - inner ℝ ξ η)) := by
      rw [mform_add_left, mform_add_right, mform_add_right, mform_theta_theta_sph ξ hξ,
        mform_theta_theta_sph η hη, mform_theta_theta_pair, mform_theta_theta_pair,
        real_inner_comm ξ η]
      ring
    rw [mform_smul, hv, pairR_mul_self ξ η h2a, mul_neg,
      inv_mul_cancel₀ (ne_of_gt h2a)]
  have hY : 0 < (pairR ξ η • (theta ξ + theta η)) (Sum.inr 0) := by
    rw [Pi.smul_apply, Pi.add_apply, theta_inr, theta_inr, smul_eq_mul]
    have := pairR_pos ξ η h2a
    linarith
  have h := eq_hlift_of_upper (pairR ξ η • (theta ξ + theta η)) hm hY
  rw [pairPoint]
  exact h.symm

lemma hdist_pairPoint (g : PO n 1) (ξ η : E n) (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n)
    (hne : ξ ≠ η) {lam μ : ℝ} (hlam : emat g *ᵥ theta ξ = lam • theta ξ)
    (hμ : emat g *ᵥ theta η = μ • theta η) (hlamμ : lam * μ = 1) (hlampos : 0 < lam) :
    hdist (pairPoint ξ η) (g • pairPoint ξ η) = |Real.log lam| := by
  have h2a := two_sub_inner_pos ξ η hξ hη hne
  have hr2 := pairR_mul_self ξ η h2a
  have hLP := hlift_pairPoint ξ η hξ hη hne
  have hMP : emat g *ᵥ (pairR ξ η • (theta ξ + theta η))
      = pairR ξ η • (lam • theta ξ + μ • theta η) := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_add, hlam, hμ]
  have hG : hlift (g • pairPoint ξ η) = pairR ξ η • (lam • theta ξ + μ • theta η) := by
    rw [← emat_hlift, hLP, hMP]
  have hXY : mform (theta ξ + theta η) (lam • theta ξ + μ • theta η)
      = -(lam + μ) * (1 - inner ℝ ξ η) := by
    rw [mform_add_left, mform_add_right, mform_add_right, mform_smul_right, mform_smul_right,
      mform_smul_right, mform_smul_right, mform_theta_theta_sph ξ hξ, mform_theta_theta_sph η hη,
      mform_theta_theta_pair, mform_theta_theta_pair, real_inner_comm ξ η]
    ring
  have hkey : (2 * (1 - inner ℝ ξ η))⁻¹ * (1 - inner ℝ ξ η) = 1 / 2 := by
    have ha : (1 - inner ℝ ξ η) ≠ 0 := by linarith
    rw [mul_inv, mul_assoc, inv_mul_cancel₀ ha, mul_one]
    norm_num
  have hcc : -mform (hlift (pairPoint ξ η)) (hlift (g • pairPoint ξ η)) = (lam + μ) / 2 := by
    rw [hLP, hG, mform_smul, hXY, hr2]
    rw [show (2 * (1 - inner ℝ ξ η))⁻¹ * (-(lam + μ) * (1 - inner ℝ ξ η))
        = -((2 * (1 - inner ℝ ξ η))⁻¹ * (1 - inner ℝ ξ η) * (lam + μ)) from by ring]
    rw [neg_neg]
    rw [hkey]
    ring
  have harc : hdist (pairPoint ξ η) (g • pairPoint ξ η)
      = Real.arcosh (-mform (hlift (pairPoint ξ η)) (hlift (g • pairPoint ξ η))) := by
    rw [show hdist (pairPoint ξ η) (g • pairPoint ξ η)
        = Real.arcosh (tpart (pairPoint ξ η) * tpart (g • pairPoint ξ η)
            - inner ℝ (pairPoint ξ η) (g • pairPoint ξ η)) from rfl,
      tpart_mul_sub_inner_eq_neg_mform]
  have hμinv : μ = lam⁻¹ := by
    calc μ = lam⁻¹ * (lam * μ) := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hlampos), one_mul]
      _ = lam⁻¹ := by rw [hlamμ, mul_one]
  have hcosh : (lam + μ) / 2 = Real.cosh (Real.log lam) := by
    rw [hμinv, Real.cosh_eq, Real.exp_neg, Real.exp_log hlampos]
  rw [harc, hcc, hcosh]
  by_cases h : 0 ≤ Real.log lam
  · rw [abs_of_nonneg h]
    exact Real.arcosh_cosh h
  · have h' : Real.log lam < 0 := not_le.1 h
    rw [abs_of_neg h', ← Real.cosh_neg]
    exact Real.arcosh_cosh (by linarith)

end Work.Mostow
