import Mathlib
import Submission.Work.Mostow.QIDefs
import Submission.Work.Mostow.nfDefs
import Submission.Work.Mostow.nfHoroProj
import Submission.Work.Mostow.hptOf_level

namespace Work.Mostow

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

noncomputable section

variable {n : ℕ}

/-- The fixed boundary point `ξ` of `g` makes the representative matrix `emat g` scale the null
vector `theta ξ` by a positive constant `c`, and the Minkowski pairing of any vector with `theta ξ`
is then scaled by `c⁻¹`; the constant is the inverse of the level of `g • 0`. -/
theorem nf_fix_theta {ξ : E n} (hξ : ξ ∈ Sph n) {g : PO n 1} (hg : bd g ξ = ξ) :
    ∃ c : ℝ, 0 < c ∧ emat g *ᵥ theta ξ = c • theta ξ ∧
      (∀ x : Fin n ⊕ Fin 1 → ℝ, mform (emat g *ᵥ x) (theta ξ) = c⁻¹ * mform x (theta ξ)) ∧
      lev ξ (g • (0 : E n)) = c⁻¹ := by
  set w : Fin n ⊕ Fin 1 → ℝ := mat (rep g) *ᵥ theta ξ with hwdef
  have hw : ∀ i : Fin n, w (Sum.inl i) / w (Sum.inr 0) = ξ i := by
    intro i
    rw [hwdef]
    have h := congrArg (fun v : E n => v i) hg
    simpa [bd, bdO, theta] using h
  have hw0 : w (Sum.inr 0) ≠ 0 := by
    rw [hwdef]; exact mat_mulVec_theta_ne_zero (rep g) hξ
  have hwθ : w = w (Sum.inr 0) • theta ξ := by
    have h := smul_theta_of_time_ne_zero w hw0
    have h' : WithLp.toLp 2 (fun i : Fin n => w (Sum.inl i) / w (Sum.inr 0)) = ξ := by
      rw [← hg]; rfl
    rwa [h'] at h
  set c : ℝ := tsign (rep g) * w (Sum.inr 0) with hcdef
  have hfix : emat g *ᵥ theta ξ = c • theta ξ := by
    have h1 : emat g *ᵥ theta ξ = tsign (rep g) • w := by
      rw [emat, Matrix.smul_mulVec, ← hwdef]
    rw [h1, hwθ, hcdef, smul_smul]
  have hcne : c ≠ 0 := by
    rw [hcdef]; exact mul_ne_zero (tsign_ne_zero (rep g)) hw0
  have htrick : ∀ x : Fin n ⊕ Fin 1 → ℝ,
      mform (emat g *ᵥ x) (theta ξ) = c⁻¹ * mform x (theta ξ) := by
    intro x
    have h : mform (emat g *ᵥ x) (theta ξ) * c = mform x (theta ξ) := by
      rw [mul_comm, ← mform_smul_right (emat g *ᵥ x) c (theta ξ), ← hfix,
        mform_mulVec_mulVec (nf_emat_isJOrth g) x (theta ξ)]
    calc mform (emat g *ᵥ x) (theta ξ) = mform x (theta ξ) / c := by
          rw [← h, mul_div_cancel_right₀ _ hcne]
      _ = c⁻¹ * mform x (theta ξ) := by rw [div_eq_inv_mul]
  have hlev0 : lev ξ (g • (0 : E n)) = c⁻¹ := by
    have h3 : lev ξ (g • (0 : E n)) = -mform (hlift (g • (0 : E n))) (theta ξ) := by
      rw [mform_hlift_theta', lev]; ring
    rw [h3, nf_hlift_smul, htrick, mform_hlift_theta']
    simp [tpart]
  have hcpos : 0 < c := by
    have h := lev_pos ξ hξ (g • (0 : E n))
    rw [hlev0] at h
    exact inv_pos.mp h
  exact ⟨c, hcpos, hfix, htrick, hlev0⟩

/-- `(y,0)` depends linearly on `y`. -/
lemma nf_wvec_smul (D : ℝ) (y : E n) : wvec (D • y) = D • wvec y := by
  ext i; rcases i with k | k <;> simp [wvec]

/-- `-⟨x,ξ⟩` is the level of the chart point of `x`: `lev ξ u = -⟪hlift u, θ_ξ⟫`. -/
lemma nf_lev_eq_neg_mform (ξ : E n) (u : E n) :
    lev ξ u = -mform (hlift u) (theta ξ) := by
  rw [mform_hlift_theta', lev]; ring

/-- The flat coordinate of `hptOf ξ y D` is `D • y` (for `y ⊥ ξ`). -/
lemma nf_wc_hptOf {ξ y : E n} (hξξ : inner ℝ ξ ξ = 1) (hy : inner ℝ y ξ = 0) (D : ℝ) :
    wc ξ (hptOf ξ y D) = D • y := by
  have hinner : inner ℝ (hptOf ξ y D) ξ = (1 + D ^ 2 * ‖y‖ ^ 2) / (2 * D) - D / 2 := by
    rw [hptOf]
    simp only [inner_add_left, real_inner_smul_left, real_inner_smul_right, hξξ, hy, mul_one,
      mul_zero, add_zero]
  rw [wc, hinner, hptOf]
  module

/-- `hspat ∘ horoProj ξ ∘ hlift = wc ξ`. -/
lemma nf_wc_eq_hspat_horoProj {ξ : E n} (hξ : ξ ∈ Sph n) (u : E n) :
    wc ξ u = hspat (horoProj ξ (hlift u)) := ((nfHoroProj hξ).2.2.1 u).symm

/-- Rescaling the horospherical coordinates: dividing the level by `c` and the flat coordinate
by `c⁻¹`. -/
lemma nf_smul_cancel (c D : ℝ) (hD : D ≠ 0) (x ν : E n) :
    (c⁻¹ * D)⁻¹ • (D • x - (D / 2) • ν) = c⁻¹⁻¹ • x + -(c / 2) • ν := by
  rw [_root_.mul_inv_rev, inv_inv, smul_sub, smul_smul, smul_smul, sub_eq_add_neg, ← neg_smul]
  congr 1
  · field_simp
  · field_simp

theorem normalForm {n : ℕ} {ξ : Submission.Mostow.E n} (hξ : ξ ∈ Submission.Mostow.Sph n)
    {g : LeanEval.Geometry.MostowRigidity.PO n 1} (hg : Submission.Mostow.bd g ξ = ξ) :
    ∃ (b : ℝ) (A : Submission.Mostow.E n →ₗ[ℝ] Submission.Mostow.E n) (v : Submission.Mostow.E n),
      0 < b ∧ inner ℝ v ξ = 0 ∧
      (∀ y, inner ℝ y ξ = 0 → inner ℝ (A y) ξ = 0) ∧
      (∀ y, inner ℝ y ξ = 0 → ‖A y‖ = ‖y‖) ∧
      ∀ (y : Submission.Mostow.E n) (D : ℝ), inner ℝ y ξ = 0 → 0 < D →
        Work.Mostow.lev ξ (g • Work.Mostow.hptOf ξ y D) = b * D ∧
        Work.Mostow.yc ξ (g • Work.Mostow.hptOf ξ y D) = b⁻¹ • (A y) + v := by
  obtain ⟨c, hcpos, hfix, htrick, hlev0⟩ := nf_fix_theta hξ hg
  obtain ⟨hdecomp, hproj, hspat_proj, hwvec_proj, hmf_wvec_theta, hmf_wvec_wvec, hinner_spat⟩ :=
    nfHoroProj (ξ := ξ) hξ
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hξξ : inner ℝ ξ ξ = 1 := hptOf_level_aux_inner_self hξ
  refine ⟨c⁻¹, nfA ξ (emat g), -(c / 2) • hspat (nfS ξ (emat g)), ?_, ?_, ?_, ?_, ?_⟩
  · exact inv_pos_of_pos hcpos
  · -- `v ⊥ ξ`
    have hν : inner ℝ (hspat (nfS ξ (emat g))) ξ = 0 :=
      hinner_spat _ (horoProj_idem ξ hξ _)
    rw [real_inner_smul_left, hν, mul_zero]
  · -- `A` maps `ξ^⊥` to `ξ^⊥`
    intro y hy
    rw [nfA_apply]
    exact hinner_spat _ (horoProj_idem ξ hξ _)
  · -- `A` is isometric on `ξ^⊥`
    intro y hy
    have hwy : horoProj ξ (wvec y) = wvec y := hwvec_proj y hy
    have hQfix : horoProj ξ (parabQ ξ (emat g) (wvec y)) = parabQ ξ (emat g) (wvec y) :=
      horoProj_idem ξ hξ _
    have h1 : nfA ξ (emat g) y = hspat (parabQ ξ (emat g) (wvec y)) := rfl
    have hsq : ‖nfA ξ (emat g) y‖ ^ 2 = ‖y‖ ^ 2 := by
      rw [h1, ← mform_eq_norm_sq_of_horoProj ξ hξ hQfix,
        parabQ_isom ξ hξ (nf_emat_isJOrth g) hfix hcne hwy hwy,
        hmf_wvec_wvec y y hy hy, real_inner_self_eq_norm_sq]
    rw [← Real.sqrt_sq (norm_nonneg (nfA ξ (emat g) y)), hsq, Real.sqrt_sq (norm_nonneg y)]
  · -- the normal form on the horospheres
    intro y D hy hD
    set u : E n := hptOf ξ y D with hu
    have hDne : D ≠ 0 := ne_of_gt hD
    have hlevu : lev ξ u = D := (hptOf_level ξ hξ D hD y hy).1
    have hwcu : wc ξ u = D • y := nf_wc_hptOf hξξ hy D
    -- the decomposition of `hlift u` along `V ⊕ V^⊥`
    have hdec : hlift u = wvec (D • y) + (mform (hlift u) (horoEta ξ) / 2) • theta ξ
        - (D / 2) • horoEta ξ := by
      conv_lhs => rw [hdecomp u]
      rw [hwcu, hlevu]
    -- push through the matrix
    have hX : emat g *ᵥ hlift u
        = emat g *ᵥ wvec (D • y) + (mform (hlift u) (horoEta ξ) / 2) • (emat g *ᵥ theta ξ)
          - (D / 2) • (emat g *ᵥ horoEta ξ) := by
      conv_lhs => rw [hdec]
      rw [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    have hmfX : mform (emat g *ᵥ hlift u) (theta ξ) = -(D * c⁻¹) := by
      rw [hX, mform_sub_left, mform_add_left, mform_smul_left, mform_smul_left,
        htrick, htrick, htrick, mform_theta_theta_sph ξ hξ, mform_eta_theta_sph ξ hξ,
        hmf_wvec_theta (D • y)]
      simp only [real_inner_smul_left, hy, mul_zero, mul_one]
      ring
    have hlevg : lev ξ (g • u) = c⁻¹ * D := by
      rw [nf_lev_eq_neg_mform, nf_hlift_smul, hmfX]
      ring
    have hwcX : hspat (horoProj ξ (emat g *ᵥ hlift u))
        = D • (nfA ξ (emat g) y) - (D / 2) • hspat (nfS ξ (emat g)) := by
      have hprojθ : horoProj ξ (emat g *ᵥ theta ξ) = 0 := by
        rw [hfix, horoProj_smul, horoProj_theta ξ hξ, smul_zero]
      have hprojw : horoProj ξ (emat g *ᵥ wvec (D • y))
          = D • horoProj ξ (emat g *ᵥ wvec y) := by
        rw [nf_wvec_smul, Matrix.mulVec_smul, horoProj_smul]
      rw [hX, horoProj_sub, horoProj_add, horoProj_smul, horoProj_smul, hprojθ, hprojw,
        smul_zero, add_zero, ← nfS_def]
      simp only [hspat_sub, hspat_smul, nfA_apply]
    have hwcg : wc ξ (g • u) = D • (nfA ξ (emat g) y) - (D / 2) • hspat (nfS ξ (emat g)) := by
      rw [← hspat_proj (g • u), nf_hlift_smul]
      exact hwcX
    constructor
    · exact hlevg
    · rw [yc, hlevg, hwcg]
      exact nf_smul_cancel c D hDne (nfA ξ (emat g) y) (hspat (nfS ξ (emat g)))

end

end Work.Mostow
