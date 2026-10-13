import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Sb5CmpAux` — calculus helpers for the SB5 barrier comparison

Auxiliary lemmas used by `Sb5CmpCore`/`sb5_compare`: openness of the quadrant, smoothness of the
explicit barrier `(M + δφ θ)(z/L)^{-k} + σ`, the identity `(z/L)^{-k} = (L/z)^k`, the endpoint
estimate for the barrier, and the negation rules for the ground-state operator `Lgs`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false
set_option maxHeartbeats 1600000

lemma sb5c_Qd_isOpen : IsOpen Work.Construction.Qd := by
  rw [Work.Construction.Qd]
  exact isOpen_Ioi.prod isOpen_Ioo

lemma sb5c_Qd_mem_nhds {z θ : ℝ} (h : (z, θ) ∈ Work.Construction.Qd) :
    Work.Construction.Qd ∈ 𝓝 (z, θ) := sb5c_Qd_isOpen.mem_nhds h



lemma sb5c_barrier_contDiffAt (k L M δ σ : ℝ) (φ : ℝ → ℝ)
    (hφ : ContDiffOn ℝ 2 φ (Ioo 0 (Real.pi / 2)))
    (hL : L ≠ 0) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Ioo 0 (Real.pi / 2)) :
    ContDiffAt ℝ 2 (fun p : ℝ × ℝ => (M + δ * φ p.2) * (p.1 / L) ^ (-k) + σ) (z, θ) := by
  have hφθ : ContDiffAt ℝ 2 φ θ := hφ.contDiffAt (isOpen_Ioo.mem_nhds hθ)
  have h1 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => δ * φ p.2) (z, θ) := by
    have := (hφθ.comp (z, θ) contDiffAt_snd).const_smul δ
    simpa [smul_eq_mul] using this
  have h2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => M + δ * φ p.2) (z, θ) :=
    (contDiffAt_const (c := M) (x := (z, θ))).add h1
  have h3 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => p.1 / L) (z, θ) :=
    contDiffAt_fst.div_const L
  have h4 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => (p.1 / L) ^ (-k)) (z, θ) :=
    h3.rpow_const_of_ne (div_ne_zero (ne_of_gt hz) hL)
  exact (h2.mul h4).add contDiffAt_const

/-- `(z/L)^{-k} = (L/z)^k` for `z,L > 0`. -/
lemma sb5c_rpow_neg_div_eq (k L z : ℝ) (hL : 0 < L) (hz : 0 < z) :
    (z / L) ^ (-k) = (L / z) ^ k := by
  rw [Real.rpow_neg (le_of_lt (div_pos hz hL)), Real.div_rpow (le_of_lt hz) (le_of_lt hL),
    Real.div_rpow (le_of_lt hL) (le_of_lt hz), inv_div]

/-- The endpoint estimate for the barrier. -/
lemma sb5c_endpoint_ineq {Mb ρ δ φa k z R L : ℝ}
    (hδφ : (Mb + 1) * (R / L) ^ k ≤ δ * φa) (hL : 0 < L) (hR : 0 < R) (hz : 0 < z)
    (hzR : z ≤ R) (hk : 0 ≤ k) (hρ : 0 ≤ ρ) (hMb : 0 ≤ Mb) (hδ : 0 < δ) (hφa : 0 ≤ φa) :
    Mb + 1 ≤ (Mb + ρ + δ * φa) * (L / z) ^ k := by
  have hRL : 0 < R / L := div_pos hR hL
  have hLR : 0 < L / R := div_pos hL hR
  have hLz : 0 < L / z := div_pos hL hz
  have hpow : (R / L) ^ k * (L / R) ^ k = 1 := by
    rw [← Real.mul_rpow (le_of_lt hRL) (le_of_lt hLR)]
    have h : R / L * (L / R) = 1 := by field_simp
    rw [h, Real.one_rpow]
  have hLRz : L / R ≤ L / z := by
    have h1 : L / R = L * R⁻¹ := by ring
    have h2 : L / z = L * z⁻¹ := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ hz hzR) (le_of_lt hL)
  calc Mb + 1 = (Mb + 1) * ((R / L) ^ k * (L / R) ^ k) := by rw [hpow, mul_one]
    _ = (Mb + 1) * (R / L) ^ k * (L / R) ^ k := by ring
    _ ≤ (δ * φa) * (L / R) ^ k := mul_le_mul_of_nonneg_right hδφ (le_of_lt (Real.rpow_pos_of_pos hLR k))
    _ ≤ (Mb + ρ + δ * φa) * (L / R) ^ k := by
        refine mul_le_mul_of_nonneg_right (by linarith) (le_of_lt (Real.rpow_pos_of_pos hLR k))
    _ ≤ (Mb + ρ + δ * φa) * (L / z) ^ k :=
        mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (le_of_lt hLR) hLRz hk)
          (by linarith [mul_nonneg hρ (le_of_lt (Real.rpow_pos_of_pos hLz k)),
                        mul_nonneg (le_of_lt hδ) hφa, hMb])


lemma sb5c_pz_neg (v : ℝ → ℝ → ℝ) :
    Work.Spaces.pz (fun z θ => -v z θ) = fun z θ => -Work.Spaces.pz v z θ := by
  funext z θ
  simp only [Work.Spaces.pz]
  exact deriv.neg

lemma sb5c_pth_neg (v : ℝ → ℝ → ℝ) :
    Work.Spaces.pth (fun z θ => -v z θ) = fun z θ => -Work.Spaces.pth v z θ := by
  funext z θ
  simp only [Work.Spaces.pth]
  exact deriv.neg

lemma sb5c_Dz_neg (v : ℝ → ℝ → ℝ) :
    Work.Spaces.Dz (fun z θ => -v z θ) = fun z θ => -Work.Spaces.Dz v z θ := by
  funext z θ
  simp only [Work.Spaces.Dz, sb5c_pz_neg, Pi.neg_apply]
  ring

lemma sb5c_DzIter_neg (n : ℕ) (v : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter n (fun z θ => -v z θ) = fun z θ => -Work.Spaces.DzIter n v z θ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.DzIter_succ, ih, sb5c_Dz_neg, Work.Spaces.DzIter_succ]

lemma sb5c_pthIter_neg (n : ℕ) (v : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter n (fun z θ => -v z θ) = fun z θ => -Work.Spaces.pthIter n v z θ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Work.Spaces.pthIter_succ, ih, sb5c_pth_neg, Work.Spaces.pthIter_succ]

lemma sb5c_Lgs_neg (α : ℝ) (v : ℝ → ℝ → ℝ) :
    Lgs α (fun z θ => -v z θ) = fun z θ => -Lgs α v z θ := by
  funext z θ
  simp only [Lgs, sb5c_DzIter_neg, sb5c_Dz_neg, sb5c_pthIter_neg, sb5c_pth_neg, Pi.neg_apply]
  ring

lemma sb5c_s2_pos_of_Ioo {θ : ℝ} (h : θ ∈ Ioo (0 : ℝ) (Real.pi / 2)) :
    0 < Work.Construction.s2 θ := by
  rw [Work.Construction.s2]
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [h.1]) (by linarith [h.2])

end Work.FTS_StreamBdry.SB25
