import Mathlib
import Submission.CDTPlan.InterfacesA
import Submission.Work.ANum2.Der2
import Submission.Work.ANum2.slit_N_bounds

/-! Guidance from the project lead (the requester):

# Slit second-derivative bound (real-valued; the mantissa version slitM2_sound is then monotone rounding)
Closed forms (Der2Defs.lean docstring): Q = (1+r)²w² − 2(1−6r+r²)w + (1+r)², S = √Q (principal; Q ∉ (−∞,0]
for |w| < 1), N = (1+r)² − 2(r−1)²w + (1+r)²w² + (1+r)(w−1)S, slit r w = N/(8rw) for w ≠ 0,
N' = −2(r−1)² + 2(1+r)²w + (1+r)S + (1+r)(w−1)Q'/(2S),
N'' = 2(1+r)² + (1+r)Q'/S + (1+r)(w−1)(2QQ'' − Q'²)/(4S³),
slit'' = (N''w² − 2N'w + 2N)/(8rw³). Prove the derivative identities on {0 < |w| < 1} (HasDerivAt, cpow on
slitPlane), then bound each magnitude by the triangle inequality with |w| ∈ [‖c‖−ρ, ‖c‖+ρ],
|Q'(w)| ≤ Qp, |Q(w)| ∈ [Qc − ρQp, Qc + ρQp] (MVT: |Q(w) − Q(c)| ≤ ρ·sup|Q'|), |S| = √|Q|.
Context: Theorem A, ANumerics conjunct 3 (φ_A(z) ≠ −1/72 on 1/1000 ≤ |z| ≤ 1) and the conjunct-2
second-derivative bounds. Chain: Z0 (analytic extension) + Z2 (outer winding, certificate) + Z3 (inner
unique simple zero, Rouché) + Z5 (generic argument-principle count) ⇒ Z4 (annulus zero-free), consumed by
`Work.ANum.a_numerics` (agent H25). Reuse: `Work.WindCert.circleIntegral_logDeriv_quadrants` (PROVED),
H25's disc/interval library in `Submission/Work/ANum/` (IvHi/CDHi at scale 2^48 = SB, psiASEncl_stages,
slitEnclS_mem, luneEnclS_mem, disc_selfmap_bound_hyper, hauptH_logDeriv, hGradBox_mem), and our own fleet
lemmas `circleIntegral_logDeriv_eq_divisor` and `rouche_simple_zero` (LOCAL copy on the lead's machine:
~/src/curric/leaneval-deepseek/dimitrov/Submission/Commons/Analysis/Complex/*.lean — fleet code, you may
re-prove them here; Mathlib has `MeromorphicOn.divisor` and circle integrals). No native_decide.
-/

namespace Work.ANum2
open Submission.CDTPlan Complex

theorem slit_Qmem (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ < 1) :
    Qf r z ∈ slitPlane := by
  rw [Qf_apply]
  exact (Work.APsi.slitQ_branch r hr0 hr1).1 z hz

theorem slit_hasDerivAt_Qf (r : ℝ) (z : ℂ) : HasDerivAt (Qf r) (Qd r z) z := by
  have h0 : HasDerivAt (K ((1 + (r : ℂ)) ^ 2)) 0 z := hasDerivAt_const z _
  have h1 : HasDerivAt (K (2 * (1 - 6 * (r : ℂ) + (r : ℂ) ^ 2)) * id)
      (2 * (1 - 6 * (r : ℂ) + (r : ℂ) ^ 2)) z := by
    refine ((hasDerivAt_id z).const_mul (2 * (1 - 6 * (r : ℂ) + (r : ℂ) ^ 2))).congr_deriv ?_
    ring
  have h2 : HasDerivAt (K ((1 + (r : ℂ)) ^ 2) * (id * id))
      ((1 + (r : ℂ)) ^ 2 * (2 * z)) z := by
    refine ((hasDerivAt_id z).mul (hasDerivAt_id z)).const_mul ((1 + (r : ℂ)) ^ 2) |>.congr_deriv ?_
    simp only [id_eq]
    ring
  refine ((h0.sub h1).add h2).congr_deriv ?_
  simp only [Qd_apply]
  ring

theorem slit_hasDerivAt_Qd (r : ℝ) (z : ℂ) : HasDerivAt (Qd r) (Qdd r z) z := by
  have h1 : HasDerivAt (K (2 * (1 + (r : ℂ)) ^ 2) * id) (2 * (1 + (r : ℂ)) ^ 2) z := by
    refine ((hasDerivAt_id z).const_mul (2 * (1 + (r : ℂ)) ^ 2)).congr_deriv ?_
    ring
  have h2 : HasDerivAt (K (2 * (1 - 6 * (r : ℂ) + (r : ℂ) ^ 2))) 0 z :=
    hasDerivAt_const z _
  refine (h1.sub h2).congr_deriv ?_
  simp only [Qdd_apply]
  ring

theorem slit_hasDerivAt_Sf (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (Sf r) (Sd r z) z := by
  have hQ := slit_hasDerivAt_Qf r z
  have h1 : HasDerivAt (fun u : ℂ => u ^ (1 / 2 : ℂ))
      ((1 / 2 : ℂ) * (Qf r z) ^ ((1 / 2 : ℂ) - 1)) (Qf r z) :=
    (hasStrictDerivAt_cpow_const (slit_Qmem r hr0 hr1 hz)).hasDerivAt
  have h2 := h1.comp z hQ
  refine h2.congr_deriv ?_
  have hS : Sf r z ≠ 0 := Sf_ne_zero hr0 hr1 hz
  rw [Sd_apply, show (1 / 2 : ℂ) - 1 = -(1 / 2 : ℂ) by norm_num, cpow_neg,
    show Qf r z ^ (1 / 2 : ℂ) = Sf r z from rfl]
  field_simp <;> ring

theorem slit_hasDerivAt_Sd (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (Sd r) (Sdd r z) z := by
  have hS := slit_hasDerivAt_Sf r hr0 hr1 hz
  have hQ := slit_hasDerivAt_Qd r z
  have h2S : HasDerivAt (K 2 * Sf r) (2 * Sd r z) z := hS.const_mul 2
  have hden : (K 2 * Sf r) z ≠ 0 := by
    show 2 * Sf r z ≠ 0
    exact mul_ne_zero two_ne_zero (Sf_ne_zero hr0 hr1 hz)
  have h := hQ.div h2S hden
  refine h.congr_deriv ?_
  have hSne : Sf r z ≠ 0 := Sf_ne_zero hr0 hr1 hz
  have hSq : (Sf r z) ^ 2 = Qf r z := Sf_sq r z
  rw [Sdd_apply, Sd_apply]
  simp only [K, Pi.mul_apply]
  field_simp
  rw [hSq]
  ring

theorem slit_hasDerivAt_Pf (r : ℝ) (z : ℂ) :
    HasDerivAt (Pf r) (-2 * ((r : ℂ) - 1) ^ 2 + 2 * (1 + (r : ℂ)) ^ 2 * z) z := by
  have h0 : HasDerivAt (K ((1 + (r : ℂ)) ^ 2)) 0 z := hasDerivAt_const z _
  have h1 : HasDerivAt (K (2 * ((r : ℂ) - 1) ^ 2) * id) (2 * ((r : ℂ) - 1) ^ 2) z := by
    refine ((hasDerivAt_id z).const_mul (2 * ((r : ℂ) - 1) ^ 2)).congr_deriv ?_
    ring
  have h2 : HasDerivAt (K ((1 + (r : ℂ)) ^ 2) * (id * id))
      ((1 + (r : ℂ)) ^ 2 * (2 * z)) z := by
    refine ((hasDerivAt_id z).mul (hasDerivAt_id z)).const_mul ((1 + (r : ℂ)) ^ 2) |>.congr_deriv ?_
    simp only [id_eq]
    ring
  refine ((h0.sub h1).add h2).congr_deriv ?_
  ring

theorem slit_hasDerivAt_Nf (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (Nf r) (Nd r z) z := by
  have hP := slit_hasDerivAt_Pf r z
  have hS := slit_hasDerivAt_Sf r hr0 hr1 hz
  have hlin : HasDerivAt (K (1 + (r : ℂ)) * (id - K 1)) (1 + (r : ℂ)) z := by
    refine ((hasDerivAt_id z).sub_const 1 |>.const_mul (1 + (r : ℂ))).congr_deriv ?_
    simp only [id_eq, sub_zero, mul_one]
  have hR : HasDerivAt (K (1 + (r : ℂ)) * (id - K 1) * Sf r)
      ((1 + (r : ℂ)) * Sf r z + (1 + (r : ℂ)) * (z - 1) * Sd r z) z := by
    refine (hlin.mul hS).congr_deriv ?_
    simp only [id_eq, K, Pi.mul_apply, Pi.sub_apply] <;> ring
  refine (hP.add hR).congr_deriv ?_
  rw [Nd_apply, Sd_apply]
  ring

theorem slit_hasDerivAt_Nd (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (Nd r) (Ndd r z) z := by
  have hS := slit_hasDerivAt_Sf r hr0 hr1 hz
  have hSd := slit_hasDerivAt_Sd r hr0 hr1 hz
  have h1 : HasDerivAt (K (-2 * ((r : ℂ) - 1) ^ 2) + K (2 * (1 + (r : ℂ)) ^ 2) * id)
      (2 * (1 + (r : ℂ)) ^ 2) z := by
    have h0 : HasDerivAt (K (-2 * ((r : ℂ) - 1) ^ 2)) 0 z := hasDerivAt_const z _
    have h1' : HasDerivAt (K (2 * (1 + (r : ℂ)) ^ 2) * id) (2 * (1 + (r : ℂ)) ^ 2) z := by
      refine ((hasDerivAt_id z).const_mul (2 * (1 + (r : ℂ)) ^ 2)).congr_deriv ?_
      ring
    refine (h0.add h1').congr_deriv ?_
    ring
  have h2 : HasDerivAt (K (1 + (r : ℂ)) * Sf r) ((1 + (r : ℂ)) * Sd r z) z :=
    hS.const_mul (1 + (r : ℂ))
  have hlin : HasDerivAt (K (1 + (r : ℂ)) * (id - K 1)) (1 + (r : ℂ)) z := by
    refine ((hasDerivAt_id z).sub_const 1 |>.const_mul (1 + (r : ℂ))).congr_deriv ?_
    simp only [id_eq, sub_zero, mul_one]
  have h3 : HasDerivAt (K (1 + (r : ℂ)) * (id - K 1) * Sd r)
      ((1 + (r : ℂ)) * Sd r z + (1 + (r : ℂ)) * (z - 1) * Sdd r z) z := by
    refine (hlin.mul hSd).congr_deriv ?_
    simp only [id_eq, K, Pi.mul_apply, Pi.sub_apply] <;> ring
  refine ((h1.add h2).add h3).congr_deriv ?_
  have hSne : Sf r z ≠ 0 := Sf_ne_zero hr0 hr1 hz
  have hSq : (Sf r z) ^ 2 = Qf r z := Sf_sq r z
  rw [Ndd_apply, Sd_apply, Sdd_apply]
  field_simp
  rw [hSq]
  ring

theorem slit_hasDerivAt_Gfun (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ < 1)
    (hz0 : z ≠ 0) : HasDerivAt (Gfun r) (Hd r z) z := by
  have hN := slit_hasDerivAt_Nf r hr0 hr1 hz
  have hden : HasDerivAt (K (8 * (r : ℂ)) * id) (8 * (r : ℂ)) z := by
    refine ((hasDerivAt_id z).const_mul (8 * (r : ℂ))).congr_deriv ?_
    ring
  refine (hN.div hden ?_).congr_deriv ?_
  · show 8 * (r : ℂ) * z ≠ 0
    exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (ne_of_gt hr0)))
      hz0
  · rw [Hd_apply]
    simp only [K, Pi.mul_apply, Pi.sub_apply, id_eq]
    field_simp <;> ring

theorem slit_hasDerivAt_Hd (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) {z : ℂ} (hz : ‖z‖ < 1)
    (hz0 : z ≠ 0) :
    HasDerivAt (Hd r) ((Ndd r z * z ^ 2 - 2 * Nd r z * z + 2 * Nf r z)
      / (8 * (r : ℂ) * z ^ 3)) z := by
  have hN := slit_hasDerivAt_Nf r hr0 hr1 hz
  have hNd := slit_hasDerivAt_Nd r hr0 hr1 hz
  have hnum : HasDerivAt (Nd r * id - Nf r) (Ndd r z * z) z := by
    refine ((hNd.mul (hasDerivAt_id z)).sub hN).congr_deriv ?_
    simp only [id_eq] <;> ring
  have hden : HasDerivAt (K (8 * (r : ℂ)) * (id * id)) (8 * (r : ℂ) * (2 * z)) z := by
    refine ((hasDerivAt_id z).mul (hasDerivAt_id z)).const_mul (8 * (r : ℂ)) |>.congr_deriv ?_
    simp only [id_eq] <;> ring
  have h8 : (8 : ℂ) * (r : ℂ) ≠ 0 :=
    mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (ne_of_gt hr0))
  refine (hnum.div hden ?_).congr_deriv ?_
  · simp only [K, Pi.mul_apply, id_eq]
    exact mul_ne_zero h8 (mul_ne_zero hz0 hz0)
  · have hzz : z * z ≠ 0 := mul_ne_zero hz0 hz0
    have hz3 : z ^ 3 ≠ 0 := pow_ne_zero 3 hz0
    simp only [K, Pi.mul_apply, Pi.sub_apply, id_eq]
    field_simp
    ring

theorem slit_deriv2_eq (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) {w : ℂ} (hw0 : w ≠ 0)
    (hw1 : ‖w‖ < 1) :
    deriv (deriv (slit r)) w
      = (Ndd r w * w ^ 2 - 2 * Nd r w * w + 2 * Nf r w) / (8 * (r : ℂ) * w ^ 3) := by
  rw [slit_eq_Gfun r]
  have hwball : w ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]; exact hw1
  have hwne : w ∈ ({0}ᶜ : Set ℂ) := by simpa using hw0
  have hev : deriv (Gfun r) =ᶠ[nhds w] Hd r := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hwball, isOpen_compl_singleton.mem_nhds hwne]
      with z hz hz0
    have hz1 : ‖z‖ < 1 := by rw [Metric.mem_ball, dist_zero_right] at hz; exact hz
    exact (slit_hasDerivAt_Gfun r hr0 hr1 hz1 hz0).deriv
  rw [hev.deriv_eq]
  exact (slit_hasDerivAt_Hd r hr0 hr1 hw1 hw0).deriv


theorem slit_second_deriv_bound (r : ℝ) (hr0 : 0 < r) (hr1 : r < 1) (c w : ℂ) (ρ : ℝ)
    (hρ : 0 ≤ ρ) (hw : ‖w - c‖ ≤ ρ) (hdisc : ‖c‖ + ρ < 1) (hwlo : ρ < ‖c‖)
    (hQlo : ρ * (‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * (1 + r) ^ 2)) <
      ‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖) :
    let A : ℝ := (1 + r) ^ 2
    let Qp : ℝ := ‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * A)
    let Qc : ℝ := ‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖
    let Qhi : ℝ := Qc + ρ * Qp
    let Slo : ℝ := Real.sqrt (Qc - ρ * Qp)
    let Shi : ℝ := Real.sqrt Qhi
    let wlo : ℝ := ‖c‖ - ρ
    let whi : ℝ := ‖c‖ + ρ
    let wm1 : ℝ := ‖c - 1‖ + ρ
    let N0 : ℝ := A + 2 * (r - 1) ^ 2 * whi + A * whi ^ 2 + (1 + r) * wm1 * Shi
    let N1 : ℝ := 2 * (r - 1) ^ 2 + 2 * A * whi + (1 + r) * Shi + (1 + r) * wm1 * Qp / (2 * Slo)
    let N2 : ℝ := 2 * A + (1 + r) * Qp / Slo + (1 + r) * wm1 * (2 * Qhi * (2 * A) + Qp ^ 2) / (4 * Slo ^ 3)
    ‖deriv (deriv (slit r)) w‖ ≤ (N2 * whi ^ 2 + 2 * N1 * whi + 2 * N0) / (8 * r * wlo ^ 3) := by
  have hb := slit_N_bounds r hr0 hr1 c w ρ hρ hw hdisc hwlo hQlo
  dsimp only at hb ⊢
  obtain ⟨hNdd, hNd, hNf⟩ := hb
  let A : ℝ := (1 + r) ^ 2
  let Qp : ℝ := ‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * A)
  let Qc : ℝ := ‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖
  let Qhi : ℝ := Qc + ρ * Qp
  let Slo : ℝ := Real.sqrt (Qc - ρ * Qp)
  let Shi : ℝ := Real.sqrt Qhi
  let wlo : ℝ := ‖c‖ - ρ
  let whi : ℝ := ‖c‖ + ρ
  let wm1 : ℝ := ‖c - 1‖ + ρ
  let N0 : ℝ := A + 2 * (r - 1) ^ 2 * whi + A * whi ^ 2 + (1 + r) * wm1 * Shi
  let N1 : ℝ := 2 * (r - 1) ^ 2 + 2 * A * whi + (1 + r) * Shi
    + (1 + r) * wm1 * Qp / (2 * Slo)
  let N2 : ℝ := 2 * A + (1 + r) * Qp / Slo
    + (1 + r) * wm1 * (2 * Qhi * (2 * A) + Qp ^ 2) / (4 * Slo ^ 3)
  have hNdd' : ‖Ndd r w‖ ≤ N2 := hNdd
  have hNd' : ‖Nd r w‖ ≤ N1 := hNd
  have hNf' : ‖Nf r w‖ ≤ N0 := hNf
  have hwhi : ‖w‖ ≤ whi := by
    show ‖w‖ ≤ ‖c‖ + ρ
    calc ‖w‖ = ‖c + (w - c)‖ := by congr 1; ring
      _ ≤ ‖c‖ + ‖w - c‖ := norm_add_le _ _
      _ ≤ ‖c‖ + ρ := add_le_add_right hw ‖c‖
  have hwlo' : wlo ≤ ‖w‖ := by
    show ‖c‖ - ρ ≤ ‖w‖
    have h := norm_add_le w (c - w)
    have h2 : ‖c - w‖ = ‖w - c‖ := norm_sub_rev c w
    have h3 : ‖w + (c - w)‖ = ‖c‖ := by rw [add_sub_cancel]
    linarith
  have hwm1 : ‖w - 1‖ ≤ wm1 := by
    show ‖w - 1‖ ≤ ‖c - 1‖ + ρ
    calc ‖w - 1‖ = ‖(w - c) + (c - 1)‖ := by congr 1; ring
      _ ≤ ‖w - c‖ + ‖c - 1‖ := norm_add_le _ _
      _ ≤ ρ + ‖c - 1‖ := add_le_add_left hw ‖c - 1‖
      _ = ‖c - 1‖ + ρ := by ring
  have hwlo0 : 0 < wlo := by show 0 < ‖c‖ - ρ; linarith
  have hShi0 : 0 ≤ Shi := by show 0 ≤ Real.sqrt Qhi; positivity
  have hSlo0 : 0 < Slo := by
    show 0 < Real.sqrt (Qc - ρ * Qp)
    apply Real.sqrt_pos.mpr
    have e1 : Qc = ‖(1 + r) ^ 2 * c ^ 2 - 2 * (1 - 6 * r + r ^ 2) * c + (1 + r) ^ 2‖ := rfl
    have e2 : Qp = ‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * (1 + r) ^ 2) := by
      show ‖2 * (1 + r) ^ 2 * c - 2 * (1 - 6 * r + r ^ 2)‖ + ρ * (2 * A) = _
      rw [show A = (1 + r) ^ 2 from rfl]
    rw [e1, e2]
    linarith [hQlo]
  have hw1 : ‖w‖ < 1 := by
    have : whi = ‖c‖ + ρ := rfl
    rw [this] at hwhi
    linarith [hdisc]
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hwlo'; simp at hwlo'; linarith
  rw [slit_deriv2_eq r hr0 hr1 hw0 hw1, norm_div]
  have hden_val : ‖8 * (r : ℂ) * w ^ 3‖ = 8 * r * ‖w‖ ^ 3 := by
    have hrC : ‖(r : ℂ)‖ = r := by
      rw [Complex.norm_def, Complex.normSq_ofReal, Real.sqrt_mul_self (le_of_lt hr0)]
    rw [norm_mul, norm_mul, norm_pow, hrC]
    norm_num
  have hdle : 8 * r * wlo ^ 3 ≤ ‖8 * (r : ℂ) * w ^ 3‖ := by
    rw [hden_val]
    show 8 * r * (‖c‖ - ρ) ^ 3 ≤ 8 * r * ‖w‖ ^ 3
    have h1 : (‖c‖ - ρ) ^ 3 ≤ ‖w‖ ^ 3 := by
      have := hwlo'; rw [show wlo = ‖c‖ - ρ from rfl] at this
      exact pow_le_pow_left₀ (le_of_lt hwlo0) this 3
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  have hb1 : ‖Ndd r w * w ^ 2‖ ≤ N2 * whi ^ 2 := by
    rw [norm_mul, norm_pow]
    refine mul_le_mul_of_nonneg hNdd' ?_ (norm_nonneg _) (by positivity)
    have := hwhi; rw [show whi = ‖c‖ + ρ from rfl] at this
    exact pow_le_pow_left₀ (norm_nonneg w) this 2
  have hb2 : ‖2 * Nd r w * w‖ ≤ 2 * N1 * whi := by
    rw [norm_mul, norm_mul]
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2n]
    refine mul_le_mul_of_nonneg (mul_le_mul_of_nonneg_left hNd' (by norm_num)) ?_
      (by positivity) (by positivity)
    simpa only [show (2 : ℝ) = 2 from rfl, whi] using hwhi
  have hb3 : ‖2 * Nf r w‖ ≤ 2 * N0 := by
    rw [norm_mul]
    have h2n : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2n]
    exact mul_le_mul_of_nonneg_left hNf' (by norm_num)
  have hnum : ‖Ndd r w * w ^ 2 - 2 * Nd r w * w + 2 * Nf r w‖
      ≤ N2 * whi ^ 2 + 2 * N1 * whi + 2 * N0 := by
    have h1 := norm_add_le (Ndd r w * w ^ 2 - 2 * Nd r w * w) (2 * Nf r w)
    have h2 := norm_sub_le (Ndd r w * w ^ 2) (2 * Nd r w * w)
    linarith
  have hdpos : 0 < 8 * r * wlo ^ 3 := by
    show 0 < 8 * r * (‖c‖ - ρ) ^ 3
    positivity
  calc ‖Ndd r w * w ^ 2 - 2 * Nd r w * w + 2 * Nf r w‖ / ‖8 * (r : ℂ) * w ^ 3‖
      ≤ ‖Ndd r w * w ^ 2 - 2 * Nd r w * w + 2 * Nf r w‖ / (8 * r * wlo ^ 3) :=
        div_le_div_of_nonneg_left (norm_nonneg _) hdpos hdle
    _ ≤ (N2 * whi ^ 2 + 2 * N1 * whi + 2 * N0) / (8 * r * wlo ^ 3) :=
        div_le_div_of_nonneg_right hnum (le_of_lt hdpos)



end Work.ANum2
