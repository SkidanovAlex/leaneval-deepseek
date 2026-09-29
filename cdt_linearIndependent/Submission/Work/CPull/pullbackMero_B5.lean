import Mathlib
import Submission.Work.CPull.defs
import Submission.Work.CPsi.psiC_facts
import Submission.Work.Pure.b5_rel
import Submission.Work.Pure.b4_B2_ode
import Submission.Work.CPhi.exists_differentiableOn_log_ball
import Submission.Work.CPull.linear_ode_extend
import Submission.Work.CPull.even_descent
import Submission.Work.B5pull.powser_deriv
import Submission.Work.B5pull.coeff_bounds
import Submission.Work.B5pull.ode_algebra
import Submission.Work.B5pull.evp_ode

namespace Work.CPull
open Metric Complex
open scoped Topology

lemma phiC_at_zero : Submission.CDTPlan.phiC 0 = 0 := by
  simp [Submission.CDTPlan.phiC, Work.CPsi.psiC_zero, Submission.CDTPlan.hauptH]

theorem pullbackMero_B5 (Φ : ℂ → ℂ) (hΦ : DifferentiableOn ℂ Φ (Metric.ball 0 1))
    (hΦzero : ∀ z ∈ Metric.ball (0:ℂ) 1, Φ z = 0 → z = 0)
    (hrel : ∀ z ∈ Metric.ball (0:ℂ) 1, Φ z + Φ (-z) = Submission.CDTPlan.phiC (z^2) ∧
      Φ z * Φ (-z) = Submission.CDTPlan.phiC (z^2)) :
    Submission.CDTPlan.PullbackMero Submission.CDTPlan.B5 Submission.CDTPlan.phiC := by
  -- ## Part 1: basic relations
  have hPhi0 : Φ 0 = 0 := by
    have h0 : (0:ℂ) ∈ Metric.ball (0:ℂ) 1 := by simp
    have h := (hrel 0 h0).1
    rw [show (0:ℂ)^2 = (0:ℂ) by norm_num, phiC_at_zero] at h
    simp only [neg_zero] at h
    linear_combination h / 2
  have hNe1 : ∀ z ∈ Metric.ball (0:ℂ) 1, Φ z ≠ 1 := by
    intro z hz hc
    have h1 := (hrel z hz).1
    have h2 := (hrel z hz).2
    rw [hc, one_mul] at h2
    rw [hc, h2] at h1
    exact one_ne_zero (by linear_combination h1)
  have hNeg : ∀ z ∈ Metric.ball (0:ℂ) 1, Φ (-z) = Φ z / (Φ z - 1) := by
    intro z hz
    have h1 := (hrel z hz).1
    have h2 := (hrel z hz).2
    have hne' : Φ z - 1 ≠ 0 := sub_ne_zero.mpr (hNe1 z hz)
    have hsum : Φ z + Φ (-z) = Φ z * Φ (-z) := by rw [h1, h2]
    have key : Φ (-z) * (Φ z - 1) = Φ z := by
      have hh : Φ z + Φ (-z) - Φ z * Φ (-z) = 0 := by rw [hsum]; ring
      linear_combination -hh
    exact ((div_eq_iff hne').mpr key.symm).symm
  have hYphi : ∀ z ∈ Metric.ball (0:ℂ) 1, Φ z ^ 2 / (Φ z - 1) = Submission.CDTPlan.phiC (z^2) := by
    intro z hz
    have h2 := (hrel z hz).2
    rw [← h2, hNeg z hz]
    have hne' : Φ z - 1 ≠ 0 := sub_ne_zero.mpr (hNe1 z hz)
    field_simp
  -- ## Part 2: the small radius
  have hΦcont : ContinuousAt Φ 0 :=
    (hΦ.differentiableAt (Metric.ball_mem_nhds 0 one_pos)).continuousAt
  obtain ⟨r₁, hr₁pos, hr₁⟩ := Metric.continuousAt_iff.mp hΦcont (1/2) (by norm_num)
  have hr₁' : ∀ z : ℂ, ‖z‖ < r₁ → ‖Φ z‖ < 1/2 := by
    intro z hz
    have h := hr₁ (by simpa [dist_eq_norm] using hz)
    rwa [hPhi0, dist_eq_norm, sub_zero] at h
  set r : ℝ := min r₁ (1/2) with hrdef
  have hrpos : 0 < r := lt_min hr₁pos (by norm_num)
  have hrlt1 : r < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hrle : r ≤ r₁ := min_le_left _ _
  have hball_sub : Metric.ball (0:ℂ) r ⊆ Metric.ball (0:ℂ) 1 := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz ⊢
    linarith
  have hΦsmall : ∀ z : ℂ, ‖z‖ < r → ‖Φ z‖ < 1/2 := fun z hz => hr₁' z (lt_of_lt_of_le hz hrle)
  -- ## Part 3: square root `S` of `Φ - 1` and `Tht` with `Tht² = Yf - 4`
  obtain ⟨L, hLdiff, hLexp⟩ := Work.CPhi.exists_differentiableOn_log_ball (c := (0:ℂ)) (r := 1)
    (V := fun z => Φ z - 1) (hΦ.sub_const 1) (fun z hz => sub_ne_zero.mpr (hNe1 z hz))
  set S : ℂ → ℂ := fun z => Complex.exp (L z / 2) with hSdef
  have hSsq : ∀ z ∈ Metric.ball (0:ℂ) 1, S z ^ 2 = Φ z - 1 := by
    intro z hz
    simp only [hSdef]
    rw [pow_two, ← Complex.exp_add, show L z / 2 + L z / 2 = L z by ring, hLexp z hz]
  have hSne : ∀ z ∈ Metric.ball (0:ℂ) 1, S z ≠ 0 := by
    intro z hz h
    have h1 := hSsq z hz
    rw [h, zero_pow (by norm_num : 2 ≠ 0)] at h1
    exact hNe1 z hz (by linear_combination -h1)
  have hSdiff : DifferentiableOn ℂ S (Metric.ball (0:ℂ) 1) := by
    simp only [hSdef]
    exact (hLdiff.div_const 2).cexp
  -- the local coordinate `Yf`
  set Yf : ℂ → ℂ := fun z => Φ z ^ 2 / (Φ z - 1) with hYdef
  have hYeq : ∀ z, Yf z = Φ z ^ 2 / (Φ z - 1) := fun z => by rw [hYdef]
  have hYdiff : DifferentiableOn ℂ Yf (Metric.ball (0:ℂ) 1) := by
    simp only [hYdef]
    exact (hΦ.pow 2).div (hΦ.sub_const 1) (fun z hz => sub_ne_zero.mpr (hNe1 z hz))
  set Tht : ℂ → ℂ := fun z => (Φ z - 2) / S z with hThdef
  have hThsq : ∀ z ∈ Metric.ball (0:ℂ) 1, Tht z ^ 2 = Yf z - 4 := by
    intro z hz
    have h1 := hSsq z hz
    have hne : Φ z - 1 ≠ 0 := sub_ne_zero.mpr (hNe1 z hz)
    rw [hYeq]
    simp only [hThdef]
    rw [div_pow, h1]
    field_simp
    ring
  have hThne : ∀ z ∈ Metric.ball (0:ℂ) 1, Tht z ≠ 0 ↔ Φ z ≠ 2 := by
    intro z hz
    have hS := hSne z hz
    constructor
    · intro h hc
      exact h (by simp only [hThdef, hc]; simp)
    · intro h hc
      have hzero : (Φ z - 2) / S z = 0 := hc
      have hmul : Φ z - 2 = (Φ z - 2) / S z * S z := by field_simp
      rw [hzero, zero_mul] at hmul
      exact h (sub_eq_zero.mp hmul)
  have hThdiff : DifferentiableOn ℂ Tht (Metric.ball (0:ℂ) 1) := by
    simp only [hThdef]
    exact (hΦ.sub_const 2).div hSdiff hSne
  -- ## Part 4: local facts on the disc of radius `r`
  have hYsmall : ∀ z : ℂ, ‖z‖ < r → ‖Yf z‖ ≤ 1/2 := by
    intro z hz
    have h1 : ‖Φ z‖ < 1/2 := hΦsmall z hz
    have h2 : (1:ℝ)/2 ≤ ‖Φ z - 1‖ := by
      have h3 := norm_sub_norm_le (1:ℂ) (Φ z)
      rw [norm_one, norm_sub_rev] at h3
      linarith
    have h3 : 0 < ‖Φ z - 1‖ := by linarith
    have h4 : ‖Φ z‖ ^ 2 ≤ (1/2:ℝ)^2 := by
      have h : 0 ≤ ‖Φ z‖ := norm_nonneg _
      nlinarith
    rw [hYeq, norm_div, norm_pow, div_le_iff₀ h3]
    linarith
  have hYne : ∀ z ∈ Metric.ball (0:ℂ) 1, z ≠ 0 → Yf z ≠ 0 := by
    intro z hz hz0 hY0
    rw [hYeq, hYphi z hz, ← (hrel z hz).2] at hY0
    rcases mul_eq_zero.mp hY0 with h' | h'
    · exact hz0 (hΦzero z hz h')
    · have h'' : (-z) = 0 := hΦzero (-z) (by simpa using hz) h'
      exact hz0 (by simpa using congrArg Neg.neg h'')
  have h5b := Work.B5pull.coeff_bounds.1
  have h2b := Work.B5pull.coeff_bounds.2
  -- the `evp`-transfer of the two formal ODEs (`Work.Pure.b5_rel`, `Work.Pure.b4_B2_ode`)
  have hEvpOdeGlobal := Work.B5pull.evp_ode (C2 := 10) (C5 := 4) (by norm_num) (by norm_num) h2b h5b
  have hp5 := Work.B5pull.powser_deriv (fun n : ℕ => (((PowerSeries.coeff n Submission.CDTPlan.B5 : ℚ) : ℂ))) 4
    (by norm_num) h5b
  have hp2 := Work.B5pull.powser_deriv (fun n : ℕ => (((PowerSeries.coeff n Submission.CDTPlan.B2 : ℚ) : ℂ))) 10
    (by norm_num) h2b
  -- ## Part 5: the local functions
  set Uf : ℂ → ℂ := fun z => Work.CPull.evp Submission.CDTPlan.B5 (Yf z) with hUdef
  set Wf : ℂ → ℂ := fun z => Work.CPull.evp Submission.CDTPlan.B2 (Yf z) with hWdef
  set Vf : ℂ → ℂ := fun z => (Wf z - 2 * Yf z) / Tht z with hVdef
  have hVeq : ∀ z, Vf z = (Wf z - 2 * Yf z) / Tht z := fun z => by rw [hVdef]
  have hUeq : ∀ z, Uf z = Work.CPull.evp Submission.CDTPlan.B5 (Yf z) := fun z => by rw [hUdef]
  have hWeq : ∀ z, Wf z = Work.CPull.evp Submission.CDTPlan.B2 (Yf z) := fun z => by rw [hWdef]
  have hB5diff : DifferentiableOn ℂ (fun y : ℂ => Work.CPull.evp Submission.CDTPlan.B5 y)
      (Metric.ball (0:ℂ) 4) := by
    intro y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact ((hp5.2.2 y hy).differentiableAt).differentiableWithinAt
  have hB2diff : DifferentiableOn ℂ (fun y : ℂ => Work.CPull.evp Submission.CDTPlan.B2 y)
      (Metric.ball (0:ℂ) 4) := by
    intro y hy
    rw [Metric.mem_ball, dist_zero_right] at hy
    exact ((hp2.2.2 y hy).differentiableAt).differentiableWithinAt
  have hYmem4 : ∀ z : ℂ, ‖z‖ < r → Yf z ∈ Metric.ball (0:ℂ) 4 := by
    intro z hz
    rw [Metric.mem_ball, dist_zero_right]
    have h := hYsmall z hz
    linarith
  have hYdiff' : DifferentiableOn ℂ Yf (Metric.ball (0:ℂ) r) := by
    intro z hz
    exact (hYdiff.differentiableAt (isOpen_ball.mem_nhds (hball_sub hz))).differentiableWithinAt
  have hUdiff : DifferentiableOn ℂ Uf (Metric.ball (0:ℂ) r) := by
    rw [hUdef]
    exact hB5diff.comp hYdiff'
      (fun z hz => hYmem4 z (by simpa [Metric.mem_ball, dist_zero_right] using hz))
  have hWdiff : DifferentiableOn ℂ Wf (Metric.ball (0:ℂ) r) := by
    rw [hWdef]
    exact hB2diff.comp hYdiff'
      (fun z hz => hYmem4 z (by simpa [Metric.mem_ball, dist_zero_right] using hz))
  have hTht_ne : ∀ z : ℂ, ‖z‖ < r → Tht z ≠ 0 := by
    intro z hz hzero
    have hmem1 : z ∈ Metric.ball (0:ℂ) 1 :=
      hball_sub (by simpa [Metric.mem_ball, dist_zero_right] using hz)
    have h2 : Tht z ^ 2 = Yf z - 4 := hThsq z hmem1
    rw [hzero, zero_pow (by norm_num : 2 ≠ 0)] at h2
    have h1 : Yf z = 4 := by linear_combination -h2
    have h3 := hYsmall z hz
    rw [h1] at h3
    norm_num at h3
  have hVdiff : DifferentiableOn ℂ Vf (Metric.ball (0:ℂ) r) := by
    rw [hVdef]
    refine (hWdiff.sub (differentiableOn_const 2 |>.mul hYdiff')).div ?_ ?_
    · intro z hz
      exact hThdiff.differentiableAt (isOpen_ball.mem_nhds (hball_sub hz)) |>.differentiableWithinAt
    · intro z hz
      exact hTht_ne z (by simpa [Metric.mem_ball, dist_zero_right] using hz)
  -- ## Part 6: the two ODEs on the punctured disc
  have key : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < r →
      HasDerivAt Vf (deriv Yf z / (2 * Yf z) * Vf z + -(2 * deriv Tht z)) z ∧
      HasDerivAt Uf ((deriv Yf z / (2 * Yf z)) * Uf z + (2 * deriv Tht z / Yf z) * Vf z) z := by
    intro z hz0 hzr
    have hz1 : z ∈ Metric.ball (0:ℂ) 1 :=
      hball_sub (by simpa [Metric.mem_ball, dist_zero_right] using hzr)
    have hYz4 : ‖Yf z‖ < 4 := by have h := hYsmall z hzr; linarith
    have hTne : Tht z ≠ 0 := hTht_ne z hzr
    have hYne' : Yf z ≠ 0 := hYne z hz1 (fun h => by rw [h, norm_zero] at hz0; exact lt_irrefl 0 hz0)
    have hYat : HasDerivAt Yf (deriv Yf z) z :=
      (hYdiff.differentiableAt (isOpen_ball.mem_nhds hz1)).hasDerivAt
    have hTat : HasDerivAt Tht (deriv Tht z) z :=
      (hThdiff.differentiableAt (isOpen_ball.mem_nhds hz1)).hasDerivAt
    have hzmemr : z ∈ Metric.ball (0:ℂ) r := by simpa [Metric.mem_ball, dist_zero_right] using hzr
    have hVat : HasDerivAt Vf (deriv Vf z) z :=
      (hVdiff.differentiableAt (isOpen_ball.mem_nhds hzmemr)).hasDerivAt
    have hThrel : deriv Yf z = 2 * Tht z * deriv Tht z := by
      have hev : (Tht ^ 2) =ᶠ[𝓝 z] (fun w : ℂ => Yf w - 4) := by
        filter_upwards [isOpen_ball.mem_nhds hz1] with w hw
        exact hThsq w hw
      have h1 : deriv (Tht ^ 2) z = 2 * Tht z * deriv Tht z := by
        have h := (hTat.pow 2).deriv
        simpa using h
      have h2 : deriv (fun w : ℂ => Yf w - 4) z = deriv Yf z := by
        have h := (hYat.sub_const 4).deriv
        simpa using h
      rw [hev.deriv_eq, h2] at h1
      exact h1
    have hWrel : Wf z = 2 * Yf z + Tht z * Vf z := by
      rw [hVeq z]
      field_simp
      ring
    have hWid : (fun w : ℂ => 2 * Yf w + Tht w * Vf w) =ᶠ[𝓝 z] Wf := by
      filter_upwards [isOpen_ball.mem_nhds hzmemr] with w hw
      have hwn : ‖w‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hw
      have hTnew : Tht w ≠ 0 := hTht_ne w hwn
      rw [hVeq w]
      field_simp
      ring
    have hYmem4z : Yf z ∈ Metric.ball (0:ℂ) 4 := by
      rw [Metric.mem_ball, dist_zero_right]; exact hYz4
    have hB5at : HasDerivAt (fun y : ℂ => Work.CPull.evp Submission.CDTPlan.B5 y)
        (deriv (fun y : ℂ => Work.CPull.evp Submission.CDTPlan.B5 y) (Yf z)) (Yf z) :=
      (hB5diff.differentiableAt (isOpen_ball.mem_nhds hYmem4z)).hasDerivAt
    have hB2at : HasDerivAt (fun y : ℂ => Work.CPull.evp Submission.CDTPlan.B2 y)
        (deriv (fun y : ℂ => Work.CPull.evp Submission.CDTPlan.B2 y) (Yf z)) (Yf z) :=
      (hB2diff.differentiableAt (isOpen_ball.mem_nhds hYmem4z)).hasDerivAt
    have hUcomp : deriv Uf z = deriv Yf z *
        deriv (fun y : ℂ => Work.CPull.evp Submission.CDTPlan.B5 y) (Yf z) := by
      have h := (hB5at.comp z hYat).deriv
      rw [hUdef]
      simpa [Function.comp_def, mul_comm] using h
    have hWcomp : deriv Wf z = deriv Yf z *
        deriv (fun y : ℂ => Work.CPull.evp Submission.CDTPlan.B2 y) (Yf z) := by
      have h := (hB2at.comp z hYat).deriv
      rw [hWdef]
      simpa [Function.comp_def, mul_comm] using h
    have hOdeB2 := hEvpOdeGlobal.1 (Yf z) hYz4
    have hOdeB5 := hEvpOdeGlobal.2 (Yf z) hYz4
    have hWdat : deriv Wf z = 2 * deriv Yf z + deriv Tht z * Vf z + Tht z * deriv Vf z := by
      have h1 : HasDerivAt (fun w : ℂ => 2 * Yf w) (2 * deriv Yf z) z := hYat.const_mul 2
      have h2 : HasDerivAt (fun w : ℂ => Tht w * Vf w)
          (deriv Tht z * Vf z + Tht z * deriv Vf z) z := hTat.mul hVat
      have h3 : HasDerivAt Wf (2 * deriv Yf z + (deriv Tht z * Vf z + Tht z * deriv Vf z)) z :=
        (h1.add h2).congr_of_eventuallyEq hWid.symm
      rw [h3.deriv]
      ring
    have hOdeW : Yf z * (4 - Yf z) * deriv Wf z
        = deriv Yf z * ((2 - Yf z) * Wf z + Yf z ^ 2) := by
      rw [hWcomp, hWeq]
      linear_combination deriv Yf z * hOdeB2
    have hOdeU : 2 * Yf z * (4 - Yf z) * deriv Uf z
        = deriv Yf z * ((4 - Yf z) * Uf z - 2 * Wf z + 4 * Yf z) := by
      rw [hUcomp, hUeq, hWeq]
      linear_combination deriv Yf z * hOdeB5
    have halg := Work.B5pull.ode_algebra (Y := Yf z) (Th := Tht z) (U := Uf z) (W := Wf z)
      (V := Vf z) (Y' := deriv Yf z) (Th' := deriv Tht z) (U' := deriv Uf z) (W' := deriv Wf z)
      (V' := deriv Vf z) hTne hYne' (hThsq z hz1) hThrel hWrel hWdat hOdeU hOdeW
    have hUat : HasDerivAt Uf (deriv Uf z) z :=
      (hUdiff.differentiableAt (isOpen_ball.mem_nhds hzmemr)).hasDerivAt
    constructor
    · have h := hVat
      rw [halg.1] at h
      have hcoef : Tht z * deriv Tht z / Yf z = deriv Yf z / (2 * Yf z) := by
        rw [hThrel]; field_simp
      rw [hcoef] at h
      exact h
    · have h := hUat
      rw [halg.2] at h
      exact h
  -- ## Part 7: extension of `Vf` and `Uf` to the whole disc
  set ac : ℂ → ℂ := fun z => deriv Yf z / (2 * Yf z) with hacdef
  have hderivTht_p : DifferentiableOn ℂ (deriv Tht) {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} :=
    (hThdiff.deriv isOpen_ball).mono (fun z hz => by
      rw [Metric.mem_ball, dist_zero_right]; exact hz.2)
  have hTht_p : DifferentiableOn ℂ Tht {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} :=
    hThdiff.mono (fun z hz => by rw [Metric.mem_ball, dist_zero_right]; exact hz.2)
  have hY_p : DifferentiableOn ℂ Yf {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} :=
    hYdiff.mono (fun z hz => by rw [Metric.mem_ball, dist_zero_right]; exact hz.2)
  have hYne_p : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < 1 → Yf z ≠ 0 := by
    intro z h0 h1
    exact hYne z (by rw [Metric.mem_ball, dist_zero_right]; exact h1)
      (fun h => by rw [h, norm_zero] at h0; exact lt_irrefl 0 h0)
  have hYderiv_p : DifferentiableOn ℂ (deriv Yf) {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} :=
    (hYdiff.deriv isOpen_ball).mono (fun z hz => by
      rw [Metric.mem_ball, dist_zero_right]; exact hz.2)
  have hac_diff : DifferentiableOn ℂ ac {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} := by
    rw [hacdef]
    exact hYderiv_p.div (differentiableOn_const 2 |>.mul hY_p)
      (fun z hz => mul_ne_zero two_ne_zero (hYne_p z hz.1 hz.2))
  have hbv_diff : DifferentiableOn ℂ (fun z : ℂ => -(2 * deriv Tht z))
      {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} := (hderivTht_p.const_mul 2).neg
  obtain ⟨Vt, hVtdiff, hVteq⟩ := Work.CPull.linear_ode_extend (a := ac)
    (b := fun z : ℂ => -(2 * deriv Tht z)) (V := Vf) (r := r) hrpos hrlt1 hac_diff hbv_diff
    hVdiff (fun z h0 h1 => (key z h0 h1).1)
  have hVt_p : DifferentiableOn ℂ Vt {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} :=
    hVtdiff.mono (fun z hz => by rw [Metric.mem_ball, dist_zero_right]; exact hz.2)
  have hbu_diff : DifferentiableOn ℂ (fun z : ℂ => (2 * deriv Tht z / Yf z) * Vt z)
      {z : ℂ | 0 < ‖z‖ ∧ ‖z‖ < 1} :=
    ((hderivTht_p.const_mul 2).div hY_p (fun z hz => hYne_p z hz.1 hz.2)).mul hVt_p
  obtain ⟨Ut, hUtdiff, hUteq⟩ := Work.CPull.linear_ode_extend (a := ac)
    (b := fun z : ℂ => (2 * deriv Tht z / Yf z) * Vt z) (V := Uf) (r := r) hrpos hrlt1
    hac_diff hbu_diff hUdiff (fun z h0 h1 => by
      have h1' : z ∈ Metric.ball (0:ℂ) r := by
        rw [Metric.mem_ball, dist_zero_right]; exact h1
      have heq : Vt z = Vf z := hVteq h1'
      have hk := (key z h0 h1).2
      rw [heq]
      exact hk)
  -- ## Part 8: evenness of `Ut` and the conclusion
  have hUevenr : ∀ z : ℂ, ‖z‖ < r → Uf (-z) = Uf z := by
    intro z hz
    have hz1 : z ∈ Metric.ball (0:ℂ) 1 :=
      hball_sub (by rw [Metric.mem_ball, dist_zero_right]; exact hz)
    have hn1 : (-z) ∈ Metric.ball (0:ℂ) 1 := by simpa using hz1
    have hden : Φ z - 1 ≠ 0 := sub_ne_zero.mpr (hNe1 z hz1)
    rw [hUeq, hUeq]
    congr 1
    rw [hYeq, hYeq, hNeg z hz1]
    field_simp
    ring
  have hUteven : ∀ z ∈ Metric.ball (0:ℂ) 1, Ut (-z) = Ut z := by
    have hf : AnalyticOnNhd ℂ Ut (Metric.ball (0:ℂ) 1) := hUtdiff.analyticOnNhd isOpen_ball
    have hgdiff : DifferentiableOn ℂ (fun z : ℂ => Ut (-z)) (Metric.ball (0:ℂ) 1) :=
      hUtdiff.comp differentiable_neg.differentiableOn (fun z hz => by simpa using hz)
    have hg : AnalyticOnNhd ℂ (fun z : ℂ => Ut (-z)) (Metric.ball (0:ℂ) 1) :=
      hgdiff.analyticOnNhd isOpen_ball
    have hev : (fun z : ℂ => Ut (-z)) =ᶠ[𝓝 (0:ℂ)] Ut := by
      filter_upwards [isOpen_ball.mem_nhds (show (0:ℂ) ∈ Metric.ball (0:ℂ) r by simpa using hrpos)]
        with z hz
      have hzn : ‖z‖ < r := by simpa [Metric.mem_ball, dist_zero_right] using hz
      have hnegr : (-z) ∈ Metric.ball (0:ℂ) r := by
        rw [Metric.mem_ball, dist_zero_right, norm_neg]; exact hzn
      rw [hUteq hnegr, hUteq hz, hUevenr z hzn]
    have hEqOn := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hg hf
      (convex_ball (0:ℂ) 1).isPreconnected (by simp : (0:ℂ) ∈ Metric.ball (0:ℂ) 1) hev
    intro z hz
    exact hEqOn hz
  obtain ⟨N, hNdiff, hNeq⟩ := Work.CPull.even_descent Ut hUtdiff hUteven
  -- ## Part 9: `PullbackMero`
  refine ⟨1, N, by simp, hNdiff, ?_⟩
  have hr2pos : 0 < r ^ 2 := pow_pos hrpos 2
  filter_upwards [isOpen_ball.mem_nhds
    (show (0:ℂ) ∈ Metric.ball (0:ℂ) (r ^ 2) by simpa using hr2pos)] with z hz
  have hznorm : ‖z‖ < r ^ 2 := by simpa [Metric.mem_ball, dist_zero_right] using hz
  set w : ℂ := Complex.sqrt z with hw
  have hw2 : w ^ 2 = z := by
    rw [hw]
    rcases eq_or_ne z 0 with h | h
    · subst h; simp
    · rw [sqrt_eq_exp h, pow_two, ← Complex.exp_add,
        show Complex.log z / 2 + Complex.log z / 2 = Complex.log z by ring, Complex.exp_log h]
  have hwn : ‖w‖ < r := by
    have h2 : ‖w‖ ^ 2 = ‖z‖ := by rw [← norm_pow, hw2]
    nlinarith [norm_nonneg w, hznorm]
  have hwmem : w ∈ Metric.ball (0:ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]; exact hwn
  have hYw : Yf w = Submission.CDTPlan.phiC z := by
    rw [hYeq, hYphi w (hball_sub hwmem), hw2]
  have hNw : N z = Uf w := by
    rw [← hw2, hNeq w (hball_sub hwmem), hUteq hwmem]
  have hsum := (hp5.1 (Yf w) (by have h := hYsmall w hwn; linarith)).hasSum
  rw [hNw, hUeq, ← hYw]
  simpa [Work.CPull.evp] using hsum

end Work.CPull
