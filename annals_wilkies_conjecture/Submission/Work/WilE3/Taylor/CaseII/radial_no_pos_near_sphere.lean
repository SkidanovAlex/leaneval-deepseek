import Mathlib
import Submission.Work.WilE3.Loj.curve_selection
import Submission.Work.WilE3.Taylor.Polar.Basic
import Submission.Work.WilE3.Taylor.Polar.Lagrange
import Submission.Work.WilE3.Taylor.criticalValueSeparation
import Submission.Work.WilE3.Taylor.CaseII.sphere_constraint_deriv_eq_zero
import Submission.Work.WilE3.Taylor.CaseII.sum_dv_mul_grad_eq_zero
import Submission.Work.WilE3.Taylor.CaseII.analyticAt_radialEq

namespace Work.WilE3.Taylor.CaseII

set_option autoImplicit false
open Classical Topology
open scoped Topology

/-- The semianalytic equation whose zero set is "on the sphere `∑ᵢ(xᵢ - yᵢ)² = δ²` **and**
`∇Φ x ∥ x - y`": `(∑ᵢ (xᵢ - yᵢ)² - δ²)²` plus the sum of squares of all `2×2` minors of
`(∇Φ x, x - y)`. -/
private noncomputable def radEq {k : ℕ} (Φ : (Fin k → ℝ) → ℝ) (y : Fin k → ℝ) (δ : ℝ) :
    (Fin k → ℝ) → ℝ :=
  fun x => (∑ i, (x i - y i) ^ 2 - δ ^ 2) ^ 2
    + ∑ p : Fin k × Fin k, (fderiv ℝ Φ x (Pi.single p.1 1) * (x p.2 - y p.2)
        - fderiv ℝ Φ x (Pi.single p.2 1) * (x p.1 - y p.1)) ^ 2

theorem radial_no_pos_near_sphere {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {y z : Fin k → ℝ} {δ : ℝ}
    (hΦ : ∀ x, AnalyticAt ℝ Φ x) (hz : Φ z = 0) (hzc : ∑ i, (z i - y i) ^ 2 = δ ^ 2) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ w : Fin k → ℝ, dist w z < ρ → (∑ i, (w i - y i) ^ 2 = δ ^ 2) →
      (∀ i j : Fin k,
        fderiv ℝ Φ w (Pi.single i 1) * (w j - y j)
          - fderiv ℝ Φ w (Pi.single j 1) * (w i - y i) = 0) → Φ w ≤ 0 := by
  classical
  by_cases hδ : δ = 0
  · -- The sphere is a single point: `z = y` and every admissible `w` equals `y`.
    refine ⟨1, one_pos, fun w _ hwsph _ => ?_⟩
    have hwy : w = y := by
      have hsum : ∑ i, (w i - y i) ^ 2 = 0 := by rw [hwsph, hδ]; ring
      funext i
      have hterm : (w i - y i) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
          (f := fun i : Fin k => (w i - y i) ^ 2) (fun i _ => sq_nonneg _)).mp hsum i
          (Finset.mem_univ i)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hterm)
    have hzy : z = y := by
      have hsum : ∑ i, (z i - y i) ^ 2 = 0 := by rw [hzc, hδ]; ring
      funext i
      have hterm : (z i - y i) ^ 2 = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
          (f := fun i : Fin k => (z i - y i) ^ 2) (fun i _ => sq_nonneg _)).mp hsum i
          (Finset.mem_univ i)
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp hterm)
    rw [hwy, ← hzy]
    exact le_of_eq hz
  · -- `δ ≠ 0`.  Suppose the conclusion fails: bad points accumulate at `z`.
    by_contra hcon
    have hbad : ∀ ρ : ℝ, 0 < ρ → ∃ w : Fin k → ℝ, dist w z < ρ ∧
        (∑ i, (w i - y i) ^ 2 = δ ^ 2) ∧
        (∀ i j : Fin k, fderiv ℝ Φ w (Pi.single i 1) * (w j - y j)
          - fderiv ℝ Φ w (Pi.single j 1) * (w i - y i) = 0) ∧ 0 < Φ w := by
      intro ρ hρ
      by_contra h
      refine hcon ⟨ρ, hρ, fun w hw hsph hrad => ?_⟩
      by_contra hlt
      exact h ⟨w, hw, hsph, hrad, lt_of_not_ge hlt⟩
    set F : (Fin k → ℝ) → ℝ := radEq Φ y δ with hF
    have hFan : AnalyticAt ℝ F z := by
      rw [hF]
      exact analyticAt_radialEq (Φ := Φ) (y := y) (δ := δ) hΦ
    -- `z` is in the closure of the basic semianalytic bad set
    have hcl : z ∈ closure (WilkiesDesign.CG.C4a.BasicSA F (fun _ : Fin 1 => Φ)) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨w, hw1, hw2, hw3, hw4⟩ := hbad ε hε
      refine ⟨w, ?_, ?_⟩
      · simp only [WilkiesDesign.CG.C4a.BasicSA, Set.mem_ofPred_eq]
        refine ⟨?_, fun _ => hw4⟩
        have h1 : (∑ i, (w i - y i) ^ 2 - δ ^ 2) ^ 2 = 0 := by rw [hw2]; ring
        have h2 : ∑ p : Fin k × Fin k, (fderiv ℝ Φ w (Pi.single p.1 1) * (w p.2 - y p.2)
            - fderiv ℝ Φ w (Pi.single p.2 1) * (w p.1 - y p.1)) ^ 2 = 0 := by
          apply Finset.sum_eq_zero
          intro p _
          rw [hw3 p.1 p.2]; ring
        simp only [hF, radEq, h1, h2, add_zero]
      · show dist z w < ε
        rw [dist_comm]; exact hw1
    -- extraction from `F x = 0`
    have h_extract : ∀ x : Fin k → ℝ, F x = 0 →
        (∑ i, (x i - y i) ^ 2 = δ ^ 2) ∧
        (∀ i j : Fin k, fderiv ℝ Φ x (Pi.single i 1) * (x j - y j)
          - fderiv ℝ Φ x (Pi.single j 1) * (x i - y i) = 0) := by
      intro x hx
      have hx' : (∑ i, (x i - y i) ^ 2 - δ ^ 2) ^ 2
          + ∑ p : Fin k × Fin k, (fderiv ℝ Φ x (Pi.single p.1 1) * (x p.2 - y p.2)
              - fderiv ℝ Φ x (Pi.single p.2 1) * (x p.1 - y p.1)) ^ 2 = 0 := by
        simpa only [hF, radEq] using hx
      have hBnn : 0 ≤ ∑ p : Fin k × Fin k, (fderiv ℝ Φ x (Pi.single p.1 1) * (x p.2 - y p.2)
              - fderiv ℝ Φ x (Pi.single p.2 1) * (x p.1 - y p.1)) ^ 2 :=
        Finset.sum_nonneg (fun p _ => sq_nonneg _)
      have hA2 : (∑ i, (x i - y i) ^ 2 - δ ^ 2) ^ 2 = 0 := by
        nlinarith [sq_nonneg (∑ i, (x i - y i) ^ 2 - δ ^ 2), hBnn, hx']
      have hA0 : ∑ i, (x i - y i) ^ 2 - δ ^ 2 = 0 := sq_eq_zero_iff.mp hA2
      have hB0 : ∑ p : Fin k × Fin k, (fderiv ℝ Φ x (Pi.single p.1 1) * (x p.2 - y p.2)
              - fderiv ℝ Φ x (Pi.single p.2 1) * (x p.1 - y p.1)) ^ 2 = 0 := by
        nlinarith [hA2, hBnn, hx']
      refine ⟨by linarith, fun i j => ?_⟩
      have hmem := (Finset.sum_eq_zero_iff_of_nonneg
        (f := fun p : Fin k × Fin k => (fderiv ℝ Φ x (Pi.single p.1 1) * (x p.2 - y p.2)
              - fderiv ℝ Φ x (Pi.single p.2 1) * (x p.1 - y p.1)) ^ 2)
        (fun p _ => sq_nonneg _)).mp hB0 (i, j) (Finset.mem_univ (i, j))
      exact sq_eq_zero_iff.mp hmem
    -- curve selection
    obtain ⟨γ, hγan, hγ0, ε₀, hε₀, hγmem⟩ :=
      (Work.WilE3.Loj.curveSel_full k) 1 F (fun _ : Fin 1 => Φ) z hFan (fun _ => hΦ z) hcl
    have hmemF : ∀ s ∈ Set.Ioo (0 : ℝ) ε₀, F (γ s) = 0 ∧ 0 < Φ (γ s) := by
      intro s hs
      have h := hγmem s hs
      simp only [WilkiesDesign.CG.C4a.BasicSA, Set.mem_ofPred_eq] at h
      exact ⟨h.1, h.2 0⟩
    -- differentiability of `γ` near `0`
    obtain ⟨r, hrpos, hr⟩ : ∃ r : ℝ, 0 < r ∧ ∀ s : ℝ, |s| < r → DifferentiableAt ℝ γ s := by
      have hev : ∀ᶠ s in 𝓝 (0 : ℝ), DifferentiableAt ℝ γ s :=
        hγan.eventually_analyticAt.mono (fun s hs => hs.differentiableAt)
      obtain ⟨r, hrpos, hr⟩ := Metric.eventually_nhds_iff.mp hev
      exact ⟨r, hrpos, fun s hs => hr (by simpa [Real.dist_eq] using hs)⟩
    set hh : ℝ → ℝ := fun s => Φ (γ s) with hhdef
    have hhan : AnalyticAt ℝ hh 0 := by
      rw [hhdef]
      exact (hΦ (γ 0)).comp hγan
    set s₁ : ℝ := min ε₀ r / 2 with hs₁def
    have hs₁pos : 0 < s₁ := by
      rw [hs₁def]; have := lt_min hε₀ hrpos; linarith
    have hs₁ε : s₁ < ε₀ := by rw [hs₁def]; linarith [min_le_left ε₀ r]
    have hs₁r : s₁ < r := by rw [hs₁def]; linarith [min_le_right ε₀ r]
    have hdiffAt : ∀ c ∈ Set.Icc (0 : ℝ) s₁, DifferentiableAt ℝ hh c := by
      intro c hc
      rcases eq_or_lt_of_le hc.1 with hc0 | hc0
      · rw [← hc0]; exact hhan.differentiableAt
      · have hcr : |c| < r := by
          rw [abs_of_pos hc0]; exact lt_of_le_of_lt hc.2 hs₁r
        have hγc : DifferentiableAt ℝ γ c := hr c hcr
        have hΦc : DifferentiableAt ℝ Φ (γ c) := (hΦ (γ c)).differentiableAt
        have h3 : DifferentiableAt ℝ (fun s => Φ (γ s)) c := hΦc.comp c hγc
        rw [hhdef]; exact h3
    have hdiffOnIcc : DifferentiableOn ℝ hh (Set.Icc 0 s₁) := fun c hc =>
      (hdiffAt c hc).differentiableWithinAt
    have hcont : ContinuousOn hh (Set.Icc 0 s₁) := hdiffOnIcc.continuousOn
    have hdiffOn : DifferentiableOn ℝ hh (Set.Ioo (0 : ℝ) s₁) := fun c hc =>
      (hdiffAt c ⟨hc.1.le, hc.2.le⟩).differentiableWithinAt
    -- the key: the derivative of `hh` vanishes on `(0, s₁)`
    have hderiv0 : ∀ c ∈ Set.Ioo (0 : ℝ) s₁, deriv hh c = 0 := by
      intro c hc
      have hcε : c ∈ Set.Ioo (0 : ℝ) ε₀ := ⟨hc.1, lt_trans hc.2 hs₁ε⟩
      have hcr : |c| < r := by
        rw [abs_of_pos hc.1]; exact lt_of_lt_of_le hc.2 (le_of_lt hs₁r)
      have hγc : DifferentiableAt ℝ γ c := hr c hcr
      have hΦc : DifferentiableAt ℝ Φ (γ c) := (hΦ (γ c)).differentiableAt
      obtain ⟨hsphere_c, hmin_c⟩ := h_extract (γ c) (hmemF c hcε).1
      have hev : Filter.Eventually (fun s : ℝ => ∑ i, (γ s i - y i) ^ 2 = δ ^ 2) (nhds c) := by
        filter_upwards [IsOpen.mem_nhds isOpen_Ioo hcε] with s hs
        exact (h_extract (γ s) (hmemF s hs).1).1
      have hcon_dv : ∑ i, (γ c i - y i) * deriv γ c i = 0 :=
        sphere_constraint_deriv_eq_zero hγc hev
      have hv_ne : (γ c - y) ≠ 0 := by
        intro h0
        have hzero : ∑ i, (γ c i - y i) ^ 2 = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          have hi : γ c i - y i = 0 := by
            have := congrFun h0 i
            simpa only [Pi.sub_apply, Pi.zero_apply] using this
          rw [hi]; ring
        have hδ2 : 0 < δ ^ 2 := sq_pos_of_ne_zero hδ
        rw [hzero] at hsphere_c
        linarith
      have hsum0 : ∑ i, (deriv γ c) i * (fun i => fderiv ℝ Φ (γ c) (Pi.single i 1)) i = 0 :=
        sum_dv_mul_grad_eq_zero (v := γ c - y)
          (g := fun i => fderiv ℝ Φ (γ c) (Pi.single i 1)) (dv := deriv γ c)
          hv_ne (fun i j => hmin_c i j) hcon_dv
      have h1 : HasFDerivAt Φ (fderiv ℝ Φ (γ c)) (γ c) := hΦc.hasFDerivAt
      have h2 : HasDerivAt γ (deriv γ c) c := hγc.hasDerivAt
      have h3 : HasDerivAt (Φ ∘ γ) ((fderiv ℝ Φ (γ c)) (deriv γ c)) c :=
        h1.comp_hasDerivAt c h2
      have h4 : HasDerivAt hh ((fderiv ℝ Φ (γ c)) (deriv γ c)) c := by
        rw [hhdef]; exact h3
      rw [h4.deriv, Work.WilE3.Taylor.fderiv_eq_sum_grad]
      simpa [Work.WilE3.Taylor.grad] using hsum0
    -- mean value theorem closes the contradiction
    obtain ⟨c, hcmem, hceq⟩ := exists_deriv_eq_slope hh hs₁pos hcont hdiffOn
    have hzero : (hh s₁ - hh 0) / (s₁ - 0) = 0 := by rw [← hceq, hderiv0 c hcmem]
    have hval : hh s₁ = hh 0 := by
      rw [div_eq_zero_iff] at hzero
      rcases hzero with h | h
      · linarith
      · exact absurd h (by linarith)
    have hh0 : hh 0 = 0 := by show Φ (γ 0) = 0; rw [hγ0]; exact hz
    have hpos₁ : 0 < hh s₁ := by
      show 0 < Φ (γ s₁)
      exact (hmemF s₁ ⟨hs₁pos, hs₁ε⟩).2
    rw [hval, hh0] at hpos₁
    exact lt_irrefl 0 hpos₁

end Work.WilE3.Taylor.CaseII
