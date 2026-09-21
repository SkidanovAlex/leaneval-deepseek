import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.Existence.curve_data_three_defs
import Submission.Work.OddVolterra.Existence.xi_close_of_small
import Submission.Work.OddVolterra.Existence.theta_lipschitz_state_ball
import Submission.Work.OddVolterra.Existence.base_volterra
import Submission.Work.OddVolterra.Existence.godd_injective_modulus_state_ball_compat
import Submission.Work.OddVolterra.Existence.krad_pos_state_region
import Submission.Work.OddVolterra.Window.volterra_unique
import Submission.Work.OddVolterra.Window.manifest_eq
import Submission.Work.OddVolterra.WinData.thetaM_close_box
import Submission.Work.Anchor.Xi_close
import Submission.Work.OddExistence.Estimates.godd_close

/-!
# The state-closeness core of the odd transition window

For any smooth state `Z` solving the paper's system `(hah44)` on `(1/4,1)`, agreeing with the ball's
state above `9/10` and staying within `1/2` of it on `[7/10,1]`, the state stays within `K ε` of the
ball's state on the whole transition window `[7/10, 9/10]`, where `ε` is the `C^{n+3}`-size of the
perturbation `h`.

The proof is a Gronwall estimate for the state difference.  Its three inputs are the linear-in-`ε`
closeness of the data `Godd`, `Θ`, `Ξ` to their unperturbed values (available from
`Work.OddExistence.Estimates.godd_close`, `Work.Anchor.Xi_close` and the manifest closeness
`WinData.thetaM_close_box`, transported to the paper's datum by `thetaM_eq_theta_ball`), together
with the *unperturbed* injectivity modulus of `Godd` and the *unperturbed* Lipschitz constant of
`Θ` in the state (`theta_lipschitz_state_ball` and `godd_injective_modulus_state_ball_compat` at
`h = 0`).
-/

namespace Work.OddVolterra.Existence

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

noncomputable section

/-- The manifest representative of the `Θ`-datum agrees with the paper's on the transition
strip: for `7/10 ≤ s < σ ≤ 1` and states in the ball of radius `1/2` around `baseState σ`. -/
lemma thetaM_eq_theta_ball (n : ℕ) (hn : 1 ≤ n) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau))
    (hsmall : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100)
    {s σ : ℝ} (hs : 7 / 10 ≤ s) (hsσ : s < σ) (hσ : σ ≤ 1)
    {z : Work.OddVolterra.St} (hz : z ∈ Metric.closedBall (Work.OddVolterra.baseState σ) (1 / 2)) :
    Work.OddVolterra.KernelExt.ThetaM n h s σ z = Work.OddVolterra.Theta n h s σ z := by
  have hsmall1 : ∀ k : ℕ, k ≤ 1 → ∀ s : ℝ, |iteratedDeriv k h s| ≤ 1 / 100 :=
    fun k hk s => hsmall k (le_trans hk (by norm_num)) s
  have hσ25 : (7 / 10 : ℝ) ≤ σ := le_trans hs hsσ.le
  obtain ⟨hz0, hz1, _⟩ :=
    state_ball_box (b := 7 / 10) (by norm_num) (by norm_num) σ ⟨hσ25, hσ⟩ z hz
  refine Work.OddVolterra.Window.ThetaM_eq_Theta n hn hh (δ := (1 / 2 : ℝ)) hsσ (by norm_num) z ?_ ?_
  · intro a ha
    exact krad_pos_state_region (b := (1 / 5 : ℝ)) (a := a) (σ := σ) (t := -(z 0))
      hsupp hsmall1 (by norm_num) (by linarith [ha.1, hs]) ha.2 hσ
      (by rw [abs_neg, abs_of_nonneg (by linarith [hz0])]; exact hz0)
  · intro a ha
    exact krad_pos_state_region (b := (1 / 5 : ℝ)) (a := a) (σ := σ) (t := z 1)
      hsupp hsmall1 (by norm_num) (by linarith [ha.1, hs]) ha.2 hσ
      (by rw [abs_of_nonneg (by linarith [hz1])]; exact hz1)

lemma continuous_baseState' : Continuous (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) := by
  have hx : Continuous (fun s : ℝ => Commons.Geometry.Ulam.profileX s) :=
    contDiff_profileX.continuous
  have hd : Continuous (fun s : ℝ => deriv Commons.Geometry.Ulam.profileX s) :=
    contDiff_profileX.continuous_deriv (WithTop.coe_le_coe.mpr le_top)
  rw [show (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St) = fun s : ℝ =>
      ![Commons.Geometry.Ulam.profileX s, Commons.Geometry.Ulam.profileX s,
        deriv Commons.Geometry.Ulam.profileX s, deriv Commons.Geometry.Ulam.profileX s]
      from rfl]
  exact continuous_pi (fun i => by
    fin_cases i <;>
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_fin_one] <;>
      assumption)

open Real MeasureTheory Set Filter
open scoped Topology ContDiff Interval
lemma gronwall_window {c₀ L₀ ρ : ℝ} (hc₀ : 0 < c₀) (hL₀ : 0 ≤ L₀) (hρ : 0 ≤ ρ)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc (7 / 10 : ℝ) (9 / 10 : ℝ)))
    (hfnn : ∀ s ∈ Set.Icc (7 / 10 : ℝ) (9 / 10 : ℝ), 0 ≤ f s)
    (hineq : ∀ s ∈ Set.Icc (7 / 10 : ℝ) (9 / 10 : ℝ),
      c₀ * f s ≤ L₀ * (∫ σ in s..(9 / 10 : ℝ), f σ) + ρ) :
    ∀ s ∈ Set.Icc (7 / 10 : ℝ) (9 / 10 : ℝ),
      f s ≤ (ρ / c₀) * (1 + (L₀ / c₀) * Real.exp (L₀ / c₀ + 1)) := by
  set H : ℝ → ℝ := fun σ => f (max (7 / 10 : ℝ) (min σ (9 / 10 : ℝ))) with hH
  have hHcont : Continuous H := by
    have hclamp : Continuous fun σ : ℝ => max (7 / 10 : ℝ) (min σ (9 / 10 : ℝ)) := by fun_prop
    have hmem : ∀ σ : ℝ, max (7 / 10 : ℝ) (min σ (9 / 10 : ℝ)) ∈ Set.Icc (7 / 10 : ℝ) (9 / 10) :=
      fun σ => ⟨le_max_left _ _, max_le (by norm_num) (min_le_right _ _)⟩
    exact hf.comp_continuous hclamp hmem
  set G : ℝ → ℝ := fun s => ∫ σ in s..(9 / 10 : ℝ), f σ with hG
  have hGapply : ∀ y : ℝ, G y = ∫ σ in y..(9 / 10 : ℝ), f σ := fun y => by simp [hG]
  have hGeq : ∀ s ∈ Set.Icc (7 / 10 : ℝ) (9 / 10 : ℝ), G s = ∫ σ in s..(9 / 10 : ℝ), H σ := by
    intro s hs
    refine intervalIntegral.integral_congr ?_
    intro σ hσ
    rw [Set.uIcc_of_le (by linarith [hs.2])] at hσ
    show f σ = H σ
    rw [hH]
    simp only
    rw [min_eq_left hσ.2, max_eq_right (le_trans hs.1 hσ.1)]
  have hGcont : ContinuousOn G (Set.Icc (7 / 10 : ℝ) (9 / 10 : ℝ)) := by
    have hprim : Continuous fun u : ℝ => ∫ σ in (9 / 10 : ℝ)..u, H σ :=
      intervalIntegral.continuous_primitive (fun a b => hHcont.intervalIntegrable a b) (9 / 10)
    refine (hprim.neg.continuousOn).congr ?_
    intro s hs
    rw [hGeq s hs, intervalIntegral.integral_symm]
    rfl
  have hGderiv : ∀ τ ∈ Set.Ioo (7 / 10 : ℝ) (9 / 10), HasDerivAt G (-(f τ)) τ := by
    intro τ hτ
    have hcontτ : ContinuousAt f τ := hf.continuousAt (Icc_mem_nhds hτ.1 hτ.2)
    have hmeasτ : StronglyMeasurableAtFilter f (𝓝 τ) volume :=
      ContinuousAt.stronglyMeasurableAtFilter (s := Set.Ioo (7 / 10 : ℝ) (9 / 10)) isOpen_Ioo
        (fun x hx => hf.continuousAt (Icc_mem_nhds hx.1 hx.2)) τ hτ
    have hInt : IntervalIntegrable f volume τ (9 / 10 : ℝ) := by
      have hc : ContinuousOn f (Set.uIcc τ (9 / 10 : ℝ)) := by
        rw [Set.uIcc_of_le hτ.2.le]
        exact hf.mono (Set.Icc_subset_Icc hτ.1.le le_rfl)
      exact hc.intervalIntegrable
    have h := intervalIntegral.integral_hasDerivAt_left hInt hmeasτ hcontτ
    simpa [hG] using h
  have hGnonneg : ∀ s ∈ Set.Icc (7 / 10 : ℝ) (9 / 10), 0 ≤ G s := by
    intro s hs
    rw [hGapply s]
    exact intervalIntegral.integral_nonneg hs.2 (fun x hx => hfnn x ⟨le_trans hs.1 hx.1, hx.2⟩)
  have hGend : G (9 / 10) = 0 := by rw [hG]; simp
  set lam : ℝ := L₀ / c₀ + 1 with hlam
  have hlampos : 0 < lam := by rw [hlam]; have : 0 ≤ L₀ / c₀ := div_nonneg hL₀ hc₀.le; linarith
  have hlam1 : 1 ≤ lam := by rw [hlam]; have : 0 ≤ L₀ / c₀ := div_nonneg hL₀ hc₀.le; linarith
  have hβ0 : 0 ≤ ρ / c₀ := div_nonneg hρ hc₀.le
  have hβlam0 : 0 ≤ (ρ / c₀) / lam := div_nonneg hβ0 hlampos.le
  intro s hs
  have hmonoOn : MonotoneOn (fun τ : ℝ => Real.exp (lam * τ) * (G τ + (ρ / c₀) / lam))
      (Set.Icc s (9 / 10)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc s (9 / 10)) ?_ ?_ ?_
    · exact ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn).mul
        ((hGcont.mono (Set.Icc_subset_Icc hs.1 le_rfl)).add continuousOn_const)
    · intro x hx
      rw [interior_Icc] at hx
      have hx' : x ∈ Set.Ioo (7 / 10 : ℝ) (9 / 10) := ⟨lt_of_le_of_lt hs.1 hx.1, hx.2⟩
      have h1 : HasDerivAt (fun τ : ℝ => Real.exp (lam * τ)) (Real.exp (lam * x) * lam) x := by
        simpa using ((hasDerivAt_id x).const_mul lam).exp
      have h3 : HasDerivAt (fun τ : ℝ => G τ + (ρ / c₀) / lam) (-(f x)) x := by
        simpa using (hGderiv x hx').add_const ((ρ / c₀) / lam)
      exact (h1.mul h3).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      have hx' : x ∈ Set.Ioo (7 / 10 : ℝ) (9 / 10) := ⟨lt_of_le_of_lt hs.1 hx.1, hx.2⟩
      have hxIcc : x ∈ Set.Icc (7 / 10 : ℝ) (9 / 10) := ⟨hx'.1.le, hx'.2.le⟩
      have hGx : 0 ≤ G x := hGnonneg x hxIcc
      have hfx : f x ≤ (L₀ / c₀) * G x + ρ / c₀ := by
        rw [hGapply x, ← show (L₀ * (∫ σ in x..(9 / 10 : ℝ), f σ) + ρ) / c₀
            = (L₀ / c₀) * (∫ σ in x..(9 / 10 : ℝ), f σ) + ρ / c₀ from by ring]
        rw [le_div_iff₀ hc₀]
        linarith [hineq x hxIcc]
      have h1 : HasDerivAt (fun τ : ℝ => Real.exp (lam * τ)) (Real.exp (lam * x) * lam) x := by
        simpa using ((hasDerivAt_id x).const_mul lam).exp
      have h3 : HasDerivAt (fun τ : ℝ => G τ + (ρ / c₀) / lam) (-(f x)) x := by
        simpa using (hGderiv x hx').add_const ((ρ / c₀) / lam)
      have hderiv : deriv (fun τ : ℝ => Real.exp (lam * τ) * (G τ + (ρ / c₀) / lam)) x
          = Real.exp (lam * x) * (lam * (G x + (ρ / c₀) / lam) + (-(f x))) := by
        have h4 := h1.mul h3
        have h4d : deriv ((fun τ : ℝ => Real.exp (lam * τ)) * (fun τ : ℝ => G τ + (ρ / c₀) / lam)) x
            = Real.exp (lam * x) * lam * (G x + (ρ / c₀) / lam) + Real.exp (lam * x) * (-(f x)) :=
          h4.deriv
        rw [show deriv (fun τ : ℝ => Real.exp (lam * τ) * (G τ + (ρ / c₀) / lam)) x
              = deriv ((fun τ : ℝ => Real.exp (lam * τ)) * (fun τ : ℝ => G τ + (ρ / c₀) / lam)) x
              from rfl, h4d]
        ring
      rw [hderiv]
      have hkey : lam * (G x + (ρ / c₀) / lam) = (L₀ / c₀) * G x + G x + ρ / c₀ := by
        have h1' : lam * (G x + (ρ / c₀) / lam) = lam * G x + ρ / c₀ := by
          rw [mul_add, mul_div_cancel₀]
          exact hlampos.ne'
        rw [h1', hlam]; ring
      have hgoal : 0 ≤ lam * (G x + (ρ / c₀) / lam) + (-(f x)) := by
        rw [hkey]; linarith [hfx, hGx]
      exact mul_nonneg (Real.exp_pos _).le hgoal
  have hmono := hmonoOn ⟨le_rfl, hs.2⟩ ⟨hs.2, le_rfl⟩ hs.2
  simp only [hGend, zero_add] at hmono
  have hexppos : 0 < Real.exp (lam * s) := Real.exp_pos _
  have hle1 : G s + (ρ / c₀) / lam ≤ Real.exp (lam * ((9 : ℝ) / 10 - s)) * ((ρ / c₀) / lam) := by
    have hexp : Real.exp (lam * ((9:ℝ)/10 - s)) * Real.exp (lam * s) = Real.exp (lam * ((9:ℝ)/10)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h2 : Real.exp (lam * ((9:ℝ)/10)) * ((ρ/c₀)/lam) / Real.exp (lam * s)
        = Real.exp (lam * ((9:ℝ)/10 - s)) * ((ρ/c₀)/lam) := by
      rw [div_eq_iff hexppos.ne']
      calc Real.exp (lam * ((9:ℝ)/10)) * ((ρ/c₀)/lam)
          = (Real.exp (lam * ((9:ℝ)/10 - s)) * Real.exp (lam * s)) * ((ρ/c₀)/lam) := by
            rw [hexp]
        _ = Real.exp (lam * ((9:ℝ)/10 - s)) * ((ρ/c₀)/lam) * Real.exp (lam * s) := by ring
    calc G s + (ρ / c₀) / lam
        ≤ Real.exp (lam * ((9:ℝ)/10)) * ((ρ / c₀) / lam) / Real.exp (lam * s) := by
          rw [le_div_iff₀ hexppos]; linarith [hmono]
      _ = Real.exp (lam * ((9:ℝ)/10 - s)) * ((ρ / c₀) / lam) := h2
  have hexp_le : Real.exp (lam * ((9:ℝ)/10 - s)) ≤ Real.exp lam := by
    refine Real.exp_le_exp.mpr ?_
    have h1 : (9:ℝ)/10 - s ≤ 1 := by linarith [hs.1]
    nlinarith [hlampos.le, h1]
  have hGs : G s ≤ Real.exp lam * ((ρ / c₀) / lam) := by
    have h1 : Real.exp (lam * ((9:ℝ)/10 - s)) * ((ρ / c₀) / lam)
        ≤ Real.exp lam * ((ρ / c₀) / lam) :=
      mul_le_mul_of_nonneg_right hexp_le hβlam0
    linarith [hle1, h1, hβlam0]
  have hfx : f s ≤ (L₀ * G s + ρ) / c₀ := by
    rw [le_div_iff₀ hc₀]; linarith [hineq s hs]
  have h7 : (L₀ / c₀) * G s ≤ (ρ / c₀) * ((L₀ / c₀) * Real.exp lam) := by
    have h4 : (L₀ / c₀) * (Real.exp lam * ((ρ / c₀) / lam))
        = (ρ / c₀) * ((L₀ / c₀) * (Real.exp lam / lam)) := by ring
    have h5 : Real.exp lam / lam ≤ Real.exp lam := by
      rw [div_le_iff₀ hlampos]; nlinarith [Real.exp_pos lam, hlam1]
    calc (L₀ / c₀) * G s ≤ (L₀ / c₀) * (Real.exp lam * ((ρ / c₀) / lam)) :=
          mul_le_mul_of_nonneg_left hGs (div_nonneg hL₀ hc₀.le)
      _ = (ρ / c₀) * ((L₀ / c₀) * (Real.exp lam / lam)) := h4
      _ ≤ (ρ / c₀) * ((L₀ / c₀) * Real.exp lam) := by
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hρ hc₀.le)
          exact mul_le_mul_of_nonneg_left h5 (div_nonneg hL₀ hc₀.le)
  have hfinal : (L₀ * G s + ρ) / c₀ ≤ (ρ / c₀) * (1 + (L₀ / c₀) * Real.exp lam) := by
    have h6 : (L₀ * G s + ρ) / c₀ = (L₀ / c₀) * G s + ρ / c₀ := by ring
    rw [h6]
    have e1 : (ρ / c₀) * (1 + (L₀ / c₀) * Real.exp lam)
        = ρ / c₀ + (ρ / c₀) * ((L₀ / c₀) * Real.exp lam) := by ring
    rw [e1]
    linarith [h7]
  have hlast := le_trans hfx hfinal
  rwa [hlam] at hlast
theorem window_state_close_core (n : ℕ) (hn : 1 ≤ n) :
    ∃ K ε₁ : ℝ, 0 < K ∧ 0 < ε₁ ∧ ε₁ ≤ 1 / 100 ∧
      ∀ (h : ℝ → ℝ) (Z : ℝ → Work.OddVolterra.St) (ε : ℝ), 0 < ε → ε ≤ ε₁ →
        Work.OddVolterra.Existence.IsSmallFlatBumpThree n ε h →
        ContDiffOn ℝ (⊤ : ℕ∞) Z (Set.Ioi (1 / 4 : ℝ)) →
        (∀ s ∈ Set.Ioo (1 / 4 : ℝ) 1,
          Work.OddVolterra.Godd n h s (Z s) =
            (∫ σ in s..(1 : ℝ), Work.OddVolterra.Theta n h s σ (Z σ)) +
              Work.OddVolterra.Xi n h s) →
        (∀ s : ℝ, 9 / 10 ≤ s → Z s = Work.OddVolterra.baseState s) →
        (∀ s ∈ Set.Icc (7 / 10 : ℝ) 1,
          dist (Z s) (Work.OddVolterra.baseState s) ≤ 1 / 2) →
        ∀ s ∈ Set.Icc (7 / 10 : ℝ) (9 / 10 : ℝ),
          dist (Z s) (Work.OddVolterra.baseState s) ≤ K * ε := by
  have hsupp0 : Function.support (0 : ℝ → ℝ) ⊆
      Set.Icc (1 - 2 * Work.OddVolterra.tau) (1 - Work.OddVolterra.tau) := by
    intro x hx; rw [Function.mem_support] at hx; exact absurd rfl hx
  have hsmall0 : ∀ k : ℕ, k ≤ 2 → ∀ s : ℝ, |iteratedDeriv k (0 : ℝ → ℝ) s| ≤ 1 / 100 := by
    intro k hk s
    rw [show (0 : ℝ → ℝ) = fun _ : ℝ => (0 : ℝ) from rfl, iteratedDeriv_const]
    split <;> simp
  obtain ⟨L₀, hL₀nn, C₀, hC₀pos, hL₀lip, hC₀bd, hC₀cont⟩ :=
    theta_lipschitz_state_ball n hn (h := 0) contDiff_const hsupp0 hsmall0
      (b := (7 / 10 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨c₀, hc₀pos, hc₀inj⟩ :=
    godd_injective_modulus_state_ball_compat n hn (h := 0) contDiff_const hsupp0 hsmall0
      (b := (7 / 10 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨C_G, hC_Gpos, hGclose⟩ :=
    Work.OddExistence.Estimates.godd_close n hn (a := (7 / 10 : ℝ)) (b := 1) (by norm_num) (by norm_num) (by norm_num)
      (ρ := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  obtain ⟨C_X, hC_Xpos, hXclose⟩ := Work.Anchor.Xi_close n hn
  obtain ⟨C_T, hC_Tpos, hThMclose⟩ :=
    Work.OddVolterra.WinData.thetaM_close_box n hn (a := (7 / 10 : ℝ)) (b := 1)
      (ρ := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hThMclose' : ∀ (hh : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) hh →
      Function.support hh ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
        (1 - Work.OddVolterra.tau) →
      ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 100 →
      (∀ k : ℕ, k ≤ n + 2 → ∀ s : ℝ, |iteratedDeriv k hh s| ≤ δ) →
      ∀ s ∈ Set.Icc (7 / 10 : ℝ) 1, ∀ σ ∈ Set.Icc (7 / 10 : ℝ) 1,
        ∀ z ∈ Metric.closedBall (Work.OddVolterra.baseState σ) (1 / 2),
        ‖Work.OddVolterra.KernelExt.ThetaM n hh s σ z -
          Work.OddVolterra.KernelExt.ThetaM n 0 s σ z‖ ≤ C_T * δ := hThMclose
  set ResB : ℝ := 3 * C_T + C_X + 3 * C_G + 1 with hResB
  have hResBpos : 0 < ResB := by rw [hResB]; linarith
  set Res : ℝ := ResB + 2 * C_T + 2 * C_G with hRes
  have hRespos : 0 < Res := by rw [hRes]; linarith
  set K : ℝ := (Res / c₀) * (1 + (L₀ / c₀) * Real.exp (L₀ / c₀ + 1)) + 1 with hK
  have hKpos : 0 < K := by
    rw [hK]
    have h1 : (0 : ℝ) < Res / c₀ := div_pos hRespos hc₀pos
    have h2 : 0 ≤ L₀ / c₀ := div_nonneg hL₀nn hc₀pos.le
    have h3 : 0 < 1 + (L₀ / c₀) * Real.exp (L₀ / c₀ + 1) := by
      have := Real.exp_pos (L₀ / c₀ + 1); nlinarith
    nlinarith
  refine ⟨K, 1 / 100, hKpos, by norm_num, le_rfl, ?_⟩
  intro h Z ε hεpos hε1 hb hZsm hZsys hZtail hZball
  have hh : ContDiff ℝ (⊤ : ℕ∞) h := hb.contDiff
  have hsupp : Function.support h ⊆ Set.Icc (1 - 2 * Work.OddVolterra.tau)
      (1 - Work.OddVolterra.tau) :=
    fun x hx => ⟨le_of_lt (hb.support_subset hx).1, le_of_lt (hb.support_subset hx).2⟩
  have hjet : ∀ k : ℕ, k ≤ n + 2 → ∀ t : ℝ, |iteratedDeriv k h t| ≤ ε :=
    fun k hk t => hb.deriv_bound (by omega) t
  have hsmall2 : ∀ k : ℕ, k ≤ 2 → ∀ t : ℝ, |iteratedDeriv k h t| ≤ 1 / 100 := by
    intro k hk t
    have h1 := hb.deriv_bound (k := k) (by omega) t
    linarith
  have hε100 : ε ≤ 1 / 100 := le_trans hε1 (by norm_num)
  have hε0 : 0 ≤ ε := hεpos.le
  have hZdist : ∀ σ ∈ Set.Icc (7 / 10 : ℝ) 1, ‖Z σ - Work.OddVolterra.baseState σ‖ ≤ 1 / 2 := by
    intro σ hσ
    rw [← dist_eq_norm]
    exact hZball σ hσ
  have hZcont : ContinuousOn Z (Set.Icc (7 / 10 : ℝ) 1) :=
    hZsm.continuousOn.mono (fun x hx => by simp only [Set.mem_Ioi]; linarith [hx.1])
  have hbasecont : ContinuousOn (Work.OddVolterra.baseState : ℝ → Work.OddVolterra.St)
      (Set.Icc (7 / 10 : ℝ) 1) := continuous_baseState'.continuousOn
  have hZfcont : ContinuousOn (fun σ => ‖Z σ - Work.OddVolterra.baseState σ‖)
      (Set.Icc (7 / 10 : ℝ) (9 / 10 : ℝ)) :=
    ((hZcont.sub hbasecont).mono (Set.Icc_subset_Icc le_rfl (by norm_num))).norm
  obtain ⟨Lh, hLhnn, Ch, hChpos, hΘlip, hΘbd, hΘcont⟩ :=
    theta_lipschitz_state_ball n hn hh hsupp hsmall2 (b := (7 / 10 : ℝ)) (by norm_num) (by norm_num)
  have hinner_all : ∀ t ∈ Set.Icc (7 / 10 : ℝ) (9 / 10 : ℝ),
      c₀ * ‖Z t - Work.OddVolterra.baseState t‖
        ≤ L₀ * (∫ σ in t..(9 / 10 : ℝ), ‖Z σ - Work.OddVolterra.baseState σ‖) + Res * ε := by
    intro t ht
    have ht1 : (7 / 10 : ℝ) ≤ t := ht.1
    have ht2 : t ≤ (9 / 10 : ℝ) := ht.2
    have hZii : IntervalIntegrable (fun σ => Work.OddVolterra.Theta n h t σ (Z σ)) volume t 1 :=
      Work.OddVolterra.Window.intervalIntegrable_Theta_integrand_win (n := n) (h := h)
        (b := (7 / 10 : ℝ)) (C := Ch) (s₁ := 1) hΘbd hΘcont ⟨ht1, by linarith⟩ (by linarith) le_rfl
        (hZcont.mono (Set.Icc_subset_Icc_left ht1))
        (fun σ hσ => hZdist σ ⟨le_trans ht1 hσ.1, hσ.2⟩)
    have hBii : IntervalIntegrable
        (fun σ => Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ)) volume t 1 :=
      Work.OddVolterra.Window.intervalIntegrable_Theta_integrand_win (n := n) (h := h)
        (b := (7 / 10 : ℝ)) (C := Ch) (s₁ := 1) hΘbd hΘcont ⟨ht1, by linarith⟩ (by linarith) le_rfl
        (hbasecont.mono (fun x hx => ⟨le_trans ht1 hx.1, hx.2⟩))
        (fun σ _ => by rw [sub_self, norm_zero]; norm_num)
    have hB0ii : IntervalIntegrable
        (fun σ => Work.OddVolterra.Theta n 0 t σ (Work.OddVolterra.baseState σ)) volume t 1 :=
      Work.OddVolterra.Window.intervalIntegrable_Theta_integrand_win (n := n) (h := 0)
        (b := (7 / 10 : ℝ)) (C := C₀) (s₁ := 1) hC₀bd hC₀cont ⟨ht1, by linarith⟩ (by linarith) le_rfl
        (hbasecont.mono (fun x hx => ⟨le_trans ht1 hx.1, hx.2⟩))
        (fun σ _ => by rw [sub_self, norm_zero]; norm_num)
    have hEqZ : Work.OddVolterra.Godd n h t (Z t) =
        (∫ σ in t..(1 : ℝ), Work.OddVolterra.Theta n h t σ (Z σ)) + Work.OddVolterra.Xi n h t :=
      hZsys t ⟨by linarith, by linarith⟩
    have hEqB : Work.OddVolterra.Godd n 0 t (Work.OddVolterra.baseState t) =
        (∫ σ in t..(1 : ℝ), Work.OddVolterra.Theta n 0 t σ (Work.OddVolterra.baseState σ)) +
          Work.OddVolterra.Xi n 0 t :=
      base_volterra n hn t ⟨by linarith, by linarith⟩
    have htailzero : (∫ σ in (9 / 10 : ℝ)..1,
        (Work.OddVolterra.Theta n h t σ (Z σ) -
          Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ))) = 0 := by
      have h : ∀ σ ∈ Set.uIcc (9 / 10 : ℝ) 1,
          (Work.OddVolterra.Theta n h t σ (Z σ) -
            Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ)) = 0 := by
        intro σ hσ
        rw [Set.uIcc_of_le (by norm_num : (9 / 10 : ℝ) ≤ 1)] at hσ
        rw [hZtail σ hσ.1, sub_self]
      rw [intervalIntegral.integral_congr h, intervalIntegral.integral_zero]
    have hsplit1 : (∫ σ in t..1, (Work.OddVolterra.Theta n h t σ (Z σ) -
          Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ)))
        = (∫ σ in t..1, Work.OddVolterra.Theta n h t σ (Z σ))
          - (∫ σ in t..1, Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ)) :=
      intervalIntegral.integral_sub hZii hBii
    have hsplit2 : (∫ σ in t..1, (Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ) -
          Work.OddVolterra.Theta n 0 t σ (Work.OddVolterra.baseState σ)))
        = (∫ σ in t..1, Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ))
          - (∫ σ in t..1, Work.OddVolterra.Theta n 0 t σ (Work.OddVolterra.baseState σ)) :=
      intervalIntegral.integral_sub hBii hB0ii
    have hsplitInt : (∫ σ in t..1, (Work.OddVolterra.Theta n h t σ (Z σ) -
          Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ)))
        = ∫ σ in t..(9 / 10 : ℝ), (Work.OddVolterra.Theta n h t σ (Z σ) -
          Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ)) := by
      have h1 : IntervalIntegrable (fun σ => Work.OddVolterra.Theta n h t σ (Z σ) -
          Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ)) volume t (9 / 10) :=
        (hZii.sub hBii).mono_set (by
          intro x hx
          rw [Set.uIcc_of_le ht2] at hx
          rw [Set.uIcc_of_le (by linarith : t ≤ 1)]
          exact ⟨hx.1, le_trans hx.2 (by norm_num)⟩)
      have h2 : IntervalIntegrable (fun σ => Work.OddVolterra.Theta n h t σ (Z σ) -
          Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ)) volume (9 / 10) 1 :=
        (hZii.sub hBii).mono_set (by
          intro x hx
          rw [Set.uIcc_of_le (by norm_num : (9 / 10 : ℝ) ≤ 1)] at hx
          rw [Set.uIcc_of_le (by linarith : t ≤ 1)]
          exact ⟨le_trans ht2 hx.1, hx.2⟩)
      rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, htailzero, add_zero]
    have hident : Work.OddVolterra.Godd n h t (Z t) -
          Work.OddVolterra.Godd n h t (Work.OddVolterra.baseState t)
        = (∫ σ in t..(9 / 10 : ℝ), (Work.OddVolterra.Theta n h t σ (Z σ) -
            Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ)))
          + ((∫ σ in t..1, (Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ) -
              Work.OddVolterra.Theta n 0 t σ (Work.OddVolterra.baseState σ)))
            + (Work.OddVolterra.Xi n h t - Work.OddVolterra.Xi n 0 t))
          - (Work.OddVolterra.Godd n h t (Work.OddVolterra.baseState t) -
              Work.OddVolterra.Godd n 0 t (Work.OddVolterra.baseState t)) := by
      rw [hEqZ, hEqB, ← hsplitInt, hsplit1, hsplit2]
      abel
    have hTheta_close_pt : ∀ {σ : ℝ}, t < σ → σ ≤ 1 → ∀ {z : Work.OddVolterra.St},
        z ∈ Metric.closedBall (Work.OddVolterra.baseState σ) (1 / 2) →
        ‖Work.OddVolterra.Theta n h t σ z - Work.OddVolterra.Theta n 0 t σ z‖ ≤ C_T * ε := by
      intro σ htσ hσ1 z hz
      have hσIcc : σ ∈ Set.Icc (7 / 10 : ℝ) 1 := ⟨le_trans ht1 htσ.le, hσ1⟩
      have htIcc : t ∈ Set.Icc (7 / 10 : ℝ) 1 := ⟨ht1, by linarith⟩
      rw [← thetaM_eq_theta_ball n hn hh hsupp hsmall2 ht1 htσ hσ1 hz,
        ← thetaM_eq_theta_ball n hn (h := 0) contDiff_const hsupp0 hsmall0 ht1 htσ hσ1 hz]
      exact hThMclose' h hh hsupp ε hεpos hε100 hjet t htIcc σ hσIcc z hz
    have hXi_pt : ‖Work.OddVolterra.Xi n h t - Work.OddVolterra.Xi n 0 t‖ ≤ C_X * ε :=
      hXclose h hh hsupp ε hεpos hε100 hjet t ⟨by linarith [ht1], by linarith [ht2]⟩
    have hGd_pt : ‖Work.OddVolterra.Godd n h t (Work.OddVolterra.baseState t) -
        Work.OddVolterra.Godd n 0 t (Work.OddVolterra.baseState t)‖ ≤ C_G * ε :=
      hGclose h hh ε hεpos hε100 hjet t ⟨ht1, by linarith [ht2]⟩
        (Work.OddVolterra.baseState t) (by rw [sub_self, norm_zero]; norm_num)
    have hIntTheta : ‖(∫ σ in t..(9 / 10 : ℝ), (Work.OddVolterra.Theta n h t σ (Z σ) -
          Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ)))‖
        ≤ 2 * (C_T * ε) + L₀ * (∫ σ in t..(9 / 10 : ℝ), ‖Z σ - Work.OddVolterra.baseState σ‖) := by
      have hI9 : IntervalIntegrable (fun σ => Work.OddVolterra.Theta n h t σ (Z σ)) volume t (9 / 10) :=
        hZii.mono_set (by
          intro x hx
          rw [Set.uIcc_of_le ht2] at hx
          rw [Set.uIcc_of_le (by linarith : t ≤ 1)]
          exact ⟨hx.1, le_trans hx.2 (by norm_num)⟩)
      have hB9 : IntervalIntegrable (fun σ => Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ)) volume t (9 / 10) :=
        hBii.mono_set (by
          intro x hx
          rw [Set.uIcc_of_le ht2] at hx
          rw [Set.uIcc_of_le (by linarith : t ≤ 1)]
          exact ⟨hx.1, le_trans hx.2 (by norm_num)⟩)
      have hfint : IntervalIntegrable (fun σ => ‖Z σ - Work.OddVolterra.baseState σ‖) volume t (9 / 10) :=
        (((hZcont.sub hbasecont).mono (by
          intro x hx
          rw [Set.uIcc_of_le ht2] at hx
          exact ⟨le_trans ht1 hx.1, le_trans hx.2 (by norm_num)⟩)).norm).intervalIntegrable
      have hIg : IntervalIntegrable
          (fun σ => 2 * (C_T * ε) + L₀ * ‖Z σ - Work.OddVolterra.baseState σ‖) volume t (9 / 10) :=
        intervalIntegrable_const.add (hfint.const_mul L₀)
      have hptZ : ∀ σ ∈ Set.Ioc t (9 / 10 : ℝ),
          ‖Work.OddVolterra.Theta n h t σ (Z σ) - Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ)‖
            ≤ 2 * (C_T * ε) + L₀ * ‖Z σ - Work.OddVolterra.baseState σ‖ := by
        intro σ hσ
        have hσ1 : σ ≤ 1 := by linarith [hσ.2]
        have hzZ : Z σ ∈ Metric.closedBall (Work.OddVolterra.baseState σ) (1 / 2) := by
          rw [Metric.mem_closedBall, dist_eq_norm]
          exact hZdist σ ⟨le_trans ht1 hσ.1.le, hσ1⟩
        have hzb : Work.OddVolterra.baseState σ ∈ Metric.closedBall (Work.OddVolterra.baseState σ) (1 / 2) := by
          rw [Metric.mem_closedBall]; simp
        have ha : ‖Work.OddVolterra.Theta n h t σ (Z σ) - Work.OddVolterra.Theta n 0 t σ (Z σ)‖ ≤ C_T * ε :=
          hTheta_close_pt hσ.1 hσ1 hzZ
        have hb' : ‖Work.OddVolterra.Theta n 0 t σ (Z σ) - Work.OddVolterra.Theta n 0 t σ (Work.OddVolterra.baseState σ)‖
            ≤ L₀ * ‖Z σ - Work.OddVolterra.baseState σ‖ :=
          hL₀lip t ⟨ht1, by linarith⟩ σ ⟨hσ.1, by linarith [hσ.2]⟩ (Z σ) hzZ
            (Work.OddVolterra.baseState σ) hzb
        have hc : ‖Work.OddVolterra.Theta n 0 t σ (Work.OddVolterra.baseState σ) -
            Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ)‖ ≤ C_T * ε := by
          rw [← norm_neg, neg_sub]
          exact hTheta_close_pt hσ.1 hσ1 hzb
        have he : Work.OddVolterra.Theta n h t σ (Z σ) - Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ)
            = (Work.OddVolterra.Theta n h t σ (Z σ) - Work.OddVolterra.Theta n 0 t σ (Z σ))
              + ((Work.OddVolterra.Theta n 0 t σ (Z σ) - Work.OddVolterra.Theta n 0 t σ (Work.OddVolterra.baseState σ))
                + (Work.OddVolterra.Theta n 0 t σ (Work.OddVolterra.baseState σ) -
                    Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ))) := by
          abel
        rw [he]
        have h4 := norm_add_le (Work.OddVolterra.Theta n 0 t σ (Z σ) - Work.OddVolterra.Theta n 0 t σ (Work.OddVolterra.baseState σ))
          (Work.OddVolterra.Theta n 0 t σ (Work.OddVolterra.baseState σ) -
            Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ))
        refine le_trans (norm_add_le _ _) ?_
        linarith
      calc ‖(∫ σ in t..(9 / 10 : ℝ), (Work.OddVolterra.Theta n h t σ (Z σ) -
              Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ)))‖
          ≤ ∫ σ in t..(9 / 10 : ℝ), (2 * (C_T * ε) + L₀ * ‖Z σ - Work.OddVolterra.baseState σ‖) :=
            intervalIntegral.norm_integral_le_of_norm_le ht2
              (Filter.Eventually.of_forall (fun σ hσ => hptZ σ hσ)) hIg
        _ = 2 * (C_T * ε) * ((9 / 10 : ℝ) - t)
              + L₀ * (∫ σ in t..(9 / 10 : ℝ), ‖Z σ - Work.OddVolterra.baseState σ‖) := by
            rw [intervalIntegral.integral_add intervalIntegrable_const (hfint.const_mul L₀),
              intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
            ring
        _ ≤ 2 * (C_T * ε) + L₀ * (∫ σ in t..(9 / 10 : ℝ), ‖Z σ - Work.OddVolterra.baseState σ‖) := by
            have h1 : (0 : ℝ) ≤ 2 * (C_T * ε) := by positivity
            have h2 : (9 / 10 : ℝ) - t ≤ 1 := by linarith [ht1]
            have h3 : 0 ≤ ∫ σ in t..(9 / 10 : ℝ), ‖Z σ - Work.OddVolterra.baseState σ‖ :=
              intervalIntegral.integral_nonneg ht2 (fun σ _ => norm_nonneg _)
            have h5 : 2 * (C_T * ε) * ((9 / 10 : ℝ) - t) ≤ 2 * (C_T * ε) * 1 :=
              mul_le_mul_of_nonneg_left h2 h1
            linarith [mul_nonneg hL₀nn h3]
    have hbz : Z t ∈ Metric.closedBall (Work.OddVolterra.baseState t) (1 / 2) := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact hZdist t ⟨ht1, by linarith [ht2]⟩
    have hbb : Work.OddVolterra.baseState t ∈ Metric.closedBall (Work.OddVolterra.baseState t) (1 / 2) := by
      rw [Metric.mem_closedBall]; simp
    have hinj := hc₀inj t ⟨ht1, by linarith [ht2]⟩ (Z t) hbz (Work.OddVolterra.baseState t) hbb
    have hge1 : ‖Work.OddVolterra.Godd n 0 t (Z t) - Work.OddVolterra.Godd n h t (Z t)‖ ≤ C_G * ε := by
      rw [← norm_neg, neg_sub]
      exact hGclose h hh ε hεpos hε100 hjet t ⟨ht1, by linarith [ht2]⟩ (Z t) (by rw [← dist_eq_norm]; exact hZdist t ⟨ht1, by linarith [ht2]⟩)
    have htri : ‖Work.OddVolterra.Godd n 0 t (Z t) - Work.OddVolterra.Godd n 0 t (Work.OddVolterra.baseState t)‖
        ≤ ‖Work.OddVolterra.Godd n 0 t (Z t) - Work.OddVolterra.Godd n h t (Z t)‖
          + ‖Work.OddVolterra.Godd n h t (Z t) - Work.OddVolterra.Godd n h t (Work.OddVolterra.baseState t)‖
          + ‖Work.OddVolterra.Godd n h t (Work.OddVolterra.baseState t) -
              Work.OddVolterra.Godd n 0 t (Work.OddVolterra.baseState t)‖ := by
      have he : Work.OddVolterra.Godd n 0 t (Z t) - Work.OddVolterra.Godd n 0 t (Work.OddVolterra.baseState t)
          = (Work.OddVolterra.Godd n 0 t (Z t) - Work.OddVolterra.Godd n h t (Z t))
            + (Work.OddVolterra.Godd n h t (Z t) - Work.OddVolterra.Godd n h t (Work.OddVolterra.baseState t))
            + (Work.OddVolterra.Godd n h t (Work.OddVolterra.baseState t) -
                Work.OddVolterra.Godd n 0 t (Work.OddVolterra.baseState t)) := by
        abel
      rw [he]
      have h4 := norm_add_le (Work.OddVolterra.Godd n 0 t (Z t) - Work.OddVolterra.Godd n h t (Z t))
        (Work.OddVolterra.Godd n h t (Z t) - Work.OddVolterra.Godd n h t (Work.OddVolterra.baseState t))
      refine le_trans (norm_add_le _ _) ?_
      linarith
    have hCte : (0 : ℝ) ≤ C_T * ε := mul_nonneg hC_Tpos.le hε0
    have hIntB : ‖(∫ σ in t..1, (Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ) -
        Work.OddVolterra.Theta n 0 t σ (Work.OddVolterra.baseState σ)))‖ ≤ C_T * ε := by
      have hc : ∀ σ ∈ Set.uIoc t 1, ‖Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ) -
          Work.OddVolterra.Theta n 0 t σ (Work.OddVolterra.baseState σ)‖ ≤ C_T * ε := by
        intro σ hσ
        rw [Set.uIoc_of_le (by linarith : t ≤ 1)] at hσ
        exact hTheta_close_pt hσ.1 (by linarith [hσ.2]) (by rw [Metric.mem_closedBall]; simp)
      refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hc) ?_
      have h2 : |(1 : ℝ) - t| ≤ 1 := by rw [abs_of_nonneg (by linarith)]; linarith
      calc C_T * ε * |(1 : ℝ) - t| ≤ C_T * ε * 1 := mul_le_mul_of_nonneg_left h2 hCte
        _ = C_T * ε := mul_one _
    have hBtot : ‖(∫ σ in t..1, (Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ) -
        Work.OddVolterra.Theta n 0 t σ (Work.OddVolterra.baseState σ)))
        + (Work.OddVolterra.Xi n h t - Work.OddVolterra.Xi n 0 t)
        - (Work.OddVolterra.Godd n h t (Work.OddVolterra.baseState t) -
            Work.OddVolterra.Godd n 0 t (Work.OddVolterra.baseState t))‖ ≤ ResB * ε := by
      have h1 : ‖(∫ σ in t..1, (Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ) -
          Work.OddVolterra.Theta n 0 t σ (Work.OddVolterra.baseState σ)))
          + (Work.OddVolterra.Xi n h t - Work.OddVolterra.Xi n 0 t)‖ ≤ C_T * ε + C_X * ε :=
        le_trans (norm_add_le _ _) (by linarith [hIntB, hXi_pt])
      refine le_trans (norm_sub_le _ _) ?_
      rw [hResB]
      nlinarith [h1, hGd_pt, hC_Tpos, hC_Xpos, hC_Gpos, hε0]
    have hmain : ‖Work.OddVolterra.Godd n h t (Z t) - Work.OddVolterra.Godd n h t (Work.OddVolterra.baseState t)‖
        ≤ L₀ * (∫ σ in t..(9 / 10 : ℝ), ‖Z σ - Work.OddVolterra.baseState σ‖) + 2 * (C_T * ε) + ResB * ε := by
      rw [hident]
      have he : (∫ σ in t..(9 / 10 : ℝ), (Work.OddVolterra.Theta n h t σ (Z σ) -
            Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ)))
          + ((∫ σ in t..1, (Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ) -
              Work.OddVolterra.Theta n 0 t σ (Work.OddVolterra.baseState σ)))
            + (Work.OddVolterra.Xi n h t - Work.OddVolterra.Xi n 0 t))
          - (Work.OddVolterra.Godd n h t (Work.OddVolterra.baseState t) -
              Work.OddVolterra.Godd n 0 t (Work.OddVolterra.baseState t))
          = (∫ σ in t..(9 / 10 : ℝ), (Work.OddVolterra.Theta n h t σ (Z σ) -
              Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ)))
            + ((∫ σ in t..1, (Work.OddVolterra.Theta n h t σ (Work.OddVolterra.baseState σ) -
                Work.OddVolterra.Theta n 0 t σ (Work.OddVolterra.baseState σ)))
              + (Work.OddVolterra.Xi n h t - Work.OddVolterra.Xi n 0 t)
              - (Work.OddVolterra.Godd n h t (Work.OddVolterra.baseState t) -
                  Work.OddVolterra.Godd n 0 t (Work.OddVolterra.baseState t))) := by
        abel
      rw [he]
      refine le_trans (norm_add_le _ _) ?_
      linarith [hIntTheta, hBtot]
    have hfin : c₀ * ‖Z t - Work.OddVolterra.baseState t‖
        ≤ L₀ * (∫ σ in t..(9 / 10 : ℝ), ‖Z σ - Work.OddVolterra.baseState σ‖) + Res * ε := by
      have h1 : 2 * (C_T * ε) + ResB * ε + 2 * (C_G * ε) ≤ Res * ε := by
        have h2 : 2 * C_T + ResB + 2 * C_G ≤ Res := by rw [hRes]; linarith
        nlinarith [hε0, h2]
      linarith [hinj, htri, hge1, hGd_pt, hmain, h1]
    exact hfin
  have hfnn : ∀ u ∈ Set.Icc (7 / 10 : ℝ) (9 / 10 : ℝ),
      0 ≤ ‖Z u - Work.OddVolterra.baseState u‖ := fun u _ => norm_nonneg _
  have hgr := gronwall_window (c₀ := c₀) (L₀ := L₀) (ρ := Res * ε)
    (f := fun σ => ‖Z σ - Work.OddVolterra.baseState σ‖) hc₀pos hL₀nn
    (mul_nonneg hRespos.le hε0) hZfcont hfnn hinner_all
  intro s hs
  have hgr' := hgr s hs
  rw [dist_eq_norm]
  calc ‖Z s - Work.OddVolterra.baseState s‖
      ≤ (Res * ε / c₀) * (1 + (L₀ / c₀) * Real.exp (L₀ / c₀ + 1)) := hgr'
    _ = ((Res / c₀) * (1 + (L₀ / c₀) * Real.exp (L₀ / c₀ + 1))) * ε := by ring
    _ ≤ K * ε := by
        rw [hK]
        have h1 : (0 : ℝ) ≤ (Res / c₀) * (1 + (L₀ / c₀) * Real.exp (L₀ / c₀ + 1)) := by
          apply mul_nonneg (div_nonneg hRespos.le hc₀pos.le)
          have : 0 ≤ (L₀ / c₀) * Real.exp (L₀ / c₀ + 1) :=
            mul_nonneg (div_nonneg hL₀nn hc₀pos.le) (Real.exp_pos _).le
          linarith
        nlinarith [hε0, h1]


end

end Work.OddVolterra.Existence
