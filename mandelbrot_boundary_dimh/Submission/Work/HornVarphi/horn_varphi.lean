import Mathlib
import Submission.Work.Interfaces.HornParts
import Submission.Work.HornTopo.horn_topo
import Submission.Work.Horn.basic
import Submission.Work.Horn.basin_facts
import Submission.Work.Parab.basinEnters.zero_not_mem_basin
import Submission.Work.Normal.montel_omits_three
import Submission.Work.HornPhi.covering_iterate
import Submission.Work.HornPhi.crit_preimage_of_iterate
import Submission.Work.L62.lift_section
import Submission.Work.HornVarphi.exists_ball_subset_diff_critOrbit
import Submission.Work.HornVarphi.exists_psi_varphi
import Submission.Work.HornVarphi.exists_mapsTo_QLeft_of_tendsto_zero
import Submission.Work.HornVarphi.tendsto_zero_of_normal_nonvanishing

/-!
# AREA HORN-VARPHI — Claim B (Shishikura, Prop. 5.3): holomorphic sections of `φ` on `Bu ∪ Bl`

`Work.HornVarphi.horn_varphi : HornVarphiStatement`.  The proof follows `NOTES_LEAD_horn.md`
(HornVarphi part), with the "key step 4" (avoidance of the attracting petal `Ωp`) implemented by
uniform convergence of the iterates on `Ωp` rather than by an appeal to the picture.

Given `y ∈ B` off the forward critical orbit `P⁺ = {f₀^[k] c | k ≥ 1}`, we pick a ball
`ball y R ⊆ B ∖ P⁺`.  For `w ∈ Bu ∪ Bl` with `φ w` in the ball:

* `T`-invariance of `Bu`, `Bl` (`Work.HornTopo`) gives `w - n ∈ Bu ∪ Bl` for all `n`, and
  `z n := φ (w - n) ∈ B` with `f₀^[n] (z n) = φ w`;
* holomorphic sections `G n` of `f₀^[n]` over `ball y R` with `G n (φ w) = z n` exist because
  `f₀^[n] : B → ℂ` is a covering map over `ball y R` (no critical value there):
  `Work.HornPhi.covering_iterate` + `Work.L62.lift_section` (`exists_section_iterate_aux`);
* the `G n` omit the two points `f₀ c`, `f₀^[2] c` of `P⁺`, so Montel's theorem makes the family
  normal, and Hurwitz's theorem upgrades the pointwise convergence `G n (φ w) = φ (w - n) → 0`
  to locally uniform convergence (`tendsto_zero_of_normal_nonvanishing`);
* on the compact ball `closedBall y (R/2)`, `G N` avoids the petal `Ωp` — if `G N u ∈ Ωp` then
  `u = f₀^[N] (G N u)`, so `‖u‖ ≤ sup_{Ωp} ‖f₀^[N]‖ < R/2 ≤ ‖u‖` — and `G N u ≠ 0`, so with
  `ball 0 ε ⊆ Ωp ∪ φ '' QLeft ∪ {0}` (`d.flower`) we get `G N u ∈ φ '' QLeft`
  (`exists_mapsTo_QLeft_of_tendsto_zero`);
* `σ u := ψ (G N u) + N`, where `ψ` is the holomorphic inverse of `φ` on `QLeft`
  (`exists_psi_varphi`), is then a holomorphic section of `φ` over `ball y (R/2)` through `w`
  (`varphi_add_nat` iterates the functional equation), and it maps into `Bu` (or `Bl`) because its
  image is preconnected in `φ⁻¹(B)` and contains `w`.
-/

namespace Work.HornVarphi

open MandelDim Set Metric Filter Topology Complex
open scoped Topology

noncomputable section


/-- `QLeft ξ` contains the half plane `{Re · < -ξ}`. -/
theorem QLeft_halfplane_subset (ξ : ℝ) : {u : ℂ | u.re < -ξ} ⊆ QLeft ξ := by
  intro u hu
  simp only [Set.mem_setOf_eq] at hu
  have hleft : (u + (ξ : ℂ)).re < 0 := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have hlt : Real.pi / 2 < |Complex.arg (u + (ξ : ℂ))| := by
    rw [← not_le]
    intro h
    have h0 : 0 ≤ (u + (ξ : ℂ)).re := Complex.abs_arg_le_pi_div_two_iff.mp h
    simp only [Complex.add_re, Complex.ofReal_re] at h0
    linarith
  have : Real.pi / 3 < Real.pi / 2 := by linarith [Real.pi_pos]
  exact lt_trans this hlt

/-- `‖τ₀ z‖ = 1/‖z‖`. -/
theorem norm_tau0 (z : ℂ) : ‖tau0 z‖ = 1 / ‖z‖ := by
  have hz : tau0 z = -(z⁻¹) := by rw [tau0]; ring
  rw [hz, norm_neg, norm_inv, one_div]

/-- `‖z‖ = (‖τ₀ z‖)⁻¹`. -/
theorem norm_eq_inv_norm_tau0 (z : ℂ) : ‖z‖ = (‖tau0 z‖)⁻¹ := by
  rw [norm_tau0, inv_div, div_one]

/-- The asymptotic main term of the left end blows up as `n → ∞`. -/
theorem tendsto_norm_add_log (a b w : ℂ) :
    Filter.Tendsto (fun n : ℕ => ‖(w - (n : ℂ)) + a * Complex.log (-(w - (n : ℂ))) + b‖)
      Filter.atTop Filter.atTop := by
  set K : ℝ := ‖w‖ + ‖a‖ * (Real.log (1 + ‖w‖) + Real.pi) + ‖b‖ with hK
  have hlog : ∀ᶠ n : ℕ in Filter.atTop, ‖a‖ * Real.log ((n : ℝ) + 1) ≤ (n : ℝ) / 2 := by
    have hb := Real.isLittleO_log_id_atTop.bound (c := 1 / (4 * ‖a‖ + 1)) (by positivity)
    have htend : Filter.Tendsto (fun n : ℕ => (n : ℝ) + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    have hb' := htend.eventually hb
    filter_upwards [hb', Filter.eventually_ge_atTop 1] with n hn hn1
    have hn1r : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hx1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have hlogpos : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg hx1
    have hhn : Real.log ((n : ℝ) + 1) ≤ (1 / (4 * ‖a‖ + 1)) * ((n : ℝ) + 1) := by
      have h := hn
      rw [Real.norm_eq_abs, abs_of_nonneg hlogpos, id_eq,
        Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (n : ℝ) + 1)] at h
      exact h
    have h2 : ‖a‖ * (1 / (4 * ‖a‖ + 1)) ≤ 1 / 4 := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      linarith [norm_nonneg a]
    calc ‖a‖ * Real.log ((n : ℝ) + 1)
        ≤ ‖a‖ * ((1 / (4 * ‖a‖ + 1)) * ((n : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_left hhn (norm_nonneg a)
      _ = (‖a‖ * (1 / (4 * ‖a‖ + 1))) * ((n : ℝ) + 1) := by ring
      _ ≤ (1 / 4) * ((n : ℝ) + 1) := mul_le_mul_of_nonneg_right h2 (by linarith)
      _ ≤ (n : ℝ) / 2 := by linarith
  have hwn : ∀ n : ℕ, (n : ℝ) - ‖w‖ ≤ ‖w - (n : ℂ)‖ := by
    intro n
    have h := abs_norm_sub_norm_le ((n : ℂ)) w
    have h2 : ‖(n : ℂ)‖ - ‖w‖ ≤ ‖w - (n : ℂ)‖ := by
      calc ‖(n : ℂ)‖ - ‖w‖ ≤ |‖(n : ℂ)‖ - ‖w‖| := le_abs_self _
        _ ≤ ‖(n : ℂ) - w‖ := h
        _ = ‖w - (n : ℂ)‖ := norm_sub_rev _ _
    rwa [Complex.norm_natCast] at h2
  have hneg : ∀ n : ℕ, ‖-(w - (n : ℂ))‖ ≤ (n : ℝ) + ‖w‖ := by
    intro n
    rw [norm_neg]
    have h := norm_sub_le w ((n : ℂ))
    rw [Complex.norm_natCast] at h
    linarith
  have hlogz : ∀ᶠ n : ℕ in Filter.atTop,
      ‖Complex.log (-(w - (n : ℂ)))‖
        ≤ Real.log ((n : ℝ) + 1) + Real.log (1 + ‖w‖) + Real.pi := by
    filter_upwards [Filter.eventually_ge_atTop (Nat.ceil (‖w‖) + 1)] with n hn
    have hn1 : (‖w‖) + 1 ≤ (n : ℝ) := by
      have h2 : ((Nat.ceil (‖w‖) + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      push_cast at h2
      linarith [Nat.le_ceil (‖w‖)]
    have ht1 : (1 : ℝ) ≤ ‖-(w - (n : ℂ))‖ := by
      have := hwn n
      rw [norm_neg]
      linarith
    calc ‖Complex.log (-(w - (n : ℂ)))‖
        ≤ |(Complex.log (-(w - (n : ℂ)))).re| + |(Complex.log (-(w - (n : ℂ)))).im| :=
          Complex.norm_le_abs_re_add_abs_im _
      _ = |Real.log ‖-(w - (n : ℂ))‖| + |Complex.arg (-(w - (n : ℂ)))| := by
          rw [Complex.log_re, Complex.log_im]
      _ = Real.log ‖-(w - (n : ℂ))‖ + |Complex.arg (-(w - (n : ℂ)))| := by
          rw [abs_of_nonneg (Real.log_nonneg ht1)]
      _ ≤ Real.log ((n : ℝ) + ‖w‖) + Real.pi := by
          have h1 : Real.log ‖-(w - (n : ℂ))‖ ≤ Real.log ((n : ℝ) + ‖w‖) := by
            exact Real.log_le_log (by linarith : (0 : ℝ) < ‖-(w - (n : ℂ))‖) (hneg n)
          have h2 : |Complex.arg (-(w - (n : ℂ)))| ≤ Real.pi := Complex.abs_arg_le_pi _
          linarith
      _ ≤ Real.log ((n : ℝ) + 1) + Real.log (1 + ‖w‖) + Real.pi := by
          have hle : (n : ℝ) + ‖w‖ ≤ ((n : ℝ) + 1) * (1 + ‖w‖) := by
            nlinarith [norm_nonneg w, (by positivity : (0:ℝ) ≤ (n:ℝ))]
          have h1 : Real.log ((n : ℝ) + ‖w‖) ≤ Real.log (((n : ℝ) + 1) * (1 + ‖w‖)) := by
            refine Real.log_le_log ?_ hle
            linarith [norm_nonneg w, ht1]
          rw [Real.log_mul (by linarith) (by linarith [norm_nonneg w])] at h1
          linarith
  have hmain : ∀ᶠ n : ℕ in Filter.atTop,
      (n : ℝ) / 2 - K ≤ ‖(w - (n : ℂ)) + a * Complex.log (-(w - (n : ℂ))) + b‖ := by
    filter_upwards [hlog, hlogz] with n hlogb hlogzn
    have h1 : ‖(w - (n : ℂ)) + a * Complex.log (-(w - (n : ℂ))) + b‖
        ≥ ‖(w - (n : ℂ)) + a * Complex.log (-(w - (n : ℂ)))‖ - ‖b‖ := by
      have h := norm_add_le ((w - (n : ℂ)) + a * Complex.log (-(w - (n : ℂ))) + b) (-b)
      simp only [add_neg_cancel_right, norm_neg] at h
      linarith
    have h2 : ‖(w - (n : ℂ)) + a * Complex.log (-(w - (n : ℂ)))‖
        ≥ ‖w - (n : ℂ)‖ - ‖a * Complex.log (-(w - (n : ℂ)))‖ := by
      have h := norm_add_le ((w - (n : ℂ)) + a * Complex.log (-(w - (n : ℂ))))
        (-(a * Complex.log (-(w - (n : ℂ)))))
      simp only [add_neg_cancel_right, norm_neg] at h
      linarith
    have h3 : ‖a * Complex.log (-(w - (n : ℂ)))‖
        = ‖a‖ * ‖Complex.log (-(w - (n : ℂ)))‖ := norm_mul _ _
    have h4 : ‖a * Complex.log (-(w - (n : ℂ)))‖
        ≤ ‖a‖ * (Real.log ((n : ℝ) + 1) + Real.log (1 + ‖w‖) + Real.pi) := by
      rw [h3]
      exact mul_le_mul_of_nonneg_left hlogzn (norm_nonneg a)
    have h5 : ‖a‖ * (Real.log ((n : ℝ) + 1) + Real.log (1 + ‖w‖) + Real.pi)
        ≤ (n : ℝ) / 2 + ‖a‖ * (Real.log (1 + ‖w‖) + Real.pi) := by
      nlinarith [hlogb, norm_nonneg a]
    rw [hK]
    linarith [h1, h2, h4, h5, hwn n, norm_nonneg b]
  have hlin : Filter.Tendsto (fun n : ℕ => (n : ℝ) / 2 - K) Filter.atTop Filter.atTop := by
    have h1 : Filter.Tendsto (fun n : ℕ => ((n : ℝ))) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop
    have h1' : Filter.Tendsto (fun n : ℕ => (n : ℝ) / 2) Filter.atTop Filter.atTop :=
      h1.atTop_div_const (by norm_num : (0 : ℝ) < 2)
    have h2 : Filter.Tendsto (fun n : ℕ => (n : ℝ) / 2 + (-K)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ (-K) h1'
    refine h2.congr' (Filter.Eventually.of_forall fun n => ?_)
    ring_nf
  exact Filter.tendsto_atTop_mono' _ hmain hlin

/-- `‖w - n‖ ≥ n - ‖w‖`: the norm of `w` shifted by `-n`. -/
theorem norm_sub_natCast_ge (w : ℂ) (n : ℕ) : (n : ℝ) - ‖w‖ ≤ ‖w - (n : ℂ)‖ := by
  have h := abs_norm_sub_norm_le ((n : ℂ)) w
  have h2 : ‖(n : ℂ)‖ - ‖w‖ ≤ ‖w - (n : ℂ)‖ := by
    calc ‖(n : ℂ)‖ - ‖w‖ ≤ |‖(n : ℂ)‖ - ‖w‖| := le_abs_self _
      _ ≤ ‖(n : ℂ) - w‖ := h
      _ = ‖w - (n : ℂ)‖ := norm_sub_rev _ _
  rwa [Complex.norm_natCast] at h2

/-- At the left end, `w - n` is eventually in the sector `QLeft ξ₀` and `φ (w - n) → 0`. -/
theorem eventually_sub_mem_QLeft_and_tendsto_varphi_aux {f₀ : ℂ → ℂ} {D₀ : Set ℂ}
    (d : ParabData f₀ D₀) {w : ℂ} :
    (∀ᶠ n : ℕ in Filter.atTop, w - n ∈ QLeft d.ξ₀) ∧
      Filter.Tendsto (fun n : ℕ => d.φ (w - n)) Filter.atTop (nhds 0) := by
  have hevQ : ∀ᶠ n : ℕ in Filter.atTop, w - n ∈ QLeft d.ξ₀ := by
    have htail : ∀ᶠ n : ℕ in Filter.atTop, (w.re + d.ξ₀) < (n : ℝ) := by
      refine Filter.eventually_atTop.mpr ⟨Nat.ceil (w.re + d.ξ₀) + 1, fun n hn => ?_⟩
      have h2 : ((Nat.ceil (w.re + d.ξ₀) + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      push_cast at h2
      linarith [Nat.le_ceil (w.re + d.ξ₀)]
    filter_upwards [htail] with n hn
    refine QLeft_halfplane_subset d.ξ₀ ?_
    simp only [Set.mem_ofPred_eq, Complex.sub_re, Complex.natCast_re]
    linarith
  refine ⟨hevQ, ?_⟩
  obtain ⟨a, b, hab⟩ := d.φ_asymp
  obtain ⟨R, hR⟩ := hab 1 (by norm_num)
  have hvanish : ∀ᶠ n : ℕ in Filter.atTop, R < ‖w - (n : ℂ)‖ := by
    refine Filter.eventually_atTop.mpr ⟨Nat.ceil (R + ‖w‖) + 1, fun n hn => ?_⟩
    have h2 : ((Nat.ceil (R + ‖w‖) + 1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    push_cast at h2
    have h3 : R + ‖w‖ < (n : ℝ) := by linarith [Nat.le_ceil (R + ‖w‖)]
    have h4 := norm_sub_natCast_ge w n
    linarith
  have hnear : ∀ᶠ n : ℕ in Filter.atTop,
      ‖tau0 (d.φ (w - n)) - ((w - (n : ℂ)) + a * Complex.log (-(w - (n : ℂ))) + b)‖ < 1 := by
    filter_upwards [hevQ, hvanish] with n hQ hR'
    exact hR _ hQ hR'
  have htu : Filter.Tendsto (fun n : ℕ => ‖tau0 (d.φ (w - n))‖) Filter.atTop Filter.atTop := by
    have hmono : ∀ᶠ n : ℕ in Filter.atTop,
        ‖(w - (n : ℂ)) + a * Complex.log (-(w - (n : ℂ))) + b‖ - 1
          ≤ ‖tau0 (d.φ (w - n))‖ := by
      filter_upwards [hnear] with n hn
      have h2 : ‖tau0 (d.φ (w - n))‖
          ≥ ‖(w - (n : ℂ)) + a * Complex.log (-(w - (n : ℂ))) + b‖ - 1 := by
        have h := norm_sub_le (tau0 (d.φ (w - n)))
          (tau0 (d.φ (w - n)) - ((w - (n : ℂ)) + a * Complex.log (-(w - (n : ℂ))) + b))
        have h' : ‖(w - (n : ℂ)) + a * Complex.log (-(w - (n : ℂ))) + b‖
            ≤ ‖tau0 (d.φ (w - n))‖
              + ‖tau0 (d.φ (w - n)) - ((w - (n : ℂ)) + a * Complex.log (-(w - (n : ℂ))) + b)‖ := by
          simpa using h
        linarith
      exact h2
    have hg : Filter.Tendsto
        (fun n : ℕ => ‖(w - (n : ℂ)) + a * Complex.log (-(w - (n : ℂ))) + b‖ - 1)
        Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ (-1) (tendsto_norm_add_log a b w)
    exact Filter.tendsto_atTop_mono' _ hmono hg
  have hnorm : Filter.Tendsto (fun n : ℕ => ‖d.φ (w - n)‖) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => (‖tau0 (d.φ (w - n))‖)⁻¹) Filter.atTop (nhds 0) :=
      htu.inv_tendsto_atTop
    refine h1.congr' (Filter.Eventually.of_forall fun n => ?_)
    exact (norm_eq_inv_norm_tau0 (d.φ (w - n))).symm
  rwa [tendsto_zero_iff_norm_tendsto_zero]

/-- Holomorphic sections of `f₀^[n]` over a ball `ball y ρ ⊆ B` avoiding the forward critical
orbit, through any prescribed preimage `z ∈ B` of a point of the ball. -/
theorem exists_section_iterate_aux {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}
    (hS : MandelDim.IsF0Setup f₀ D₀ B c) (n : ℕ) {y : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hball : Metric.ball y ρ ⊆ B) (hav : ∀ u ∈ Metric.ball y ρ, u ∉ MandelDim.critOrbit f₀ c)
    {z : ℂ} (hzB : z ∈ B) (hfz : f₀^[n] z ∈ Metric.ball y ρ) :
    ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball y ρ) ∧ G (f₀^[n] z) = z ∧
      (∀ u ∈ Metric.ball y ρ, G u ∈ B ∧ f₀^[n] (G u) = u ∧ G u ∉ MandelDim.critOrbit f₀ c) := by
  have hgerm : IsParabolicGerm f₀ D₀ := hS.1
  have himm : IsImmediateBasin f₀ D₀ B := hS.2.1
  have huniq : ∀ c' ∈ B, deriv f₀ c' = 0 → c' = c := hS.2.2.2.2
  have hBopen : IsOpen B := himm.1
  have hBsubD : B ⊆ D₀ := HornTopo.subset_D₀_of_immediateBasin himm
  have hBmap : MapsTo f₀ B B := himm.2.2.2.2.1
  have hiter : ∀ k : ℕ, MapsTo (f₀^[k]) B B := by
    intro k
    induction k with
    | zero => intro x hx; exact hx
    | succ j ih =>
        intro x hx
        rw [Function.iterate_succ_apply']
        exact hBmap (ih hx)
  have hfD : ∀ w ∈ D₀, DifferentiableAt ℂ f₀ w :=
    fun w hw => hgerm.2.2.1.differentiableAt (hgerm.1.mem_nhds hw)
  have hdiffB : ∀ m : ℕ, ∀ w ∈ B, DifferentiableAt ℂ (f₀^[m]) w := fun m w hw =>
    Work.HornPhi.differentiableAt_iterate m (fun j _ => hfD _ (hBsubD (hiter j hw)))
  have hloc : ∀ w ∈ B, f₀^[n] w ∈ Metric.ball y ρ → deriv (f₀^[n]) w ≠ 0 := by
    intro w hwB hwball hcrit
    obtain ⟨j, hjN, hjc⟩ :=
      Work.HornPhi.crit_preimage_of_iterate hgerm himm huniq hwB hcrit
    have hsplit : f₀^[n] w = f₀^[n - j] c := by
      rw [show f₀^[n] w = f₀^[n - j] (f₀^[j] w) from by
            rw [← Function.iterate_add_apply, Nat.sub_add_cancel (le_of_lt hjN)], hjc]
    exact hav _ hwball ⟨n - j, by omega, hsplit⟩
  have hproper : ∀ m : ℕ, ∀ L : Set ℂ, L ⊆ B → IsCompact L → IsCompact (B ∩ (f₀^[m]) ⁻¹' L) := by
    intro m
    induction m with
    | zero =>
        intro L hLB hL
        have h0 : (f₀^[0]) ⁻¹' L = L := by ext w; simp
        rw [h0, Set.inter_eq_right.mpr hLB]
        exact hL
    | succ k ih =>
        intro L hLB hL
        have hset : B ∩ (f₀^[k + 1]) ⁻¹' L = B ∩ f₀ ⁻¹' (B ∩ (f₀^[k]) ⁻¹' L) := by
          ext w
          simp only [Set.mem_inter_iff, Set.mem_preimage, Function.iterate_succ,
            Function.comp_apply]
          constructor
          · rintro ⟨hwB, hw⟩; exact ⟨hwB, hBmap hwB, hw⟩
          · rintro ⟨hwB, _, hw⟩; exact ⟨hwB, hw⟩
        rw [hset]
        exact himm.2.2.2.2.2.2 _ Set.inter_subset_left (ih L hLB hL)
  have hcov : IsCoveringMapOn (fun z : B => f₀^[n] z) (Metric.ball y ρ) :=
    Work.HornPhi.covering_iterate hBopen Metric.isOpen_ball hball (hdiffB n) hloc (hproper n)
  haveI : ContractibleSpace (Metric.ball y ρ) :=
    (convex_ball y ρ).contractibleSpace ⟨y, Metric.mem_ball_self hρ⟩
  haveI : SimplyConnectedSpace (Metric.ball y ρ) := inferInstance
  have hp : DifferentiableOn ℂ (f₀^[n]) B := fun w hw => (hdiffB n w hw).differentiableWithinAt
  obtain ⟨G, hGdiff, hGat, hGprop⟩ :=
    Work.L62.lift_section hBopen hp Metric.isOpen_ball inferInstance hcov hfz hzB rfl
  refine ⟨G, hGdiff, hGat, fun u hu => ⟨(hGprop u hu).1, (hGprop u hu).2, ?_⟩⟩
  rintro ⟨k, hk1, hku⟩
  have hu' : u = f₀^[n + k] c := by
    rw [Function.iterate_add_apply, ← hku, (hGprop u hu).2]
  exact hav u hu ⟨n + k, by omega, hu'⟩

/-! ## Glue lemmas (mine) -/

/-- Iterating the functional equation along a point of `Dφ` whose `φ`-image stays in `B`. -/
theorem varphi_add_nat {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : ParabData f₀ D₀) {B : Set ℂ}
    (hBmaps : MapsTo f₀ B B) (hBsubD : B ⊆ D₀) {u : ℂ} (hu : u ∈ d.Dφ) (huB : d.φ u ∈ B) :
    ∀ n : ℕ, u + n ∈ d.Dφ ∧ d.φ (u + n) = f₀^[n] (d.φ u) := by
  have hiter : ∀ k : ℕ, MapsTo (f₀^[k]) B B := by
    intro k
    induction k with
    | zero => intro x hx; exact hx
    | succ j ih =>
        intro x hx
        rw [Function.iterate_succ_apply']
        exact hBmaps (ih hx)
  intro n
  induction n with
  | zero =>
      have h0 : u + ((0 : ℕ) : ℂ) = u := by norm_num
      rw [h0]
      exact ⟨hu, rfl⟩
  | succ k ih =>
      obtain ⟨hDφk, hφk⟩ := ih
      have hφkB : d.φ (u + k) ∈ B := by rw [hφk]; exact hiter k huB
      have hsucc : u + k + 1 ∈ d.Dφ := (d.succ_iff (u + k) hDφk).mpr (hBsubD hφkB)
      have hcast : u + ((k + 1 : ℕ) : ℂ) = u + k + 1 := by push_cast; ring
      refine ⟨by rw [hcast]; exact hsucc, ?_⟩
      rw [hcast, d.φ_abel (u + k) hDφk hsucc, hφk, Function.iterate_succ_apply']

/-- Two distinct points of the forward critical orbit. -/
theorem exists_two_distinct_critOrbit {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}
    (hS : IsF0Setup f₀ D₀ B c) :
    ∃ p ∈ critOrbit f₀ c, ∃ q ∈ critOrbit f₀ c, p ≠ q := by
  have hgem : IsParabolicGerm f₀ D₀ := hS.1
  have himm : IsImmediateBasin f₀ D₀ B := hS.2.1
  have hcB : c ∈ B := hS.2.2.1
  have h0B : (0 : ℂ) ∉ B := fun h =>
    Work.Parab.basinEnters.zero_not_mem_parabolicBasin hgem (himm.2.2.1 h)
  have hBmaps : MapsTo f₀ B B := himm.2.2.2.2.1
  have hfcB : f₀ c ∈ B := hBmaps hcB
  refine ⟨f₀ c, ⟨1, le_rfl, rfl⟩, f₀^[2] c, ⟨2, by norm_num, rfl⟩, ?_⟩
  intro heq
  have hfix : f₀ (f₀ c) = f₀ c := by
    simpa [Function.iterate_succ_apply] using heq.symm
  have hfixiter : ∀ m : ℕ, f₀^[m] (f₀ c) = f₀ c := by
    intro m
    induction m with
    | zero => rfl
    | succ j ih =>
        rw [Function.iterate_succ_apply, hfix, ih]
  have htend : Filter.Tendsto (fun k : ℕ => f₀^[k] c) Filter.atTop (nhds 0) :=
    Work.Horn.BasinAux.tendsto_zero (himm.2.2.1 hcB)
  have hcont : ContinuousAt f₀ (0 : ℂ) :=
    hgem.2.2.1.continuousOn.continuousAt (hgem.1.mem_nhds hgem.2.1)
  have h2 : Filter.Tendsto (fun k : ℕ => f₀ (f₀^[k] c)) Filter.atTop (nhds (f₀ 0)) :=
    hcont.tendsto.comp htend
  rw [hgem.2.2.2.1] at h2
  have h3 : Filter.Tendsto (fun k : ℕ => f₀ (f₀^[k] c)) Filter.atTop (nhds (f₀ c)) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [Function.iterate_succ_apply, hfixiter m, hfix]
  have h4 : f₀ c = 0 := tendsto_nhds_unique h3 h2
  exact h0B (h4 ▸ hfcB)

/-- Claim B: `φ` has holomorphic local sections over small discs in `B` off the critical orbit. -/
theorem horn_varphi : HornVarphiStatement := by
  intro f₀ D₀ B c d hS
  intro y hyB hycrit
  have hgem : IsParabolicGerm f₀ D₀ := hS.1
  have himm : IsImmediateBasin f₀ D₀ B := hS.2.1
  have h0B : (0 : ℂ) ∉ B := fun h =>
    Work.Parab.basinEnters.zero_not_mem_parabolicBasin hgem (himm.2.2.1 h)
  have hBsubD : B ⊆ D₀ := HornTopo.subset_D₀_of_immediateBasin himm
  have hBmaps : MapsTo f₀ B B := himm.2.2.2.2.1
  obtain ⟨-, -, hTinvU, hTinvL, -, -, hSubDE⟩ := HornTopo.horn_topo f₀ D₀ B c d hS
  -- F3: a ball around `y` inside `B` and off the critical orbit
  obtain ⟨R, hRpos, hRball, hRcrit⟩ := exists_ball_subset_diff_critOrbit hS hyB hycrit
  have hzeroR : (0 : ℂ) ∉ ball y R := fun h => h0B (hRball h)
  have hyR : R ≤ ‖y‖ := by
    have h1 : ¬ (dist (0 : ℂ) y < R) := fun h2 => hzeroR (Metric.mem_ball.mpr h2)
    have h2 : dist (0 : ℂ) y = ‖y‖ := by rw [dist_eq_norm]; simp
    rw [h2] at h1
    exact not_lt.mp h1
  set r : ℝ := R / 2 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; linarith
  have hrR : r < R := by rw [hrdef]; linarith
  have hballr : ball y r ⊆ B := by
    rw [hrdef]
    exact subset_trans (Metric.ball_subset_ball (by linarith)) hRball
  have hballrR : ball y r ⊆ ball y R := by
    rw [hrdef]; exact Metric.ball_subset_ball (by linarith)
  refine ⟨r, hrpos, hballr, ?_⟩
  intro w hwB hφw
  -- Step 1: `w - n` stays in `Bu ∪ Bl`
  have hshift : ∀ n : ℕ, w - n ∈ BuOf d B ∪ BlOf d B := by
    intro n
    have hcast : ((↑(-(n : ℤ)) : ℂ)) = -(n : ℂ) := by push_cast; ring
    rcases hwB with hw | hw
    · left
      have h := Work.Horn.MandelDim.IsTInvariant.add_int hTinvU hw (-(n : ℤ))
      rw [hcast] at h
      simpa [sub_eq_add_neg] using h
    · right
      have h := Work.Horn.MandelDim.IsTInvariant.add_int hTinvL hw (-(n : ℤ))
      rw [hcast] at h
      simpa [sub_eq_add_neg] using h
  -- Step 2: `z n = φ (w - n) ∈ B` with `f^[n] (z n) = φ w`
  have hzBtil : ∀ n : ℕ, w - n ∈ Btil d B := fun n => by
    rcases hshift n with h | h
    · exact connectedComponentIn_subset _ _ h
    · exact connectedComponentIn_subset _ _ h
  have hznB : ∀ n : ℕ, d.φ (w - n) ∈ B := fun n => (hzBtil n).2
  have hzf : ∀ n : ℕ, f₀^[n] (d.φ (w - n)) = d.φ w := by
    intro n
    have h := (varphi_add_nat d hBmaps hBsubD (hzBtil n).1 (hznB n) n).2
    have hw' : (w - n) + (n : ℂ) = w := by ring
    rw [hw'] at h
    exact h.symm
  have hφwR : d.φ w ∈ ball y R := hballrR hφw
  -- Step 3: the holomorphic sections `G n`
  have hsec : ∀ n : ℕ, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (ball y R) ∧
      G (d.φ w) = d.φ (w - n) ∧
      (∀ u ∈ ball y R, G u ∈ B ∧ f₀^[n] (G u) = u ∧ G u ∉ critOrbit f₀ c) := by
    intro n
    have hfz : f₀^[n] (d.φ (w - n)) ∈ ball y R := by
      rw [hzf n]; exact hφwR
    obtain ⟨G, h1, h2, h3⟩ := exists_section_iterate_aux hS n hRpos hRball hRcrit (hznB n) hfz
    exact ⟨G, h1, by rw [← hzf n]; exact h2, h3⟩
  choose G hG using hsec
  have hGhol : ∀ n, DifferentiableOn ℂ (G n) (ball y R) := fun n => (hG n).1
  have hGat : ∀ n, G n (d.φ w) = d.φ (w - n) := fun n => (hG n).2.1
  have hGprop : ∀ n u, u ∈ ball y R →
      G n u ∈ B ∧ f₀^[n] (G n u) = u ∧ G n u ∉ critOrbit f₀ c :=
    fun n u hu => (hG n).2.2 u hu
  -- Step 4: the family `{G n}` is normal (two points of the critical orbit are omitted)
  obtain ⟨p, hp, q, hq, hpq⟩ := exists_two_distinct_critOrbit hS
  have hnormal : Work.Normal.IsNormalFamily (Set.range G) (ball y R) := by
    refine Work.Normal.montel_two_omitted hpq Metric.isOpen_ball
      (convex_ball y R).isPreconnected ?_ ?_
    · rintro f ⟨n, rfl⟩
      exact hGhol n
    · rintro f ⟨n, rfl⟩ u hu
      have h := hGprop n u hu
      exact ⟨fun hc => h.2.2 (hc ▸ hp), fun hc => h.2.2 (hc ▸ hq)⟩
  -- Step 5: pointwise convergence at `φ w`
  have hlim : Filter.Tendsto (fun n : ℕ => G n (d.φ w)) Filter.atTop (nhds 0) := by
    have h := (eventually_sub_mem_QLeft_and_tendsto_varphi_aux (w := w) d).2
    exact Filter.Tendsto.congr' (Filter.Eventually.of_forall fun n => (hGat n).symm) h
  -- Step 6: locally uniform convergence to `0`
  have hconv : TendstoLocallyUniformlyOn G (fun _ => 0) Filter.atTop (ball y R) :=
    tendsto_zero_of_normal_nonvanishing Metric.isOpen_ball (convex_ball y R).isPreconnected G
      hGhol (fun n z hz h0 => h0B (h0 ▸ (hGprop n z hz).1)) hnormal hφwR hlim
  -- Step 7: petal avoidance on the smaller ball
  obtain ⟨N₀, hN₀⟩ := exists_mapsTo_QLeft_of_tendsto_zero d h0B hRpos hzeroR G hGhol
    (fun n u hu => (hGprop n u hu).1) (fun n u hu => (hGprop n u hu).2.1) hconv
  -- Step 8: choose `N ≥ N₀` with `w - N ∈ QLeft`
  obtain ⟨m, hm⟩ := d.exhaust (w - N₀) (hzBtil N₀).1
  set N : ℕ := N₀ + m with hNdef
  have hQN : w - N ∈ QLeft d.ξ₀ := by
    have hcast : w - N = (w - N₀) - m := by rw [hNdef]; push_cast; ring
    rw [hcast]; exact hm
  have hGN : ∀ u ∈ closedBall y r, G N u ∈ d.φ '' QLeft d.ξ₀ := by
    intro u hu
    rw [hrdef] at hu
    exact hN₀ N (by rw [hNdef]; exact Nat.le_add_right _ _) u hu
  -- Step 9: the section `σ = ψ ∘ (G N) + N`
  obtain ⟨ψ, hψhol, hψleft, hψright⟩ := exists_psi_varphi d
  have hψGN : ∀ u ∈ ball y r, ψ (G N u) ∈ QLeft d.ξ₀ ∧ d.φ (ψ (G N u)) = G N u :=
    fun u hu => hψright (G N u) (hGN u (Metric.ball_subset_closedBall hu))
  have hGNR : ∀ u ∈ ball y r, u ∈ ball y R := fun u hu => hballrR hu
  have hσat : ψ (G N (d.φ w)) + (N : ℂ) = w := by
    rw [hGat N, hψleft (w - N) hQN]
    ring
  have hσdiff : DifferentiableOn ℂ (fun u => ψ (G N u) + (N : ℂ)) (ball y r) := by
    have h1 : DifferentiableOn ℂ (fun u => ψ (G N u)) (ball y r) :=
      hψhol.comp ((hGhol N).mono hballrR)
        (fun u hu => hGN u (Metric.ball_subset_closedBall hu))
    exact h1.add_const _
  have hσφ : ∀ u ∈ ball y r, d.φ (ψ (G N u) + (N : ℂ)) = u := by
    intro u hu
    obtain ⟨hQ, hφψ⟩ := hψGN u hu
    have hvar := varphi_add_nat d hBmaps hBsubD (d.Q_sub hQ)
      (by rw [hφψ]; exact (hGprop N u (hGNR u hu)).1) N
    rw [hvar.2, hφψ, (hGprop N u (hGNR u hu)).2.1]
  have hσbtil : ∀ u ∈ ball y r, ψ (G N u) + (N : ℂ) ∈ Btil d B := by
    intro u hu
    obtain ⟨hQ, hφψ⟩ := hψGN u hu
    have hvar := varphi_add_nat d hBmaps hBsubD (d.Q_sub hQ)
      (by rw [hφψ]; exact (hGprop N u (hGNR u hu)).1) N
    exact ⟨hvar.1, by rw [hvar.2, hφψ, (hGprop N u (hGNR u hu)).2.1]; exact hballr hu⟩
  have hσmap : MapsTo (fun u => ψ (G N u) + (N : ℂ)) (ball y r)
      (BuOf d B ∪ BlOf d B) := by
    intro u hu
    have hpre : IsPreconnected ((fun u => ψ (G N u) + (N : ℂ)) '' ball y r) :=
      (convex_ball y r).isPreconnected.image _ hσdiff.continuousOn
    rcases hwB with hw | hw
    · left
      have hcomp := IsPreconnected.subset_connectedComponentIn hpre
        (show w ∈ (fun u => ψ (G N u) + (N : ℂ)) '' ball y r from ⟨d.φ w, hφw, hσat⟩)
        (fun z hz => by rcases hz with ⟨v, hv, rfl⟩; exact hσbtil v hv)
      have heq : connectedComponentIn (Btil d B) w = BuOf d B :=
        (connectedComponentIn_eq hw).symm
      rw [← heq]
      exact hcomp ⟨u, hu, rfl⟩
    · right
      have hcomp := IsPreconnected.subset_connectedComponentIn hpre
        (show w ∈ (fun u => ψ (G N u) + (N : ℂ)) '' ball y r from ⟨d.φ w, hφw, hσat⟩)
        (fun z hz => by rcases hz with ⟨v, hv, rfl⟩; exact hσbtil v hv)
      have heq : connectedComponentIn (Btil d B) w = BlOf d B :=
        (connectedComponentIn_eq hw).symm
      rw [← heq]
      exact hcomp ⟨u, hu, rfl⟩
  exact ⟨fun u => ψ (G N u) + (N : ℂ), hσdiff, hσmap, hσφ, hσat⟩


end

end Work.HornVarphi
