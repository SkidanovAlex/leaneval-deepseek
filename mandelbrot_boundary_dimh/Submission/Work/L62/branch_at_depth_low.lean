import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.perturbed_branch_lower
import Submission.Work.L62.branch_shadow_base

namespace Work.L62

open MandelDim Set Filter Topology Complex
open scoped Topology

noncomputable section

/-- A predicate that holds eventually along the lower end holds on a deep half-plane. -/
private lemma lowerEnd_eventually' {P : ℂ → Prop} (h : {w : ℂ | P w} ∈ MandelDim.lowerEnd) :
    ∃ T : ℝ, ∀ w : ℂ, w.im < -T → P w := by
  rw [MandelDim.lowerEnd, Filter.mem_comap] at h
  obtain ⟨t, ht, hts⟩ := h
  rw [Filter.mem_atBot_sets] at ht
  obtain ⟨R, hR⟩ := ht
  exact ⟨-R, fun w hw => hts (hR w.im (by linarith))⟩

theorem branch_at_depth_low {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {cl : ℂ}
    (hcl : Filter.Tendsto (fun w : ℂ => d.E w - w) MandelDim.lowerEnd (nhds cl))
    {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ) (hδκ : δ ≤ min (κ / 16) (1 / 8)) :
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ β : ℂ, κ ≤ Complex.im cl - Complex.im β →
      ∀ (R : ℂ → ℂ) (DR : Set ℂ), IsOpen DR → MandelDim.IsTEquivariantOn R DR →
        DifferentiableOn ℂ R DR → {w : ℂ | Complex.im w < -(y - 1 / 2)} ⊆ DR →
        (∀ w : ℂ, Complex.im w < -(y - 1 / 2) → ‖R w - d.E w‖ ≤ δ) →
        ∃ (H ρ : ℂ → ℂ) (c : ℂ),
          DifferentiableOn ℂ H {w : ℂ | Complex.im w < -y} ∧
          (∀ w : ℂ, Complex.im w < -y → Complex.im (H w) < -y ∧ H w ∈ DR ∧
            R (H w) - β = w ∧ H w = w + (β - cl) + ρ w) ∧
          DifferentiableOn ℂ ρ {w : ℂ | Complex.im w < -y} ∧
          (∀ w : ℂ, Complex.im w < -y → ρ (w + 1) = ρ w) ∧
          (∀ w : ℂ, Complex.im w < -y → ‖ρ w‖ ≤ 2 * δ) ∧
          (∀ w : ℂ, Complex.im w < -y → Complex.im (H w - w) ≤ -(κ / 4)) ∧
          Set.InjOn H {w : ℂ | Complex.im w < -y} ∧
          Filter.Tendsto ρ (Filter.comap Complex.im Filter.atBot) (nhds c) := by
  -- ## 0. thresholds coming from the (unperturbed) data
  obtain ⟨Yc, hYc⟩ : ∃ Yc : ℝ, ∀ u : ℂ, u.im < -Yc → ‖(d.E u - u) - cl‖ ≤ δ := by
    have h2 : {u : ℂ | ‖(d.E u - u) - cl‖ < δ} ∈ MandelDim.lowerEnd := by
      have h1 : ∀ᶠ u : ℂ in MandelDim.lowerEnd, dist (d.E u - u) cl < δ :=
        (Metric.tendsto_nhds.mp hcl) δ hδ
      filter_upwards [h1] with u hu
      simpa [dist_eq_norm] using hu
    obtain ⟨T, hT⟩ := lowerEnd_eventually' h2
    exact ⟨T, fun u hu => le_of_lt (hT u hu)⟩
  obtain ⟨Ylip, hYlip⟩ := deriv_E_sub_id_lower d (1 / 4) (by norm_num)
  set y₀ : ℝ := max (max (Yc + 1) (Ylip + 1)) (d.η₀ + 1) with hy₀def
  refine ⟨y₀, fun y hy β hβ R DR hDRo hTeq hRd hDRsub hclose => ?_⟩
  have hyYc : Yc + 1 ≤ y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hy
  have hyYlip : Ylip + 1 ≤ y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hy
  have hyη : d.η₀ + 1 ≤ y := le_trans (le_max_right _ _) hy
  have hδ16 : δ ≤ κ / 16 := le_trans hδκ (min_le_left _ _)
  have hδ4 : 4 * δ ≤ κ / 4 := by linarith
  have hR0 : (0 : ℝ) < 4 * δ := by linarith
  have hnorm : -(y - 1 / 2) = -y + 1 / 2 := by ring
  -- ## 1. depth bookkeeping: shifting down by `cl - β` buys `κ` of depth
  have him1 : ∀ v : ℂ, v.im < -y + 4 * δ → (v - (cl - β)).im < -y - 3 * κ / 4 := by
    intro v hv
    have h1 : (v - (cl - β)).im = v.im - (cl.im - β.im) := by simp
    rw [h1]
    have h2 : κ ≤ cl.im - β.im := hβ
    linarith
  have himU : ∀ z : ℂ, z.im < -y → ∀ v ∈ Metric.closedBall z (4 * δ),
      (v - (cl - β)).im < -y - 3 * κ / 4 := by
    intro z hz v hv
    refine him1 v ?_
    have h1 : v.im ≤ z.im + ‖v - z‖ := by
      have h := Complex.im_le_norm (v - z)
      rw [Complex.sub_im] at h
      linarith
    have h2 : ‖v - z‖ ≤ 4 * δ := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hv
      exact hv
    linarith
  have hdeep : ∀ u : ℂ, u.im < -y - 3 * κ / 4 → u.im < -(y - 1 / 2) := by
    intro u hu
    rw [hnorm]
    linarith [hκ]
  have hbelow : ∀ u : ℂ, u.im < -y - 3 * κ / 4 → u.im < -y := by
    intro u hu
    linarith [hκ]
  have hball_deep : ∀ u : ℂ, u.im < -y - 3 * κ / 4 →
      Metric.closedBall u (4 * δ) ⊆ {w : ℂ | w.im < -(y - 1 / 2)} := by
    intro u hu w hw
    have h1 : w.im ≤ u.im + ‖w - u‖ := by
      have h := Complex.im_le_norm (w - u)
      rw [Complex.sub_im] at h
      linarith
    have h2 : ‖w - u‖ ≤ 4 * δ := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      exact hw
    show w.im < -(y - 1 / 2)
    rw [hnorm]
    linarith [hδ4]
  -- ## 2. differentiability of the pieces, and the Cauchy estimate
  have hE_diff : ∀ w : ℂ, w.im < -(y - 1 / 2) → DifferentiableAt ℂ d.E w := by
    intro w hw
    have hη : d.η₀ < |w.im| := by
      have hw' : w.im < -y + 1 / 2 := by rw [hnorm] at hw; exact hw
      have h1 : d.η₀ < -w.im := by linarith [hyη, hw']
      exact lt_of_lt_of_le h1 (neg_le_abs w.im)
    exact ((Work.Horn.differentiableOn_E_abs_im_gt d) w hη).differentiableAt
      ((isOpen_lt continuous_const (continuous_abs.comp Complex.continuous_im)).mem_nhds hη)
  have hR_diff : ∀ w : ℂ, w.im < -(y - 1 / 2) → DifferentiableAt ℂ R w :=
    fun w hw => hRd.differentiableAt (hDRo.mem_nhds (hDRsub hw))
  have hCauchy : ∀ u : ℂ, u.im < -y - 3 * κ / 4 →
      ‖deriv (fun v : ℂ => R v - d.E v) u‖ ≤ 1 / 4 := by
    intro u hu
    have hsub := hball_deep u hu
    have hd1 : DifferentiableOn ℂ (fun v : ℂ => R v - d.E v) {w : ℂ | w.im < -(y - 1 / 2)} := by
      intro w hw
      exact ((hR_diff w hw).sub (hE_diff w hw)).differentiableWithinAt
    have hdd : DiffContOnCl ℂ (fun v : ℂ => R v - d.E v) (Metric.ball u (4 * δ)) :=
      hd1.diffContOnCl_ball hsub
    have hsph : ∀ w ∈ Metric.sphere u (4 * δ), ‖(fun v : ℂ => R v - d.E v) w‖ ≤ δ := by
      intro w hw
      have h1 : ‖w - u‖ = 4 * δ := by
        rw [← dist_eq_norm]
        exact Metric.mem_sphere.mp hw
      have h2 : w.im ≤ u.im + ‖w - u‖ := by
        have h := Complex.im_le_norm (w - u)
        rw [Complex.sub_im] at h
        linarith
      have h3 : w.im < -(y - 1 / 2) := by
        rw [h1] at h2
        rw [hnorm]
        linarith [hδ4]
      exact hclose w h3
    have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := u) (R := 4 * δ)
      (C := δ) hR0 hdd hsph
    have h4 : δ / (4 * δ) = 1 / 4 := by
      rw [div_eq_div_iff (by positivity) (by norm_num)]
      ring
    linarith [hc, h4]
  have hcontr : ∀ u : ℂ, u.im < -y - 3 * κ / 4 → ‖deriv R u - 1‖ ≤ 1 / 2 := by
    intro u hu
    have hu' : u.im < -(y - 1 / 2) := hdeep u hu
    have hR' : DifferentiableAt ℂ R u := hR_diff u hu'
    have hE' : DifferentiableAt ℂ d.E u := hE_diff u hu'
    have h1 := hCauchy u hu
    have h2 : ‖deriv (fun v : ℂ => d.E v - v) u‖ ≤ 1 / 4 := hYlip u (by linarith [hyYlip])
    have hA : DifferentiableAt ℂ (fun v : ℂ => R v - d.E v) u := hR'.sub hE'
    have hB : DifferentiableAt ℂ (fun v : ℂ => d.E v - v) u := hE'.sub differentiableAt_id
    have key : deriv R u - 1
        = deriv (fun v : ℂ => R v - d.E v) u + deriv (fun v : ℂ => d.E v - v) u := by
      have e1 : deriv (fun v : ℂ => R v - v) u = deriv R u - 1 :=
        (hR'.hasDerivAt.sub (hasDerivAt_id u)).deriv
      have e2 : deriv (fun v : ℂ => (R v - d.E v) + (d.E v - v)) u
          = deriv (fun v : ℂ => R v - d.E v) u + deriv (fun v : ℂ => d.E v - v) u :=
        deriv_add hA hB
      have e3 : (fun v : ℂ => (R v - d.E v) + (d.E v - v)) = (fun v : ℂ => R v - v) := by
        funext v; ring
      rw [← e1, ← e3, e2]
    rw [key]
    exact le_trans (norm_add_le _ _) (by linarith)
  -- ## 3. the branch, via the abstract contraction argument
  set S : ℂ → ℂ := fun v => R (v - (cl - β)) - β with hSdef
  have hSval : ∀ z : ℂ, z.im < -y → ∀ v ∈ Metric.closedBall z (4 * δ), ‖S v - v‖ ≤ 2 * δ := by
    intro z hz v hv
    have hu := himU z hz v hv
    have h1 : (v - (cl - β)).im < -(y - 1 / 2) := hdeep _ hu
    have h2 : ‖R (v - (cl - β)) - d.E (v - (cl - β))‖ ≤ δ := hclose _ h1
    have h3 : ‖(d.E (v - (cl - β)) - (v - (cl - β))) - cl‖ ≤ δ := hYc _ (by linarith [hyYc])
    have heq : S v - v
        = (R (v - (cl - β)) - d.E (v - (cl - β)))
          + ((d.E (v - (cl - β)) - (v - (cl - β))) - cl) := by
      simp only [hSdef]; ring
    rw [heq]
    exact le_trans (norm_add_le _ _) (by linarith)
  have hSderiv_eq : ∀ v : ℂ, (v - (cl - β)).im < -(y - 1 / 2) →
      deriv S v = deriv R (v - (cl - β)) := by
    intro v hv
    have hmem : v - (cl - β) ∈ DR := hDRsub hv
    have hR' : DifferentiableAt ℂ R (v - (cl - β)) := hRd.differentiableAt (hDRo.mem_nhds hmem)
    have hshift : HasDerivAt (fun v : ℂ => v - (cl - β)) 1 v :=
      (hasDerivAt_id v).sub_const (cl - β)
    have hcomp : deriv (fun v : ℂ => R (v - (cl - β))) v = deriv R (v - (cl - β)) := by
      have hh := (hR'.hasDerivAt.comp v hshift).deriv
      rw [mul_one] at hh
      exact hh
    simp only [hSdef]
    rw [deriv_sub_const, hcomp]
  have hSderiv : ∀ z : ℂ, z.im < -y → ∀ v ∈ Metric.closedBall z (4 * δ), ‖deriv S v - 1‖ ≤ 1 / 2 := by
    intro z hz v hv
    have hu := himU z hz v hv
    rw [hSderiv_eq v (hdeep _ hu)]
    exact hcontr _ hu
  have hSdiff : ∀ z : ℂ, z.im < -y → ∀ v ∈ Metric.closedBall z (4 * δ), DifferentiableAt ℂ S v := by
    intro z hz v hv
    have hu := himU z hz v hv
    have hv' : v - (cl - β) ∈ DR := hDRsub (hdeep _ hu)
    have hR' : DifferentiableAt ℂ R (v - (cl - β)) := hRd.differentiableAt (hDRo.mem_nhds hv')
    have hshift : DifferentiableAt ℂ (fun v : ℂ => v - (cl - β)) v :=
      differentiableAt_id.sub_const (cl - β)
    simp only [hSdef]
    exact (hR'.comp v hshift).sub_const β
  obtain ⟨W, hWmem, hWuniq, hWdiff⟩ :=
    exists_branch_abstract (S := S) (B := {z : ℂ | z.im < -y}) (R₀ := 4 * δ) (k := 1 / 2)
      (δ := 2 * δ) hR0 (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith)
      hSdiff hSval hSderiv
  -- ## 4. the two functions and their properties
  set H : ℂ → ℂ := fun z => W z - (cl - β) with hHdef
  set ρ : ℂ → ℂ := fun z => W z - z with hρdef
  have hHz_le : ∀ z : ℂ, z.im < -y → (H z).im ≤ z.im + 4 * δ - κ := by
    intro z hz
    have hW1 : W z ∈ Metric.closedBall z (4 * δ) := (hWmem z hz).1
    have h1 : (W z).im ≤ z.im + ‖W z - z‖ := by
      have h := Complex.im_le_norm (W z - z)
      rw [Complex.sub_im] at h
      linarith
    have h2 : ‖W z - z‖ ≤ 4 * δ := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hW1
      exact hW1
    have h3 : (H z).im = (W z).im - (cl - β).im := by simp only [hHdef, Complex.sub_im]
    have h4 : κ ≤ (cl - β).im := by simp only [Complex.sub_im]; exact hβ
    rw [h3]
    linarith
  have hHprop : ∀ z : ℂ, z.im < -y → (H z).im < -y ∧ H z ∈ DR ∧ R (H z) - β = z ∧
      H z = z + (β - cl) + ρ z := by
    intro z hz
    have hz' : (H z).im < -y - 3 * κ / 4 := by
      have := hHz_le z hz
      linarith [hδ4, hκ]
    have hHim : (H z).im < -y := hbelow _ hz'
    have hHDR : H z ∈ DR := hDRsub (hdeep _ hz')
    have hRHeq : R (H z) - β = z := by
      simpa only [hHdef, hSdef] using (hWmem z hz).2.1
    have heq : H z = z + (β - cl) + ρ z := by
      simp only [hHdef, hρdef]; ring
    exact ⟨hHim, hHDR, hRHeq, heq⟩
  have hHdiff : DifferentiableOn ℂ H {w : ℂ | w.im < -y} := by
    intro z hz
    simp only [hHdef]
    exact ((hWdiff z hz).sub_const (cl - β)).differentiableWithinAt
  have hρdiff : DifferentiableOn ℂ ρ {w : ℂ | w.im < -y} := by
    intro z hz
    simp only [hρdef]
    exact ((hWdiff z hz).sub differentiableAt_id).differentiableWithinAt
  have hρbd : ∀ z : ℂ, z.im < -y → ‖ρ z‖ ≤ 2 * δ := by
    intro z hz
    simp only [hρdef]
    exact (hWmem z hz).2.2
  have hρper : ∀ z : ℂ, z.im < -y → ρ (z + 1) = ρ z := by
    intro z hz
    have hz1 : (z + 1).im < -y := by simpa using hz
    have hWz1 : W z + 1 = W (z + 1) := by
      have hmem : W z + 1 ∈ Metric.closedBall (z + 1) (4 * δ) := by
        have h1 : W z ∈ Metric.closedBall z (4 * δ) := (hWmem z hz).1
        rw [Metric.mem_closedBall, dist_eq_norm] at h1 ⊢
        have h2 : W z + 1 - (z + 1) = W z - z := by ring
        rw [h2]
        exact h1
      have heq : S (W z + 1) = z + 1 := by
        have hHDR : H z ∈ DR := (hHprop z hz).2.1
        have hTeq' : R (H z + 1) = R (H z) + 1 := hTeq.2 (H z) hHDR
        have hRHeq : R (H z) - β = z := (hHprop z hz).2.2.1
        have hRHeq' : R (H z) + 1 - β = z + 1 := by
          rw [show R (H z) + 1 - β = (R (H z) - β) + 1 by ring, hRHeq]
        have hH1 : W z + 1 - (cl - β) = H z + 1 := by simp only [hHdef]; ring
        simp only [hSdef]
        rw [hH1, hTeq', hRHeq']
      exact hWuniq (z + 1) hz1 (W z + 1) hmem heq
    simp only [hρdef]
    rw [← hWz1]
    ring
  have hinj : Set.InjOn H {w : ℂ | w.im < -y} := by
    intro z hz z' hz' heq
    have h1 : R (H z) - β = z := (hHprop z hz).2.2.1
    have h2 : R (H z') - β = z' := (hHprop z' hz').2.2.1
    rw [heq] at h1
    exact h1.symm.trans h2
  have hdrift : ∀ z : ℂ, z.im < -y → (H z - z).im ≤ -(κ / 4) := by
    intro z hz
    have h1 : (H z - z).im = (H z).im - z.im := by simp
    rw [h1]
    have h2 := hHz_le z hz
    linarith [hδ4]
  -- ## 5. the limit of `ρ` at the lower end
  have hρdiffAt : ∀ z : ℂ, z.im < -y → DifferentiableAt ℂ ρ z := fun z hz =>
    (hρdiff z hz).differentiableAt ((isOpen_lt Complex.continuous_im continuous_const).mem_nhds hz)
  obtain ⟨c, hc⟩ := tendsto_atBot_of_periodic_bounded (φ := ρ) (Y := y) (B := 2 * δ)
    hρdiffAt hρper hρbd
  exact ⟨H, ρ, c, hHdiff, hHprop, hρdiff, hρper, hρbd, hdrift, hinj, hc⟩

end

end Work.L62
