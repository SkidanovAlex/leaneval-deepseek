import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.perturbed_branch

/-!
# `Work.L62.branch_at_depth_up` — the perturbed inverse branch at depth `y` (upper end)

For every admissible perturbation `R` of the lifted horn map `d.E` on the half-plane
`{y - 1/2 < Im}` (`T`-equivariant, holomorphic on `DR ⊇ {y - 1/2 < Im}`, `δ`-close to `d.E`
there), and every `β` with `κ ≤ Im β`, there is a holomorphic inverse branch `H` of
`w ↦ R w - β` on the half-plane `{y < Im}`, whose increment `ρ = H - id - β` is holomorphic,
`1`-periodic, bounded by `2δ`, with drift `κ/4 ≤ Im (H w - w)`, with `H` injective, and with
`ρ → c` at the upper end.  The depth threshold `y₀` is uniform in `y`, `β`, `R` and `DR`; it
depends only on `d`, `hd`, `κ` and `δ`.

This is the contraction argument of `Work.L62.perturbed_branch` run with ball radius `r = 4δ`
(so that the drift `κ - r ≥ κ/4` and the increment bound `‖ρ w‖ = ‖R (H w) - H w‖ ≤ 2δ` are both
available from `δ ≤ κ/16`), directly on the half-plane at depth `y`: no model branch `H₀` is
needed, since `ParabData.E_upper` makes the correction `u ↦ d.E u - u` small on a deep
half-plane, and Cauchy's estimate on the same deep half-plane makes its derivative small too.
-/

namespace Work.L62

open MandelDim Set Metric Filter Topology
open scoped Topology

noncomputable section

theorem branch_at_depth_up {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {κ δ : ℝ} (hκ : 0 < κ) (hδ : 0 < δ)
    (hδκ : δ ≤ min (κ / 16) (1 / 8)) :
    ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ β : ℂ, κ ≤ Complex.im β →
      ∀ (R : ℂ → ℂ) (DR : Set ℂ), IsOpen DR → MandelDim.IsTEquivariantOn R DR →
        DifferentiableOn ℂ R DR → {w : ℂ | y - 1 / 2 < Complex.im w} ⊆ DR →
        (∀ w : ℂ, y - 1 / 2 < Complex.im w → ‖R w - d.E w‖ ≤ δ) →
        ∃ (H ρ : ℂ → ℂ) (c : ℂ),
          DifferentiableOn ℂ H {w : ℂ | y < Complex.im w} ∧
          (∀ w : ℂ, y < Complex.im w → y < Complex.im (H w) ∧ H w ∈ DR ∧
            R (H w) - β = w ∧ H w = w + β + ρ w) ∧
          DifferentiableOn ℂ ρ {w : ℂ | y < Complex.im w} ∧
          (∀ w : ℂ, y < Complex.im w → ρ (w + 1) = ρ w) ∧
          (∀ w : ℂ, y < Complex.im w → ‖ρ w‖ ≤ 2 * δ) ∧
          (∀ w : ℂ, y < Complex.im w → κ / 4 ≤ Complex.im (H w - w)) ∧
          Set.InjOn H {w : ℂ | y < Complex.im w} ∧
          Filter.Tendsto ρ (Filter.comap Complex.im Filter.atTop) (nhds c) := by
  classical
  have hδ₁ : δ ≤ κ / 16 := le_trans hδκ (min_le_left (κ / 16) (1 / 8))
  have hδ₂ : δ ≤ 1 / 8 := le_trans hδκ (min_le_right (κ / 16) (1 / 8))
  have h4δ : 4 * δ ≤ κ / 4 := by nlinarith [hδ₁, hκ]
  -- the depth at which the correction `E - id` is small (and, by Cauchy, flat)
  obtain ⟨R₀, hR₀⟩ := E_sub_id_small d δ hδ
  set Y_E : ℝ := max (R₀ + 2) (max (hd.η + 2) (d.η₀ + 2)) with hYEdef
  have hYE₁ : R₀ + 2 ≤ Y_E := le_max_left _ _
  have hYE₂ : hd.η + 2 ≤ Y_E := le_trans (le_max_left _ _) (le_max_right _ _)
  refine ⟨Y_E + 4 * δ + 1, ?_⟩
  intro y hy β hβ R DR hDRo hTeq hRhol hDRsub hclose
  -- ## geometry of the two half-planes
  set b₁ : ℝ := y - 1 / 2 with hb₁def
  have hb₁η : hd.η < b₁ := by rw [hb₁def]; linarith
  set Y : ℝ := max Y_E (b₁ + 8 * δ) with hYdef
  have hY₁ : Y_E ≤ Y := le_max_left _ _
  have hY₂ : b₁ + 8 * δ ≤ Y := le_max_right _ _
  have hYR : R₀ < Y := by linarith
  have hYη : hd.η < Y := by linarith
  have hYb : b₁ < Y := by linarith [hδ]
  -- the target half-plane `{y < Im}` lands strictly inside the contraction domain
  have hY_lt : Y < y + 3 * κ / 4 := by
    rw [hYdef]
    apply max_lt
    · have : Y_E < y := by linarith
      linarith
    · rw [hb₁def]; nlinarith [hκ, hδ₁]
  have hYsub : Y + κ / 4 < y + κ := by linarith
  -- the deep ball of the contraction stays deep
  have hYball : Y + 4 * δ < y + κ := by
    have h : Y < y + κ - 4 * δ := by
      rw [hYdef]
      apply max_lt
      · have : Y_E < y := by linarith
        linarith [h4δ, hκ]
      · rw [hb₁def]; nlinarith [hκ, hδ₁]
    linarith
  set Ω : Set ℂ := {u : ℂ | Y < u.im} with hΩdef
  set s : Set ℂ := {w : ℂ | Y + κ / 4 < (w + β).im} with hsdef
  have hΩopen : IsOpen Ω := by
    rw [hΩdef]; exact isOpen_lt continuous_const Complex.continuous_im
  have hsopen : IsOpen s := by
    rw [hsdef]
    exact isOpen_lt continuous_const
      (Complex.continuous_im.comp (continuous_id.add continuous_const))
  have hmemΩ : ∀ u : ℂ, u ∈ Ω ↔ Y < u.im := by intro u; rw [hΩdef]; exact Iff.rfl
  have hmems : ∀ w : ℂ, w ∈ s ↔ Y + κ / 4 < (w + β).im := by intro w; rw [hsdef]; exact Iff.rfl
  have hsub_s : {w : ℂ | y < w.im} ⊆ s := by
    intro w hw
    have hw' : y < w.im := hw
    refine (hmems w).mpr ?_
    have h1 : y + κ < (w + β).im := by rw [Complex.add_im]; linarith [hβ, hw']
    linarith [hYsub]
  -- ## `R` and `d.E` on the deep half-plane
  have hRΩ : DifferentiableOn ℂ R Ω := by
    refine hRhol.mono fun u hu => hDRsub ?_
    have h := (hmemΩ u).mp hu
    show b₁ < Complex.im u
    linarith [hYb]
  have hEΩ : DifferentiableOn ℂ d.E Ω := by
    rw [hΩdef]
    exact E_differentiableOn_horn d hd (by linarith)
  set Ψ : ℂ → ℂ := fun u => R u - u with hΨdef
  have hΨΩ : DifferentiableOn ℂ Ψ Ω := by
    rw [hΨdef]; exact hRΩ.sub differentiableOn_id
  -- ## the correction `R - E` on the base half-plane (small, and Cauchy-flat)
  have hηd : DifferentiableOn ℂ (fun z : ℂ => R z - d.E z) {z : ℂ | b₁ < z.im} :=
    (hRhol.mono fun z hz => hDRsub hz).sub (E_differentiableOn_horn d hd hb₁η)
  have hηbd : ∀ z : ℂ, b₁ < z.im → ‖R z - d.E z‖ ≤ δ := fun z hz => hclose z hz
  have hEsmall : ∀ u : ℂ, Y < u.im → ‖d.E u - u‖ < δ := fun u hu => hR₀ u (by linarith)
  -- ## the contraction data
  have hball_mem : ∀ w ∈ s, ∀ u ∈ Metric.closedBall (w + β) (4 * δ), Y < u.im := by
    intro w hw u hu
    have h1 : ‖u - (w + β)‖ ≤ 4 * δ := by
      have h := Metric.mem_closedBall.mp hu
      rwa [dist_eq_norm] at h
    have h2 := (abs_le.mp (Complex.abs_im_le_norm (u - (w + β)))).1
    rw [Complex.sub_im] at h2
    have h3 : Y + κ / 4 < (w + β).im := (hmems w).mp hw
    linarith [h4δ]
  have hΨsmall : ∀ w ∈ s, ∀ u ∈ Metric.closedBall (w + β) (4 * δ),
      ‖Ψ u‖ ≤ (1 - 1 / 2) * (4 * δ) := by
    intro w hw u hu
    have huΩ : Y < u.im := hball_mem w hw u hu
    have h1 : ‖R u - d.E u‖ ≤ δ := hclose u (by linarith [huΩ, hYb])
    have h2 : ‖d.E u - u‖ < δ := hEsmall u huΩ
    have h3 : ‖Ψ u‖ ≤ δ + δ := by
      have hsplit : Ψ u = (R u - d.E u) + (d.E u - u) := by rw [hΨdef]; ring
      rw [hsplit]
      exact (norm_add_le _ _).trans (add_le_add h1 h2.le)
    rw [hΨdef] at h3
    linarith
  have hΨderiv : ∀ w ∈ s, ∀ u ∈ Metric.closedBall (w + β) (4 * δ), ‖deriv Ψ u‖ ≤ 1 / 2 := by
    intro w hw u hu
    have huΩ : Y < u.im := hball_mem w hw u hu
    have hdη : DifferentiableAt ℂ (fun z : ℂ => R z - d.E z) u :=
      hηd.differentiableAt
        ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds
          (by show b₁ < Complex.im u; linarith [huΩ, hYb]))
    have hdE' : DifferentiableAt ℂ (fun z : ℂ => d.E z - z) u :=
      (hEΩ.differentiableAt (hΩopen.mem_nhds huΩ)).sub differentiableAt_id
    have hfun : Ψ = (fun z : ℂ => R z - d.E z) + (fun z : ℂ => d.E z - z) := by
      funext z; rw [hΨdef]; simp only [Pi.add_apply]; ring
    have hderiv : deriv Ψ u = deriv (fun z : ℂ => R z - d.E z) u +
        deriv (fun z : ℂ => d.E z - z) u := by
      rw [hfun, deriv_add hdη hdE']
    have hηderiv : ‖deriv (fun z : ℂ => R z - d.E z) u‖ ≤ δ / ((u.im - b₁) / 2) :=
      halfplane_deriv_bound (by linarith [huΩ, hYb]) hηd hηbd (by linarith)
    have hηle : δ / ((u.im - b₁) / 2) ≤ 1 / 4 := by
      have hpos : 0 < (u.im - b₁) / 2 := by linarith [huΩ, hYb]
      rw [div_le_iff₀ hpos]
      nlinarith [hδ, hY₂, huΩ, h4δ, hκ]
    have hEdiff' : DifferentiableOn ℂ (fun z : ℂ => d.E z - z) {z : ℂ | Y - 1 < z.im} :=
      (E_differentiableOn_horn d hd (by linarith)).sub differentiableOn_id
    have hEbd' : ∀ z : ℂ, Y - 1 < z.im → ‖d.E z - z‖ ≤ δ := by
      intro z hz
      have hz' : Y - 1 < z.im := hz
      exact (hR₀ z (by linarith [hYR])).le
    have hEderiv : ‖deriv (fun z : ℂ => d.E z - z) u‖ ≤ 1 / 4 := by
      have h := halfplane_deriv_bound (g := fun z : ℂ => d.E z - z) (Y := Y - 1) (B := δ) (r := 1)
        (by norm_num) hEdiff' hEbd' (by linarith)
      rw [div_one] at h
      linarith [hδ₂]
    rw [hderiv]
    refine (norm_add_le _ _).trans ?_
    linarith [hηderiv, hηle, hEderiv]
  obtain ⟨H, hHdiff, hHfix, hHuniq⟩ :=
    contraction_fixed_point_holomorphic_tmp (s := s) (Ω := Ω) (Ψ := Ψ) (β := β)
      (r := 4 * δ) (L := 1 / 2) hsopen hΩopen hΨΩ (by linarith) (by norm_num) (by norm_num)
      (fun w hw u hu => (hmemΩ u).mpr (hball_mem w hw u hu)) hΨsmall hΨderiv
  have hHmem_ball : ∀ w ∈ s, H w ∈ Metric.closedBall (w + β) (4 * δ) := fun w hw => (hHfix w hw).1
  have hH_eq : ∀ w ∈ s, R (H w) = w + β := by
    intro w hw
    have h2 : H w = w + β - Ψ (H w) := (hHfix w hw).2
    rw [hΨdef] at h2
    have h5 : H w + (R (H w) - H w) = R (H w) := by ring
    have h3 : H w + (R (H w) - H w) = w + β := by nth_rewrite 1 [h2]; ring
    rwa [h5] at h3
  have hHimeq : ∀ w ∈ s, (w + β).im - 4 * δ ≤ (H w).im := by
    intro w hw
    have h := Metric.mem_closedBall.mp (hHmem_ball w hw)
    rw [dist_eq_norm] at h
    have h2 := (abs_le.mp (Complex.abs_im_le_norm (H w - (w + β)))).1
    rw [Complex.sub_im] at h2
    linarith
  have hHDR : ∀ w ∈ s, H w ∈ DR := by
    intro w hw
    refine hDRsub ?_
    have h1 := hHimeq w hw
    have h2 : Y + κ / 4 < (w + β).im := (hmems w).mp hw
    show b₁ < Complex.im (H w)
    linarith [h4δ, hYb]
  have hs_shift : ∀ w : ℂ, w ∈ s → w + 1 ∈ s := by
    intro w hw
    refine (hmems (w + 1)).mpr ?_
    have h2 : Y + κ / 4 < (w + β).im := (hmems w).mp hw
    have h3 : (w + 1 + β).im = (w + β).im := by
      rw [show w + 1 + β = (w + β) + 1 by ring, Complex.add_im, Complex.one_im, add_zero]
    rwa [h3]
  have hHper : ∀ w ∈ s, H (w + 1) = H w + 1 := by
    intro w hw
    have hw1 : w + 1 ∈ s := hs_shift w hw
    have hu_mem : H w + 1 ∈ Metric.closedBall (w + 1 + β) (4 * δ) := by
      have h : ‖H w - (w + β)‖ ≤ 4 * δ := by
        have h := Metric.mem_closedBall.mp (hHmem_ball w hw)
        rwa [dist_eq_norm] at h
      rw [Metric.mem_closedBall, dist_eq_norm]
      have he : H w + 1 - (w + 1 + β) = H w - (w + β) := by ring
      rw [he]; exact h
    have hfixpt : H w + 1 = (w + 1) + β - Ψ (H w + 1) := by
      have hR1 : R (H w + 1) = R (H w) + 1 := hTeq.2 (H w) (hHDR w hw)
      have hRw : R (H w) = w + β := hH_eq w hw
      rw [hΨdef]
      show H w + 1 = (w + 1) + β - (R (H w + 1) - (H w + 1))
      rw [hR1, hRw]
      ring
    exact (hHuniq (w + 1) hw1 (H w + 1) hu_mem hfixpt).symm
  -- ## the increment `ρ` and the final package
  set ρ : ℂ → ℂ := fun w => H w - w - β with hρdef
  have hρhol : DifferentiableOn ℂ ρ {w : ℂ | y < w.im} := by
    have he : (fun w : ℂ => H w - w - β) = fun w : ℂ => H w - (w + β) := by funext w; ring
    rw [hρdef, he]
    exact (hHdiff.mono (fun w hw => hsub_s hw)).sub (differentiableOn_id.add_const β)
  have hρper : ∀ w : ℂ, w ∈ s → ρ (w + 1) = ρ w := by
    intro w hw
    simp only [hρdef]
    rw [hHper w hw]
    ring
  have hρbd : ∀ w : ℂ, y < w.im → ‖ρ w‖ ≤ 2 * δ := by
    intro w hw
    have hws : w ∈ s := hsub_s hw
    have h1 : ‖R (H w) - d.E (H w)‖ ≤ δ := by
      refine hclose (H w) ?_
      have h1 := hHimeq w hws
      have h2 : Y + κ / 4 < (w + β).im := (hmems w).mp hws
      linarith [h4δ, hYb]
    have h2 : ‖d.E (H w) - H w‖ < δ := by
      refine hEsmall (H w) ?_
      have h1 := hHimeq w hws
      have h2 : Y + κ / 4 < (w + β).im := (hmems w).mp hws
      linarith
    have hRw : R (H w) = w + β := hH_eq w hws
    have heq : ρ w = -(R (H w) - H w) := by
      simp only [hρdef]
      rw [hRw]; ring
    have h3 : ‖R (H w) - H w‖ ≤ δ + δ := by
      have hsplit : R (H w) - H w = (R (H w) - d.E (H w)) + (d.E (H w) - H w) := by ring
      rw [hsplit]
      exact (norm_add_le _ _).trans (add_le_add h1 h2.le)
    rw [heq, norm_neg]
    linarith
  have hdrift : ∀ w : ℂ, y < w.im → κ / 4 ≤ Complex.im (H w - w) := by
    intro w hw
    have hws : w ∈ s := hsub_s hw
    have h := Metric.mem_closedBall.mp (hHmem_ball w hws)
    rw [dist_eq_norm] at h
    have h2 := (abs_le.mp (Complex.abs_im_le_norm (H w - (w + β)))).1
    rw [Complex.sub_im] at h2
    have hb : -4 * δ ≤ Complex.im (H w - (w + β)) := by
      rw [Complex.sub_im]; linarith
    have him : Complex.im (H w - w) = Complex.im (H w - (w + β)) + Complex.im β := by
      rw [show H w - w = (H w - (w + β)) + β by ring, Complex.add_im]
    rw [him]
    linarith [hβ, h4δ, hκ]
  have hinj : Set.InjOn H {w : ℂ | y < w.im} := by
    intro w hw w' hw' heq
    have h1 : R (H w) - β = w := by rw [hH_eq w (hsub_s hw)]; ring
    have h2 : R (H w') - β = w' := by rw [hH_eq w' (hsub_s hw')]; ring
    rw [← h1, ← h2, heq]
  obtain ⟨c, M, hdecay⟩ := end_fourier (φ := ρ) (Y := y + 1) (B := 2 * δ)
    (fun w hw => hρper w (hsub_s (by
      have hw' : y + 1 ≤ Complex.im w := hw
      show y < Complex.im w
      linarith)))
    (hρhol.mono (fun w hw => by rw [Set.mem_setOf_eq] at hw ⊢; linarith))
    (fun w hw => hρbd w (by
      have hw' : y + 1 ≤ Complex.im w := hw
      linarith))
  have hlim : Tendsto ρ (Filter.comap Complex.im Filter.atTop) (nhds c) :=
    tendsto_upperEnd_of_decay hdecay
  refine ⟨H, ρ, c, ?_, ?_, hρhol, ?_, hρbd, hdrift, hinj, hlim⟩
  · exact hHdiff.mono (fun w hw => hsub_s hw)
  · intro w hw
    have hyw : y < Complex.im w := hw
    have hws : w ∈ s := hsub_s hyw
    have h2 : Y + κ / 4 < (w + β).im := (hmems w).mp hws
    have h1 := hHimeq w hws
    have h : y < (H w).im := by
      have h5 : y + κ < (w + β).im := by rw [Complex.add_im]; linarith [hβ, hyw]
      linarith [h4δ, hκ]
    refine ⟨h, hHDR w hws, ?_, ?_⟩
    · rw [hH_eq w hws]; ring
    · simp only [hρdef]; ring
  · intro w hw
    have hyw : y < Complex.im w := hw
    exact hρper w (hsub_s hyw)

end

end Work.L62
