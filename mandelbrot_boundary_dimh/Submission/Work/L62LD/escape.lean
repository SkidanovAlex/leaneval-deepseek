import Mathlib
import Submission.Work.L62LD.cyl_family

/-!
# L62LD — joint continuity, escape and uniform escape for the lower-end cylinder family

Given a provider `HD : ∀ β, AvailableDown d hd β → HeadData d hd cl β` (see
`Submission/Work/L62LD/cyl_family.lean`), this file builds the family
`HB β = (HD β _).H` (value `0` off the available set) and proves

* `Work.L62LD.HB_continuousOn` — joint continuity on the available box × `lowOmega`
  (`Work.L62.cont_family_of_selfmap` with `g ζ = τ₀ (pushdown d.E (τ₀ ζ))`, `c β = π (-β)`;
  `g`'s holomorphy and `g'(0) ≠ 0` come from `Work.L62.tau0_pushdown_holo_deriv`);
* `Work.L62LD.HB_escape` — the per-`β` escape (`Work.L62C.escape_of_selfmap`: `H` is holomorphic,
  a self-map of the bounded preconnected `lowOmega`, fixes `0`, is injective and has
  `‖deriv H 0‖ = ‖π (cl - β)‖ = e^{-2π (cl - β).im} < 1` by `Work.L62.avail_down`);
* `Work.L62LD.HB_uniform_escape` — a single step count `J` for all `β` in the box
  (`Work.L62.uniform_escape2` with the contraction supplied by
  `Work.L62.lowBall_contraction`).
-/

namespace Work.L62LD

open Classical MandelDim Set Filter Topology
open scoped Topology

noncomputable section

variable {g₀ : ℂ → ℂ} {D : Set ℂ}

/-- The parameter set of the lower-end head: the `β`-box of Lemma 6.2 intersected with
`AvailableDown`. -/
def downBox (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d) (b : ℝ) : Set ℂ :=
  {β : ℂ | 0 ≤ β.re ∧ β.re ≤ 1 ∧ |β.im| ≤ b} ∩ {β : ℂ | Work.L62.AvailableDown d hd β}

theorem isCompact_downBox (d : MandelDim.ParabData g₀ D) (hd : MandelDim.HornData d) (b : ℝ) :
    IsCompact (downBox d hd b) :=
  Work.L62.availableDown_box d hd

/-- The family of reflected pushdowns attached to a provider, with the junk value `0` off the
available set. -/
def HB {d : MandelDim.ParabData g₀ D} {hd : MandelDim.HornData d} {cl : ℂ}
    (HD : ∀ β : ℂ, Work.L62.AvailableDown d hd β → HeadData d hd cl β) (β : ℂ) : ℂ → ℂ :=
  if h : Work.L62.AvailableDown d hd β then (HD β h).H else 0

theorem HB_apply {d : MandelDim.ParabData g₀ D} {hd : MandelDim.HornData d} {cl : ℂ}
    {HD : ∀ β : ℂ, Work.L62.AvailableDown d hd β → HeadData d hd cl β} {β : ℂ}
    (h : Work.L62.AvailableDown d hd β) : HB HD β = (HD β h).H := by
  simp only [HB]; rw [dite_eq_left h]

/-- **Joint continuity of the lower-end cylinder family** on `downBox × lowOmega`. -/
theorem HB_continuousOn {d : MandelDim.ParabData g₀ D} {hd : MandelDim.HornData d} {cl : ℂ}
    {b : ℝ} (HD : ∀ β : ℂ, Work.L62.AvailableDown d hd β → HeadData d hd cl β)
    (hcl : Filter.Tendsto (fun w => d.E w - w) MandelDim.lowerEnd (nhds cl)) :
    ContinuousOn (fun p : ℂ × ℂ => HB HD p.1 p.2)
      (downBox d hd b ×ˢ Work.L62.lowOmega d hd) := by
  have hΛc : IsCompact (downBox d hd b) := isCompact_downBox d hd b
  obtain ⟨hgder, hgdiff⟩ := Work.L62.tau0_pushdown_holo_deriv d hd hcl
  have hg0 : (fun ζ : ℂ => MandelDim.tau0 (MandelDim.pushdown d.E (MandelDim.tau0 ζ))) 0 = 0 := by
    simp [MandelDim.tau0, MandelDim.pushdown]
  have hpi : Continuous MandelDim.piExp := by unfold MandelDim.piExp; fun_prop
  refine Work.L62.cont_family_of_selfmap (Ω := Work.L62.lowOmega d hd) (Λ := downBox d hd b)
    (g := fun ζ : ℂ => MandelDim.tau0 (MandelDim.pushdown d.E (MandelDim.tau0 ζ)))
    (H := HB HD) (c := fun β : ℂ => MandelDim.piExp (-β))
    (Work.L62.isOpen_lowOmega d hd) (Work.L62.isBounded_lowOmega d hd)
    (Work.L62.isPreconnected_lowOmega d hd) (Work.L62.zero_mem_lowOmega d hd) hΛc hgdiff hg0 ?_ ?_ ?_ ?_ ?_ ?_
  · -- `deriv g 0 ≠ 0` : `g'(0) = π (-cl)`
    rw [hgder.deriv]
    exact Work.Horn.MandelDim.piExp_ne_zero _
  · -- continuity of `β ↦ π (-β)`
    exact hpi.continuousOn.comp continuous_neg.continuousOn (fun β _ => Set.mem_univ _)
  · -- holomorphy of each member
    intro β hβ
    rw [HB_apply (HD := HD) hβ.2]
    exact (HD β hβ.2).H_holo
  · -- each member maps `lowOmega` into itself
    intro β hβ
    rw [HB_apply (HD := HD) hβ.2]
    exact (HD β hβ.2).H_map
  · -- each member fixes `0`
    intro β hβ
    rw [HB_apply (HD := HD) hβ.2]
    exact (HD β hβ.2).H_zero
  · -- the section relation
    intro β hβ ζ hζ
    rw [HB_apply (HD := HD) hβ.2]
    exact (HD β hβ.2).H_rel ζ hζ

/-- **The per-`β` escape.**  For `AvailableDown β` the iterates of `H β` converge to `0` uniformly
on every compact subset of `lowOmega`. -/
theorem HB_escape {d : MandelDim.ParabData g₀ D} {hd : MandelDim.HornData d} {cl : ℂ}
    {HD : ∀ β : ℂ, Work.L62.AvailableDown d hd β → HeadData d hd cl β} {β : ℂ}
    (hcl : Filter.Tendsto (fun w => d.E w - w) MandelDim.lowerEnd (nhds cl))
    (hβ : Work.L62.AvailableDown d hd β) :
    ∀ δ : ℝ, 0 < δ → ∀ S : Set ℂ, S ⊆ Work.L62.lowOmega d hd → IsCompact S →
      ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ S, ((HB HD β)^[n]) z ∈ Metric.ball 0 δ := by
  have hHB : HB HD β = (HD β hβ).H := HB_apply (HD := HD) hβ
  have hnorm : ‖deriv (HB HD β) 0‖ < 1 := by
    have hlt : β.im < cl.im := Work.L62.avail_down d hd hcl hβ
    rw [hHB, (HD β hβ).H_deriv.deriv, Work.L62.norm_piExp_lowBall, Complex.sub_im]
    rw [Real.exp_lt_one_iff]
    nlinarith [Real.pi_pos]
  refine Work.L62C.escape_of_selfmap (Ω := Work.L62.lowOmega d hd)
    (Work.L62.isOpen_lowOmega d hd) (Work.L62.isBounded_lowOmega d hd)
    (Work.L62.isPreconnected_lowOmega d hd) (Work.L62.zero_mem_lowOmega d hd)
    (F := HB HD β) ?_ ?_ ?_ ?_ hnorm
  · rw [hHB]; exact (HD β hβ).H_holo
  · rw [hHB]; exact (HD β hβ).H_map
  · rw [hHB]; exact (HD β hβ).H_zero
  · rw [hHB]; exact (HD β hβ).H_inj

/-- **A single uniform step count.**  On the available box with drift `κ > 0` (`β.im ≤ cl.im - κ`)
all members of the family reach the ball `ball 0 eps` from any fixed compact
`K ⊆ lowOmega` within the same number of steps. -/
theorem HB_uniform_escape {d : MandelDim.ParabData g₀ D} {hd : MandelDim.HornData d} {cl : ℂ}
    {b κ eps : ℝ} {HD : ∀ β : ℂ, Work.L62.AvailableDown d hd β → HeadData d hd cl β}
    (hcl : Filter.Tendsto (fun w => d.E w - w) MandelDim.lowerEnd (nhds cl))
    (hκ : 0 < κ) (hκb : ∀ β ∈ downBox d hd b, β.im ≤ cl.im - κ)
    {K : Set ℂ} (hKc : IsCompact K) (hK : K ⊆ Work.L62.lowOmega d hd) (heps : 0 < eps) :
    ∃ J : ℕ, ∀ β ∈ downBox d hd b, ∀ n ≥ J, ∀ z ∈ K,
      ((HB HD β)^[n]) z ∈ Metric.ball 0 eps := by
  obtain ⟨r₀, hr₀, hcontr₀⟩ := Work.L62.lowBall_contraction (H := HB HD) d hd hκ hκb
    (fun β hβ => by rw [HB_apply (HD := HD) hβ.2]; exact (HD β hβ.2).H_holo)
    (fun β hβ => by rw [HB_apply (HD := HD) hβ.2]; exact (HD β hβ.2).H_map)
    (fun β hβ => by rw [HB_apply (HD := HD) hβ.2]; exact (HD β hβ.2).H_zero)
    (fun β hβ => by rw [HB_apply (HD := HD) hβ.2]; exact (HD β hβ.2).H_deriv.deriv)
  set r : ℝ := min r₀ (Real.exp (-(2 * Real.pi * hd.η)) / 2) with hrdef
  have hr : 0 < r := lt_min hr₀ (by positivity)
  have hrΩ : Metric.ball 0 r ⊆ Work.L62.lowOmega d hd :=
    (Metric.ball_subset_ball (min_le_right _ _)).trans
      ((Metric.ball_subset_ball (by linarith [Real.exp_pos (-(2 * Real.pi * hd.η))])).trans
        (Work.L62.ball_subset_lowOmega d hd))
  have hcontr : ∀ β ∈ downBox d hd b, ∀ w ∈ Metric.ball 0 r,
      ‖HB HD β w‖ ≤ (1 / 2 + Real.exp (-(2 * Real.pi * κ)) / 2) * ‖w‖ := by
    intro β hβ w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    exact hcontr₀ β hβ w (le_trans (le_of_lt hw) (min_le_left _ _))
  refine Work.L62.uniform_escape2 (Work.L62.isOpen_lowOmega d hd) (isCompact_downBox d hd b) hKc hK
    hr hrΩ (by positivity) ?_ heps ?_ hcontr ?_ ?_
  · -- `μ < 1`
    have hlt1 : Real.exp (-(2 * Real.pi * κ)) < 1 := by
      rw [Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, hκ]
    linarith
  · intro β hβ
    rw [HB_apply (HD := HD) hβ.2]
    exact (HD β hβ.2).H_map
  · -- joint continuity
    exact HB_continuousOn HD hcl
  · -- per-`β` escape on the fixed compact
    intro β hβ z hz
    obtain ⟨n, hn⟩ := HB_escape (HD := HD) hcl hβ.2 r hr K hK hKc
    exact ⟨n, hn n le_rfl z hz⟩

end

end Work.L62LD
