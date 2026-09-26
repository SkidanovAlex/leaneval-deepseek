import Mathlib
import Submission.Work.Smooth.SphereJordan.radialModelAux
import Submission.Work.Smooth.SphereJordan.localSliceArc
import Submission.Work.Smooth.SphereJordan.sphereLocalArc

/-!
# The local structure of the frontier of a finite union of equal closed discs

Foundational definitions for the local analysis at a frontier point `x` of
`S = ⋃ w ∈ Q, closedBall w r`:

* `eicC θ` is the point of the unit circle with argument `θ`;
* `actC Q r x` is the set of *active* centres (those with `dist x w = r`);
* `mC Q r x hA u` is the radial profile `max_{w active} ⟪u, w - x⟫`:  the local model says that
  `x + ρ * u ∈ S` iff `ρ ≤ 2 * mC u` (for `0 < ρ < ε`).

From this we derive the exact description of the frontier near `x`:
`x + ρ * u ∈ frontier S ↔ ρ = 2 * mC u`.
-/

namespace Work.Smooth.SphereJordan

open Set Metric

noncomputable section

open scoped Classical

/-- The point of the unit circle with argument `θ`. -/
def eicC (θ : ℝ) : ℂ := Complex.exp ((θ : ℂ) * Complex.I)

theorem norm_eicC (θ : ℝ) : ‖eicC θ‖ = 1 := by
  rw [eicC]; exact Complex.norm_exp_ofReal_mul_I θ

theorem continuous_eicC : Continuous eicC :=
  Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

theorem eicC_add (s t : ℝ) : eicC (s + t) = eicC s * eicC t := by
  rw [eicC, eicC, eicC, ← Complex.exp_add]; congr 1; push_cast; ring

/-- The active centres: those whose boundary circle passes through `x`. -/
def actC (Q : Finset ℂ) (r : ℝ) (x : ℂ) : Finset ℂ := Q.filter (fun w => dist x w = r)

theorem mem_actC {Q : Finset ℂ} {r : ℝ} {x w : ℂ} :
    w ∈ actC Q r x ↔ w ∈ Q ∧ dist x w = r := Finset.mem_filter

/-- **At a frontier point there is an active centre.** -/
theorem actC_nonempty {Q : Finset ℂ} {r : ℝ} (hr : 0 < r) {x : ℂ}
    (hx : x ∈ frontier (⋃ w ∈ Q, Metric.closedBall w r)) : (actC Q r x).Nonempty := by
  have hSclosed : IsClosed (⋃ w ∈ Q, Metric.closedBall w r) := isClosed_ballUAux Q r
  have hxS : x ∈ ⋃ w ∈ Q, Metric.closedBall w r := hSclosed.closure_eq ▸ hx.1
  obtain ⟨w, hw, hxw⟩ := Set.mem_iUnion₂.mp hxS
  refine ⟨w, mem_actC.mpr ⟨hw, le_antisymm (Metric.mem_closedBall.mp hxw) ?_⟩⟩
  by_contra hlt
  rw [not_le] at hlt
  have hxball : x ∈ Metric.ball w r := by rw [Metric.mem_ball]; exact hlt
  exact hx.2 (interior_mono (fun y hy => Set.mem_iUnion₂.mpr ⟨w, hw, hy⟩)
    (Metric.ball_subset_interior_closedBall hxball))

/-- The radial profile `max_{w active} ⟪u, w - x⟫`. -/
def mC (Q : Finset ℂ) (r : ℝ) (x : ℂ) (hA : (actC Q r x).Nonempty) (u : ℂ) : ℝ :=
  (actC Q r x).sup' hA (fun w => (star u * (w - x)).re)

theorem le_mC {Q : Finset ℂ} {r : ℝ} {x : ℂ} {hA : (actC Q r x).Nonempty} {u : ℂ} {w : ℂ}
    (hw : w ∈ actC Q r x) : (star u * (w - x)).re ≤ mC Q r x hA u :=
  Finset.le_sup' (fun w => (star u * (w - x)).re) hw

theorem mC_achieved {Q : Finset ℂ} (r : ℝ) (x : ℂ) (hA : (actC Q r x).Nonempty) (u : ℂ) :
    ∃ w ∈ actC Q r x, mC Q r x hA u = (star u * (w - x)).re := by
  obtain ⟨w, hw, heq⟩ := Finset.exists_mem_eq_sup' hA (fun w => (star u * (w - x)).re)
  exact ⟨w, hw, heq⟩

/-- `∃ w ∈ s, a ≤ f w` is `a ≤ s.sup' f`. -/
theorem exists_le_iff_le_sup' {ι : Type*} {s : Finset ι} (h : s.Nonempty) (f : ι → ℝ) (a : ℝ) :
    (∃ i ∈ s, a ≤ f i) ↔ a ≤ s.sup' h f := by
  constructor
  · rintro ⟨i, hi, hle⟩
    exact le_trans hle (Finset.le_sup' f hi)
  · intro hle
    obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' h f
    exact ⟨i, hi, by rw [← heq]; exact hle⟩

theorem two_mul_sup' {ι : Type*} {s : Finset ι} (h : s.Nonempty) (f : ι → ℝ) :
    2 * s.sup' h f = s.sup' h (fun i => 2 * f i) := by
  refine le_antisymm ?_ ?_
  · obtain ⟨i, hi, heq⟩ := Finset.exists_mem_eq_sup' h f
    rw [heq]
    exact Finset.le_sup' (fun i => 2 * f i) hi
  · refine Finset.sup'_le h (fun i => 2 * f i) (fun i hi => ?_)
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' f hi) (by norm_num)

/-- The radial membership criterion in terms of the profile `mC`, from the raw local model. -/
theorem model_of_raw {Q : Finset ℂ} {r : ℝ} {x : ℂ} {hA : (actC Q r x).Nonempty} {ε : ℝ}
    (hraw : ∀ (u : ℂ) (ρ : ℝ), ‖u‖ = 1 → 0 < ρ → ρ < ε →
      (x + ρ * u ∈ ⋃ w ∈ Q, Metric.closedBall w r ↔
        ∃ w ∈ Q, dist x w = r ∧ ρ ≤ 2 * (star u * (w - x)).re)) :
    ∀ (u : ℂ) (ρ : ℝ), ‖u‖ = 1 → 0 < ρ → ρ < ε →
      (x + ρ * u ∈ ⋃ w ∈ Q, Metric.closedBall w r ↔ ρ ≤ 2 * mC Q r x hA u) := by
  intro u ρ hu hρ hρε
  rw [hraw u ρ hu hρ hρε]
  constructor
  · rintro ⟨w, hw, hwx, hle⟩
    exact le_trans hle (mul_le_mul_of_nonneg_left (le_mC (u := u) (mem_actC.mpr ⟨hw, hwx⟩))
      (by norm_num))
  · rintro hle
    obtain ⟨w, hwact, heq⟩ := mC_achieved (Q := Q) r x hA u
    rw [heq] at hle
    exact ⟨w, (mem_actC.mp hwact).1, (mem_actC.mp hwact).2, hle⟩

/-- The radial membership criterion in terms of the profile `mC` (existential form). -/
theorem exists_model_mC {Q : Finset ℂ} {r : ℝ} (hr : 0 < r) {x : ℂ}
    (hx : x ∈ frontier (⋃ w ∈ Q, Metric.closedBall w r)) :
    ∃ ε > 0, ∀ (u : ℂ) (ρ : ℝ), ‖u‖ = 1 → 0 < ρ → ρ < ε →
      (x + ρ * u ∈ ⋃ w ∈ Q, Metric.closedBall w r ↔
        ρ ≤ 2 * mC Q r x (actC_nonempty hr hx) u) := by
  obtain ⟨ε, hε, hraw⟩ := localRadialModelAux hr hx
  exact ⟨ε, hε, model_of_raw (hA := actC_nonempty hr hx) hraw⟩

/-- The algebraic identity behind the strict criterion: if `dist x w = r` then
`‖x + ρ * u - w‖ ^ 2 = r ^ 2 - 2 * ρ * (star u * (w - x)).re + ρ ^ 2`. -/
theorem norm_sq_profile {x w u : ℂ} {r ρ : ℝ} (hwx : dist x w = r) (hu : ‖u‖ = 1) (hρ : 0 < ρ) :
    ‖x + ρ * u - w‖ ^ 2 = r ^ 2 - 2 * ρ * (star u * (w - x)).re + ρ ^ 2 := by
  have hnorm : ‖x - w‖ = r := by rw [← dist_eq_norm]; exact hwx
  have hinner : inner ℝ (x - w) u = - (star u * (w - x)).re := by
    rw [real_inner_comm, Complex.inner]
    simp only [starRingEnd_apply]
    have h2 : (x - w) * star u = -(star u * (w - x)) := by ring
    rw [h2]; simp
  have hu1 : ‖(((ρ:ℝ):ℂ) * u)‖ = ρ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρ, hu, mul_one]
  have h1 : x + ρ * u - w = (x - w) + ρ * u := by ring
  rw [h1, norm_add_sq_real, hnorm, hu1,
      show inner ℝ (x - w) (((ρ:ℝ):ℂ) * u) = ρ * inner ℝ (x - w) u from by
        rw [show ((ρ:ℝ):ℂ) * u = ρ • u from rfl, real_inner_smul_right],
      hinner]
  ring

/-- **The strict criterion**: below the profile the point is interior. -/
theorem lt_mC_interior {Q : Finset ℂ} {r : ℝ} {x : ℂ} {hA : (actC Q r x).Nonempty}
    {u : ℂ} {ρ : ℝ} (hu : ‖u‖ = 1) (hρ0 : 0 < ρ)
    (h : ρ < 2 * mC Q r x hA u) :
    x + ρ * u ∈ interior (⋃ w ∈ Q, Metric.closedBall w r) := by
  obtain ⟨w, hwact, heq⟩ := mC_achieved (Q := Q) r x hA u
  have hwlt : ρ < 2 * (star u * (w - x)).re := by rw [heq] at h; linarith
  have hwx : dist x w = r := (mem_actC.mp hwact).2
  have hr0 : 0 ≤ r := hwx ▸ dist_nonneg
  have hquad := norm_sq_profile (x := x) (w := w) (u := u) (ρ := ρ) hwx hu hρ0
  have hsq : ‖x + ρ * u - w‖ ^ 2 < r ^ 2 := by
    have h2 : ρ * ρ < ρ * (2 * (star u * (w - x)).re) := mul_lt_mul_of_pos_left hwlt hρ0
    nlinarith [hquad, h2]
  have hlt : ‖x + ρ * u - w‖ < r := by
    nlinarith [hsq, norm_nonneg (x + ρ * u - w), hr0]
  have hball : x + ρ * u ∈ Metric.ball w r := by
    rw [Metric.mem_ball]; rwa [dist_eq_norm]
  exact interior_mono (fun y hy => Set.mem_iUnion₂.mpr ⟨w, (mem_actC.mp hwact).1, hy⟩)
    (Metric.ball_subset_interior_closedBall hball)

/-- **Above the profile the point is not interior** (points further out on the ray are outside
`S`). -/
theorem eq_mC_not_interior {Q : Finset ℂ} {r : ℝ} {x : ℂ} {hA : (actC Q r x).Nonempty} {ε : ℝ}
    (hmodel : ∀ (u : ℂ) (ρ : ℝ), ‖u‖ = 1 → 0 < ρ → ρ < ε →
      (x + ρ * u ∈ ⋃ w ∈ Q, Metric.closedBall w r ↔ ρ ≤ 2 * mC Q r x hA u))
    {u : ℂ} {ρ : ℝ} (hu : ‖u‖ = 1) (hρ0 : 0 < ρ) (hρε : ρ < ε)
    (heq : ρ = 2 * mC Q r x hA u) :
    x + ρ * u ∉ interior (⋃ w ∈ Q, Metric.closedBall w r) := by
  intro hint
  obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp isOpen_interior (x + ρ * u) hint
  set ρ' : ℝ := min (ρ + δ / 2) ((ρ + ε) / 2) with hρ'def
  have hρ'ρ : ρ < ρ' := by
    rw [hρ'def]; exact lt_min (by linarith) (by linarith)
  have hρ'ε : ρ' < ε := by
    rw [hρ'def]; exact lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hnotS : x + ρ' * u ∉ ⋃ w ∈ Q, Metric.closedBall w r := by
    rw [hmodel u ρ' hu (lt_trans hρ0 hρ'ρ) hρ'ε]
    rw [heq] at hρ'ρ
    exact not_le.mpr hρ'ρ
  have hmem : x + ρ' * u ∈ Metric.ball (x + ρ * u) δ := by
    rw [Metric.mem_ball, dist_eq_norm]
    have he : x + ρ' * u - (x + ρ * u) = ((ρ' - ρ : ℝ) : ℂ) * u := by push_cast; ring
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), hu, mul_one]
    have h1 : ρ' - ρ ≤ δ / 2 := by
      rw [hρ'def]
      linarith [min_le_left (ρ + δ / 2) ((ρ + ε) / 2)]
    linarith
  exact hnotS (interior_subset (hδ hmem))

/-- **The frontier is the graph of the profile.** -/
theorem frontier_iff_eq_mC {Q : Finset ℂ} {r : ℝ} {x : ℂ} {hA : (actC Q r x).Nonempty} {ε : ℝ}
    (hmodel : ∀ (u : ℂ) (ρ : ℝ), ‖u‖ = 1 → 0 < ρ → ρ < ε →
      (x + ρ * u ∈ ⋃ w ∈ Q, Metric.closedBall w r ↔ ρ ≤ 2 * mC Q r x hA u))
    {u : ℂ} {ρ : ℝ} (hu : ‖u‖ = 1) (hρ0 : 0 < ρ) (hρε : ρ < ε) :
    x + ρ * u ∈ frontier (⋃ w ∈ Q, Metric.closedBall w r) ↔ ρ = 2 * mC Q r x hA u := by
  have hclosed : IsClosed (⋃ w ∈ Q, Metric.closedBall w r) := isClosed_ballUAux Q r
  constructor
  · intro hmem
    have hS : x + ρ * u ∈ ⋃ w ∈ Q, Metric.closedBall w r := hclosed.closure_eq ▸ hmem.1
    have hle : ρ ≤ 2 * mC Q r x hA u := (hmodel u ρ hu hρ0 hρε).mp hS
    have hge : ¬ (ρ < 2 * mC Q r x hA u) := fun hlt =>
      hmem.2 (lt_mC_interior hu hρ0 hlt)
    exact le_antisymm hle (not_lt.mp hge)
  · intro heq
    refine ⟨?_, ?_⟩
    · rw [hclosed.closure_eq]
      exact (hmodel u ρ hu hρ0 hρε).mpr (le_of_eq heq)
    · exact eq_mC_not_interior hmodel hu hρ0 hρε heq

/-- **`mC` in angular form**: the profile is the sup of `r cos (arg (w - x) - θ)` over the
active centres. -/
theorem mC_eicC {Q : Finset ℂ} {r : ℝ} {x : ℂ} (hA : (actC Q r x).Nonempty) (θ : ℝ) :
    mC Q r x hA (eicC θ)
      = (actC Q r x).sup' hA (fun w => r * Real.cos (Complex.arg (w - x) - θ)) := by
  rw [mC]
  refine Finset.sup'_congr hA rfl (fun w hw => ?_)
  simp only [eicC]
  have hwx : dist x w = r := (mem_actC.mp hw).2
  have hnorm : ‖w - x‖ = r := by rw [← dist_eq_norm, dist_comm]; exact hwx
  rw [re_star_exp_I_mul, hnorm]

end

end Work.Smooth.SphereJordan
