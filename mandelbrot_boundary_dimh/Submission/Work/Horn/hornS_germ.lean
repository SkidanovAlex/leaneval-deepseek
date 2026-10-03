import Mathlib
import Submission.Work.Horn.horn_chart

/-!
# The germ of the inverted horn section at `u = 0`

`hornS s` is the transfer of a section `s` of the horn map to the inverted chart
`u = e^{-2πiw}`.  If `s w = w - cl + o(1)` as `w` escapes to the *lower* end
(`w.im → -∞`) and `D` contains a lower half-plane, then the lower lift
`u ↦ w(u) = -(log u)/(2πi)` of `u ∈ ℂ*` escapes to the lower end as `u → 0`, and

`hornS s u / u = π(cl) + o(1)`,

i.e. `Ŝ(u)/u → e^{2πi cl}`.  This is the germ that removes the singularity of `Ŝ`
at the puncture `0` (the derivative of `Ŝ` at `0` is `e^{2πi cl}`).
-/

namespace Work.Horn

noncomputable section
open MandelDim Filter Topology Metric Set
open scoped Topology

/-- The lower lift of `u ≠ 0` to the `w`-plane: `w = -(log u)/(2πi)`.  It satisfies
`π w = 1/u` and escapes to the lower end `w.im → -∞` as `u → 0`. -/
def hornS_lift (u : ℂ) : ℂ := -(Complex.log u / (2 * Real.pi * Complex.I))

theorem piExp_add_germ (a b : ℂ) :
    MandelDim.piExp (a + b) = MandelDim.piExp a * MandelDim.piExp b := by
  rw [MandelDim.piExp, MandelDim.piExp, MandelDim.piExp,
    show 2 * ↑Real.pi * Complex.I * (a + b) =
      2 * ↑Real.pi * Complex.I * a + 2 * ↑Real.pi * Complex.I * b by ring,
    Complex.exp_add]

theorem piExp_neg_germ (x : ℂ) : MandelDim.piExp (-x) = 1 / MandelDim.piExp x := by
  have h : 2 * (Real.pi : ℂ) * Complex.I * (-x) = -(2 * (Real.pi : ℂ) * Complex.I * x) := by
    ring
  rw [one_div, MandelDim.piExp, MandelDim.piExp, h, Complex.exp_neg]

theorem piExp_hornS_lift {u : ℂ} (hu : u ≠ 0) :
    MandelDim.piExp (hornS_lift u) = 1 / u := by
  rw [hornS_lift, piExp_neg_germ, Work.Horn.MandelDim.piExp_log_div u hu]

theorem hornS_div_lift (s : ℂ → ℂ) {u : ℂ} (hu : u ≠ 0) :
    hornS s u / u = MandelDim.piExp (-(s (hornS_lift u) - hornS_lift u)) := by
  have h1 : hornS s u = MandelDim.piExp (-(s (hornS_lift u))) := by
    simp [hornS, hornS_lift, hu]
  rw [h1, div_eq_mul_one_div, ← piExp_hornS_lift hu, ← piExp_add_germ]
  congr 1
  ring

/-- **The germ of the inverted horn section at the puncture.**

If `D` contains the lower half-plane `{Im < -η}` and the section `s` is asymptotic to
`w - cl` at the lower end of `D`, then the descended section `Ŝ = hornS s` satisfies
`Ŝ(u)/u → π(cl) = e^{2πi cl}` as `u → 0`, `u ≠ 0`. -/
theorem hornS_germ {s : ℂ → ℂ} {D : Set ℂ} {cl : ℂ} {η : ℝ}
    (hlow : {w : ℂ | w.im < -η} ⊆ D)
    (hasymp : ∀ ε > 0, ∃ R : ℝ, ∀ w ∈ D, w.im < R → ‖s w - (w - cl)‖ < ε) :
    Filter.Tendsto (fun u : ℂ => Work.Horn.hornS s u / u)
      (nhdsWithin (0 : ℂ) {(0 : ℂ)}ᶜ) (nhds (MandelDim.piExp cl)) := by
  -- the lower lift escapes to the lower end
  have hlog : ∀ a : ℝ, ∀ᶠ u : ℂ in nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ),
      a ≤ (Complex.log u / (2 * (Real.pi : ℂ) * Complex.I)).im := by
    intro a
    have h := Work.Horn.MandelDim.tendsto_log_div_upperEnd
    rw [MandelDim.upperEnd, Filter.tendsto_comap_iff, Filter.tendsto_atTop] at h
    exact h a
  have hVle : ∀ R : ℝ, ∀ᶠ u : ℂ in nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ),
      (hornS_lift u).im ≤ R := by
    intro R
    filter_upwards [hlog (-R)] with u hu
    have hvv : (hornS_lift u).im
        = -(Complex.log u / (2 * (Real.pi : ℂ) * Complex.I)).im := by
      simp [hornS_lift]
    rw [hvv]; linarith
  have hVmem : ∀ᶠ u : ℂ in nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ), hornS_lift u ∈ D := by
    filter_upwards [hVle (-η - 1)] with u hu
    have hmem : (hornS_lift u).im < -η := by linarith
    exact hlow hmem
  -- the asymptotic expansion of `s` at the lower end
  have hg : Filter.Tendsto (fun u : ℂ => s (hornS_lift u) - hornS_lift u)
      (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ)) (nhds (-cl)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨R, hR⟩ := hasymp ε hε
    filter_upwards [hVmem, hVle (R - 1)] with u huD huR
    have hlt : (hornS_lift u).im < R := by linarith
    have h := hR (hornS_lift u) huD hlt
    have heq : s (hornS_lift u) - hornS_lift u - (-cl)
        = s (hornS_lift u) - (hornS_lift u - cl) := by ring
    rw [dist_eq_norm, heq]
    exact h
  have hkey : ∀ᶠ u : ℂ in nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ),
      hornS s u / u = MandelDim.piExp (-(s (hornS_lift u) - hornS_lift u)) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hornS_div_lift s (by simpa using hu)
  have hcont : Continuous (fun z : ℂ => MandelDim.piExp (-z)) := by
    simp only [MandelDim.piExp]
    fun_prop
  have hpi : Filter.Tendsto (fun u : ℂ => MandelDim.piExp (-(s (hornS_lift u) - hornS_lift u)))
      (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ)) (nhds (MandelDim.piExp cl)) := by
    have h2 : Filter.Tendsto
        (fun u : ℂ => MandelDim.piExp (-(s (hornS_lift u) - hornS_lift u)))
        (nhdsWithin (0 : ℂ) ({(0 : ℂ)}ᶜ)) (nhds (MandelDim.piExp (-(-cl)))) :=
      (hcont.tendsto (-cl)).comp hg
    rw [neg_neg] at h2
    exact h2
  exact (Filter.tendsto_congr' hkey).2 hpi

end

end Work.Horn
