import Mathlib

namespace Work.RPB.B5

/-- If `f` is continuous on `[0,∞)` and "quasi-periodic" with shift `c>0`
(`f (t+c) = f t + c`), then `f` is continuous on all of `ℝ`. -/
theorem continuous_of_continuousOn_Ici_of_quasiPeriodic {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c)
    (hf : ContinuousOn f (Set.Ici 0)) (hper : ∀ t : ℝ, f (t + c) = f t + c) :
    Continuous f := by
  -- Iterate the quasi-periodicity: `f (t + n*c) = f t + n*c`.
  have hiter : ∀ (n : ℕ) (t : ℝ), f (t + (n : ℝ) * c) = f t + (n : ℝ) * c := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ n ih =>
      intro t
      have e : ((n + 1 : ℕ) : ℝ) * c = (n : ℝ) * c + c := by push_cast; ring
      have e2 : t + ((n : ℝ) * c + c) = (t + (n : ℝ) * c) + c := by ring
      rw [e, e2, hper, ih]
      ring
  rw [continuous_iff_continuousAt]
  intro x
  -- Pick `n` with `x + n*c > 0` so that a whole neighbourhood of `x` is mapped
  -- into the half-line where we already know continuity.
  obtain ⟨n, hn⟩ := exists_nat_gt (-x / c)
  have h2 : -x < (n : ℝ) * c := (div_lt_iff₀ hc).mp hn
  have hxc : 0 < x + (n : ℝ) * c := by linarith
  have hmem : Set.Ici (0 : ℝ) ∈ nhds (x + (n : ℝ) * c) :=
    Filter.mem_of_superset (Ioi_mem_nhds hxc) Set.Ioi_subset_Ici_self
  have hcont : ContinuousAt f (x + (n : ℝ) * c) := hf.continuousAt hmem
  have hshift : ContinuousAt (fun y : ℝ => y + (n : ℝ) * c) x :=
    (continuous_id.add continuous_const).continuousAt
  have hcomp : ContinuousAt (fun y : ℝ => f (y + (n : ℝ) * c)) x :=
    hcont.comp (f := fun y : ℝ => y + (n : ℝ) * c) hshift
  have hsub : ContinuousAt (fun y : ℝ => f (y + (n : ℝ) * c) - (n : ℝ) * c) x :=
    hcomp.sub continuous_const.continuousAt
  have heq : (fun y : ℝ => f (y + (n : ℝ) * c) - (n : ℝ) * c) = f := by
    funext y
    rw [hiter n y]
    ring
  rwa [heq] at hsub

end Work.RPB.B5
