import Mathlib
import Submission.Work.BasinSC.tower

namespace Work.BasinSC.Tower

/-- On the immediate basin `B` every iterate of `f₀` is continuous at every point of `B`: the
forward orbit of a point of `B` stays in `B ⊆ ParabolicBasin f₀ D₀`, hence in `D₀`, where `f₀` is
holomorphic.  The composition argument uses that `D₀` is open to pass from continuity on `D₀` to
continuity at the orbit points (which all lie in `D₀`). -/
lemma continuousAt_iterate_of_mem_basin {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ}
    (hF0 : MandelDim.IsF0Setup f₀ D₀ B c) {z : ℂ} (hz : z ∈ B) (n : ℕ) :
    ContinuousAt (f₀^[n]) z := by
  obtain ⟨hGerm, hBasin, -, -, -⟩ := hF0
  obtain ⟨hDopen, -, hDholo, -, -, -⟩ := hGerm
  obtain ⟨-, -, hBsub, -, hBmap, -, -⟩ := hBasin
  have hcont : ContinuousOn f₀ D₀ := hDholo.continuousOn
  -- the orbit of a point of `B` stays in `B`
  have hiterB : ∀ m : ℕ, (f₀^[m]) z ∈ B := by
    intro m
    induction m with
    | zero => simpa using hz
    | succ k ih => simpa [Function.iterate_succ_apply'] using hBmap ih
  -- hence in the parabolic basin, and therefore in `D₀`
  have hiterD : ∀ m : ℕ, (f₀^[m]) z ∈ D₀ := by
    intro m
    obtain ⟨U, hU, hUmaps, -⟩ := hBsub (hiterB m)
    simpa using hUmaps 0 (mem_of_mem_nhds hU)
  induction n with
  | zero => exact continuousAt_id
  | succ k ih =>
    have hk : ContinuousAt f₀ ((f₀^[k]) z) :=
      hcont.continuousAt (hDopen.mem_nhds (hiterD k))
    have hcomp : ContinuousAt (f₀ ∘ (f₀^[k])) z := hk.comp ih
    simpa only [Function.iterate_succ'] using hcomp

-- The levels of the tower `V n = {z | f₀^[n] z ∈ Ωp} ∩ B` are open in `ℂ`: on the basin the
-- iterates of `f₀` are continuous at every point (the orbit of a basin point stays in `B ⊆ D₀`,
-- where `f₀` is holomorphic), so the preimage of the open petal is open.
theorem tower_isOpen {f₀ : ℂ → ℂ} {D₀ B : Set ℂ} {c : ℂ} (hF0 : MandelDim.IsF0Setup f₀ D₀ B c)
    (d : MandelDim.ParabData f₀ D₀) (n : ℕ) : IsOpen (Work.BasinSC.tower f₀ B d.Ωp n) := by
  have hBopen : IsOpen B := hF0.2.1.1
  show IsOpen ({z : ℂ | (f₀^[n]) z ∈ d.Ωp} ∩ B)
  rw [isOpen_iff_mem_nhds]
  rintro z ⟨hzΩ, hzB⟩
  have hcontn : ContinuousAt (f₀^[n]) z := continuousAt_iterate_of_mem_basin hF0 hzB n
  exact Filter.inter_mem (hcontn.preimage_mem_nhds (d.Ωp_open.mem_nhds hzΩ)) (hBopen.mem_nhds hzB)

end Work.BasinSC.Tower
