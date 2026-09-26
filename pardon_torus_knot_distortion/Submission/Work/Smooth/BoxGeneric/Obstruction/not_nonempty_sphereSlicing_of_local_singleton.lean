import Mathlib
import Submission.Work.InnermostDisk.Slicing
import Submission.Work.CoreTopology.Basic

namespace Work.Smooth.BoxGeneric.Obstruction

open LeanEval.KnotTheory.PardonDistortion
open Set

/-- **A slicing is incompatible with an isolated point of `S ∩ F`.**

If `y` is a point of `S ∩ F` whose intersection with `S ∩ F` is locally just `{y}`, then `S`
admits no PL slicing by `F`.

Indeed, `SphereSlicing.covers` applied to the constant loop at `y` (which lies in `S ∩ F`)
produces a component loop `c i` of the slicing that passes through `y`.  That loop lies in
`S ∩ F` and is simple, hence non-constant; but the local-singleton hypothesis forces
`(c i).γ ⁻¹' {y}` to be clopen in `ℝ`, so by connectedness of `ℝ` the loop is constant — a
contradiction. -/
theorem not_nonempty_sphereSlicing_of_local_singleton {P : Work.CoreTopology.ParamTorus} {S : Set LeanEval.KnotTheory.PardonDistortion.R3} {y : LeanEval.KnotTheory.PardonDistortion.R3} (hyS : y ∈ S) (hyc : y ∈ P.carrier) (hloc : ∃ U : Set LeanEval.KnotTheory.PardonDistortion.R3, IsOpen U ∧ y ∈ U ∧ U ∩ (S ∩ P.carrier) = {y}) : ¬ Nonempty (Work.InnermostDisk.SphereSlicing P S) := by
  rintro ⟨h⟩
  obtain ⟨U, hUopen, hyU, hUeq⟩ := hloc
  -- the constant loop at `y` lies in `S`, so it is contained in one component of the slicing
  obtain ⟨i, hi⟩ := h.covers (Work.InnermostDisk.constCurve P y hyc) (fun _ => hyS)
  have hyi : y ∈ Set.range (h.c i).γ := hi (by simp)
  obtain ⟨t₀, ht₀⟩ := hyi
  -- the preimage of `{y}` is that of the open neighbourhood `U`
  have hpre : (h.c i).γ ⁻¹' {y} = (h.c i).γ ⁻¹' U := by
    apply Set.Subset.antisymm
    · intro t ht
      simp only [Set.mem_preimage] at ht ⊢
      rw [ht]; exact hyU
    · intro t ht
      simp only [Set.mem_preimage] at ht ⊢
      have hmem : (h.c i).γ t ∈ U ∩ (S ∩ P.carrier) :=
        ⟨ht, h.mem i t, (h.c i).mem t⟩
      rw [hUeq] at hmem
      simpa using hmem
  have hclopen : IsClopen ((h.c i).γ ⁻¹' {y}) := by
    refine ⟨isClosed_singleton.preimage (h.c i).cont, ?_⟩
    rw [hpre]; exact hUopen.preimage (h.c i).cont
  have hne : ((h.c i).γ ⁻¹' {y}).Nonempty := ⟨t₀, by simpa using ht₀⟩
  have huniv : (h.c i).γ ⁻¹' {y} = Set.univ := hclopen.eq_univ hne
  -- so the loop is constant ...
  have hconst : ∀ t, (h.c i).γ t = y := by
    intro t
    have : t ∈ (h.c i).γ ⁻¹' {y} := by rw [huniv]; trivial
    simpa using this
  -- ... contradicting simplicity of the component
  have hsimple : Set.InjOn (h.c i).γ (Set.Ico 0 (2 * Real.pi)) := h.simple i
  have h0 : (0 : ℝ) ∈ Set.Ico 0 (2 * Real.pi) := ⟨le_refl 0, by positivity⟩
  have h1 : Real.pi ∈ Set.Ico 0 (2 * Real.pi) := ⟨Real.pi_pos.le, by linarith [Real.pi_pos]⟩
  have heq : (0 : ℝ) = Real.pi := hsimple h0 h1 (by rw [hconst 0, hconst Real.pi])
  linarith [Real.pi_pos]

end Work.Smooth.BoxGeneric.Obstruction
