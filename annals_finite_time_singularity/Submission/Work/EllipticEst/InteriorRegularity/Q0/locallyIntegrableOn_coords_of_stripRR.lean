/-
Local integrability on the strip `stripE ⊆ E2` of the coordinate pull-back `x ↦ g (x 0, x 1)`, from
local integrability of `g` on the half-strip `univ ×ˢ (0,π/2)`.

The coordinate identification `Φ p = coords p.1 p.2` (i.e. `(s,θ) ↦ s • e0 + θ • e1`) is a
measure-preserving measurable embedding; the change of variables formula
`MeasureTheory.MeasurePreserving.integrableOn_comp_preimage` then transfers integrability.  In
concrete terms, for a compact `K ⊆ stripE` the preimage `Φ ⁻¹' K` lies in the compact rectangle
`A ×ˢ B`, where `A = (· 0) '' K`, `B = (· 1) '' K ⊆ (0,π/2)`, on which `g` is integrable by
hypothesis.
-/
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.EllipticEst.InteriorRegularity.VT.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.EllipticEst.InteriorRegularity.Q0

open MeasureTheory Set Filter
open scoped Topology

theorem locallyIntegrableOn_coords_of_stripRR {g : ℝ × ℝ → ℂ}
    (hg : MeasureTheory.LocallyIntegrableOn g (Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2))) :
    MeasureTheory.LocallyIntegrableOn
      (fun x : Work.EllipticEst.InteriorRegularity.E2 => g (x 0, x 1))
      Work.EllipticEst.InteriorRegularity.stripE := by
  -- the coordinate identification `(s,θ) ↦ s • e0 + θ • e1` is measure preserving and an embedding
  have hmp : MeasurePreserving (fun p : ℝ × ℝ => coords p.1 p.2)
      (volume : Measure (ℝ × ℝ)) (volume : Measure E2) :=
    Work.EllipticEst.InteriorRegularity.VT.coords_measurePreserving
  have hme : MeasurableEmbedding (fun p : ℝ × ℝ => coords p.1 p.2) :=
    Work.EllipticEst.InteriorRegularity.VT.coords_measurableEmbedding
  rw [MeasureTheory.locallyIntegrableOn_iff
    (Work.EllipticEst.InteriorRegularity.VT.isOpen_stripE).isLocallyClosed]
  intro K hKsub hKc
  -- the coordinate projections of the compact set `K` bound the preimage of `K`
  set A : Set ℝ := (fun x : E2 => x 0) '' K with hA
  set B : Set ℝ := (fun x : E2 => x 1) '' K with hB
  have hAcont : Continuous fun x : E2 => x 0 :=
    PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) (0 : Fin 2)
  have hBcont : Continuous fun x : E2 => x 1 :=
    Work.EllipticEst.InteriorRegularity.VT.continuous_coord_one
  have hAc : IsCompact A := hKc.image hAcont
  have hBc : IsCompact B := hKc.image hBcont
  have hABsub : A ×ˢ B ⊆ Set.univ ×ˢ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    refine ⟨trivial, ?_⟩
    rw [hB] at hb
    obtain ⟨x, hxK, hxb⟩ := hb
    rw [← hxb]
    exact hKsub hxK
  have hIntAB : IntegrableOn g (A ×ˢ B) :=
    hg.integrableOn_compact_subset hABsub (hAc.prod hBc)
  -- the preimage of `K` under the coordinate map lies in that rectangle
  have hPre : (fun p : ℝ × ℝ => coords p.1 p.2) ⁻¹' K ⊆ A ×ˢ B := by
    intro p hp
    have hp' : (fun p : ℝ × ℝ => coords p.1 p.2) p ∈ K := hp
    refine ⟨?_, ?_⟩
    · rw [hA]
      exact ⟨coords p.1 p.2, hp', Work.EllipticEst.InteriorRegularity.VT.coords_zero p.1 p.2⟩
    · rw [hB]
      exact ⟨coords p.1 p.2, hp', Work.EllipticEst.InteriorRegularity.VT.coords_one p.1 p.2⟩
  have hIntPre : IntegrableOn g ((fun p : ℝ × ℝ => coords p.1 p.2) ⁻¹' K) :=
    hIntAB.mono_set hPre
  -- the pull-back of `g` along the coordinate map is `g` itself
  have hcomp : (fun x : E2 => g (x 0, x 1)) ∘ (fun p : ℝ × ℝ => coords p.1 p.2) = g := by
    funext p
    obtain ⟨a, b⟩ := p
    exact congrArg g (Prod.ext (Work.EllipticEst.InteriorRegularity.VT.coords_zero a b)
      (Work.EllipticEst.InteriorRegularity.VT.coords_one a b))
  have hIntPre' : IntegrableOn
      ((fun x : E2 => g (x 0, x 1)) ∘ (fun p : ℝ × ℝ => coords p.1 p.2))
      ((fun p : ℝ × ℝ => coords p.1 p.2) ⁻¹' K) := by
    rw [hcomp]
    exact hIntPre
  -- change of variables
  exact (hmp.integrableOn_comp_preimage hme (f := fun x : E2 => g (x 0, x 1))
    (s := K)).mp hIntPre'

end Work.EllipticEst.InteriorRegularity.Q0
