import Mathlib
import Submission.Work.RatHurewicz.subsingleton_relPi_of_compressRel_range
import Submission.Work.RatHurewicz.AttachPush.PushOff
import Submission.Work.AttachPush.exists_homotopy_avoids_cellOrigins
import Submission.Work.RatHurewicz.compression_of_relPiVanishing

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

open scoped Topology unitInterval

namespace Work.Serre.AttachCompress

open Work.RatHurewicz

/-- **Attaching `(n+2)`-cells does not change the homotopy groups in degrees `≤ n`, in compression
form.**  The general-position step (pushing a cube off the cell centres) is
`Work.AttachPush.exists_homotopy_avoids_cellOrigins` and the push-off step is
`Work.RatHurewicz.exists_pushOff_homotopy`; concatenating the two homotopies gives the compression
of the pair `(attachCells n Y ι f, range (attachIncl n Y ι f))` in dimensions `≤ n+1`. -/
theorem compression (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(cellSphere n, Y)) :
    ∀ d, d ≤ n + 1 → CompressRel (attachCells n Y ι f) (Set.range (attachIncl n Y ι f)) d := by
  intro d hd
  intro g hg
  obtain ⟨g₁, H₁, h₁0, h₁bd, h₁1, havoid⟩ :=
    Work.AttachPush.exists_homotopy_avoids_cellOrigins (d := d) n Y ι f hd g hg
  obtain ⟨H₂, h₂0, h₂A, h₂1⟩ :=
    Work.RatHurewicz.exists_pushOff_homotopy (X := ICube d) n Y ι f g₁ havoid
  have hg₁ : ∀ x, x ∈ Cube.boundary (Fin d) → g₁ x ∈ Set.range (attachIncl n Y ι f) := by
    intro x hx
    rw [← h₁1 x, h₁bd x hx]
    exact hg x hx
  set Gfun : ICube d × I → attachCells n Y ι f := fun p =>
    if (2 : ℝ) * (p.2 : ℝ) ≤ 1 then H₁ (p.1, clampI (2 * (p.2 : ℝ)))
    else H₂ (p.1, clampI (2 * (p.2 : ℝ) - 1)) with Gfun_def
  have hGcont : Continuous Gfun := by
    rw [Gfun_def]
    refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
    · exact H₁.continuous.comp (continuous_fst.prodMk (continuous_clampI.comp (by fun_prop)))
    · exact H₂.continuous.comp (continuous_fst.prodMk (continuous_clampI.comp (by fun_prop)))
    · exact continuous_const.mul (continuous_subtype_val.comp continuous_snd)
    · exact continuous_const
    · intro p hp
      have h1 : clampI (2 * (p.2 : ℝ)) = (1 : I) := by rw [hp, clampI_one']
      have h2 : clampI (2 * (p.2 : ℝ) - 1) = (0 : I) := by
        have h2' : 2 * (p.2 : ℝ) - 1 = 0 := by rw [hp]; norm_num
        rw [h2', clampI_zero']
      rw [h1, h2, h₁1, h₂0]
  refine ⟨⟨Gfun, hGcont⟩, ?_, ?_, ?_⟩
  · intro x
    show (if (2 : ℝ) * (((0 : I) : ℝ)) ≤ 1 then H₁ (x, clampI (2 * ((0 : I) : ℝ)))
      else H₂ (x, clampI (2 * ((0 : I) : ℝ) - 1))) = g x
    rw [show (2 : ℝ) * (((0 : I) : ℝ)) = 0 by norm_num, clampI_zero',
      if_pos (by norm_num)]
    exact h₁0 x
  · intro x hx t
    show (if (2 : ℝ) * (t : ℝ) ≤ 1 then H₁ (x, clampI (2 * (t : ℝ)))
      else H₂ (x, clampI (2 * (t : ℝ) - 1))) = g x
    by_cases h : (2 : ℝ) * (t : ℝ) ≤ 1
    · rw [if_pos h, h₁bd x hx]
    · rw [if_neg h, h₂A x (hg₁ x hx)]
      exact (h₁1 x).symm.trans (h₁bd x hx 1)
  · intro x
    show (if (2 : ℝ) * (((1 : I) : ℝ)) ≤ 1 then H₁ (x, clampI (2 * ((1 : I) : ℝ)))
      else H₂ (x, clampI (2 * ((1 : I) : ℝ) - 1))) ∈ Set.range (attachIncl n Y ι f)
    rw [if_neg (by norm_num), show (2 : ℝ) * (((1 : I) : ℝ)) - 1 = 1 by norm_num, clampI_one']
    exact h₂1 x

end Work.Serre.AttachCompress
