import Mathlib
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B5.LagData

/-!
# B5: smoothness of the chart slice `(τ, x, t) ↦ W τ t (rho τ x t)`

The chart `W` is only `C⁸` on the set `Icc 0 1 ×ˢ univ ×ˢ Ioo (-ρ₀) ρ₀` (the `ρ`-variable
must stay in the chart's box), while `rho` is globally `C⁸`.  At a point where
`rho τ₀ x₀ t₀ ∈ Ioo (-ρ₀) ρ₀`, the composite is `C⁸` within `Icc 0 1 ×ˢ univ ×ˢ univ`: by
continuity of `rho` the third coordinate stays in the (open) box on a neighbourhood, and the
`τ`-coordinate is confined to `Icc 0 1` by the within-set.  The proof composes `hWsm` with the
global `C⁸` map `z ↦ (z.1, (z.2.2, rho z.1 z.2.1 z.2.2))` using `ContDiffWithinAt.comp` on the
shrunk within-set `s ∩ rho ⁻¹' Ioo (-ρ₀) ρ₀`, which is a neighbourhood of the point in `𝓝[s]`.
-/

namespace Work.RPB.B5

theorem chartSlice_contDiffWithinAt (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (D : Work.RPB.B5.LagData CI a) {τ₀ x₀ t₀ : ℝ} (hτ : τ₀ ∈ Set.Icc (0 : ℝ) 1)
    (hint : D.rho τ₀ x₀ t₀ ∈ Set.Ioo (-D.ρ₀) D.ρ₀) :
    ContDiffWithinAt ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => D.W z.1 z.2.2 (D.rho z.1 z.2.1 z.2.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) (τ₀, (x₀, t₀)) := by
  have hrcont : Continuous (fun z : ℝ × (ℝ × ℝ) => D.rho z.1 z.2.1 z.2.2) :=
    D.hrhosm.continuous
  -- the box in which the `ρ`-variable of `W` may live is an open neighbourhood of the point
  have hN : (fun z : ℝ × (ℝ × ℝ) => D.rho z.1 z.2.1 z.2.2) ⁻¹'
      Set.Ioo (-D.ρ₀) D.ρ₀ ∈ nhds (τ₀, (x₀, t₀)) :=
    (isOpen_Ioo.preimage hrcont).mem_nhds (by simpa [Set.mem_preimage] using hint)
  -- the inner map `z ↦ (z.1, (z.2.2, rho z.1 z.2.1 z.2.2))` is globally `C⁸`
  have hfC : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.2, D.rho z.1 z.2.1 z.2.2))) :=
    (contDiff_fst : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => z.1)).prodMk
      (((contDiff_snd : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => z.2)).snd).prodMk D.hrhosm)
  have hg : ContDiffWithinAt ℝ 8 (fun w : ℝ × (ℝ × ℝ) => D.W w.1 w.2.1 w.2.2)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-D.ρ₀) D.ρ₀)
      (τ₀, (t₀, D.rho τ₀ x₀ t₀)) := by
    refine D.hWsm.contDiffWithinAt ?_
    simp only [Set.mem_prod, Set.mem_Icc, Set.mem_univ, Set.mem_Ioo, true_and]
    exact ⟨hτ, hint⟩
  have hf : ContDiffWithinAt ℝ 8 (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.2, D.rho z.1 z.2.1 z.2.2)))
      ((Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) ∩
        (fun z : ℝ × (ℝ × ℝ) => D.rho z.1 z.2.1 z.2.2) ⁻¹' Set.Ioo (-D.ρ₀) D.ρ₀)
      (τ₀, (x₀, t₀)) := hfC.contDiffWithinAt
  have hmap : Set.MapsTo (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.2, D.rho z.1 z.2.1 z.2.2)))
      ((Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) ∩
        (fun z : ℝ × (ℝ × ℝ) => D.rho z.1 z.2.1 z.2.2) ⁻¹' Set.Ioo (-D.ρ₀) D.ρ₀)
      (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (-D.ρ₀) D.ρ₀) := by
    intro z hz
    obtain ⟨hz1, hzN⟩ := hz
    simp only [Set.mem_prod, Set.mem_Icc, Set.mem_univ, Set.mem_Ioo, true_and] at hz1 hzN ⊢
    exact ⟨hz1.1, hzN⟩
  have hcomp : ContDiffWithinAt ℝ 8
      ((fun w : ℝ × (ℝ × ℝ) => D.W w.1 w.2.1 w.2.2) ∘
        (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.2, D.rho z.1 z.2.1 z.2.2))))
      ((Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) ∩
        (fun z : ℝ × (ℝ × ℝ) => D.rho z.1 z.2.1 z.2.2) ⁻¹' Set.Ioo (-D.ρ₀) D.ρ₀)
      (τ₀, (x₀, t₀)) :=
    ContDiffWithinAt.comp (τ₀, (x₀, t₀)) hg hf hmap
  -- enlarge the within-set back to the whole slab
  have hN' : (fun z : ℝ × (ℝ × ℝ) => D.rho z.1 z.2.1 z.2.2) ⁻¹' Set.Ioo (-D.ρ₀) D.ρ₀ ∈
      nhdsWithin (τ₀, (x₀, t₀)) (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) :=
    Filter.mem_of_superset (inter_mem_nhdsWithin (Set.Icc (0:ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) hN)
      Set.inter_subset_right
  have hmain := (contDiffWithinAt_inter' (f := (fun w : ℝ × (ℝ × ℝ) => D.W w.1 w.2.1 w.2.2) ∘
      (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.2, D.rho z.1 z.2.1 z.2.2))))
      (x := (τ₀, (x₀, t₀))) hN').mp hcomp
  have hfun : ((fun w : ℝ × (ℝ × ℝ) => D.W w.1 w.2.1 w.2.2) ∘
        (fun z : ℝ × (ℝ × ℝ) => (z.1, (z.2.2, D.rho z.1 z.2.1 z.2.2))))
      = fun z : ℝ × (ℝ × ℝ) => D.W z.1 z.2.2 (D.rho z.1 z.2.1 z.2.2) := rfl
  rw [hfun] at hmain
  exact hmain

end Work.RPB.B5
