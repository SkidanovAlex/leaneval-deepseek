import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.R7d

theorem Vth_edge_cont {Vz Vθ : ℝ → ℝ → ℝ → ℝ} {S : ℝ}
    (hcont : ContinuousOn (fun p : ℝ × ℝ × ℝ => (Vz p.1 p.2.1 p.2.2, Vθ p.1 p.2.1 p.2.2))
      (Set.Ioi (0:ℝ) ×ˢ (Set.Icc (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)))
    {z τ : ℝ} (hz : 0 < z) (hτ0 : 0 ≤ τ) (hτS : τ ≤ S) :
    Filter.Tendsto (fun θ' : ℝ => Vθ z θ' τ) (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (Vθ z 0 τ)) ∧
    Filter.Tendsto (fun θ' : ℝ => Vθ z θ' τ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds (Vθ z (Real.pi / 2) τ)) := by
  -- We prove continuity of `θ' ↦ Vθ z θ' τ` within the (open) interval `(0, π/2)` and then
  -- transfer the (`nhdsWithin`-)filter to the two edge restrictions `Ioi 0` and `Iio (π/2)`.
  set A : Set ℝ := Set.Ioo (0:ℝ) (Real.pi / 2) with hAdef
  have hπ : 0 < Real.pi / 2 := by linarith [Real.pi_pos]
  have hG : ContinuousOn (fun p : ℝ × ℝ × ℝ => Vθ p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ (Set.Icc (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) := hcont.snd
  have key : ∀ x : ℝ, x ∈ Set.Icc (0:ℝ) (Real.pi / 2) →
      ContinuousWithinAt (fun θ' : ℝ => Vθ z θ' τ) A x := by
    intro x hx
    have hmem : (z, x, τ) ∈
        (Set.Ioi (0:ℝ) ×ˢ (Set.Icc (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) :=
      ⟨hz, hx, hτ0, hτS⟩
    have hGx := hG.continuousWithinAt hmem
    -- the curve `θ' ↦ (z, θ', τ)` maps `A` into the half-strip and is continuous
    have hfx : ContinuousWithinAt (fun θ' : ℝ => (z, θ', τ)) A x :=
      (continuous_const.prodMk (continuous_id.prodMk continuous_const)).continuousAt.continuousWithinAt
    have hmap : Set.MapsTo (fun θ' : ℝ => (z, θ', τ)) A
        (Set.Ioi (0:ℝ) ×ˢ (Set.Icc (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) := by
      intro θ' hθ'
      exact ⟨hz, ⟨le_of_lt hθ'.1, le_of_lt hθ'.2⟩, hτ0, hτS⟩
    have hcomp : ContinuousWithinAt
        ((fun p : ℝ × ℝ × ℝ => Vθ p.1 p.2.1 p.2.2) ∘ (fun θ' : ℝ => (z, θ', τ))) A x :=
      ContinuousWithinAt.comp (x := x) (f := fun θ' : ℝ => (z, θ', τ)) hGx hfx hmap
    exact hcomp
  have h0 : ContinuousWithinAt (fun θ' : ℝ => Vθ z θ' τ) A 0 := key 0 ⟨le_refl 0, hπ.le⟩
  have hpi : ContinuousWithinAt (fun θ' : ℝ => Vθ z θ' τ) A (Real.pi / 2) :=
    key (Real.pi / 2) ⟨hπ.le, le_refl _⟩
  constructor
  · -- the two filters `𝓝[Ioi 0] 0` and `𝓝[Ioo 0 (π/2)] 0` agree
    have hfil : nhdsWithin (0:ℝ) (Set.Ioi 0) = nhdsWithin (0:ℝ) A := by
      rw [hAdef]
      exact nhdsWithin_eq_nhdsWithin' (s := Set.Iio (Real.pi / 2)) (t := Set.Ioi (0:ℝ))
        (u := Set.Ioo (0:ℝ) (Real.pi / 2))
        (isOpen_Iio.mem_nhds (by positivity : (0:ℝ) < Real.pi / 2))
        (by ext y; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio, Set.mem_Ioo]; tauto)
    rw [hfil]
    exact h0
  · -- and likewise `𝓝[Iio (π/2)] (π/2)` and `𝓝[Ioo 0 (π/2)] (π/2)`
    have hfil : nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)) = nhdsWithin (Real.pi / 2) A := by
      rw [hAdef]
      exact nhdsWithin_eq_nhdsWithin' (s := Set.Ioi (0:ℝ)) (t := Set.Iio (Real.pi / 2))
        (u := Set.Ioo (0:ℝ) (Real.pi / 2))
        (isOpen_Ioi.mem_nhds (by positivity : (0:ℝ) < Real.pi / 2))
        (by ext y; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Iio, Set.mem_Ioo]; tauto)
    rw [hfil]
    exact hpi

end Work.FTS.RegPkgGal.R7d
