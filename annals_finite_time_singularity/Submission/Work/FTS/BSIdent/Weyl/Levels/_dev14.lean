import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Group.AddTorsor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Have
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Basic
import Submission.Work.FTS.BSIdent.Weyl.Levels._stub
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev5
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev2
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev11
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev12

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FTS.BSIdent.Weyl.Dev14

open Filter Set MeasureTheory
open scoped Topology
open Work.FTS.BSIdent.Weyl.Dev5 (GG)

variable {Φ : Work.FTS.BSIdent.Fam} {τ : ℝ}

/-- The value of the `θ`-derivative of `GG` at `θ = 0`. -/
theorem pdZ_GG_zero_eq {w₀ : ℝ} (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ →
      θ < Real.pi / 2 + 1 → ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) (hw₀ : 0 < w₀) :
    Work.Cyl.pdZ (GG Φ τ) w₀ 0 = Work.Cyl.pdZ (fun w θ => Φ w θ τ) w₀ 0 := by
  have hθ0 : |(0:ℝ)| < Real.pi / 2 + 1 := by rw [abs_zero]; linarith [Real.pi_pos]
  have hC2 : ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w₀, 0) :=
    Dev2.contDiffAt_Phi (τ := τ) (Φ := Φ) hsm (by linarith) hθ0
  have hd : DifferentiableAt ℝ (fun θ' : ℝ => Φ w₀ θ' τ) 0 :=
    Work.Cyl.differentiableAt_slice_snd (fun w θ => Φ w θ τ) w₀ 0
      (hC2.differentiableAt (by norm_num))
  have hderiv : HasDerivAt (fun θ' : ℝ => Φ w₀ θ' τ)
      (deriv (fun θ' : ℝ => Φ w₀ θ' τ) 0) 0 := hd.hasDerivAt
  have hΦ0 : Φ w₀ 0 τ = 0 := h0 w₀ hw₀
  have hGG0 : GG Φ τ w₀ 0 = 0 := by
    rw [Dev5.GG_of_nonneg (Φ := Φ) (τ := τ) le_rfl, hΦ0]
  have hslopeΦ : Tendsto (slope (fun θ' : ℝ => Φ w₀ θ' τ) 0) (𝓝[≠] (0:ℝ))
      (𝓝 (deriv (fun θ' : ℝ => Φ w₀ θ' τ) 0)) := hderiv.tendsto_slope
  have hGGfun : (fun θ' : ℝ => GG Φ τ w₀ θ') = GG Φ τ w₀ := rfl
  have hslopeGG : Tendsto (slope (fun θ' : ℝ => GG Φ τ w₀ θ') 0) (𝓝[≠] (0:ℝ))
      (𝓝 (deriv (fun θ' : ℝ => Φ w₀ θ' τ) 0)) := by
    have hslopeΦpos : Tendsto (slope (fun θ' : ℝ => Φ w₀ θ' τ) 0) (𝓝[>] (0:ℝ))
        (𝓝 (deriv (fun θ' : ℝ => Φ w₀ θ' τ) 0)) :=
      hslopeΦ.mono_left (nhdsWithin_mono 0 (fun x hx => ne_of_gt hx))
    have hpos : Tendsto (slope (fun θ' : ℝ => GG Φ τ w₀ θ') 0) (𝓝[>] (0:ℝ))
        (𝓝 (deriv (fun θ' : ℝ => Φ w₀ θ' τ) 0)) := by
      refine hslopeΦpos.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [slope_fun_def, vsub_eq_sub, hGG0, hΦ0, sub_zero]
      rw [Dev5.GG_of_nonneg (Φ := Φ) (τ := τ) (le_of_lt hh)]
    have hrefl : Tendsto (fun h : ℝ => slope (fun θ' : ℝ => Φ w₀ θ' τ) 0 (-h)) (𝓝[<] (0:ℝ))
        (𝓝 (deriv (fun θ' : ℝ => Φ w₀ θ' τ) 0)) := by
      have hmap : Tendsto (fun h : ℝ => -h) (𝓝[<] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
        refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
        · have hcont : ContinuousAt (fun h : ℝ => -h) 0 := continuous_neg.continuousAt
          have := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio (0:ℝ)))
          simpa using this
        · filter_upwards [self_mem_nhdsWithin] with h hh
          exact neg_pos.mpr (by simpa using hh)
      have hcomp := hslopeΦpos.comp hmap
      simpa [Function.comp_def] using hcomp
    have hneg : Tendsto (slope (fun θ' : ℝ => GG Φ τ w₀ θ') 0) (𝓝[<] (0:ℝ))
        (𝓝 (deriv (fun θ' : ℝ => Φ w₀ θ' τ) 0)) := by
      refine hrefl.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hne : h ≠ 0 := ne_of_lt hh
      simp only [slope_fun_def, vsub_eq_sub, hGG0, hΦ0, sub_zero]
      rw [Dev5.GG_of_neg (Φ := Φ) (τ := τ) hh]
      field_simp
      simp only [neg_smul, smul_neg]
    have hset : (({0} : Set ℝ))ᶜ = Set.Ioi 0 ∪ Set.Iio 0 := by
      ext x
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_union, Set.mem_Ioi,
        Set.mem_Iio]
      constructor
      · intro hx
        rcases lt_or_gt_of_ne hx with h | h
        · exact Or.inr h
        · exact Or.inl h
      · rintro (h | h)
        · exact ne_of_gt h
        · exact ne_of_lt h
    have hsplit : 𝓝[≠] (0:ℝ) = 𝓝[>] (0:ℝ) ⊔ 𝓝[<] (0:ℝ) := by
      show 𝓝[(({0} : Set ℝ))ᶜ] (0:ℝ) = 𝓝[>] (0:ℝ) ⊔ 𝓝[<] (0:ℝ)
      rw [hset, nhdsWithin_union]
    rw [hsplit]
    exact tendsto_sup.mpr ⟨hpos, hneg⟩
  have hfin : HasDerivAt (fun θ' : ℝ => GG Φ τ w₀ θ')
      (deriv (fun θ' : ℝ => Φ w₀ θ' τ) 0) 0 := hasDerivAt_iff_tendsto_slope.mpr hslopeGG
  show deriv (fun θ' : ℝ => GG Φ τ w₀ θ') 0 = deriv (fun θ' : ℝ => Φ w₀ θ' τ) 0
  exact hfin.deriv

end Work.FTS.BSIdent.Weyl.Dev14
