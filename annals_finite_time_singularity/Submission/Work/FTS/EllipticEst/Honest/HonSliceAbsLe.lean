import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology

namespace Work.FTS.EllipticEst.Honest

theorem HonSliceAbsLe (M : ℝ) (hM : 0 ≤ M) : ∀ f : ℝ → ℝ,
    ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) →
    Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) →
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |deriv f θ| ≤ M) →
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * θ) ∧
      (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |f θ| ≤ M * (Real.pi / 2 - θ)) := by
  intro f hcont h0 hpi hderiv
  have hpi2 : (0 : ℝ) < Real.pi / 2 := by positivity
  -- Lipschitz bound on the open interval, from the mean value theorem.
  have hL : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ∀ y ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      |f y - f x| ≤ M * |y - x| := by
    intro x hx y hy
    have hdiff : ∀ z ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), DifferentiableAt ℝ f z := fun z hz =>
      (hcont.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds hz)
    have hbnd : ∀ z ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), ‖deriv f z‖ ≤ M := fun z hz => by
      rw [Real.norm_eq_abs]
      exact hderiv z hz
    have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hbnd (convex_Ioo _ _) hx hy
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h
  constructor
  · -- left endpoint: `f θ` is the limit of `f θ - f η` as `η → 0⁺`
    intro θ hθ
    have hθ0 : (0 : ℝ) < θ := hθ.1
    have hmem : ∀ᶠ η in 𝓝[>] (0 : ℝ), η ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) ∧ η < θ := by
      have ha : ∀ᶠ η in 𝓝[>] (0 : ℝ), η ∈ Set.Ioi (0 : ℝ) := self_mem_nhdsWithin
      have hb : ∀ᶠ η in 𝓝[>] (0 : ℝ), η ∈ Set.Iio (Real.pi / 2) :=
        nhdsWithin_le_nhds (Iio_mem_nhds hpi2)
      have hc : ∀ᶠ η in 𝓝[>] (0 : ℝ), η ∈ Set.Iio θ :=
        nhdsWithin_le_nhds (Iio_mem_nhds hθ0)
      filter_upwards [ha, hb, hc] with η ha' hb' hc'
      exact ⟨⟨ha', hb'⟩, hc'⟩
    have h1 : Filter.Tendsto (fun η : ℝ => ‖f θ - f η‖) (𝓝[>] (0 : ℝ)) (𝓝 ‖f θ‖) := by
      have h : Filter.Tendsto (fun η : ℝ => f θ - f η) (𝓝[>] (0 : ℝ)) (𝓝 (f θ - 0)) :=
        (tendsto_const_nhds (x := f θ)).sub h0
      simpa using h.norm
    have h2 : Filter.Tendsto (fun η : ℝ => M * (θ - η)) (𝓝[>] (0 : ℝ)) (𝓝 (M * θ)) := by
      have hsub : Filter.Tendsto (fun η : ℝ => θ - η) (𝓝 (0 : ℝ)) (𝓝 (θ - 0)) :=
        (tendsto_const_nhds (x := θ)).sub Filter.tendsto_id
      have hc : Filter.Tendsto (fun η : ℝ => M * (θ - η)) (𝓝 (0 : ℝ)) (𝓝 (M * θ)) := by
        simpa using hsub.const_mul M
      exact hc.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))
    have h3 : ∀ᶠ η in 𝓝[>] (0 : ℝ), ‖f θ - f η‖ ≤ M * (θ - η) := by
      filter_upwards [hmem] with η hη
      have habs : |η - θ| = θ - η := by
        rw [abs_of_neg (by linarith [hη.2] : η - θ < 0)]
        ring
      calc ‖f θ - f η‖ = |f η - f θ| := by rw [Real.norm_eq_abs, abs_sub_comm]
        _ ≤ M * |η - θ| := hL θ hθ η hη.1
        _ = M * (θ - η) := by rw [habs]
    have hmain := le_of_tendsto_of_tendsto h1 h2 h3
    rw [Real.norm_eq_abs] at hmain
    exact hmain
  · -- right endpoint: `f θ` is the limit of `f θ - f η` as `η → (π/2)⁻`
    intro θ hθ
    have hθ0 : (0 : ℝ) < θ := hθ.1
    have hθlt : θ < Real.pi / 2 := hθ.2
    have hmem : ∀ᶠ η in 𝓝[<] (Real.pi / 2), η ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) ∧ θ < η := by
      have ha : ∀ᶠ η in 𝓝[<] (Real.pi / 2), η ∈ Set.Ioi (0 : ℝ) :=
        nhdsWithin_le_nhds (Ioi_mem_nhds hpi2)
      have hb : ∀ᶠ η in 𝓝[<] (Real.pi / 2), η ∈ Set.Iio (Real.pi / 2) :=
        self_mem_nhdsWithin
      have hc : ∀ᶠ η in 𝓝[<] (Real.pi / 2), η ∈ Set.Ioi θ :=
        nhdsWithin_le_nhds (Ioi_mem_nhds hθlt)
      filter_upwards [ha, hb, hc] with η ha' hb' hc'
      exact ⟨⟨ha', hb'⟩, hc'⟩
    have h1 : Filter.Tendsto (fun η : ℝ => ‖f θ - f η‖) (𝓝[<] (Real.pi / 2)) (𝓝 ‖f θ‖) := by
      have h : Filter.Tendsto (fun η : ℝ => f θ - f η) (𝓝[<] (Real.pi / 2)) (𝓝 (f θ - 0)) :=
        (tendsto_const_nhds (x := f θ)).sub hpi
      simpa using h.norm
    have h2 : Filter.Tendsto (fun η : ℝ => M * (η - θ)) (𝓝[<] (Real.pi / 2))
        (𝓝 (M * (Real.pi / 2 - θ))) := by
      have hsub : Filter.Tendsto (fun η : ℝ => η - θ) (𝓝 (Real.pi / 2))
          (𝓝 (Real.pi / 2 - θ)) :=
        Filter.tendsto_id.sub (tendsto_const_nhds (x := θ))
      have hc : Filter.Tendsto (fun η : ℝ => M * (η - θ)) (𝓝 (Real.pi / 2))
          (𝓝 (M * (Real.pi / 2 - θ))) := by
        simpa using hsub.const_mul M
      exact hc.mono_left
        (nhdsWithin_le_nhds (a := Real.pi / 2) (s := Set.Iio (Real.pi / 2)))
    have h3 : ∀ᶠ η in 𝓝[<] (Real.pi / 2), ‖f θ - f η‖ ≤ M * (η - θ) := by
      filter_upwards [hmem] with η hη
      have habs : |θ - η| = η - θ := by
        rw [abs_of_neg (by linarith [hη.2] : θ - η < 0)]
        ring
      calc ‖f θ - f η‖ = |f θ - f η| := Real.norm_eq_abs _
        _ ≤ M * |θ - η| := hL η hη.1 θ hθ
        _ = M * (η - θ) := by rw [habs]
    have hmain := le_of_tendsto_of_tendsto h1 h2 h3
    rw [Real.norm_eq_abs] at hmain
    exact hmain

end Work.FTS.EllipticEst.Honest
