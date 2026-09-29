import Mathlib
import Submission.Work.A14.defs
import Submission.Work.C17f.frobenius_double_exponent_zero
import Submission.Work.A14D.setup
import Submission.Work.A14D.slitDisk_continuation
import Submission.Work.A14D.local_structure_at_ninth
import Submission.Work.A14D.inhomog_extension_from_disk

namespace Work.A14D

open Complex Metric Filter
open scoped Topology

/-- Every solution of `LZ f = 0` on an open convex piece `V` of the slit disc has a well defined
logarithmic coefficient at the ninth: `f = κ · y9 · log (· - 1/9) + (holomorphic on the disc)`.

Strategy.  Continue `f` to the slit disc (`slitDisk_continuation`), read off its log coefficient and
holomorphic part near the ninth (`local_structure_at_ninth`), extend that holomorphic part to the
whole disc (`inhomog_extension_from_disk`), and compare the two sides on the slit disc with the
identity theorem. -/
theorem logCoeff_exists {y9 : ℂ → ℂ} {δ : ℝ} (hY : Y9 y9 δ) (V : Set ℂ) (hV : IsOpen V) (hVc : Convex ℝ V) (hVsub : V ⊆ ball ninth δ ∩ {z | z.im ≠ 0 ∨ ninth.re < z.re}) (f : ℂ → ℂ) (hf : DifferentiableOn ℂ f V) (hL : ∀ z ∈ V, LZ f z = 0) : ∃ κ, LogCoeff y9 δ V f κ := by
  have hY0 : Y9 y9 δ := hY
  obtain ⟨hδpos, hδ20, hy9d, hy9ne, hy9ode⟩ := hY
  have hδ8 : δ ≤ 8 / 9 := by linarith
  by_cases hVne : V.Nonempty
  · have hVsubS : V ⊆ slitDisk δ := hVsub
    have hOpenS : IsOpen (slitDisk δ) := isOpen_slitDisk δ
    have hpre : IsPreconnected (slitDisk δ) := isPreconnected_slitDisk hδpos
    -- 1. continue `f` to the slit disc
    obtain ⟨F, hFd, hFL, hFeq⟩ :=
      slitDisk_continuation (δ := δ) (V := V) (f := f) hδpos hδ8 hV hVc hVsubS hf hL
    -- 2. local structure at the ninth
    obtain ⟨ρ, hρpos, hρδ, κ, hh, hhd, hhode, hhid⟩ :=
      local_structure_at_ninth (y9 := y9) (δ := δ) hY0 hFd hFL
    -- 3. extend the holomorphic part to the disc
    obtain ⟨G, hGd, hGeq, _hGode⟩ :=
      inhomog_extension_from_disk (y9 := y9) (δ := δ) (ρ := ρ) hY0 hρpos hρδ κ hhd hhode
    -- 4. `F - κ · logTerm y9` and `G` agree on the slit disc
    set x₀ : ℂ := ninth + (((ρ / 2 : ℝ)) : ℂ) * Complex.I with hx₀def
    have hx₀sub : x₀ - ninth = (((ρ / 2 : ℝ)) : ℂ) * Complex.I := by rw [hx₀def]; ring
    have hx₀norm : ‖x₀ - ninth‖ = ρ / 2 := by
      rw [hx₀sub, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0 : ℝ) < ρ / 2)]
    have hx₀ball : x₀ ∈ Metric.ball ninth ρ := by
      rw [Metric.mem_ball, Complex.dist_eq, hx₀norm]; linarith
    have hx₀comp : x₀ ∈ slitComp := by
      left
      have hxim : x₀.im = ρ / 2 := by
        rw [hx₀def]
        simp [ninth]
      rw [hxim]; linarith
    have hx₀S : x₀ ∈ slitDisk δ :=
      ⟨by rw [Metric.mem_ball, Complex.dist_eq, hx₀norm]; linarith, hx₀comp⟩
    have hAnal : AnalyticOnNhd ℂ (fun z => F z - κ * logTerm y9 z) (slitDisk δ) :=
      (hFd.sub ((differentiableOn_logTerm hy9d).const_mul κ)).analyticOnNhd hOpenS
    have hAnalG : AnalyticOnNhd ℂ G (slitDisk δ) :=
      (hGd.mono (fun z hz => hz.1)).analyticOnNhd hOpenS
    have hev : (fun z => F z - κ * logTerm y9 z) =ᶠ[𝓝 x₀] G := by
      filter_upwards [(hOpenS.inter Metric.isOpen_ball).mem_nhds ⟨hx₀S, hx₀ball⟩] with z hz
      have h1 := hhid z hz
      have h2 := hGeq hz.2
      rw [logTerm, h2, h1]
      ring
    have hEqOn : Set.EqOn (fun z => F z - κ * logTerm y9 z) G (slitDisk δ) :=
      AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hAnal hAnalG hpre hx₀S hev
    refine ⟨κ, G, hGd, ?_⟩
    intro z hz
    have h1 : F z - κ * logTerm y9 z = G z := hEqOn (hVsubS hz)
    have h2 : f z = F z := (hFeq hz).symm
    rw [h2, show F z = κ * logTerm y9 z + G z from by linear_combination h1, logTerm]
    ring
  · refine ⟨0, fun _ => 0, differentiableOn_const 0, ?_⟩
    intro z hz
    exact absurd ⟨z, hz⟩ hVne

end Work.A14D
