/-
Copyright: work module for the Elgindi finite-time singularity project.

# The second difference quotient of the dilation

For `F` of class `C²` on a neighbourhood of `z > 0`,

  `(F (c² z) - 2 F (c z) + F z) / (c - 1)²  ⟶  z F'(z) + z² F''(z)`   as `c → 1⁺`.

The proof reduces to a general analytic statement about a `C²` function `ψ`: the second
difference quotient with respect to the non-symmetric nodes `h` and `2h + h²` (i.e. the two
images of a point `1 + h` under `x ↦ x` and `x ↦ x²`) converges to `ψ'(0) + ψ''(0)`.  That is
`secondDiffQuot_aux` below; the Taylor expansion `Real.taylor_tendsto` provides the Peano
remainder, and the substitution `ψ h = F (z (1 + h))` turns the statement above into it.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Topology
open Filter Set

namespace Work.FTS.EllipticEst.Cores.Dil

set_option autoImplicit false

/-- Second difference quotient of a `C²` function along the non-symmetric pair of nodes
`h` and `2h + h²` (equivalently: along the two images of `1 + h` under `x ↦ x` and
`x ↦ x²`), as `h → 0⁺`:

  `(ψ (2h + h²) - 2 ψ h + ψ 0) / h²  ⟶  ψ'(0) + ψ''(0)`.

Only `C²`-regularity of `ψ` on a one-sided neighbourhood of `0` is needed. -/
theorem secondDiffQuot_aux {ψ : ℝ → ℝ} (hψ : ContDiffOn ℝ 2 ψ (Set.Ioi (-1))) :
    Filter.Tendsto (fun h : ℝ => (ψ (2 * h + h ^ 2) - 2 * ψ h + ψ 0) / h ^ 2)
      (𝓝[>] (0:ℝ)) (𝓝 (deriv ψ 0 + deriv (deriv ψ) 0)) := by
  have hsc : Convex ℝ (Set.Ioi (-1:ℝ)) := convex_Ioi (-1)
  have h0 : (0:ℝ) ∈ Set.Ioi (-1:ℝ) := by norm_num
  -- the two Taylor coefficients
  set a : ℝ := iteratedDeriv 1 ψ 0 with hadef
  set b : ℝ := iteratedDeriv 2 ψ 0 with hbdef
  have hda : deriv ψ 0 = a := by rw [hadef, iteratedDeriv_one]
  have hdb : deriv (deriv ψ) 0 = b := by
    rw [hbdef]
    show deriv (deriv ψ) 0 = iteratedDeriv (1 + 1) ψ 0
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  rw [hda, hdb]
  -- the second order Taylor polynomial of `ψ` at `0`
  set T : ℝ → ℝ := fun x => ψ 0 + x * a + (x ^ 2 / 2) * b with hTdef
  have hT : ∀ x : ℝ, taylorWithinEval ψ 2 (Set.Ioi (-1)) 0 x = T x := by
    intro x
    rw [taylor_within_apply, hTdef, hadef, hbdef]
    simp only [iteratedDerivWithin_of_isOpen isOpen_Ioi h0]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [iteratedDeriv_zero]
    ring
  -- Peano remainder, as `h → 0⁺`
  have hTay : Filter.Tendsto (fun x : ℝ => (ψ x - T x) / x ^ 2) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    have h := Real.taylor_tendsto (x₀ := (0:ℝ)) (n := 2) hsc h0 hψ
    have h' : Filter.Tendsto (fun x : ℝ => (ψ x - taylorWithinEval ψ 2 (Set.Ioi (-1)) 0 x) / x ^ 2)
        (𝓝[Set.Ioi (-1)] 0) (𝓝 0) := by simpa using h
    have h'' : Filter.Tendsto (fun x : ℝ => (ψ x - taylorWithinEval ψ 2 (Set.Ioi (-1)) 0 x) / x ^ 2)
        (𝓝[Set.Ioi (0:ℝ)] 0) (𝓝 0) :=
      h'.mono_left (nhdsWithin_mono 0 (Set.Ioi_subset_Ioi (by norm_num : (-1:ℝ) ≤ 0)))
    refine h''.congr' (Filter.Eventually.of_forall fun x => ?_)
    simp only [hT x]
  -- `h ↦ 2h + h²` preserves the one-sided neighbourhood of `0`
  have hmap : Filter.Tendsto (fun h : ℝ => 2 * h + h ^ 2) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Continuous fun h : ℝ => 2 * h + h ^ 2 := by fun_prop
      simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      exact show 0 < 2 * h + h ^ 2 by nlinarith [show (0:ℝ) < h from hh]
  have hA1 : Filter.Tendsto (fun h : ℝ => (ψ (2 * h + h ^ 2) - T (2 * h + h ^ 2)) / (2 * h + h ^ 2) ^ 2)
      (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa [Function.comp_def] using hTay.comp hmap
  have hA2 : Filter.Tendsto (fun h : ℝ => (2 + h) ^ 2) (𝓝[>] (0:ℝ)) (𝓝 ((2:ℝ) ^ 2)) := by
    have hc : Continuous fun h : ℝ => (2 + h) ^ 2 := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hB : Filter.Tendsto (fun h : ℝ => -2 * ((ψ h - T h) / h ^ 2)) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa using hTay.const_mul (-2)
  have hC : Filter.Tendsto (fun h : ℝ => a + ((2 + h) ^ 2 / 2 - 1) * b) (𝓝[>] (0:ℝ))
      (𝓝 (a + (1:ℝ) * b)) := by
    have hc : Continuous fun h : ℝ => a + ((2 + h) ^ 2 / 2 - 1) * b := by fun_prop
    have h1 : Filter.Tendsto (fun h : ℝ => a + ((2 + h) ^ 2 / 2 - 1) * b) (𝓝[>] (0:ℝ))
        (𝓝 (a + ((2 + (0:ℝ)) ^ 2 / 2 - 1) * b)) :=
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    have h2 : a + ((2 + (0:ℝ)) ^ 2 / 2 - 1) * b = a + 1 * b := by norm_num
    rwa [h2] at h1
  have hsum : Filter.Tendsto (fun h : ℝ =>
      (ψ (2 * h + h ^ 2) - T (2 * h + h ^ 2)) / (2 * h + h ^ 2) ^ 2 * (2 + h) ^ 2 +
        (-2 * ((ψ h - T h) / h ^ 2) + (a + ((2 + h) ^ 2 / 2 - 1) * b)))
      (𝓝[>] (0:ℝ)) (𝓝 ((0 * (2:ℝ) ^ 2) + (0 + (a + (1:ℝ) * b)))) :=
    (hA1.mul hA2).add (hB.add hC)
  -- splitting off the Taylor polynomial
  have hident : ∀ h : ℝ, 0 < h → (ψ (2 * h + h ^ 2) - 2 * ψ h + ψ 0) / h ^ 2
      = (ψ (2 * h + h ^ 2) - T (2 * h + h ^ 2)) / (2 * h + h ^ 2) ^ 2 * (2 + h) ^ 2 +
        (-2 * ((ψ h - T h) / h ^ 2) + (a + ((2 + h) ^ 2 / 2 - 1) * b)) := by
    intro h hh
    have hTpoly : T (2 * h + h ^ 2) - 2 * T h + T 0 = h ^ 2 * a + h ^ 2 * ((2 + h) ^ 2 / 2 - 1) * b := by
      rw [hTdef]; ring
    have hT0 : T 0 = ψ 0 := by rw [hTdef]; ring
    have hne : h ≠ 0 := ne_of_gt hh
    have hne2 : 2 * h + h ^ 2 ≠ 0 := by nlinarith [hh]
    rw [← hT0]
    have : a + ((2 + h) ^ 2 / 2 - 1) * b = (T (2 * h + h ^ 2) - 2 * T h + T 0) / h ^ 2 := by
      rw [hTpoly]; field_simp
    rw [this]
    field_simp
    ring
  have heq : (fun h : ℝ =>
      (ψ (2 * h + h ^ 2) - T (2 * h + h ^ 2)) / (2 * h + h ^ 2) ^ 2 * (2 + h) ^ 2 +
        (-2 * ((ψ h - T h) / h ^ 2) + (a + ((2 + h) ^ 2 / 2 - 1) * b)))
      =ᶠ[𝓝[>] (0:ℝ)] (fun h : ℝ => (ψ (2 * h + h ^ 2) - 2 * ψ h + ψ 0) / h ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with h hh
    exact (hident h hh).symm
  have hlim : (0 * (2:ℝ) ^ 2) + (0 + (a + (1:ℝ) * b)) = a + b := by ring
  rw [hlim] at hsum
  exact hsum.congr' heq

theorem SecondDiffQuot {F : ℝ → ℝ} {z : ℝ} (hz : 0 < z)
    (hF : ContDiffOn ℝ 2 F (Set.Ioi 0)) :
    Filter.Tendsto (fun c : ℝ => (F (c ^ 2 * z) - 2 * F (c * z) + F z) / (c - 1) ^ 2)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (z * deriv F z + z ^ 2 * deriv (deriv F) z)) := by
  set ψ : ℝ → ℝ := fun h => F (z * (1 + h)) with hψdef
  have hφ_deriv : ∀ x : ℝ, HasDerivAt (fun h : ℝ => z * (1 + h)) z x := by
    intro x
    simpa using ((hasDerivAt_const x (1:ℝ)).add (hasDerivAt_id x)).const_mul z
  have hψ : ContDiffOn ℝ 2 ψ (Set.Ioi (-1)) := by
    have h1 : ContDiffOn ℝ 2 (fun h : ℝ => z * (1 + h)) (Set.Ioi (-1)) := by fun_prop
    have h2 : Set.MapsTo (fun h : ℝ => z * (1 + h)) (Set.Ioi (-1)) (Set.Ioi (0:ℝ)) := by
      intro h hh
      have hh' : (-1:ℝ) < h := hh
      exact mul_pos hz (by linarith)
    have h3 := hF.comp h1 h2
    simpa [hψdef, Function.comp_def] using h3
  have hmem : Set.Ioi (0:ℝ) ∈ 𝓝 z := isOpen_Ioi.mem_nhds hz
  have hFd : DifferentiableAt ℝ F z := (hF.differentiableOn (by norm_num)).differentiableAt hmem
  have hui : UniqueDiffOn ℝ (Set.Ioi (0:ℝ)) := isOpen_Ioi.uniqueDiffOn
  have hderF : DifferentiableOn ℝ (deriv F) (Set.Ioi 0) := by
    have h1 := hF.differentiableOn_iteratedDerivWithin (m := 1) (by norm_num) hui
    refine h1.congr (fun x hx => ?_)
    rw [iteratedDerivWithin_one, derivWithin_of_isOpen isOpen_Ioi hx]
  have hdFd : DifferentiableAt ℝ (deriv F) z := hderF.differentiableAt hmem
  have hderivψ : deriv ψ 0 = z * deriv F z := by
    have hFz : HasDerivAt F (deriv F z) ((fun h : ℝ => z * (1 + h)) 0) := by
      simpa using hFd.hasDerivAt
    have key : HasDerivAt (F ∘ (fun h : ℝ => z * (1 + h))) (deriv F z * z) 0 :=
      HasDerivAt.comp 0 hFz (hφ_deriv 0)
    have hcomp : ψ = F ∘ (fun h : ℝ => z * (1 + h)) := rfl
    rw [hcomp, key.deriv]
    ring
  have hderiv2ψ : deriv (deriv ψ) 0 = z ^ 2 * deriv (deriv F) z := by
    have hev : deriv ψ =ᶠ[𝓝 (0:ℝ)] fun h => deriv F (z * (1 + h)) * z := by
      have hmem' : ∀ᶠ h in 𝓝 (0:ℝ), z * (1 + h) ∈ Set.Ioi 0 := by
        have hcont : Continuous (fun h : ℝ => z * (1 + h)) := by fun_prop
        exact hcont.continuousAt.preimage_mem_nhds (isOpen_Ioi.mem_nhds (by simpa using hz))
      filter_upwards [hmem'] with h hh
      have hFh : HasDerivAt F (deriv F (z * (1 + h))) (z * (1 + h)) :=
        ((hF.differentiableOn (by norm_num)).differentiableAt (isOpen_Ioi.mem_nhds hh)).hasDerivAt
      have key : HasDerivAt (F ∘ (fun h : ℝ => z * (1 + h))) (deriv F (z * (1 + h)) * z) h :=
        HasDerivAt.comp h hFh (hφ_deriv h)
      have hcomp : ψ = F ∘ (fun h : ℝ => z * (1 + h)) := rfl
      rw [hcomp, key.deriv]
    have h2 : deriv (deriv ψ) 0 = deriv (fun h : ℝ => deriv F (z * (1 + h)) * z) 0 := hev.deriv_eq
    have h3 : deriv (fun h : ℝ => deriv F (z * (1 + h)) * z) 0
        = deriv (fun h : ℝ => deriv F (z * (1 + h))) 0 * z := by
      have hd : DifferentiableAt ℝ (fun h : ℝ => deriv F (z * (1 + h))) 0 := by
        have hdz : DifferentiableAt ℝ (deriv F) ((fun h : ℝ => z * (1 + h)) 0) := by simpa using hdFd
        simpa [Function.comp_def] using
          hdz.comp 0 (by fun_prop : DifferentiableAt ℝ (fun h : ℝ => z * (1 + h)) 0)
      exact deriv_mul_const hd z
    have h4 : deriv (fun h : ℝ => deriv F (z * (1 + h))) 0 = deriv (deriv F) z * z := by
      have hdz : HasDerivAt (deriv F) (deriv (deriv F) z) ((fun h : ℝ => z * (1 + h)) 0) := by
        simpa using hdFd.hasDerivAt
      have key : HasDerivAt ((deriv F) ∘ (fun h : ℝ => z * (1 + h))) (deriv (deriv F) z * z) 0 :=
        HasDerivAt.comp 0 hdz (hφ_deriv 0)
      simpa [Function.comp_def] using key.deriv
    rw [h2, h3, h4]
    ring
  have hcomp : Filter.Tendsto (fun c : ℝ => c - 1) (nhdsWithin 1 (Set.Ioi 1)) (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc : Continuous fun c : ℝ => c - 1 := by fun_prop
      simpa using (hc.tendsto 1).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with c hc
      exact show 0 < c - 1 by linarith [show (1:ℝ) < c from hc]
  have hmain := (secondDiffQuot_aux hψ).comp hcomp
  rw [hderivψ, hderiv2ψ] at hmain
  have hfun : (fun c : ℝ => (F (c ^ 2 * z) - 2 * F (c * z) + F z) / (c - 1) ^ 2)
      = fun c : ℝ => (ψ (2 * (c - 1) + (c - 1) ^ 2) - 2 * ψ (c - 1) + ψ 0) / (c - 1) ^ 2 := by
    funext c
    simp only [hψdef]
    rw [show z * (1 + (2 * (c - 1) + (c - 1) ^ 2)) = c ^ 2 * z by ring,
        show z * (1 + (c - 1)) = c * z by ring,
        show z * (1 + 0) = z by ring]
  rw [hfun]
  exact hmain

end Work.FTS.EllipticEst.Cores.Dil
