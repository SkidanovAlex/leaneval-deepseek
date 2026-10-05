import Mathlib
import Submission.Work.RPB.Port.Drive.WindingNumber
import Submission.Work.RPB.Port.Drive.degree_homotopic
import Submission.Work.RPB.Port.Drive.ratio_loop
import Submission.Work.RPB.Port.Drive.winding_pair_ne

/-!
# A smooth Jordan curve has a point of non-zero winding number

`Work.RPB.Port.Drive.exists_winding_ne_zero`: a continuous injective `C¹` closed plane curve `γ` (a smooth
Jordan curve, in the `ℝ/ℤ` parametrisation) has a point `p` off it about which it winds non-trivially.

This is "input A of the capping" of Hugelmeyer's order theory: the curve separates the plane, so it
has an inside, and about an interior point the (doubled) winding number is `±2`.  The proof here
avoids the full Jordan separation theorem: it uses the local two-sided computation at a regular point
of the curve (`Work.RPB.Port.Drive.winding_pair_ne`), which produces two points off the curve with *different*
winding numbers; one of the two is then non-zero.

The inputs are

* `Work.RPB.Port.Drive.exists_deriv_ne_zero`: a `C¹` closed curve which is injective is not constant, hence has
  a parameter where its derivative is non-zero (otherwise it would be constant, contradicting
  injectivity);
* `Work.RPB.Port.Drive.winding_comp_add_right`: rotating the parameter of the curve does not change the
  winding number, so one may move the regular parameter to `0`;
* `Work.RPB.Port.Drive.winding_pair_ne` (a colleague's lemma, `Submission/Work/Drive/winding_pair_ne.lean`):
  the two points on the normal on either side of a regular point of the curve have different winding
  numbers, because the chord-ratio loop of the two families of chords has degree `2`.
-/

namespace Work.RPB.Port.Drive

open scoped Manifold ContDiff

noncomputable section

/-! ## Auxiliary lemmas -/

/-- Translating the parameter of a closed plane curve does not change its range. -/
lemma range_comp_add_right (γ : UnitAddCircle → ℝ × ℝ) (c : UnitAddCircle) :
    Set.range (fun u : UnitAddCircle => γ (u + c)) = Set.range γ := by
  ext p
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨u + c, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨v - c, by simp⟩

/-- **Rotating the parameter of a closed plane curve does not change the winding number** about a
point off it.  The shifted direction map is the original one precomposed with the rotation
`u ↦ u + c`, and `Work.RPB.Port.Drive.degree_comp_add_right` says the degree is unchanged. -/
theorem winding_comp_add_right (γ : UnitAddCircle → ℝ × ℝ) (hγ : Continuous γ)
    (c : UnitAddCircle) {p : ℝ × ℝ}
    (hp : p ∉ Set.range (fun u : UnitAddCircle => γ (u + c))) :
    winding (fun u : UnitAddCircle => γ (u + c))
        (hγ.comp (continuous_id.add continuous_const)) hp
      = winding γ hγ (by rwa [range_comp_add_right] at hp) := by
  have hdir : dirCurve (fun u : UnitAddCircle => γ (u + c))
        (hγ.comp (continuous_id.add continuous_const)) p hp
      = fun u : UnitAddCircle =>
          dirCurve γ hγ p (by rwa [range_comp_add_right] at hp) (u + c) := by
    funext u
    rfl
  rw [winding, winding]
  rw [degree_congr_fun hdir _ _]
  exact degree_comp_add_right _ _ c

/-- **A `C¹` injective closed plane curve has a parameter at which its derivative does not
vanish.**  Otherwise the derivative would vanish identically, so the curve would be constant, and
`γ 0 = γ (1/2)` would contradict injectivity since `1/2` is not an integer in `ℝ/ℤ`. -/
lemma exists_deriv_ne_zero (γ : UnitAddCircle → ℝ × ℝ) (hinj : Function.Injective γ)
    (hsmooth : ContDiff ℝ 1 (fun t : ℝ => γ (t : UnitAddCircle))) :
    ∃ t₀ : ℝ, deriv (fun t : ℝ => γ (t : UnitAddCircle)) t₀ ≠ 0 := by
  by_contra h
  push_neg at h
  have hdiff : Differentiable ℝ (fun t : ℝ => γ (t : UnitAddCircle)) :=
    hsmooth.differentiable (by norm_num)
  have hconst := is_const_of_deriv_eq_zero hdiff h
  have h01 : (0 : UnitAddCircle) = ((1 / 2 : ℝ) : UnitAddCircle) :=
    hinj (by simpa using hconst 0 (1 / 2))
  have hcoe : ((1 / 2 : ℝ) : UnitAddCircle) = 0 := h01.symm
  obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_of_pos_iff (p := (1 : ℝ))
    (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 1 / 2)).mp hcoe
  rw [nsmul_eq_mul, mul_one] at hn
  have h2 : ((2 * n : ℕ) : ℝ) = 1 := by push_cast; linarith
  have h3 : (2 * n : ℕ) = 1 := by exact_mod_cast h2
  omega

/-! ## The main theorem -/

open Manifold in
open scoped Manifold ContDiff in
/-- **Input A of the capping.**  A smooth embedded closed plane curve encloses some point: there is a
point of the plane off the curve about which the curve has non-zero (doubled-direction) winding
number.  With `winding_values`, `≠ 0` is the same as `= ±2`. -/
theorem exists_winding_ne_zero (γ : UnitAddCircle → ℝ × ℝ) (hγ : Continuous γ)
    (hinj : Function.Injective γ)
    (hsmooth : ContDiff ℝ 1 (fun t : ℝ => γ (t : UnitAddCircle))) :
    ∃ (p : ℝ × ℝ) (hp : p ∉ Set.range γ), Work.RPB.Port.Drive.winding γ hγ hp ≠ 0 := by
  -- a parameter where the derivative does not vanish
  obtain ⟨t₀, ht₀⟩ := exists_deriv_ne_zero γ hinj hsmooth
  set H : ℝ → ℝ × ℝ := fun t : ℝ => γ (t : UnitAddCircle) with hH
  have hHdiff : Differentiable ℝ H := by
    rw [hH]
    exact hsmooth.differentiable (by norm_num)
  have hderH : HasDerivAt H (deriv H t₀) t₀ := hHdiff.differentiableAt.hasDerivAt
  have hHne : deriv H t₀ ≠ 0 := by rwa [hH] at ht₀
  -- the shifted curve and the derivative of its rescaling at `0`
  set c : UnitAddCircle := (t₀ : UnitAddCircle) with hc
  set V : ℝ × ℝ := (1 / (2 * Real.pi)) • deriv H t₀ with hV
  have hVne : V ≠ 0 := by
    rw [hV]
    exact smul_ne_zero (by positivity) hHne
  have hγccont : Continuous (fun u : UnitAddCircle => γ (u + c)) :=
    hγ.comp (continuous_id.add continuous_const)
  have hγcinj : Function.Injective (fun u : UnitAddCircle => γ (u + c)) := fun u v huv =>
    add_right_cancel (hinj huv)
  have hφ : HasDerivAt (fun x : ℝ => x / (2 * Real.pi) + t₀) (1 / (2 * Real.pi)) 0 := by
    have h1 : HasDerivAt (fun x : ℝ => x / (2 * Real.pi)) (1 / (2 * Real.pi)) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).div_const (2 * Real.pi)
    simpa using h1.add_const t₀
  have hs : HasDerivAt (H ∘ fun x : ℝ => x / (2 * Real.pi) + t₀) V 0 := by
    have h := HasDerivAt.scomp_of_eq (0 : ℝ) hderH hφ (by simp)
    rw [hV]
    exact h
  have hSder : HasDerivAt (fun x : ℝ => (fun u : UnitAddCircle => γ (u + c))
      ((x / (2 * Real.pi) : ℝ) : UnitAddCircle)) V 0 := by
    have hfun : (H ∘ fun x : ℝ => x / (2 * Real.pi) + t₀)
        = fun x : ℝ => (fun u : UnitAddCircle => γ (u + c))
            ((x / (2 * Real.pi) : ℝ) : UnitAddCircle) := by
      funext x
      show γ (((x / (2 * Real.pi) + t₀ : ℝ)) : UnitAddCircle)
        = γ (((x / (2 * Real.pi) : ℝ) : UnitAddCircle) + c)
      rw [hc, ← AddCircle.coe_add]
    rwa [hfun] at hs
  -- the two-sided input at the regular parameter `0` of the shifted curve
  obtain ⟨p, hp, p', hp', hne⟩ :=
    winding_pair_ne (fun u : UnitAddCircle => γ (u + c)) hγccont hγcinj hVne hSder
  have hpγ : p ∉ Set.range γ := by rwa [range_comp_add_right γ c] at hp
  have hp'γ : p' ∉ Set.range γ := by rwa [range_comp_add_right γ c] at hp'
  -- the two windings differ, hence one of them is non-zero
  by_cases h0 : winding γ hγ hpγ = 0
  · refine ⟨p', hp'γ, ?_⟩
    intro hzero
    refine hne ?_
    calc winding (fun u : UnitAddCircle => γ (u + c)) hγccont hp
        = winding γ hγ hpγ := winding_comp_add_right γ hγ c hp
      _ = 0 := h0
      _ = winding γ hγ hp'γ := hzero.symm
      _ = winding (fun u : UnitAddCircle => γ (u + c)) hγccont hp' :=
          (winding_comp_add_right γ hγ c hp').symm
  · exact ⟨p, hpγ, h0⟩

end

end Work.RPB.Port.Drive
