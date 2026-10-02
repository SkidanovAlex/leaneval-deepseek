import Mathlib
import Submission.Work.Landing.Rays
import Submission.Work.Landing.Land.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Landing.Caratheodory

open Classical Filter
open LeanEval.ComplexAnalysis (Tantibar)
open Work.ParamRays (IsDynBottcher Escaping)

/-- A point of the dynamic ray at angle `θ` is recovered from its Böttcher coordinate by the
inverse coordinate `Ψ` (which is defined on the exterior of the unit disk): `z = Ψ (φ z)`. -/
private lemma dynRay_eq_Psi {c : ℂ} {φ Ψ : ℂ → ℂ}
    (h : Work.Landing.IsDynBottcherHomeo c φ)
    (hΨ : ∀ w : ℂ, 1 < ‖w‖ → Escaping c (Ψ w) ∧ φ (Ψ w) = w)
    {θ : ℝ} {z : ℂ} (hz : z ∈ Work.Landing.dynRay c φ θ) : z = Ψ (φ z) := by
  obtain ⟨hzesc, hzray⟩ := hz
  obtain ⟨hΨesc, hΨphi⟩ := hΨ (φ z) (Work.Landing.Rays.radialRay_norm hzray)
  exact h.2.1 z (Ψ (φ z)) hzesc hΨesc hΨphi.symm

/-- A point of the dynamic ray has Böttcher coordinate on the radial line of its angle:
`φ z = ‖φ z‖ • rayDirection θ`. -/
private lemma dynRay_phi_eq_norm_smul {c : ℂ} {φ : ℂ → ℂ} {θ : ℝ} {z : ℂ}
    (hz : z ∈ Work.Landing.dynRay c φ θ) :
    φ z = (‖φ z‖ : ℂ) * Work.Landing.rayDirection θ := by
  obtain ⟨-, r, hr, hrz⟩ := hz
  have h1 : ‖φ z‖ = r := by
    rw [hrz, norm_mul, Work.Landing.Rays.norm_rayDirection, mul_one, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by linarith)]
  rw [h1]
  exact hrz

/-- If the inverse Böttcher coordinate extends continuously to the unit circle, then every dynamic
ray lands: the ray at angle `θ` lands at `Ψ (rayDirection θ)`.  This is the existence half of
Milnor 18.10, reduced to the Carathéodory/local-connectivity input `InverseBottcherExtends`. -/
theorem landsAt_of_extension {c : ℂ} {φ Ψ : ℂ → ℂ}
    (h : Work.Landing.IsDynBottcherHomeo c φ)
    (hcont : ContinuousOn Ψ {w : ℂ | 1 ≤ ‖w‖})
    (hΨ : ∀ w : ℂ, 1 < ‖w‖ → Work.ParamRays.Escaping c (Ψ w) ∧ φ (Ψ w) = w) (θ : ℝ) :
    Work.Landing.landsAt c θ (Ψ (Work.Landing.rayDirection θ)) := by
  refine ⟨φ, h.1, ?_⟩
  set u : ℂ := Work.Landing.rayDirection θ with hu
  have hun : ‖u‖ = 1 := Work.Landing.Rays.norm_rayDirection θ
  -- the given set and continuity of `Ψ` at `u`
  have humem : u ∈ {w : ℂ | 1 ≤ ‖w‖} := by
    show (1 : ℝ) ≤ ‖u‖
    rw [hun]
  have hcu : ContinuousWithinAt Ψ {w : ℂ | 1 ≤ ‖w‖} u := hcont.continuousWithinAt humem
  have hcε : ∀ ε > 0, ∃ δ > 0, ∀ y ∈ {w : ℂ | 1 ≤ ‖w‖},
      dist y u < δ → dist (Ψ y) (Ψ u) < ε := by
    intro ε hε
    obtain ⟨δ, hδ, hδp⟩ := Metric.continuousWithinAt_iff.mp hcu ε hε
    exact ⟨δ, hδ, fun y hy hd => hδp hy hd⟩
  -- the points `r • u` for `r > 1` lie on the ray and have Böttcher coordinate `r • u`
  have hkey : ∀ r : ℝ, 1 < r →
      Ψ ((r : ℂ) * u) ∈ Work.Landing.dynRay c φ θ ∧ φ (Ψ ((r : ℂ) * u)) = (r : ℂ) * u := by
    intro r hr
    have hnorm : ‖(r : ℂ) * u‖ = r := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith), hun, mul_one]
    obtain ⟨hesc, hphi⟩ := hΨ ((r : ℂ) * u) (by rw [hnorm]; exact hr)
    exact ⟨⟨hesc, ⟨r, hr, hphi⟩⟩, hphi⟩
  have hsmul_norm : ∀ r : ℝ, 0 < r → ‖(r : ℂ) * u‖ = r := by
    intro r hr
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr, hun, mul_one]
  have hsmul_mem : ∀ r : ℝ, 1 ≤ r → (r : ℂ) * u ∈ {w : ℂ | 1 ≤ ‖w‖} := by
    intro r hr
    show (1 : ℝ) ≤ ‖(r : ℂ) * u‖
    rw [hsmul_norm r (lt_of_lt_of_le zero_lt_one hr)]
    exact hr
  refine Set.Subset.antisymm ?_ ?_
  · -- `rayAccum c φ θ ⊆ {Ψ u}`
    intro x hx
    rw [Set.mem_singleton_iff]
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨δ, hδ, hδp⟩ := hcε (ε / 2) (by linarith)
    set ρ : ℝ := 1 + δ / 2 with hρdef
    have hρ1 : 1 < ρ := by rw [hρdef]; linarith
    obtain ⟨z, hz, hzd⟩ := Metric.mem_closure_iff.mp (hx ρ hρ1) (ε / 2) (by linarith)
    have hzray : z ∈ Work.Landing.dynRay c φ θ := hz.1
    have hzeq : z = Ψ (φ z) := dynRay_eq_Psi h hΨ hzray
    have hzphi : φ z = (‖φ z‖ : ℂ) * u := dynRay_phi_eq_norm_smul hzray
    have hz1 : 1 < ‖φ z‖ := Work.Landing.Rays.radialRay_norm hzray.2
    have hdistu : dist (φ z) u < δ := by
      have hsub : φ z - u = ((‖φ z‖ - 1 : ℝ) : ℂ) * u := by
        nth_rewrite 1 [hzphi]
        push_cast
        ring
      rw [dist_eq_norm, hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, hun, mul_one,
        abs_of_nonneg (by linarith)]
      linarith [hz.2, hρdef, hδ]
    have hzmem : φ z ∈ {w : ℂ | 1 ≤ ‖w‖} := by
      show (1 : ℝ) ≤ ‖φ z‖
      exact le_of_lt hz1
    have hcz : dist z (Ψ u) < ε / 2 := by
      have h := hδp (φ z) hzmem hdistu
      rwa [← hzeq] at h
    refine le_of_lt ?_
    calc dist x (Ψ u) ≤ dist x z + dist z (Ψ u) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by linarith
      _ = ε := by ring
  · -- `{Ψ u} ⊆ rayAccum c φ θ`
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    intro ρ hρ
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨δ, hδ, hδp⟩ := hcε ε hε
    set r : ℝ := 1 + min (δ / 2) ((ρ - 1) / 2) with hrdef
    have hminpos : 0 < min (δ / 2) ((ρ - 1) / 2) :=
      lt_min (by linarith) (by linarith)
    have hr1 : 1 < r := by rw [hrdef]; linarith [hminpos]
    have hrρ : r < ρ := by
      rw [hrdef]
      have h1 : min (δ / 2) ((ρ - 1) / 2) ≤ (ρ - 1) / 2 := min_le_right _ _
      linarith
    have hrδ : r - 1 < δ := by
      rw [hrdef]
      have h1 : min (δ / 2) ((ρ - 1) / 2) ≤ δ / 2 := min_le_left _ _
      linarith
    obtain ⟨hzray, hzphi⟩ := hkey r hr1
    refine ⟨Ψ ((r : ℂ) * u), ?_, ?_⟩
    · refine ⟨hzray, ?_⟩
      rw [hzphi, hsmul_norm r (by linarith)]
      exact le_of_lt hrρ
    · have hdist : dist (Ψ ((r : ℂ) * u)) (Ψ u) < ε := by
        refine hδp ((r : ℂ) * u) (hsmul_mem r (by linarith)) ?_
        rw [dist_eq_norm]
        have hsub : (r : ℂ) * u - u = ((r - 1 : ℝ) : ℂ) * u := by
          push_cast
          ring
        rw [hsub, norm_mul, Complex.norm_real, Real.norm_eq_abs, hun, mul_one,
          abs_of_nonneg (by linarith)]
        exact hrδ
      rw [dist_comm]
      exact hdist

end Work.Landing.Caratheodory
