/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/MixedSliceDerivAt.lean` — the raw slot chain rule, at
every point of the quadrant

`EpsE4Thr.mixed_slice_deriv` (proved) is stated on a *compact box* `Icc z₁ z₂ ×ˢ Icc θ₁ θ₂` of
the quadrant, with the slot bound `hbdd` given as a single constant `C` on that box.  The
consumers (`EpsE4Thr.hasDerivWithinAt_mixed_JfamP_raw`, and through it the energy identities of
`AprioriP`) need it **at every point of the quadrant, uniformly in the fake time**, in the
`HasDerivAt` form

  `hraw : ∀ s ∈ (0,T), ∀ (z,θ) ∈ Q0, HasDerivAt (fun x => mixed j i (slice g x) z θ)
            (mixed j i (epsRHSP … s) z θ) s`,

with the domination hypothesis given in the standard *locally uniform on compact subsets of `Q0`*
form (the shape used by `EpsSlotAux`/`smoothOpen_slice_of_epsRHSP`).  This module performs that
conversion: at a given `(z,θ)` it selects the box `(z/2, 2z) × (θ/2, (θ+π/2)/2) ⊂ Q0` and applies
the box statement with the constant supplied by `hbdd` on the compact closure of that box.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.mixed_slice_deriv

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- **The raw slot chain rule at every point of the quadrant** (from the box form
`mixed_slice_deriv`).  `hbdd`/`hbddR` are the locally uniform slot bounds of the two families on
compact subsets of the open quadrant. -/
theorem mixed_slice_deriv_at {ρ : ℝ × ℝ → ℝ} {α T ε : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g : Fam} {j i : ℕ}
    (hρ : IsSmoothKernel ρ) (hε : 0 < ε)
    (hsol : IsEpsSolP α ρ ε T Φs E g₀ g) (hji : j + i ≤ 4)
    (hsm : ∀ s ∈ Set.Icc 0 T,
      Work.FTS.EllipticEst.SmoothOpen (slice g s))
    (hsmR : ∀ s ∈ Set.Icc 0 T,
      Work.FTS.EllipticEst.SmoothOpen (epsRHSP α ρ ε Φs E g s))
    (hmeas : ∀ (k l : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l (slice g s) z θ)
        (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hmeasR : ∀ (k l : ℕ) (z θ : ℝ), (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed k l
        (epsRHSP α ρ ε Φs E g s) z θ) (volume.restrict (Set.Icc (0 : ℝ) T)))
    (hbdd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), k + l ≤ 4 → ∀ q : ℝ × ℝ,
        q ∈ K → |Work.Spaces.mixed k l (slice g s) q.1 q.2| ≤ C)
    (hbddR : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), k + l ≤ 4 → ∀ q : ℝ × ℝ,
        q ∈ K → |Work.Spaces.mixed k l (epsRHSP α ρ ε Φs E g s) q.1 q.2| ≤ C)
    (hcontR : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) → ContinuousOn (fun s : ℝ =>
      Work.Spaces.mixed j i (epsRHSP α ρ ε Φs E g s) z θ) (Set.Icc 0 T))
    {s : ℝ} (hs : s ∈ Set.Ioo 0 T) :
    ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      HasDerivAt (fun x => Work.Spaces.mixed j i (slice g x) z θ)
        (Work.Spaces.mixed j i (epsRHSP α ρ ε Φs E g s) z θ) s := by
  intro z θ hz hθ
  -- the box around `(z,θ)`, strictly inside the open quadrant
  have hz2 : 0 < 2 * z := by linarith [hz]
  have hθ2 : 0 < π / 2 - θ := by linarith [hθ.2, Real.pi_pos]
  have hb1 : 0 < z / 2 := by linarith [hz]
  have hb3 : 0 < θ / 2 := by linarith [hθ.1]
  have hb4 : (θ + π / 2) / 2 < π / 2 := by linarith [hθ.2, Real.pi_pos]
  have hKQ : Set.Icc (z / 2) (2 * z) ×ˢ Set.Icc (θ / 2) ((θ + π / 2) / 2)
      ⊆ Work.FTS.EllipticEst.Q0 := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    exact ⟨lt_of_lt_of_le hb1 ha.1, lt_of_lt_of_le hb3 hb.1, lt_of_le_of_lt hb.2 hb4⟩
  obtain ⟨C, hC0, hC⟩ := hbdd _ (isCompact_Icc.prod isCompact_Icc) hKQ
  obtain ⟨C', hC'0, hC'⟩ := hbddR _ (isCompact_Icc.prod isCompact_Icc) hKQ
  -- the box hypotheses of the box statement
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), k + l ≤ 4 → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc (z / 2) (2 * z) ×ˢ Set.Icc (θ / 2) ((θ + π / 2) / 2) →
        |Work.Spaces.mixed k l (slice g s) q.1 q.2| ≤ max C C' := fun s hs k l hkl q hq =>
    le_trans (hC s hs k l hkl q hq) (le_max_left _ _)
  have hboundR : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ (k l : ℕ), k + l ≤ 4 → ∀ q : ℝ × ℝ,
      q ∈ Set.Icc (z / 2) (2 * z) ×ˢ Set.Icc (θ / 2) ((θ + π / 2) / 2) →
        |Work.Spaces.mixed k l (epsRHSP α ρ ε Φs E g s) q.1 q.2| ≤ max C C' :=
    fun s hs k l hkl q hq => le_trans (hC' s hs k l hkl q hq) (le_max_right _ _)
  have hzz : (z, θ) ∈ Set.Ioo (z / 2) (2 * z) ×ˢ Set.Ioo (θ / 2) ((θ + π / 2) / 2) :=
    ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  exact (mixed_slice_deriv (C := max C C') hρ hε hsol hsm hsmR hmeas hmeasR
    (le_max_of_le_left hC0) hbound hboundR hKQ hzz hji (hcontR z θ hz hθ) hs).hasDerivAt
    (Icc_mem_nhds hs.1 hs.2)

end Work.FTS.StrongEps.EpsE4Thr
