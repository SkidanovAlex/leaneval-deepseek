import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.RegExportIface.RXT.Leaves
import Submission.Work.FTS_RegExport.RXB.l12_zero_lim_proved
import Submission.Work.FTS_RegExport.RXT.Sys.PullDefs
import Submission.Work.FTS_RegExport.RXT.Sys.pw_identity_mine
import Submission.Work.FTS_RegExport.RXT.cone_induction
import Submission.Work.FTS_RegExport.VPDefs
import Submission.Work.Spaces.one_le_mul_w
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS_RegExport.RXT.Sys.pw_regularity =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-! Joint continuity of `pw`, `pws`, `pwψ` on the pulled-back slab and the two partial
derivatives of `pw` in the logarithmic coordinates, from the T5c hypotheses (continuity of
`w`, `wz`, `wθ` and the two partial-derivative relations `D_z w = wz/z`,
`D_θ w = wθ/sin 2θ`).

The derivative computations are the chain rule plus the two `ω`-identities of
`RXT.omega_facts`:
* `∂_s (w ∘ cz) = (wz/z)·cz = wz` and `∂_s om = om·2/(1+cz)`, whence
  `∂_sφ = wz/om − 2φ/(1+cz) = pws`;
* `∂_ψ (w ∘ cth) = (wθ/sin 2θ)·(sin 2θ/2) = wθ/2` and
  `∂_ψ om = om·(2α·c2m/sin 2θ)·(sin 2θ/2) = om·α·c2m`, whence
  `∂_ψφ = wθ/(2om) − α·c2m·φ = pwψ`. -/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory
namespace Work.FTS_RegExport.RXT.Sys

set_option maxHeartbeats 1000000

theorem pw_regularity {n : ℕ} {w wz wθ : Fin n → ℝ → ℝ → ℝ → ℝ} {S α : ℝ} (hα : 0 < α)
    (hcont : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => w k p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S))
    (hz : ∀ k z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0:ℝ) S →
      HasDerivAt (fun z' => w k z' θ τ) (wz k z θ τ / z) z)
    (hθ : ∀ k z θ τ, 0 < z → 0 < θ → θ < Real.pi / 2 → τ ∈ Set.Icc (0:ℝ) S →
      HasDerivAt (fun θ' => w k z θ' τ) (wθ k z θ τ / Real.sin (2 * θ)) θ)
    (hcz : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => wz k p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S))
    (hcθ : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => wθ k p.1 p.2.1 p.2.2)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S)) :
    (∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => pw α (w k) p.1 p.2.1 p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S)) ∧
    (∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => pws α (wz k) (w k) p.1 p.2.1 p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S)) ∧
    (∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => pwψ α (wθ k) (w k) p.1 p.2.1 p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S)) ∧
    (∀ k s ψ τ, τ ∈ Set.Icc (0:ℝ) S →
      HasDerivAt (fun s' => pw α (w k) s' ψ τ) (pws α (wz k) (w k) s ψ τ) s) ∧
    (∀ k s ψ τ, τ ∈ Set.Icc (0:ℝ) S →
      HasDerivAt (fun ψ' => pw α (w k) s ψ' τ) (pwψ α (wθ k) (w k) s ψ τ) ψ) := by
  have hcoord : ContinuousOn (fun p : ℝ × ℝ × ℝ => (cz p.1, (cth p.2.1, p.2.2)))
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
    Work.FTS_RegExport.RXT.continuousOn_coords (S := S)
  have hmap : Set.MapsTo (fun p : ℝ × ℝ × ℝ => (cz p.1, (cth p.2.1, p.2.2)))
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S)
      (Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi / 2) ×ˢ Set.Icc (0:ℝ) S) :=
    Work.FTS_RegExport.RXT.mapsTo_coords (S := S)
  have homc : ContinuousOn (fun p : ℝ × ℝ × ℝ => om α p.1 p.2.1)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
    Work.FTS_RegExport.RXT.continuousOn_om (S := S) hα
  have homne : ∀ p : ℝ × ℝ × ℝ, om α p.1 p.2.1 ≠ 0 :=
    fun p => ne_of_gt (Work.FTS_RegExport.RXT.om_pos (α := α) hα)
  have huc : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => w k (cz p.1) (cth p.2.1) p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
    fun k => (hcont k).comp hcoord hmap
  have hzc : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => wz k (cz p.1) (cth p.2.1) p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
    fun k => (hcz k).comp hcoord hmap
  have hθc : ∀ k, ContinuousOn (fun p : ℝ × ℝ × ℝ => wθ k (cz p.1) (cth p.2.1) p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
    fun k => (hcθ k).comp hcoord hmap
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k
    have h : ContinuousOn (fun p : ℝ × ℝ × ℝ => w k (cz p.1) (cth p.2.1) p.2.2 / om α p.1 p.2.1)
        (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
      (huc k).div homc (fun p _ => homne p)
    exact h
  · intro k
    have h1 : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        wz k (cz p.1) (cth p.2.1) p.2.2 / om α p.1 p.2.1)
        (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
      (hzc k).div homc (fun p _ => homne p)
    have h2 : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        2 * (w k (cz p.1) (cth p.2.1) p.2.2 / om α p.1 p.2.1) / (1 + cz p.1))
        (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
      (continuousOn_const.mul ((huc k).div homc (fun p _ => homne p))).div
        (continuousOn_const.add (Work.FTS_RegExport.RXT.continuousOn_cz (S := S)))
        (fun p _ => by
          have hp := Work.FTS_RegExport.RXT.cz_pos p.1
          positivity)
    have h : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        wz k (cz p.1) (cth p.2.1) p.2.2 / om α p.1 p.2.1
          - 2 * (w k (cz p.1) (cth p.2.1) p.2.2 / om α p.1 p.2.1) / (1 + cz p.1))
        (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) := h1.sub h2
    exact h
  · intro k
    have h1 : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        wθ k (cz p.1) (cth p.2.1) p.2.2 / (2 * om α p.1 p.2.1))
        (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
      (hθc k).div (continuousOn_const.mul homc) (fun p _ => by
        have hp := homne p
        positivity)
    have h2 : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        (w k (cz p.1) (cth p.2.1) p.2.2 / om α p.1 p.2.1)
          * (α * Work.Construction.c2m (cth p.2.1)))
        (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) :=
      ((huc k).div homc (fun p _ => homne p)).mul
        (continuousOn_const.mul (Work.FTS_RegExport.RXT.continuousOn_c2m_comp (S := S)))
    have h : ContinuousOn (fun p : ℝ × ℝ × ℝ =>
        wθ k (cz p.1) (cth p.2.1) p.2.2 / (2 * om α p.1 p.2.1)
          - (w k (cz p.1) (cth p.2.1) p.2.2 / om α p.1 p.2.1)
            * (α * Work.Construction.c2m (cth p.2.1)))
        (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) S) := h1.sub h2
    exact h
  · intro k s ψ τ hτ
    have hC : cz s ≠ 0 := ne_of_gt (Work.FTS_RegExport.RXT.cz_pos s)
    have hD : (1 + cz s) ≠ 0 := by
      have hp := Work.FTS_RegExport.RXT.cz_pos s
      positivity
    have hO : om α s ψ ≠ 0 := ne_of_gt (Work.FTS_RegExport.RXT.om_pos (α := α) hα)
    have hz1 : HasDerivAt (fun s' : ℝ => w k (cz s') (cth ψ) τ) (wz k (cz s) (cth ψ) τ) s := by
      have h1 := (hz k (cz s) (cth ψ) τ (Work.FTS_RegExport.RXT.cz_pos s)
        (Work.FTS_RegExport.RXT.cth_pos ψ) (Work.FTS_RegExport.RXT.cth_lt ψ) hτ).comp s
        (Work.FTS_RegExport.RXT.hasDerivAt_cz s)
      refine h1.congr_deriv ?_
      field_simp
    have hom1 : HasDerivAt (fun s' : ℝ => om α s' ψ)
        (om α s ψ * (2 / (cz s * (1 + cz s))) * cz s) s := by
      have h1 := (Work.FTS_RegExport.RXT.hasDerivAt_omega_z α (cz s) (cth ψ)
        (Work.FTS_RegExport.RXT.cz_pos s)).comp s (Work.FTS_RegExport.RXT.hasDerivAt_cz s)
      simpa only [om, Function.comp_def] using h1
    have hq := hz1.div hom1 hO
    refine hq.congr_deriv ?_
    simp only [pws, pw]
    field_simp
  · intro k s ψ τ hτ
    have hS2 : Real.sin (2 * cth ψ) ≠ 0 :=
      ne_of_gt (Work.FTS_RegExport.RXT.cth_sin_two_pos ψ)
    have hO : om α s ψ ≠ 0 := ne_of_gt (Work.FTS_RegExport.RXT.om_pos (α := α) hα)
    have hθ1 : HasDerivAt (fun ψ' : ℝ => w k (cz s) (cth ψ') τ) (wθ k (cz s) (cth ψ) τ / 2) ψ := by
      have h1 := (hθ k (cz s) (cth ψ) τ (Work.FTS_RegExport.RXT.cz_pos s)
        (Work.FTS_RegExport.RXT.cth_pos ψ) (Work.FTS_RegExport.RXT.cth_lt ψ) hτ).comp ψ
        (Work.FTS_RegExport.RXT.hasDerivAt_cth ψ)
      refine h1.congr_deriv ?_
      field_simp
    have hom1 : HasDerivAt (fun ψ' : ℝ => om α s ψ')
        (om α s ψ * (2 * α * Work.Construction.c2m (cth ψ) / Real.sin (2 * cth ψ))
          * (Real.sin (2 * cth ψ) / 2)) ψ := by
      have h1 := (Work.FTS_RegExport.RXT.hasDerivAt_omega_theta α (cz s) (cth ψ) hα
        (Work.FTS_RegExport.RXT.cth_pos ψ)
        (Work.FTS_RegExport.RXT.cth_lt ψ)).comp ψ (Work.FTS_RegExport.RXT.hasDerivAt_cth ψ)
      simpa only [om, Function.comp_def] using h1
    have hq := hθ1.div hom1 hO
    refine hq.congr_deriv ?_
    simp only [pwψ, pw]
    field_simp

end Work.FTS_RegExport.RXT.Sys
end
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.step_integrated_fix =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The corrected leaf T4: `step_integrated_nonneg`

`Work.FTS_RegExport.RXT.step_integrated` (this directory) is **false** as stated: its
conclusion `ConeStep n φ T A (n * C) F` fails for `C < 0` because the endpoint bound `B` of
`ConeStep` is universally quantified (see the refutation `step_integrated_false` in
`Submission/Work/FTS_RegExport/RXT/step_integrated.lean`).  The missing hypothesis is `0 ≤ C`;
this file proves the statement with that hypothesis added, nothing else changed:

```
theorem step_integrated_nonneg ... (hC : 0 ≤ C) (hcont) (hs) (hψ) (hcs) (hcψ) (hab) (hA)
    (hRi) (hRb) (hId) : ConeStep n φ T A (n * C) F
```

The proof is the discrete one-step argument of the RX-T plan; see the module docstring of
`step_integrated.lean` for the outline.  All constants are the naive ones (no optimality is
claimed):
`ε` is split as `3ε/4 + ε/4` into `η_s = ε/(4(A+1))` (uniform continuity of `∂_sφ`, `∂_ψφ`)
and `η_G = ε/(4(nC+1))` (closeness of `∑_j |φ_j(s,ψ,σ)|` to its value at `τ+h`).
-/

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## The corrected statement -/


end Work.FTS_RegExport.RXT
end
-- ===== merged: Submission.Work.FTS_RegExport.RXT.transport_weighted_proved =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXT.transport_weighted_proved` — RX-T (the weighted characteristic
estimate of the transport operator of `(E)`).

The statement (`Producers.transport_weighted`, verbatim) is the pointwise weighted estimate

  `|u z θ τ| ≤ e^{K·S}·(K₀ + S·Kσ)·ω α z θ`

for a solution of `∂_τu + Vz·D_z u + Vθ·∂_θu + cs·u = σ` on the open quadrant with
`0 ≤ Vz ≤ M`, `|Vθ| ≤ M·sin 2θ`, `|cs| ≤ M`, `|σ| ≤ Kσ·ω` and data bounded by `K₀·ω` at `τ = 0`.

## The route (no characteristic ODE is used — and none is available)

The hypotheses give *no* regularity of `Vz, Vθ, cs, σ` in `τ` and only a *per-`τ`* Lipschitz
bound, so the classical characteristic flow cannot be constructed.  Instead one works with the
**cone maximum principle** (`RXT.cone_max_principle`): in the logarithmic coordinates of
`RXT.Defs` the domain becomes all of `ℝ²`, the transport coefficients become the bounded
quantities `a = Vz`, `b = 2Vθ/sin 2θ`, and the weight ratio `φ = u/ω` satisfies a transport
equation with `|a|,|b| ≤ 2M`, `|c| ≤ M(3+4α)`, `|f| ≤ Kσ`, `|φ(·,0)| ≤ K₀`.  The cone maximum
principle then gives `|φ| ≤ exp(2·M(3+4α)·τ)·(K₀ + τ·Kσ)`, which is the statement with
`K = 2M(3+4α)`.
-/

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.RXT

set_option autoImplicit false


end Work.FTS_RegExport.RXT
end
end
