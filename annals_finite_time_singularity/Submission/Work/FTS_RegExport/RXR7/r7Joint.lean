import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXR7.Defs
import Submission.Work.FTS_RegExport.RXR7.Joint.CLM
import Submission.Work.FTS_RegExport.RXR7.Joint.ProfBasic
import Submission.Work.FTS_RegExport.RXR7.Joint.Interior
import Submission.Work.FTS_RegExport.RXR7.Joint.Boundary
import Submission.Work.FTS_RegExport.RXR7.Joint.Assembly

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS_RegExport.RXR7

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- **RX-R7, the `hFjoint` field.**  Joint `C¹`-regularity of the full profile of the R7
block, `Prof α g p.1 p.2.1 p.2.2 = profFull α (extG (gS α (tauExt g))) p.1 p.2.1 p.2.2`, on the
slab `R7Slab S = (0,∞) × (0,π/2) × [0,S]` — i.e. *including* `τ = 0`, where `RegPkgMin.c1` (only
`τ > 0`) gives nothing.

Route.  Write `K` for `K7 α Φs E g`.  Two inputs are needed.

(A) **`K` is jointly continuous on the slab.**  By `hVP S hS`, the triple
`(Vz7ᵣ, Vθ7ᵣ, cs7ᵣ)` is continuous on `Ioi 0 ×ˢ Icc 0 (π/2) ×ˢ Icc 0 S` (`VelPkg.cont`), and by
the proved `Work.FTS_RegExport.RXT.jc3` the mixed jets `mixed j i (slice g τ)` (`j+i ≤ 3`) are
continuous on `Ioi 0 ×ˢ Ioo 0 (π/2) ×ˢ Icc 0 T`.  On `z > 0` and `τ ≥ 0`, `Prof α g` agrees with
`Ftau (pExp α) (GR α g) τ = F_* + slice (GR α g) τ = F_* + slice g τ` (use
`extG_of_pos`, `gS`, `tauExt_of_nonneg`, `slice_tauExt`), so `Prof`, `Dz (Prof)` and `pth (Prof)`
are jointly continuous there (`jc3` at `(0,0)`, `(1,0)`, `(0,1)` plus the explicit smooth `F_*`;
`pth = mixed 0 1 / sin 2θ`).  Product of jointly continuous functions gives `K` continuous.

(B) **The one-sided `C¹` at the boundary `τ = 0`.**  Fix `q = (z,θ,0) ∈ R7Slab S` and
`y = (z',θ',τ') ∈ R7Slab S` near `q`.  Decompose
`Prof(y) - Prof(q) = [Prof(z',θ',0) - Prof(q)] + [Prof(z',θ',τ') - Prof(z',θ',0)]`.
The first bracket is `o(‖y-q‖)` because the `τ = 0` slice is `C⁴`, hence `C¹`, on `Q0`
(`hOK.1.1.c4 0`; on the quadrant `Prof α g z θ 0 = F_* + g z θ 0`).  For the second bracket:
the map `s ↦ Prof α g z' θ' s` has derivative `-K(z',θ',s)` at every `s ∈ (0,τ']` (`hEq`), so the
FTC on `[ε,τ']` for `ε ↓ 0` (using `hOK.1.1.cont` for continuity at `s = 0` and boundedness of
`K` near `q`) gives `Prof(z',θ',τ') - Prof(z',θ',0) = -∫₀^{τ'} K(z',θ',s) ds`, whence
`|Prof(z',θ',τ') - Prof(z',θ',0) + K(q)τ'| ≤ τ'·sup_{s∈(0,τ')}|K(z',θ',s) - K(q)| ≤ ‖y-q‖·(small)`
by (A).  So the profile is differentiable within the slab at `q`, with the linear map whose
`(z,θ)`-part is the `C¹` differential of the `τ = 0` slice and whose `τ`-component is `-K(q)`.

Assembly: at `τ > 0` the profile is `C¹` around the point by `hOK.1.1.c1`
(`ContDiffAt` on `Ioi 0 ×ˢ Ioo 0 (π/2) ×ˢ Ioi 0`, transported along
`extG (GR α g) = g` on the quadrant); at `τ = 0` use (B).  Conclude `ContDiffOn ℝ 1` from
`contDiffWithinAt_succ_iff_hasFDerivWithinAt` with `n = 0` and the slab `R7Slab S` as the set,
the derivative function being continuous on the slab ((A) plus `jc3` for the spatial partials),
then `ContDiffOn` from `ContDiffWithinAt` at every point. -/
theorem r7Joint {α C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam} {S : ℝ}
    (hS : 0 < S) (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hSol : Work.FTS.FinalV2.Sol (Work.FTS.Regularity.pExp α) Φs E g)
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    (hμ : Work.FTS.RegExportIface.ClockBd α Φs E g)
    (hVP : ∀ S > 0, Work.FTS.RegExportIface.VelPkg (Work.FTS.Regularity.pExp α)
      (Work.FTS_RegExport.RXR7.μR α Φs E g) (Work.FTS_RegExport.RXR7.GR α g)
      (Work.FTS_RegExport.RXR7.ΦR α Φs E g) S)
    (hEq : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => Work.FTS_RegExport.RXR7.Prof α g z θ s)
        (-(Work.FTS_RegExport.RXR7.K7 α Φs E g z θ τ)) τ) :
    ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => Work.FTS_RegExport.RXR7.Prof α g p.1 p.2.1 p.2.2)
      (Work.FTS_RegExport.RXR7.R7Slab S) := by
  -- the derivative function is jointly continuous on the slab
  have hFD : ContinuousOn (fun p : ℝ × ℝ × ℝ => ProfD α Φs E g p) (R7Slab S) :=
    ProfD_contOn_slab hS hα hα13 hOK (hVP S hS)
  -- and it is the honest derivative at every point of the slab
  have hderiv := profile_hasFDerivWithinAt hS hα hα13 hOK (hVP S hS) hEq
  intro q hq
  rw [show (1 : WithTop ℕ∞) = 0 + 1 from rfl]
  rw [contDiffWithinAt_succ_iff_hasFDerivWithinAt' (n := 0)
    (by simp : (0 : WithTop ℕ∞) ≠ ((⊤ : ℕ∞) : WithTop ℕ∞))]
  refine ⟨R7Slab S, ?_, ?_, ?_, (fun p => ProfD α Φs E g p), hderiv, ?_⟩
  · rw [mem_nhdsWithin_insert]
    exact ⟨hq, self_mem_nhdsWithin⟩
  · exact subset_insert q (R7Slab S)
  · intro h; exact absurd h (by simp)
  · rw [contDiffWithinAt_zero hq]
    exact ⟨univ, Filter.univ_mem, by simpa using hFD⟩
end Work.FTS_RegExport.RXR7
