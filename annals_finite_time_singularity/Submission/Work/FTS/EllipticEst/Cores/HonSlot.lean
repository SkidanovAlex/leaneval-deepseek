/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Cores/HonSlot` — single-slot honesty extraction from `HkMem`

`Work.Spaces.HkMem α k f` says that the whole `ℋ^k`-integrand of `f` is honest (integrable
`θ`-slices, integrable slice-integral).  Since the integrand is a *sum of squares* of the
weighted derivatives, honesty at order `k` gives honesty of every single slot at order `0`:

  `HkMem α k f → HkMem α 0 (D_z^i f)`  for `i ≤ k`,

and for the angular slot

  `HkMem α k (∂_θ f) → HkMem α 0 (D_z (∂_θ f))`  for `1 ≤ k`.

## Why this is recorded

The tree's Step 2 of `prop:H2` (`I₁`, the coercivity of `L₀` on the orthogonal complement of
`sin 2θ`) is **false** in the class `AeData` exactly because that class does not control the
`θ → π/2⁻` trace of `U = z∂_z u`; see `Submission/Work/FTS/EllipticEst/H2W/AeWAux/
NOTES_aeI1Data_FALSE.md` and the analysis in `H2W/AngBW/Chain/aeI1Paper.lean`.  The documented
repair is to add the *mixed-derivative* honesty

  `HkMem α 0 (fun z θ => z * ∂_z ∂_θ u z θ)`   (equivalently the finiteness of `∫∫ (∂_θ U)² ρ`),

which is what makes the endpoint term `T` of `S2` vanish.  The weak class `TT.EllWeakPos` used by
the current `TT` chain does **not** carry it, but the *trace-free* class `EllHypT`
(`Submission/Work/FTS/EllipticEst/RegQ.lean`) **does**: its field `memDth : HkMem α k (∂_θ Ψ)`
has the slot `i = 1` of the pure `D_z`-sum, i.e. exactly `HkMem α 0 (D_z ∂_θ Ψ)`.  The lemmas
below make that extraction explicit, so that a repaired chain stated on the trace-free class can
consume the honesty without redoing the descent.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.RegQ

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores

set_option autoImplicit false

/-! ## The level-`0` integrand -/

/-- At order `0` the `ℋ^0`-integrand is the single weighted square of the function itself (the
mixed sum is empty because every mixed slot carries `1 ≤ i` with `i + j ≤ 0`, which is
unsatisfiable). -/
theorem HkIntegrand_zero_apply (α : ℝ) (g : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-! ## Single-slot honesty -/

/-- **A single pure `D_z`-slot of an honest `ℋ^k`-function is honest at order `0`.**  This is the
`ℋ^k`-analogue of `TT.HkMem_descend_open` for *other* slots than the function itself: the slot
`D_z^i f` is bounded pointwise by the whole integrand (`Work.Spaces.sq_le_HkIntegrand_z`), and the
open-quadrant smoothness of `f` makes the smaller integrand continuous there, hence a.e. strongly
measurable. -/
theorem HkMem_zero_of_DzIter_slot {α : ℝ} {k i : ℕ} {f : ℝ → ℝ → ℝ} (hi : i ≤ k)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hm : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α 0 (Work.Spaces.DzIter i f) :=
  Work.FTS.LocData.HkMem_of_majorant α 0
    ((hf.DzIter i).continuousOn_HkIntegrand α 0) hm.1 hm.2
    (fun z _ θ _ => by
      rw [HkIntegrand_zero_apply]
      exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ i hi)

/-- The same for the *first angular slot* of `f`: `HkMem α k (∂_θ f)` yields
`HkMem α 0 (D_z ∂_θ f)`, i.e. the finiteness of `∫∫ (∂_θ (z ∂_z f))² w² sin(2θ)^{-η}` (up to the
commutation of `∂_θ` with `z ∂_z`). -/
theorem HkMem_zero_of_DzIter_one_pth {α : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ} (hk : 1 ≤ k)
    (hf : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth f))
    (hm : Work.Spaces.HkMem α k (Work.Spaces.pth f)) :
    Work.Spaces.HkMem α 0 (Work.Spaces.Dz (Work.Spaces.pth f)) := by
  have h := HkMem_zero_of_DzIter_slot (α := α) (k := k) (i := 1) hk hf hm
  simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero] using h

/-! ## The honesty the trace-free class supplies -/

/-- `SmoothQuad f` implies `SmoothOpen f` (the strip of `SmoothQuad` contains the open
quadrant). -/
theorem smoothOpen_of_smoothQuad {f : ℝ → ℝ → ℝ}
    (h : Work.FTS.LocData.SmoothQuad f) : Work.FTS.EllipticEst.SmoothOpen f :=
  h.mono (by
    rw [Work.FTS.EllipticEst.Q0]
    exact Set.prod_mono (Set.Ioi_subset_Ioi (by norm_num)) (le_refl _))

/-- **The mixed-derivative honesty of the trace-free class.**  For `k ≥ 2` and data of `EllHypT`,
the function `z ∂_z ∂_θ Ψ` has an honest `ℋ^0`-integrand.  By Clairaut this is `∂_θ (z ∂_z Ψ)`,
i.e. `∂_θ U` for `U = z ∂_z Ψ`: exactly the quantity whose finiteness the `I₁` step of `prop:H2`
needs (and which `TT.EllWeakPos` does not provide). -/
theorem EllHypT.hkMem_Dz_pth {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.EllHypT α k F Ψ) :
    Work.Spaces.HkMem α 0 (Work.Spaces.Dz (Work.Spaces.pth Ψ)) :=
  HkMem_zero_of_DzIter_one_pth (α := α) (k := k) (f := Ψ) (by omega)
    ((smoothOpen_of_smoothQuad h.quadPsi).pth) h.memDth

/-- The `z`-weighted first-order honesty `HkMem α 0 (z ∂_z Ψ)` of the trace-free class (the
second honesty the `z`-integration by parts of the `I₁` step consumes). -/
theorem EllHypT.hkMem_Dz {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.EllHypT α k F Ψ) :
    Work.Spaces.HkMem α 0 (Work.Spaces.Dz Ψ) :=
  HkMem_zero_of_DzIter_slot (α := α) (k := k) (i := 1) (by omega)
    (smoothOpen_of_smoothQuad h.quadPsi) h.memPsi

/-- **The honesty package of the trace-free class.**  For `k ≥ 2` the data of `EllHypT` carry
both mixed-derivative honesties that the repaired `I₁` step of `prop:H2` needs:
`HkMem α 0 (z ∂_z Ψ)` and `HkMem α 0 (z ∂_z ∂_θ Ψ) = HkMem α 0 (∂_θ (z ∂_z Ψ))`.  A level-`0`
estimate stated on the class `AeData`/`EllWeakPos` **together with these two hypotheses** is the
corrected interface (see the module docstring). -/
theorem EllHypT.honesty {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.EllHypT α k F Ψ) :
    Work.Spaces.HkMem α 0 (Work.Spaces.Dz Ψ) ∧
      Work.Spaces.HkMem α 0 (Work.Spaces.Dz (Work.Spaces.pth Ψ)) :=
  ⟨EllHypT.hkMem_Dz hk h, EllHypT.hkMem_Dz_pth hk h⟩

end Work.FTS.EllipticEst.Cores
