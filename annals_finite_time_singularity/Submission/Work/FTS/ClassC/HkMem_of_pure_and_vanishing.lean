/-
Copyright: work module for the Elgindi finite-time singularity project.

# `HkMem_of_pure_and_vanishing` — the sharp reduction of `HkMem α k f` to the
  σ-weighted pure-`z` slots plus the **vanishing-weight** plain angular slots

## What this is for

`ClassC/HkMem_of_plain_slots` reduces `HkMem α k f` to the *σ-weighted* level-`0` honesties of
the plain slots `D_z^j f` (`j ≤ k`) and `D_z^j ∂_θ^r f` (`1 ≤ r`, `r + j ≤ k`).  This module
sharpens the angular family: by `mixedSlot_vanishing_weight_domination` the mixed part of the
`ℋ^k`-integrand is dominated by the **vanishing** angular weights
`sin(2θ)^{2r-γ}` (`2r - γ ≥ 2 - γ > 0`), so the angular slots are only needed with those much
smaller weights.  Only the *pure-`z`* slots keep the singular weight `σ = sin(2θ)^{-η}`.

This matters for the elliptic node `EllNode7` (`ClassC/ellClassOk_exists_of_classC.lean`): the
σ-weighted angular slots of θ-order ≥ 3 are exactly the part of the node's honesty that the
box/energy route is expected to produce only with the vanishing weights (see
`NOTES_node_honesty_frontier.md`).

## Contents

* `vig` — the vanishing-weight plain-slot integrand
  `(D_z^l ∂_θ^r f · w)² · sin(2θ)^{2r-γ}`;
* `vig_eq`, `sin_two_nonneg_of_mem_Iθ'`, `vig_nonneg`;
* `vanC`, `vanC_pos`, `vanC_spec` — the per-slot constant of the sharp domination;
* **`HkMem_of_pure_and_vanishing`** — the reduction.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.SliceDecompDefs
import Submission.Work.FTS.ClassC.HkMem_of_plain_slots
import Submission.Work.FTS.ClassC.mixedSlot_vanishing_weight_domination
import Submission.Work.FTS.LocData.HkMem_of_majorant

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.ClassC

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The vanishing-weight plain-slot integrand -/

/-- The *vanishing-weight* plain-slot integrand of the sharp reduction:
`(D_z^l ∂_θ^r f z θ · w(z))² · sin(2θ)^{2r-γ}`.  Its angular weight vanishes at the
endpoints as soon as `r ≥ 1` (because `2r - γ ≥ 2 - γ > 0`). -/
def vig (α : ℝ) (f : ℝ → ℝ → ℝ) (r j : ℕ) (z θ : ℝ) : ℝ :=
  (Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ * Work.Spaces.w z) ^ 2
    * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α)

/-- `vig` with the two squares separated (the shape produced by
`mixedSlot_vanishing_weight_domination`). -/
theorem vig_eq (α : ℝ) (f : ℝ → ℝ → ℝ) (r j : ℕ) (z θ : ℝ) :
    vig α f r j z θ
      = (Work.Spaces.DzIter j (Work.Spaces.pthIter r f) z θ) ^ 2 * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (2 * (r : ℝ) - Work.Spaces.gam α) := by
  rw [vig, mul_pow]

/-- `sin (2θ) ≥ 0` on `Iθ`. -/
theorem sin_two_nonneg_of_mem_Iθ' {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Real.sin (2 * θ) := by
  have h1 : 0 ≤ 2 * θ := by linarith [hθ.1]
  have h2 : 2 * θ ≤ Real.pi := by linarith [hθ.2]
  exact Real.sin_nonneg_of_nonneg_of_le_pi h1 h2

/-- The vanishing-weight plain-slot integrand is non-negative on `Iθ`. -/
theorem vig_nonneg (α : ℝ) (f : ℝ → ℝ → ℝ) (r j : ℕ) {z θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ vig α f r j z θ := by
  rw [vig]
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg_of_mem_Iθ' hθ) _)

/-! ## The per-slot constant of the sharp domination -/

/-- The constant of the sharp domination for the slot `(i,j)` (`1 ≤ i`). -/
def vanC (α : ℝ) (hα : 0 < α) (hγ : Work.Spaces.gam α ≤ 3 / 2) (f : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (i j : ℕ) (hi : 1 ≤ i) : ℝ :=
  Classical.choose (mixedSlot_vanishing_weight_domination hα hγ hsm i j hi)

theorem vanC_pos (α : ℝ) (hα : 0 < α) (hγ : Work.Spaces.gam α ≤ 3 / 2) (f : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (i j : ℕ) (hi : 1 ≤ i) :
    0 < vanC α hα hγ f hsm i j hi :=
  (Classical.choose_spec (mixedSlot_vanishing_weight_domination hα hγ hsm i j hi)).1

/-- The sharp domination in the `vig` notation. -/
theorem vanC_spec (α : ℝ) (hα : 0 < α) (hγ : Work.Spaces.gam α ≤ 3 / 2) (f : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen f) (i j : ℕ) (hi : 1 ≤ i) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ vanC α hα hγ f hsm i j hi * ∑ r ∈ Finset.Icc 1 i, vig α f r j z θ := by
  intro z hz θ hθ
  refine le_trans
    ((Classical.choose_spec (mixedSlot_vanishing_weight_domination hα hγ hsm i j hi)).2
      z hz θ hθ) ?_
  refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (vanC_pos α hα hγ f hsm i j hi))
  exact le_of_eq (Finset.sum_congr rfl fun r _ => (vig_eq α f r j z θ).symm)

/-! ## The reduction -/

/-- **The sharp reduction.**  If `f` is `C^∞` on the open quadrant, every *pure-`z`* slot
`D_z^i f` (`i ≤ k`) is `ℋ^0`-honest, and every plain angular slot `D_z^j ∂_θ^r f`
(`1 ≤ r`, `r + j ≤ k`) is integrable against the *vanishing* weight
`w(z)² · sin(2θ)^{2r-γ}` (both slicewise in `z` and in the outer `z`-integral), then
`f ∈ ℋ^k`.

This is the sharpened form of `HkMem_of_plain_slots`: the angular slots are required only with
the vanishing weights; the singular weight `σ = sin(2θ)^{-η}` is needed for the pure-`z` slots
alone.  (On `Iθ` one has `sin(2θ)^{2r-γ} ≤ σ` for every `r ≥ 0`, so the σ-weighted hypothesis of
`HkMem_of_plain_slots` implies the vanishing one; the converse is what the sharpness buys.) -/
theorem HkMem_of_pure_and_vanishing {α : ℝ} (hα : 0 < α) (hγ : Work.Spaces.gam α ≤ 3 / 2)
    {k : ℕ} {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    (hz : ∀ i ≤ k, Work.Spaces.HkMem α 0 (Work.Spaces.DzIter i f))
    (hv : ∀ j r : ℕ, 1 ≤ r → r + j ≤ k →
      (∀ z ∈ Work.Spaces.Iz, IntegrableOn (fun θ => vig α f r j z θ) Work.Spaces.Iθ) ∧
      IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, vig α f r j z θ) Work.Spaces.Iz) :
    Work.Spaces.HkMem α k f := by
  classical
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k f p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := hsm.continuousOn_HkIntegrand α k
  -- index bookkeeping: `r ≤ i` and `i + j ≤ k` from the `Finset` memberships
  have hidx : ∀ {j i r : ℕ}, j ∈ Finset.range (k + 1) → i ∈ Finset.Icc 1 (k - j) →
      r ∈ Finset.Icc 1 i → 1 ≤ r ∧ r + j ≤ k := by
    intro j i r hj hi hr
    have h1 := (Finset.mem_Icc.mp hr).1
    have h2 := (Finset.mem_Icc.mp hr).2
    have h3 := (Finset.mem_Icc.mp hi).2
    have h4 := Finset.mem_range.mp hj
    exact ⟨h1, by omega⟩
  set vanM : ℝ → ℝ → ℝ := fun z θ =>
      ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.Icc 1 (k - j),
        (if h : 1 ≤ i then vanC α hα hγ f hsm i j h else 0)
          * ∑ r ∈ Finset.Icc 1 i, vig α f r j z θ with hvanMdef
  set M : ℝ → ℝ → ℝ := fun z θ =>
      (∑ j ∈ Finset.range (k + 1), Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ)
      + vanM z θ with hMdef
  -- slicewise integrability of the `vanM` summands
  have hinner : ∀ z ∈ Work.Spaces.Iz, ∀ j ∈ Finset.range (k + 1),
      ∀ i ∈ Finset.Icc 1 (k - j),
      Integrable (fun θ => (if h : 1 ≤ i then vanC α hα hγ f hsm i j h else 0)
        * ∑ r ∈ Finset.Icc 1 i, vig α f r j z θ) (volume.restrict Work.Spaces.Iθ) := by
    intro z hz' j hj i hi
    refine Integrable.const_mul (integrable_finsetSum _ fun r hr => ?_) _
    exact (hv j r (hidx hj hi hr).1 (hidx hj hi hr).2).1 z hz'
  have hvanM_slice : ∀ z ∈ Work.Spaces.Iz,
      Integrable (fun θ => vanM z θ) (volume.restrict Work.Spaces.Iθ) := by
    intro z hz'
    rw [hvanMdef]
    exact integrable_finsetSum _ fun j hj => integrable_finsetSum _ fun i hi =>
      hinner z hz' j hj i hi
  refine Work.FTS.LocData.HkMem_of_majorant (M := M) α k hcont ?_ ?_ ?_
  · -- slicewise integrability of the majorant
    intro z hz'
    rw [hMdef]
    exact Integrable.add (integrable_finsetSum _ fun j hj =>
      (hz j (by have h := Finset.mem_range.mp hj; omega)).1 z hz') (hvanM_slice z hz')
  · -- the outer integral of the majorant is integrable
    set G : ℝ → ℝ := fun z =>
        (∑ j ∈ Finset.range (k + 1),
            ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ)
        + ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.Icc 1 (k - j),
            (if h : 1 ≤ i then vanC α hα hγ f hsm i j h else 0)
              * (∑ r ∈ Finset.Icc 1 i,
                  ∫ θ in Work.Spaces.Iθ, vig α f r j z θ) with hGdef
    have hGint : IntegrableOn G Work.Spaces.Iz := by
      rw [hGdef]
      refine Integrable.add ?_ ?_
      · exact integrable_finsetSum _ fun j hj =>
          (hz j (by have h := Finset.mem_range.mp hj; omega)).2
      · refine integrable_finsetSum _ fun j hj => integrable_finsetSum _ fun i hi =>
          Integrable.const_mul (integrable_finsetSum _ fun r hr =>
            (hv j r (hidx hj hi hr).1 (hidx hj hi hr).2).2) _
    have hpoint : ∀ z ∈ Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ, M z θ) = G z := by
      intro z hz'
      have hsingle : (∫ θ in Work.Spaces.Iθ, ∑ j ∈ Finset.range (k + 1),
            Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ)
          = ∑ j ∈ Finset.range (k + 1),
              ∫ θ in Work.Spaces.Iθ,
                Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ :=
        MeasureTheory.integral_finsetSum _ (fun j hj =>
          (hz j (by have h := Finset.mem_range.mp hj; omega)).1 z hz')
      have hdouble : (∫ θ in Work.Spaces.Iθ, vanM z θ)
          = ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.Icc 1 (k - j),
              (if h : 1 ≤ i then vanC α hα hγ f hsm i j h else 0)
                * (∑ r ∈ Finset.Icc 1 i,
                    ∫ θ in Work.Spaces.Iθ, vig α f r j z θ) := by
        rw [hvanMdef]
        rw [MeasureTheory.integral_finsetSum _ fun j hj =>
          integrable_finsetSum _ fun i hi => hinner z hz' j hj i hi]
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [MeasureTheory.integral_finsetSum _ fun i hi => hinner z hz' j hj i hi]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [MeasureTheory.integral_const_mul]
        congr 1
        exact MeasureTheory.integral_finsetSum _ fun r hr =>
          (hv j r (hidx hj hi hr).1 (hidx hj hi hr).2).1 z hz'
      rw [hMdef, MeasureTheory.integral_add
        (integrable_finsetSum _ fun j hj =>
          (hz j (by have h := Finset.mem_range.mp hj; omega)).1 z hz')
        (hvanM_slice z hz'), hsingle, hdouble, hGdef]
    exact hGint.congr_fun (fun z hz' => (hpoint z hz').symm) measurableSet_Ici
  · -- the pointwise domination of the integrand by the majorant
    intro z hz' θ hθ'
    have hGrp : ∀ j ∈ Finset.range (k + 1),
        Work.FTS.EllipticEst.sliceGroup α k j f z θ
          = Work.Spaces.HkIntegrand α 0 (Work.Spaces.DzIter j f) z θ
            + ∑ i ∈ Finset.Icc 1 (k - j),
                (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      intro j hj
      rw [Work.FTS.EllipticEst.sliceGroup, HkIntegrand_zero_eq_classC]
    rw [hMdef, hvanMdef, Work.FTS.EllipticEst.HkIntegrand_eq_slice_sum,
      Finset.sum_congr rfl hGrp, Finset.sum_add_distrib]
    refine add_le_add le_rfl (Finset.sum_le_sum fun j hj => ?_)
    refine Finset.sum_le_sum fun i hi => ?_
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    rw [dif_pos hi1]
    exact vanC_spec α hα hγ f hsm i j hi1 z hz' θ hθ'

end Work.FTS.ClassC
