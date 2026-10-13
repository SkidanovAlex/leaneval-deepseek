/-
Copyright: work module for the Elgindi finite-time singularity project.

# `HkMem_JepsSub`: `ℋ^k` is closed under the difference `J_ε f - f`

The log-coordinate mollifier `J_ε` of `Submission/Work/FTS/StrongEps/Basic.lean` maps `ℋ^k` into
itself (`HkMem_Jeps`, `Submission/Work/FTS/StrongEps/HkMem_Jeps.lean`).  Here we record the
companion statement needed by the `ε → 0` comparison: if `f` and `J_ε f` are both in `ℋ^k`, then so
is the *difference* `J_ε f - f`.

The point is that `HkMem` is only the integrability of a sum of *squares* of weighted derivatives,
and the derivatives are not linear unless the data are smooth.  For the difference `J_ε f - f` the
*slots* are nevertheless under control on the open quadrant, thanks to the hypothesis `hlin` of the
statement: for `z > 0`, `θ ∈ (0,π/2)` and every `j i`,

`mixed j i (J_ε f - f) = J_ε (mixed j i f) - mixed j i f`,

i.e. every slot of the difference is the *difference of the corresponding slots*.  (`hlin` is
exactly what the caller has: it is the open-quadrant form of the commutation `E1`, one slot at a
time.)  Consequently `HkIntegrand α k (J_ε f - f)` agrees on the open quadrant with the slot-wise
difference integrand `HkIntDiff α k (J_ε f) f` of
`Submission/Work/FTS/StrongEps/JepsSubDefs.lean`:

* that expression is *dominated* by `2 · HkIntegrand α k (J_ε f) + 2 · HkIntegrand α k f`
  (`HkIntDiff_le`, pure algebra), and
* it is *continuous on the open quadrant* (`JepsSubAux.continuousOn_HkIntDiff`), because every slot
  of `J_ε f` equals `J_ε` of the corresponding slot of `f` there and `J_ε` preserves continuity.

Measurability of the integrand of the difference therefore comes for free from that continuity, and
the a.e. domination is transferred to `HkMem` by `JepsSubAux.HkMem_of_majorant_ae` — the a.e. form
of `Work.FTS.LocData.HkMem_of_majorant`.  This is exactly why `HkMem_JepsSub` does *not* need the
stronger hypothesis `IsSmoothKernel ρ` (smoothness of `J_ε f` itself is never used).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps
import Submission.Work.FTS.StrongEps.JepsHkMem.AuxMeas
import Submission.Work.FTS.StrongEps.HkSqAux.continuousOn_HkIntegrand_Quad
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.JepsSubDefs
import Submission.Work.FTS.StrongEps.JepsSubAux.continuousOn_HkIntDiff
import Submission.Work.FTS.StrongEps.JepsSubAux.HkMem_of_majorant_ae

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## The slot of the difference

The one place where the hypothesis `hlin` of the statement is used: on the open quadrant each mixed
slot of `J_ε f - f` is the difference of the corresponding slots of `J_ε f` and of `f`.  The second
equality is the `C^∞`-commutation `mixed_Jeps` of `E1`; the first is the hypothesis itself. -/

theorem JepsSub_mixed_eq (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (hlin : ∀ j i : ℕ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.mixed j i (fun z' θ' => Jeps ρ ε f z' θ' - f z' θ') z θ
        = Jeps ρ ε (Work.Spaces.mixed j i f) z θ - Work.Spaces.mixed j i f z θ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (j i : ℕ) :
    Work.Spaces.mixed j i (fun z' θ' => Jeps ρ ε f z' θ' - f z' θ') z θ
      = Work.Spaces.mixed j i (Jeps ρ ε f) z θ - Work.Spaces.mixed j i f z θ := by
  rw [hlin j i z θ hz hθ, mixed_Jeps ρ hρ hε hf hz hθ j i]

/-- **`HkIntegrand α k (J_ε f - f)` is the slot-wise difference integrand on the open quadrant.** -/
theorem HkIntegrand_sub_eqOn (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ} (hε : 0 < ε)
    {f : ℝ → ℝ → ℝ} (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (hlin : ∀ j i : ℕ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.mixed j i (fun z' θ' => Jeps ρ ε f z' θ' - f z' θ') z θ
        = Jeps ρ ε (Work.Spaces.mixed j i f) z θ - Work.Spaces.mixed j i f z θ)
    (α : ℝ) (k : ℕ) :
    Set.EqOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k
        (fun z θ => Jeps ρ ε f z θ - f z θ) q.1 q.2)
      (fun q : ℝ × ℝ => HkIntDiff α k (Jeps ρ ε f) f q.1 q.2) Quad := by
  rintro ⟨z, θ⟩ ⟨hz, hθ⟩
  have hslot1 : ∀ i : ℕ, Work.Spaces.DzIter i (fun z' θ' => Jeps ρ ε f z' θ' - f z' θ') z θ
      = Work.Spaces.DzIter i (Jeps ρ ε f) z θ - Work.Spaces.DzIter i f z θ := by
    intro i
    have h := JepsSub_mixed_eq ρ hρ hε hf hlin hz hθ i 0
    simpa only [Work.Spaces.mixed_zero_right] using h
  have hslot2 : ∀ j i : ℕ,
      Work.Spaces.mixed j i (fun z' θ' => Jeps ρ ε f z' θ' - f z' θ') z θ
        = Work.Spaces.mixed j i (Jeps ρ ε f) z θ - Work.Spaces.mixed j i f z θ :=
    fun j i => JepsSub_mixed_eq ρ hρ hε hf hlin hz hθ j i
  show Work.Spaces.HkIntegrand α k (fun z θ => Jeps ρ ε f z θ - f z θ) z θ
    = HkIntDiff α k (Jeps ρ ε f) f z θ
  simp only [Work.Spaces.HkIntegrand, HkIntDiff]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [hslot1 i]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hslot2 j i]

/-- **The `ℋ^k`-integrand of `J_ε f - f` is continuous on the open quadrant.**  Immediate from the
continuity of the slot-wise difference integrand (`JepsSubAux.continuousOn_HkIntDiff`) and the
identification above. -/
theorem HkIntegrand_JepsSub_continuousOn (ρ : ℝ × ℝ → ℝ) (hρ : IsMollKernel ρ) {ε : ℝ}
    (hε : 0 < ε) {f : ℝ → ℝ → ℝ} (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (hlin : ∀ j i : ℕ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.mixed j i (fun z' θ' => Jeps ρ ε f z' θ' - f z' θ') z θ
        = Jeps ρ ε (Work.Spaces.mixed j i f) z θ - Work.Spaces.mixed j i f z θ)
    (α : ℝ) (k : ℕ) :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k
      (fun z θ => Jeps ρ ε f z θ - f z θ) q.1 q.2) Quad :=
  (JepsSubAux.continuousOn_HkIntDiff α k hρ hε hf).congr
    (HkIntegrand_sub_eqOn ρ hρ hε hf hlin α k)

/-! ## The main theorem -/

theorem HkMem_JepsSub (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ) {α : ℝ}
    {k : ℕ} {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hlin : ∀ j i : ℕ, ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (Real.pi / 2) →
      Work.Spaces.mixed j i (fun z' θ' => Work.FTS.StrongEps.Jeps ρ ε f z' θ' - f z' θ') z θ
        = Work.FTS.StrongEps.Jeps ρ ε (Work.Spaces.mixed j i f) z θ
            - Work.Spaces.mixed j i f z θ)
    (hmem : Work.Spaces.HkMem α k f)
    (hmemJ : Work.Spaces.HkMem α k (Work.FTS.StrongEps.Jeps ρ ε f)) :
    Work.Spaces.HkMem α k (fun z θ => Work.FTS.StrongEps.Jeps ρ ε f z θ - f z θ) := by
  -- the two parametrisations (`Q0` of the statement and the area's `Quad`) are the same set
  have hf' : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad := hf
  refine JepsSubAux.HkMem_of_majorant_ae
    (M := fun z θ => 2 * Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ
      + 2 * Work.Spaces.HkIntegrand α k f z θ) α k
    (HkIntegrand_JepsSub_continuousOn ρ hρ hε hf' hlin α k) ?_ ?_ ?_
  · -- the angular slices of `M` are integrable
    intro z hz
    exact ((hmemJ.1 z hz).const_mul 2).add ((hmem.1 z hz).const_mul 2)
  · -- the `z`-integral of the slices of `M` is integrable
    refine MeasureTheory.IntegrableOn.congr_fun
      ((hmemJ.2.const_mul 2).add (hmem.2.const_mul 2)) ?_ measurableSet_Ici
    intro z hz
    show 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ)
        + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      = ∫ θ in Work.Spaces.Iθ, (2 * Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ
          + 2 * Work.Spaces.HkIntegrand α k f z θ)
    rw [integral_add ((hmemJ.1 z hz).const_mul 2) ((hmem.1 z hz).const_mul 2),
      integral_const_mul, integral_const_mul]
  · -- the a.e. domination, on the open quadrant
    intro z hz
    rw [JepsHkMem.restrict_Iθ_eq]
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · -- at `z = 0` the integrand of the difference vanishes
      refine Filter.Eventually.of_forall fun θ => ?_
      rw [← hz0, Work.FTS.LocData.HkIntegrand_zero_fst]
      have h1 := Work.Spaces.HkIntegrand_nonneg α k (Jeps ρ ε f) 0 θ
      have h2 := Work.Spaces.HkIntegrand_nonneg α k f 0 θ
      linarith
    · filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
      have hq : (z, θ) ∈ Quad := ⟨hzpos, hθ⟩
      have h1 : Work.Spaces.HkIntegrand α k (fun z' θ' => Jeps ρ ε f z' θ' - f z' θ') z θ
          = HkIntDiff α k (Jeps ρ ε f) f z θ :=
        HkIntegrand_sub_eqOn ρ hρ hε hf' hlin α k hq
      rw [h1]
      exact HkIntDiff_le α k (Jeps ρ ε f) f z θ

end Work.FTS.StrongEps
