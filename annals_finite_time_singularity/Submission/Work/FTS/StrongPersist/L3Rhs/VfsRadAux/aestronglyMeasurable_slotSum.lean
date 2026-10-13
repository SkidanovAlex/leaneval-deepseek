import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.StrongPersist.L3Rhs.N0gAuxDefs
import Submission.Work.Spaces.mixed_mul_eq

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Almost everywhere strong measurability of the radial slot sum `∑_{q ≤ 3} (D_z^q (L₁₂f·B))² w²`

The integrand of `VfsRadSlotBound` (the weighted slot bound for the radial product
`z ↦ L₁₂(f)(z)·B(z)`) is a finite sum of the four terms
`(D_z^q (fun z _ => L₁₂ f z * B z) z 0)² · (w z)²`, `q ≤ 3`.

Since the function `(z,θ) ↦ L₁₂f z · B z` is independent of `θ`, the slot operators act on
the radial profile `G z = L₁₂ f z · B z` as the one-dimensional operator `Zop u = z·u'`
(`Zop_slice`), so the `q`-th slot is `Zop^[q] G`.  Both `L₁₂ f` and `B` are `C⁴` on `(0,∞)`,
hence so is `G` (`ContDiffOn.mul`), and a `C^{b+k}` function has `C^k` `Zop`-iterates of
order `b`; in particular `Zop^[q] G` is continuous on the *open* half-line `(0,∞)` for
`q ≤ 3`.  A function continuous on `(0,∞)` is a.e. strongly measurable for the restriction
of Lebesgue measure, and `(0,∞)` and `Iz = [0,∞)` differ by the null set `{0}`
(`Measure.restrict_congr_set` and `Ioi_ae_eq_Ici`), which gives the statement for `Iz`.

Everything is proved from Mathlib alone (the workspace imports supply only the *definitions*
`L₁₂`, `Iz`, `w`, `DzIter`, `Zop`, and the identity `Zop_slice`).
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Rhs.VfsRadAux

/-- A `C^{n+1}` function on `(0,∞)` has `C^n` derivative there. -/
private theorem contDiffOn_deriv_of_succ {n : ℕ} {u : ℝ → ℝ}
    (hu : ContDiffOn ℝ (n + 1) u (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ n (deriv u) (Set.Ioi (0 : ℝ)) := by
  have hfd : ContDiffOn ℝ n (fderiv ℝ u) (Set.Ioi (0 : ℝ)) :=
    hu.fderiv_of_isOpen isOpen_Ioi (by simp)
  have hev : ContDiffOn ℝ n (fun z : ℝ => (fderiv ℝ u z) 1) (Set.Ioi (0 : ℝ)) :=
    hfd.clm_apply contDiffOn_const
  refine hev.congr (fun z _ => ?_)
  rw [fderiv_apply_one_eq_deriv]

/-- A `C^{b+k}` function on `(0,∞)` has `C^k` `Zop`-iterates of order `b`. -/
private theorem contDiffOn_Zop_iter {u : ℝ → ℝ} (b k : ℕ)
    (hu : ContDiffOn ℝ (b + k) u (Set.Ioi (0 : ℝ))) :
    ContDiffOn ℝ k (Work.Spaces.Zop^[b] u) (Set.Ioi (0 : ℝ)) := by
  induction b generalizing k with
  | zero => simpa using hu
  | succ b ih =>
      have hu' : ContDiffOn ℝ (b + (k + 1)) u (Set.Ioi (0 : ℝ)) :=
        hu.of_le (by exact_mod_cast (by omega : b + (k + 1) ≤ (b + 1) + k))
      have h1 : ContDiffOn ℝ (k + 1) (Work.Spaces.Zop^[b] u) (Set.Ioi (0 : ℝ)) :=
        ih (k + 1) hu'
      have h2 : ContDiffOn ℝ k (deriv (Work.Spaces.Zop^[b] u)) (Set.Ioi (0 : ℝ)) :=
        contDiffOn_deriv_of_succ h1
      have h3 : ContDiffOn ℝ k (fun z : ℝ => z * deriv (Work.Spaces.Zop^[b] u) z)
          (Set.Ioi (0 : ℝ)) := (contDiff_id.contDiffOn).mul h2
      rw [Function.iterate_succ_apply']
      exact h3

/-- A `C^m` function on `(0,∞)` has a `C^{m-q}` `Zop`-iterate of order `q ≤ m`, hence a
continuous one. -/
private theorem contDiffOn_Zop_iter_le {u : ℝ → ℝ} {m q : ℕ}
    (hu : ContDiffOn ℝ m u (Set.Ioi (0 : ℝ))) (hq : q ≤ m) :
    ContDiffOn ℝ (m - q) (Work.Spaces.Zop^[q] u) (Set.Ioi (0 : ℝ)) := by
  refine contDiffOn_Zop_iter q (m - q) ?_
  refine hu.of_le ?_
  exact_mod_cast (by omega : q + (m - q) ≤ m)

theorem aestronglyMeasurable_slotSum {f : ℝ → ℝ → ℝ} {B : ℝ → ℝ}
    (hL : ContDiffOn ℝ 4 (Work.Construction.L12 f) (Set.Ioi (0 : ℝ)))
    (hB : ContDiffOn ℝ 4 B (Set.Ioi (0 : ℝ))) :
    MeasureTheory.AEStronglyMeasurable (fun z => ∑ q ∈ Finset.range 4,
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
  let G : ℝ → ℝ := fun z => Work.Construction.L12 f z * B z
  have hG : ContDiffOn ℝ 4 G (Set.Ioi (0 : ℝ)) := hL.mul hB
  have hw : Measurable (Work.Spaces.w) := by
    unfold Work.Spaces.w
    fun_prop
  -- the `Zop`-iterates of the radial profile are continuous on `(0,∞)`
  have hZcont : ∀ q ≤ 3, ContinuousOn (Work.Spaces.Zop^[q] G) (Set.Ioi (0 : ℝ)) := by
    intro q _
    exact (contDiffOn_Zop_iter_le (u := G) (m := 4) hG (by omega)).continuousOn
  -- the slot sum built from the `Zop`-iterates is a.e. strongly measurable on `(0,∞)`
  have haesmZop : MeasureTheory.AEStronglyMeasurable (fun z => ∑ q ∈ Finset.range 4,
        (Work.Spaces.Zop^[q] G z) ^ 2 * (Work.Spaces.w z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h' : MeasureTheory.AEStronglyMeasurable (∑ q ∈ Finset.range 4,
        fun z : ℝ => (Work.Spaces.Zop^[q] G z) ^ 2 * (Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      Finset.aestronglyMeasurable_sum (Finset.range 4)
        (f := fun q z => (Work.Spaces.Zop^[q] G z) ^ 2 * (Work.Spaces.w z) ^ 2)
        (fun q hq => by
          have hq3 : q ≤ 3 := by have := Finset.mem_range.mp hq; omega
          exact (((hZcont q hq3).aestronglyMeasurable measurableSet_Ioi).pow 2).mul
            (hw.aestronglyMeasurable.pow 2))
    refine h'.congr (Filter.Eventually.of_forall (fun z => ?_))
    simp only [Finset.sum_apply]
  -- the slot operators of a `θ`-independent function are the `Zop`-iterates of its profile
  have hpt : ∀ q : ℕ, ∀ z : ℝ,
      Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0
        = Work.Spaces.Zop^[q] G z := by
    intro q z
    have h1 := congrFun (Work.Spaces.Zop_slice q
      (fun z _ => Work.Construction.L12 f z * B z) 0) z
    rw [h1]
  have heq : (fun z => ∑ q ∈ Finset.range 4,
        (Work.Spaces.DzIter q (fun z _ => Work.Construction.L12 f z * B z) z 0) ^ 2
          * (Work.Spaces.w z) ^ 2)
      = (fun z => ∑ q ∈ Finset.range 4,
        (Work.Spaces.Zop^[q] G z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    funext z
    exact Finset.sum_congr rfl (fun q _ => by rw [hpt q z])
  rw [heq]
  -- `(0,∞)` and `Iz = [0,∞)` differ by the null set `{0}`
  have hIoi : MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz := by
    show MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
      = MeasureTheory.volume.restrict (Set.Ici (0 : ℝ))
    exact Measure.restrict_congr_set Ioi_ae_eq_Ici
  rw [← hIoi]
  exact haesmZop

end Work.FTS.StrongPersist.L3Rhs.VfsRadAux
