import Mathlib
import Submission.Work.MRMT.Found.ae_tendsto_conjNum_sub

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

/-- A subset of `ℂ` whose intersection with every compact set is finite is countable:
`ℂ` is covered by the countably many compact balls `closedBall 0 n`. -/
theorem countable_of_forall_isCompact_inter_finite {S : Set ℂ}
    (hSfin : ∀ K : Set ℂ, IsCompact K → (S ∩ K).Finite) : S.Countable := by
  have hcover : S = ⋃ n : ℕ, S ∩ Metric.closedBall (0:ℂ) (n:ℝ) := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_ge ‖z‖
      exact ⟨n, hz, hn⟩
    · rintro ⟨n, hz, _⟩; exact hz
  rw [hcover]
  refine Set.countable_iUnion fun n => (hSfin _ (isCompact_closedBall (0:ℂ) (n:ℝ))).countable

/-- Global a.e. form of `ae_tendsto_conjNum_sub`: the exceptional set `S` is locally finite
(hence countable and null), and outside it the algebraic identity `μ z = pullRev μ f z`
forces the defect `conjNum - μ z · conjDen` to vanish, so the approximating defects tend to
`0` almost everywhere. -/
theorem ae_tendsto_defect_global {μ f : ℂ → ℂ} {S : Set ℂ}
    (hSfin : ∀ K : Set ℂ, IsCompact K → (S ∩ K).Finite)
    (hrev : ∀ z ∉ S, ‖Work.MRMT.dz f z‖ < ‖Work.MRMT.dzbar f z‖)
    {μn : ℕ → ℂ → ℂ} {k : ℝ} (hk : k < 1) (hμn_le : ∀ n z, ‖μn n z‖ ≤ k)
    (hμn : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Filter.Tendsto (fun n => μn n w) Filter.atTop (nhds (μ w)))
    (hμnc : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ),
      Filter.Tendsto (fun n => μn n (f z)) Filter.atTop (nhds (μ (f z))))
    (hμb : ∀ᵐ w ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ w‖ ≤ k)
    (hμbc : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), ‖μ (f z)‖ ≤ k)
    (hinv : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), μ z = Work.MRMT.Found.pullRev μ f z) :
    ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), Filter.Tendsto
      (fun n => Work.MRMT.Found.conjNum (μn n) f z - μn n z * Work.MRMT.Found.conjDen (μn n) f z)
      Filter.atTop (nhds 0) := by
  -- `S` is locally finite, hence countable, hence null.
  have hSae : ∀ᵐ z ∂(MeasureTheory.volume : MeasureTheory.Measure ℂ), z ∉ S :=
    (countable_of_forall_isCompact_inter_finite hSfin).ae_notMem _
  filter_upwards [hμn, hμnc, hμbc, hinv, hSae] with z hμz hcz hbz hiz hzS
  -- outside `S`, `f` is orientation reversing at `z`, so the denominator is nonzero.
  have hrevz : ‖Work.MRMT.dz f z‖ < ‖Work.MRMT.dzbar f z‖ := hrev z hzS
  have hden : Work.MRMT.Found.conjDen μ f z ≠ 0 :=
    Work.MRMT.Found.conjDen_ne_zero (f := f) (μF := μ) hbz hk hrevz
  -- the two convergent parameter families
  have h2 : Filter.Tendsto (fun n => star (μn n (f z))) Filter.atTop (nhds (star (μ (f z)))) :=
    hcz.star
  have hnum : Filter.Tendsto (fun n => Work.MRMT.Found.conjNum (μn n) f z) Filter.atTop
      (nhds (Work.MRMT.Found.conjNum μ f z)) := by
    simp only [conjNum]
    exact tendsto_const_nhds.add (h2.mul tendsto_const_nhds)
  have hden' : Filter.Tendsto (fun n => Work.MRMT.Found.conjDen (μn n) f z) Filter.atTop
      (nhds (Work.MRMT.Found.conjDen μ f z)) := by
    simp only [conjDen]
    exact tendsto_const_nhds.add (h2.mul tendsto_const_nhds)
  have hmain := hnum.sub (hμz.mul hden')
  -- the limit is `conjNum μ f z - μ z · conjDen μ f z = 0`
  have hzero : Work.MRMT.Found.conjNum μ f z - μ z * Work.MRMT.Found.conjDen μ f z = 0 := by
    have hmul : μ z * Work.MRMT.Found.conjDen μ f z = Work.MRMT.Found.conjNum μ f z := by
      rw [hiz, pullRev]
      exact div_mul_cancel₀ _ hden
    rw [hmul, sub_self]
  rw [hzero] at hmain
  exact hmain

end Work.MRMT.Found
