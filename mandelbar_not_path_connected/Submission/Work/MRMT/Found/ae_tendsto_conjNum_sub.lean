import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.conjAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Found

-- `hcomp` (the a.e. convergence of `μn n (f z)`) was added after review; without it the
-- conclusion is not derivable.
--
-- Proof idea.  Write `a := dz f z`, `b := dzbar f z`.  Then
--   `conjNum μF f z - μF z · conjDen μF f z
--      = (star a + star (μF (f z)) · b) - μF z · (star b + star (μF (f z)) · a)`,
-- a polynomial expression in the two parameters `w := μF z` and `X := star (μF (f z))`.
-- For a.e. `z` we have `μn n z → μ z` and `μn n (f z) → μ (f z)` (whence
-- `star (μn n (f z)) → star (μ (f z))`), so the expression converges to
-- `(star a + star (μ (f z)) · b) - μ z · (star b + star (μ (f z)) · a)`.
-- Finally `μ z = pullRev μ f z = num / den` with `num = star a + star (μ (f z)) · b` and
-- `den = star b + star (μ (f z)) · a = conjDen μ f z ≠ 0` (nonvanishing in the
-- orientation-reversing case), which makes the limit equal to `num - (num / den) · den = 0`.
theorem ae_tendsto_conjNum_sub {μ : ℂ → ℂ} {f : ℂ → ℂ}
    {S : Set ℂ} (hrev : ∀ z ∉ S, ‖Work.MRMT.dz f z‖ < ‖Work.MRMT.dzbar f z‖)
    {K : Set ℂ} (hK : IsCompact K) (hKS : Disjoint K S)
    {μn : ℕ → ℂ → ℂ} {k : ℝ} (hk : k < 1) (hμn_le : ∀ n z, ‖μn n z‖ ≤ k)
    (hμn : Filter.Eventually (fun w => Filter.Tendsto (fun n => μn n w) Filter.atTop (nhds (μ w)))
      (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℂ)))
    (hcomp : Filter.Eventually (fun z => z ∈ K → Filter.Tendsto (fun n => μn n (f z)) Filter.atTop
        (nhds (μ (f z)))) (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℂ)))
    (hbound : Filter.Eventually (fun z => z ∈ K → ‖μ (f z)‖ ≤ k)
      (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℂ)))
    (hinv : Filter.Eventually (fun z => μ z = Work.MRMT.Found.pullRev μ f z)
      (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℂ))) :
    Filter.Eventually (fun z => z ∈ K → Filter.Tendsto
      (fun n => Work.MRMT.Found.conjNum (μn n) f z - μn n z * Work.MRMT.Found.conjDen (μn n) f z)
      Filter.atTop (nhds 0)) (MeasureTheory.ae (MeasureTheory.volume : MeasureTheory.Measure ℂ)) := by
  filter_upwards [hμn, hcomp, hbound, hinv] with z hμz hcz hbz hiz
  intro hzK
  -- `z` lies outside `S`, so `f` is orientation reversing at `z`.
  have hzS : z ∉ S := Set.disjoint_left.mp hKS hzK
  have hrevz : ‖Work.MRMT.dz f z‖ < ‖Work.MRMT.dzbar f z‖ := hrev z hzS
  -- the denominator does not vanish
  have hden : star (Work.MRMT.dzbar f z) + star (μ (f z)) * Work.MRMT.dz f z ≠ 0 := by
    simpa only [conjDen] using conjDen_ne_zero (μF := μ) (hbz hzK) hk hrevz
  -- unfold `hinv` into the explicit quotient
  rw [pullRev] at hiz
  -- the two convergent parameter sequences
  have h2 : Filter.Tendsto (fun n => star (μn n (f z))) Filter.atTop (nhds (star (μ (f z)))) :=
    (hcz hzK).star
  have ha : Filter.Tendsto
      (fun n => star (Work.MRMT.dz f z) + star (μn n (f z)) * Work.MRMT.dzbar f z)
      Filter.atTop (nhds (star (Work.MRMT.dz f z) + star (μ (f z)) * Work.MRMT.dzbar f z)) :=
    tendsto_const_nhds.add (h2.mul tendsto_const_nhds)
  have hb : Filter.Tendsto
      (fun n => μn n z * (star (Work.MRMT.dzbar f z) + star (μn n (f z)) * Work.MRMT.dz f z))
      Filter.atTop (nhds (μ z * (star (Work.MRMT.dzbar f z) + star (μ (f z)) * Work.MRMT.dz f z))) :=
    hμz.mul (tendsto_const_nhds.add (h2.mul tendsto_const_nhds))
  have h4 := ha.sub hb
  -- the limit is zero because `μ z = num / den` and `den ≠ 0`
  have hzero : star (Work.MRMT.dz f z) + star (μ (f z)) * Work.MRMT.dzbar f z
      - μ z * (star (Work.MRMT.dzbar f z) + star (μ (f z)) * Work.MRMT.dz f z) = 0 := by
    have hmul : μ z * (star (Work.MRMT.dzbar f z) + star (μ (f z)) * Work.MRMT.dz f z)
        = star (Work.MRMT.dz f z) + star (μ (f z)) * Work.MRMT.dzbar f z := by
      rw [hiz, div_mul_cancel₀ _ hden]
    rw [hmul, sub_self]
  rw [hzero] at h4
  simpa only [conjNum, conjDen] using h4

end Work.MRMT.Found
