import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.UBBInputs.Sliding
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory

namespace Work.UBBInputs.shape

/-!
# `SlidingSumData` forces `R' ≤ 0`

The residual bundle `Work.UBBInputs.SlidingSumData` is stated for states of
`abox`-norm one over *every* box `(N, L)`.  Evaluating it at the degenerate box
`N = 0` — where every word of the corpus vanishes (`kinWord 0`, `qLHSword 0`,
`cnPlus 0`, `cnPlusBox 0`, `tBdiagForm 0`, hence `tBwordB 0` and
`qLHSwordB 0`) — the bundle's integrated per-box field collapses to

    `R' - 4π·(dens 0 L)²·(a v)·L³·(1 + …) + C·B ≤ ∫_{G} eBf` ,

i.e. `R' + C·B ≤ ∫_{G} eBf` since `dens 0 L = 0`.  On the good set `G` the
per-box bound `hbox` of the bundle and the vanishing of the `𝒯_B` word and of
the localised potential word give `eBf ≤ 0` pointwise, so `∫_{G} eBf ≤ 0`; and
`C·B ≥ 0` (`C ≥ 0` is a field of the bundle, and `B ≥ ∫_{Gᶜ} χ_{B(u)}² ≥ 0`
with the `χ`-mass nonnegative, `chiMass_nonneg`).  Hence `R' ≤ 0`: the residual
constant `R'` of the bundle carries no positive slack.
-/

theorem slidingSumData_forces_Rprime_nonpos {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {b K_B R' J ε₀ : ℝ} {d M : ℕ} (hε₀ : 0 ≤ ε₀) {L : ℝ} (hL : 1 ≤ L)
    {Φ : Submission.BoseGases.CSBox 0 L}
    (hnorm : Work.UBBInputs.sqNormN 0 L (Φ : Submission.BoseGases.X 0 → ℝ) = 1)
    (hdata : Work.UBBInputs.SlidingSumData v h b K_B R' J ε₀ d M) : R' ≤ 0 := by
  have hdens : Work.UBB.dens 0 L = 0 := by simp [Work.UBB.dens]
  -- the bundle at the degenerate box `N = 0`, where the state is automatically low
  obtain ⟨ε, c, C, B, eBf, hC, _hloc, hbox, _hpot, hintt, hintq, hintf, _hintmass,
    _hlowu, hmass, hsum⟩ :=
    hdata L hL 0 (by simpa [hdens] using hε₀) Φ hnorm (by
      have h1 : Work.UBB.WordDens 0 L (Work.UBB.dens 0 L) v h
          (Φ : Submission.BoseGases.X 0 → ℝ) = 0 := by
        simp [Work.UBB.WordDens, Submission.BoseGases.sboxE, Submission.BoseGases.kinWord,
          Submission.BoseGases.qLHSword, Submission.BoseGases.pairSet]
      have h2 : Work.UBB.Theta (BoseGases.a v) J (Work.UBB.dens 0 L) = 0 := by
        simp [Work.UBB.Theta, hdens]
      rw [h1, h2])
  -- both words of the per-box bound vanish at `N = 0`
  have htB : ∀ u : EuclideanSpace ℝ (Fin 3),
      Work.SmallBoxTBWord.tBwordB 0 L d ε c u (Φ : Submission.BoseGases.X 0 → ℝ) = 0 := fun u =>
    by simp [Work.SmallBoxTBWord.tBwordB, Work.SmallBoxTBWord.tBword,
      Work.SmallBoxTBWord.cnPlusBox, Work.SmallBoxTBWord.tBwordKin, Work.SmallBoxTBWord.tBdiagForm]
  have hqB : ∀ u : EuclideanSpace ℝ (Fin 3),
      Work.SmallBoxSliding.qLHSwordB h M L d (Work.UBB.dens 0 L) u
        (Φ : Submission.BoseGases.X 0 → ℝ) = 0 := fun u =>
    by simp [Work.SmallBoxSliding.qLHSwordB, Submission.BoseGases.qLHSword, Submission.BoseGases.pairSet]
  -- the good-set integral of `eBf` is therefore nonpositive
  have hint : (∫ u in Work.SmallBoxSliding.goodSet L d (Work.UBB.dens 0 L), eBf u) ≤ 0 := by
    have hFint : IntegrableOn (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.SmallBoxTBWord.tBwordB 0 L d ε c u (Φ : Submission.BoseGases.X 0 → ℝ) +
          Work.SmallBoxSliding.qLHSwordB h M L d (Work.UBB.dens 0 L) u
            (Φ : Submission.BoseGases.X 0 → ℝ))
        (Work.SmallBoxSliding.goodSet L d (Work.UBB.dens 0 L)) volume :=
      (hintt.add hintq).integrableOn
    have hmono := setIntegral_mono_on hintf.integrableOn hFint
      (Work.SmallBoxSliding.measurableSet_goodSet L d (Work.UBB.dens 0 L))
      (fun u _ => hbox u)
    have hFz : (∫ u in Work.SmallBoxSliding.goodSet L d (Work.UBB.dens 0 L),
        (Work.SmallBoxTBWord.tBwordB 0 L d ε c u (Φ : Submission.BoseGases.X 0 → ℝ) +
          Work.SmallBoxSliding.qLHSwordB h M L d (Work.UBB.dens 0 L) u
            (Φ : Submission.BoseGases.X 0 → ℝ))) = 0 := by
      simp [htB, hqB]
    linarith [hmono, hFz]
  -- and `B ≥ 0`, so the bundle's `C·B` slack is nonnegative
  have hB : 0 ≤ B := by
    have h0 : 0 ≤ ∫ u in (Work.SmallBoxSliding.goodSet L d (Work.UBB.dens 0 L))ᶜ,
        Work.SmallBoxSliding.chiMass M L d u :=
      integral_nonneg (fun u => Work.SmallBoxSliding.chiMass_nonneg M L d u)
    linarith
  have hsum' : R' + C * B
      ≤ ∫ u in Work.SmallBoxSliding.goodSet L d (Work.UBB.dens 0 L), eBf u := by
    simpa [hdens] using hsum
  nlinarith [hsum', hint, mul_nonneg hC hB]

end Work.UBBInputs.shape
