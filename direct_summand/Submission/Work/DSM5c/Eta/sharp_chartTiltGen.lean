import Mathlib
import Submission.Work.DSM5c.ChartFunctor
import Submission.Work.DSPB2.Main

namespace Work.DSM5c.Eta

/-- **The tilt of a compatible tower of `p`-power roots has the tower's first term as its
untilt.**  The compatible system `n ↦ tr n mod p` is an element of `PreTilt W p` whose `n`-th
coefficient is lifted by `tr n`, and that lift satisfies `tr n ^ p ^ n = tr 0` on the nose, so
the approximation condition of `Perfection.teichmuller_spec` is met with no error term. -/
theorem untilt_tiltOf {p : ℕ} [Fact p.Prime] {W : Type} [CommRing W] [Fact ¬IsUnit (p : W)]
    [IsAdicComplete (Ideal.span {(p : W)}) W] (tr : ℕ → W)
    (htr : ∀ k, tr (k + 1) ^ p = tr k) :
    PreTilt.untilt (Work.DSM5c.tiltOf tr htr) = tr 0 := by
  have hpow : ∀ n, tr n ^ p ^ n = tr 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', pow_mul, htr n, ih]
  refine Perfection.teichmuller_spec (fun n => ⟨tr n, ?_, ?_⟩)
  · rw [← Work.DSM5c.coeff_tiltOf tr htr n, PreTilt.coeff_def]
  · rw [hpow n]

/-- **The `♯`-property of the tilt of the `ϖ`-tower** (`Work.DSM5c.tiltVarpi Q`). -/
theorem untilt_tiltVarpi {p : ℕ} [Fact p.Prime] {W : Type} [CommRing W]
    [Fact ¬IsUnit (p : W)] [IsAdicComplete (Ideal.span {(p : W)}) W]
    (Q : DSMap.PerfectoidData p W) :
    PreTilt.untilt (Work.DSM5c.tiltVarpi Q) = Q.ϖ 0 :=
  untilt_tiltOf (fun k => Q.ϖ k) (fun k => Q.root k)

/-- **The `♯`-property of the tilted chart generators.**  For the M5c data the Teichmüller untilt
`PreTilt.untilt : PreTilt W p →* W` of the tilted chart generator
`Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e i` is the honest generator `t i`.

For `i = j₀` this is `Work.DSPB1.varpiTilt_untilt` (`♯(ϖ♭) = ϖ 0`) plus multiplicativity; for
`i ≠ j₀` it is the general fact that the tilt of a compatible tower has the tower's first term as
its untilt (`Perfection.teichmuller_spec`, taking the tower itself as the approximating sequence);
note `Eta/Scratch.lean` (scratch file, not part of the deliverable) already contains this step as
`Work.DSM5c.Eta.sharp_tiltOf`. -/
theorem sharp_chartTiltGen {p : ℕ} [Fact p.Prime] {W : Type} [CommRing W] [Fact ¬IsUnit (p : W)]
    [IsAdicComplete (Ideal.span {(p : W)}) W] {ι : Type} [DecidableEq ι]
    (Q : DSMap.PerfectoidData p W)
    (t : ι → W) (tr : ι → ℕ → W) (htr0 : ∀ i, tr i 0 = t i)
    (htr : ∀ i k, tr i (k + 1) ^ p = tr i k) (j₀ : ι) (e : ℕ)
    (hj₀ : t j₀ = Q.ϖ 0 ^ e) (i : ι) :
    PreTilt.untilt (Work.DSM5c.chartTiltGen Q t tr htr0 htr j₀ e i) = t i := by
  by_cases hi : i = j₀
  · rw [hi, Work.DSM5c.chartTiltGen_j₀ Q t tr htr0 htr j₀ e, map_pow, untilt_tiltVarpi Q, ← hj₀]
  · rw [Work.DSM5c.chartTiltGen_of_ne Q t tr htr0 htr j₀ e hi]
    exact (untilt_tiltOf (tr i) (htr i)).trans (htr0 i)

end Work.DSM5c.Eta
