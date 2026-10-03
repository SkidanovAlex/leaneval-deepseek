/-
# The `g`-side low-pass variational estimate (paper (lin-2), the `s₂ = -u`, `j₂ = 0` case)

This file isolates the single remaining analytic input of the `g`-side linear lacunary variational
estimate `Work.KMTAreas.A7Hi.LinVarG`: the low-frequency case `k₂ = 0` of the paper's (lin-2), in
which the unmodulated bump `φ̃_N = kmtEta(2^{d Log N} ·)` does *not* vanish at the frequency origin.
The *uniform-in-signs* route (`Work.KMTAreas.A7.varEst_of_narrow_symbols_twoEndpoints`) is
unavailable here – the signed sums `Σ_{n∈U} ω_n φ̃_{N_n}` equal `|U|` at the origin – and the paper
handles this case by Lépingle's inequality plus a standard square-function argument
([JSW, Theorem 1.1 and Lemma 3.2]).

Statement: for `Λ`-lacunary scales `N_n = ⌊a n⌋`, `1 < p < ∞`, `2 < r`, in the narrow regime
`GoodMajorArcs ρ Cρ l₂ k` with the bumps supported in `realArc k`, the `r`-variation over `n` of
the Ionescu–Wainger projections `Tle ρ l₂ (φ̃_{N_n})` is bounded on `ℓᵖ(ℤ)` by
`C (1+l₂)² ‖f‖_{ℓᵖ}`, uniformly in the family `a`, the height `l₂` and the narrowness level `k`.

The consumer is `Work.KMTAreas.A7Hi.lacunaryBumpVarEstimate_assemblyG`
(hypothesis `hLowpass`), hence `Work.KMTAreas.A7Hi.LinVarG`.

Route (for the prover) — see `NOTES_A7Hi_LinVarG_SESSION.md` for the detailed version.  The
statement is the same as the pre-existing `Work.KMTAreas.A7.varphitildeN_lowpassVar` (whose proof
is already written) from the two stubs `Work.KMTAreas.A7.plainBumpVar` (the arithmetic-free
`l₂ = 0` case, i.e. the discrete JSW/Lépingle low-pass estimate) and
`Work.KMTAreas.A7.lowpassAlphaTransfer` (the Ionescu–Wainger transference, loss `⟨l₂⟩`); so a
single proof of those two suffices.

* The transference: writing `Tle ρ l₂ φ = convOp (TleKer ρ l₂ φ)` and
  `TleKer ρ l₂ φ i = TleArChar ρ l₂ i · cw φ i` (`KMTPlan.A6.TleKer_eq_arChar_cw`, PROVED), and
  noting that `TleArChar ρ l₂` is `Q := arithQ ρ l₂`-periodic (`A7/arithChar_periodic`), the
  projection splits into the `Q` (windowed) *sublattice* averages
  `Σ_k cw φ (r+kQ) f(x - r - kQ)`, each of which is (up to translation) the plain low-pass family
  applied to the sub-sampled sequence `k ↦ f(r + Qk)` — so the `l₂ = 0` estimate applies to every
  piece.  **Careful:** the subadditivity over `r` then costs `Σ_{r<Q} ‖TleArChar ρ l₂ r‖ / Q`,
  which is **NOT** bounded by `1` (Cauchy–Schwarz only gives `≤ √#A`, and `#A ≈ 0.3 · 2^{2 l₂}`);
  numerically, for `A = ⋃_{q ≤ Q₀}(1/q)ℤ`, `Q = lcm(1..Q₀)`, the values are `1.67, 2.0, 2.6, 2.6,
  3.74, 4.28, 5.07, 6.47` for `Q₀ = 3,4,5,6,8,10,12,16` — consistent with the `⟨l₂⟩` loss of the
  transference, but the *correct* quantitative arithmetic lemma (a polynomial bound
  `Σ_{r<Q} ‖TleArChar ρ l r‖ ≤ C (1+l)^A Q`) still has to be proved.
* The plain case: `varphitildeN d N 0 = varphiN (N^d) 0`, and the family is a family of smooth
  window averages of growing lacunary length; the mechanism is the definitional split
  `variationalNorm = supPart + chainPart`, the domination of `supPart` by the discrete
  Hardy--Littlewood maximal function (available in `Work/Analysis/HardyLittlewood`), and the split
  `Λ_n = U_n + D_n` into an arithmetic Fejér/triangular (reverse-martingale) part `U` — Lépingle,
  `A7/lacDilTriVar`, `Work.Analysis.Hilbert.latticeWalk_var_le` — and a narrow band-pass deviation
  `D`, where the *uniform-in-signs* machinery does apply
  (`A7/varEst_of_narrow_symbols_twoEndpoints`).  The `f`-side analogue of this decomposition is
  already assembled (and PROVED) as `A7Hi/lowpassNarrowVar_of_fejer_dev`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7Rescue.lowpassVarG

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## Integration note (owner of area A6, H61)

The `sorry` of this module was replaced by the (proved) rescue copy
`Work.KMTAreas.A7Rescue.lowpassVarG`, as recommended by `A7/NOTES_to_H61.md` and
`A7/NOTES_onpath_audit.md`: the statement is verbatim the same, the file has no live owner, and the
rescue copy routes the estimate through the workspace's *canonical* crux
`A7HiRep.chainPartSqFunPos` instead of the mis-stated `A7HiRep.chainPartSqFun`. -/

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.EndVar

/-- **The `g`-side low-pass variational estimate.**  The `j₂ = 0`, `s₂ = -u` case of the paper's
(lin-2): the `r`-variation over a `Λ`-lacunary family of scales of the Ionescu–Wainger projections
of the *unmodulated* `g`-side bumps `φ̃_N = varphitildeN d N 0`, `d = P.natDegree`. -/
theorem lowpassVarG (P : Polynomial ℤ) (hdeg : 2 ≤ P.natDegree) :
    ∀ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (r : NNReal) (hr : 2 < r)
      (p : ENNReal) (hp : 1 < p) (hptop : p < ⊤) (Λ : NNReal) (hΛ : 1 < Λ),
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (k : ℤ) (l₂ : ℕ) (a : ℕ → NNReal) (ha : PointwiseErgodicTheorems.Lacunary Λ a)
          (ha1 : ∀ n, 1 ≤ a n) (f : ℤ → ℂ),
          Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l₂ k →
          (∀ n : ℕ, -((P.natDegree : ℤ) *
            Work.Analysis.EndVar.logN (Nat.floor (a n))) ≤ k) →
          MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => Work.KMTAreas.A7.Tle ρ l₂
              (Work.KMTAreas.A7.varphitildeN P.natDegree (Nat.floor (a n)) 0) f x))
            p MeasureTheory.Measure.count
          ≤ ENNReal.ofReal (C * (1 + (l₂ : ℝ)) ^ 2) *
              MeasureTheory.eLpNorm f p MeasureTheory.Measure.count :=
  Work.KMTAreas.A7Rescue.lowpassVarG P hdeg

end Work.KMTAreas.A7Hi
