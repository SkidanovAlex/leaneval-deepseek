import Mathlib
import Submission.Work.NN.Core.CnPert
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.NN.Core.gagliardoNirenbergGeomMean
import Submission.Work.NN.Core.Lev.exists_polydisc_cutoff
import Submission.Work.NN.Core.ofReal_norm_le_liminf_eLpNorm
import Submission.Work.NN.Core.Lev.srcWShiftCacc
import Submission.Work.NN.Core.Lev.moserSourceGlue

namespace Work.NN.Core.Lev

/-
Status (session S8, see `Submission/Work/NN/Core/Lev/NOTES_moserSource_S8.md` for the full
state): the statement below is *not* proved.  Four natural reductions were delegated and each
came back **refuted with a rigorous counterexample**:

* `potCaccBounded` / `dgSourceBounded`: a *single* level of the Caccioppoli family (even with the
  potential/zero-order term, and even with the support restriction `tsupport φ ⊆ {h < W}`) does
  not give the sup bound — `W_L(z) = (1-|z|/L)^β` and `W_ε(z) = (‖z‖+ε)^{-α}` satisfy it while
  `sup/‖·‖_{L²} → ∞`.
* `dgIterationSup`: the *level-set* Caccioppoli with the (level-independent) source `Λ²∫ψ²` does
  not give the sup bound — rescaled bumps with `δ_ε = c ε^{1-n}` satisfy it and violate the
  conclusion.
* `realCaccShiftedOfInt`: the integer-level family does **not** give the real-exponent shifted
  Caccioppoli (the modulation window `|γ-k| ≲ k/√A₀` is too narrow).

So the *full* family over all integer levels has to be used in a way none of those reductions
captures (in particular the source term `k²Λ²∫φ²(‖u‖²)^{k-1}` is *proportional to the solution's
own weight*, which is what excludes the counterexamples above).

Proved companions that are available: `Lev.moserSourceAux`, `Lev.moserSourceReduction`,
`Lev.eLpNorm_max_le`, `Lev.moserSourceAssembly`, `Lev.shiftedMoserSup`, `Lev.srcWLipschitz`,
`Lev2.levelSetCaccSource`, `Lev2.PowCacc`, `Lev.dgClassLocalBounded`.
Session S9: the whole assignment is now reduced to a single clean statement, see
`Submission/Work/NN/Core/Lev/NOTES_moserSource_S9.md`.

* `Work.NN.Core.Lev.srcWShiftCacc` (delegated S9): from `HasPowCaccSource ρ A₀ Λ u` one gets, with
  `W := srcW u Λ` and at every level `k ≥ 1`,
  `∫ φ²‖D(W^k)‖² ≤ C (k²Λ²∫φ²W^{2k-2} + ∫‖Dφ‖²W^{2k})`, `C = 16 n A₀`.
* `Work.NN.Core.Lev.moserSourceCrux` (delegated S9, the CRUX): a nonnegative locally Lipschitz
  `W ≥ Λ` satisfying that family for all `k ≥ 1` with one constant `C` obeys
  `sup_{polydisc 0 σ} W ≤ C'(C,n,σ,ρ)‖W‖_{L²(polydisc 0 ρ)}`.
* the remaining bookkeeping is `Lev.eLpNorm_max_le` (PROVED).

All standard routes for the CRUX are documented to stall: the exponent ladder needs the
Caccioppoli at non-integer levels `qk` (`q = n/(n-1)`), the modulation window that repairs this
has relative width `1/(2√C)` (too narrow for `C > (n-1)²/4`), and the De Giorgi/level-set route
only gives a *sublinear* measure recursion because the level-set class inequality is false for
this family (`NOTES_deGiorgiClass.md`, `u = z`).
-/

theorem moserSource {n : ℕ} (hn : 0 < n) {σ ρ : Fin n → ℝ}
    (hσ0 : ∀ j, 0 < σ j) (hρ0 : ∀ j, 0 < ρ j) (hσρ : ∀ j, σ j < ρ j)
    {A₀ : ℝ} (hA₀ : 0 < A₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Λ : ℝ}, 0 ≤ Λ →
      ∀ u : Work.NN.Core.Cn n → ℂ,
        ContDiffOn ℝ 1 u (Work.CR.Flat.polydisc 0 ρ) →
        (∀ (k : ℕ), 1 ≤ k → ∀ (φ : Work.NN.Core.Cn n → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ Work.CR.Flat.polydisc 0 ρ → (∀ z, 0 ≤ φ z) →
          ∫ z in Work.CR.Flat.polydisc 0 ρ,
              (k : ℝ)^2 * (φ z)^2 * (‖u z‖^2)^(k-1) *
                (∑ j, (‖Work.CR.Flat.dCoord j u z‖^2
                  + ‖Work.CR.Flat.dbarCoord j u z‖^2))
            ≤ A₀ * ((∫ z in Work.CR.Flat.polydisc 0 ρ, ‖fderiv ℝ φ z‖^2 * (‖u z‖^2)^k)
                   + (k:ℝ)^2 * ∫ z in Work.CR.Flat.polydisc 0 ρ,
                       (φ z)^2 * (‖u z‖^2)^(k-1) * Λ^2)) →
        ∀ z ∈ Work.CR.Flat.polydisc 0 σ,
          ENNReal.ofReal ‖u z‖ ≤ ENNReal.ofReal C *
            (MeasureTheory.eLpNorm u 2 (MeasureTheory.volume.restrict (Work.CR.Flat.polydisc 0 ρ))
              + ENNReal.ofReal Λ) := by
  obtain ⟨Cg, hCg0, hshift⟩ := srcWShiftCacc (n := n) hn hρ0 hA₀
  obtain ⟨C, hC0, hglue⟩ := moserSourceGlue (n := n) hn hσ0 hρ0 hσρ (C₀ := Cg) hCg0
  refine ⟨C, hC0, ?_⟩
  intro Λ hΛ u hu hH z hz
  refine hglue hΛ u hu ?_ z hz
  intro k hk φ hφsm hφcs hφts hφnn
  exact hshift hΛ u hu hH k hk φ hφsm hφcs hφts hφnn

end Work.NN.Core.Lev
