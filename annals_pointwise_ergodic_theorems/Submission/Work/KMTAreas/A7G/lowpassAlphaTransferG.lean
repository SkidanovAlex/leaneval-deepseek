import Mathlib
import Submission.Work.KMTAreas.A7G.annuliUniformSigns
import Submission.Work.KMTAreas.A7G.chainPartLowpass
import Submission.Work.KMTAreas.A7G.maximalLowpass

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7G

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.EndVar Work.KMTContract

/-! ## §1.  The `g`-side low-pass family is the family of IW projections -/

/-- The `g`-side family is the family of Ionescu--Wainger projections. -/
theorem Tle_varphitildeN_zero_eq_kmtProj (ρ : ℝ) (l d N : ℕ) :
    Work.KMTAreas.A7.Tle ρ l (Work.KMTAreas.A7.varphitildeN d N 0)
      = Work.KMTContract.kmtProj ρ l (-((d : ℤ) * Work.Analysis.EndVar.logN N)) := by
  rw [varphitildeN_zero_eq_etaCutG]
  rfl

/-- The `l₂ = 0` low-pass family is the family of plain cutoffs (the hypothesis's family). -/
theorem Tle_zero_eq_kmtProj (ρ : ℝ) (d N : ℕ) :
    Work.KMTAreas.A7.Tle ρ 0 (Work.KMTAreas.A7.varphitildeN d N 0)
      = Work.KMTContract.kmtProj ρ 0 (-((d : ℤ) * Work.Analysis.EndVar.logN N)) :=
  Tle_varphitildeN_zero_eq_kmtProj ρ 0 d N

/-! ## §2.  The transference

The conclusion is assembled from the sibling inputs of this directory:
* `annuliUniformSigns` — the uniform-in-signs single-scale bound for the lacunary annuli
  `η_{≤-(m₀+n+1)} - η_{≤-(m₀+n)}` (the provable companion of the available `incrementVar`);
* `sqFunLowpass` — the resulting square-function bound
  `‖ (Σ'_n |Δ_n f x|²)^{1/2} ‖_{ℓᵖ} ≤ C ‖f‖_{ℓᵖ}` (Khintchine);
* `chainPartLowpass` — the Lépingle/JSW real-variable step
  `chainPart r (T·f) ≤ B (supPart r (T·f) + sqFun)` with `B` *absolute*;
* `maximalLowpass` — the values-supremum (Ionescu--Wainger maximal) estimate
  `‖ supPart r (Π_{≤l,≤-(m₀+n)}·f) ‖_{ℓᵖ} ≤ C ⟨l⟩ ‖f‖_{ℓᵖ}`;
* `hypConstantLower` — the hypothesis forces `C₀ ≥ k₀ > 0`.

The reindexing `σ n = d · logN ⌊a n⌋ - d · logN ⌊a 0⌋` identifies the conclusion's family with a
subsequence of the (consecutive) family `m ↦ Π_{≤l₂,≤-(m₀+m)}` of the sibling statements, whose
variational norm dominates the subsequence's (`Work.KMTAreas.A7.variationalNorm_comp_mono_le`).

**Do NOT use `varRhoAll 2` as the intermediate**: the `r = 2` endpoint of the variational
estimate is FALSE (Krause--Mirek--Tao, "Unboundedness of quadratic variation", Cor. `r-counter`:
no variational estimate holds for `r ≤ 2`; the trusted `theorem_1_17_iv` accordingly assumes
`r > 2`).  `varRhoAll 2` is a *pointwise* supremum over chains, so bounding each chain does not
bound it.  The correct intermediate is the band-pass **square function** of the consecutive
increments, as above. -/

end

end Work.KMTAreas.A7G
