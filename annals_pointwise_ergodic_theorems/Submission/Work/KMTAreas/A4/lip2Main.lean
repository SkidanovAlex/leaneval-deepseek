/-
# Assembly of the large-`N` case of Proposition `lip-2`

This module collects the pieces of the paper's §5.2 argument used by
`Work.KMTAreas.A4.lip2MainCase` (the large-`N` case of `Work.KMTAreas.A4.lip2`).

## The chain

Write `X := Ã*_N(h,g) = AhalfTranspose N P h g` and let `F` be the function produced by
`Work.KMTAreas.A4.lip2_arcCorrelation` (transposition + Cauchy--Schwarz + the refined inverse
theorem `LipL1Fine`) followed by the single-arc extraction `Work.KMTAreas.A4.lip2ArcExtract`.
Then

1. `𝓕_ℤ F` is supported in one arc `arcSet γ R` with `R ≤ 1/(2M)` and `M ≥ 2` large, and
   `δ^{K} N^d ≤ ‖⟨X, F⟩‖`;
2. the reproducing formula `Work.KMTAreas.A4.lip2Reproduce` expands the pairing
   (`Work.KMTAreas.A4.lip2WindowExpansion`)
   `⟨X, F⟩ = ∑'_s ∑'_y h y · F (y+s) · lip2Avg N P M γ g s y`,
   whose tail beyond `|s| ≤ S` is controlled by `Work.KMTAreas.A4.lip2WindowTail`
   (`lip2WindowTail`);
3. the pigeonhole over the `≈ S` surviving shifts plus Cauchy--Schwarz in `y` gives a *single*
   shift `s` with a large `ℓ²` mass `∑'_y ‖lip2Avg N P M γ g s y‖²`; the `ℓ²`-Plancherel identity
   `Work.KMTAreas.A4.lip2PlancherelIcc` rewrites this mass as
   `N^{-2} ∫₀¹ ‖kmtFhat g‖² ‖winSumIcc M γ t P s a b‖²`;
4. the layer-cake/`Ω` step (`lip2OmegaMass`) produces an `ε = δ^{O(1)}` and a lower bound for
   `∫_{ε ≤ ‖winSumIcc‖} ‖kmtFhat g‖²`;
5. the inverse Weyl estimate (`Work.KMTAreas.A4.lip2WeylIcc`) inverts `ε ≤ ‖winSumIcc …‖` into a
   rational approximation of `t·lc(P)`, and the pigeonhole over the admissible pairs
   (`Work.KMTAreas.A4.lip2WeylPigeonhole`) gives a *single* pair `(q,a')` with a large mass on the
   corresponding interval;
6. the window pinning `winFT M'' s'' ≡ 1` on that interval and the arc projection
   `Work.KMTAreas.A4.lip2Projection` produce `G` with `𝓕_ℤ G` supported in the arc of radius
   `1/M''` around `-s''` and `‖⟨g,G⟩‖` large;
7. `(s'': ℝ) ∈ majorArc ρ l k` for `l = ` the dyadic level of `q·|lc P|` and `k` chosen by
   `Work.KMTAreas.A4.lipExistsZpowTwo` (via `Work.KMTAreas.A4.lipMemMajorArcOfClose`), and the
   sup-norm/`ℓ¹` bounds come from `lip2Projection`.

The lemmas below are the pieces of steps 2--3 and the summability needed to justify the
interchanges of step 2.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.lip2Step1
import Submission.Work.KMTAreas.A4.lip2ArcExtract
import Submission.Work.KMTAreas.A4.lip2WindowExpansion
import Submission.Work.KMTAreas.A4.lip2WindowTail
import Submission.Work.KMTAreas.A4.lip2PlancherelIcc
import Submission.Work.KMTAreas.A4.lip2Projection
import Submission.Work.KMTAreas.A4.lipL1Fine

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators
open Polynomial

namespace Work.KMTAreas.A4

open Work.Analysis.InverseTheory

/-- The inner summand of the expansion `lip2WindowExpansion`. -/
noncomputable def lip2Inner (N : ℕ) (P : Polynomial ℤ) (M : ℝ) (γ : FreqCircle)
    (F g h : ℤ → ℂ) (s : ℤ) : ℂ :=
  ∑' y : ℤ, h y * F (y + s) * lip2Avg N P M γ g s y


end Work.KMTAreas.A4
