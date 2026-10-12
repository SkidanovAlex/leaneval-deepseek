import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.pairRowS2Row
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.Defs` — the shared vocabulary of the `L¹`-weight tail chapter

Source: the curric-46 design `sources/boseDCF/bose_L1tails.md` (+ `bose_L1tails_REVIEW.md`,
`bose_L1tails.lean`, namespace `C46L1`), filed here under the area namespace `Work.BoseBoxFock`.

The honest weights of `PotPairRows` / `PotCubicFreeU` are only `L¹` (`W1fun ≤ᵃᵉ 3g₀ ≤ᵃᵉ 3v`,
`v ∈ L¹`), so every `L²`-kernel step of the sessions-3–8 route (`latRowSum_tendsto_L2`,
`latFourier_tendsto_periodisation`, `K1exp_sub_K1lim_pairing_le`, and every pairing form with
`ε√(∫∫‖G‖²)`) is unusable — and the `L²`-pairing form is **false** at these weights (the `m = 0`
term `W1fun(w−y)` of `K1lim` is itself `∉ L²`, and the two reviewers of
`chiChiImages_pairing_L1` refuted the `W`-independent `L²` shape outright).

The replacement, per the lead's design (message of this session, and
`FINDING_PotPairRows_exists.md` §9.13): pair `Ŵ` against the state's **Dirichlet** content and pay
with the **Coulomb energy** of `W`, which is finite by the scattering identity
(`∫g₀w₀ = (8π)⁻¹∬g₀g₀/‖x−y‖`, `Submission.NewtonCoulomb`).

This file only fixes the vocabulary; the statements `T1 … T7` live in the sibling modules
`spectDirichlet`, `latticeDirichlet`, `coulombDual`, `latCoulomb_le`, `W1fun_coulomb_le`,
`kernelTail`, `chiChiImages_pairing_coul`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Real

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- `χ_Λ·Q_Λψ`: FS's windowed mean-free one-body function at `u = 0`, as a `ℂ`-valued map. -/
def winQ (ℓ : ℝ) (ψ : E3 → ℝ) : E3 → ℂ :=
  fun z => ((Work.BSKinetic.bsWin ℓ 0 z : ℝ) : ℂ) * ((Work.BSKinetic.bsQ ℓ 0 ψ z : ℝ) : ℂ)

/-- The lattice momentum `κ_n = (2π/ℓ)·n` on the box `boxL ℓ` (the corpus's `kmomInt`). -/
abbrev kappaL (ℓ : ℝ) (n : Fin 3 → ℤ) : E3 := kmomInt ℓ n

/-- The Coulomb-energy integrand `W(x)W(y)/‖x − y‖`. -/
def coulInt (W : E3 → ℝ) : E3 × E3 → ℝ := fun p => W p.1 * W p.2 * (‖p.1 - p.2‖ : ℝ)⁻¹

end Work.BoseBoxFock
