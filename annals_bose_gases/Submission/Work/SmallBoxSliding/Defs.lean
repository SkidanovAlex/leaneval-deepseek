import ChallengeDeps
import Submission.Work.DLSlidingIntegral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The sliding-localisation layer — definitions

FS `final_v2.tex` `thm:aprioriHLambda` (step 2 of the a-priori chain): the
big box `Λ = acube ℓ` is localised over the family of `u`-indexed *small*
boxes `B(u) = acube ℓ ∩ ((ℓd)•u + acube(ℓd))` (`DLInfra.dlBox`), with the
two-factor cutoffs `χ_{B(u)} = χ(x/ℓ)·χ(x/(ℓd) − u)`
(`ChiSmall.chiSmallB`, the cosine-`M` bump of `ChiSmallBand`).  The sliding
sum (FS `eq:BSsliding2` → `eq:appsliding`)

    H_Λ(μ) ≥ (b/2ℓ²)·ΣᵢQ_{Λ,i} + ∫_{G} H_{B(u)}(m(u)μ) du

holds on the *good set*

    G := {u : ‖(ℓd)•u‖_∞ ≤ ½ℓ(1+d) − μ^{-1/3}} ,

which is exactly the set of `u` for which every box `B(u)` has shortest side
`λ₁(u) ≥ μ^{-1/3}` (FS `thm:smallbox`'s standing hypothesis) — see
`Geom.shortSide_of_mem_goodSet`.  The complement `Gᶜ` is discarded; it splits
as `Gᶜ ⊆ bandSet ∪ farSet` where

  * `farSet` = `{u : some coordinate of (ℓd)•u exceeds ½ℓ(1+d)}` — there the
    small box `B(u)` misses the big box entirely, so `χ_{B(u)} ≡ 0`
    (`Geom.chiSmallB_eq_zero_of_mem_farSet`) and the discarded contribution
    is `0`;
  * `bandSet` = the coordinatewise `μ ↦ 4μ` band of `ChiSmallBand`
    (`bandSet ℓ d μ = chiSmallBadBand ℓ d μ`, definitionally), whose
    `χ`-mass is bounded by the CLOSED `chiSmallB_badband_integral_law`.

This module fixes the definitions; `Geom`, `BadBand`, `Words`, `Jensen`,
`Window`, `Sliding` build the API on top.

## Conventions

* `A := ½ℓ(1+d)` is the outer half-side in the `w := (ℓd)•u` coordinates;
* `δ := μ^{-1/3}` is the FS shortest-side scale;
* the *interior* `I₋ := {∀j, |w_j| ≤ A − 2δ}` is where `m(u) = 1`; on
  `G ∖ I₋ ⊆ bandSet` the chemical potential is doubled (`m(u) = 4`);
* `boxVol ℓ d := (ℓd)³` stands for `|B(u)|` (the nominal small-box volume;
  on `G` the true volume is `≍ boxVol`).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases

/-! ## The sliding geometry -/

/-- The **good set** `G` of the sliding localisation:
`‖(ℓd)•u‖_∞ ≤ ½ℓ(1+d) − μ^{-1/3}`.  Equivalently every `B(u)` has shortest
side `λ₁(u) ≥ μ^{-1/3}`. -/
def goodSet (ℓ d μ : ℝ) : Set ℝ³ :=
  {u : ℝ³ | ∀ j : Fin 3,
      |((ℓ * d) • u).ofLp j| ≤ (1 / 2) * ℓ * (1 + d) - μ ^ (-1 / 3 : ℝ)}

/-- The **interior** `I₋` (`m(u) = 1`): the shortest side is at least
`2μ^{-1/3}`, so the chemical-potential lemma is not needed. -/
def interiorSet (ℓ d μ : ℝ) : Set ℝ³ :=
  {u : ℝ³ | ∀ j : Fin 3,
      |((ℓ * d) • u).ofLp j| ≤ (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ)}

/-- The **far set**: some coordinate of `w = (ℓd)•u` exceeds the outer
half-side `A = ½ℓ(1+d)`.  There the small box misses the big box and
`χ_{B(u)} ≡ 0`. -/
def farSet (ℓ d μ : ℝ) : Set ℝ³ :=
  {u : ℝ³ | ∃ j : Fin 3,
      (1 / 2) * ℓ * (1 + d) < |((ℓ * d) • u).ofLp j|}

/-- The **bad band** of `ChiSmallBand` (`= chiSmallBadBand ℓ d μ`,
definitionally): some face-coordinate of `w = (ℓd)•u` reaches
`A − 2μ^{-1/3}` while all stay `≤ A`.  This is the `μ ↦ 4μ` band; its
`χ_{B(u)}`-mass is controlled by `chiSmallB_badband_integral_law`. -/
def bandSet (ℓ d μ : ℝ) : Set ℝ³ :=
  {u : ℝ³ |
    (∃ j : Fin 3,
      (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ) ≤ |((ℓ * d) • u).ofLp j|)
      ∧ (∀ j : Fin 3, |((ℓ * d) • u).ofLp j| ≤ (1 / 2) * ℓ * (1 + d))}

/-- The nominal small-box volume `|B(u)|` used in the per-box density
`n(u)/|B(u)|`. -/
def boxVol (ℓ d : ℝ) : ℝ := (ℓ * d) ^ 3

/-- The outer half-side `A := ½ℓ(1+d)` (proof-bookkeeping only). -/
def halfSide (ℓ d : ℝ) : ℝ := (1 / 2) * ℓ * (1 + d)

/-- The shortest-side scale `δ := μ^{-1/3}` (proof-bookkeeping only). -/
def deltaScale (μ : ℝ) : ℝ := μ ^ (-1 / 3 : ℝ)

/-! ## The `u`-localised small-box Hamiltonians `H_{B(u)}` -/

/-- The kinetic word **localised to `B(u)`**: the `χ_{B(u)}²`-weighted
Dirichlet energy of `Φ` over the big box,
`ΣᵢΣₖ ∫_{abox ℓ} χ_{B(u)}(xᵢ)² (∂ᵢₖΦ)²`.  This is the corpus form of the
kinetic part of `H_{B(u)}`. -/
noncomputable def kinWordB (N : ℕ) (M : ℕ) (ℓ d : ℝ) (u : ℝ³) (Φ : X N → ℝ) : ℝ :=
  ∑ i : Fin N, ∑ k : Fin 3,
    ∫ x in abox N ℓ, (chiSmallB M ℓ d u (x i)) ^ 2 *
      (fderiv ℝ Φ x (kcDir N i k)) ^ 2

/-- The potential word **localised to `B(u)`**: the corpus `qLHSword` word
machinery at the per-`u` localised kernels
`w_{B(u)} = wSmallPair M ℓ d u v` and `w_{1,B(u)} = wSmall1Pair h M ℓ d u`
(the `DLSmallKernels` objects).  This is the corpus form of the potential
part of `H_{B(u)}` at chemical potential `μ`. -/
noncomputable def qLHSwordB {N : ℕ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (M : ℕ) (ℓ d μ : ℝ)
    (u : ℝ³) (Φ : X N → ℝ) : ℝ :=
  qLHSword (N := N) ℓ μ (wSmallPair M ℓ d u v) (wSmall1Pair h M ℓ d u) Φ

/-- The **per-box energy word** `E_{B(u)}(Φ) = kinWordB + qLHSwordB`: the
corpus expectation of `H_{B(u)}(μ)` (the `eBf u` of the sliding sum). -/
noncomputable def sboxEBWord {N : ℕ} {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (M : ℕ) (ℓ d μ : ℝ)
    (u : ℝ³) (Φ : X N → ℝ) : ℝ :=
  kinWordB N M ℓ d u Φ + qLHSwordB h M ℓ d μ u Φ

/-! ## The a-priori remainder `R_Ψ` and its window data -/

/-- The `F`-remainder of FS step 2 (the `R_Ψ`-integrand weight):
`F(t) = c (t − μ)²/(1 + t μ^{-1})`. -/
def psiWeight (c μ : ℝ) (t : ℝ) : ℝ := c * (t - μ) ^ 2 / (1 + t * μ⁻¹)

/-- The a-priori remainder `R_Ψ := ∫_{I₋} F(n(u)/|B(u)|)·(∬ w_{1,B(u)}) du`
with the per-box mass `∬ w_{1,B(u)} = ∫_x∫_y wSmall1Pair h M ℓ d u x y` the
genuine corpus object.  `R_Ψ ≥ 0` is FS step 4 (`Jensen.R_Psi_nonneg`). -/
noncomputable def R_Psi {v : ℝ³ → ℝ}
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (M : ℕ) (ℓ d μ c : ℝ)
    (n : ℝ³ → ℝ) : ℝ :=
  ∫ u in interiorSet ℓ d μ,
    psiWeight c μ (n u / boxVol ℓ d) *
      (∫ x : ℝ³, ∫ y : ℝ³, wSmall1Pair h M ℓ d u x y)

/-- The localised particle number of a density `ρ`: the `B(u)`-mass
`n(u) := ∫_x ρ(x)·χ_{B(u)}(x)²`.  Its `u`-integral is the big-box number
(`Words.nBox_integral_u`), the mass identity underlying the Cauchy–Schwarz
window. -/
noncomputable def nBox (M : ℕ) (ℓ d : ℝ) (ρ : ℝ³ → ℝ) (u : ℝ³) : ℝ :=
  ∫ x : ℝ³, ρ x * (chiSmallB M ℓ d u x) ^ 2

end Work.SmallBoxSliding
