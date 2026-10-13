/-
# `Work.FTS.Apriori` — node N5: the global a-priori bound for the dynamic modulated equation

This directory is the **a-priori chapter** of the route (`FTS/N45_DESIGN_LEAD.md`, §4 and the
interface correction of `FTS/Vocab.lean`): the subproject that turns

* **N2**'s coercive inner product `Work.FTS.Nonlin.UnifIP` and
* **N4**'s §8 pairing estimate `Work.FTS.Nonlin.pairing_bound` (input here as the structure
  `PairData`),

together with the *exact* Galerkin energy identity of `Submission/Work/FTS/Galerkin/Projection.lean`,
into the **uniform `ℋ⁴` a-priori bound** consumed by the existence theorem for the dynamic
modulated equation (node N6):

* `galerkin_bound` — the Galerkin bound, in the exact shape of design §4 L-N5.7: constants
  `α₅, C₀` **independent of `τ`, `n`, `T` and `α`**, for data with `|g₀|_{ℋ⁴} ≤ α²` whose profiles
  lie in the frozen class `Work.FTS.Nonlin.GalClass`;
* `hInit`, `hProfileBdd`, `hLimBound` — the three remaining a-priori fields of N6, in the exact
  shapes of design §1.3 / §4 L-N5.6, L-N5.10;
* `HkNorm_le_of_tendstoLocUnif` — the lower semicontinuity of `|·|_{ℋ⁴}` under locally uniform
  convergence (no weak compactness is needed), through which `hLimBound` is discharged;
* `L12_zero_rhs` — the `L₁₂` zero-mode identity `L₁₂(RHS)(0) = (1-μ)·L₁₂(g)(0)` that N6 needs for
  its `hDetermines` on `V₀ = {f : L₁₂(f)(0) = 0}`;
* `psiCan_galerkin`, `galFun_galClass`, `galerkin_energy_deriv` — the supporting interface of
  design §4 L-N5.1–L-N5.3.

## Conventions

The *frozen* vocabulary comes from `Submission/Work/FTS/Vocab.lean` (namespace `Work.FTS.Nonlin`):
`Xn` (the size `|g|_{ℋ⁴}`), `RegQ` (the interior class that **replaces** the analyticity predicate
`Spaces.SmoothNbhd`), `GalClass`, `CoerAdm`, `UnifIP`, `EllPkgG`, `StarPkg`, `Pbd`, `PsiCan`,
`GalBasis`.  Nothing of it is redefined here; the aliases at the end of the chapter
(`Submission/Work/FTS/Apriori/Alias.lean`) re-export the main results under their design names in
`Work.FTS.Nonlin`.

Functions of the self-similar variables are curried, `f : ℝ → ℝ → ℝ`, applied as `f z θ`; the
family of a fake-time evolution is `Fam = ℝ → ℝ → ℝ → ℝ`, applied as `g z θ τ`; every integral is
over `[0,∞) × [0,π/2]` with the measure `dz dθ` (the Warning of §Notation of the paper).

## The mathematical content

Write `E(τ) = Σ_k c_k(τ)²` for the `ℓ²`-energy of the Galerkin coefficients and
`X = Xn α gₙ = |gₙ|_{ℋ⁴}`.  The energy identity of the Galerkin scheme is *exact* (no
differentiation under the integral sign):

  `E'(τ) = 2 Σ_k c_k ċ_k = 2 Σ_k c_k · (galField …) k`,

and the a-priori input is the inequality

  `E'(τ) ≤ -2·cc·X² + 2·C_N·Pbd α X`.

With `κ := cc·clo/Cup`, `clo·X² ≤ E ≤ Cup·X²` gives, at a time where `E = Y := clo C₀²α⁴`,

  `E' ≤ -2κC₀²α⁴ + 2C_N·Pbd α (C₀α²)`  `< 0`  for `α ≤ α₅`,

provided `C₀ ≥ max(2C_N/κ, 2√(Ccs/clo))` and `α₅ ≤ min(1/4, α₂, α₄, α_cl)` with
`(C₀+C₀²)√α_cl + C₀³α_cl^{3/2} < 1`.  The barrier then gives `E ≤ Y` for all `τ`, i.e.
`Σ_k c_k² ≤ (√clo·C₀·α²)²` and `|gₙ|_{ℋ⁴} ≤ C₀α²` — uniformly in `τ`, `n`, `T`, `α`.

The two constants are defined *explicitly* in this file (`C0`, `alpha5`), so that no existential
quantification hides them: `galerkin_bound` concludes the existential only by exhibiting them.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Vocab
import Submission.Work.FTS.Galerkin.Projection
import Submission.Work.FTS.Galerkin.Hilbert
import Submission.Work.Coercivity.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.CoercivityStep.Norm.HkSq_mono_le
import Submission.Work.Construction.MufunS

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Apriori

open Work.FTS.Nonlin
open Work.FTS.Galerkin (Fn Fam slice galFun galFam galField galRHS coeffOf IsSolOn IsGalFam
  ConvLocUnif ConvPoint Slab muDyn lamDyn dynLin dynRHS prof)

set_option autoImplicit false

/-! ## The constants of the a-priori bound (design §2.1–2.2)

They are all *explicit* functions of the constants of `UnifIP` and of N4's `pairing_bound`. -/

/-- The dissipation scale `κ = cc·clo/Cup` of the bootstrap (design §2.1). -/
def kappa (cc clo Cup : ℝ) : ℝ := cc * clo / Cup

/-- The radius `C₀ = max(2C_N/κ, 2√(Ccs/clo))` of the a-priori ball (design §2.2). -/
def C0 (CcN cc clo Cup Ccs : ℝ) : ℝ :=
  max (2 * CcN / kappa cc clo Cup) (2 * Real.sqrt (Ccs / clo))

/-- The smallness threshold of the closing inequality:
`α_cl = min(1, (16(C₀+C₀²+C₀³)²)⁻¹)`; for `α ≤ α_cl` one has
`(C₀+C₀²)√α + C₀³α^{3/2} < 1` (`alphaCl_key`). -/
def alphaCl (C₀ : ℝ) : ℝ := min 1 (1 / (16 * (C₀ + C₀ ^ 2 + C₀ ^ 3) ^ 2))

/-- The smallness threshold of the a-priori bound (design §2.2):
`α₅ = min{1/4, α₂, α₄, α_cl, C₀^{-4}}`.  The last term guarantees `C₀α² ≤ α^{7/4}`, the
smallness under which N4's pairing estimate applies (`C0_mul_sq_le`). -/
def alpha5 (CcN cc clo Cup Ccs α₂ α₄ : ℝ) : ℝ :=
  min (min (1 / 4) α₂) (min α₄ (min (alphaCl (C0 CcN cc clo Cup Ccs))
    ((C0 CcN cc clo Cup Ccs) ^ (-(4 : ℝ)))))

/-- The radius `R = √clo·C₀·α²` of the coefficient ball (`DynInputs.R`, design §2.3). -/
def Rstar (clo C₀ α : ℝ) : ℝ := Real.sqrt clo * C₀ * α ^ 2

/-- The level `Y = (√clo·C₀·α²)² = clo·C₀²·α⁴` of the energy barrier (design §2.3). -/
def Ybar (clo C₀ α : ℝ) : ℝ := (Rstar clo C₀ α) ^ 2

/-! ## The two hypotheses of the chapter

* `PairData` is the *output* of N4's `pairing_bound` (design §3.6): the modulation bound plus the
  pairing estimate for the assembled right-hand side, with `C_N` and the range `α₄` exhibited.
* `GalEnergyIneq` is the inequality the bootstrap consumes: it is the conjunction of the N2
  coercivity clause and the N4 pairing estimate *after* they have been assembled with the exact
  Galerkin energy identity.  The assembly is `galerkin_energy_ineq` (design §4 L-N5.4); it is the
  only place where the structural facts `RegQ α 4 (𝓛_Γ^T gₙ)`, `RegQ α 4 (gRHS …)` and the
  `IP`-orthonormality of the Galerkin span are used. -/

/-- The modulation constant `μ` of the *total* stream function `Φ = Φs + Φg`, as a function of the
profile `g` (this is `muDyn α Φ g τ` with the families evaluated).  It is
`Construction.mufunS`, the sign-corrected constant of `FTS_MUFUN_SIGN.md` §5, so that
`2α·muOf = μ̄ + L₁₂(Transport g)(0)`. -/
def muOf (α : ℝ) (g Φ : Fn) : ℝ :=
  Work.Construction.mufunS α (Work.Construction.N0 α (Work.Construction.Ftot α g) g)
    (Work.Construction.N α (Work.Construction.Ftot α g) Φ) g

/-- The pairing of N4's right-hand side `gRHS` with the profile `g`, at the modulations
`μ = muOf α g Φ`, `λ = lamfun μ`. -/
def rhsPair (IP : ℝ → Fn → Fn → ℝ) (α : ℝ) (g Φ : Fn) : ℝ :=
  IP α (Work.Construction.gRHS α (muOf α g Φ) (Work.Construction.lamfun (muOf α g Φ))
    (Work.Construction.Ftot α g) Φ g) g

/-- **The output of N4's `pairing_bound`** (design §3.6), with the two constants exhibited: a
universal `C_N > 0` and a range `α₄` such that, for `0 < α ≤ α₄` and every admissible pair
(`g ∈ GalClass`, `Φ_* ∈ StarPkg`, `Φ_g ∈ EllPkgG`) with `|g|_{ℋ⁴} ≤ α^{7/4}`, the modulation
constant and the pairing obey the paper's estimate. -/
structure PairData (IP : ℝ → Fn → Fn → ℝ) (CcN Ce Cs α₄ : ℝ) : Prop where
  /-- the universal constant of the estimate. -/
  hCcN : 0 < CcN
  /-- the range of `α` of the estimate. -/
  hα₄ : 0 < α₄
  /-- the modulation bound and the pairing bound of N4. -/
  bound : ∀ α : ℝ, 0 < α → α ≤ α₄ → ∀ g Φs Φg : Fn,
    GalClass α g → StarPkg α Cs Φs → EllPkgG α Ce g Φg → Xn α g ≤ α ^ (7 / 4 : ℝ) →
    |muOf α g (fun z θ => Φs z θ + Φg z θ)|
        ≤ CcN * (α + α ^ (-(1 : ℝ)) * Xn α g + α ^ (-(5 / 2 : ℝ)) * Xn α g ^ 2)
      ∧ |muOf α g (fun z θ => Φs z θ + Φg z θ)| ≤ 1 / 2
      ∧ |rhsPair IP α g (fun z θ => Φs z θ + Φg z θ)| ≤ CcN * Pbd α (Xn α g)

/-- **The Galerkin energy inequality** (design §4 L-N5.4): along every solution `c` of the
projected ODE on `[0,T]`, at every time at which the profile is small enough for N4's pairing
estimate to apply (`|gₙ|_{ℋ⁴} ≤ α^{7/4}`, the paper's smallness hypothesis), the fake-time
derivative `E' = 2 Σ_k c_k ċ_k` of the coefficient energy is bounded by minus the dissipation plus
the nonlinearity.  The smallness hypothesis is not a restriction: the energy bootstrap only uses
the inequality at the barrier level, where `|gₙ|_{ℋ⁴} ≤ C₀α² ≤ α^{7/4}` (`C0_mul_sq_le`). -/
def GalEnergyIneq (IP : ℝ → Fn → Fn → ℝ) (α cc CcN : ℝ) (φ : ℕ → Fn) (Psi : Fam → Fam)
    (g₀ : Fn) : Prop :=
  ∀ (n : ℕ) (T : ℝ) (c : ℝ → Fin n → ℝ),
    IsSolOn (galField α (IP α) φ n Psi) (coeffOf (IP α) g₀ φ n) T c →
    ∀ τ ∈ Set.Icc 0 T, Xn α (galFun φ (c τ)) ≤ α ^ (7 / 4 : ℝ) →
      2 * (∑ k : Fin n, c τ k * galField α (IP α) φ n Psi τ (c τ) k)
        ≤ -2 * cc * Work.Spaces.HkSq α 4 (galFun φ (c τ))
          + 2 * CcN * Pbd α (Xn α (galFun φ (c τ)))

/-- The four a-priori fields of N6's `DynInputs`, in the exact shapes of design §1.3 and §4:
`hInit`, `hCoeffBound`, `hProfileBdd` and `hLimBound`.  They are stated *conditionally on* the
Galerkin energy inequality `hE`, which is the a-priori input of the chapter (N2's coercivity
assembled with N4's pairing estimate by `galerkin_energy_ineq`); with `hE` fixed, each field has
literally the shape of the corresponding field of `Work.FTS.Galerkin.DynInputs`. -/
structure AprioriFields (IP : ℝ → Fn → Fn → ℝ) (α C₀ clo cc CcN : ℝ) (φ : ℕ → Fn)
    (Psi : Fam → Fam) (g₀ : Fn) (hE : GalEnergyIneq IP α cc CcN φ Psi g₀) : Prop where
  /-- **`hInit`** (design L-N5.6): the projected datum lies in the a-priori ball. -/
  hInit : ∀ n : ℕ, ∑ k : Fin n, (coeffOf (IP α) g₀ φ n k) ^ 2 ≤ (Rstar clo C₀ α) ^ 2
  /-- **`hCoeffBound`** (design L-N5.7): every Galerkin solution stays in the a-priori ball. -/
  hCoeffBound : ∀ (n : ℕ) (T : ℝ), 0 ≤ T → ∀ c : ℝ → Fin n → ℝ,
    IsSolOn (galField α (IP α) φ n Psi) (coeffOf (IP α) g₀ φ n) T c →
    ∀ τ ∈ Set.Icc 0 T, ∑ k : Fin n, (c τ k) ^ 2 ≤ (Rstar clo C₀ α) ^ 2
  /-- **`hProfileBdd`** (design L-N5.10): the Galerkin profiles are uniformly bounded on compact
  subsets of the slab. -/
  hProfileBdd : ∀ c, IsGalFam α (IP α) φ Psi (Rstar clo C₀ α) c →
    ∀ K : Set (ℝ × ℝ × ℝ), IsCompact K → K ⊆ Slab →
      ∃ Cb : ℝ, ∀ n : ℕ, ∀ p ∈ K, |prof φ c n p| ≤ Cb
  /-- **`hLimBound`** (design §1.3, L-N5.9): the limit of a convergent subsequence of Galerkin
  profiles obeys the same a-priori bound. -/
  hLimBound : ∀ c, IsGalFam α (IP α) φ Psi (Rstar clo C₀ α) c → ∀ (ψ : ℕ → ℕ) (g : Fam),
    StrictMono ψ → ConvLocUnif (fun n => galFam φ (ψ n) (c (ψ n))) g →
    (∀ τ : ℝ, 0 ≤ τ → LocData.SmoothQuad (slice g τ)) →
    ∀ τ : ℝ, 0 ≤ τ → Xn α (slice g τ) ≤ C₀ * α ^ 2

end Work.FTS.Apriori
