/-
# `Work.FTS.RegPkgGal.GalMin` — the reduced input bundle of the assembly

`GalHyp.lean` (the input of `Assembly.regPkg_of_galerkin`) still *assumes* five quantities that are
in fact **derivable** from the a-priori class data: the sup bounds (`hsup`), the `z`-moduli
(`hhz`, `hhzp`) and the `τ`-moduli (`hhτ`, `hhτp`) of `g̃ = extG g`.  This file introduces the
reduced bundle **`GalMin`**, in which

* everything of `GalHyp` that is not one of those five is kept, but the four constants `M`, `Lz`,
  `Nθ`… are no longer parameters: the two angular moduli `hhθ`, `hhθp` are kept as *class data* with
  existential constants (they are not derivable — see `NOTES_RegPkgGal.md` §8);
* the **new** fields are the ones the derivation consumes:

  - `hSt2 : StData2 α S (extG g)` — the second-order `z`-class data at the origin
    (`Der/Defs.lean`): the bound on `∂_z²g` on `0 < z ≤ 2`.  It is exactly as much class data as
    `StData.quad` and is not derivable from `ℋ⁴`-membership (see its module docstring).
  - `hRQ : ∀ τ ∈ Icc 0 S, RegQ (pExp α) 4 (gSlice g τ)` — the ***frozen* interior class** of
    `Work.FTS.Vocab` (`SmoothQuad ∧ HkMem ∧ BdryTraces`) at every slice.  This is the class the
    whole project's estimates are stated in (`GalClass.reg` is `RegQ α 6 g`), and it is what the
    `ℋ⁴`→`L^∞` interior estimate `H2.mixed_supAbsO_le` consumes.
  - `hHkn : ∃ C₀ ≥ 0, ∀ τ ∈ Icc 0 S, HkNorm (pExp α) 4 (gSlice g τ) ≤ C₀` — the uniform `ℋ⁴` bound
    on the strip (a stated input of the route: `HkNorm (pExp α) 4 (slice g τ) ≤ C₀(pExp α)²`).

  The right-hand side's `z`-differentiability (needed for the `τ`-modulus of `∂_zg̃`) is a field of
  the R5 slot, `R5Slot.hRHz`.

Everything else of `GalHyp` is kept verbatim (the lead's `RegPkgMin`, the class data `StData`, the
angular endpoint continuity, the far-field bound, the R1 joint-limit data of the equation and the
R7 transport data of the modulation).

The single new class-data export is `StData2`; the two θ-moduli and the R5 slot are the other two
named exports, and the `RegQ`/`HkNorm` field is the standard interior class plus the uniform bound
that the estimates areas already produce.

Beyond the five sup/`z`/`τ`/`∂_z` quantities, four further fields of `GalHyp` are **not** assumed
here either, and are derived in `GalMinConv`:

* `hsm1` (`C¹` on the open quadrant at every strip time) — from `RegPkgMin.c4` (the `C⁴` field) by
  order monotonicity;
* `hcont0`, `hcontπ` (angular endpoint continuity) — from `BdryTraces` (which is part of `RegQ`) by
  `Der.endpoint_cont` (lead's R-c);
* `hfar` (the far-field `Γ`-bound) — from the support propagation and `Der.far_of_support`.

The R7 velocity's Lipschitz constant is asked only on `z > Lz7` (lead's R-a): the backward
characteristics from `z > Lz7·e^{aS}` stay above `Lz7`, which is what `R7e.support_strip_zL` uses.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.Der.Defs
import Submission.Work.FTS.RegPkgGal.St1Class
import Submission.Work.FTS.Vocab

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology MeasureTheory
open scoped Topology Real

namespace Work.FTS.RegPkgGal

open Work.FTS.Regularity

set_option autoImplicit false

/-- **THE REDUCED INPUT BUNDLE.**  See the module docstring: `GalHyp` minus the five derivable
fields (`hsup`, `hhz`, `hhzp`, `hhτ`, `hhτp`) and their constants, plus `StData2`, `RegQ` and the
uniform `ℋ⁴` bound. -/
structure GalMin (α S : ℝ) (g : Fam) (m : ℝ → ℝ) (Vz Vθ cs : ℝ → ℝ → ℝ → ℝ)
    (a b c Lz7 : ℝ) : Prop where
  /-- the Hölder exponent is positive -/
  hα : 0 < α
  /-- the paper's regime -/
  hα13 : α ≤ 1 / 3
  /-- the fake-time strip is nonempty -/
  hS : 0 < S
  /-- the lead's minimal Galerkin input (design `FTS_STRONG_ROUTE.md` §1/§4) -/
  hmin : RegPkgMin (pExp α) g
  /-- the modulation rate of design §2 is continuous near the strip -/
  hm : ContinuousOn m (Set.Ioo (-1 : ℝ) (S + 1))
  /-- `|m| ≤ 1/2` on the strip (design §2) -/
  hmb : ∀ τ : ℝ, τ ∈ Set.Ioo (-1 : ℝ) (S + 1) → |m τ| ≤ 1 / 2
  /-- `m` is `α`-Hölder on the strip (design §2, `muDyn_holderOn`) -/
  hmh : ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
    |m τ - m τ'| ≤ L * |τ - τ'| ^ α
  /-- **THE ONE NAMED CLASS-DATA CONJUNCT** (`St1Class.lean`): the `Γ`-vanishing of `D_θg̃` with its
  `z²` factor, the Taylor data at `z = 0`, the second-order `z`-bound at the origin, and the two
  angular moduli `hhθ`, `hhθp`.  Not derivable from `RegPkgMin` + the `ℋ⁴` bound (NOTES §2, §8,
  §11.4), so it is the export the strong-solution/persistence side must provide. -/
  hSt1 : St1Class α S g
  /-- the frozen interior class `RegQ (pExp α) 4` of every slice (the class the estimates use) -/
  hRQ : ∀ τ ∈ Set.Icc 0 S, Work.FTS.Nonlin.RegQ (pExp α) 4 (gSlice g τ)
  /-- the uniform `ℋ⁴` bound of the slices on the strip -/
  hHkn : ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ τ ∈ Set.Icc 0 S,
    Work.Spaces.HkNorm (pExp α) 4 (gSlice g τ) ≤ C₀
  /-- R1's joint `C¹` hypothesis on `{z > 0}` -/
  hbase : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => g q.1 θ q.2)
    (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1)))
  /-- R1: the joint limit `(z,τ) → (0,τ₀)` of `g` -/
  hj0 : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
    Filter.Tendsto (fun p : ℝ × ℝ => g p.1 θ p.2)
      (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  /-- R1: the joint limit of `z⁻¹g` -/
  hjz : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
    Filter.Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * g p.1 θ p.2)
      (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  /-- R1: the joint limit of `∂_zg` -/
  hjdz : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
    Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun z => g z θ p.2) p.1)
      (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  /-- R1: the joint limit of `∂_τg` -/
  hjdt : ∀ θ ∈ Work.Spaces.Iθ, ∀ τ₀ ∈ Set.Ico 0 (S + 1),
    Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun s => g p.1 θ s) p.2)
      (nhdsWithin (0, τ₀) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  /-- R1: `C¹` of `z ↦ ∂_τg(z,θ,0)` on `{z > 0}` -/
  hd1 : ∀ θ ∈ Work.Spaces.Iθ, ContDiffOn ℝ 1 (fun q : ℝ × ℝ => deriv (fun s => g q.1 θ s) 0)
    (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioi (-1)))
  /-- R1: the joint limit of `∂_z(∂_τg(·,θ,0))` -/
  hd1z : ∀ θ ∈ Work.Spaces.Iθ,
    Filter.Tendsto (fun p : ℝ × ℝ => deriv (fun z => deriv (fun s => g z θ s) 0) p.1)
      (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  /-- R1: the joint limit of `z⁻¹∂_τg(z,θ,0)` -/
  hd1z2 : ∀ θ ∈ Work.Spaces.Iθ,
    Filter.Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * deriv (fun s => g p.1 θ s) 0)
      (nhdsWithin (0, 0) (Set.prod (Set.Ioi (0:ℝ)) (Set.univ))) (nhds 0)
  /-- R1: right continuity of `τ ↦ ∂_τg` at `τ = 0` -/
  ht0 : ∀ θ ∈ Work.Spaces.Iθ, ∀ z : ℝ, 0 < z →
    Filter.Tendsto (fun τ => deriv (fun s => g z θ s) τ)
      (nhdsWithin 0 (Set.Ioi (0:ℝ))) (nhds (deriv (fun s => g z θ s) 0))
  /-- R7: joint `C¹` of the full profile `F = F_* + g̃` on the slab -/
  hFjoint : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => profFull α (extG g) p.1 p.2.1 p.2.2)
    (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Ioo (0:ℝ) (Real.pi / 2)) (Set.Icc (0:ℝ) S)))
  /-- R7: joint continuity of the transport velocity on the closed angular box -/
  hVjoint : ContinuousOn (fun p : ℝ × ℝ × ℝ => (Vz p.1 p.2.1 p.2.2, Vθ p.1 p.2.1 p.2.2))
    (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Icc (0:ℝ) (Real.pi / 2)) (Set.Icc (0:ℝ) S)))
  /-- R7: a `τ`-uniform Lipschitz constant for the velocity, required only on `z > Lz7` (the
  region visited by the backward characteristics, which stay above `Lz7` because `0 ≤ Vz ≤ a` and
  the support threshold is `Lz7·e^{aS}`; design item R-a, `R7e.support_strip_zL`) -/
  hVlipU : ∃ K : NNReal, ∀ τ ∈ Set.Icc 0 S, LipschitzOnWith K
    (fun p : ℝ × ℝ => (Vz p.1 p.2 τ, Vθ p.1 p.2 τ))
    (Set.prod (Set.Ioi Lz7) (Set.Ioo (0:ℝ) (Real.pi / 2)))
  /-- R7: continuity of the source coefficient -/
  hcscont : ContinuousOn (fun p : ℝ × ℝ × ℝ => cs p.1 p.2.1 p.2.2)
    (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Icc (0:ℝ) (Real.pi / 2)) (Set.Icc (0:ℝ) S)))
  /-- R7: the transport equation `(E)` in the characteristic form -/
  hEq : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
    HasDerivAt (fun s => profFull α (extG g) z θ s)
      (-(Vz z θ τ * Work.Spaces.Dz (fun z θ => profFull α (extG g) z θ τ) z θ
        + Vθ z θ τ * Work.Spaces.pth (fun z θ => profFull α (extG g) z θ τ) z θ
        + cs z θ τ * profFull α (extG g) z θ τ)) τ
  /-- R7: non-negativity of the `z`-speed -/
  hVz0 : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → 0 ≤ Vz z θ τ
  /-- R7: the `z`-speed bound -/
  hVza : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → Vz z θ τ ≤ a
  /-- R7: the `θ`-speed bound -/
  hVθb : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → |Vθ z θ τ| ≤ b
  /-- R7: the `θ`-speed vanishes at `θ = 0` -/
  hVθ0 : ∀ z τ : ℝ, 0 < z → 0 < τ → τ ≤ S → Vθ z 0 τ = 0
  /-- R7: the `θ`-speed vanishes at `θ = π/2` -/
  hVθπ : ∀ z τ : ℝ, 0 < z → 0 < τ → τ ≤ S → Vθ z (Real.pi / 2) τ = 0
  /-- R7: the source coefficient is bounded -/
  hcsc : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → |cs z θ τ| ≤ c
  /-- R7: the initial support of the profile (the localised datum) -/
  hInit : ∀ z θ : ℝ, Lz7 < z → 0 < θ → θ < Real.pi / 2 →
    profFull α (extG g) z θ 0 = 0
  /-- the profile vanishes for `z ≥ L` at the angles *outside* `Iθ` -/
  hsuppOut : ∃ L : ℝ, 0 < L ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, L ≤ z →
    θ ∉ Work.Spaces.Iθ → profFull α (extG g) z θ τ = 0
  /-- R7: the support threshold is non-negative -/
  hLz7 : 0 ≤ Lz7
  /-- R7: the `z`-speed bound is non-negative -/
  ha : 0 ≤ a
  /-- R7: the `θ`-speed bound is non-negative -/
  hb : 0 ≤ b
  /-- R7: the source bound is non-negative -/
  hc : 0 ≤ c

end Work.FTS.RegPkgGal
