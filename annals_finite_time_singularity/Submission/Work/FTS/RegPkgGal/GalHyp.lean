/-
# `Work.FTS.RegPkgGal.GalHyp` — the input bundle of the assembly

The assembly `Work.FTS.RegPkgGal.regPkg_of_galerkin` (`Assembly.lean`) derives `RegPkg' α S
(Avort m) (Bdyn m) (extG g)` from the data below.  Every field is **route-level input data**, not
a restatement of `RegPkg'`: it is either part of the lead's `RegPkgMin`, or one of the class
conditions of the paper (`StData`), or one of the hypotheses of a *proved* R-lemma (`R1b`'s joint
limits, `R2c`/`R4d`'s endpoint continuity, `R3b`'s sup/Lipschitz data, `R7d`'s transport data), or
the modulation data of design §2.  The one R-lemma conclusion that is *not* yet available —
R5's fake-time jet — is kept as a separate hypothesis of the assembly, since its own statement
(`R5c.jet_dtg`) is still under proof.

## Why the data is stated for the extension `g̃ = extG g`

`R2c`/`R4d` need the angular slices to be *continuous* at `θ = 0, π/2` (the genuine profile is
continuous there but not `C¹`), and at `z = 0` the slice of the extension is identically `0` while
an open-quadrant smoothness hypothesis says nothing (`D_θ` vanishes at `z = 0` and `deriv` is the
junk value `0` off differentiability).  Stating the class data for `g̃` makes every clause at
`z = 0` trivial and keeps `R2c`/`R4d` applicable.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.Defs
import Submission.Work.FTS.RegPkgGal.RVocab

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

/-- **THE INPUT BUNDLE OF THE ASSEMBLY.**  See the module docstring for the provenance of each
group of fields. -/
structure GalHyp (α S : ℝ) (g : Fam) (m : ℝ → ℝ) (Vz Vθ cs : ℝ → ℝ → ℝ → ℝ)
    (a b c Lz7 M Lz Lθ Lt Nz Nθ Nt : ℝ) : Prop where
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
  /-- the `St1`-class data of `g̃` (the `Γ`-vanishing of `D_θg̃` with its `z²` factor, and the
  quadratic/linear vanishing at `z = 0`); *not* implied by `ℋ⁴`-membership, see
  `NOTES_RegPkgGal.md` §2 -/
  hSt : StData α S (extG g)
  /-- `C¹` on the open quadrant for every strip time (this is `RegPkgMin.c4` read as `C¹`) -/
  hsm1 : ∀ τ ∈ Set.Icc 0 S,
    ContDiffOn ℝ 1 (Function.uncurry (fun z θ => extG g z θ τ))
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2)))
  /-- continuity of the angular slices at `θ = 0` -/
  hcont0 : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
    Filter.Tendsto (fun θ => extG g z θ τ) (nhdsWithin 0 (Set.Ioi (0:ℝ)))
      (nhds (extG g z 0 τ))
  /-- continuity of the angular slices at `θ = π/2` -/
  hcontπ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
    Filter.Tendsto (fun θ => extG g z θ τ) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
      (nhds (extG g z (Real.pi / 2) τ))
  /-- the far-field `Γ`-bound (`g̃ = -F_*` for `z ≥ L`); supplied by the compact support of the
  localised profile together with the explicit bound `F_* ≤ (2 pExp α/c)Γ` -/
  hfar : ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, Cf ≤ z →
    θ ∈ Work.Spaces.Iθ → |extG g z θ τ| ≤ Cf * Gamma α θ
  /-- sup bounds for the profile and its `z`-derivative (the data `R3c.jet_g` consumes).
  **There is deliberately no bound on `pth (·) = ∂_θg`**: together with the compact support it
  would be unsatisfiable (`g = -F_*` at `z = L` has `∂_θg ~ θ^{α-1}`; machine-checked as
  `R5c.no_data`).  The bounded angular quantity is `D_θg` — see `NOTES_RegPkgGal.md` §6. -/
  hsup : ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ →
    |extG g z θ τ| ≤ M ∧ |Work.Spaces.pz (fun z θ => extG g z θ τ) z θ| ≤ M
  /-- the `z`-modulus of `g̃` (`α`-Hölder, `R3d`) -/
  hhz : ∀ τ ∈ Set.Icc 0 S, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → ∀ θ ∈ Work.Spaces.Iθ,
    |extG g z θ τ - extG g z' θ τ| ≤ Lz * |z - z'| ^ α
  /-- the `θ`-modulus of `g̃` (`α`-Hölder, `R3d`; *not* Lipschitz: the profile is `Γ`-shaped, so
  a uniform Lipschitz modulus in `θ` is unsatisfiable — see `NOTES_RegPkgGal.md` §8) -/
  hhθ : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
    ∀ θ' ∈ Work.Spaces.Iθ, |extG g z θ τ - extG g z θ' τ| ≤ Lθ * |θ - θ'| ^ α
  /-- the `τ`-modulus of `g̃` (`α`-Hölder, `R3d`) -/
  hhτ : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
    ∀ θ ∈ Work.Spaces.Iθ, |extG g z θ τ - extG g z θ τ'| ≤ Lt * |τ - τ'| ^ α
  /-- the `z`-modulus of `∂_zg̃` (`α`-Hölder, `R3d`) -/
  hhzp : ∀ τ ∈ Set.Icc 0 S, ∀ z z' : ℝ, 0 ≤ z → 0 ≤ z' → ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.pz (fun z θ => extG g z θ τ) z θ
      - Work.Spaces.pz (fun z θ => extG g z θ τ) z' θ| ≤ Nz * |z - z'| ^ α
  /-- the `θ`-modulus of `∂_zg̃` (`α`-Hölder, `R3d`) -/
  hhθp : ∀ τ ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z → ∀ θ ∈ Work.Spaces.Iθ,
    ∀ θ' ∈ Work.Spaces.Iθ,
    |Work.Spaces.pz (fun z θ => extG g z θ τ) z θ
      - Work.Spaces.pz (fun z θ => extG g z θ τ) z θ'| ≤ Nθ * |θ - θ'| ^ α
  /-- the `τ`-modulus of `∂_zg̃` (`α`-Hölder, `R3d`) -/
  hhτp : ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S, ∀ z : ℝ, 0 ≤ z →
    ∀ θ ∈ Work.Spaces.Iθ,
    |Work.Spaces.pz (fun z θ => extG g z θ τ) z θ
      - Work.Spaces.pz (fun z θ => extG g z θ τ') z θ| ≤ Nt * |τ - τ'| ^ α
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
  /-- R7: a `τ`-uniform Lipschitz constant for the velocity, required only on `z > Lz7` (design
  item R-a: the backward characteristics stay above `Lz7`, so the Lipschitz control is needed only
  there; `R7e.support_strip_zL`) -/
  hVlipU : ∃ K : NNReal, ∀ τ ∈ Set.Icc 0 S, LipschitzOnWith K
    (fun p : ℝ × ℝ => (Vz p.1 p.2 τ, Vθ p.1 p.2 τ))
    (Set.prod (Set.Ioi Lz7) (Set.Ioo (0:ℝ) (Real.pi / 2)))
  /-- R7: continuity of the source coefficient -/
  hcscont : ContinuousOn (fun p : ℝ × ℝ × ℝ => cs p.1 p.2.1 p.2.2)
    (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Icc (0:ℝ) (Real.pi / 2)) (Set.Icc (0:ℝ) S)))
  /-- R7: the transport equation `(E)` in the characteristic form `∂_τF = -(Vz·D_zF + Vθ·∂_θF + cs·F)` -/
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
  /-- the profile vanishes for `z ≥ L` at the angles *outside* `Iθ` — the field `RegPkg'.hsupp`
  quantifies over all `θ`, and only `θ ∈ Iθ` is seen by the physical reconstruction; outside that
  range the profile is not constrained by the localised construction -/
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
  /-- R3b: the sup constant is non-negative -/
  hMn : 0 ≤ M
  /-- R3b: the `z`-modulus constant of `g̃` -/
  hLzn : 0 ≤ Lz
  /-- R3b: the `θ`-modulus constant of `g̃` -/
  hLθn : 0 ≤ Lθ
  /-- R3b: the `τ`-modulus constant of `g̃` -/
  hLtn : 0 ≤ Lt
  /-- R3b: the `z`-modulus constant of `∂_zg̃` -/
  hNzn : 0 ≤ Nz
  /-- R3b: the `θ`-modulus constant of `∂_zg̃` -/
  hNθn : 0 ≤ Nθ
  /-- R3b: the `τ`-modulus constant of `∂_zg̃` -/
  hNtn : 0 ≤ Nt
end Work.FTS.RegPkgGal
