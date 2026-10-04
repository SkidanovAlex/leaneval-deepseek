import Mathlib
import Submission.Diff.STEGal
import Submission.Work.Diff.STE.Lead.Gal.Prelude
import Submission.Work.Diff.STE.Lead.Gal.Prelude2
import Submission.Work.Diff.STE.Lead.GalTame.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The contracts of the final assembly of `gal_uniform_v2`

This module collects, as plain `def … : Prop`, the *exact* statements of the analytic inputs of
`Work.Diff.STE.Lead.Lead.gal_uniform_v2`, so that the assembly (and every wrapper around a missing
input) can be stated and proved **without importing** the modules that are still in flux.

Every contract below is *definitionally* the conclusion of a proved (or promised) lemma:

| contract | supplied by |
|---|---|
| `DefectData k` | `Work.Diff.STE.Lead.GalTame.pdVec_defect_sharp k` |
| `GardingSharpData D hLC k k₀` | `Work.Diff.STE.Lead.GalTame.gardingSharp D hLC k k₀ … hDefSharp` |
| `GardingData D hLC k k₀` | `Work.Diff.STE.Lead.GalTame.gardingSharp_hG_of_jet` (the `hjet`-free form) |
| `TransportData D hLC k` | `Work.Diff.STE.Lead.GalTame.GardDataL2_of_tame D hLC k hk1 hk2` |
| `LowEnergyData D hLC k k₀` | `Work.Diff.STE.Lead.GalTame.lowEnergy_of_transport` |
| `CommData D ρ k` | `Work.Diff.STE.Lead.Gal.galE_comm D ρ hρ hρ0 hρs hρ1 k hk hk1` |

The point is that `gal_uniform_v2` then has the shape

`galerkin_trapped_solution_clean … (hapr := hapr_of_aPrioriL2 hG hLow hComm hJN …)`

with `hG` produced from `GardingSharpData` by `gardingSharp_hG_of_jet`, and every remaining input
either purely bookkeeping (proved) or an explicit hypothesis of the final theorem.
-/

namespace Work.Diff.STE.Lead.GalTame

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

local notation "Idx" => Fin (Module.finrank ℝ E)

/-- Shorthand: the chart-wise smoothness of a section, in the form needed by the Layer B3
component maps (`ContDiff ℝ ⊤` of the localised components). -/
def CmptSmooth (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) : Prop :=
  ∀ (i : ι₀) (a b : Idx), ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (D.R i h a b)

/-- **The sharp `L²` defect `[∂^k, A∂∂]u`** (the conclusion of
`Work.Diff.STE.Lead.GalTame.pdVec_defect_sharp`): for a coefficient family `A` bounded by `S` with
its first derivative, with `KA` a bound for the `L²` norm of its jets up to order `k` and `Q1` a
bound for the top jet of `u`, the `k`-th commutator is bounded by `Cd · S² (1 + KA + Q1)`. -/
def DefectData (k : ℕ) : Prop :=
  ∃ Cd : ℝ, 0 ≤ Cd ∧
    ∀ (A : Idx → Idx → (Idx → ℝ) → ℝ) (u : (Idx → ℝ) → ℂ) (KA S Q1 : ℝ)
      (hA : ∀ c d, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (A c d))
      (hAper : ∀ c d, Work.Diff.STE.Periodic1 (A c d))
      (hu : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) u)
      (hup : Work.Diff.STE.Periodic1 u)
      (hKA : 0 ≤ KA) (hS : 0 ≤ S) (hQ1 : 0 ≤ Q1),
      (∀ (z : Idx → ℝ) (c d : Idx), |A c d z| ≤ S) →
      (∀ (z : Idx → ℝ) (r c d : Idx),
        |Work.Diff.STE.pdR r (fun y : Idx → ℝ => A c d y) z| ≤ S) →
      (∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Idx) (c d : Idx),
        Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β
          (fun y : Idx → ℝ => ((A c d y : ℝ) : ℂ))) ≤ KA) →
      (∀ (m : ℕ) (hm : m ≤ 2) (β : Fin m → Idx) (z : Idx → ℝ),
        ‖Work.Diff.STE.pdVec m β u z‖ ≤ S) →
      (∀ β : Fin (k + 1) → Idx, Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec (k + 1) β u) ≤ Q1) →
      ∀ l : Fin k → Idx,
        Work.Diff.STE.ENormSq 0 (fun z : Idx → ℝ =>
            Work.Diff.STE.pdVec k l
                (fun y : Idx → ℝ => ∑ c, ∑ d,
                  ((A c d y : ℝ) : ℂ) * Work.Diff.STE.pd c (Work.Diff.STE.pd d u) y) z
              - ∑ c, ∑ d, ((A c d z : ℝ) : ℂ)
                  * Work.Diff.STE.pd c (Work.Diff.STE.pd d (Work.Diff.STE.pdVec k l u)) z)
          ≤ Cd * (S ^ 2 * (1 + KA + Q1))

/-- **The *differential* form of the sharp Gårding estimate** — verbatim the conclusion of
`Work.Diff.STE.Lead.GalTame.gardingSharp`: it still asks for a pointwise bound `K` on the first jet
of the chart matrix of `h`. -/
def GardingSharpData (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (k k₀ : ℕ) : Prop :=
  ∀ (lam K B₀ : ℝ), 0 < lam → 0 < K → 0 ≤ B₀ →
    ∃ (lam' Cg : ℝ), 0 < lam' ∧ 0 ≤ Cg ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
        (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
        (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
        (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
        (hjet : ∀ (i : ι₀) (c d r : Idx) (z : Idx → ℝ), ‖z‖ ≤ 2 * D.σ i →
          |Work.Diff.STE.pdR r (D.mat i h c d) z| ≤ K),
        D.ENormB k₀ h + D.ENormB 0 h ≤ B₀ →
        D.ENormB_pair k
            (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) h
          ≤ -(lam' / 2) * D.ENormB (k + 1) h + Cg * (1 + D.ENormB k h)

/-- **The sharp Gårding datum `hG` of the a priori estimate `galE_apriori_L2`**: as
`GardingSharpData`, but with the pointwise first-jet hypothesis `hjet` *discharged* by the
level-`k₀` energy bound. -/
def GardingData (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (k k₀ : ℕ) : Prop :=
  ∀ (lam K B₀ : ℝ), 0 < lam → 0 < K → 0 ≤ B₀ →
    ∃ (lam' Cg : ℝ), 0 < lam' ∧ 0 ≤ Cg ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
        (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
        (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
        (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v),
        D.ENormB k₀ h + D.ENormB 0 h ≤ B₀ →
        D.ENormB_pair k
            (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) h
          ≤ -(lam' / 2) * D.ENormB (k + 1) h + Cg * (1 + D.ENormB k h)

/-- **The tame transport data.**  Verbatim the conclusion of
`Work.Diff.STE.Lead.GalTame.GardDataL2_of_tame`: constants uniform in the section, only the
first-order chart-matrix jet (`hjet`) as an extra hypothesis. -/
def TransportData (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (k : ℕ) : Prop :=
  ∀ (lam K : ℝ), 0 < lam → 0 < K →
    ∃ (lam' C : ℝ), 0 < lam' ∧ 0 ≤ C ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
        (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
        (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
        (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
        (hjet : ∀ (i : ι₀) (c d r : Idx) (z : Idx → ℝ), ‖z‖ ≤ 2 * D.σ i →
          |Work.Diff.STE.pdR r (D.mat i h c d) z| ≤ K),
        GardDataL2 (I := I) (M := M) D hLC k lam' C h hsym hpos hsmooth

/-- **The low-order energy datum `hLow` of `galE_apriori_L2`**, with the pointwise first-jet
hypothesis discharged by the level-`k₀` energy bound (exactly as in `GardingData`). -/
def LowEnergyData (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (k k₀ : ℕ) : Prop :=
  ∀ (lam K B₀ : ℝ), 0 < lam → 0 < K → 0 ≤ B₀ →
    ∃ Cl : ℝ, 0 ≤ Cl ∧
      ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
        (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
        (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
        (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v),
        D.ENormB k₀ h + D.ENormB 0 h ≤ B₀ →
        D.ENormB (k - 1)
            (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth)
          + D.ENormB 0
            (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth)
          ≤ Cl * (1 + D.ENormB (k + 1) h)

/-- **The order-`k` Friedrichs adjointness of `J ρ ε`** — verbatim the conclusion of
`Work.Diff.STE.Lead.Gal.galE_comm` (and of `B3/ENormB_pair_J_commutator_v2`). -/
def CommData (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Idx → ℝ) → ℝ) (k : ℕ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (f u : Work.Diff.STE.Bil (I := I) (M := M)),
        CmptSmooth (I := I) (M := M) D f →
        CmptSmooth (I := I) (M := M) D u →
        |D.ENormB_pair k (D.J ρ ε f) u - D.ENormB_pair k f (D.J ρ ε u)|
          ≤ C * Real.sqrt (D.ENormB (k - 1) f + D.ENormB 0 f)
            * Real.sqrt (D.ENormB k u)

/-- **The `ε`-uniform bound for the Friedrichs mollifier in the composite norm**, in the exact
shape of the hypothesis `hJN` of the target: constants uniform in the section and in
`ε ∈ (0, 1]`. -/
def JNBound (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Idx → ℝ) → ℝ) : Prop :=
  ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
    ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
      Work.Diff.STE.D.ChartData (I := I) (M := M) h →
      D.BNorm k (D.J ρ ε h) ≤ C * D.BNorm k h

end

end Work.Diff.STE.Lead.GalTame
