import Mathlib
import Submission.Work.Drive.T6GenAtD
import Submission.Work.Drive.regBaseAssembly
import Submission.Work.Drive.bijective_fderiv_sqDisk_foldBox
import Submission.Work.Drive.diskPlane_mfderiv
import Submission.Work.Drive.collapseTransport
import Submission.Work.Drive.hdensePolarDefs
import Submission.Work.Drive.collapseFaceAvoid

/-!
# The `s = 1` pair datum of the radial collapse, from the transport's bundles

The transport `T6` of the design (`Work.Drive.odd_topBdryMeet_zero_iff_of_T6GenAtDBox_meet3Hyp`,
`Drive/blockT6Wrapper.lean`) consumes the `s = 1` half `hpair` of the collar regularity
(`Work.Drive.hregBase_design_chains`).  This file proves that half:

> `Work.Drive.pairOneData_of_T6GenAt` — for the collapse family `colPlane β Q` and the constant plane
> family `diskPlane Q` against the two clamped sweeps of `P₁, P₂`, every `s = 1` meet
> `x ∈ ppMeet (colPlane β Q) (diskPlane Q) V W` (with the plane parameter strictly interior) satisfies
> `PairOneData`, from the at-`t` bundles `T6GenAt Q P₁ P₂ c₁ c₂` (the two `GoodLoopChain`s and the cut
> avoidance of a neighbourhood of the origin), the collar identity `β = √·` on `[δ²,∞)`, the seam
> clause of the chart, and the smoothness of the chart.

## The geometry of the proof

At `ftS x = 1` the collapse is the radial projection in the collar and the *outer part* of the
collapsed plane `colPlane β Q 1` is the core loop of `Q`, while the *radial fibres* of the collapse are
the diameters of `Q`:

* `colPlane β Q 1 u = Q (ρ (Φ u))` with `ρ = colMap β 1`, `Φ = sqDisk ∘ foldBox`; in the collar
  `ρ z = z / ‖z‖ = exp (i π t)` for a `t ∈ [0,1]` (up to sign, which `Q` cannot see on the circle), so
  the `(t, ftY x)` is a **core meet** of `Q` with the sweep of `P₁`, and the derivative of
  `colPlane β Q 1` at `u = ftU x` is a real multiple of the derivative of `coreLoop Q` at `t`;
* `Φ u = ‖Φ u‖ • (ρ (Φ u))`, so if the derivative of `u ↦ ρ (Φ u)` kills a vector `a`, then
  `dΦ(u) a` is a real multiple of `Φ u`; the point `(σ₀, ftZ x)` with `σ₀ = (1 ∓ ‖Φ u‖)/2` is then a
  **diameter meet** of `diamLoop Q t` with the sweep of `P₂`, and `dQ (Φ u) (dΦ u a)` is a real
  multiple of the derivative of the diameter loop there;
* the two `GoodLoopChain`s are exactly the transversality of the two loops against the two sweeps, so

  - a direction in the kernel of `d(colPlane β Q 1)` at `u` lies in the kernel of the *diameter*
    loop's direction pairing, killing the radial component,
  - the tangential component is killed by the core chain,
  - and the two sweeps' derivatives are injective (they have rank `3` in a `4`-dimensional space).

Everything is stated for the concrete chains of the design, so that the consumer
(`Drive/blockT6Wrapper.lean`) can apply it directly.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

set_option backward.isDefEq.respectTransparency false

noncomputable section

set_option linter.unusedVariables false

/-! ## 1. The rank output of `GoodLoopChain` at a meet

At a meet of a `1`-periodic loop `L` with a `3`-parameter sweep `D` in the `4`-dimensional capping
space, the transversality `range dL ⊔ range dD = ⊤` forces the dimension count to be *sharp*: the
loop's derivative spans a line, the sweep's derivative has rank `3` (hence is injective), and the two
ranges meet only in `0`. -/

/-- **The sharp dimension count of a loop/sweep meet.**  For a linear map `A` out of `ℝ` and a linear
map `B` out of `ℝ³` whose ranges span a `4`-dimensional space: the two ranges are independent, `A` is
non-zero and `B` is injective. -/
theorem range_inf_range_eq_bot_of_sup_eq_top
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (hV : Module.finrank ℝ V = 4)
    {A : ℝ →L[ℝ] V} {B : EuclideanSpace ℝ (Fin 3) →L[ℝ] V}
    (h : LinearMap.range A.toLinearMap ⊔ LinearMap.range B.toLinearMap = ⊤) :
    LinearMap.range A.toLinearMap ⊓ LinearMap.range B.toLinearMap = ⊥ ∧
      A 1 ≠ 0 ∧ Function.Injective B := by
  have hA : Module.finrank ℝ ↥(LinearMap.range A.toLinearMap) ≤ 1 := by
    have h1 := LinearMap.finrank_range_le A.toLinearMap
    simpa using h1
  have hB : Module.finrank ℝ ↥(LinearMap.range B.toLinearMap) ≤ 3 := by
    have h1 := LinearMap.finrank_range_le B.toLinearMap
    rw [finrank_euclideanSpace] at h1
    simpa using h1
  have hform := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range A.toLinearMap) (LinearMap.range B.toLinearMap)
  rw [h, finrank_top, hV] at hform
  have hbot : Module.finrank ℝ ↥(LinearMap.range A.toLinearMap ⊓ LinearMap.range B.toLinearMap) = 0 := by
    omega
  have hAeq : Module.finrank ℝ ↥(LinearMap.range A.toLinearMap) = 1 := by omega
  have hBeq : Module.finrank ℝ ↥(LinearMap.range B.toLinearMap) = 3 := by omega
  refine ⟨(Submodule.finrank_eq_zero.mp hbot), ?_, ?_⟩
  · intro h0
    have hle : LinearMap.range A.toLinearMap ≤ ⊥ := by
      rintro v ⟨w, rfl⟩
      have : A w = 0 := by
        have : w = w • (1 : ℝ) := by simp
        rw [this, map_smul, h0, smul_zero]
      simpa using this
    have := Submodule.finrank_mono hle
    rw [finrank_bot, hAeq] at this
    omega
  · have hk := LinearMap.finrank_range_add_finrank_ker B.toLinearMap
    rw [hBeq, finrank_euclideanSpace] at hk
    norm_num at hk
    exact LinearMap.ker_eq_bot.mp hk

/-! ## 2. The rank output at a `GoodLoopChain` meet

`Work.Drive.GoodLoopChain L D` (`T6GenAtDefs.lean`) is the general-position statement of a loop `L`
against a `3`-parameter chain `D` in the capping space.  Its transversality clause, fed into
`range_inf_range_eq_bot_of_sup_eq_top`, gives the four facts the polar dictionary of the collapse
(`Work.Drive.PolarDict`, `hdensePolarDefs.lean`) and the pair datum need:

* the loop's tangent line is **complementary** to the chain's tangent space,
* the loop is **immersive** at the parameter of the meet (`Work.Drive.CoreImmersiveAt` — the
  non-degeneracy input of `Work.Drive.PolarDict`),
* the chain is an **immersion** at the meet (clauses (ii)/(iii) of `Work.Drive.PairOneData`). -/

/-- **The rank data of a loop/chain meet.** -/
theorem loopChain_rank_data
    {L : ℝ → CappingSpace} {D : EuclideanSpace ℝ (Fin 3) → CappingSpace}
    (hGL : GoodLoopChain L D) {p : ℝ × EuclideanSpace ℝ (Fin 3)} (hp : p ∈ meetBox L D) :
    LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) L p.1).toLinearMap ⊓
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) D p.2).toLinearMap = ⊥ ∧
      mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) L p.1 ≠ 0 ∧
      Function.Injective (mfderiv (𝓡 3) (𝓡 4) D p.2) := by
  have h := range_inf_range_eq_bot_of_sup_eq_top
    (V := EuclideanSpace ℝ (Fin 4)) (by simp) (hGL.2.2 p hp)
  refine ⟨h.1, ?_, h.2.2⟩
  intro hzero
  exact h.2.1 (by rw [hzero]; rfl)

/-- **The core loop is immersive at a core meet** — the non-degeneracy hypothesis `hcore` of
`Work.Drive.PolarDict` (`hdensePolarDefs.lean`), obtained from the transversality of the meet. -/
theorem coreImmersiveAt_of_goodLoopChain
    {Q : ℂ → CappingSpace} {c : ℝ} {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (hGL : GoodLoopChain (coreLoop Q) (clampedSweep c (fun r => 1 - r) P))
    {q : ℝ × EuclideanSpace ℝ (Fin 3)} (hq : q ∈ coreMeet Q c P) :
    CoreImmersiveAt Q q.1 :=
  (loopChain_rank_data hGL hq).2.1

/-- **The sweeps of a `GoodLoopChain` meet are immersed** — clauses (ii) and (iii) of
`Work.Drive.PairOneData` at the two loop/chain meets of the pair datum. -/
theorem injective_mfderiv_of_goodLoopChain
    {L : ℝ → CappingSpace} {D : EuclideanSpace ℝ (Fin 3) → CappingSpace}
    (hGL : GoodLoopChain L D) {p : ℝ × EuclideanSpace ℝ (Fin 3)} (hp : p ∈ meetBox L D) :
    Function.Injective (mfderiv (𝓡 3) (𝓡 4) D p.2) :=
  (loopChain_rank_data hGL hp).2.2

/-! ## 3. The assembly: the pair datum from the polar dictionary and the rank data

`Work.Drive.PairOneData` (`regBaseAssembly.lean`) has three clauses: the mixed one (i) — no non-zero
direction is carried into *both* sweep ranges by the two plane blocks — and the injectivity of the two
sweeps (ii), (iii).  At an `s = 1` meet of the collapse pair the three clauses follow from

* the two `GoodLoopChain`s at the two meets the collapse produces (the **core** meet `(t, ftY x)` and
  the **diameter** meet `(σ, ftZ x)`), through `loopChain_rank_data`: the loop tangent is complementary
  to the sweep tangent, and the sweeps are immersed;
* `Work.Drive.PolarDict` (`hdensePolarDefs.lean`) — the derivative of the collapsed plane is a scalar
  multiple of the core loop's tangent, and every direction it kills is carried by the honest plane into
  the diameter loop's tangent;
* `Function.Injective (mfderiv (diskPlane Q) (ftU x))` — the **joint kernel** input.  This hypothesis
  is *not* redundant: on the faces of the parameter square the fold direction of `sqDisk ∘ foldBox` is
  killed by *both* plane blocks, so clause (i) fails there (see
  `Submission/Work/Drive/PAIRONEDATA_INTERIORITY_DEFECT.md`).  At a point with `ftU x` strictly
  interior it is supplied by the chart's immersion at `sqDisk (foldBox (ftU x))`
  (`injective_mfderiv_diskPlane_of_openSquare` below). -/

/-- **The pair datum from the rank data and the polar dictionary** — the assembly of
`Work.Drive.PairOneData` at an `s = 1` meet, with the *joint-kernel* input isolated as an explicit
hypothesis. -/
theorem pairOneData_of_rank_data
    {β : ℝ → ℝ} {Q : ℂ → CappingSpace}
    {P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace} {c₁ c₂ : ℝ}
    {x : EuclideanSpace ℝ (Fin 9)} {t σ : ℝ}
    (hcoreMeet : (t, ftY x) ∈ coreMeet Q c₁ P₁)
    (hdiamMeet : (σ, ftZ x) ∈ diamMeet Q t (clampedSweep c₂ (fun r => 1 - r) P₂))
    (hcore : GoodLoopChain (coreLoop Q) (clampedSweep c₁ (fun r => 1 - r) P₁))
    (hdiam : GoodLoopChain (diamLoop Q t) (clampedSweep c₂ (fun r => 1 - r) P₂))
    (hpd : PolarDict β Q (ftU x) t σ)
    (hB : Function.Injective (mfderiv (𝓡 2) (𝓡 4) (diskPlane Q) (ftU x))) :
    PairOneData (colPlane β Q) (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
      (clampedSweep c₁ (fun r => 1 - r) P₁) (clampedSweep c₂ (fun r => 1 - r) P₂) x := by
  obtain ⟨hL, hLne, hVinj⟩ := loopChain_rank_data hcore hcoreMeet
  obtain ⟨hDl, hDne, hWinj⟩ := loopChain_rank_data hdiam hdiamMeet
  have hDinj : Function.Injective
      (mfderiv (𝓡 3) (𝓡 4) (clampedSweep c₂ (fun r => 1 - r) P₂) (ftZ x)) := hWinj
  refine ⟨?_, ?_, ?_⟩
  · -- clause (i): the mixed condition
    intro a hinV hinW
    have hAin : mfderiv (𝓡 2) (𝓡 4) (colPlane β Q 1) (ftU x) a
        ∈ LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (coreLoop Q) t).toLinearMap := by
      obtain ⟨c, hc⟩ := hpd.1 a
      rw [hc]
      exact Submodule.smul_mem _ c (LinearMap.mem_range_self _ _)
    have hA0 : mfderiv (𝓡 2) (𝓡 4) (colPlane β Q 1) (ftU x) a = 0 := by
      have hmem : mfderiv (𝓡 2) (𝓡 4) (colPlane β Q 1) (ftU x) a
          ∈ LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (coreLoop Q) t).toLinearMap ⊓
            LinearMap.range (mfderiv (𝓡 3) (𝓡 4)
              (clampedSweep c₁ (fun r => 1 - r) P₁) (ftY x)).toLinearMap :=
        ⟨hAin, hinV⟩
      rw [hL, Submodule.mem_bot] at hmem
      exact hmem
    have hBin : mfderiv (𝓡 2) (𝓡 4) (diskPlane Q) (ftU x) a
        ∈ LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (diamLoop Q t) σ).toLinearMap :=
      hpd.2 a hA0
    have hB0 : mfderiv (𝓡 2) (𝓡 4) (diskPlane Q) (ftU x) a = 0 := by
      have hmem : mfderiv (𝓡 2) (𝓡 4) (diskPlane Q) (ftU x) a
          ∈ LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (diamLoop Q t) σ).toLinearMap ⊓
            LinearMap.range (mfderiv (𝓡 3) (𝓡 4)
              (clampedSweep c₂ (fun r => 1 - r) P₂) (ftZ x)).toLinearMap :=
        ⟨hBin, hinW⟩
      rw [hDl, Submodule.mem_bot] at hmem
      exact hmem
    have hz : mfderiv (𝓡 2) (𝓡 4) (diskPlane Q) (ftU x)
        (0 : TangentSpace (𝓡 2) (ftU x)) = 0 := map_zero _
    exact hB (by rw [hB0, hz])
  · exact hVinj
  · exact hDinj

/-- **The joint-kernel input at a strictly interior plane parameter**: the honest plane block is an
immersion there as soon as the chart is.  This is the `Q`-form of
`Work.Drive.injective_mfderiv_cls_diskPlane_of_openSquare` (`diskPlane_mfderiv.lean`, which states it
for the *class* map `cls ∘ Q`); with it the hypothesis `hB` of `pairOneData_of_rank_data` is obtained
from the chart's immersion and the interiority of the plane parameter, and it *fails* on the faces of
the square, where the fold direction of `sqDisk ∘ foldBox` is killed by both plane blocks. -/
theorem injective_mfderiv_diskPlane_of_openSquare
    {Q : ℂ → CappingSpace} {u : EuclideanSpace ℝ (Fin 2)}
    (hu0 : u 0 ∈ Set.Ioo (0 : ℝ) 1) (hu1 : u 1 ∈ Set.Ioo (0 : ℝ) 1)
    (hQdiff : MDifferentiableAt (𝓘(ℝ, ℂ)) (𝓡 4) Q (sqDisk (foldBox u)))
    (hQinj : Function.Injective
      (mfderiv (𝓘(ℝ, ℂ)) (𝓡 4) Q (sqDisk (foldBox u)))) :
    Function.Injective (mfderiv (𝓡 2) (𝓡 4) (diskPlane Q) u) := by
  have hfold : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) foldBox :=
    contDiff_iff_contDiffAt.mpr fun y => contMDiffAt_iff_contDiffAt.mp (foldBox_contMDiff y)
  have hΦcont : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun u : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox u)) :=
    sqDisk_contDiff.comp hfold
  have hΦdiff : MDifferentiableAt (𝓡 2) (𝓘(ℝ, ℂ))
      (fun u : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox u)) u :=
    (contMDiffAt_iff_contDiffAt.mpr hΦcont.contDiffAt).mdifferentiableAt (by simp)
  have hmain := mfderiv_comp (I := 𝓡 2) (I' := 𝓘(ℝ, ℂ)) (I'' := 𝓡 4)
    (f := fun u : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox u))
    (g := Q) u hQdiff hΦdiff
  have hfun : (diskPlane Q)
      = (Q ∘ fun u : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox u)) := rfl
  rw [hfun, hmain]
  intro a b hab
  have hab' : (mfderiv (𝓡 2) (𝓘(ℝ, ℂ))
      (fun u : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox u)) u) a
      = (mfderiv (𝓡 2) (𝓘(ℝ, ℂ))
      (fun u : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox u)) u) b := by
    apply hQinj
    simpa only [ContinuousLinearMap.coe_comp, Function.comp_apply] using hab
  have hinj : Function.Injective (mfderiv (𝓡 2) (𝓘(ℝ, ℂ))
      (fun u : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox u)) u) :=
    inj_mfderiv_sqDisk_foldBox u hu0 hu1
  have hzero : (mfderiv (𝓡 2) (𝓘(ℝ, ℂ))
      (fun u : EuclideanSpace ℝ (Fin 2) => sqDisk (foldBox u)) u) (a - b) = 0 := by
    rw [map_sub, hab', sub_self]
  exact sub_eq_zero.mp (hinj (by rw [hzero, map_zero]))

/-- **The two *sweep* parameters of an `s = 1` collar meet are strictly interior** — the half of the
consumer's `Work.Drive.CollarInterior` datum that comes for free from the two `GoodLoopChain`s (their
interiority clause), as soon as the meet is identified with the core/diameter meet it belongs to.  The
remaining coordinate — the *plane* parameter `ftU x` — is the genuine `collarInterior_one` obligation
(it is equivalent, for `u ∈ unitBox 1`, to `‖sqDisk (foldBox u)‖ < 1`, i.e. to the meet's disk point
not lying on the seam); see `PAIRONEDATA_INTERIORITY_DEFECT.md` §7. -/
theorem collarInterior_sweep_of_goodLoopChain
    {Q : ℂ → CappingSpace} {c₁ c₂ : ℝ}
    {P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace} {x : EuclideanSpace ℝ (Fin 9)} {t σ : ℝ}
    (hcoreMeet : (t, ftY x) ∈ coreMeet Q c₁ P₁)
    (hdiamMeet : (σ, ftZ x) ∈ diamMeet Q t (clampedSweep c₂ (fun r => 1 - r) P₂))
    (hcore : GoodLoopChain (coreLoop Q) (clampedSweep c₁ (fun r => 1 - r) P₁))
    (hdiam : GoodLoopChain (diamLoop Q t) (clampedSweep c₂ (fun r => 1 - r) P₂)) :
    (∀ i : Fin 3, ftY x i ∈ Set.Ioo (0 : ℝ) 1) ∧
      (∀ i : Fin 3, ftZ x i ∈ Set.Ioo (0 : ℝ) 1) :=
  ⟨(hcore.2.1 _ hcoreMeet).2, (hdiam.2.1 _ hdiamMeet).2⟩

/-! ## 4. Wrappers, and the failure of clause (i) on the faces of the square -/

/-- Smoothness of a plane presentation, as a `Prop` that can be mentioned without the local
`ChartedSpace CappingSpace` instance of the chart files. -/
def IsSmoothPlane (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) : Prop :=
  ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P

/-- The chart is an immersion at `z` (`Work.Drive.ImmersionAt`). -/
def ChartImmersiveAt (Q : ℂ → CappingSpace) (z : ℂ) : Prop :=
  Function.Injective (mfderiv (𝓘(ℝ, ℂ)) (𝓡 4) Q z)

/-- **`PairOneData` at the capping space**, as a `Prop` that can be mentioned without the local
`ChartedSpace CappingSpace` instance (the definition `Work.Drive.PairOneData` is polymorphic in the
target manifold, so mentioning it in a delegated statement requires the instance; this wrapper is
instance-free). -/
def PairOneDataC (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (V W : EuclideanSpace ℝ (Fin 3) → CappingSpace) (x : EuclideanSpace ℝ (Fin 9)) : Prop :=
  PairOneData E E' V W x

/-- **The repaired pair datum**: `PairOneData` at an `s = 1` meet of the collapse pair, from the polar
dictionary of the collapse, the two meet identifications and the *joint-kernel* input, which is
supplied here by the interiority of the plane parameter together with the chart's immersion at the
disk point.  This is `Work.Drive.pairOneData_of_T6GenAt` (`pairOneData_of_T6GenAt.lean`) with the two
hypotheses that statement is missing (`PAIRONEDATA_INTERIORITY_DEFECT.md` §3, §7); the only remaining
inputs are the dictionary `Work.Drive.PolarDict` and the two meets, both of which the collapse
dictionary (`collapse_polar_dictionary.lean`) produces. -/
theorem pairOneData_of_dictionary
    {β : ℝ → ℝ} {Q : ℂ → CappingSpace} (hQ : IsSmoothChart Q)
    {P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace} {c₁ c₂ : ℝ}
    {x : EuclideanSpace ℝ (Fin 9)} {t σ : ℝ}
    (hcoreMeet : (t, ftY x) ∈ coreMeet Q c₁ P₁)
    (hdiamMeet : (σ, ftZ x) ∈ diamMeet Q t (clampedSweep c₂ (fun r => 1 - r) P₂))
    (hcore : GoodLoopChain (coreLoop Q) (clampedSweep c₁ (fun r => 1 - r) P₁))
    (hdiam : GoodLoopChain (diamLoop Q t) (clampedSweep c₂ (fun r => 1 - r) P₂))
    (hpd : PolarDict β Q (ftU x) t σ)
    (hu0 : ftU x 0 ∈ Set.Ioo (0 : ℝ) 1) (hu1 : ftU x 1 ∈ Set.Ioo (0 : ℝ) 1)
    (himm : ChartImmersiveAt Q (sqDisk (foldBox (ftU x)))) :
    PairOneDataC (colPlane β Q) (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
      (clampedSweep c₁ (fun r => 1 - r) P₁) (clampedSweep c₂ (fun r => 1 - r) P₂) x :=
  pairOneData_of_rank_data hcoreMeet hdiamMeet hcore hdiam hpd
    (injective_mfderiv_diskPlane_of_openSquare hu0 hu1
      (hQ.mdifferentiableAt (by simp)) himm)

/-- **The repaired pair datum at an `s = 1` meet of the collapse pair**, in the *meet* form: the two
meet identifications are given as equalities of values (as `collapse_polar_dictionary` produces them),
so that a consumer at a point `x ∈ ppMeet ...` with `ftS x = 1` and the interiority of `ftU x` only has
to substitute the two meet equations. -/
theorem pairOneData_of_dictionary_meet
    {β : ℝ → ℝ} {Q : ℂ → CappingSpace} (hQ : IsSmoothChart Q)
    {P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace} {c₁ c₂ : ℝ}
    {x : EuclideanSpace ℝ (Fin 9)} {t σ : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (hσ : σ ∈ Set.Icc (0 : ℝ) 1)
    (hy : ftY x ∈ Submission.Drive.unitBox 2)
    (hz : ftZ x ∈ Submission.Drive.unitBox 2)
    (hcoreEq : coreLoop Q t = clampedSweep c₁ (fun r => 1 - r) P₁ (ftY x))
    (hdiamEq : diamLoop Q t σ = clampedSweep c₂ (fun r => 1 - r) P₂ (ftZ x))
    (hcore : GoodLoopChain (coreLoop Q) (clampedSweep c₁ (fun r => 1 - r) P₁))
    (hdiam : GoodLoopChain (diamLoop Q t) (clampedSweep c₂ (fun r => 1 - r) P₂))
    (hpd : PolarDict β Q (ftU x) t σ)
    (hu0 : ftU x 0 ∈ Set.Ioo (0 : ℝ) 1) (hu1 : ftU x 1 ∈ Set.Ioo (0 : ℝ) 1)
    (himm : ChartImmersiveAt Q (sqDisk (foldBox (ftU x)))) :
    PairOneDataC (colPlane β Q) (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
      (clampedSweep c₁ (fun r => 1 - r) P₁) (clampedSweep c₂ (fun r => 1 - r) P₂) x :=
  pairOneData_of_dictionary hQ ⟨ht, hy, hcoreEq⟩ ⟨hσ, hz, hdiamEq⟩ hcore hdiam hpd hu0 hu1 himm

/-- **The pair datum from the rank data, the polar dictionary and the *joint kernel*.**  This is the
sharp form of `pairOneData_of_rank_data`: the hypothesis on the honest plane block is only the
vanishing of its *joint* kernel with the collapsed plane, which is what the geometry actually supplies
(`Work.Drive.jointKernel_of_coreImmersive`, `pairOneDataKernel.lean`) and which holds at a strictly
interior plane parameter, whereas the full injectivity of `mfderiv (diskPlane Q) (ftU x)` used in
`pairOneData_of_rank_data` is *false* on the faces of the square. -/
theorem pairOneData_of_joint_kernel
    {β : ℝ → ℝ} {Q : ℂ → CappingSpace}
    {P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace} {c₁ c₂ : ℝ}
    {x : EuclideanSpace ℝ (Fin 9)} {t σ : ℝ}
    (hcoreMeet : (t, ftY x) ∈ coreMeet Q c₁ P₁)
    (hdiamMeet : (σ, ftZ x) ∈ diamMeet Q t (clampedSweep c₂ (fun r => 1 - r) P₂))
    (hcore : GoodLoopChain (coreLoop Q) (clampedSweep c₁ (fun r => 1 - r) P₁))
    (hdiam : GoodLoopChain (diamLoop Q t) (clampedSweep c₂ (fun r => 1 - r) P₂))
    (hpd : PolarDict β Q (ftU x) t σ)
    (hjk : ∀ a : EuclideanSpace ℝ (Fin 2),
      (mfderiv (𝓡 2) (𝓡 4) (colPlane β Q 1) (ftU x)) a = 0 →
      (mfderiv (𝓡 2) (𝓡 4) (diskPlane Q) (ftU x)) a = 0 → a = 0) :
    PairOneDataC (colPlane β Q) (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
      (clampedSweep c₁ (fun r => 1 - r) P₁) (clampedSweep c₂ (fun r => 1 - r) P₂) x := by
  obtain ⟨hL, hLne, hVinj⟩ := loopChain_rank_data hcore hcoreMeet
  obtain ⟨hDl, hDne, hWinj⟩ := loopChain_rank_data hdiam hdiamMeet
  refine ⟨?_, hVinj, hWinj⟩
  intro a hinV hinW
  have hAin : mfderiv (𝓡 2) (𝓡 4) (colPlane β Q 1) (ftU x) a
      ∈ LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (coreLoop Q) t).toLinearMap := by
    obtain ⟨c, hc⟩ := hpd.1 a
    rw [hc]
    exact Submodule.smul_mem _ c (LinearMap.mem_range_self _ _)
  have hA0 : mfderiv (𝓡 2) (𝓡 4) (colPlane β Q 1) (ftU x) a = 0 := by
    have hmem : mfderiv (𝓡 2) (𝓡 4) (colPlane β Q 1) (ftU x) a
        ∈ LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (coreLoop Q) t).toLinearMap ⊓
          LinearMap.range (mfderiv (𝓡 3) (𝓡 4)
            (clampedSweep c₁ (fun r => 1 - r) P₁) (ftY x)).toLinearMap :=
      ⟨hAin, hinV⟩
    rw [hL, Submodule.mem_bot] at hmem
    exact hmem
  have hBin : mfderiv (𝓡 2) (𝓡 4) (diskPlane Q) (ftU x) a
      ∈ LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (diamLoop Q t) σ).toLinearMap :=
    hpd.2 a hA0
  have hB0 : mfderiv (𝓡 2) (𝓡 4) (diskPlane Q) (ftU x) a = 0 := by
    have hmem : mfderiv (𝓡 2) (𝓡 4) (diskPlane Q) (ftU x) a
        ∈ LinearMap.range (mfderiv (𝓘(ℝ, ℝ)) (𝓡 4) (diamLoop Q t) σ).toLinearMap ⊓
          LinearMap.range (mfderiv (𝓡 3) (𝓡 4)
            (clampedSweep c₂ (fun r => 1 - r) P₂) (ftZ x)).toLinearMap :=
      ⟨hBin, hinW⟩
    rw [hDl, Submodule.mem_bot] at hmem
    exact hmem
  exact hjk a hA0 hB0

/-- **The plane parameter is strictly interior exactly when the disk point is strictly inside the
disk.**  For `u` in the parameter square, being on its boundary is the same as being on the seam of the
folded square, and (by `norm_sqDisk_eq_one_iff` and the strict positivity of the fold on `(0,1)`) that
is the same as `‖sqDisk (foldBox u)‖ = 1` (i.e. `‖cdFoldDisk u‖ = 1`).  This is the precise form of the
obstruction identified in `PAIRONEDATA_INTERIORITY_DEFECT.md` §8: the `s = 1` meets of the collapse
pair whose plane parameter is on the boundary of the square are exactly those whose disk point lies on
the unit circle, and excluding them is the design's obligation `collarInterior_one`. -/
theorem norm_sqDisk_foldBox_eq_one_iff {u : EuclideanSpace ℝ (Fin 2)}
    (hu : u ∈ Submission.Drive.unitBox 1) :
    ‖sqDisk (foldBox u)‖ = 1 ↔ ¬(∀ i : Fin 2, u i ∈ Set.Ioo (0 : ℝ) 1) := by
  rw [norm_sqDisk_eq_one_iff (foldBox u) (foldBox_mem_unitBox u)]
  simp only [onSeam2, foldBox_apply_zero, foldBox_apply_one]
  constructor
  · intro h hint
    rcases h with h | h | h | h
    · exact foldFun_ne_zero_of_mem_Ioo (hint 0) h
    · exact foldFun_ne_one_of_mem_Ioo (hint 0) h
    · exact foldFun_ne_zero_of_mem_Ioo (hint 1) h
    · exact foldFun_ne_one_of_mem_Ioo (hint 1) h
  · intro h
    push Not at h
    obtain ⟨i, hi⟩ := h
    have hbox : u i ∈ Set.Icc (0 : ℝ) 1 := hu i
    rw [Set.mem_Icc] at hbox
    have hval : u i = 0 ∨ u i = 1 := by
      rcases lt_or_ge (0 : ℝ) (u i) with hpos | hnonpos
      · right
        have hle : 1 ≤ u i := by
          by_contra hlt
          push Not at hlt
          exact hi ⟨hpos, hlt⟩
        exact le_antisymm hbox.2 hle
      · left
        exact le_antisymm hnonpos hbox.1
    rcases i with ⟨n, hn⟩
    interval_cases n
    · rcases hval with h0 | h0
      · exact Or.inl (by rw [show u 0 = 0 by simpa using h0, foldFun_zero])
      · exact Or.inr (Or.inl (by rw [show u 0 = 1 by simpa using h0, foldFun_one]))
    · rcases hval with h0 | h0
      · exact Or.inr (Or.inr (Or.inl (by
          rw [show u 1 = 0 by simpa using h0, foldFun_zero])))
      · exact Or.inr (Or.inr (Or.inr (by
          rw [show u 1 = 1 by simpa using h0, foldFun_one])))

end

end Work.Drive
