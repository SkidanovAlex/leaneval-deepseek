import Mathlib
import Submission.Work.Drive.sideCountDefs
import Submission.Work.Drive.clampedSweep
import Submission.Work.Drive.sideValue
import Submission.Work.Drive.designCountLocalityGen
import Submission.Work.Drive.chainLocalityDesign
import Submission.Work.Drive.classImageGraphData

/-!
# The *germ* side value `sideGerm` (the lead's design of 14:15) — definitions and germ bookkeeping

`Submission/Work/Drive/HN4_SEAM_DEFECT.md` records that the design's box count
`coreSideCount (linCapping A ∘ Q) c (rotPresentation Q w)` is not locally constant in the angle `w`:
its *parity* flips at the isolated angles where a meet crosses a seam of the parameter square (the
chain presentation `diskPlane = Q ∘ sqDisk ∘ foldBox` is `seamInv2`-invariant on the seam, so a meet on
the seam is counted twice by the box count), and the tangency/fold angles cannot be removed by one
fixed perturbation either.  The side value is therefore defined as a **germ**: the value taken by the
parity of the count over *small chart perturbations* `Ξ`, with "small" allowed to depend on the angle.

* `Work.Drive.chartDisk Q` — the image of the closed unit disk under the chart (the part of
  `CappingSpace` the plane occupies).
* `Work.Drive.ChartPert Q m Ξ` — a smooth `m`-parameter family of self-maps of `CappingSpace` with
  `Ξ 0 = id`, whose parameter-derivative at **every point of `CappingSpace`** is onto.  (The original
  draft asked this only on `chartDisk Q`; that is *not enough*: the meets of the count lie on the
  **sweep's** image, which is in the *rotated* disk `rotCapping w '' chartDisk Q`, not in `chartDisk
  Q` — so the Sard argument needs the surjectivity there as well.  `Work.Drive.exists_chartPert`
  (`Submission/Work/Drive/exists_chartPert.lean`) constructs the family by scaling the level and acting
  on the projective class by the transitive `S³`-action, and its surjectivity holds at *every* point of
  `CappingSpace` — the docstring there says so explicitly.  The strengthening loses nothing and is what
  the germ route consumes.)
* `Work.Drive.GoodPair Q₁ Q₂ c` — the design's regularity condition for a *pair* of plane
  presentations: finiteness of `coreMeet`, every meet **interior** in the box (this excludes at once the
  loop's seam and the chain's box seam — both are counted twice by the box parameterisation, cf.
  `HN4_SEAM_DEFECT.md`), and intrinsic transversality `range dLoop ⊔ range dSweep = ⊤` at every meet.
  At a `GoodPair` the box count is the parameterisation-free pairing `⟨[core loop], [sweep]⟩` and hence
  the mod-2 intersection number of the two images.
* `Work.Drive.GoodAt Ξ Q c w t` / `Work.Drive.CntAt Ξ Q c w t` — the two expressions occurring in
  `sideGerm`: the goodness of the perturbed pair and its count, for the *two independent* perturbations
  `t.1` (loop's chart) and `t.2` (sweep's chart).  Two independent perturbations are needed: the
  parameter-derivative of the *difference* map is `(A, −B)` with `A`, `B` separately onto, hence onto.
* `Work.Drive.sideGerm Ξ Q c w` — the germ parity: `1` iff, for every `t` near `0`, the perturbed pair
  is a `GoodPair` and its count is odd; otherwise `0`.  The guard `GoodPair → …` inside the `∀ᶠ`
  is what makes the definition independent of the perturbation: whenever the pair is not regular (a
  seam meet, a fold, a non-finite meet set) nothing is asked, and the Sard lane supplies regular
  parameters arbitrarily close to `0`.

The interface statements live in `Submission/Work/Drive/sideGerm.lean`:
`Work.Drive.sideGerm_spec` (the item (a) of the lead's message, to be proved), its `hn4`-shaped
corollary `Work.Drive.sideGerm_hn4`, and the wall-level glue `Work.Drive.parityCore_of_sideGerm`.

## The germ bookkeeping (this file)

`sideGerm` is a `Prop`-valued `if`, so its value is exactly "the good configurations near `0` are
odd".  The lemmas below make this explicit and reduce the value to *pointwise* statements about good
configurations, which is the form the Sard/locality lane supplies:

* `sideGerm_eq_one_iff` — `sideGerm = 1` iff good configurations of **even** count do *not* accumulate
  at `0` (equivalently: `∀ᶠ t, GoodAt → Odd`).
* `sideGerm_eq_one_iff_frequently_good_odd` — given (i) that good configurations accumulate at `0`
  (`hE`, the Sard existence) and (ii) that the parity is the same at any two good configurations in a
  ball (`hU`, the path/Sard statement), the germ value is `1` **iff there is a good configuration of
  odd count**.  This is the form in which the side value is compared across angles.
* `sideGerm_eq_of_germAgree` — if the good predicate and the parity of the count agree with those at
  the centre `w` in a ball around `0`, then the germ values at `w'` and `w` coincide.
* `sideGerm_localconst_of_eventually_germAgree` — the `∀ᶠ`-in-`w` version of the previous item, i.e.
  the `hn4` shape.
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The disk of the chart**: the image of the closed unit disk of `ℂ`. -/
def chartDisk (Q : ℂ → CappingSpace) : Set CappingSpace := Q '' Metric.closedBall (0 : ℂ) 1

/-- **A smooth chart** of the plane: a `C^∞` disk presentation of the capped plane.  (This is stated
as a definition so that statements *about* `Q` — for instance the delegated
`Work.Drive.sideGerm_spec` — do not have to mention the charted-space instances of `CappingSpace`,
which are `local` in the files that use them.) -/
def IsSmoothChart (Q : ℂ → CappingSpace) : Prop :=
  ContMDiff (𝓘(ℝ,ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q

/-- **The chart data the germ route needs**: a `C^∞` disk presentation of the capped plane together
with the **seam clause** `Q (-z) = Q z` on the unit circle.

The seam clause is *not* cosmetic: it is exactly the statement that the core loop
`Work.Drive.coreLoop Q = Q ∘ (t ↦ exp (iπt))` of the chart is **closed**
(`coreLoop Q 0 = Q 1`, `coreLoop Q 1 = Q (-1)`), and it also gives the `seamInv`-invariance of the
chain presentation `diskPlane Q = Q ∘ sqDisk ∘ foldBox` (`Work.Drive.diskPlane_seamInv2`).  Both are
inputs of the L6 family engine which computes the parity of the loop-vs-sweep count over the box
`[0,1] × unitBox 2`: without the closure, a meet can leave the box through the *loop's* seam faces
`a ∈ {0,1}` — which the box parameterisation does not identify — and the parity of the count jumps
between two good configurations.  Hence the parity-locality statement of the route
(`Drive/sideGerm_parity_eq_of_close`) is **false** on smooth charts alone (a prover of the fleet
verified this and returned `declare_false`), and the route's statements must carry the seam clause.

The clause is the third conjunct of `Work.Drive.IsPlaneChart` (`planeChartDefs.lean`), which is what the
chart lane produces, so the glue `IsChartData_of_isPlaneChart`
(`Submission/Work/Drive/chartIsSmooth.lean`) feeds the route from that output. -/
def IsChartData (Q : ℂ → CappingSpace) : Prop :=
  ContMDiff (𝓘(ℝ,ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q ∧
  (∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)

/-- A chart perturbation of the plane: a smooth `m`-parameter family of self-maps of the capping
space with `Ξ 0 = id` whose parameter-derivative at every parameter `t` and every point `p` of the
capping space is onto.

The canonical instance (the lead's item (e), proved in `Submission/Work/Drive/exists_chartPert.lean`)
is a finite union of chart shifts, scaling the level and acting on the projective class by the
transitive `S³`-action; its surjectivity holds at every point of `CappingSpace`.

**Why "every point of `CappingSpace`" and not only the chart's disk.**  The meets of the count are
pairs `(loop parameter, sweep parameter)` whose common value lies both on the chart's disk (the loop)
and on the *sweep*'s image, i.e. in the image of `diskPlane (rotCapping w ∘ Ξ t.2 ∘ Q)` — a subset of
the **rotated** disk `rotCapping w '' chartDisk (Ξ t.2 ∘ Q)`, which is *not* contained in `chartDisk Q`.
The parametric-Sard argument that produces good configurations needs the parameter-derivative of the
system to be onto at *every* zero of the system in the box, hence at every point of the rotated disk
too.  (This is the resolvent of the "set argument" of §6 of `GEOMETRIC_LOCALITY_STATUS.md`: the reviewer
noted there that the set argument of this definition is the single place to change.) -/
def ChartPert (_Q : ℂ → CappingSpace) (m : ℕ)
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) : Prop :=
  (∀ p : CappingSpace, Ξ 0 p = p) ∧
  ContMDiff ((𝓡 m).prod (𝓡 4)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
    (fun q : EuclideanSpace ℝ (Fin m) × CappingSpace => Ξ q.1 q.2) ∧
  ∀ (t : EuclideanSpace ℝ (Fin m)) (p : CappingSpace),
    Function.Surjective
      (mfderiv (𝓡 m) (𝓡 4) (fun t' => Ξ t' p) t)

/-- **The design's regularity condition for a pair of plane presentations**: the meet set of the core
loop of `Q₁` with the clamped sweep (cutoff `1 - ·`, level `c`) of `Q₂` is finite, every meet is
*interior* in the parameter box (both the loop parameter and all three chain parameters strictly
inside), and the loop and the sweep are transverse there — the intrinsic form
`range (mfderiv coreLoop) ⊔ range (mfderiv sweep) = ⊤`.

Interiority is the sharpest form of the seam hypotheses of
`Submission/Work/Drive/GEOMETRIC_LOCALITY_STATUS.md`: it excludes at once the loop's seam (`q 1 = 0`
or `1`) and the chain's box seam (`q 2 i ∈ {0,1}`), and at such a pair the box count and the
parameterisation-free geometric count of the meets agree — so the box count is the mod-2 intersection
number of the core loop with the sweep's image (`HN4_SEAM_DEFECT.md`). -/
def GoodPair (Q₁ Q₂ : ℂ → CappingSpace) (c : ℝ) : Prop :=
  ContMDiff (𝓘(ℝ,ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q₁ ∧
  ContMDiff (𝓘(ℝ,ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q₂ ∧
  (coreMeet Q₁ c (diskPlane Q₂)).Finite ∧
  (∀ q ∈ coreMeet Q₁ c (diskPlane Q₂),
    q.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ i : Fin 3, q.2 i ∈ Set.Ioo (0 : ℝ) 1) ∧
  (∀ q ∈ coreMeet Q₁ c (diskPlane Q₂),
    LinearMap.range (mfderiv (𝓘(ℝ,ℝ)) (𝓡 4) (coreLoop Q₁) q.1).toLinearMap ⊔
      LinearMap.range
        (mfderiv (𝓡 3) (𝓡 4)
          (clampedSweep c (fun t => 1 - t) (diskPlane Q₂)) q.2).toLinearMap = ⊤)

/-- The chart of the plane after the perturbation with parameter `t`. -/
def pertChart {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (t : EuclideanSpace ℝ (Fin m)) : ℂ → CappingSpace :=
  fun z => Ξ t (Q z)

/-- **The goodness of the perturbed pair** at the angle `w`: `GoodPair` for the two independently
perturbed charts `Ξ t.1 ∘ Q` (the loop's chart) and `rotCapping w ∘ Ξ t.2 ∘ Q` (the sweep's chart).
This is the guard of `sideGerm`. -/
def GoodAt {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle)
    (t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) : Prop :=
  GoodPair (pertChart Ξ Q t.1) (fun p => rotCapping w (pertChart Ξ Q t.2 p)) c

/-- **The count of the perturbed pair** at the angle `w`: the loop-vs-sweep box count of the
perturbed chart `Ξ t.1 ∘ Q` against the sweep of the rotated perturbed chart `Ξ t.2 ∘ Q`. -/
def CntAt {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle)
    (t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) : ℕ :=
  coreSideCount (pertChart Ξ Q t.1) c (rotPresentation (pertChart Ξ Q t.2) w)

/-- **The germ side value.**  `sideGerm Ξ Q c w = 1` iff, for every parameter `t` near `0`, the pair
of perturbed charts `(Ξ t.1 ∘ Q, rot w ∘ Ξ t.2 ∘ Q)` is a `GoodPair` and its loop-vs-sweep count is
odd.  The guard `GoodPair → …` is what makes the value independent of `Ξ`: at the irregular parameters
nothing is asked. -/
def sideGerm {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle) : ZMod 2 := by
  classical
  exact if ∀ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c w t → Odd (CntAt Ξ Q c w t) then 1 else 0

/-- The two-parameter germ form of `sideGerm` (the perturbation of the loop's chart and of the
sweep's chart are independent, which is what the Sard argument needs). -/
theorem sideGerm_eq_iff {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle) :
    sideGerm Ξ Q c w = 1 ↔
      ∀ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c w t → Odd (CntAt Ξ Q c w t) := by
  rw [sideGerm]
  by_cases h : ∀ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c w t → Odd (CntAt Ξ Q c w t)
  · rw [if_pos h]; exact ⟨fun _ => h, fun _ => rfl⟩
  · rw [if_neg h]; exact ⟨fun h1 => absurd h1 zero_ne_one, fun h2 => absurd h2 h⟩

/-- **The chart's disk is compact** when the chart is continuous. -/
lemma chartDisk_compact {Q : ℂ → CappingSpace} (hQ : Continuous Q) : IsCompact (chartDisk Q) :=
  (isCompact_closedBall (0 : ℂ) 1).image hQ

/-- **The disjointness of the chart's disk from its rotation is an *open* condition in the angle.**
With `hQ` continuous, `chartDisk Q` is compact, and the set of angles at which it meets its rotation is
the continuous image of the compact `chartDisk Q × univ × chartDisk Q ∩ {x = rot w q}`, hence closed;
`hdisj` says that `w` is not in it. -/
theorem chartDisk_disjoint_nhds {Q : ℂ → CappingSpace} (hQ : Continuous Q)
    {w : UnitAddCircle} (hdisj : Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q)) :
    ∀ᶠ w' in 𝓝 w, Disjoint (chartDisk Q) (rotCapping w' '' chartDisk Q) := by
  set A : Set CappingSpace := chartDisk Q with hA
  have hAcomp : IsCompact A := chartDisk_compact hQ
  have hVclosed : IsClosed {z : CappingSpace × (UnitAddCircle × CappingSpace) |
      z.1 = rotCapping z.2.1 z.2.2} :=
    isClosed_eq continuous_fst (continuous_rotCapping_uncurry.comp
      ((continuous_fst.comp continuous_snd).prodMk (continuous_snd.comp continuous_snd)))
  have hWcomp : IsCompact (A ×ˢ (Set.univ : Set UnitAddCircle) ×ˢ A) :=
    hAcomp.prod (isCompact_univ.prod hAcomp)
  set K : Set UnitAddCircle := (fun z : CappingSpace × (UnitAddCircle × CappingSpace) => z.2.1) ''
    ((A ×ˢ (Set.univ : Set UnitAddCircle) ×ˢ A) ∩ {z | z.1 = rotCapping z.2.1 z.2.2}) with hKdef
  have hKclosed : IsClosed K := by
    rw [hKdef]
    exact ((hWcomp.inter_right hVclosed).image
      (continuous_fst.comp continuous_snd)).isClosed
  have hnotmem : w ∉ K := by
    rintro ⟨z, ⟨⟨hzA, -, hqA⟩, hzV⟩, rfl⟩
    exact (Set.disjoint_left.mp hdisj hzA) ⟨z.2.2, hqA, hzV.symm⟩
  filter_upwards [hKclosed.isOpen_compl.mem_nhds hnotmem] with w' hw'
  rw [Set.disjoint_iff_inter_eq_empty]
  ext x
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false, not_and]
  rintro hxA ⟨q, hqA, hxq⟩
  exact hw' ⟨(x, (w', q)), ⟨⟨hxA, Set.mem_univ _, hqA⟩, hxq.symm⟩, rfl⟩

/-! ## The germ bookkeeping -/

/-- **The germ value is `1` exactly when good configurations of even count do not accumulate at
`0`.**  This is the `Prop`-level unfolding of the definition of `sideGerm`. -/
theorem sideGerm_eq_one_iff {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle) :
    sideGerm Ξ Q c w = 1 ↔
      ¬ ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c w t ∧ Even (CntAt Ξ Q c w t) := by
  have hpt : ∀ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      (GoodAt Ξ Q c w t → Odd (CntAt Ξ Q c w t)) ↔
        ¬ (GoodAt Ξ Q c w t ∧ Even (CntAt Ξ Q c w t)) := by
    intro t
    constructor
    · rintro h ⟨hg, he⟩
      exact (Nat.not_odd_iff_even.mpr he) (h hg)
    · intro h hg
      by_contra hno
      exact h ⟨hg, Nat.not_odd_iff_even.mp hno⟩
  have hiff : (∀ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c w t → Odd (CntAt Ξ Q c w t)) ↔
      ¬ ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c w t ∧ Even (CntAt Ξ Q c w t) := by
    rw [Filter.not_frequently]
    exact Filter.eventually_congr (Filter.Eventually.of_forall hpt)
  rw [sideGerm]
  by_cases h : ∀ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c w t → Odd (CntAt Ξ Q c w t)
  · rw [if_pos h]
    exact ⟨fun _ => hiff.mp h, fun _ => rfl⟩
  · rw [if_neg h]
    exact ⟨fun h1 => absurd h1 zero_ne_one, fun h2 => absurd (hiff.mpr h2) h⟩

/-- The `≠ 1` form of `sideGerm_eq_one_iff`: the germ vanishes exactly when good configurations of
even count accumulate at `0`. -/
theorem sideGerm_ne_one_iff {m : ℕ} (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle) :
    sideGerm Ξ Q c w ≠ 1 ↔
      ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c w t ∧ Even (CntAt Ξ Q c w t) :=
  (Iff.not (sideGerm_eq_one_iff Ξ Q c w)).trans not_not

/-- **The germ value from the good set.**  Assume

* `hE` (the Sard existence): every ball around `0` contains a good configuration, i.e. good
  configurations *accumulate* at `0`;
* `hU` (the path/Sard statement): there is a ball in which any two good configurations have the same
  count parity.

Then the germ value is `1` exactly when there is a good configuration of **odd** count, i.e.
`sideGerm Ξ Q c w = 1 ↔ ∃ᶠ t, GoodAt t ∧ Odd (CntAt t)`.

(`hU` is the honest content: at a good configuration the box count is the mod-2 intersection number of
the loop with the sweep, which is unchanged by the deformation as long as the loop stays off the swept
plane — the hypothesis `hdisj` of `sideGerm_spec` and the smallness of the perturbation.  Its proof is
the L6 family engine along a *good path* joining the two configurations, the path being produced by the
parametric Sard on the box `[0,1] × unitBox 2`.) -/
theorem sideGerm_eq_one_iff_frequently_good_odd {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle)
    (hE : ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c w t)
    (hU : ∃ ε : ℝ, 0 < ε ∧ ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → ‖t'‖ < ε → GoodAt Ξ Q c w t → GoodAt Ξ Q c w t' →
        Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ Q c w t')) :
    sideGerm Ξ Q c w = 1 ↔
      ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c w t ∧ Odd (CntAt Ξ Q c w t) := by
  rw [sideGerm_eq_one_iff]
  constructor
  · intro h
    have hP : ∀ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c w t → Odd (CntAt Ξ Q c w t) := by
      rw [Filter.not_frequently] at h
      filter_upwards [h] with t ht hg
      by_contra hno
      exact ht ⟨hg, Nat.not_odd_iff_even.mp hno⟩
    exact (hE.and_eventually hP).mono fun t ht => ⟨ht.1, ht.2 ht.1⟩
  · intro h
    rw [Filter.not_frequently]
    obtain ⟨ε, hε, hUε⟩ := hU
    have hball : ∀ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        ‖t‖ < ε := by
      filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin m) ×
        EuclideanSpace ℝ (Fin m)) hε] with t ht
      rwa [Metric.mem_ball, dist_zero_right] at ht
    obtain ⟨t₀, ⟨⟨hg₀, ho₀⟩, ht₀⟩⟩ := (h.and_eventually hball).exists
    filter_upwards [hball] with t ht
    rintro ⟨hg, hEven⟩
    have hodd : Odd (CntAt Ξ Q c w t) := by
      rw [hUε t t₀ ht ht₀ hg hg₀]
      exact ho₀
    exact (Nat.not_odd_iff_even.mpr hEven) hodd

/-- **The germ is unchanged by a perturbation of the angle that agrees with the centre near `0`.**
If the good predicate and the parity of the count at the angle `w'` agree with those at `w` on a ball
around `0`, then `sideGerm Ξ Q c w' = sideGerm Ξ Q c w`. -/
theorem sideGerm_eq_of_germAgree {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) {w w' : UnitAddCircle}
    (hst : ∃ ε : ℝ, 0 < ε ∧ ∀ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
      ‖t‖ < ε → (GoodAt Ξ Q c w' t ↔ GoodAt Ξ Q c w t) ∧
        Odd (CntAt Ξ Q c w' t) = Odd (CntAt Ξ Q c w t)) :
    sideGerm Ξ Q c w' = sideGerm Ξ Q c w := by
  classical
  obtain ⟨ε, hε, hstε⟩ := hst
  have hpred : ∀ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m), ‖t‖ < ε →
      ((GoodAt Ξ Q c w' t → Odd (CntAt Ξ Q c w' t)) ↔
        (GoodAt Ξ Q c w t → Odd (CntAt Ξ Q c w t))) := by
    intro t ht
    obtain ⟨hG, hp⟩ := hstε t ht
    rw [hG, hp]
  have heq : (∀ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c w' t → Odd (CntAt Ξ Q c w' t)) ↔
      (∀ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c w t → Odd (CntAt Ξ Q c w t)) := by
    constructor
    · intro h
      obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp h
      refine Metric.mem_nhds_iff.mpr ⟨min δ ε, lt_min hδ hε, fun t ht => ?_⟩
      rw [Metric.mem_ball, dist_zero_right] at ht
      exact (hpred t (lt_of_lt_of_le ht (min_le_right _ _))).mp
        (hδsub (by rw [Metric.mem_ball, dist_zero_right]
                   exact lt_of_lt_of_le ht (min_le_left _ _)))
    · intro h
      obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp h
      refine Metric.mem_nhds_iff.mpr ⟨min δ ε, lt_min hδ hε, fun t ht => ?_⟩
      rw [Metric.mem_ball, dist_zero_right] at ht
      exact (hpred t (lt_of_lt_of_le ht (min_le_right _ _))).mpr
        (hδsub (by rw [Metric.mem_ball, dist_zero_right]
                   exact lt_of_lt_of_le ht (min_le_left _ _)))
  rw [sideGerm, sideGerm]
  by_cases h1 : ∀ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c w' t → Odd (CntAt Ξ Q c w' t)
  · rw [if_pos h1]
    by_cases h2 : ∀ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c w t → Odd (CntAt Ξ Q c w t)
    · rw [if_pos h2]
    · rw [if_neg h2]; exact absurd (heq.mp h1) h2
  · rw [if_neg h1]
    by_cases h2 : ∀ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c w t → Odd (CntAt Ξ Q c w t)
    · rw [if_pos h2]; exact absurd (heq.mpr h2) h1
    · rw [if_neg h2]

/-- **The assembly of the germ route.**  Assume

* `hA` (the Sard existence, `Drive/sideGerm_good_exists`): for **every** angle good configurations
  accumulate at `0`;
* `hC` (the parity locality, `Drive/sideGerm_parity_eq_of_close`): at the centre `w` there are
  `ε, δ > 0` such that any good configuration of norm `< ε` at `w` and any good configuration of norm
  `< ε` at an angle `w'` with `dist w' w < δ` have the **same count parity**.

Then `sideGerm Ξ Q c` is constant near `w`.  The proof is the germ bookkeeping of this file: by
`sideGerm_eq_one_iff_frequently_good_odd` (applied at `w` and at `w'`, the self-uniformity of the
parity at each of the two angles following from `hC` by comparison with a fixed good configuration of
the centre) the germ value is `1` exactly when there is a good configuration of odd count, and `hC`
transfers "good configuration of odd count" between the angles `w` and `w'`. -/
theorem sideGerm_localconst_of_exists_and_parity {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle)
    (hA : ∀ w' : UnitAddCircle, ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c w' t)
    (hC : ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (w' : UnitAddCircle),
        ‖t‖ < ε → ‖t'‖ < ε → dist w' w < δ → GoodAt Ξ Q c w t → GoodAt Ξ Q c w' t' →
          Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ Q c w' t')) :
    ∀ᶠ w' in 𝓝 w, sideGerm Ξ Q c w' = sideGerm Ξ Q c w := by
  classical
  obtain ⟨ε, δ, hε, hδ, hCεδ⟩ := hC
  have hball : ∀ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0, ‖t‖ < ε := by
    filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin m)) hε] with t ht
    rwa [Metric.mem_ball, dist_zero_right] at ht
  obtain ⟨t₀, hgood₀, ht₀⟩ := (hA w).and_eventually hball |>.exists
  have hUw : ∃ ε' : ℝ, 0 < ε' ∧
      ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
        ‖t‖ < ε' → ‖t'‖ < ε' → GoodAt Ξ Q c w t → GoodAt Ξ Q c w t' →
          Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ Q c w t') :=
    ⟨ε, hε, fun t t' ht ht' hg hg' => hCεδ t t' w ht ht' (by simpa using hδ) hg hg'⟩
  filter_upwards [Metric.ball_mem_nhds w hδ] with w' hw'
  have hUw' : ∃ ε' : ℝ, 0 < ε' ∧
      ∀ t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m),
        ‖t‖ < ε' → ‖t'‖ < ε' → GoodAt Ξ Q c w' t → GoodAt Ξ Q c w' t' →
          Odd (CntAt Ξ Q c w' t) = Odd (CntAt Ξ Q c w' t') :=
    ⟨ε, hε, fun t t' ht ht' hg hg' =>
      (hCεδ t₀ t w' ht₀ ht hw' hgood₀ hg).symm.trans
        (hCεδ t₀ t' w' ht₀ ht' hw' hgood₀ hg')⟩
  have hiff_w' : (∀ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c w' t → Odd (CntAt Ξ Q c w' t)) ↔
      ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c w' t ∧ Odd (CntAt Ξ Q c w' t) :=
    (sideGerm_eq_iff Ξ Q c w').symm.trans
      (sideGerm_eq_one_iff_frequently_good_odd Ξ Q c w' (hA w') hUw')
  have hiff_w : (∀ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c w t → Odd (CntAt Ξ Q c w t)) ↔
      ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c w t ∧ Odd (CntAt Ξ Q c w t) :=
    (sideGerm_eq_iff Ξ Q c w).symm.trans
      (sideGerm_eq_one_iff_frequently_good_odd Ξ Q c w (hA w) hUw)
  have hkey : (∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c w' t ∧ Odd (CntAt Ξ Q c w' t)) ↔
      ∃ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c w t ∧ Odd (CntAt Ξ Q c w t) := by
    constructor
    · intro hf
      obtain ⟨t₂, ⟨⟨hg₂, ho₂⟩, ht₂⟩⟩ := (hf.and_eventually hball).exists
      exact ((hA w).and_eventually hball).mono fun t ht =>
        ⟨ht.1, (hCεδ t t₂ w' ht.2 ht₂ hw' ht.1 hg₂) ▸ ho₂⟩
    · intro hf
      obtain ⟨t₁, ⟨⟨hg₁, ho₁⟩, ht₁⟩⟩ := (hf.and_eventually hball).exists
      exact ((hA w').and_eventually hball).mono fun t' ht' =>
        ⟨ht'.1, (hCεδ t₁ t' w' ht₁ ht'.2 hw' hg₁ ht'.1) ▸ ho₁⟩
  rw [sideGerm, sideGerm]
  by_cases h1 : ∀ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
      GoodAt Ξ Q c w' t → Odd (CntAt Ξ Q c w' t)
  · rw [if_pos h1]
    by_cases h2 : ∀ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c w t → Odd (CntAt Ξ Q c w t)
    · rw [if_pos h2]
    · rw [if_neg h2]
      exact absurd (hiff_w.mpr (hkey.mp (hiff_w'.mp h1))) h2
  · rw [if_neg h1]
    by_cases h2 : ∀ᶠ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) in 𝓝 0,
        GoodAt Ξ Q c w t → Odd (CntAt Ξ Q c w t)
    · rw [if_pos h2]
      exact absurd (hiff_w'.mpr (hkey.mpr (hiff_w.mp h2))) h1
    · rw [if_neg h2]

/-- **Local constancy of the germ value** (the `hn4` shape): if for `w'` near `w` the good predicate
and the count parity agree with the centre `w` in a ball around `0`, then `sideGerm Ξ Q c` is constant
on a neighbourhood of `w`. -/
theorem sideGerm_localconst_of_eventually_germAgree {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace)
    (Q : ℂ → CappingSpace) (c : ℝ) (w : UnitAddCircle)
    (h : ∀ᶠ w' in 𝓝 w, ∃ ε : ℝ, 0 < ε ∧
      ∀ t : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m), ‖t‖ < ε →
        (GoodAt Ξ Q c w' t ↔ GoodAt Ξ Q c w t) ∧
          Odd (CntAt Ξ Q c w' t) = Odd (CntAt Ξ Q c w t)) :
    ∀ᶠ w' in 𝓝 w, sideGerm Ξ Q c w' = sideGerm Ξ Q c w :=
  h.mono fun _ hw => sideGerm_eq_of_germAgree Ξ Q c hw

end

end Work.Drive
