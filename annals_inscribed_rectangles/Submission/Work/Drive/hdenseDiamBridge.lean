import Mathlib
import Submission.Work.Drive.T6GenAtDefs
import Submission.Work.Drive.collapseTransport
import Submission.Work.Drive.colMeet_one_ncard_eq_fibreMeet
import Submission.Work.Drive.sideGermDefs

/-!
# The diameter clause of the transport's at-`t` bundle `T6GenAt`, in the forms the design consumes

*(Node `Work.Drive.hdense_sideGerm`, the wall `hdense`.  Read with `HDENSE_STATUS.md` (addendum 2),
`NOTES_LEAD_hblock_uniformity.md` §4.2/§4.3, `NOTES_LEAD_hfib.md` §0.)*

`Work.Drive.T6GenAt Q P₁ P₂ c₁ c₂` (`T6GenAtDefs.lean`) has three conjuncts: the core loop of `Q`
meets the sweep of `P₁` in general position (`GoodLoopChain`), at **every** core meet the *diameter*
loop of `Q` meets the sweep of `P₂` in general position, and the cut of `Q` misses a neighbourhood of
the origin.  This module provides the dictionary between that second conjunct and the hypotheses of
the transport `T6` (`hfind`, `ht5`, `hδcut`), namely

* `meetBox_diamLoop` / `meetBox_arcLoop` — `GoodLoopChain (diamLoop Q t) W` is *by definition* the
  triple of properties of `diamMeet Q t W` (and likewise for the half-circle loop `arcLoop`);
* `hfind_of_T6GenAt` / `hint_of_T6GenAt` — the finiteness and the strict interiority of `diamMeet`
  at the core meets, i.e. exactly the `hfind` input of `T6` at the design's blocks;
* `diamMeet_transverse_of_T6GenAt` — the transversality clause of the same bundle.

The last two lemmas of the module record a **necessary condition** that the diameter clause forces and
that the lane's genericity statement must therefore include: the diameter loop `diamLoop Q t` *starts*
(and, for a seam-invariant chart, *ends*) at the core loop point `coreLoop Q t`
(`diamLoop_zero`, `diamLoop_one_of_seam`), so the interiority clause of `GoodLoopChain` says that the
core loop at such a `t` **does not meet the diameter partner's chain at all**
(`not_mem_coreMeet_of_goodLoopChain_diamLoop`).  In the design this means: the core-meet angles of the
pair `(blockChart k, P₁)` must avoid the core-meet angles of the pair `(blockChart k, P₂)` — an
additional open-dense avoidance in the free parameter, which the *single* condition
"D(diam)meet is generic" does **not** imply and which has to be built into the producer.

Everything here is sorry-free and axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-! ## 1. `GoodLoopChain` is the `diamMeet` / `arcMeet` regularity -/

/-- **The meet box of the *diameter* loop is the diameter meet set** (definitionally): the design's
`diamMeet Q t W` is `meetBox (diamLoop Q t) W`. -/
theorem meetBox_diamLoop (Q : ℂ → CappingSpace) (t : ℝ)
    (W : EuclideanSpace ℝ (Fin 3) → CappingSpace) :
    meetBox (diamLoop Q t) W = diamMeet Q t W := rfl

/-- **The meet box of the *half-circle* loop is the arc meet set** (definitionally). -/
theorem meetBox_arcLoop (Q : ℂ → CappingSpace) (t : ℝ)
    (W : EuclideanSpace ℝ (Fin 3) → CappingSpace) :
    meetBox (arcLoop Q t) W = arcMeet Q t W := rfl

/-- The diameter meet set is finite whenever the diameter loop is transverse to the chain. -/
theorem diamMeet_finite_of_goodLoopChain {Q : ℂ → CappingSpace} {t : ℝ}
    {W : EuclideanSpace ℝ (Fin 3) → CappingSpace}
    (h : GoodLoopChain (diamLoop Q t) W) : (diamMeet Q t W).Finite := by
  rw [← meetBox_diamLoop]; exact h.1

/-- Every diameter meet is strictly interior in the box, whenever the diameter loop is transverse to
the chain. -/
theorem diamMeet_interior_of_goodLoopChain {Q : ℂ → CappingSpace} {t : ℝ}
    {W : EuclideanSpace ℝ (Fin 3) → CappingSpace}
    (h : GoodLoopChain (diamLoop Q t) W) :
    ∀ p ∈ diamMeet Q t W,
      p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ i : Fin 3, p.2 i ∈ Set.Ioo (0 : ℝ) 1 := by
  intro p hp
  rw [← meetBox_diamLoop] at hp
  exact h.2.1 p hp

/-- The diameter loop and the chain are transverse at every diameter meet. -/
theorem diamMeet_transverse_of_goodLoopChain {Q : ℂ → CappingSpace} {t : ℝ}
    {W : EuclideanSpace ℝ (Fin 3) → CappingSpace}
    (h : GoodLoopChain (diamLoop Q t) W) :
    ∀ p ∈ diamMeet Q t W,
      LinearMap.range (mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (diamLoop Q t) p.1).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) W p.2).toLinearMap = ⊤ := by
  intro p hp
  rw [← meetBox_diamLoop] at hp
  exact h.2.2 p hp

/-- The half-circle loop meets the chain finitely often whenever it is transverse to it. -/
theorem arcMeet_finite_of_goodLoopChain {Q : ℂ → CappingSpace} {t : ℝ}
    {W : EuclideanSpace ℝ (Fin 3) → CappingSpace}
    (h : GoodLoopChain (arcLoop Q t) W) : (arcMeet Q t W).Finite := by
  rw [← meetBox_arcLoop]; exact h.1

/-! ## 2. The transport inputs at the design's blocks -/

/-- **`hfind` of the transport, straight out of the second conjunct of `T6GenAt`**: the diameter meet
set of `Q` against the sweep of `P₂` is finite at every core meet with the sweep of `P₁`. -/
theorem hfind_of_T6GenAt {Q : ℂ → CappingSpace}
    {P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace} {c₁ c₂ : ℝ}
    (h : T6GenAt Q P₁ P₂ c₁ c₂) :
    ∀ q ∈ coreMeet Q c₁ P₁,
      (diamMeet Q q.1 (clampedSweep c₂ (fun t => 1 - t) P₂)).Finite :=
  fun q hq => diamMeet_finite_of_goodLoopChain (h.2.1 q hq)

/-- **The interiority of the diameter meets at the core meets**, again from `T6GenAt`'s second
conjunct: no diameter meet lies on the boundary of the parameter box. -/
theorem hint_of_T6GenAt {Q : ℂ → CappingSpace}
    {P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace} {c₁ c₂ : ℝ}
    (h : T6GenAt Q P₁ P₂ c₁ c₂) :
    ∀ q ∈ coreMeet Q c₁ P₁, ∀ p ∈ diamMeet Q q.1 (clampedSweep c₂ (fun t => 1 - t) P₂),
      p.1 ∈ Set.Ioo (0 : ℝ) 1 ∧ ∀ i : Fin 3, p.2 i ∈ Set.Ioo (0 : ℝ) 1 :=
  fun q hq => diamMeet_interior_of_goodLoopChain (h.2.1 q hq)

/-- The transversality of the diameter meets at the core meets, from `T6GenAt`'s second conjunct. -/
theorem htrans_diam_of_T6GenAt {Q : ℂ → CappingSpace}
    {P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace} {c₁ c₂ : ℝ}
    (h : T6GenAt Q P₁ P₂ c₁ c₂) :
    ∀ q ∈ coreMeet Q c₁ P₁, ∀ p ∈ diamMeet Q q.1 (clampedSweep c₂ (fun t => 1 - t) P₂),
      LinearMap.range (mfderiv 𝓘(ℝ, ℝ) (𝓡 4) (diamLoop Q q.1) p.1).toLinearMap ⊔
        LinearMap.range
          (mfderiv (𝓡 3) (𝓡 4) (clampedSweep c₂ (fun t => 1 - t) P₂) p.2).toLinearMap = ⊤ :=
  fun q hq => diamMeet_transverse_of_goodLoopChain (h.2.1 q hq)

/-! ## 3. The endpoints of the diameter loop, and the avoidance the diameter clause forces -/

/-- **The diameter loop at parameter `0` is the core loop point at the angle `t`.** -/
theorem diamLoop_zero (Q : ℂ → CappingSpace) (t : ℝ) : diamLoop Q t 0 = coreLoop Q t := by
  rw [diamLoop_eq, ← polPt_ofReal (t := t) (σ := 0), coreLoop]
  have hcoef : (((1 - 2 * (0 : ℝ)) : ℝ) : ℂ) = (1 : ℂ) := by norm_num
  rw [hcoef, one_mul]

/-- **The diameter loop at parameter `1` is again the core loop point at the angle `t`**, for a chart
satisfying the seam clause (the two endpoints `± e^{iπt}` have equal image). -/
theorem diamLoop_one_of_seam {Q : ℂ → CappingSpace}
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z) (t : ℝ) :
    diamLoop Q t 1 = coreLoop Q t := by
  have hz : ‖Complex.exp (Real.pi * (t : ℂ) * Complex.I)‖ = 1 := norm_exp_pi_mul_I t
  rw [diamLoop_eq, ← polPt_ofReal (t := t) (σ := 1), coreLoop]
  have hcoef : (((1 - 2 * (1 : ℝ)) : ℝ) : ℂ) = (-1 : ℂ) := by norm_num
  rw [hcoef, neg_one_mul]
  exact hQseam _ hz

/-- **The half-circle loop at parameter `0` is the core loop point at the angle `t`.** -/
theorem arcLoop_zero (Q : ℂ → CappingSpace) (t : ℝ) : arcLoop Q t 0 = coreLoop Q t := by
  unfold arcLoop coreLoop
  congr 1
  congr 1
  push_cast
  ring

/-- **A necessary condition of the diameter clause**: if the diameter loop `diamLoop Q t` meets the
chain `W` in general position (`GoodLoopChain`), then the core loop point `coreLoop Q t` — which is the
*start* of the diameter loop — does **not** lie on the chain.  (The corresponding meet `(0, y)` would
be on the boundary of the parameter box, contradicting strict interiority.)

In the design this says: the core-meet angles of `(blockChart k, P₁)` must avoid the core-meet angles
of `(blockChart k, P₂)` — an extra avoidance which the diameter clause *entails*, and which a producer
of `T6GenAt` must therefore establish. -/
theorem not_mem_coreMeet_of_goodLoopChain_diamLoop {Q : ℂ → CappingSpace} {t c : ℝ} {ψ : ℝ → ℝ}
    {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (h : GoodLoopChain (diamLoop Q t) (clampedSweep c ψ P)) :
    ∀ y ∈ Submission.Drive.unitBox 2, coreLoop Q t ≠ clampedSweep c ψ P y := by
  intro y hy heq
  have hmem : (0, y) ∈ meetBox (diamLoop Q t) (clampedSweep c ψ P) :=
    ⟨⟨le_rfl, zero_le_one⟩, hy, by rw [diamLoop_zero]; exact heq⟩
  exact absurd (h.2.1 (0, y) hmem).1.1 (lt_irrefl (0 : ℝ))

/-- The `σ = 1` form of `not_mem_coreMeet_of_goodLoopChain_diamLoop`: for a seam-invariant chart the
diameter loop also *ends* at the core loop point, so the same avoidance follows from the interiority
at the *upper* end of the box. -/
theorem not_mem_coreMeet_of_goodLoopChain_diamLoop_one {Q : ℂ → CappingSpace}
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z) {t c : ℝ} {ψ : ℝ → ℝ}
    {P : EuclideanSpace ℝ (Fin 2) → CappingSpace}
    (h : GoodLoopChain (diamLoop Q t) (clampedSweep c ψ P)) :
    ∀ y ∈ Submission.Drive.unitBox 2, coreLoop Q t ≠ clampedSweep c ψ P y := by
  intro y hy heq
  have hmem : (1, y) ∈ meetBox (diamLoop Q t) (clampedSweep c ψ P) :=
    ⟨⟨zero_le_one, le_rfl⟩, hy, by rw [diamLoop_one_of_seam hQseam]; exact heq⟩
  exact absurd (h.2.1 (1, y) hmem).1.2 (lt_irrefl (1 : ℝ))


/-! ## 4. A smoothness bundle for loops (instance-free statements) -/

/-- **A `C^∞` loop of the capping space**, in the model-with-corners form.

This is a *definition* rather than an inline `ContMDiff` so that statements which need `C^∞`-regularity
of a loop can be written **without** referring to the (file-local) charted-space instances of
`CappingSpace`: those instances are `attribute [local instance]` in every file that uses them, so a
statement mentioning `ContMDiff` on `CappingSpace` cannot be elaborated where they are absent (for
instance in a standalone review/hand-off file). -/
def IsSmoothLoop (L : ℝ → CappingSpace) : Prop :=
  ContMDiff (modelWithCornersSelf ℝ ℝ)
    (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) L

/-- The unfolding of `IsSmoothLoop`, for consumers. -/
theorem isSmoothLoop_iff (L : ℝ → CappingSpace) :
    IsSmoothLoop L ↔ ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) L := Iff.rfl

/-- **The diameter loop of a smooth chart is a smooth loop.**  (`diamLoop Q θ σ = Q ((1−2σ) e^{iπθ})`;
this is the `IsSmoothLoop` instance needed to apply the sweep-side Sard
`Work.Drive.sgGoodChain_of_small_shift_sweep` at the design's *diameter* loops, whose loop is
`diamLoop (blockChart Ξ Q u τ k) q.1`.)  The argument is routed through `Work.Drive.polPt`
(`polPt_ofReal`), so that no syntactic matching of the coefficient's coercions is needed. -/
theorem isSmoothLoop_diamLoop {Q : ℂ → CappingSpace}
    (hQ : ContMDiff (modelWithCornersSelf ℝ ℂ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) Q) (θ : ℝ) :
    IsSmoothLoop (diamLoop Q θ) := by
  rw [IsSmoothLoop]
  have hg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun σ : ℝ => (((1 - 2 * σ : ℝ)) : ℂ)
        * Complex.exp (Real.pi * (θ : ℂ) * Complex.I)) := by
    refine (Complex.ofRealCLM.contDiff.comp ?_).mul contDiff_const
    exact contDiff_const.sub (contDiff_const.mul contDiff_id)
  have hEq : (fun σ : ℝ => (((1 - 2 * σ : ℝ)) : ℂ)
        * Complex.exp (Real.pi * (θ : ℂ) * Complex.I)) = fun σ : ℝ => polPt θ σ := by
    funext σ; exact polPt_ofReal θ σ
  have hg' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun σ : ℝ => polPt θ σ) := by
    simpa only [hEq] using hg
  have h := hQ.comp (contMDiff_iff_contDiff.mpr hg')
  have hfun : diamLoop Q θ = fun σ : ℝ => Q (polPt θ σ) := by
    funext σ; exact diamLoop_eq Q θ σ
  rw [hfun]
  simpa only [Function.comp_def] using h

/-! ## 5. A `ChartPert` needs at least as many parameters as the dimension -/

/-- **`ChartPert Q m Ξ` forces `4 ≤ m`**: the parameter-derivative at a point is a surjective linear
map `𝔼^m → ℝ⁴`, so the dimension of the source is at least `4`.  (In particular the general-`m`
statements of the germ lane are vacuous below `m = 4`; the concrete `Work.Drive.chartPert` has
`m = 4`.) -/
theorem four_le_of_chartPert {m : ℕ} {Q : ℂ → CappingSpace}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (hΞ : ChartPert Q m Ξ) :
    4 ≤ m := by
  have h := hΞ.2.2 0 (Q 0)
  have h2 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 4))
      ≤ Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) :=
    LinearMap.finrank_le_finrank_of_surjective
      (f := (mfderiv (𝓡 m) (𝓡 4)
        (fun t' : EuclideanSpace ℝ (Fin m) => Ξ t' (Q 0)) 0).toLinearMap) h
  simpa [finrank_euclideanSpace_fin] using h2

end

end Work.Drive
