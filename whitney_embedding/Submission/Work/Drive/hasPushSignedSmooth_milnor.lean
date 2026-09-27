import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Whitney.lct42_chain
import Submission.Work.Drive.PushDisc.pushAlgebra
import Submission.Work.Drive.Whitney.modelPush
import Submission.Work.Drive.Whitney.Frame
import Submission.Work.Drive.Whitney.modelChart2
import Submission.Work.Drive.Whitney.separation2
import Submission.Work.Drive.Whitney.modelChartCore
import Submission.Work.Drive.PushDisc.asymChart
import Submission.Work.Drive.PushDisc.windowChart
import Submission.Work.Drive.PushDisc.isWhitneyDisc
import Submission.Work.Drive.Whitney.whitneyDiscSmooth
import Submission.Work.Drive.PushDisc.lensWiringSolid

/-! Guidance from the project lead (the requester):

# Guidance (project lead) — hasPushSignedSmooth_milnor (the TEXTBOOK Whitney move: standard model + explicit isotopy)

`Work.Drive.HasPushSignedSmooth` is the ONE remaining input of the compact n ≥ 3 case; everything downstream is proved.
Two colleagues attack it by other routes and both report a piece with no plan: collar/slab one-sidedness, and a degree
theory for even spheres. Do NOT use slabs, fingers, base shears or degree theory. Follow Milnor, "Lectures on the
h-cobordism theorem", §6 (Whitney's lemma). In that proof ALL the difficulty is putting the configuration into a standard
model; the move in the model is one explicit formula.

THE MODEL. ℝ^{2n} = ℝ²_{(x,y)} × ℝ^{n-1}_u × ℝ^{n-1}_v.
- Sheet A = {(x, 0, u, 0)} (an n-plane).
- Sheet B = {(x, c(x), 0, v)}, where c : ℝ → ℝ is smooth with c(±1) = 0, c > 0 on (−1, 1) and c < 0 outside, transverse at ±1. So A ∩ B = {(±1, 0, 0, 0)}: two double points,
  with opposite signs by construction.
- Whitney disc D₀ = {(x, y, 0, 0) : |x| ≤ 1, 0 ≤ y ≤ c(x)}.
- The move: B₁ = {(x, c(x) − 2·μ(x)·λ(|v|), 0, v)}, with μ a bump that is ≥ max c on [−1, 1] and λ a bump with λ(0) = 1. At v = 0 the curve lies
  below the x-axis on [−1, 1], so there is no intersection with A (which needs y = 0 and v = 0). For v ≠ 0 there is none either, since A needs v = 0.
- The ambient version is ψ_t(x, y, u, v) = (x, y − 2t·μ(x)·λ(|v|)·κ(y, u), u, v), cut off by κ in (y, u) so that A is fixed.
  A is fixed because κ = 0 near {y = 0, |u| arbitrary}? No: A has y = 0. Choose the push to act only on points near B:
  multiply by a bump in the "distance to B" coordinate, or use the classical formula (Milnor 6.7: an isotopy of B supported
  near D₀ and extended to an ambient isotopy by the isotopy extension theorem). The repository has
  `Work.Isotopy.exists_smoothAmbientIsotopy_extending` (proved) in Submission/Work/Isotopy/.
Prove the MODEL statement first, in coordinates: the explicit ψ is a diffeo, the identity off a compact neighbourhood of D₀,
ψ(B ∩ nbhd) ∩ A = ∅, and the double points are removed. That is pure calculus.

PUTTING f INTO THE MODEL (the real work):
1. Whitney disc. The loop f∘γ₁ ∪ f∘γ₂ bounds a smooth embedded 2-disc D ⊂ ℝ^{2n} that meets f(M) only along the two
   arcs. General position works because 2 + n < 2n for n ≥ 3; ℝ^{2n} is simply connected; the Sard bricks are in Work/Projection.
   Make D meet the sheets orthogonally near its boundary.
2. Framing. The normal bundle of D is trivial (D is contractible). The prescribed boundary framing is: along γ₁, the
   directions tangent to sheet 1 (the u-directions); along γ₂, those tangent to sheet 2 (the v-directions). It extends over D iff a loop in
   O(2n−2) is null. The hypothesis `OppositeType` (Whitney/ArcFraming.lean) is exactly the sign condition that makes the
   corners compatible. The remaining ℤ/2 in π₁(O(2n−2)) can be killed by twisting the u-frame along γ₁ by a loop in
   SO(n−1): n − 1 ≥ 2, so π₁(SO(n−1)) → π₁(SO(2n−2)) is onto.
3. The tubular map Φ : nbhd(D₀) → nbhd(D), built from D and the framing (an exponential-type map), is a diffeo onto
   its image, sending A, B to f(sheet 1), f(sheet 2) near D. Adjust the sheets by a small isotopy so that they are
   EXACTLY the model planes near D.
4. ψ := Φ ∘ ψ_model ∘ Φ⁻¹ near D and the identity elsewhere. W₀ := f⁻¹(the part of sheet 2 near D). Verify the clauses of
   `HasAmbientPushData` (Whitney/PushDefs.lean l.493).
Proved bricks worth grepping: Work/Whitney/ArcFraming, PairDet, DoubleDetC, exists_tubular_param*, exists_bump_model_pair_smooth,
Work/Isotopy/*, Work/Drive/Push/* (tubeFlattening, smoothCollarTrivialisation: flattening a tube around γ₂ into an n-plane;
this is step 3 for one sheet). Delegate steps 1–4 and the model lemma as separate EXACT statements.
-/

namespace Work.Drive


/-- The double value of a clean pair has no third preimage.  Needed by every route to the target
statement (it turns the `W`-local cleanness into the global `hsep2` of the local push lemmas). -/
theorem preimage_double_eq {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ y : M)
    (hW₂ : p₂ ∈ W) (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁))
    (hy : f y = f p₂) : y = p₁ ∨ y = p₂ := by
  by_cases hyW : y ∈ W
  · rcases hclean y p₂ hyW hW₂ hy with h | h | h
    · exact Or.inr h
    · exact Or.inl h.1
    · exact Or.inr h.1
  · exact absurd hy.symm (hsep p₂ y hW₂ hyW)

/-- The same at the second crossing of the bigon. -/
theorem preimage_double_eq' {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (q₁ q₂ y : M)
    (hW₄ : q₂ ∈ W) (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = q₁ ∧ z = q₂) ∨ (y = q₂ ∧ z = q₁))
    (hy : f y = f q₂) : y = q₁ ∨ y = q₂ :=
  preimage_double_eq f W q₁ q₂ y hW₄ hsep hclean hy

/-- **Piece (a) of the local patch push: the containment of a small clean ball.**  The clean/sep
hypotheses inside `W` make the double value `f p₂` a value with exactly two preimages, so
`Work.Whitney.exists_radius_containment42` applies: a small ball around `f p₂` has its preimage
inside any prescribed pair of open neighbourhoods of `p₁`, `p₂`. -/
theorem exists_radius_containment_of_clean {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] (f : M → EuclideanSpace ℝ (Fin (2 * n))) (hf : Continuous f)
    (W : Set M) (p₁ p₂ : M) (hW₂ : p₂ ∈ W)
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁))
    (U₁ U₂ : Set M) (hU₁ : IsOpen U₁) (hU₂ : IsOpen U₂) (hp₁ : p₁ ∈ U₁) (hp₂ : p₂ ∈ U₂) :
    ∃ ε : ℝ, 0 < ε ∧ f ⁻¹' (Metric.ball (f p₂) ε) ⊆ U₁ ∪ U₂ :=
  Work.Whitney.exists_radius_containment42 f hf (f p₂) p₁ p₂
    (fun y hy => preimage_double_eq f W p₁ p₂ y hW₂ hsep hclean hy)
    U₁ U₂ hU₁ hU₂ hp₁ hp₂

/-- **Piece (c) of the local patch push, half 1 (`shearCollisionFar`), estimate-free.**

In the `Ξ`-coordinates of the model (`T` = the tangent plane of the `p₂`-branch, branch 2 =
`u ↦ (G₂ u, H₂ u)`, branch 1 = `x ↦ (G₁ x, H₁ x)`) the Milnor displacement has zero first
coordinate up to `‖δ‖ ≤ r₀` (the tilt window `λ < r₀/‖w‖` gives exactly this bound for the
tilted Milnor displacement, see §15), hence `‖first coord of the image‖ ≥ ‖G₂u‖ - r₀`.  Since
branch 1 lies in the set where that coordinate is `G₁ x` with `‖G₁ x‖ ≤ η`, every source with
`η < ‖G₂ u‖` is automatically off branch 1 — for *any* amplitude, with no estimate and no fold.
This is the "drop direction in which the partner branch is absent" (see §9 of
`Drive/NOTES_milnor_patch_route.md`); the remaining sources (`‖G₂u‖ ≤ η`, e.g. `η = R/100`) are the
quantitative half, where the second-coordinate mismatch with `H₁ x` does the work. -/
theorem shearCollisionFar {n : ℕ}
    (G₁ H₁ G₂ H₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (u x δ w : EuclideanSpace ℝ (Fin n)) (η r₀ : ℝ)
    (hr₀ : 0 < r₀) (hδ : ‖δ‖ ≤ r₀)
    (hη : η + r₀ < ‖G₂ u‖) (hx : ‖G₁ x‖ ≤ η) :
    (G₂ u, H₂ u) + (δ, w) ≠ (G₁ x, H₁ x) := by
  intro h
  have h1 : G₂ u + δ = G₁ x := by
    simpa using congrArg Prod.fst h
  have h3 : ‖G₂ u‖ ≤ ‖G₁ x‖ + ‖δ‖ := by
    have h4 : G₂ u = G₁ x - δ := by rw [← h1]; abel
    rw [h4]
    exact norm_sub_le _ _
  linarith

/-- **Piece (c) of the local patch push, near case (`shearCollisionNear`): the order-theoretic core,
phrased against the proved bricks of `Drive/PushDisc/pushAlgebra.lean`** (both reviewers:
"looks correct as stated"; `Drive/NOTES_milnor_patch_route.md` §10–§11).

With the *tilted* Milnor displacement `w` and the forbidden bullet `{⟪·,w⟫ ≤ 0} ∪ B(0,r₀)`, a pushed
source with cut-off `χ` that is either a sheet-one source outside the bullet (`0 < χ`,
`0 < ⟪z,w⟫`, `r₀ < ‖z‖`) or a sheet-two source of the *plateau* (`χ = 1`, `‖z‖ < ‖w‖ - r₀`, the one
place the amplitude hypothesis `χ = 1` is needed) is carried outside the bullet.

Far-case companion: `Work.Drive.shearCollisionFar` above (no estimates).  The geometric content
(that the sheet-two sources of the support lie in the plateau, and `λ ≠ 0` so that `w` is not
tangential to the `p₁`-branch) is deliberately *not* part of this statement; `λ = 0` must not be
assumed (`PushDisc/perpendicular_counterexample.lean`). -/
theorem shearCollisionNear {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (z w : E) (χ r₀ : ℝ) (hr₀ : 0 < r₀) (hr : r₀ < ‖w‖)
    (hcase : (0 < χ ∧ 0 < inner ℝ z w ∧ r₀ < ‖z‖) ∨ (χ = 1 ∧ ‖z‖ < ‖w‖ - r₀)) :
    0 < inner ℝ (z + χ • w) w ∧ r₀ < ‖z + χ • w‖ := by
  rcases hcase with ⟨hχ, hz, hrz⟩ | ⟨hχ1, hz⟩
  · exact Work.Drive.PushDisc.sheet_one_clause z w χ r₀ hχ hz hr₀ hrz
  · rw [hχ1, one_smul]
    exact ⟨(Work.Drive.PushDisc.sheet_two_clause z w r₀ hr₀ hz).2,
      (Work.Drive.PushDisc.sheet_two_clause z w r₀ hr₀ hz).1⟩

/-- **The caller `shearSourceRegion`, far-branch discharge** (§12/§15 of
`Drive/NOTES_milnor_patch_route.md`): with the model data of `Work.Drive.PushPatch.chartBranchModel`
(the branch parametrisations `F₁`, `F₂` and the radius `Δ`, here `η`), a source `v` whose first
`Ξ`-coordinate exceeds `η + r₀` is carried off branch 1 by the *tilted* Milnor displacement
`(δ, w)` — an immediate instantiation of `Work.Drive.shearCollisionFar` above, with no estimates.
The near branch (sources with `‖(F₂ v).1‖ ≤ η + r₀`) is the other half: `χ (F₂ v) = 1` from
`Work.Drive.PushPatch.capsuleAmplitude`'s plateau clause together with the single
`‖F₂ v‖ ≤ c + O(ε) < ‖w‖ - r₀` estimate. -/
theorem shearSourceRegion_far {n : ℕ}
    (F₁ F₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    (v x : EuclideanSpace ℝ (Fin n)) (δ w : EuclideanSpace ℝ (Fin n)) (η r₀ : ℝ)
    (hr₀ : 0 < r₀) (hδ : ‖δ‖ ≤ r₀)
    (hfar : η + r₀ < ‖(F₂ v).1‖) (hx : ‖(F₁ x).1‖ ≤ η) :
    F₂ v + (δ, w) ≠ F₁ x := by
  simpa using shearCollisionFar (fun y => (F₁ y).1) (fun y => (F₁ y).2)
    (fun y => (F₂ y).1) (fun y => (F₂ y).2) v x δ w η r₀ hr₀ hδ hfar hx

/-- **The caller `shearSourceRegion`, near-branch discharge** (§12/§14/§15 of
`Drive/NOTES_milnor_patch_route.md`): with the amplitude clauses of
`Work.Drive.PushPatch.capsuleAmplitude` — the *unconditional* plateau (P) and the source bound (B) —
and the scale order `c < ε < r₀`, `r₀ + ε < ‖w‖`, every source of branch 2 inside the parameter ball
that is moved at all has `χ (g₂ v) = 1` and `‖g₂ v‖ < ‖w‖ - r₀`.  The second inequality needs **no**
thinness estimate: (B) gives `‖g₂ v‖ ≤ c < ε < r₀ < ‖w‖ - r₀`, which is the whole content of the
`‖g₂ v‖ ≤ c + O(ε) < ‖w‖ - r₀` bound that §14 recorded as the near branch's only obligation.  With
this, the two halves of the caller are both in the repository. -/
theorem shearSourceRegion_near {n : ℕ}
    (g₂ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin (2 * n)))
    (χ : EuclideanSpace ℝ (Fin (2 * n)) → ℝ) (w : EuclideanSpace ℝ (Fin (2 * n)))
    (c ε r₀ : ℝ) (hε : 0 < ε) (hεr : ε < r₀) (hr₀w : r₀ + ε < ‖w‖) (hcε : c < ε)
    (hP : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ ≤ 1 → χ (g₂ v) ≠ 0 → χ (g₂ v) = 1)
    (hB : ∀ v : EuclideanSpace ℝ (Fin n), ‖v‖ ≤ 1 → χ (g₂ v) ≠ 0 → ‖g₂ v‖ ≤ c)
    (v : EuclideanSpace ℝ (Fin n)) (hv : ‖v‖ ≤ 1) (hne : χ (g₂ v) ≠ 0) :
    χ (g₂ v) = 1 ∧ ‖g₂ v‖ < ‖w‖ - r₀ := by
  refine ⟨hP v hv hne, ?_⟩
  have h1 : ‖g₂ v‖ ≤ c := hB v hv hne
  linarith


/-!
## ROUTE (session 2026-09-24, revised on the project lead's directive)

This file no longer depends on `Work.Drive.hasPushSignedSmooth`, nor on anything under
`Submission/Work/Whitney/CutPush/` or `Submission/Work/Drive/Slab/`.  That chain is a *colleague's
open* slab/finger route, and, as the lead observed, an interface which never consumes the arc
hypotheses (`hγend`) or the framing hypothesis (`OppositeType`) cannot be the Whitney move at all:
a pair of double points of the *same* sign can never be cancelled, so a sound statement must spend
the sign.  The route of this file is the textbook one (Milnor, *Lectures on the h-cobordism
theorem*, §6), split into five exact statements, each proved in its own module under
`Submission/Work/Drive/Whitney/`:

* **M1** `Work.Drive.Whitney.modelPush` (`Drive/Whitney/modelPush.lean`) — DELEGATED this session —
  the MODEL move, pure calculus.  In the coordinates `ℝ^{2n} = ℝ²_{(x,y)} × ℝ^{n-1}_u × ℝ^{n-1}_v` with the model sheets
  `A = {(x, 0, u, 0)}` and `B = {(x, c x, 0, v)}` (where `c` vanishes exactly at `±1`, is positive on
  `(-1,1)`, negative outside, and is transverse at `±1`), the explicit vertical shear
  `ψ (x,y,u,v) = (x, y - 2 m x * l ‖v‖, u, v)` — with `m` a bump `= 1` on `[-1,1]`, `0` off
  `(-3/2,3/2)`, and `l` a bump with `l 0 = 1`, `l = 0` off `[0,1)` — is a `C^∞` diffeomorphism with
  the explicit inverse `σ (x,y,u,v) = (x, y + 2 m x * l ‖v‖, u, v)`, fixes `{m = 0} ∪ {l = 0}`,
  acts on `B` by `(x, c x, 0, v) ↦ (x, c x - 2 m x * l ‖v‖, 0, v)`, and carries the *moved* part of
  `B` off `A ∪ B`.  (`A` requires `v = 0`, where the moved height is `c x - 2 m x < 0`; this is the
  "drop direction in which the partner branch is absent" — and it is precisely why a shear in base
  coordinates for which *both* sheets are graphs is obstructed (see
  `Submission/Work/Drive/NOTES_milnor_model_route.md` §3), while the model's coordinates are not of
  that shape.)
* **M2** `Work.Drive.Whitney.exists_whitneyDisc` — DELEGATED this session — the loop `f ∘ γ₁ ∪ f ∘ γ₂` bounds an embedded
  topological/smooth `2`-disc `D ⊂ ℝ^{2n}` meeting `f '' M` only along the two arcs (general
  position; `2 + n < 2n`, i.e. `n ≥ 3`).
* **M3** `Work.Drive.Whitney.exists_framingExtension` — the boundary framing of `D` (the sheet
  directions along `γ₁`, resp. `γ₂`) extends over `D`; this is where `OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂`
  is spent (the loop in `SO(2n-2)` is null exactly under the opposite-sign condition).
* **M4** `Work.Drive.Whitney.exists_modelChart` — a tubular map `Φ` from a neighbourhood of `D` to
  the model of M1, carrying the two sheet germs at `(p₁,p₂)` and `(q₁,q₂)` to the model sheets `A`,
  `B` and the two arcs to the model arcs.
* **M5** `Work.Drive.Whitney.hasAmbientPushData_of_modelData` — the assembly: the conjugate of M1's
  `ψ` by `Φ` (and its extension by the identity) has all the clauses of
  `Work.Whitney.HasAmbientPushData f W p₁ p₂ q₁ q₂`.

The target theorem at the bottom is then the one-line consequence of M2–M5 (the route actually
completed: the lens assembly of `Work.Drive.PushDisc`).
-/


/-- Auxiliary case analysis, first arc: a point `y` with `f y` equal to the value of the first
bigon arc at a parameter `s` lies on one of the two bigon arcs. -/
theorem mem_arcs_of_f_eq_arc₁ {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (γ₁ γ₂ : ℝ → M)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    {y : M} {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (hys : f (γ₁ s) = f y) :
    y ∈ γ₁ '' Set.Icc (0 : ℝ) 1 ∪ γ₂ '' Set.Icc (0 : ℝ) 1 := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  have hzsW : γ₁ s ∈ W := hγW₁ s hs
  by_cases hyW : y ∈ W
  · rcases hclean (γ₁ s) y hzsW hyW hys with h | h | h | h | h
    · exact Or.inl ⟨s, hs, h⟩
    · exact Or.inr ⟨0, h0, by rw [hγ₂0]; exact h.2.symm⟩
    · exact Or.inl ⟨0, h0, by rw [hγ₁0]; exact h.2.symm⟩
    · exact Or.inr ⟨1, h1, by rw [hγ₂1]; exact h.2.symm⟩
    · exact Or.inl ⟨1, h1, by rw [hγ₁1]; exact h.2.symm⟩
  · exact absurd hys (hsep (γ₁ s) y hzsW hyW)

/-- Auxiliary case analysis, second arc. -/
theorem mem_arcs_of_f_eq_arc₂ {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (γ₁ γ₂ : ℝ → M)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    {y : M} {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) (hys : f (γ₂ s) = f y) :
    y ∈ γ₁ '' Set.Icc (0 : ℝ) 1 ∪ γ₂ '' Set.Icc (0 : ℝ) 1 := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  have hzsW : γ₂ s ∈ W := hγW₂ s hs
  by_cases hyW : y ∈ W
  · rcases hclean (γ₂ s) y hzsW hyW hys with h | h | h | h | h
    · exact Or.inr ⟨s, hs, h⟩
    · exact Or.inr ⟨0, h0, by rw [hγ₂0]; exact h.2.symm⟩
    · exact Or.inl ⟨0, h0, by rw [hγ₁0]; exact h.2.symm⟩
    · exact Or.inr ⟨1, h1, by rw [hγ₂1]; exact h.2.symm⟩
    · exact Or.inl ⟨1, h1, by rw [hγ₁1]; exact h.2.symm⟩
  · exact absurd hys (hsep (γ₂ s) y hzsW hyW)

/-- **The preimage of the bigon loop is the loop.**  A point of `M` whose `f`-value is the value of
one of the two bigon arcs lies on one of the two arcs.  (The four double points are on the arcs by
`hγ₁0`, `hγ₁1`, `hγ₂0`, `hγ₂1`, so the two partners of each end are covered.)  This is the
cleanliness statement underlying the *isolation* condition (`hsheets`) of the model chart: the only
part of `f '' M` near the loop is the loop itself, i.e. the two sheets. -/
theorem mem_arcs_of_f_mem_loop {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M) (γ₁ γ₂ : ℝ → M)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    {y : M} (hy : f y ∈ f '' (γ₁ '' Set.Icc (0 : ℝ) 1) ∪ f '' (γ₂ '' Set.Icc (0 : ℝ) 1)) :
    y ∈ γ₁ '' Set.Icc (0 : ℝ) 1 ∪ γ₂ '' Set.Icc (0 : ℝ) 1 := by
  rcases hy with ⟨x, ⟨s, hs, rfl⟩, hxy⟩ | ⟨x, ⟨s, hs, rfl⟩, hxy⟩
  · exact mem_arcs_of_f_eq_arc₁ f W p₁ p₂ q₁ q₂ γ₁ γ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1 hγW₁ hγW₂
      hclean hsep hs hxy
  · exact mem_arcs_of_f_eq_arc₂ f W p₁ p₂ q₁ q₂ γ₁ γ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1 hγW₁ hγW₂
      hclean hsep hs hxy

/-- **The isolation tube around a compactum in a compact space.**  If every point of `M` mapped onto
`f '' L` already lies in `S₁ ∪ S₂`, then the set `U` of points of `ℝ^{2n}` whose preimage lies in
`S₁ ∪ S₂` (the complement of the image of `(S₁ ∪ S₂)ᶜ`) is open, contains `f '' L`, and is exactly
what the `hsheets` clause of the model chart needs: everything of `f '' M` inside `U` comes from the
two sheets. -/
theorem exists_open_tube_of_preimage {n : ℕ} {M : Type*} [TopologicalSpace M] [CompactSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (hf : Continuous f)
    (L S₁ S₂ : Set M) (hS₁ : IsOpen S₁) (hS₂ : IsOpen S₂)
    (hpre : ∀ y : M, f y ∈ f '' L → y ∈ S₁ ∪ S₂) :
    ∃ U : Set (EuclideanSpace ℝ (Fin (2 * n))),
      IsOpen U ∧ f '' L ⊆ U ∧ f ⁻¹' U ⊆ S₁ ∪ S₂ := by
  let C : Set M := (S₁ ∪ S₂)ᶜ
  have hCclosed : IsClosed C := (hS₁.union hS₂).isClosed_compl
  have hCcpt : IsCompact C := hCclosed.isCompact
  have hKcpt : IsCompact (f '' C) := hCcpt.image hf
  have hKclosed : IsClosed (f '' C) := hKcpt.isClosed
  refine ⟨(f '' C)ᶜ, hKclosed.isOpen_compl, ?_, ?_⟩
  · intro z hz
    simp only [Set.mem_compl_iff]
    rintro ⟨b, hbC, hbz⟩
    obtain ⟨a, haL, rfl⟩ := hz
    exact hbC (hpre b ⟨a, haL, hbz.symm⟩)
  · intro y hy
    by_contra hyS
    exact hy ⟨y, hyS, rfl⟩

/-- **The isolation tube for the bigon.**  The two arcs are contained in the open sets `S₁`, `S₂`;
then there is an open set `U ⊆ ℝ^{2n}` containing both arcs' images such that every point of `M`
mapping into `U` lies in `S₁ ∪ S₂`.  This is the `hsheets` clause of the model chart
(`Work.Drive.Whitney.ModelChartData`) in the exact hypotheses of the target: the model slab will be
a subset of `U`, so the only pieces of `f '' M` inside it are the two sheets. -/
theorem exists_isolation_tube_of_clean {n : ℕ} {M : Type*} [TopologicalSpace M] [CompactSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (hf : Continuous f) (W : Set M)
    (p₁ p₂ q₁ q₂ : M) (γ₁ γ₂ : ℝ → M)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (S₁ S₂ : Set M) (hS₁ : IsOpen S₁) (hS₂ : IsOpen S₂)
    (hγ₁S : γ₁ '' Set.Icc (0 : ℝ) 1 ⊆ S₁) (hγ₂S : γ₂ '' Set.Icc (0 : ℝ) 1 ⊆ S₂) :
    ∃ U : Set (EuclideanSpace ℝ (Fin (2 * n))), IsOpen U ∧
      f '' (γ₁ '' Set.Icc (0 : ℝ) 1) ⊆ U ∧ f '' (γ₂ '' Set.Icc (0 : ℝ) 1) ⊆ U ∧
      f ⁻¹' U ⊆ S₁ ∪ S₂ := by
  obtain ⟨U, hUo, hUL, hUpre⟩ := exists_open_tube_of_preimage f hf
    (γ₁ '' Set.Icc (0 : ℝ) 1 ∪ γ₂ '' Set.Icc (0 : ℝ) 1) S₁ S₂ hS₁ hS₂ (by
      intro y hy
      rw [Set.image_union] at hy
      rcases mem_arcs_of_f_mem_loop f W p₁ p₂ q₁ q₂ γ₁ γ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1 hγW₁ hγW₂
        hclean hsep hy with h | h
      · exact Or.inl (hγ₁S h)
      · exact Or.inr (hγ₂S h))
  exact ⟨U, hUo, fun z hz => hUL (Set.image_mono Set.subset_union_left hz),
    fun z hz => hUL (Set.image_mono Set.subset_union_right hz), hUpre⟩


/-- **Why a *single* crossing cannot be pushed: the IVT guard.**

In the model coordinates `ℝ^{2n} = ℝ²_{(x,y)} × ℝ^{n-1}_u × ℝ^{n-1}_v`, take `A = {y = 0, v = 0}` and
`B = {u = 0, y = c x}`.  A push of `B` off `A` supported in `|x| ≤ 1` must produce a continuous
amplitude `g = φ(·, 0)` with `g (± 1) = 0` and `g x ≠ c x` for `|x| ≤ 1` (otherwise the moved point
`(x, c x - g x, 0, 0)` of `B` lies on `A`).  If the height `c` has *opposite* signs at the two ends of
the support -- which is what a **single** transversal crossing between them forces -- then the
intermediate value theorem gives a solution of `g x = c x`, so no such push exists.  This is the
reason every "local push at one double point" route (the patch route of
`Drive/NOTES_milnor_patch_route.md`, `Work.Whitney.local_push_data_hloc`, the slab/finger routes) is
dead, and it is why the *two*-crossing model of M1 (`c (± 1) = 0`, `c` of one sign outside `[-1,1]`)
is the only shape in which the shear can work: there `g (-1) - c (-1)` and `g 1 - c 1` have the *same*
sign and no obstruction is forced. -/
theorem no_push_across_single_crossing {c g : ℝ → ℝ} (hc : Continuous c) (hg : Continuous g)
    (hg0 : ∀ x : ℝ, 1 ≤ |x| → g x = 0) (hcneg : c (-1) > 0) (hcpos : c 1 < 0) :
    ∃ x : ℝ, |x| ≤ 1 ∧ g x = c x := by
  have hmem1 : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_refl _, by norm_num⟩
  have hmem2 : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, le_refl _⟩
  have hgneg : (g - c) (-1) < 0 := by
    have : g (-1) = 0 := hg0 (-1) (by norm_num [abs_neg])
    simp only [Pi.sub_apply, this]; linarith
  have hgpos : 0 < (g - c) 1 := by
    have : g 1 = 0 := hg0 1 (by norm_num)
    simp only [Pi.sub_apply, this]; linarith
  have hsub := intermediate_value_Icc (a := (-1 : ℝ)) (b := 1) (by norm_num)
    (hg.continuousOn.sub hc.continuousOn)
  obtain ⟨x, hx, hx0⟩ := hsub ⟨le_of_lt hgneg, le_of_lt hgpos⟩
  refine ⟨x, ?_, ?_⟩
  · rw [abs_le]; exact ⟨hx.1, hx.2⟩
  · have : g x - c x = 0 := hx0
    linarith

/-- `γ₁ t` is not one of the *other* arc's endpoints, for `t ∈ [0,1]`. -/
theorem arc₁_ne_partner {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (p₁ p₂ q₁ q₂ : M) (γ₁ γ₂ : ℝ → M)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hp₁p₂ : p₁ ≠ p₂) (hp₂q₁ : p₂ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂) (hq₁q₂ : q₁ ≠ q₂)
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : γ₁ t ≠ p₂ ∧ γ₁ t ≠ q₂ := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  constructor
  · intro hcon
    have := hγend t ht 0 h0 (by rw [hγ₂0, ← hcon])
    rcases this with ⟨h, -⟩ | ⟨-, h⟩
    · rw [h, hγ₁0] at hcon; exact hp₁p₂ hcon
    · norm_num at h
  · intro hcon
    have := hγend t ht 1 h1 (by rw [hγ₂1, ← hcon])
    rcases this with ⟨-, h⟩ | ⟨h, -⟩
    · norm_num at h
    · rw [h, hγ₁1] at hcon; exact hq₁q₂ hcon

/-- **Faithfulness of `f` on an isolated tube around the first arc**: a point of the tube whose
`f`-value is the value of the first arc *is* the corresponding arc point. -/
theorem f_eq_arc₁_of_mem_of_f_eq {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M) (γ₁ γ₂ : ℝ → M)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hp₁p₂ : p₁ ≠ p₂) (hp₂q₁ : p₂ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂) (hq₁q₂ : q₁ ≠ q₂)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (S : Set M) (hS₂ : p₂ ∉ S) (hS₄ : q₂ ∉ S)
    {y : M} (hy : y ∈ S) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hf : f y = f (γ₁ t)) : y = γ₁ t := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  -- the arc point is not one of the other arc's endpoints
  have hne_t := arc₁_ne_partner f p₁ p₂ q₁ q₂ γ₁ γ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1 hp₁p₂ hp₂q₁ hp₁q₂
    hq₁q₂ hγend ht
  -- the value is a value of the loop, so `y` is on one of the arcs
  have hval : f y ∈ f '' (γ₁ '' Set.Icc (0 : ℝ) 1) ∪ f '' (γ₂ '' Set.Icc (0 : ℝ) 1) := by
    rw [hf]
    exact Or.inl (Set.mem_image_of_mem f (Set.mem_image_of_mem γ₁ ht))
  rcases mem_arcs_of_f_mem_loop f W p₁ p₂ q₁ q₂ γ₁ γ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1 hγW₁ hγW₂ hclean hsep
    hval with ⟨s, hs, hys⟩ | ⟨s, hs, hys⟩
  · -- `y` is on the first arc: compare the two arc parameters
    have hyW : y ∈ W := hys ▸ hγW₁ s hs
    have hEq : f (γ₁ s) = f (γ₁ t) := by rw [hys]; exact hf
    have hne_s := arc₁_ne_partner f p₁ p₂ q₁ q₂ γ₁ γ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1 hp₁p₂ hp₂q₁ hp₁q₂
      hq₁q₂ hγend hs
    rcases hclean (γ₁ s) (γ₁ t) (hγW₁ s hs) (hγW₁ t ht) hEq with h | h | h | h | h
    · rw [← hys, h]
    · exact absurd h.2 hne_t.1
    · exact absurd h.1 hne_s.1
    · exact absurd h.2 hne_t.2
    · exact absurd h.1 hne_s.2
  · -- `y` is on the second arc: then it is one of the two double points, contradicting `S`
    have hEq : f (γ₂ s) = f (γ₁ t) := by rw [hys]; exact hf
    rcases hγend t ht s hs hEq.symm with ⟨ht0, hs0⟩ | ⟨ht1, hs1⟩
    · have hyp : y = p₂ := hys.symm.trans (by rw [hs0, hγ₂0])
      exact (hS₂ (hyp ▸ hy)).elim
    · have hyp : y = q₂ := hys.symm.trans (by rw [hs1, hγ₂1])
      exact (hS₄ (hyp ▸ hy)).elim


/-- The mirror of `Work.Drive.arc₁_ne_partner`: the second arc never passes through `p₁` or `q₁`. -/
theorem arc₂_ne_partner {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (p₁ p₂ q₁ q₂ : M) (γ₁ γ₂ : ℝ → M)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hp₁p₂ : p₁ ≠ p₂) (hp₂q₁ : p₂ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂) (hq₁q₂ : q₁ ≠ q₂)
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : γ₂ t ≠ p₁ ∧ γ₂ t ≠ q₁ := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  constructor
  · intro hcon
    have := hγend 0 h0 t ht (by rw [hγ₁0, ← hcon])
    rcases this with ⟨-, h⟩ | ⟨h, -⟩
    · rw [h, hγ₂0] at hcon; exact hp₁p₂ hcon.symm
    · norm_num at h
  · intro hcon
    have := hγend 1 h1 t ht (by rw [hγ₁1, ← hcon])
    rcases this with ⟨h, -⟩ | ⟨-, h⟩
    · norm_num at h
    · rw [h, hγ₂1] at hcon; exact hq₁q₂ hcon.symm

/-- **Faithfulness of `f` on an isolated tube around the second arc** (the mirror of
`Work.Drive.f_eq_arc₁_of_mem_of_f_eq`): a point of a set avoiding `p₁` and `q₁` whose `f`-value is the
value of the second arc *is* the corresponding arc point. -/
theorem f_eq_arc₂_of_mem_of_f_eq {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M) (γ₁ γ₂ : ℝ → M)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hp₁p₂ : p₁ ≠ p₂) (hp₂q₁ : p₂ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂) (hq₁q₂ : q₁ ≠ q₂)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (S : Set M) (hS₁ : p₁ ∉ S) (hS₃ : q₁ ∉ S)
    {y : M} (hy : y ∈ S) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hf : f y = f (γ₂ t)) : y = γ₂ t := by
  have hne_t := arc₂_ne_partner f p₁ p₂ q₁ q₂ γ₁ γ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1 hp₁p₂ hp₂q₁ hp₁q₂
    hq₁q₂ hγend ht
  have hval : f y ∈ f '' (γ₁ '' Set.Icc (0 : ℝ) 1) ∪ f '' (γ₂ '' Set.Icc (0 : ℝ) 1) := by
    rw [hf]
    exact Or.inr (Set.mem_image_of_mem f (Set.mem_image_of_mem γ₂ ht))
  rcases mem_arcs_of_f_mem_loop f W p₁ p₂ q₁ q₂ γ₁ γ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1 hγW₁ hγW₂ hclean hsep
    hval with ⟨s, hs, hys⟩ | ⟨s, hs, hys⟩
  · have hEq : f (γ₁ s) = f (γ₂ t) := by rw [hys]; exact hf
    rcases hγend s hs t ht hEq with ⟨hs0, -⟩ | ⟨hs1, -⟩
    · have hyp : y = p₁ := hys.symm.trans (by rw [hs0, hγ₁0])
      exact (hS₁ (hyp ▸ hy)).elim
    · have hyp : y = q₁ := hys.symm.trans (by rw [hs1, hγ₁1])
      exact (hS₃ (hyp ▸ hy)).elim
  · have hEq : f (γ₂ s) = f (γ₂ t) := by rw [hys]; exact hf
    have hne_s := arc₂_ne_partner f p₁ p₂ q₁ q₂ γ₁ γ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1 hp₁p₂ hp₂q₁ hp₁q₂
      hq₁q₂ hγend hs
    rcases hclean (γ₂ s) (γ₂ t) (hγW₂ s hs) (hγW₂ t ht) hEq with h | h | h | h | h
    · rw [← hys, h]
    · exact absurd h.1 hne_s.1
    · exact absurd h.2 hne_t.1
    · exact absurd h.1 hne_s.2
    · exact absurd h.2 hne_t.2

/-!
## The state of the route (session of the MARK II interface)

The earlier interfaces of the model chart (`Work.Drive.Whitney.ModelChartData`,
`SheetChartAll`, `SheetSetupAll`, `SheetRawAll`) carried the **global isolation clause**

    hs : ∀ ξ, |ξ.1| < 3/2 → ‖ξ.2.2.2‖ < 1 → Θ ξ ∈ f '' M → ξ ∈ sheetA ∪ sheetB c

and that clause is **FALSE** — it forces the base map `y ↦ ((Φ (f y)).1, (Φ (f y)).2.2.2)` to have
exactly one preimage over the punctured slab, which is impossible for a smooth map from a closed
`n`-manifold to `ℝ^n` (the counting half is proved in `Drive/Whitney/sheetSetupAll.lean`; see
`Drive/Whitney/NOTES_sheetSetupAll_S3_TARGET_FALSE.md`).  Nothing downstream of it can be used.

The repaired interface is `Work.Drive.Whitney.ModelChartData2`
(`Drive/Whitney/modelChart2.lean`): the model shear there is the *`u`-shear*
`ψ (x,y,u,v) = (x, y, u - b x * l (‖v‖²), v)` of small amplitude `‖b‖ < δ`, and the isolation is
replaced by the *separation* clause of the two compact patches, which is **automatic**:

* `Work.Drive.Whitney.hasAmbientPushData_of_modelChartData2` — the assembly: `ModelChartData2`
  ⟹ `Work.Whitney.HasAmbientPushData` (proved, axiom-clean);
* `Work.Drive.Whitney.exists_separation` (`Drive/Whitney/separation2.lean`) — the separation clause
  `hsepδ` of `ModelChartData2` is *provable* from the rest of the data (compactness + `hclean`).

So the single remaining geometric obligation is the **two-sheet normal form along the bigon**:
`Work.Drive.Whitney.ModelChartDataAll2`, i.e. the existence of the chart in which one tube is a thin
piece of the plane `sheetA` and the other tube is the graph `{(x, c x, 0, v)}` — the classical
"Milnor §6" straightening.  Everything else in the interface is bookkeeping (`ε` and `b` are free
bumps, `δ` is `exists_separation`, the `Oo`/frontier clause is
`Work.Drive.Whitney.modelChartOo_of_t2`).
-/

/-- **The target from the corrected geometric input.** -/
theorem hasPushSignedSmooth_milnor_of_modelChartDataAll2 {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (h : Work.Drive.Whitney.ModelChartDataAll2 n M) :
    Work.Drive.HasPushSignedSmooth n M :=
  Work.Drive.Whitney.hasPushSignedSmooth_of_modelChartDataAll2 h

/-- **The target from the core (sharpest) geometric input.**  `ModelChartCoreAll` is the two-sheet
normal form plus the single numeric clause `hsepε`; everything else (the model shear, the amplitude,
the separation, the frontier clause) is proved in `Drive/Whitney/modelChart2.lean`,
`Drive/Whitney/modelChartCore.lean` and `Drive/Whitney/separation2.lean`. -/
theorem hasPushSignedSmooth_milnor_of_modelChartCoreAll {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (h : Work.Drive.Whitney.ModelChartCoreAll n M) :
    Work.Drive.HasPushSignedSmooth n M :=
  Work.Drive.Whitney.hasPushSignedSmooth_of_modelChartCoreAll h

/-- **The target from the one-sided normal form** (the *asymmetric* route, `Drive/PushDisc`): the
whole compact `n ≥ 3` case follows from the existence of the model chart in which only the *first*
sheet is straightened (`Work.Drive.PushDisc.AsymChartAll`).  This is the live route: the tangent-plane
alignment `(O2')` is available from the tiny brick (`Work.Drive.PushDisc.TinyRegime`) by
`Work.Drive.PushDisc.arcRangeAlignmentCore_of_tiny_solid` (`Drive/PushDisc/arcRangeAssembly.lean`,
proved, axiom-clean), so `AsymChartAll` is the single remaining geometric input. -/
theorem hasPushSignedSmooth_milnor_of_asymChartAll {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (h : Work.Drive.PushDisc.AsymChartAll n M) :
    Work.Drive.HasPushSignedSmooth n M :=
  Work.Drive.PushDisc.hasPushSignedSmooth_of_asymChartAll h

/-- **The target from the WINDOWED chart data of the Whitney disc** (the interface of the current
route; project lead's message of 2026-09-25, 13:00): producing
`Work.Drive.PushDisc.WhitneyChartWindowData` for *every* configuration of the target — i.e. the
general-position construction of the Whitney disc (`exists_whitneyDisc`) together with its framing
(`whitneyChart_of_disc`, where `OppositeType` is spent) — gives the target.

The bridge to the one-sided normal form is the *proved*
`Work.Drive.PushDisc.asymChartAll_of_windowChartAll`, whose core is the *proved*
`Work.Drive.PushDisc.nonempty_asymChartData_of_windowData` (`windowChart.lean`, axiom-clean: the
windowed interface is the non-vacuous repair of the empty global-`σ₁` `WhitneyChartData`).  So the
whole remaining content of the compact `n ≥ 3` case is the *geometric* statement
`Work.Drive.PushDisc.WhitneyChartWindowAll`. -/
theorem hasPushSignedSmooth_milnor_of_windowChartAll {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (h : Work.Drive.PushDisc.WhitneyChartWindowAll n M) :
    Work.Drive.HasPushSignedSmooth n M :=
  hasPushSignedSmooth_milnor_of_asymChartAll (Work.Drive.PushDisc.asymChartAll_of_windowChartAll h)

/-- **The first arc's image is injective** (`f` is injective along `γ₁`): the hypothesis
`hγ₁injf` of `Work.Drive.Whitney.whitneyDiscSmooth` (the Whitney disc) is *free* from the bigon
data.  The only pairs of `f`-equal points of `W` involving the arc are the `(p₁,p₂)` and `(q₁,q₂)`
pairs, and `p₂, q₂` are not on the first arc (`hγdisj`). -/
theorem arc_image_injOn₁ {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M) (γ₁ γ₂ : ℝ → M)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hp₁p₂ : p₁ ≠ p₂) (hp₂q₁ : p₂ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂) (hq₁q₂ : q₁ ≠ q₂)
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    Set.InjOn (fun s : ℝ => f (γ₁ s)) (Set.Icc (0 : ℝ) 1) := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  -- `p₂` and `q₂` are not on the first arc
  have hp₂ : p₂ ∉ γ₁ '' Set.Icc (0 : ℝ) 1 := by
    rintro ⟨u, hu, hup⟩
    have hzu : γ₁ u = γ₂ 0 := by rw [hup, hγ₂0]
    rcases hγdisj u hu 0 h0 hzu with ⟨hu0, -⟩ | ⟨hu1, h⟩
    · rw [hu0, hγ₁0] at hup; exact hp₁p₂ hup
    · norm_num at h
  have hq₂ : q₂ ∉ γ₁ '' Set.Icc (0 : ℝ) 1 := by
    rintro ⟨u, hu, hup⟩
    have hzu : γ₁ u = γ₂ 1 := by rw [hup, hγ₂1]
    rcases hγdisj u hu 1 h1 hzu with ⟨hu0, h⟩ | ⟨hu1, -⟩
    · norm_num at h
    · rw [hu1, hγ₁1] at hup; exact hq₁q₂ hup
  intro s hs t ht hst
  rcases hclean (γ₁ s) (γ₁ t) (hγW₁ s hs) (hγW₁ t ht) hst with h | h | h | h | h
  · exact hγ₁inj hs ht h
  · exact absurd ⟨t, ht, h.2⟩ hp₂
  · exact absurd ⟨s, hs, h.1⟩ hp₂
  · exact absurd ⟨t, ht, h.2⟩ hq₂
  · exact absurd ⟨s, hs, h.1⟩ hq₂

/-- **The second arc's image is injective** (the mirror of `Work.Drive.arc_image_injOn₁`). -/
theorem arc_image_injOn₂ {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M) (γ₁ γ₂ : ℝ → M)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hp₁p₂ : p₁ ≠ p₂) (hp₂q₁ : p₂ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂) (hq₁q₂ : q₁ ≠ q₂)
    (hγ₂inj : Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1))
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    Set.InjOn (fun s : ℝ => f (γ₂ s)) (Set.Icc (0 : ℝ) 1) := by
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  have hp₁ : p₁ ∉ γ₂ '' Set.Icc (0 : ℝ) 1 := by
    rintro ⟨u, hu, hup⟩
    have hzu : γ₁ 0 = γ₂ u := by rw [hup, hγ₁0]
    rcases hγdisj 0 h0 u hu hzu with ⟨h, hu0⟩ | ⟨h, hu1⟩
    · rw [hu0, hγ₂0] at hup; exact hp₁p₂ hup.symm
    · norm_num at h
  have hq₁ : q₁ ∉ γ₂ '' Set.Icc (0 : ℝ) 1 := by
    rintro ⟨u, hu, hup⟩
    have hzu : γ₁ 1 = γ₂ u := by rw [hup, hγ₁1]
    rcases hγdisj 1 h1 u hu hzu with ⟨h, hu0⟩ | ⟨h, hu1⟩
    · norm_num at h
    · rw [hu1, hγ₂1] at hup; exact hq₁q₂ hup.symm
  intro s hs t ht hst
  rcases hclean (γ₂ s) (γ₂ t) (hγW₂ s hs) (hγW₂ t ht) hst with h | h | h | h | h
  · exact hγ₂inj hs ht h
  · exact absurd ⟨s, hs, h.1⟩ hp₁
  · exact absurd ⟨t, ht, h.2⟩ hp₁
  · exact absurd ⟨s, hs, h.1⟩ hq₁
  · exact absurd ⟨t, ht, h.2⟩ hq₁

/-- **The Whitney disc of the bigon, in the `IsWhitneyDisc` packaging.**

The general-position construction is the *proved* `Work.Drive.Whitney.whitneyDiscSmooth`
(`Drive/Whitney/whitneyDiscSmooth.lean`, axiom-clean): on the strip `[-1,1] × [0,1]` the loop
`f ∘ γ₁ ∪ f ∘ γ₂` bounds a `C^∞` embedded disc whose interior misses `f '' M` and which is
transverse to `f '' M` along its two horizontal edges.  Its two `f`-injectivity hypotheses are
supplied here *for free* from the bigon data (`arc_image_injOn₁`, `arc_image_injOn₂`). -/
theorem isWhitneyDisc_of_bigonData {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (hn : 3 ≤ n) (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (W : Set M) (p₁ p₂ q₁ q₂ : M) (γ₁ γ₂ : ℝ → M)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hp₁p₂ : p₁ ≠ p₂) (hq₁q₂ : q₁ ≠ q₂)
    (hp₁q₁ : p₁ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂) (hp₂q₁ : p₂ ≠ q₁) (hp₂q₂ : p₂ ≠ q₂)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hγ₂inj : Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1))
    (hγ₁smooth : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂smooth : ContMDiff (modelWithCornersSelf ℝ ℝ)
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    ∃ D : ℝ × ℝ → EuclideanSpace ℝ (Fin (2 * n)),
      Work.Drive.PushDisc.IsWhitneyDisc f γ₁ γ₂ D := by
  have hγv0 : f (γ₁ 0) = f (γ₂ 0) := by rw [hγ₁0, hγ₂0]; exact hfp
  have hγv1 : f (γ₁ 1) = f (γ₂ 1) := by rw [hγ₁1, hγ₂1]; exact hfq
  have hinjf₁ : Set.InjOn (fun s : ℝ => f (γ₁ s)) (Set.Icc (0 : ℝ) 1) :=
    arc_image_injOn₁ f W p₁ p₂ q₁ q₂ γ₁ γ₂ hγW₁ hγ₁0 hγ₁1 hγ₂0 hγ₂1 hp₁p₂ hp₂q₁ hp₁q₂
      hq₁q₂ hγ₁inj hclean hγdisj
  have hinjf₂ : Set.InjOn (fun s : ℝ => f (γ₂ s)) (Set.Icc (0 : ℝ) 1) :=
    arc_image_injOn₂ f W p₁ p₂ q₁ q₂ γ₁ γ₂ hγW₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1 hp₁p₂ hp₂q₁ hp₁q₂
      hq₁q₂ hγ₂inj hclean hγdisj
  obtain ⟨D, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
    Work.Drive.Whitney.whitneyDiscSmooth hn f hf himm γ₁ γ₂ hγ₁smooth hγ₂smooth hγv0 hγv1
      hinjf₁ hinjf₂ hγend
  exact ⟨D, Work.Drive.PushDisc.isWhitneyDisc_of_conj ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩⟩


/-! ## The final wiring: the target from the lens assembly

The complete construction of the windowed chart of the Whitney disc is
`Work.Drive.PushDisc.lensWiringSolid` (`Submission/Work/Drive/PushDisc/lensWiringSolid.lean`, proved,
axiom-clean; child `H344-L2699`): for *every* configuration of the target it produces
`Nonempty (WhitneyChartWindowData n f W p₁ p₂ q₁ q₂)` from the configuration rows together with the
two fibre rows `hfibp`, `hfibq` of the two double points.  Those two rows are *not* part of the
configuration: they are derived here from the clean/separated hypotheses (`hclean`, `hsep`) by
`mem_double_of_five` / `mem_double_q_of_five`.  Hence `WhitneyChartWindowAll n M` holds, and with the
proved `hasPushSignedSmooth_milnor_of_windowChartAll` the target follows. -/

/-- **The fibre row of the first crossing**, from the five-way clean form: `f ⁻¹' {f p₂} ⊆ {p₁, p₂}`.
The two `q`-cases of the disjunction are killed by `p₂ ≠ q₁`, `p₂ ≠ q₂`. -/
theorem mem_double_of_five {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ y : M)
    (hW₂ : p₂ ∈ W) (hp₂q₁ : p₂ ≠ q₁) (hp₂q₂ : p₂ ≠ q₂)
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hy : f y = f p₂) : y = p₁ ∨ y = p₂ := by
  by_cases hyW : y ∈ W
  · rcases hclean y p₂ hyW hW₂ hy with h | h | h | h | h
    · exact Or.inr h
    · exact Or.inl h.1
    · exact Or.inr h.1
    · exact absurd h.2 hp₂q₂
    · exact absurd h.2 hp₂q₁
  · exact absurd hy.symm (hsep p₂ y hW₂ hyW)

/-- **The fibre row of the second crossing**: `f ⁻¹' {f q₂} ⊆ {q₁, q₂}`. -/
theorem mem_double_q_of_five {n : ℕ} {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ y : M)
    (hW₄ : q₂ ∈ W) (hp₁q₂ : p₁ ≠ q₂) (hp₂q₂ : p₂ ≠ q₂)
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hy : f y = f q₂) : y = q₁ ∨ y = q₂ := by
  by_cases hyW : y ∈ W
  · rcases hclean y q₂ hyW hW₄ hy with h | h | h | h | h
    · exact Or.inr h
    · exact absurd h.2 (Ne.symm hp₂q₂)
    · exact absurd h.2 (Ne.symm hp₁q₂)
    · exact Or.inl h.1
    · exact Or.inr h.1
  · exact absurd hy.symm (hsep q₂ y hW₄ hyW)

/-- **`WhitneyChartWindowAll` from the lens assembly**: the last remaining input of the compact
`n ≥ 3` case of the Whitney embedding theorem.  It is the `∀`-configurations form of the proved
`Work.Drive.PushDisc.lensWiringSolid`, whose two extra fibre rows are discharged above. -/
theorem windowChartAll_of_lensWiring {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] :
    Work.Drive.PushDisc.WhitneyChartWindowAll n M := by
  intro hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂ hp₁q₁ hp₁q₂
    hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1
    hγW₁ hγW₂ hγ₁inj hγ₂inj hγ₁smooth hγ₂smooth hγ₁imm hγ₂imm hγdisj hγend hsign
  exact Work.Drive.PushDisc.lensWiringSolid hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃
    hW₄ hp₁p₂ hq₁q₂ hp₁q₁ hp₁q₂ hp₂q₁ hp₂q₂ hfp hfq hclean hsep
    (fun z hz => mem_double_of_five f W p₁ p₂ q₁ q₂ z hW₂ hp₂q₁ hp₂q₂ hsep hclean
      (by rw [hz, hfp]))
    (fun z hz => mem_double_q_of_five f W p₁ p₂ q₁ q₂ z hW₄ hp₁q₂ hp₂q₂ hsep hclean
      (by rw [hz, hfq]))
    htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1 hγW₁ hγW₂ hγ₁inj hγ₂inj hγ₁smooth
    hγ₂smooth hγ₁imm hγ₂imm hγdisj hγend hsign

/-- The signed bigon push for SMOOTH immersed arcs: the remaining geometric input of the compact
`n ≥ 3` case. -/
theorem hasPushSignedSmooth_milnor {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] :
    Work.Drive.HasPushSignedSmooth n M :=
  hasPushSignedSmooth_milnor_of_windowChartAll
    (windowChartAll_of_lensWiring (n := n) (M := M))

end Work.Drive
