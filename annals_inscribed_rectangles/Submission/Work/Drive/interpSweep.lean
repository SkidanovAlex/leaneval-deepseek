import Mathlib
import Submission.Work.Drive.interp_ne_zero_iff
import Submission.Work.Drive.linearPlaneChart
import Submission.Work.Drive.mk2CLM
import Submission.Work.Drive.SeamSweep
import Submission.Work.Drive.planeChain

/-!
# The interpolation sweep: from a plane presentation to a *linear* plane

The end contribution `Σ_k bottom_k ≡ 1` of the chain route needs, for each of the three rotated planes
`P_k`, a `3`-chain `D_k` with

> `D_k` at `x 2 = 1` the **plane** `P_k` (the top face) and `D_k` at `x 2 = 0` a **linear** projective
> plane `Z_k` of the level `c k` (the bottom face),

because the bottom count for three *linear* planes in general position is the proved
`Work.Drive.ncard_linPlaneTriples_eq_one` / `Work.Drive.projective_planes_meet_oddly`, while the count
for the *shadow* would need the (unavailable) `α³` of `ℝP³`.

`Submission/Work/Drive/END_CONTRIBUTION_STATUS.md` §2(a) records the obstruction of the natural
construction: presenting both faces by *lifts* `V` (of the plane) and `W` (of the linear plane) and
interpolating them **linearly**, the interpolated lift

> `s ↦ (1 - s) • V y + s • W y`

vanishes at `s = 1/(1 - ρ)` whenever `W y = ρ • V y` with `ρ < 0`, i.e. exactly at the base points `y`
where the two lifts are *negatively* parallel.  This file makes that criterion exact
(`interpLift_ne_zero_iff`) and builds the sweep on top of it, so that the only geometric input the
construction needs is

> `∀ y, ¬ ∃ c : ℝ, c < 0, W y = c • V y`   (no base point at which the two lifts are negatively parallel)

which is an **open condition on the data** (the plane presentation and the choice of `Z_k`): it is the
"diagonal is empty" condition.  It is *not* an obstruction: for a generic choice of the linear bottom
the same-parameter diagonal is empty (`INTERP_DIAGONAL_NOTES.md`).

The sweep is built in the capping space through the transparent coordinates
`Work.Drive.cappingVecPoint` (`(level, class)`), so that a *single* formula covers the whole path from
the plane to the linear plane:

* `Work.Drive.interpLevel` — the level: `ℓ y` at `s = 1`, `c` at `s = 0`, multiplicatively
  interpolated, hence positive for all `s ∈ ℝ` (the chains of the engine are maps on all of `ℝ³`);
* `Work.Drive.interpLiftStep` — the clamped straight-line interpolation of the two lifts, using the
  reversed smooth step `Work.Drive.interpRho` (`1` for `s ≤ 0`, `0` for `s ≥ 1`), so that the chain is
  smooth on all of `ℝ³` and *constant* outside the unit interval in `s`;
* `Work.Drive.interpSweep` — the chain;
* `Work.Drive.interpSweep_face_one` / `..._face_zero` — the two faces (the plane and the linear plane);
* `Work.Drive.interpSweep_seamInv` — the antipodal compatibility of the four seam faces, which is
  inherited from the two presentations (the seam involution acts on both lifts by `-1`);
* `Work.Drive.interpSweep_face_zero_linPlane` — the identification of the bottom face with the folded
  chart `Work.Drive.diskPlane (Work.Drive.linPlaneChart φ c hc)` of a linear plane, for the concrete
  choice `W y = φ (linVecC (sqDisk (foldBox y)))`, whose seam sign is
  `Work.Drive.linVecC_foldBox_seamInv`;
* `Work.Drive.interpLevel_eq_of_slice`, `Work.Drive.interpSweep_slice_point` — the *level slices* of
  the sweep: the radial parameter whose interpolated level is `c₀ ∈ (c, ℓ)` and the transparent
  coordinates of the sweep there;
* `Work.Drive.sliceRho`, `..._mem_Icc`, `Work.Drive.sliceLift`, `Work.Drive.sliceLevel`,
  `Work.Drive.sliceFamily`, `Work.Drive.sliceFamilyBox` — the **bordism inside the level** `c₀` of
  `INTERP_DIAGONAL_NOTES.md` §5/§10: the slice of the sweep with bottom level driven from `c₀` (so that
  the face is the *linear* plane) down to `c₁`; `Work.Drive.sliceFamilyBox_seamInv` is its seam
  invariance.  Its smoothness is delegated as `Work.Drive.contMDiff_sliceFamilyBox`
  (`Submission/Work/Drive/contMDiff_sliceFamilyBox.lean`), whose `..._face_zero` / `..._face_one` are
  the two boundary faces of the bordism;
* `Work.Drive.meet3Hyp_interpSweeps` — the *engine* interface: the three interpolation sweeps satisfy
  `Work.Drive.Meet3Hyp` from the genericity data and the smoothness of the presentations.
  `Work.Drive.contMDiff_interpSweep` (`Submission/Work/Drive/contMDiff_interpSweep.lean`) is the
  smoothness of the chain itself, and `Work.Drive.meet3Hyp_interpSweeps_of_contMDiff` the version that
  discharges that hypothesis; `Work.Drive.deriv_interpRho_ne_zero` is the small fact that the radial
  coefficient is non-degenerate.

What is **not** in this file (and is the remaining work of the ends): the *genericity* of the
interpolation sweep (`Meet3Generic`: the transversality of the triple intersections, the face condition
and the radial non-degeneracy — see `INTERP_DIAGONAL_NOTES.md` §6 for what changes with respect to the
clamped sweep), the *data* condition "no negative parallelism" for the actual charts (§1–§3 there), the
identification of the *top* count with the mod-2 intersection number `n_P`
(`ENDS_AND_SEAMS_NOTES.md` §2, `CONCRETE_CHAINS_STATUS.md` §3), and the level-engine application of the
bordism.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

-- The smooth structure of the capping space, as a local instance of this file (`Submission/Work/Drive/
-- planeChain.lean` sets the same instances locally where the engine's vocabulary lives).  Only the
-- engine-facing statements of §9 need them; nothing else in this file does.
set_option warn.classDefReducibility false in
  attribute [local instance] cappingCharted isManifold_cappingCharted t2Space_cappingSpace projCharted

/-! ## 1. The straight-line interpolation of two lifts, and its vanishing criterion -/

/-- The straight-line interpolation of two vector lifts. -/
def interpLift {X : Type*} (V W : X → Eucl 3) (x : X) (s : ℝ) : Eucl 3 :=
  (1 - s) • V x + s • W x

/-- **The uniform vanishing criterion.**  The straight-line interpolation of two lifts vanishes
somewhere on the open segment exactly at the base points at which the second lift is a *negative*
multiple of the first. -/
theorem interpLift_ne_zero_iff {X : Type*} (V W : X → Eucl 3) :
    (∀ x (s : ℝ), 0 < s → s < 1 → interpLift V W x s ≠ 0) ↔
      ∀ x, ¬ ∃ c : ℝ, c < 0 ∧ W x = c • V x := by
  constructor
  · intro h x
    exact interp_ne_zero_iff.mp fun s hs hs1 => h x s hs hs1
  · intro h x s hs hs1
    exact interp_ne_zero_iff.mpr (h x) s hs hs1

/-- The interpolation is non-vanishing on the closed segment as soon as neither lift vanishes and the
two are never negatively parallel. -/
theorem interpLift_ne_zero {X : Type*} (V W : X → Eucl 3) (hV : ∀ x, V x ≠ 0)
    (hW : ∀ x, W x ≠ 0) (h : ∀ x, ¬ ∃ c : ℝ, c < 0 ∧ W x = c • V x) :
    ∀ x (s : ℝ), 0 ≤ s → s ≤ 1 → interpLift V W x s ≠ 0 := by
  intro x s hs0 hs1
  rcases lt_or_eq_of_le hs0 with hs | rfl
  · rcases lt_or_eq_of_le hs1 with hs' | rfl
    · exact (interpLift_ne_zero_iff V W).mpr h x s hs hs'
    · simpa [interpLift] using hW x
  · simpa [interpLift] using hV x

/-- **The sign of the criterion can be flipped**: if no two lifts are *positively* parallel, then the
straight-line interpolation of the first with the **negated** second is non-vanishing on the closed
segment.  (The negated lift presents the same projective classes, so the two chains have the same
faces; this is the reduction of the criterion to "all parallel points have the same sign".) -/
theorem interpLift_ne_zero_of_no_pos_parallel {X : Type*} (V W : X → Eucl 3)
    (hV : ∀ x, V x ≠ 0) (hW : ∀ x, W x ≠ 0)
    (h : ∀ x, ¬ ∃ c : ℝ, 0 < c ∧ W x = c • V x) :
    ∀ x (s : ℝ), 0 ≤ s → s ≤ 1 →
      interpLift V (fun x => - W x) x s ≠ 0 := by
  refine interpLift_ne_zero V (fun x => - W x) hV (fun x => neg_ne_zero.mpr (hW x)) ?_
  rintro x ⟨c, hc, hc'⟩
  exact h x ⟨-c, neg_pos.mpr hc, by rw [neg_smul, neg_eq_iff_eq_neg.mp hc']⟩

/-! ## 2. The reversed smooth step and the clamped interpolation -/

/-- The reversed smooth step: `1` on `(-∞,0]`, `0` on `[1,∞)`, smooth and in `[0,1]`. -/
def interpRho (s : ℝ) : ℝ := Real.smoothTransition (1 - s)

lemma interpRho_nonneg (s : ℝ) : 0 ≤ interpRho s := Real.smoothTransition.nonneg _

lemma interpRho_le_one (s : ℝ) : interpRho s ≤ 1 := Real.smoothTransition.le_one _

lemma interpRho_zero : interpRho 0 = 1 := by
  rw [interpRho, sub_zero, Real.smoothTransition.one]

lemma interpRho_one : interpRho 1 = 0 := by
  rw [interpRho, sub_self, Real.smoothTransition.zero]

lemma interpRho_eq_one_of_nonpos {s : ℝ} (h : s ≤ 0) : interpRho s = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

lemma interpRho_eq_zero_of_one_le {s : ℝ} (h : 1 ≤ s) : interpRho s = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- The clamped interpolation of two lifts: equal to the first for `s ≤ 0`, to the second for
`s ≥ 1`, a convex combination in between. -/
def interpLiftStep {X : Type*} (V W : X → Eucl 3) (x : X) (s : ℝ) : Eucl 3 :=
  (1 - interpRho s) • V x + interpRho s • W x

/-- **The clamped interpolation never vanishes**, from the vanishing criterion of the straight line. -/
theorem interpLiftStep_ne_zero {X : Type*} (V W : X → Eucl 3) (hV : ∀ x, V x ≠ 0)
    (hW : ∀ x, W x ≠ 0) (hne : ∀ x t, 0 ≤ t → t ≤ 1 → interpLift V W x t ≠ 0) :
    ∀ x s, interpLiftStep V W x s ≠ 0 := by
  intro x s
  have h0 : 0 ≤ interpRho s := interpRho_nonneg s
  have h1 : interpRho s ≤ 1 := interpRho_le_one s
  rcases eq_or_lt_of_le h0 with h | h
  · rw [interpLiftStep, ← h, sub_zero, one_smul, zero_smul, add_zero]
    exact hV x
  · rcases eq_or_lt_of_le h1 with h' | h'
    · rw [interpLiftStep, h', sub_self, zero_smul, one_smul, zero_add]
      exact hW x
    · exact hne x (interpRho s) h.le h'.le

theorem interpLiftStep_of_nonpos {X : Type*} (V W : X → Eucl 3) (x : X) {s : ℝ} (h : s ≤ 0) :
    interpLiftStep V W x s = W x := by
  rw [interpLiftStep, interpRho_eq_one_of_nonpos h, sub_self, zero_smul, one_smul, zero_add]

theorem interpLiftStep_of_one_le {X : Type*} (V W : X → Eucl 3) (x : X) {s : ℝ} (h : 1 ≤ s) :
    interpLiftStep V W x s = V x := by
  rw [interpLiftStep, interpRho_eq_zero_of_one_le h, sub_zero, one_smul, zero_smul, add_zero]

/-! ## 3. The level interpolation -/

/-- The multiplicatively interpolated level: `c` on `(-∞,0]`, `ℓ x` on `[1,∞)`, positive
everywhere. -/
def interpLevel {X : Type*} (ℓ : X → ℝ) (c : ℝ) (x : X) (s : ℝ) : ℝ :=
  (ℓ x) ^ (1 - interpRho s) * c ^ (interpRho s)

theorem interpLevel_pos {X : Type*} (ℓ : X → ℝ) (c : ℝ) (hℓ : ∀ x, 0 < ℓ x) (hc : 0 < c)
    (x : X) (s : ℝ) : 0 < interpLevel ℓ c x s :=
  mul_pos (Real.rpow_pos_of_pos (hℓ x) _) (Real.rpow_pos_of_pos hc _)

theorem interpLevel_of_nonpos {X : Type*} (ℓ : X → ℝ) (c : ℝ) (x : X) {s : ℝ} (h : s ≤ 0) :
    interpLevel ℓ c x s = c := by
  rw [interpLevel, interpRho_eq_one_of_nonpos h, sub_self, Real.rpow_zero,
    Real.rpow_one, one_mul]

theorem interpLevel_of_one_le {X : Type*} (ℓ : X → ℝ) (c : ℝ) (x : X) {s : ℝ} (h : 1 ≤ s) :
    interpLevel ℓ c x s = ℓ x := by
  rw [interpLevel, interpRho_eq_zero_of_one_le h, sub_zero, Real.rpow_one,
    Real.rpow_zero, mul_one]

/-! ## 4. Congruence lemmas for the capping point -/

/-- `Projectivization.mk` depends only on the vector (the non-vanishing proofs are filled by the
caller). -/
lemma projectivizationMk_eq_of_eq_vector {v v' : Eucl 3} (h : v = v') :
    ∀ (hv : v ≠ 0) (hv' : v' ≠ 0),
      Projectivization.mk ℝ v hv = Projectivization.mk ℝ v' hv' := by
  subst h
  intro hv hv'
  exact projectivizationMk_congr ℝ (Eucl 3)

/-- `Projectivization.mk` maps a vector and its negative to the same point. -/
lemma projectivizationMk_eq_of_eq_neg_vector {v v' : Eucl 3} (h : v = - v') :
    ∀ (hv : v ≠ 0) (hv' : v' ≠ 0),
      Projectivization.mk ℝ v hv = Projectivization.mk ℝ v' hv' := by
  intro hv hv'
  exact projectivizationMk_eq_of_eq_neg h hv' hv

/-- The capping point does not depend on the non-vanishing proofs. -/
lemma cappingVecPoint_proof_irrel (r : ℝ) (hr hr' : 0 < r) (V : Eucl 3) (hV hV' : V ≠ 0) :
    cappingVecPoint r hr V hV = cappingVecPoint r hr' V hV' := by
  apply cappingSpaceHomeoProj.injective
  simp only [cappingSpaceHomeoProj_cappingVecPoint]

/-- Two capping points of the same radius with the same projective class agree. -/
lemma cappingVecPoint_eq_of_class {r : ℝ} (hr : 0 < r) {V V' : Eucl 3} (hV : V ≠ 0)
    (hV' : V' ≠ 0) (h : Projectivization.mk ℝ V hV = Projectivization.mk ℝ V' hV') :
    cappingVecPoint r hr V hV = cappingVecPoint r hr V' hV' := by
  apply cappingSpaceHomeoProj.injective
  simp only [cappingSpaceHomeoProj_cappingVecPoint]
  exact Prod.ext rfl h

/-- **Negating the lift does not change the capping point** (the projective class of `-v` is that of
`v`).  Consequently the sign convention of the bottom lift of `interpSweep` is free. -/
lemma cappingVecPoint_neg (r : ℝ) (hr : 0 < r) (V : Eucl 3) (hV : V ≠ 0) (hV' : - V ≠ 0) :
    cappingVecPoint r hr (- V) hV' = cappingVecPoint r hr V hV :=
  cappingVecPoint_eq_of_class hr hV' hV (projectivizationMk_eq_of_eq_neg rfl hV hV')

/-! ## 5. The interpolation sweep -/

/-- **The interpolation sweep**: the chain from a plane presentation `(ℓ, V)` at `x 2 = 1` to the
linear plane presentation `(c, W)` at `x 2 = 0`, in the transparent coordinates of the capping
space. -/
def interpSweep (c : ℝ) (hc : 0 < c) (ℓ : EuclideanSpace ℝ (Fin 2) → ℝ) (hℓ : ∀ y, 0 < ℓ y)
    (V W : EuclideanSpace ℝ (Fin 2) → Eucl 3) (hV : ∀ y, V y ≠ 0) (hW : ∀ y, W y ≠ 0)
    (hne : ∀ y t, 0 ≤ t → t ≤ 1 → interpLift V W y t ≠ 0)
    (x : EuclideanSpace ℝ (Fin 3)) : CappingSpace :=
  cappingVecPoint (interpLevel ℓ c (mk2 (x 0) (x 1)) (x 2))
    (interpLevel_pos ℓ c hℓ hc (mk2 (x 0) (x 1)) (x 2))
    (interpLiftStep V W (mk2 (x 0) (x 1)) (x 2))
    (interpLiftStep_ne_zero V W hV hW hne (mk2 (x 0) (x 1)) (x 2))

/-- **The `x 2 = 1` face of the interpolation sweep is the plane presentation.** -/
theorem interpSweep_face_one (c : ℝ) (hc : 0 < c) (ℓ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hℓ : ∀ y, 0 < ℓ y) (V W : EuclideanSpace ℝ (Fin 2) → Eucl 3) (hV : ∀ y, V y ≠ 0)
    (hW : ∀ y, W y ≠ 0) (hne : ∀ y t, 0 ≤ t → t ≤ 1 → interpLift V W y t ≠ 0)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : x 2 = 1) :
    interpSweep c hc ℓ hℓ V W hV hW hne x
      = cappingVecPoint (ℓ (mk2 (x 0) (x 1))) (hℓ _) (V (mk2 (x 0) (x 1))) (hV _) := by
  unfold interpSweep
  apply cappingSpaceHomeoProj.injective
  simp only [cappingSpaceHomeoProj_cappingVecPoint]
  refine Prod.ext (Subtype.ext ?_) ?_
  · exact interpLevel_of_one_le ℓ c (mk2 (x 0) (x 1)) hx.ge
  · exact projectivizationMk_eq_of_eq_vector
      (interpLiftStep_of_one_le V W (mk2 (x 0) (x 1)) hx.ge) _ _

/-- **The `x 2 = 0` face of the interpolation sweep is the linear plane presentation.** -/
theorem interpSweep_face_zero (c : ℝ) (hc : 0 < c) (ℓ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hℓ : ∀ y, 0 < ℓ y) (V W : EuclideanSpace ℝ (Fin 2) → Eucl 3) (hV : ∀ y, V y ≠ 0)
    (hW : ∀ y, W y ≠ 0) (hne : ∀ y t, 0 ≤ t → t ≤ 1 → interpLift V W y t ≠ 0)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : x 2 = 0) :
    interpSweep c hc ℓ hℓ V W hV hW hne x
      = cappingVecPoint c hc (W (mk2 (x 0) (x 1))) (hW _) := by
  unfold interpSweep
  apply cappingSpaceHomeoProj.injective
  simp only [cappingSpaceHomeoProj_cappingVecPoint]
  refine Prod.ext (Subtype.ext ?_) ?_
  · exact interpLevel_of_nonpos ℓ c (mk2 (x 0) (x 1)) hx.le
  · exact projectivizationMk_eq_of_eq_vector
      (interpLiftStep_of_nonpos V W (mk2 (x 0) (x 1)) hx.le) _ _

/-- **The interpolation sweep inherits the seam invariance of its two presentations**, the seam
involution acting on both lifts by `-1` (the disk models of both planes are antipodal on their
boundary circles) and fixing the level function. -/
theorem interpSweep_seamInv (c : ℝ) (hc : 0 < c) (ℓ : EuclideanSpace ℝ (Fin 2) → ℝ)
    (hℓ : ∀ y, 0 < ℓ y) (V W : EuclideanSpace ℝ (Fin 2) → Eucl 3) (hV : ∀ y, V y ≠ 0)
    (hW : ∀ y, W y ≠ 0) (hne : ∀ y t, 0 ≤ t → t ≤ 1 → interpLift V W y t ≠ 0)
    (hℓs : ∀ y, onSeam2 y → ℓ (seamInv2 y) = ℓ y)
    (hVs : ∀ y, onSeam2 y → V (seamInv2 y) = - V y)
    (hWs : ∀ y, onSeam2 y → W (seamInv2 y) = - W y)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : onSeam x) :
    interpSweep c hc ℓ hℓ V W hV hW hne (seamInv x)
      = interpSweep c hc ℓ hℓ V W hV hW hne x := by
  have hy : onSeam2 (mk2 (x 0) (x 1)) := onSeam2_of_onSeam x hx
  have hp : mk2 ((seamInv x) 0) ((seamInv x) 1) = seamInv2 (mk2 (x 0) (x 1)) := mk2_seamInv x
  have h2 : (seamInv x) 2 = x 2 := seamInv_apply_two x
  have hlev : interpLevel ℓ c (mk2 ((seamInv x) 0) ((seamInv x) 1)) ((seamInv x) 2)
      = interpLevel ℓ c (mk2 (x 0) (x 1)) (x 2) := by
    simp only [interpLevel]
    rw [hp, h2, hℓs _ hy]
  have hlift : interpLiftStep V W (mk2 ((seamInv x) 0) ((seamInv x) 1)) ((seamInv x) 2)
      = - interpLiftStep V W (mk2 (x 0) (x 1)) (x 2) := by
    rw [hp, h2, interpLiftStep, interpLiftStep, hVs _ hy, hWs _ hy, smul_neg, smul_neg,
      neg_add]
  unfold interpSweep
  apply cappingSpaceHomeoProj.injective
  simp only [cappingSpaceHomeoProj_cappingVecPoint]
  refine Prod.ext (Subtype.ext ?_) ?_
  · exact hlev
  · exact projectivizationMk_eq_of_eq_neg_vector hlift _ _

/-! ## 6. The bottom face is the folded chart of a linear plane -/

/-- The linear plane chart is the capping point of its lift. -/
lemma linPlaneChart_eq_cappingVecPoint (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c) (z : ℂ) :
    linPlaneChart φ c hc z = cappingVecPoint c hc (φ (linVecC z)) (phi_linVecC_ne_zero φ z) := by
  apply cappingSpaceHomeoProj.injective
  simp only [cappingSpaceHomeoProj_cappingVecPoint, cappingSpaceHomeoProj_linPlaneChart]

/-- **The bottom face of the interpolation sweep with the linear plane's lift
`W y = φ (linVecC (sqDisk (foldBox y)))` is exactly the folded chart
`diskPlane (linPlaneChart φ c hc)` of the linear plane** (`Submission/Work/Drive/planeChain.lean`).
So with this choice of `W` the interpolation sweep runs from the plane presentation `(ℓ, V)` to the
linear plane's chain. -/
theorem interpSweep_face_zero_linPlane (φ : Eucl 3 ≃L[ℝ] Eucl 3) (c : ℝ) (hc : 0 < c)
    (ℓ : EuclideanSpace ℝ (Fin 2) → ℝ) (hℓ : ∀ y, 0 < ℓ y)
    (V : EuclideanSpace ℝ (Fin 2) → Eucl 3) (hV : ∀ y, V y ≠ 0)
    (hne : ∀ y t, 0 ≤ t → t ≤ 1 →
      interpLift V (fun y => φ (linVecC (sqDisk (foldBox y)))) y t ≠ 0)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : x 2 = 0) :
    interpSweep c hc ℓ hℓ V (fun y => φ (linVecC (sqDisk (foldBox y)))) hV
        (fun y => phi_linVecC_ne_zero φ (sqDisk (foldBox y))) hne x
      = diskPlane (linPlaneChart φ c hc) (mk2 (x 0) (x 1)) := by
  rw [interpSweep_face_zero c hc ℓ hℓ V (fun y => φ (linVecC (sqDisk (foldBox y)))) hV
    (fun y => phi_linVecC_ne_zero φ (sqDisk (foldBox y))) hne x hx, diskPlane_apply]
  exact (linPlaneChart_eq_cappingVecPoint φ c hc (sqDisk (foldBox (mk2 (x 0) (x 1))))).symm

/-! ## 7. The seam sign of the concrete linear chart -/

/-- **The linear plane's lift flips sign under the seam involution.**  This is the concrete discharge
of the hypothesis `hWs` of `Work.Drive.interpSweep_seamInv` for the bottom chart
`W y = φ (linVecC (sqDisk (foldBox y)))`: on the boundary of the square `sqDisk` lands on the unit
circle (`Work.Drive.norm_sqDisk_eq_one_iff`) and `Work.Drive.linVecC_neg` applies. -/
theorem linVecC_foldBox_seamInv (φ : Eucl 3 ≃L[ℝ] Eucl 3) (y : EuclideanSpace ℝ (Fin 2))
    (hy : onSeam2 y) :
    φ (linVecC (sqDisk (foldBox (seamInv2 y)))) = - φ (linVecC (sqDisk (foldBox y))) := by
  have hnorm : ‖sqDisk (foldBox y)‖ = 1 :=
    (norm_sqDisk_eq_one_iff _ (foldBox_mem_unitBox y)).mpr (onSeam2_foldBox hy)
  rw [foldBox_seamInv2, sqDisk_seamInv, linVecC_neg hnorm, map_neg]

/-! ## 8. The level slices of the interpolation sweep

For the end contribution the chain is truncated at a level `c₀` with `c < c₀ < ℓ`, and what enters the
bordism of `INTERP_DIAGONAL_NOTES.md` §5 is the *level-`c₀` slice* of the sweep, i.e. the point of the
sweep whose level is `c₀`.  The radial parameter of that slice is the smooth function
`(log c₀ - log (ℓ y)) / (log c - log (ℓ y))` of the weight `interpRho`, and the slice point is
explicit. -/

/-- The reversed smooth step is onto `[0,1]`. -/
lemma exists_interpRho_eq {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧ interpRho s = t := by
  have hmem : t ∈ Set.Icc (Real.smoothTransition 0) (Real.smoothTransition 1) := by
    rw [Real.smoothTransition.zero, Real.smoothTransition.one]
    exact ⟨h0, h1⟩
  obtain ⟨x, hx, hxe⟩ := intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num)
    (Real.smoothTransition.continuous.continuousOn) hmem
  exact ⟨1 - x, by linarith [hx.2], by linarith [hx.1],
    by rw [interpRho, show (1 : ℝ) - (1 - x) = x by ring, hxe]⟩

/-- **The level slice of the interpolation level**: for `0 < c < c₀ < ℓ x` there is a radial parameter
`s ∈ [0,1]` whose weight is `(log c₀ - log (ℓ x)) / (log c - log (ℓ x))` and at which the interpolated
level is exactly `c₀`. -/
theorem interpLevel_eq_of_slice {X : Type*} (ℓ : X → ℝ) (c : ℝ) (x : X) {c₀ : ℝ}
    (hc : 0 < c) (hc₀ : 0 < c₀) (hcc₀ : c < c₀) (hc₀ℓ : c₀ < ℓ x) :
    ∃ s : ℝ, 0 ≤ s ∧ s ≤ 1 ∧
      interpRho s = (Real.log c₀ - Real.log (ℓ x)) / (Real.log c - Real.log (ℓ x)) ∧
      interpLevel ℓ c x s = c₀ := by
  have hlog : Real.log c < Real.log (ℓ x) := Real.log_lt_log hc (lt_trans hcc₀ hc₀ℓ)
  have hlog' : Real.log c < Real.log c₀ := Real.log_lt_log hc hcc₀
  have hlog₀ : Real.log c₀ < Real.log (ℓ x) := Real.log_lt_log hc₀ hc₀ℓ
  have hne : Real.log c - Real.log (ℓ x) ≠ 0 := sub_ne_zero.mpr (ne_of_lt hlog)
  have hden : Real.log c - Real.log (ℓ x) < 0 := sub_neg.mpr hlog
  have hnum : Real.log c₀ - Real.log (ℓ x) < 0 := sub_neg.mpr hlog₀
  have hρpos : 0 < (Real.log c₀ - Real.log (ℓ x)) / (Real.log c - Real.log (ℓ x)) :=
    div_pos_of_neg_of_neg hnum hden
  have hρlt : (Real.log c₀ - Real.log (ℓ x)) / (Real.log c - Real.log (ℓ x)) < 1 := by
    rw [div_lt_iff_of_neg hden, one_mul]
    linarith
  obtain ⟨s, hs0, hs1, hs⟩ := exists_interpRho_eq hρpos.le hρlt.le
  refine ⟨s, hs0, hs1, hs, ?_⟩
  have hlin : Real.log (ℓ x) * (1 - interpRho s) + Real.log c * interpRho s = Real.log c₀ := by
    rw [hs]
    field_simp
    ring
  simp only [interpLevel]
  rw [Real.rpow_def_of_pos (lt_trans hc (lt_trans hcc₀ hc₀ℓ)), Real.rpow_def_of_pos hc,
    ← Real.exp_add, hlin, Real.exp_log hc₀]

/-- **The level-`c₀` slice of the interpolation sweep is explicit**: at a parameter whose interpolated
level is `c₀`, the *transparent coordinates* of the sweep are the level `c₀` and the class of the
interpolated lift `(1 - ρ) • V y + ρ • W y`.  This is the *slice point* entering the bordism inside the
level of `INTERP_DIAGONAL_NOTES.md` §5. -/
theorem interpSweep_slice_point (c c₀ : ℝ) (hc : 0 < c)
    (ℓ : EuclideanSpace ℝ (Fin 2) → ℝ) (hℓ : ∀ y, 0 < ℓ y)
    (V W : EuclideanSpace ℝ (Fin 2) → Eucl 3) (hV : ∀ y, V y ≠ 0) (hW : ∀ y, W y ≠ 0)
    (hne : ∀ y t, 0 ≤ t → t ≤ 1 → interpLift V W y t ≠ 0)
    (x : EuclideanSpace ℝ (Fin 3))
    (hlev : interpLevel ℓ c (mk2 (x 0) (x 1)) (x 2) = c₀) :
    ((cappingSpaceHomeoProj (interpSweep c hc ℓ hℓ V W hV hW hne x)).1 : ℝ) = c₀ ∧
      (cappingSpaceHomeoProj (interpSweep c hc ℓ hℓ V W hV hW hne x)).2
        = Projectivization.mk ℝ
            ((1 - interpRho (x 2)) • V (mk2 (x 0) (x 1))
              + interpRho (x 2) • W (mk2 (x 0) (x 1)))
            (interpLiftStep_ne_zero V W hV hW hne (mk2 (x 0) (x 1)) (x 2)) := by
  unfold interpSweep
  rw [cappingSpaceHomeoProj_cappingVecPoint]
  exact ⟨hlev, projectivizationMk_eq_of_eq_vector rfl _ _⟩

/-! ## 9. The engine interface for the interpolation sweeps -/

/-- **The three interpolation sweeps satisfy the engine's hypotheses** (`Work.Drive.Meet3Hyp`), given
the genericity data of the three chains (`Work.Drive.Meet3Generic`) and the smoothness of the
presentations: this is `Work.Drive.meet3Hyp_of_generic` applied to `interpSweep_seamInv`.  So once the
smoothness `Work.Drive.contMDiff_interpSweep` is available, the ends' chains of
`INTERP_DIAGONAL_NOTES.md` §5 are engine-ready. -/
theorem meet3Hyp_interpSweeps
    (c : Fin 3 → ℝ) (hc : ∀ k, 0 < c k)
    (ℓ : Fin 3 → EuclideanSpace ℝ (Fin 2) → ℝ) (hℓ : ∀ k y, 0 < ℓ k y)
    (V W : Fin 3 → EuclideanSpace ℝ (Fin 2) → Eucl 3) (hV : ∀ k y, V k y ≠ 0)
    (hW : ∀ k y, W k y ≠ 0)
    (hne : ∀ k y t, 0 ≤ t → t ≤ 1 → interpLift (V k) (W k) y t ≠ 0)
    (hℓs : ∀ k y, onSeam2 y → ℓ k (seamInv2 y) = ℓ k y)
    (hVs : ∀ k y, onSeam2 y → V k (seamInv2 y) = - V k y)
    (hWs : ∀ k y, onSeam2 y → W k (seamInv2 y) = - W k y)
    (hsm : ∀ k, ContMDiff (𝓡 3) (𝓡 4) (((⊤ : ℕ∞) : WithTop ℕ∞))
      (interpSweep (c k) (hc k) (ℓ k) (hℓ k) (V k) (W k) (hV k) (hW k) (hne k)))
    (hgen : Meet3Generic CappingSpace
      (fun k => interpSweep (c k) (hc k) (ℓ k) (hℓ k) (V k) (W k) (hV k) (hW k) (hne k))) :
    Meet3Hyp CappingSpace
      (fun k => interpSweep (c k) (hc k) (ℓ k) (hℓ k) (V k) (W k) (hV k) (hW k) (hne k)) :=
  meet3Hyp_of_generic _
    (fun k => hsm k) hgen
    (fun k x hx => (interpSweep_seamInv (c k) (hc k) (ℓ k) (hℓ k) (V k) (W k) (hV k) (hW k)
      (hne k) (hℓs k) (hVs k) (hWs k) x hx).symm)

/-! ## 10. The bordism inside the level: the slice family

`INTERP_DIAGONAL_NOTES.md` §5 compares the end count of the interpolation sweeps with the count of three
*linear* planes by a bordism **inside the level** `c₀`: the level-`c₀` slice of the sweep with bottom
level `t` moves, as `t` runs from `c₁` to `c₀`, from the slice of the sweep `D^{c₁}` to the bottom face
`Z` (a linear plane).  This section fixes that family as a box map.

* `sliceRho c₀ t ℓ` — the weight of the slice in the interpolated lift: it solves
  `interpLevel ℓ t s = c₀` (compare `interpLevel_eq_of_slice`);
* `sliceLift c₀ t ℓ V W` — the interpolated lift `(1 - ρ) • V + ρ • W` at that weight;
* `sliceLevel c₀ c₁ t` — the *clamped* bottom level: `c₀` for `t ≤ 0`, `c₁` for `t ≥ 1`, so that the
  family is defined on all of `ℝ³` and its two faces are the ones the bordism needs;
* `sliceFamily`, `sliceFamilyBox` — the family as a capping-space point and as a box map. -/

/-- The weight of the level-`c₀` slice of an interpolation sweep with bottom level `t`. -/
noncomputable def sliceRho (c₀ t ℓ : ℝ) : ℝ := (Real.log c₀ - Real.log ℓ) / (Real.log t - Real.log ℓ)

/-- The lift along the level-`c₀` slice: the straight-line interpolation of `V` and `W` at the weight
of the slice. -/
noncomputable def sliceLift (c₀ t ℓ : ℝ) (V W : Eucl 3) : Eucl 3 :=
  (1 - sliceRho c₀ t ℓ) • V + sliceRho c₀ t ℓ • W

/-- The *clamped* bottom level of the slice family: `c₀` for `t ≤ 0`, `c₁` for `t ≥ 1`. -/
noncomputable def sliceLevel (c₀ c₁ t : ℝ) : ℝ := c₁ + (c₀ - c₁) * interpRho t

lemma sliceLevel_of_nonpos {c₀ c₁ t : ℝ} (h : t ≤ 0) : sliceLevel c₀ c₁ t = c₀ := by
  rw [sliceLevel, interpRho_eq_one_of_nonpos h]; ring

lemma sliceLevel_of_one_le {c₀ c₁ t : ℝ} (h : 1 ≤ t) : sliceLevel c₀ c₁ t = c₁ := by
  rw [sliceLevel, interpRho_eq_zero_of_one_le h]; ring

lemma sliceLevel_mem_Icc {c₀ c₁ t : ℝ} (hlt : c₁ ≤ c₀) :
    sliceLevel c₀ c₁ t ∈ Set.Icc c₁ c₀ := by
  have h0 : 0 ≤ interpRho t := interpRho_nonneg t
  have h1 : interpRho t ≤ 1 := interpRho_le_one t
  constructor
  · rw [sliceLevel]; nlinarith
  · rw [sliceLevel]; nlinarith

/-- For `0 < t < c₀ < ℓ` the slice weight lies in `(0,1)`. -/
lemma sliceRho_mem_Ioo {c₀ t ℓ : ℝ} (ht : 0 < t) (hc₀ : 0 < c₀) (htc₀ : t < c₀)
    (hc₀ℓ : c₀ < ℓ) : sliceRho c₀ t ℓ ∈ Set.Ioo (0 : ℝ) 1 := by
  have hlt : Real.log t < Real.log c₀ := Real.log_lt_log ht htc₀
  have hlt2 : Real.log c₀ < Real.log ℓ := Real.log_lt_log hc₀ hc₀ℓ
  have hden : Real.log t - Real.log ℓ < 0 := sub_neg.mpr (lt_trans hlt hlt2)
  have hnum : Real.log c₀ - Real.log ℓ < 0 := sub_neg.mpr hlt2
  constructor
  · show 0 < (Real.log c₀ - Real.log ℓ) / (Real.log t - Real.log ℓ)
    exact div_pos_of_neg_of_neg hnum hden
  · show (Real.log c₀ - Real.log ℓ) / (Real.log t - Real.log ℓ) < 1
    rw [div_lt_iff_of_neg hden, one_mul]
    linarith

/-- At `t = c₀` the slice weight is `1`, i.e. the slice is the bottom face. -/
lemma sliceRho_eq_one {c₀ ℓ : ℝ} (hc₀ : 0 < c₀) (hℓ : 0 < ℓ) (h : c₀ ≠ ℓ) :
    sliceRho c₀ c₀ ℓ = 1 := by
  have hne : Real.log c₀ - Real.log ℓ ≠ 0 := fun hc =>
    h (Real.log_injOn_pos hc₀ hℓ (sub_eq_zero.mp hc))
  show (Real.log c₀ - Real.log ℓ) / (Real.log c₀ - Real.log ℓ) = 1
  exact div_self hne

/-- For `0 < t ≤ c₀ < ℓ` the slice weight lies in `[0,1]`. -/
lemma sliceRho_mem_Icc {c₀ t ℓ : ℝ} (ht : 0 < t) (htc₀ : t ≤ c₀) (hc₀ : 0 < c₀)
    (hℓ : 0 < ℓ) (hc₀ℓ : c₀ < ℓ) : sliceRho c₀ t ℓ ∈ Set.Icc (0 : ℝ) 1 := by
  rcases eq_or_lt_of_le htc₀ with h | h
  · subst h
    rw [sliceRho_eq_one hc₀ hℓ (ne_of_lt hc₀ℓ)]
    exact ⟨zero_le_one, le_refl 1⟩
  · exact ⟨(sliceRho_mem_Ioo ht hc₀ h hc₀ℓ).1.le, (sliceRho_mem_Ioo ht hc₀ h hc₀ℓ).2.le⟩

/-- The slice lift does not vanish, from the straight-line criterion at the weights in `[0,1]`. -/
lemma sliceLift_ne_zero {V W : Eucl 3} {ρ : ℝ} (hV : V ≠ 0) (hW : W ≠ 0)
    (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (hne : ∀ ρ' : ℝ, 0 ≤ ρ' → ρ' ≤ 1 → (1 - ρ') • V + ρ' • W ≠ 0) :
    (1 - ρ) • V + ρ • W ≠ 0 := by
  rcases eq_or_lt_of_le h0 with h | h
  · rw [← h, sub_zero, one_smul, zero_smul, add_zero]; exact hV
  · rcases eq_or_lt_of_le h1 with h' | h'
    · rw [h', sub_self, zero_smul, one_smul, zero_add]; exact hW
    · exact hne ρ h.le h'.le

/-- **The level-`c₀` slice of the interpolation sweep with bottom level `t`**, as a point of the
capping space. -/
noncomputable def sliceFamily (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hlt : c₁ < c₀)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (hc₀ℓ : c₀ < ℓ) (V W : Eucl 3) (hV : V ≠ 0) (hW : W ≠ 0)
    (hne : ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 → (1 - ρ) • V + ρ • W ≠ 0) (t : ℝ) : CappingSpace :=
  cappingVecPoint c₀ hc₀ (sliceLift c₀ (sliceLevel c₀ c₁ t) ℓ V W)
    (sliceLift_ne_zero hV hW
      (sliceRho_mem_Icc (lt_of_lt_of_le hc₁ (sliceLevel_mem_Icc hlt.le).1)
        (sliceLevel_mem_Icc hlt.le).2 hc₀ hℓ hc₀ℓ).1
      (sliceRho_mem_Icc (lt_of_lt_of_le hc₁ (sliceLevel_mem_Icc hlt.le).1)
        (sliceLevel_mem_Icc hlt.le).2 hc₀ hℓ hc₀ℓ).2 hne)

/-- **The slice family as a box map**: the level-`c₀` slice of the interpolation sweep whose bottom
level is driven from `c₀` (at `x 2 ≤ 0`, so that the family's face is the **linear plane**) to `c₁`
(at `x 2 ≥ 1`). -/
noncomputable def sliceFamilyBox (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hlt : c₁ < c₀)
    (ℓ : EuclideanSpace ℝ (Fin 2) → ℝ) (hℓ : ∀ y, 0 < ℓ y) (hℓc : ∀ y, c₀ < ℓ y)
    (V W : EuclideanSpace ℝ (Fin 2) → Eucl 3) (hV : ∀ y, V y ≠ 0) (hW : ∀ y, W y ≠ 0)
    (hne : ∀ (y : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), 0 ≤ ρ → ρ ≤ 1 →
      (1 - ρ) • V y + ρ • W y ≠ 0)
    (x : EuclideanSpace ℝ (Fin 3)) : CappingSpace :=
  sliceFamily c₀ c₁ hc₀ hc₁ hlt (ℓ (mk2 (x 0) (x 1))) (hℓ _) (hℓc _) (V _) (W _) (hV _) (hW _)
    (fun ρ h0 h1 => hne (mk2 (x 0) (x 1)) ρ h0 h1) (x 2)

/-- **The slice family is seam-invariant**: the seam involution acts on `ℓ` trivially and on the two
lifts by `-1`, hence on the slice lift by `-1` as well, and the level is the constant `c₀`.  This is the
seam condition of the level-engine for the bordism of `INTERP_DIAGONAL_NOTES.md` §5. -/
theorem sliceFamilyBox_seamInv (c₀ c₁ : ℝ) (hc₀ : 0 < c₀) (hc₁ : 0 < c₁) (hlt : c₁ < c₀)
    (ℓ : EuclideanSpace ℝ (Fin 2) → ℝ) (hℓ : ∀ y, 0 < ℓ y) (hℓc : ∀ y, c₀ < ℓ y)
    (V W : EuclideanSpace ℝ (Fin 2) → Eucl 3) (hV : ∀ y, V y ≠ 0) (hW : ∀ y, W y ≠ 0)
    (hne : ∀ (y : EuclideanSpace ℝ (Fin 2)) (ρ : ℝ), 0 ≤ ρ → ρ ≤ 1 →
      (1 - ρ) • V y + ρ • W y ≠ 0)
    (hℓs : ∀ y, onSeam2 y → ℓ (seamInv2 y) = ℓ y)
    (hVs : ∀ y, onSeam2 y → V (seamInv2 y) = - V y)
    (hWs : ∀ y, onSeam2 y → W (seamInv2 y) = - W y)
    (x : EuclideanSpace ℝ (Fin 3)) (hx : onSeam x) :
    sliceFamilyBox c₀ c₁ hc₀ hc₁ hlt ℓ hℓ hℓc V W hV hW hne (seamInv x)
      = sliceFamilyBox c₀ c₁ hc₀ hc₁ hlt ℓ hℓ hℓc V W hV hW hne x := by
  have hy : onSeam2 (mk2 (x 0) (x 1)) := onSeam2_of_onSeam x hx
  have hp : mk2 ((seamInv x) 0) ((seamInv x) 1) = seamInv2 (mk2 (x 0) (x 1)) := mk2_seamInv x
  have h2 : (seamInv x) 2 = x 2 := seamInv_apply_two x
  have hlift : sliceLift c₀ (sliceLevel c₀ c₁ ((seamInv x) 2)) (ℓ (mk2 ((seamInv x) 0) ((seamInv x) 1)))
        (V (mk2 ((seamInv x) 0) ((seamInv x) 1))) (W (mk2 ((seamInv x) 0) ((seamInv x) 1)))
      = - sliceLift c₀ (sliceLevel c₀ c₁ (x 2)) (ℓ (mk2 (x 0) (x 1)))
        (V (mk2 (x 0) (x 1))) (W (mk2 (x 0) (x 1))) := by
    simp only [hp, h2, hℓs _ hy, hVs _ hy, hWs _ hy, sliceLift, sliceRho, smul_neg, neg_add]
  unfold sliceFamilyBox sliceFamily
  exact cappingVecPoint_eq_of_class hc₀ _ _ (projectivizationMk_eq_of_eq_neg_vector hlift _ _)

end

end Work.Drive
