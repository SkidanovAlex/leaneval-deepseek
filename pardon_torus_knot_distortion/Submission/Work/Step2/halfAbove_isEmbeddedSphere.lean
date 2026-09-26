import Mathlib
import Submission.Work.Step2.Geometry
import Submission.Work.Step2.halfAbove_eq_frontier_upperBody
import Submission.Work.Topology.SphereSlicing.isEmbeddedSphere_BoxSphere

/-!
# Each half of Pardon's double bubble is an embedded sphere

Pardon's Step 2 replaces the box sphere `∂PBox s c σ` by the *double bubble* obtained by cutting
the sphere along the plane `{y (σ 2) = c (σ 2) + u}` and gluing in the flat disc
`cutDisc s c σ u`.  The two halves are `halfAbove s c σ u` (the closed upper cap glued to the
disc) and `halfBelow s c σ u`.

`halfAbove s c σ u` is the frontier of the solid *upper half-box*
`upperBody s c σ u = PBox s c σ ∩ {c (σ 2) + u < y (σ 2)}`
(`Work.Step2.halfAbove_eq_frontier_upperBody`), a convex body whose boundary is a topological
sphere.  Here we make that explicit: we build a continuous bijection of the unit sphere onto
`halfAbove`.

The construction is the "straightening" of the upper half-box in the `σ 2`-direction.  Writing
`B = boxSide 2 * s` (so that `|u| < B`, the hypothesis `hu`), the affine map

`bubbleShift B u t = u + (t + B) * ((B - u) / (2 * B))`

is the increasing bijection of `[-B, B]` onto `[u, B]`; it reparametrises the `σ 2`-coordinate
of the box sphere while all other coordinates are kept.  Its effect on `ℝ³` is the shear

`bubblePush B c σ u y = y + (bubbleShift B u (y (σ 2) - c (σ 2)) - (y (σ 2) - c (σ 2))) • e`,
`e = PiLp.single 2 (σ 2) 1`,

which is a continuous injection (indeed a homeomorphism of `ℝ³`) carrying the box sphere
`{boxNorm c σ · = s}` onto `halfAbove s c σ u`:

* `bubblePush_mem_halfAbove`: a point of the box sphere goes to a point of `halfAbove`;
* `bubblePull_mem_sphereSet` and `bubblePush_bubblePull`: every point of `halfAbove` is the image
  of the explicit point `bubblePull B c σ u w` (the inverse shear) of the box sphere.

Composing with the radial parametrisation `boxSpherePoint s c σ` of the box sphere
(`Work.Topology.SphereSlicing.isEmbeddedSphere_BoxSphere`) produces the required continuous
bijection of `Metric.sphere 0 1` onto `halfAbove s c σ u`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.Step2

noncomputable section

/-! ## The affine reparametrisation of the `σ 2`-coordinate -/

/-- The increasing affine bijection of `[-B, B]` onto `[u, B]` (`B > 0`, `|u| < B`): it is the
reparametrisation of the `σ 2`-coordinate which turns one half-box into a full box. -/
private def bubbleShift (B u t : ℝ) : ℝ := u + (t + B) * ((B - u) / (2 * B))

/-- The inverse reparametrisation: the increasing affine bijection of `[u, B]` onto `[-B, B]`. -/
private def bubbleShiftInv (B u t : ℝ) : ℝ := (t - u) * ((2 * B) / (B - u)) - B

/-- The shear of `ℝ³` induced by `bubbleShift` in the `σ 2`-direction: it moves `y` in the
`σ 2`-coordinate by the amount needed to send `y (σ 2) - c (σ 2)` to
`bubbleShift B u (y (σ 2) - c (σ 2))`, and fixes all other coordinates. -/
private def bubblePush (B : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (y : R3) : R3 :=
  y + (bubbleShift B u (y (σ 2) - c (σ 2)) - (y (σ 2) - c (σ 2))) •
    (PiLp.single 2 (σ 2) (1 : ℝ) : R3)

/-- The inverse shear of `bubblePush`: it sends `w (σ 2) - c (σ 2)` back to
`bubbleShiftInv B u (w (σ 2) - c (σ 2))`. -/
private def bubblePull (B : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (w : R3) : R3 :=
  w + (bubbleShiftInv B u (w (σ 2) - c (σ 2)) - (w (σ 2) - c (σ 2))) •
    (PiLp.single 2 (σ 2) (1 : ℝ) : R3)

/-! ## The two shears in coordinates -/

/-- Two points of `ℝ³` agree as soon as they agree in the three coordinates `σ i`. -/
private theorem eq_of_coord_eq {a b : R3} {σ : Equiv.Perm (Fin 3)}
    (h : ∀ i : Fin 3, a (σ i) = b (σ i)) : a = b := by
  ext j
  obtain ⟨i, rfl⟩ := σ.surjective j
  exact h i

private theorem bubblePush_apply_self (B : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (y : R3) :
    bubblePush B c σ u y (σ 2) = c (σ 2) + bubbleShift B u (y (σ 2) - c (σ 2)) := by
  simp only [bubblePush, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul,
    ↓reduceIte]
  ring

private theorem bubblePush_apply_of_ne (B : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (y : R3)
    {i : Fin 3} (hi : i ≠ 2) : bubblePush B c σ u y (σ i) = y (σ i) := by
  simp only [bubblePush, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul,
    Equiv.apply_eq_iff_eq, hi, ↓reduceIte, mul_zero, add_zero]

private theorem bubblePull_apply_self (B : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (w : R3) :
    bubblePull B c σ u w (σ 2) = w (σ 2) +
      (bubbleShiftInv B u (w (σ 2) - c (σ 2)) - (w (σ 2) - c (σ 2))) := by
  simp only [bubblePull, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul,
    ↓reduceIte, mul_one]

private theorem bubblePull_apply_of_ne (B : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (w : R3)
    {i : Fin 3} (hi : i ≠ 2) : bubblePull B c σ u w (σ i) = w (σ i) := by
  simp only [bubblePull, PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul,
    Equiv.apply_eq_iff_eq, hi, ↓reduceIte, mul_zero, add_zero]

/-- The `σ 2`-coordinate of `bubblePush B c σ u y`, as an affine function of the
`σ 2`-coordinate of `y`. -/
private theorem bubblePush_coord_sub (B : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (y : R3) :
    bubblePush B c σ u y (σ 2) - c (σ 2)
      = bubbleShift B u (y (σ 2) - c (σ 2)) := by
  rw [bubblePush_apply_self]; ring

private theorem bubblePull_coord_sub (B : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (w : R3) :
    bubblePull B c σ u w (σ 2) - c (σ 2)
      = bubbleShiftInv B u (w (σ 2) - c (σ 2)) := by
  rw [bubblePull_apply_self]; ring

/-! ## Continuity -/

private theorem continuous_bubblePush (B : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) :
    Continuous (bubblePush B c σ u) := by
  have hcoord : Continuous fun y : R3 => y (σ 2) :=
    PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2)
  have hshift : Continuous (bubbleShift B u) := by
    rw [show bubbleShift B u = fun t : ℝ => u + (t + B) * ((B - u) / (2 * B)) from rfl]
    fun_prop
  rw [show bubblePush B c σ u = fun y : R3 =>
      y + (bubbleShift B u (y (σ 2) - c (σ 2)) - (y (σ 2) - c (σ 2))) •
        (PiLp.single 2 (σ 2) (1 : ℝ) : R3) from rfl]
  exact continuous_id.add
    (((hshift.comp (hcoord.sub continuous_const)).sub (hcoord.sub continuous_const)).smul
      continuous_const)

/-! ## The affine reparametrisation -/

private theorem bubbleShift_neg (B u : ℝ) : bubbleShift B u (-B) = u := by simp [bubbleShift]

private theorem bubbleShift_self {B u : ℝ} (hB : B ≠ 0) : bubbleShift B u B = B := by
  rw [bubbleShift]; field_simp; ring

private theorem bubbleShift_bubbleShiftInv {B u t : ℝ} (hB : B ≠ 0) (hu : B - u ≠ 0) :
    bubbleShift B u (bubbleShiftInv B u t) = t := by
  rw [bubbleShift, bubbleShiftInv]; field_simp; ring

private theorem bubbleShiftInv_bubbleShift {B u t : ℝ} (hB : B ≠ 0) (hu : B - u ≠ 0) :
    bubbleShiftInv B u (bubbleShift B u t) = t := by
  rw [bubbleShift, bubbleShiftInv]; field_simp; ring

private theorem bubbleShift_inv_neg (B u : ℝ) : bubbleShiftInv B u u = -B := by
  simp [bubbleShiftInv]

private theorem bubbleShift_inv_self {B u : ℝ} (hu : B - u ≠ 0) : bubbleShiftInv B u B = B := by
  rw [bubbleShiftInv]; field_simp; ring

private theorem bubbleShift_injective {B u : ℝ} (hB : B ≠ 0) (hu : B - u ≠ 0) :
    Function.Injective (bubbleShift B u) :=
  Function.LeftInverse.injective (g := bubbleShiftInv B u)
    (fun t => bubbleShiftInv_bubbleShift (t := t) hB hu)

/-- `bubbleShift B u` maps `[-B, B]` into `[u, B]`. -/
private theorem bubbleShift_mem_Icc {B u t : ℝ} (hB : 0 < B) (hu : |u| < B) (ht : t ∈ Icc (-B) B) :
    bubbleShift B u t ∈ Icc u B := by
  obtain ⟨hu1, hu2⟩ := abs_lt.mp hu
  obtain ⟨ht1, ht2⟩ := ht
  have hk : 0 < (B - u) / (2 * B) := div_pos (by linarith) (by linarith)
  constructor
  · have : 0 ≤ (t + B) * ((B - u) / (2 * B)) := mul_nonneg (by linarith) hk.le
    rw [bubbleShift]; linarith
  · have h2 : (t + B) * ((B - u) / (2 * B)) ≤ B - u := by
      calc (t + B) * ((B - u) / (2 * B)) ≤ (2 * B) * ((B - u) / (2 * B)) :=
            mul_le_mul_of_nonneg_right (by linarith) hk.le
        _ = B - u := by field_simp
    rw [bubbleShift]; linarith

/-- `bubbleShiftInv B u` maps `[u, B]` into `[-B, B]`. -/
private theorem bubbleShiftInv_mem {B u t : ℝ} (hB : 0 < B) (hu : |u| < B) (ht : t ∈ Icc u B) :
    bubbleShiftInv B u t ∈ Icc (-B) B := by
  obtain ⟨hu1, hu2⟩ := abs_lt.mp hu
  obtain ⟨ht1, ht2⟩ := ht
  have hden : 0 < B - u := by linarith
  have hcoef : 0 < (2 * B) / (B - u) := div_pos (by linarith) hden
  have h0 : 0 ≤ (t - u) * ((2 * B) / (B - u)) := mul_nonneg (by linarith) hcoef.le
  have hle : (t - u) * ((2 * B) / (B - u)) ≤ 2 * B := by
    calc (t - u) * ((2 * B) / (B - u)) ≤ (B - u) * ((2 * B) / (B - u)) :=
          mul_le_mul_of_nonneg_right (by linarith) hcoef.le
      _ = 2 * B := by field_simp
  rw [bubbleShiftInv]
  constructor <;> linarith

/-! ## Elementary coordinate estimates for the box norm -/

/-- Each coordinate term of the box norm is bounded by the box norm. -/
private theorem boxNorm_ge_div (c : R3) (σ : Equiv.Perm (Fin 3)) (y : R3) (i : Fin 3) :
    |y (σ i) - c (σ i)| / Submission.boxSide i ≤ Submission.boxNorm c σ y := by
  rw [Submission.boxNorm]
  fin_cases i
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  · exact le_trans (le_max_right _ _) (le_max_left _ _)
  · exact le_max_right _ _

/-- A point whose three coordinate terms are bounded by `s` has box norm at most `s`. -/
private theorem boxNorm_le_of_forall (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) (y : R3)
    (h : ∀ i : Fin 3, |y (σ i) - c (σ i)| ≤ Submission.boxSide i * s) :
    Submission.boxNorm c σ y ≤ s := by
  rw [Submission.boxNorm, max_le_iff, max_le_iff]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [div_le_iff₀ (Submission.boxSide_pos 0)]; linarith [h 0]
  · rw [div_le_iff₀ (Submission.boxSide_pos 1)]; linarith [h 1]
  · rw [div_le_iff₀ (Submission.boxSide_pos 2)]; linarith [h 2]

/-- If the box norm of `y` is exactly `s`, one coordinate is binding. -/
private theorem exists_binding_of_boxNorm_eq (c : R3) (σ : Equiv.Perm (Fin 3)) (s : ℝ) (y : R3)
    (h : Submission.boxNorm c σ y = s) :
    ∃ i : Fin 3, |y (σ i) - c (σ i)| = Submission.boxSide i * s := by
  rw [Submission.boxNorm] at h
  rcases max_eq_iff.mp h with ⟨h1, -⟩ | ⟨h2, -⟩
  · rcases max_eq_iff.mp h1 with ⟨h0, -⟩ | ⟨h1', -⟩
    · refine ⟨0, ?_⟩
      rw [div_eq_iff (ne_of_gt (Submission.boxSide_pos 0))] at h0
      linarith [h0]
    · refine ⟨1, ?_⟩
      rw [div_eq_iff (ne_of_gt (Submission.boxSide_pos 1))] at h1'
      linarith [h1']
  · refine ⟨2, ?_⟩
    rw [div_eq_iff (ne_of_gt (Submission.boxSide_pos 2))] at h2
    linarith [h2]

/-! ## The two composites -/

/-- **The inverse of the shear composed with it is the identity.** -/
private theorem bubblePush_bubblePull (B : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ) (w : R3)
    (hB : B ≠ 0) (hu : B - u ≠ 0) :
    bubblePush B c σ u (bubblePull B c σ u w) = w := by
  apply eq_of_coord_eq (σ := σ)
  intro i
  by_cases hi : i = 2
  · subst hi
    rw [bubblePush_apply_self, bubblePull_coord_sub, bubbleShift_bubbleShiftInv hB hu]
    ring
  · rw [bubblePush_apply_of_ne B c σ u _ hi, bubblePull_apply_of_ne B c σ u w hi]

/-- **The shear is injective.** -/
private theorem bubblePush_injective {B : ℝ} (hB : B ≠ 0) {u : ℝ} (hu : B - u ≠ 0)
    (c : R3) (σ : Equiv.Perm (Fin 3)) :
    Function.Injective (bubblePush B c σ u) := by
  intro y y' h
  apply eq_of_coord_eq (σ := σ)
  intro i
  by_cases hi : i = 2
  · subst hi
    have h2 := congrArg (fun z : R3 => z (σ 2) - c (σ 2)) h
    rw [bubblePush_coord_sub, bubblePush_coord_sub] at h2
    have := bubbleShift_injective hB hu h2
    linarith
  · have h2 := congrArg (fun z : R3 => z (σ i)) h
    rwa [bubblePush_apply_of_ne B c σ u y hi, bubblePush_apply_of_ne B c σ u y' hi] at h2

/-! ## The shear carries the box sphere onto one half of the bubble -/

/-- **A point of the box sphere goes into `halfAbove`** under the shear.  The `σ 2`-coordinate is
reparametrised into `[c (σ 2) + u, c (σ 2) + B]`; if the point of the box sphere is *not* binding
in its `σ 2`-coordinate, that coordinate still binds, so the image is on the sphere part of
`halfAbove`, and if it is binding in the `σ 2`-coordinate then either the image is on the
sphere part (binding in `σ 2`, at `c (σ 2) + B`) or it lies on the cutting plane inside the open
box (at `c (σ 2) + u`), which is the flat part of `halfAbove`. -/
private theorem bubblePush_mem_halfAbove {s : ℝ} (hs : 0 < s) {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hu : |u| < Submission.boxSide 2 * s) {y : R3}
    (hy : y ∈ Work.BoxShrink.Core.sphereSet c σ s) :
    bubblePush (Submission.boxSide 2 * s) c σ u y ∈ halfAbove s c σ u := by
  have hB : 0 < Submission.boxSide 2 * s := mul_pos (Submission.boxSide_pos 2) hs
  have hy' : Submission.boxNorm c σ y = s := hy
  have htabs : |y (σ 2) - c (σ 2)| ≤ Submission.boxSide 2 * s :=
    abs_sub_le_of_boxNorm_le (le_of_eq hy') 2
  have htmem : y (σ 2) - c (σ 2) ∈
      Set.Icc (-(Submission.boxSide 2 * s)) (Submission.boxSide 2 * s) :=
    Set.mem_Icc.mpr (abs_le.mp htabs)
  have hgmem : bubbleShift (Submission.boxSide 2 * s) u (y (σ 2) - c (σ 2)) ∈
      Set.Icc u (Submission.boxSide 2 * s) := bubbleShift_mem_Icc hB hu htmem
  have hcoef : 0 < (Submission.boxSide 2 * s - u) / (2 * (Submission.boxSide 2 * s)) :=
    div_pos (by linarith [(abs_lt.mp hu).2]) (by linarith)
  have hdiff : bubbleShift (Submission.boxSide 2 * s) u (y (σ 2) - c (σ 2)) - u
      = ((y (σ 2) - c (σ 2)) + Submission.boxSide 2 * s)
        * ((Submission.boxSide 2 * s - u) / (2 * (Submission.boxSide 2 * s))) := by
    rw [bubbleShift]; ring
  have hcoord : ∀ i : Fin 3,
      |bubblePush (Submission.boxSide 2 * s) c σ u y (σ i) - c (σ i)|
        ≤ Submission.boxSide i * s := by
    intro i
    by_cases hi : i = 2
    · subst hi
      rw [bubblePush_apply_self]
      have h2 : |bubbleShift (Submission.boxSide 2 * s) u (y (σ 2) - c (σ 2))|
          ≤ Submission.boxSide 2 * s := by
        rw [abs_le]
        exact ⟨by linarith [hgmem.1, (abs_lt.mp hu).1], hgmem.2⟩
      simpa using h2
    · rw [bubblePush_apply_of_ne (Submission.boxSide 2 * s) c σ u y hi]
      exact abs_sub_le_of_boxNorm_le (le_of_eq hy') i
  have hle : Submission.boxNorm c σ (bubblePush (Submission.boxSide 2 * s) c σ u y) ≤ s :=
    boxNorm_le_of_forall c σ s _ hcoord
  have hge : c (σ 2) + u ≤ bubblePush (Submission.boxSide 2 * s) c σ u y (σ 2) := by
    rw [bubblePush_apply_self]; linarith [hgmem.1]
  have hkey : bubbleShift (Submission.boxSide 2 * s) u (y (σ 2) - c (σ 2)) ≠ u →
      Submission.boxNorm c σ (bubblePush (Submission.boxSide 2 * s) c σ u y) = s := by
    intro hgu
    refine le_antisymm hle ?_
    have hgt : u < bubbleShift (Submission.boxSide 2 * s) u (y (σ 2) - c (σ 2)) :=
      lt_of_le_of_ne hgmem.1 (Ne.symm hgu)
    have htk : 0 < (y (σ 2) - c (σ 2)) + Submission.boxSide 2 * s := by
      have hpos : 0 < ((y (σ 2) - c (σ 2)) + Submission.boxSide 2 * s)
          * ((Submission.boxSide 2 * s - u) / (2 * (Submission.boxSide 2 * s))) := by
        rw [← hdiff]; linarith
      by_contra hcon
      push Not at hcon
      have := mul_nonpos_of_nonpos_of_nonneg hcon hcoef.le
      linarith
    obtain ⟨i, hi⟩ := exists_binding_of_boxNorm_eq c σ s y hy'
    have hbind : |bubblePush (Submission.boxSide 2 * s) c σ u y (σ i) - c (σ i)|
        = Submission.boxSide i * s := by
      by_cases hi2 : i = 2
      · subst hi2
        rw [bubblePush_apply_self]
        have htB : y (σ 2) - c (σ 2) = Submission.boxSide 2 * s := by
          rcases eq_or_eq_neg_of_abs_eq hi with h | h
          · exact h
          · linarith
        rw [htB, bubbleShift_self (ne_of_gt hB),
          show c (σ 2) + Submission.boxSide 2 * s - c (σ 2) = Submission.boxSide 2 * s by ring,
          abs_of_pos hB]
      · rw [bubblePush_apply_of_ne (Submission.boxSide 2 * s) c σ u y hi2]; exact hi
    have hdiv : |bubblePush (Submission.boxSide 2 * s) c σ u y (σ i) - c (σ i)|
          / Submission.boxSide i = s := by
      rw [hbind, mul_div_cancel_left₀ s (ne_of_gt (Submission.boxSide_pos i))]
    have hb := boxNorm_ge_div c σ (bubblePush (Submission.boxSide 2 * s) c σ u y) i
    rw [hdiv] at hb
    exact hb
  rw [mem_halfAbove]
  rcases lt_or_ge (Submission.boxNorm c σ (bubblePush (Submission.boxSide 2 * s) c σ u y)) s with
    hlt | hge'
  · refine Or.inr ⟨(Submission.mem_PBox_iff s c σ _).mpr hlt, ?_⟩
    have hgu : bubbleShift (Submission.boxSide 2 * s) u (y (σ 2) - c (σ 2)) = u := by
      by_contra hne
      exact absurd (hkey hne) (ne_of_lt hlt)
    rw [bubblePush_apply_self, hgu]
  · exact Or.inl ⟨le_antisymm hle hge', hge⟩

/-- **Every point of `halfAbove` has its inverse shear on the box sphere.**  This is the converse
of `bubblePush_mem_halfAbove`: the inverse shear reparametrises the `σ 2`-coordinate back into
`[-B, B]` and all the other coordinates are kept, so the result is on the box sphere because
`w` itself is on the closed box, and some coordinate of `w` is binding on the sphere part of
`halfAbove` (or, on the flat part, the `σ 2`-coordinate `u` is sent to `c (σ 2) - B`). -/
private theorem bubblePull_mem_sphereSet {s : ℝ} (hs : 0 < s) {c : R3} {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hu : |u| < Submission.boxSide 2 * s) {w : R3} (hw : w ∈ halfAbove s c σ u) :
    bubblePull (Submission.boxSide 2 * s) c σ u w ∈ Work.BoxShrink.Core.sphereSet c σ s := by
  have hB : 0 < Submission.boxSide 2 * s := mul_pos (Submission.boxSide_pos 2) hs
  obtain ⟨hu1, hu2⟩ := abs_lt.mp hu
  have hwle : Submission.boxNorm c σ w ≤ s := by
    rcases (mem_halfAbove.mp hw) with ⟨heq, -⟩ | ⟨hbox, -⟩
    · exact le_of_eq heq
    · exact le_of_lt ((Submission.mem_PBox_iff s c σ w).mp hbox)
  have htmem : w (σ 2) - c (σ 2) ∈ Set.Icc u (Submission.boxSide 2 * s) := by
    refine Set.mem_Icc.mpr ⟨?_, ?_⟩
    · rcases (mem_halfAbove.mp hw) with ⟨-, hle⟩ | ⟨-, heq⟩
      · linarith
      · linarith
    · linarith [le_abs_self (w (σ 2) - c (σ 2)), abs_sub_le_of_boxNorm_le hwle 2]
  have hinv := bubbleShiftInv_mem hB hu htmem
  have hcoord : ∀ i : Fin 3,
      |bubblePull (Submission.boxSide 2 * s) c σ u w (σ i) - c (σ i)|
        ≤ Submission.boxSide i * s := by
    intro i
    by_cases hi : i = 2
    · subst hi
      rw [bubblePull_coord_sub]
      exact abs_le.mpr hinv
    · rw [bubblePull_apply_of_ne (Submission.boxSide 2 * s) c σ u w hi]
      exact abs_sub_le_of_boxNorm_le hwle i
  refine le_antisymm (boxNorm_le_of_forall c σ s _ hcoord) ?_
  by_cases hcase : Submission.boxNorm c σ w = s
  · obtain ⟨i, hi⟩ := exists_binding_of_boxNorm_eq c σ s w hcase
    have hbind : |bubblePull (Submission.boxSide 2 * s) c σ u w (σ i) - c (σ i)|
        = Submission.boxSide i * s := by
      by_cases hi2 : i = 2
      · subst hi2
        rw [bubblePull_coord_sub]
        have htB : w (σ 2) - c (σ 2) = Submission.boxSide 2 * s := by
          rcases eq_or_eq_neg_of_abs_eq hi with h | h
          · exact h
          · linarith [htmem.1]
        rw [htB, bubbleShift_inv_self (by linarith : Submission.boxSide 2 * s - u ≠ 0),
          abs_of_pos hB]
      · rw [bubblePull_apply_of_ne (Submission.boxSide 2 * s) c σ u w hi2]; exact hi
    have hdiv : |bubblePull (Submission.boxSide 2 * s) c σ u w (σ i) - c (σ i)|
          / Submission.boxSide i = s := by
      rw [hbind, mul_div_cancel_left₀ s (ne_of_gt (Submission.boxSide_pos i))]
    have hb := boxNorm_ge_div c σ (bubblePull (Submission.boxSide 2 * s) c σ u w) i
    rw [hdiv] at hb
    exact hb
  · have ht_eq : w (σ 2) - c (σ 2) = u := by
      rcases (mem_halfAbove.mp hw) with ⟨heq, -⟩ | ⟨-, heq⟩
      · exact absurd heq hcase
      · linarith
    have hbind : |bubblePull (Submission.boxSide 2 * s) c σ u w (σ 2) - c (σ 2)|
        = Submission.boxSide 2 * s := by
      rw [bubblePull_coord_sub, ht_eq, bubbleShift_inv_neg, abs_neg, abs_of_pos hB]
    have hdiv : |bubblePull (Submission.boxSide 2 * s) c σ u w (σ 2) - c (σ 2)|
          / Submission.boxSide 2 = s := by
      rw [hbind, mul_div_cancel_left₀ s (ne_of_gt (Submission.boxSide_pos 2))]
    have hb := boxNorm_ge_div c σ (bubblePull (Submission.boxSide 2 * s) c σ u w) 2
    rw [hdiv] at hb
    exact hb

/-- **The shear carries the box sphere exactly onto one half of the bubble.** -/
private theorem bubblePush_image_sphereSet {s : ℝ} (hs : 0 < s) {c : R3} {σ : Equiv.Perm (Fin 3)}
    {u : ℝ} (hu : |u| < Submission.boxSide 2 * s) :
    bubblePush (Submission.boxSide 2 * s) c σ u '' Work.BoxShrink.Core.sphereSet c σ s =
      halfAbove s c σ u := by
  have hB : 0 < Submission.boxSide 2 * s := mul_pos (Submission.boxSide_pos 2) hs
  apply Set.Subset.antisymm
  · rintro z ⟨y, hy, rfl⟩
    exact bubblePush_mem_halfAbove hs hu hy
  · intro w hw
    exact ⟨bubblePull (Submission.boxSide 2 * s) c σ u w, bubblePull_mem_sphereSet hs hu hw,
      bubblePush_bubblePull _ _ _ _ _ (ne_of_gt hB) (by linarith [(abs_lt.mp hu).2])⟩

/-! ## The half of the double bubble is an embedded sphere -/

theorem halfAbove_isEmbeddedSphere {s : ℝ} (hs : 0 < s) (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) {u : ℝ}
    (hu : |u| < Submission.boxSide 2 * s) :
    Work.InnermostDisk.IsEmbeddedSphere (Work.Step2.halfAbove s c σ u) := by
  have hB : 0 < Submission.boxSide 2 * s := mul_pos (Submission.boxSide_pos 2) hs
  have hrange : Set.range (Work.Topology.SphereSlicing.boxSpherePoint s c σ) =
      Work.BoxShrink.Core.sphereSet c σ s := by
    ext y
    constructor
    · rintro ⟨w, rfl⟩
      exact Work.Topology.SphereSlicing.boxSpherePoint_mem hs c σ w
    · intro hy
      exact Work.Topology.SphereSlicing.boxSpherePoint_surjective hs c σ y hy
  let e : C(Metric.sphere (0 : R3) 1, R3) :=
    { toFun := fun w => bubblePush (Submission.boxSide 2 * s) c σ u
        (Work.Topology.SphereSlicing.boxSpherePoint s c σ w)
      continuous_toFun := (continuous_bubblePush (Submission.boxSide 2 * s) c σ u).comp
        (Work.Topology.SphereSlicing.continuous_boxSpherePoint s c σ) }
  refine ⟨e, ?_, ?_⟩
  · intro w w' h
    exact Work.Topology.SphereSlicing.boxSpherePoint_injective hs c σ
      (bubblePush_injective (ne_of_gt hB) (by linarith [(abs_lt.mp hu).2]) c σ h)
  · show Set.range (fun w => bubblePush (Submission.boxSide 2 * s) c σ u
        (Work.Topology.SphereSlicing.boxSpherePoint s c σ w)) = halfAbove s c σ u
    rw [show Set.range (fun w => bubblePush (Submission.boxSide 2 * s) c σ u
          (Work.Topology.SphereSlicing.boxSpherePoint s c σ w))
        = bubblePush (Submission.boxSide 2 * s) c σ u ''
          Set.range (Work.Topology.SphereSlicing.boxSpherePoint s c σ) from
        Set.range_comp (g := bubblePush (Submission.boxSide 2 * s) c σ u)
          (f := Work.Topology.SphereSlicing.boxSpherePoint s c σ)]
    rw [hrange, bubblePush_image_sphereSet hs hu]

end

end Work.Step2
