import Mathlib
import Submission.QuadrisecantCircle
import Submission.KnotMap

open scoped RealInnerProductSpace

noncomputable section

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# Quadrisecants as chords with two middle points

`HasQuadrisecant r` (four distinct parameters in one period with collinear
images) asks, in Kuperberg's geometric language, for a *secant with two
middle points*: a chord of the knot (two distinct parameters `a,b`) whose
open segment contains two further distinct knot points `z,w`.  This module
proves the equivalence

    hasQuadrisecant_iff_quadrisecantChord (h : IsSmoothKnot r) :
        HasQuadrisecant r ↔ QuadrisecantChord r

(`QuadrisecantChord r` = `∃ a b z w`, `QuadDistinct a b z w` with `z,w`
strictly between `a,b`).  The forward direction is immediate
(`quadrisecantChord_imp_circleQuadrisecant`): four strictly-collinear points
are collinear.  The converse is the elementary fact that among four
distinct collinear points, the two *extreme* ones form a chord containing the
other two strictly in its interior: coefficients `a₀..a₃` (pairwise
distinct, since the points are distinct and `v ≠ 0`) have a minimum and a
maximum index (`Finset.exists_min_image` / `exists_max_image` on
`Fin 4`), and every remaining index has coefficient strictly between them;
`mem_openSegment_affine_coeff` then witnesses strict betweenness on the
line `{p + s • v}`.
-/

section GenericAffine

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Cancellation of real coefficients on a nonzero vector (an inner-product
space over `ℝ` has no zero-scalar-divisors). -/
lemma coeff_eq_of_smul_eq_smul {a b : ℝ} {v : E} (hv : v ≠ 0)
    (h : a • v = b • v) : a = b := by
  have h' : (a - b) • v = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact h
  have hinner : inner ℝ ((a - b) • v) v = 0 := by simp [h']
  have hin : (a - b) * (inner ℝ v v) = 0 := by
    simpa [inner_smul_left] using hinner
  have hvv : inner ℝ v v ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hv)
  exact sub_eq_zero.mp ((mul_eq_zero.mp hin).resolve_right hvv)

/-- An affine point strictly between two affine points on a line, in terms of
coefficients: `lo < mid < hi` ⇒ `p + mid•v` lies in the open segment from
`p + lo•v` to `p + hi•v`. -/
lemma mem_openSegment_affine_coeff {p v : E} {lo mid hi : ℝ}
    (hlo : lo < mid) (hmid : mid < hi) :
    p + mid • v ∈ openSegment ℝ (p + lo • v) (p + hi • v) := by
  let a : ℝ := (hi - mid) / (hi - lo)
  let b : ℝ := (mid - lo) / (hi - lo)
  have hhi_lo : 0 < hi - lo := sub_pos.mpr (lt_trans hlo hmid)
  have ha0 : 0 < a := by unfold a; exact div_pos (sub_pos.mpr hmid) hhi_lo
  have hb0 : 0 < b := by unfold b; exact div_pos (sub_pos.mpr hlo) hhi_lo
  have hab : a + b = 1 := by
    unfold a b
    field_simp
    ring
  have hmid_scalar : a * lo + b * hi = mid := by
    unfold a b
    field_simp
    ring
  refine ⟨a, b, ha0, hb0, hab, ?_⟩
  calc
    a • (p + lo • v) + b • (p + hi • v) = (a + b) • p + (a * lo + b * hi) • v := by
      rw [smul_add, smul_add, smul_smul, smul_smul, add_smul, add_smul]
      abel
    _ = p + mid • v := by
      rw [hab, hmid_scalar]
      simp

/-- A convex combination of `A` and `B` with coefficients summing to one is
`B` shifted from `A` along the segment. -/
lemma smul_add_smul_eq_add_smul_sub {A B : E} {s t : ℝ} (hst : s + t = 1) :
    s • A + t • B = A + t • (B - A) := by
  calc
    s • A + t • B = (s + t) • A + t • (B - A) := by
      rw [add_smul, smul_sub]
      abel
    _ = A + t • (B - A) := by rw [hst]; simp

end GenericAffine

/-- Four pairwise distinct elements of a type are an injective function on
`Fin 4` (via `![x0, x1, x2, x3]`). -/
lemma fin4_injective_of_QuadDistinct {α : Type*} (x0 x1 x2 x3 : α)
    (h : QuadDistinct x0 x1 x2 x3) :
    Function.Injective (![x0, x1, x2, x3] : Fin 4 → α) := by
  rcases h with ⟨h01, h02, h03, h12, h13, h23⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp at hij ⊢
  all_goals
    first
    | rfl
    | contradiction
    | exact False.elim (h01 hij)
    | exact False.elim (h02 hij)
    | exact False.elim (h03 hij)
    | exact False.elim (h12 hij)
    | exact False.elim (h13 hij)
    | exact False.elim (h23 hij)
    | exact False.elim (h01 hij.symm)
    | exact False.elim (h02 hij.symm)
    | exact False.elim (h03 hij.symm)
    | exact False.elim (h12 hij.symm)
    | exact False.elim (h13 hij.symm)
    | exact False.elim (h23 hij.symm)

/-- Given two distinct indices of `Fin 4`, two further distinct indices
avoiding them exist. -/
lemma two_other_indices (imin imax : Fin 4) (hne : imin ≠ imax) :
    ∃ k1 k2 : Fin 4, k1 ≠ imin ∧ k1 ≠ imax ∧ k2 ≠ imin ∧ k2 ≠ imax ∧ k1 ≠ k2 := by
  let F : Finset (Fin 4) := (Finset.univ.erase imax).erase imin
  have himin_mem : imin ∈ (Finset.univ.erase imax : Finset (Fin 4)) := by
    rw [Finset.mem_erase]
    exact ⟨hne, by simp⟩
  have hcard1 : (Finset.univ.erase imax : Finset (Fin 4)).card = 3 := by
    rw [Finset.card_erase_of_mem (by simp : imax ∈ (Finset.univ : Finset (Fin 4)))]
    simp
  have hFcard : F.card = 2 := by
    unfold F
    rw [Finset.card_erase_of_mem himin_mem, hcard1]
  have hFne : F.Nonempty := (Finset.card_pos.mp (by rw [hFcard]; norm_num))
  let k1 : Fin 4 := F.min' hFne
  have hk1F : k1 ∈ F := Finset.min'_mem F hFne
  have hk1 : k1 ≠ imin ∧ k1 ≠ imax := by
    simpa [F, Finset.mem_erase] using hk1F
  have hF2ne : (F.erase k1).Nonempty :=
    (Finset.card_pos.mp (by rw [Finset.card_erase_of_mem hk1F, hFcard]; norm_num))
  let k2 : Fin 4 := (F.erase k1).min' hF2ne
  have hk2F : k2 ∈ F.erase k1 := Finset.min'_mem (F.erase k1) hF2ne
  have hk2mem : k2 ∈ F := (Finset.mem_erase.mp hk2F).2
  have hk2 : k2 ≠ imin ∧ k2 ≠ imax := by
    simpa [F, Finset.mem_erase] using hk2mem
  have hk2k1 : k1 ≠ k2 := (Finset.mem_erase.mp hk2F).1.symm
  exact ⟨k1, k2, hk1.1, hk1.2, hk2.1, hk2.2, hk2k1⟩

/-- `z` is a point of the knot lying strictly inside the chord with endpoints
`a b` (i.e. `knotMap r z` is strictly between `knotMap r a` and `knotMap r b`). -/
def IsMiddleOnChord (r : ℝ → Space) (a b z : AddCircle period) : Prop :=
  knotMap r z ∈ openSegment ℝ (knotMap r a) (knotMap r b)

/-- A *quadrisecant chord*: four pairwise-distinct parameters `a, b, z, w`
with `z` and `w` strictly inside the chord from `a` to `b` (Kuperberg's
"secant with two middle points"). -/
def QuadrisecantChord (r : ℝ → Space) : Prop :=
  ∃ a b z w : AddCircle period, QuadDistinct a b z w ∧
    IsMiddleOnChord r a b z ∧ IsMiddleOnChord r a b w

/-- A quadrisecant chord gives four collinear image points. -/
lemma quadrisecantChord_imp_circleQuadrisecant {r : ℝ → Space} (h : IsSmoothKnot r)
    (hq : QuadrisecantChord r) : CircleQuadrisecant r := by
  rcases hq with ⟨a, b, z, w, hd, hz, hw⟩
  let p : Space := knotMap r a
  let v : Space := knotMap r b - knotMap r a
  have hv : v ≠ 0 := by
    unfold v
    exact sub_ne_zero.mpr (by
      intro hba
      exact hd.1 ((knotMap_injective h) hba).symm)
  rcases hz with ⟨az, bz, haz0, hbz0, habz, hzeq⟩
  rcases hw with ⟨aw, bw, haw0, hbw0, habw, hweq⟩
  have hz_v : knotMap r z = p + bz • v := by
    calc
      knotMap r z = az • knotMap r a + bz • knotMap r b := hzeq.symm
      _ = knotMap r a + bz • (knotMap r b - knotMap r a) :=
        smul_add_smul_eq_add_smul_sub (E := Space) habz
      _ = p + bz • v := rfl
  have hw_v : knotMap r w = p + bw • v := by
    calc
      knotMap r w = aw • knotMap r a + bw • knotMap r b := hweq.symm
      _ = knotMap r a + bw • (knotMap r b - knotMap r a) :=
        smul_add_smul_eq_add_smul_sub (E := Space) habw
      _ = p + bw • v := rfl
  refine ⟨a, b, z, w, p, v, (0 : ℝ), (1 : ℝ), bz, bw, hd, hv, ?_, ?_, ?_, ?_⟩
  · simp [p]
  · simp [p, v]
  · exact hz_v
  · exact hw_v

/-- Four distinct collinear points of the knot contain two extremes whose
chord strictly contains the other two (i.e. a circle quadrisecant gives a
quadrisecant chord). -/
lemma circleQuadrisecant_imp_quadrisecantChord {r : ℝ → Space} (h : IsSmoothKnot r)
    (hq : CircleQuadrisecant r) : QuadrisecantChord r := by
  rcases hq with ⟨x0, x1, x2, x3, p, v, a0, a1, a2, a3, hd, hv,
    hi0, hi1, hi2, hi3⟩
  let xs : Fin 4 → AddCircle period := ![x0, x1, x2, x3]
  let as : Fin 4 → ℝ := ![a0, a1, a2, a3]
  have hcol : ∀ i : Fin 4, knotMap r (xs i) = p + (as i) • v := by
    intro i
    fin_cases i
    · simpa [xs, as] using hi0
    · simpa [xs, as] using hi1
    · simpa [xs, as] using hi2
    · simpa [xs, as] using hi3
  have hxs_inj : Function.Injective xs := by
    simpa [xs] using (fin4_injective_of_QuadDistinct x0 x1 x2 x3 hd)
  have hkm_inj : Function.Injective (knotMap r) := (knotMap_injective h)
  have has_inj : Function.Injective as := by
    intro i j hij
    apply hxs_inj
    apply hkm_inj
    calc
      knotMap r (xs i) = p + (as i) • v := hcol i
      _ = p + (as j) • v := by rw [hij]
      _ = knotMap r (xs j) := (hcol j).symm
  obtain ⟨imin, _, himin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin 4)) as (by simp)
  obtain ⟨imax, _, himax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin 4)) as (by simp)
  have himin_le : ∀ k : Fin 4, as imin ≤ as k := fun k => himin k (by simp)
  have himax_ge : ∀ k : Fin 4, as k ≤ as imax := fun k => himax k (by simp)
  have hne_im : imin ≠ imax := by
    intro h_eq
    have hall : ∀ k : Fin 4, as k = as imin := fun k =>
      le_antisymm (by simpa [h_eq] using himax_ge k) (himin_le k)
    have h01 : as 0 = as 1 := (hall 0).trans (hall 1).symm
    exact (by norm_num : (0 : Fin 4) ≠ (1 : Fin 4)) (has_inj h01)
  rcases two_other_indices imin imax hne_im with
    ⟨k1, k2, hk1im, hk1ax, hk2im, hk2ax, hk1k2⟩
  have hk1_between : as imin < as k1 ∧ as k1 < as imax := by
    constructor
    · have hle := himin_le k1
      have hne : as k1 ≠ as imin := fun hq => hk1im (has_inj hq)
      exact lt_of_le_of_ne hle (Ne.symm hne)
    · have hle := himax_ge k1
      have hne : as k1 ≠ as imax := fun hq => hk1ax (has_inj hq)
      exact lt_of_le_of_ne hle hne
  have hk2_between : as imin < as k2 ∧ as k2 < as imax := by
    constructor
    · have hle := himin_le k2
      have hne : as k2 ≠ as imin := fun hq => hk2im (has_inj hq)
      exact lt_of_le_of_ne hle (Ne.symm hne)
    · have hle := himax_ge k2
      have hne : as k2 ≠ as imax := fun hq => hk2ax (has_inj hq)
      exact lt_of_le_of_ne hle hne
  refine ⟨xs imax, xs imin, xs k1, xs k2, ?_, ?_, ?_⟩
  · have nemaxmin : xs imax ≠ xs imin := by intro hq; exact hne_im (hxs_inj hq).symm
    have nemaxk1 : xs imax ≠ xs k1 := by intro hq; exact hk1ax (hxs_inj hq).symm
    have nemaxk2 : xs imax ≠ xs k2 := by intro hq; exact hk2ax (hxs_inj hq).symm
    have nemink1 : xs imin ≠ xs k1 := by intro hq; exact hk1im (hxs_inj hq).symm
    have nemink2 : xs imin ≠ xs k2 := by intro hq; exact hk2im (hxs_inj hq).symm
    have nek1k2 : xs k1 ≠ xs k2 := by intro hq; exact hk1k2 (hxs_inj hq)
    exact ⟨nemaxmin, nemaxk1, nemaxk2, nemink1, nemink2, nek1k2⟩
  · unfold IsMiddleOnChord
    have hseg : p + (as k1) • v ∈ openSegment ℝ (p + (as imax) • v) (p + (as imin) • v) := by
      simpa [openSegment_symm] using
        (mem_openSegment_affine_coeff (E := Space) (p := p) (v := v)
          (lo := as imin) (mid := as k1) (hi := as imax) hk1_between.1 hk1_between.2)
    simpa [← hcol k1, ← hcol imax, ← hcol imin] using hseg
  · unfold IsMiddleOnChord
    have hseg : p + (as k2) • v ∈ openSegment ℝ (p + (as imax) • v) (p + (as imin) • v) := by
      simpa [openSegment_symm] using
        (mem_openSegment_affine_coeff (E := Space) (p := p) (v := v)
          (lo := as imin) (mid := as k2) (hi := as imax) hk2_between.1 hk2_between.2)
    simpa [← hcol k2, ← hcol imax, ← hcol imin] using hseg

/-- On the parameter circle, a quadrisecant is exactly a chord with two
middle points. -/
lemma circleQuadrisecant_iff_quadrisecantChord {r : ℝ → Space} (h : IsSmoothKnot r) :
    CircleQuadrisecant r ↔ QuadrisecantChord r :=
  ⟨circleQuadrisecant_imp_quadrisecantChord h, quadrisecantChord_imp_circleQuadrisecant h⟩

/-- `HasQuadrisecant r` (the trusted statement: four distinct parameters with
collinear images) is equivalent to the existence of a chord of the knot whose
interior contains two distinct knot points. -/
lemma hasQuadrisecant_iff_quadrisecantChord {r : ℝ → Space} (h : IsSmoothKnot r) :
    HasQuadrisecant r ↔ QuadrisecantChord r := by
  rw [hasQuadrisecant_iff_circle h]
  exact circleQuadrisecant_iff_quadrisecantChord h

end LeanEval.KnotTheory.Quadrisecant
