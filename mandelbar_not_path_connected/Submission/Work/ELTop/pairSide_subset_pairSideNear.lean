/-
# `Work.ELTop.pairSide_subset_pairSideNear`

Two co-landing pairs `P`, `Q` of external rays of the dynamical plane whose *curves* are disjoint
and whose arcs stand in the relation "the far arc of `P` is contained in the near arc of `Q`"
satisfy `pairSide P ⊆ pairSideNear Q`: the far side of `P` lies in the near side of `Q`.

## The plan

`pairSide P = connectedComponentIn (pairCurve P)ᶜ rf` and
`pairSideNear Q = connectedComponentIn (pairCurve Q)ᶜ rnQ` are *components* of the complements of
the two pair curves, so they are open and preconnected.

* The reference point `rf` of the far side of `P` has external angle `mf` in the far arc of `P`;
  by hypothesis that angle lies in the near arc of `Q`, whence `rf ∈ pairSideNear Q`
  (`Work.ELTop.paramRay_subset_pairSideNear`).
* It remains to see that `pairSide P` does not meet the curve `pairCurve Q`.  The points of
  `pairCurve Q` which could meet it are the two rays `R(Q.a)`, `R(Q.b)` — both contained in the
  near side `pairSideNear P`, since `Q.a` and `Q.b` lie in the near arc of `P` — and the landing
  point `Q.y`, which does not lie in `pairSide P` either: the ray `R(Q.a)` converges to it inside
  `pairSideNear P`, and the two sides of `P` are disjoint.
* The disjointness of the two sides of `P` is the plane topology of the truncated Jordan curve
  `polyCurve [P] R` at a level `R` above the maximum of the potential on a hypothetical path
  (`pairSide_disjoint_aux`).

Everything is reduced to the *normalized* pair `P₁` with `P₁.b = P.a + arcLen P.a P.b`
(`1`-periodicity of the rays), for which the two arcs of the `InArc` predicate are the honest
intervals `(P.a, P.b)` and `(P.b, P.a + 1)`.

## Main statements

* `Work.ELTop.InArc_or_InArc_near_aux`, `Work.ELTop.InArc_right_add_int` : angle arithmetic;
* `Work.ELTop.isPreconnected_paramRay_aux` : a ray is preconnected;
* `Work.ELTop.rayPt_notMem_polyCurve_farArc`, `..._nearArc` : angle/level data decide membership
  in the lollipop `polyCurve [P] R`;
* `Work.ELTop.pairSide_disjoint_aux` : the two sides of a nondegenerate pair are disjoint;
* `Work.ELTop.pairSide_subset_pairSideNear` : the main theorem.
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.PolyCurve.Blocks
import Submission.Work.ELTop.mem_pairSideNear_of_nearArc
import Submission.Work.ELTop.paramRay_subset_pairSide
import Submission.Work.ELTop.paramRay_subset_pairSideNear
import Submission.Work.ELTop.isOpen_pairSide
import Submission.Work.ELTop.polyCurve_isJordan
import Submission.Work.ELTop.polyRegion_eq_sides_I
import Submission.Work.ELTop.rayPt_add_int
import Submission.Work.Top.Jordan
import Submission.Work.Top.paramRay_unbounded
import Submission.Work.Top.continuousOn_rayPt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELTop

open Work.EL

/-! ## Angle arithmetic -/

/-- The predicate `InArc` is invariant under an integer translation of the *right* endpoint:
the angles `b` and `b + 1` represent the same point of the circle. -/
theorem InArc_right_add_int (x a b : ℝ) (m : ℤ) :
    Work.EL.InArc x a (b + (m : ℝ)) ↔ Work.EL.InArc x a b := by
  unfold Work.EL.InArc Work.EL.arcLen
  rw [show b + (m : ℝ) - a = (b - a) + (m : ℝ) by ring, Int.fract_add_intCast]

/-- The predicate `InArc` is invariant under an integer translation of the angle. -/
theorem InArc_left_add_int (x a b : ℝ) (m : ℤ) :
    Work.EL.InArc (x + (m : ℝ)) a b ↔ Work.EL.InArc x a b := by
  unfold Work.EL.InArc
  rw [show x + (m : ℝ) - a = (x - a) + (m : ℝ) by ring, Int.fract_add_intCast]

/-- **The two cyclic arcs cut the circle.**  If `a < b < a + 1` then every angle which is
congruent modulo `ℤ` to neither endpoint lies in the open arc `(a, b)` or in the open arc
`(b, a + 1)`. -/
theorem InArc_or_InArc_near_aux {a b θ : ℝ} (hab : a < b) (hb1 : b < a + 1)
    (h1 : ∀ k : ℤ, θ ≠ a + (k : ℝ)) (h2 : ∀ k : ℤ, θ ≠ b + (k : ℝ)) :
    Work.EL.InArc θ a b ∨ Work.EL.InArc θ b (a + 1) := by
  have hℓa : Work.EL.arcLen a b = b - a :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hℓb : Work.EL.arcLen b (a + 1) = a + 1 - b :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have hfr_ne : Int.fract (θ - a) ≠ 0 := by
    intro h0
    obtain ⟨z, hz⟩ := Set.mem_range.mp (Int.fract_eq_zero_iff.mp h0)
    exact h1 z (by linarith)
  have hfr_pos : 0 < Int.fract (θ - a) := lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm hfr_ne)
  have hfr_lt : Int.fract (θ - a) < 1 := Int.fract_lt_one _
  have hkey : θ - b = (Int.fract (θ - a) - (b - a)) + ((⌊θ - a⌋ : ℤ) : ℝ) := by
    have h := Int.fract_add_floor (θ - a)
    linarith
  rcases lt_trichotomy (Int.fract (θ - a)) (b - a) with hlt | heq | hgt
  · exact Or.inl ⟨hfr_pos, by rw [hℓa]; exact hlt⟩
  · exfalso
    have hb' : Int.fract (θ - b) = 0 := by
      rw [hkey, Int.fract_add_intCast, heq, sub_self, Int.fract_zero]
    obtain ⟨z, hz⟩ := Set.mem_range.mp (Int.fract_eq_zero_iff.mp hb')
    exact h2 z (by linarith)
  · have hfrb : Int.fract (θ - b) = Int.fract (θ - a) - (b - a) := by
      rw [hkey, Int.fract_add_intCast]
      exact Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    exact Or.inr ⟨by rw [hfrb]; linarith, by rw [hfrb, hℓb]; linarith⟩

/-! ## Rays and rays points -/

/-- The landing point of a ray belongs to the pair curve of its own pair. -/
theorem self_mem_pairCurve_aux {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (P : Work.EL.CoPair hN) : P.y ∈ Work.EL.pairCurve P :=
  (Work.EL.mem_pairCurve_iff P P.y).mpr (Or.inr (Or.inl rfl))

/-- A parameter ray is preconnected: it is the image of the interval `(1, ∞)` under
`t ↦ rayPt hN θ t`. -/
theorem isPreconnected_paramRay_aux {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (θ : ℝ) :
    IsPreconnected (Work.EL.paramRay hN θ) := by
  have heq : Work.EL.paramRay hN θ = (fun t : ℝ => Work.EL.rayPt hN θ t) '' Set.Ioi 1 := by
    ext z
    rw [Work.Top.NakaneData.mem_paramRay_iff]
    constructor
    · rintro ⟨hzK, t, ht, hΦ⟩
      exact ⟨t, ht, (hN.injOn_Phi hzK (Work.EL.rayPt_notMem_K hN ht)
        (by rw [hΦ, Work.Top.NakaneData.Phi_rayPt hN ht])).symm⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨Work.EL.rayPt_notMem_K hN ht, t, ht, Work.Top.NakaneData.Phi_rayPt hN ht⟩
  rw [heq]
  exact IsPreconnected.image isPreconnected_Ioi _ (Work.Top.continuousOn_rayPt hN θ)

/-- If two pairs have disjoint curves, then no ray of the one is a `1`-periodic translate of a
ray of the other. -/
theorem ne_congr_of_disjoint {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (P Q : Work.EL.CoPair hN)
    (hdisj : Disjoint (Work.EL.pairCurve P) (Work.EL.pairCurve Q)) {α β : ℝ}
    (hα : Work.EL.paramRay hN α ⊆ Work.EL.pairCurve P)
    (hβ : Work.EL.paramRay hN β ⊆ Work.EL.pairCurve Q) :
    ∀ m : ℤ, α ≠ β + (m : ℝ) := by
  intro m h
  have h1 : Work.EL.rayPt hN α 2 ∈ Work.EL.pairCurve P :=
    hα (Work.EL.rayPt_mem_paramRay hN (by norm_num))
  have h2 : Work.EL.rayPt hN α 2 ∈ Work.EL.pairCurve Q := by
    have hp : Work.EL.paramRay hN α = Work.EL.paramRay hN β := by
      rw [h]
      exact paramRay_add_int hN β m
    have hmem : Work.EL.rayPt hN α 2 ∈ Work.EL.paramRay hN β := by
      rw [← hp]
      exact Work.EL.rayPt_mem_paramRay hN (by norm_num)
    exact hβ hmem
  exact (Set.disjoint_left.mp hdisj) h1 h2

/-! ## The lollipop `polyCurve [P] R` -/

/-- **A ray point whose angle lies in the far arc of `P` never lies on the lollipop
`polyCurve [P] R`.**

It is not the landing point (which is in the filled Julia set, while a ray point is not), it lies
on neither ray piece (its angle is congruent to neither `P.a` nor `P.b`, because it lies strictly
inside the cyclic arc `(P.a, P.b)`), and it is not on the equipotential part: that part consists
of the points `rayPt θ R` whose angle avoids the far arc, while two ray points are equal only if
their levels agree and their angles are congruent modulo `1`. -/
theorem rayPt_notMem_polyCurve_farArc {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) {θ t R : ℝ} (hR : 1 < R) (ht : 1 < t)
    (hfar : Work.EL.InArc θ P.a P.b) :
    Work.EL.rayPt hN θ t ∉ Work.EL.polyCurve [P] R := by
  intro hmem
  have hne_a : ∀ k : ℤ, θ ≠ P.a + (k : ℝ) := by
    intro k hk
    have h0 : Int.fract (θ - P.a) = 0 := by
      rw [show θ - P.a = ((k : ℤ) : ℝ) by linarith]
      simp
    linarith [hfar.1, h0]
  have hne_b : ∀ k : ℤ, θ ≠ P.b + (k : ℝ) := by
    intro k hk
    have h0 : Int.fract (θ - P.a) = Int.fract (P.b - P.a) := by
      rw [show θ - P.a = (P.b - P.a) + (k : ℝ) by linarith, Int.fract_add_intCast]
    have hf : Int.fract (θ - P.a) < Int.fract (P.b - P.a) := hfar.2
    rw [h0] at hf
    exact absurd hf (lt_irrefl _)
  rw [Work.EL.polyCurve, Set.mem_ofPred_eq] at hmem
  rcases hmem with ⟨Q, hQ, hy | ha | hb⟩ | ⟨θ', hθ', hfar', hθeq⟩
  · simp only [List.mem_singleton] at hQ
    rw [hQ] at hy
    exact Work.EL.rayPt_notMem_K hN ht (hy ▸ landsN_mem_K hN P.lands_a)
  · simp only [List.mem_singleton] at hQ
    rw [hQ] at ha
    exact notMem_paramRay_of_ne_int hN hne_a ht
      (Work.Top.NakaneData.rayPiece_subset_paramRay ha)
  · simp only [List.mem_singleton] at hQ
    rw [hQ] at hb
    exact notMem_paramRay_of_ne_int hN hne_b ht
      (Work.Top.NakaneData.rayPiece_subset_paramRay hb)
  · obtain ⟨-, ⟨k, hk⟩⟩ := (rayPt_eq_iff hN ht hR).mp hθeq
    have hIn : Work.EL.InArc (θ + (k : ℝ)) P.a P.b := (InArc_left_add_int θ P.a P.b k).mpr hfar
    rw [hk] at hfar'
    exact (hfar' P (by simp)) hIn

/-- **A ray point of a level `t ≠ R` whose angle is congruent to neither `P.a` nor `P.b` never
lies on the lollipop `polyCurve [P] R`.**  (The angle need not lie in the near arc: only the
equipotential part of the lollipop, at level exactly `R`, is excluded by the level hypothesis.) -/
theorem rayPt_notMem_polyCurve_nearArc {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) {θ t R : ℝ} (hR : 1 < R) (ht : 1 < t)
    (hne_a : ∀ k : ℤ, θ ≠ P.a + (k : ℝ)) (hne_b : ∀ k : ℤ, θ ≠ P.b + (k : ℝ))
    (htR : t ≠ R) : Work.EL.rayPt hN θ t ∉ Work.EL.polyCurve [P] R := by
  intro hmem
  rw [Work.EL.polyCurve, Set.mem_ofPred_eq] at hmem
  rcases hmem with ⟨Q, hQ, hy | ha | hb⟩ | ⟨θ', hθ', hfar', hθeq⟩
  · simp only [List.mem_singleton] at hQ
    rw [hQ] at hy
    exact Work.EL.rayPt_notMem_K hN ht (hy ▸ landsN_mem_K hN P.lands_a)
  · simp only [List.mem_singleton] at hQ
    rw [hQ] at ha
    exact notMem_paramRay_of_ne_int hN hne_a ht
      (Work.Top.NakaneData.rayPiece_subset_paramRay ha)
  · simp only [List.mem_singleton] at hQ
    rw [hQ] at hb
    exact notMem_paramRay_of_ne_int hN hne_b ht
      (Work.Top.NakaneData.rayPiece_subset_paramRay hb)
  · exact htR (rayPt_eq_iff hN ht hR |>.mp hθeq).1

/-- The single-pair list is admissible. -/
theorem polyAdmissible_singleton_aux {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (P : Work.EL.CoPair hN) (hab : P.a < P.b) (hb1 : P.b < P.a + 1) :
    Work.EL.PolyAdmissible [P] := by
  have hcyc : Work.EL.CyclicStrict [P.a, P.b] := by
    refine ⟨by simp, ?_, ?_⟩
    · rw [List.pairwise_cons]
      refine ⟨?_, by simp⟩
      intro y hy
      rw [List.mem_singleton] at hy
      rw [hy]
      exact hab
    · intro x hx
      have hx' : x = P.a ∨ x = P.b := by simpa using hx
      have hhead : ([P.a, P.b] : List ℝ).headD 0 = P.a := rfl
      rw [hhead]
      rcases hx' with rfl | rfl <;> linarith
  refine ⟨by simp, ?_, ?_⟩
  · have hflat : ([P].flatMap fun Q : Work.EL.CoPair hN => [Q.a, Q.b]) = [P.a, P.b] := by simp
    rw [hflat]
    exact hcyc
  · rw [List.pairwise_cons]
    exact ⟨fun b hb => absurd hb (by simp), by simp⟩

/-! ## The two sides of a nondegenerate pair are disjoint -/

/-- **The two sides of a nondegenerate co-landing pair are disjoint.**

Both are components of `(pairCurve P)ᶜ`, through the ray points of level `2` at the middles `mf`
of the far arc and `mn` of the near arc.  If they met, those two points would be joined by a path
inside `(pairCurve P)ᶜ`.  Truncating the pair curve at a level `R` above the maximum of the
potential on the path, and closing it by the equipotential arc over the near arc, gives a Jordan
curve `polyCurve [P] R`.  The path misses it, but the two points lie in different sides of it:
`mf` is an angle of the *far* arc, so the whole ray `R(mf)` is an unbounded preconnected subset
of the complement of the lollipop, hence lies in the unbounded side, while the ray `R(mn)` at
level `2` is joined to the reference point of the polygon region by a ray piece which misses the
lollipop, hence lies in the bounded side. -/
theorem pairSide_disjoint_aux {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (P : Work.EL.CoPair hN) (hab : P.a < P.b) (hb1 : P.b < P.a + 1) :
    Disjoint (Work.EL.pairSide P) (Work.EL.pairSideNear P) := by
  classical
  have harc : Work.EL.arcLen P.a P.b = P.b - P.a :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  have harcn : Work.EL.arcLen P.b P.a = P.a + 1 - P.b :=
    Int.fract_eq_iff.mpr ⟨by linarith, by linarith, ⟨-1, by push_cast; ring⟩⟩
  set mf : ℝ := P.a + Work.EL.arcLen P.a P.b / 2 with hmf
  set mn : ℝ := P.b + Work.EL.arcLen P.b P.a / 2 with hmn
  have hL1 : Work.EL.arcLen P.a P.b < 1 := Work.EL.arcLen_lt_one P.a P.b
  have hmf_gt : P.a < mf := by rw [hmf, harc]; linarith
  have hmf_lt : mf < P.a + 1 := by rw [hmf, harc]; linarith
  have hmf_gt_b : P.b - 1 < mf := by rw [hmf, harc]; linarith
  have hmf_lt_b : mf < P.b := by rw [hmf, harc]; linarith
  have hmn_gt : P.b < mn := by rw [hmn, harcn]; linarith
  have hmn_lt : mn < P.b + 1 := by rw [hmn, harcn]; linarith
  have hmn_ga : P.a < mn := by rw [hmn, harcn]; linarith
  have hmn_la : mn < P.a + 1 := by rw [hmn, harcn]; linarith
  have hmf_InArc : Work.EL.InArc mf P.a P.b := by
    have hsub : mf - P.a = Work.EL.arcLen P.a P.b / 2 := by rw [hmf]; ring
    have h1 : 0 < Work.EL.arcLen P.a P.b / 2 := by rw [harc]; linarith
    have h2 : Work.EL.arcLen P.a P.b / 2 < 1 := by linarith
    rw [Work.EL.InArc, hsub, Int.fract_eq_self.mpr ⟨le_of_lt h1, h2⟩]
    exact ⟨h1, by rw [harc]; linarith⟩
  have hmn_nInArc : ¬ Work.EL.InArc mn P.a P.b := by
    intro h
    have hf : Int.fract (mn - P.a) = mn - P.a := Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have h2 : Int.fract (mn - P.a) < Int.fract (P.b - P.a) := h.2
    have hfr2 : Int.fract (P.b - P.a) = P.b - P.a :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    rw [hf, hfr2] at h2
    linarith
  have hmf_ne_a : ∀ k : ℤ, mf ≠ P.a + (k : ℝ) := fun k => unitIoo_ne_add_int hmf_gt hmf_lt k
  have hmf_ne_b : ∀ k : ℤ, mf ≠ P.b + (k : ℝ) := by
    intro k hk
    have h := unitIoo_ne_add_int (a := P.b - 1) hmf_gt_b (by linarith : mf < P.b - 1 + 1)
      (k + 1)
    exact h (by push_cast at hk ⊢; linarith)
  have hmn_ne_a : ∀ k : ℤ, mn ≠ P.a + (k : ℝ) := fun k => unitIoo_ne_add_int hmn_ga hmn_la k
  have hmn_ne_b : ∀ k : ℤ, mn ≠ P.b + (k : ℝ) := fun k => unitIoo_ne_add_int hmn_gt hmn_lt k
  set rf : ℂ := Work.EL.rayPt hN mf 2 with hrf
  set rn : ℂ := Work.EL.rayPt hN mn 2 with hrn
  have hrf_notmem : rf ∉ Work.EL.pairCurve P := by
    rw [Work.EL.mem_pairCurve_iff]
    push_neg
    refine ⟨?_, ?_, ?_⟩
    · exact notMem_paramRay_of_ne_int hN (fun j => hmf_ne_a j) (by norm_num)
    · intro hy
      have hK : rf ∈ Work.EL.K c := by rw [hy]; exact landsN_mem_K hN P.lands_a
      exact Work.EL.rayPt_notMem_K hN (θ := mf) (t := 2) (by norm_num) hK
    · exact notMem_paramRay_of_ne_int hN (fun j => hmf_ne_b j) (by norm_num)
  have hrn_notmem : rn ∉ Work.EL.pairCurve P := by
    rw [Work.EL.mem_pairCurve_iff]
    push_neg
    refine ⟨?_, ?_, ?_⟩
    · exact notMem_paramRay_of_ne_int hN (fun j => hmn_ne_a j) (by norm_num)
    · intro hy
      have hK : rn ∈ Work.EL.K c := by rw [hy]; exact landsN_mem_K hN P.lands_b
      exact Work.EL.rayPt_notMem_K hN (θ := mn) (t := 2) (by norm_num) hK
    · exact notMem_paramRay_of_ne_int hN (fun j => hmn_ne_b j) (by norm_num)
  rw [Set.disjoint_left]
  intro z hzA hzB
  have h1 : connectedComponentIn (Work.EL.pairCurve P)ᶜ rf
      = connectedComponentIn (Work.EL.pairCurve P)ᶜ z :=
    connectedComponentIn_eq (F := (Work.EL.pairCurve P)ᶜ) (x := rf) (y := z) hzA
  have h2 : connectedComponentIn (Work.EL.pairCurve P)ᶜ rn
      = connectedComponentIn (Work.EL.pairCurve P)ᶜ z :=
    connectedComponentIn_eq (F := (Work.EL.pairCurve P)ᶜ) (x := rn) (y := z) hzB
  have hmem : rf ∈ connectedComponentIn (Work.EL.pairCurve P)ᶜ rn := by
    have hm : rf ∈ connectedComponentIn (Work.EL.pairCurve P)ᶜ rf :=
      mem_connectedComponentIn hrf_notmem
    rw [h1] at hm
    rw [h2]
    exact hm
  have hLopen : IsOpen (connectedComponentIn (Work.EL.pairCurve P)ᶜ rn) :=
    IsOpen.connectedComponentIn ((isClosed_pairCurve_local P).isOpen_compl)
  have hpc : IsPathConnected (connectedComponentIn (Work.EL.pairCurve P)ᶜ rn) :=
    (hLopen.isConnected_iff_isPathConnected).mp
      ⟨⟨rn, mem_connectedComponentIn hrn_notmem⟩, isPreconnected_connectedComponentIn⟩
  obtain ⟨γ, hγmem⟩ := hpc.joinedIn rn (mem_connectedComponentIn hrn_notmem) rf hmem
  obtain ⟨x₀, -, hmax⟩ := (isCompact_range γ.continuous).exists_isMaxOn (Set.range_nonempty γ)
    (hN.continuous_potential.continuousOn.mono (Set.subset_univ _))
  set M : ℝ := Work.EL.pot hN x₀ with hM
  have hMbd : ∀ t, Work.EL.pot hN (γ t) ≤ M := fun t => isMaxOn_iff.mp hmax (γ t) ⟨t, rfl⟩
  set R : ℝ := max 4 (Real.exp M + 1) with hRdef
  have hR1 : 1 < R := by rw [hRdef]; linarith [le_max_left (4 : ℝ) (Real.exp M + 1)]
  have hlogR : M < Real.log R := by
    rw [hRdef]
    have h2 : M < Real.log (Real.exp M + 1) := by
      have h : Real.log (Real.exp M) < Real.log (Real.exp M + 1) :=
        Real.log_lt_log (Real.exp_pos M) (by linarith)
      rwa [Real.log_exp M] at h
    have h3 : Real.log (Real.exp M + 1) ≤ Real.log (max 4 (Real.exp M + 1)) :=
      Real.log_le_log (by linarith [Real.exp_pos M]) (le_max_right _ _)
    linarith
  have hR4 : (4 : ℝ) ≤ R := le_max_left _ _
  have hsqrt_ge : 2 ≤ Real.sqrt R := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]
    linarith
  have hsqrt_lt : Real.sqrt R < R := by
    rw [Real.sqrt_lt' (x := R) (y := R) (by linarith : (0 : ℝ) < R)]
    nlinarith
  have hAdm : Work.EL.PolyAdmissible [P] := polyAdmissible_singleton_aux P hab hb1
  have hCj : Work.Top.IsJordanCurve (Work.EL.polyCurve [P] R) :=
    polyCurve_isJordan hN [P] hAdm hR1
  obtain ⟨S, hSI⟩ := polyRegion_eq_sides_I hN hJ [P] hAdm hR1 hCj
  have hrnI : rn ∈ S.I := by
    rw [← hSI]
    have hmid : Work.EL.midNear [P] = mn := by
      show P.b + Int.fract (P.a + 1 - P.b) / 2 = mn
      rw [show Int.fract (P.a + 1 - P.b) = Work.EL.arcLen P.b P.a by
        rw [Work.EL.arcLen]
        rw [show P.a + 1 - P.b = (P.a - P.b) + ((1 : ℤ) : ℝ) by push_cast; ring,
          Int.fract_add_intCast]]
    show rn ∈ Work.EL.polyRegion [P] R
    rw [Work.EL.polyRegion, hmid]
    have hpiece : IsPreconnected
        ((fun t : ℝ => Work.EL.rayPt hN mn t) '' Set.Icc (2 : ℝ) (Real.sqrt R)) :=
      IsPreconnected.image isPreconnected_Icc _
        ((Work.Top.continuousOn_rayPt hN mn).mono (fun t ht => by
          rcases Set.mem_Icc.mp ht with ⟨h1, -⟩
          exact lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) h1))
    have hpiece_sub : ((fun t : ℝ => Work.EL.rayPt hN mn t) '' Set.Icc (2 : ℝ) (Real.sqrt R))
        ⊆ (Work.EL.polyCurve [P] R)ᶜ := by
      rintro w ⟨t, ht, rfl⟩
      rw [Set.mem_compl_iff]
      refine rayPt_notMem_polyCurve_nearArc hN P hR1 ?_ hmn_ne_a hmn_ne_b ?_
      · rcases Set.mem_Icc.mp ht with ⟨h1, -⟩
        linarith
      · rcases Set.mem_Icc.mp ht with ⟨-, h2⟩
        exact ne_of_lt (lt_of_le_of_lt h2 hsqrt_lt)
    have hxmem : Work.EL.rayPt hN mn (Real.sqrt R)
        ∈ (fun t : ℝ => Work.EL.rayPt hN mn t) '' Set.Icc (2 : ℝ) (Real.sqrt R) :=
      ⟨Real.sqrt R, ⟨hsqrt_ge, le_rfl⟩, rfl⟩
    have htarget : Work.EL.rayPt hN mn 2
        ∈ (fun t : ℝ => Work.EL.rayPt hN mn t) '' Set.Icc (2 : ℝ) (Real.sqrt R) :=
      ⟨2, ⟨le_rfl, hsqrt_ge⟩, rfl⟩
    exact IsPreconnected.subset_connectedComponentIn hpiece hxmem hpiece_sub htarget
  have hrfO : rf ∈ S.O := by
    have hsub : Work.EL.paramRay hN mf ⊆ (Work.EL.polyCurve [P] R)ᶜ := by
      intro w hw
      rw [Set.mem_compl_iff]
      obtain ⟨hwK, t, ht, hΦ⟩ := (Work.Top.NakaneData.mem_paramRay_iff hN).mp hw
      have hwt : w = Work.EL.rayPt hN mf t :=
        hN.injOn_Phi hwK (Work.EL.rayPt_notMem_K hN ht)
          (by rw [hΦ, Work.Top.NakaneData.Phi_rayPt hN ht])
      rw [hwt]
      exact rayPt_notMem_polyCurve_farArc hN P hR1 ht hmf_InArc
    have hunb : ∀ n : ℕ, ∃ w ∈ Work.EL.paramRay hN mf, (n : ℝ) ≤ ‖w‖ :=
      Work.Top.paramRay_unbounded hN mf
    have hO : Work.EL.paramRay hN mf ⊆ S.O :=
      S.subset_O_of_unbounded (isPreconnected_paramRay_aux hN mf) hsub hunb
    exact hO (Work.EL.rayPt_mem_paramRay hN (θ := mf) (t := 2) (by norm_num))
  have hγC : ∀ t, γ t ∈ (Work.EL.polyCurve [P] R)ᶜ := by
    intro t
    rw [Set.mem_compl_iff]
    intro ht
    have hzc : γ t ∉ Work.EL.pairCurve P :=
      connectedComponentIn_subset ((Work.EL.pairCurve P)ᶜ) rn (hγmem t)
    have hpot := hMbd t
    rw [Work.EL.polyCurve, Set.mem_ofPred_eq] at ht
    rcases ht with ⟨Q, hQ, hy | ha | hb⟩ | ⟨θ, hθ, hfar, hθeq⟩
    · simp only [List.mem_singleton] at hQ
      rw [hQ] at hy
      exact hzc (hy ▸ self_mem_pairCurve_aux P)
    · simp only [List.mem_singleton] at hQ
      rw [hQ] at ha
      exact hzc ((Work.EL.mem_pairCurve_iff P _).mpr
        (Or.inl (Work.Top.NakaneData.rayPiece_subset_paramRay ha)))
    · simp only [List.mem_singleton] at hQ
      rw [hQ] at hb
      exact hzc ((Work.EL.mem_pairCurve_iff P _).mpr
        (Or.inr (Or.inr (Work.Top.NakaneData.rayPiece_subset_paramRay hb))))
    · have hpotR : Work.EL.pot hN (γ t) = Real.log R := by
        rw [hθeq, Work.EL.pot_rayPt hN hR1]
      linarith
  exact (S.not_joinedIn hrnI hrfO) ⟨γ, hγC⟩

/-! ## The main theorem -/

/-- **The far side of `P` lies in the near side of `Q`.**

If the curves of the two co-landing pairs are disjoint and the far arc of `P` is contained in
the near arc of `Q`, then `pairSide P ⊆ pairSideNear Q`.

The pair `P` is first normalized so that `P₁.b = P.a + arcLen P.a P.b`; this does not change its
curve (the rays are `1`-periodic) nor its sides, but it turns the arc `(P₁.a, P₁.b)` into the
honest interval `(P.a, P.a + arcLen P.a P.b)`, so that the two angles `Q.a`, `Q.b` of the second
pair can be located with `InArc_or_InArc_near_aux`: they lie in the *near* arc of `P₁`.

The reference point of `pairSide P₁` has an angle in the far arc of `P₁`, hence — by the
hypothesis on the arcs — in the near arc of `Q`; consequently it lies in `pairSideNear Q`.  The
side `pairSide P₁` is preconnected and contains that point, so it suffices to see that it misses
the curve of `Q`: the points of that curve are its two rays, which lie in `pairSideNear P₁`, and
its landing point `Q.y`, which does not lie in `pairSide P₁` because the ray `R(Q.a)` converges
to it inside the open set `pairSideNear P₁`, disjoint from `pairSide P₁`. -/
theorem pairSide_subset_pairSideNear {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (P Q : Work.EL.CoPair hN)
    (hdisj : Disjoint (Work.EL.pairCurve P) (Work.EL.pairCurve Q))
    (harc : ∀ θ : ℝ, Work.EL.InArc θ P.a P.b → Work.EL.InArc θ Q.b (Q.a + 1)) :
    Work.EL.pairSide P ⊆ Work.EL.pairSideNear Q := by
  classical
  rcases eq_or_lt_of_le (Work.EL.arcLen_nonneg P.a P.b) with hdeg | hpos
  · -- degenerate arc: the far side is empty
    have hrefC : Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2
        ∈ Work.EL.pairCurve P := by
      rw [← hdeg]
      simp only [zero_div, add_zero]
      exact (Work.EL.mem_pairCurve_iff P _).mpr
        (Or.inl (Work.EL.rayPt_mem_paramRay hN (by norm_num)))
    have hempty : Work.EL.pairSide P = ∅ := by
      have h1 : Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2
          ∉ (Work.EL.RawPair.curve hN P.toRawPair)ᶜ := by
        rw [Set.mem_compl_iff]
        exact fun h => h hrefC
      exact connectedComponentIn_eq_empty h1
    rw [hempty]
    exact Set.empty_subset _
  · -- nondegenerate arc: normalize the pair `P`
    set k : ℤ := ⌊P.b - P.a⌋ with hk
    have hb_eq : P.a + Work.EL.arcLen P.a P.b = P.b - (k : ℝ) := by
      have hff := Int.floor_add_fract (P.b - P.a)
      rw [← hk] at hff
      simp only [Work.EL.arcLen]
      linarith
    let P₁ : Work.EL.CoPair hN :=
      { toRawPair := ⟨P.a, P.b - (k : ℝ), P.y⟩
        lands_a := P.lands_a
        lands_b := by
          have h := LandsN_add_int hN P.lands_b (-k)
          rw [show P.b + ((-k : ℤ) : ℝ) = P.b - (k : ℝ) by push_cast; ring] at h
          exact h }
    have hP1a : P₁.a = P.a := rfl
    have hP1b : P₁.b = P.b - (k : ℝ) := rfl
    have hP1y : P₁.y = P.y := rfl
    have hP1arc : Work.EL.arcLen P₁.a P₁.b = Work.EL.arcLen P.a P.b := by
      simp only [hP1a, hP1b, Work.EL.arcLen]
      rw [show P.b - (k : ℝ) - P.a = (P.b - P.a) + ((-k : ℤ) : ℝ) by push_cast; ring,
        Int.fract_add_intCast]
    have hP1arcn : Work.EL.arcLen P₁.b P₁.a = Work.EL.arcLen P.b P.a := by
      simp only [hP1a, hP1b, Work.EL.arcLen]
      rw [show P.a - (P.b - (k : ℝ)) = (P.a - P.b) + (k : ℝ) by push_cast; ring,
        Int.fract_add_intCast]
    have hP1lt : P₁.a < P₁.b := by rw [hP1a, hP1b, ← hb_eq]; linarith
    have hP1lt1 : P₁.b < P₁.a + 1 := by
      rw [hP1a, hP1b, ← hb_eq]
      linarith [Work.EL.arcLen_lt_one P.a P.b]
    have hparam_b : Work.EL.paramRay hN P₁.b = Work.EL.paramRay hN P.b := by
      rw [hP1b]
      have h := paramRay_add_int hN P.b (-k)
      rwa [show P.b + ((-k : ℤ) : ℝ) = P.b - (k : ℝ) by push_cast; ring] at h
    have hcurve : Work.EL.pairCurve P₁ = Work.EL.pairCurve P := by
      show Work.EL.RawPair.curve hN P₁.toRawPair = Work.EL.RawPair.curve hN P.toRawPair
      simp only [Work.EL.RawPair.curve, hP1a, hP1y, hparam_b]
    have href : Work.EL.rayPt hN (P₁.a + Work.EL.arcLen P₁.a P₁.b / 2) 2
        = Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2 := by rw [hP1a, hP1arc]
    have hrefn : Work.EL.rayPt hN (P₁.b + Work.EL.arcLen P₁.b P₁.a / 2) 2
        = Work.EL.rayPt hN (P.b + Work.EL.arcLen P.b P.a / 2) 2 := by
      have harg : P₁.b + Work.EL.arcLen P₁.b P₁.a / 2
          = (P.b + Work.EL.arcLen P.b P.a / 2) + ((-k : ℤ) : ℝ) := by
        rw [hP1b, hP1arcn]; push_cast; ring
      rw [harg, rayPt_add_int hN (P.b + Work.EL.arcLen P.b P.a / 2) 2 (-k)]
    have hsideP : Work.EL.pairSide P₁ = Work.EL.pairSide P := by
      show connectedComponentIn (Work.EL.pairCurve P₁)ᶜ
          (Work.EL.rayPt hN (P₁.a + Work.EL.arcLen P₁.a P₁.b / 2) 2)
        = connectedComponentIn (Work.EL.pairCurve P)ᶜ
          (Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2)
      rw [hcurve, href]
    have hdisj1 : Disjoint (Work.EL.pairCurve P₁) (Work.EL.pairCurve Q) := by
      rw [hcurve]; exact hdisj
    -- the angles of `Q` avoid the far arc of `P₁`
    have harc1 : ∀ θ : ℝ, Work.EL.InArc θ P₁.a P₁.b → Work.EL.InArc θ Q.b (Q.a + 1) := by
      intro θ hθ
      refine harc θ ?_
      rw [hP1a] at hθ
      rw [hP1b] at hθ
      have hθ' : Work.EL.InArc θ P.a (P.b + ((-k : ℤ) : ℝ)) := by
        rw [show P.b + ((-k : ℤ) : ℝ) = P.b - (k : ℝ) by push_cast; ring]
        exact hθ
      exact (InArc_right_add_int θ P.a P.b (-k)).mp hθ'
    have hneQa1 : ∀ m : ℤ, Q.a ≠ P₁.a + (m : ℝ) :=
      ne_congr_of_disjoint Q P₁ hdisj1.symm
        (fun z hz => (Work.EL.mem_pairCurve_iff Q z).mpr (Or.inl hz))
        (fun z hz => (Work.EL.mem_pairCurve_iff P₁ z).mpr (Or.inl hz))
    have hneQa2 : ∀ m : ℤ, Q.a ≠ P₁.b + (m : ℝ) :=
      ne_congr_of_disjoint Q P₁ hdisj1.symm
        (fun z hz => (Work.EL.mem_pairCurve_iff Q z).mpr (Or.inl hz))
        (fun z hz => (Work.EL.mem_pairCurve_iff P₁ z).mpr (Or.inr (Or.inr hz)))
    have hneQb1 : ∀ m : ℤ, Q.b ≠ P₁.a + (m : ℝ) :=
      ne_congr_of_disjoint Q P₁ hdisj1.symm
        (fun z hz => (Work.EL.mem_pairCurve_iff Q z).mpr (Or.inr (Or.inr hz)))
        (fun z hz => (Work.EL.mem_pairCurve_iff P₁ z).mpr (Or.inl hz))
    have hneQb2 : ∀ m : ℤ, Q.b ≠ P₁.b + (m : ℝ) :=
      ne_congr_of_disjoint Q P₁ hdisj1.symm
        (fun z hz => (Work.EL.mem_pairCurve_iff Q z).mpr (Or.inr (Or.inr hz)))
        (fun z hz => (Work.EL.mem_pairCurve_iff P₁ z).mpr (Or.inr (Or.inr hz)))
    have hQa_not_far : ¬ Work.EL.InArc Q.a P₁.a P₁.b := by
      intro h
      have h' := harc1 Q.a h
      have h2 : Int.fract (Q.a - Q.b) < Work.EL.arcLen Q.b Q.a := by
        rw [← arcLen_add_one_at Q.b Q.a]
        exact h'.2
      rw [Work.EL.arcLen] at h2
      exact absurd h2 (lt_irrefl _)
    have hQb_not_far : ¬ Work.EL.InArc Q.b P₁.a P₁.b := by
      intro h
      have h' := harc1 Q.b h
      have h0 : Int.fract (Q.b - Q.b) = 0 := by simp
      linarith [h'.1, h0]
    have hnQa : Work.EL.InArc Q.a P₁.b (P₁.a + 1) :=
      (InArc_or_InArc_near_aux hP1lt hP1lt1 hneQa1 hneQa2).resolve_left hQa_not_far
    have hnQb : Work.EL.InArc Q.b P₁.b (P₁.a + 1) :=
      (InArc_or_InArc_near_aux hP1lt hP1lt1 hneQb1 hneQb2).resolve_left hQb_not_far
    -- the two rays of `Q` lie in the near side of `P₁`
    have hrayA : Work.EL.paramRay hN Q.a ⊆ Work.EL.pairSideNear P₁ :=
      paramRay_subset_pairSideNear hN hJ P₁ hnQa
    have hrayB : Work.EL.paramRay hN Q.b ⊆ Work.EL.pairSideNear P₁ :=
      paramRay_subset_pairSideNear hN hJ P₁ hnQb
    have hAB : Disjoint (Work.EL.pairSide P₁) (Work.EL.pairSideNear P₁) :=
      pairSide_disjoint_aux hN hJ P₁ hP1lt hP1lt1
    -- the landing point of `Q` does not lie in the far side of `P₁`
    have hQy_notA : Q.y ∉ Work.EL.pairSide P₁ := by
      intro hmem
      have hopen : IsOpen (Work.EL.pairSide P₁) := (isOpen_pairSide hN P₁).1
      have hev : ∀ᶠ t in 𝓝[Set.Ioi (1 : ℝ)] 1, Work.EL.rayPt hN Q.a t ∈ Work.EL.pairSide P₁ :=
        Q.lands_a.eventually (hopen.mem_nhds hmem)
      haveI : (𝓝[Set.Ioi (1 : ℝ)] 1).NeBot := nhdsWithin_Ioi_neBot le_rfl
      obtain ⟨t, htA, ht1⟩ := (hev.and self_mem_nhdsWithin).exists
      exact (Set.disjoint_left.mp hAB) htA (hrayA (Work.EL.rayPt_mem_paramRay hN ht1))
    -- hence the far side of `P₁` misses the curve of `Q`
    have hsub_compl : Work.EL.pairSide P₁ ⊆ (Work.EL.pairCurve Q)ᶜ := by
      intro w hw
      rw [Set.mem_compl_iff]
      intro hwQ
      rw [Work.EL.mem_pairCurve_iff] at hwQ
      rcases hwQ with h | h | h
      · exact (Set.disjoint_left.mp hAB) hw (hrayA h)
      · rw [h] at hw
        exact hQy_notA hw
      · exact (Set.disjoint_left.mp hAB) hw (hrayB h)
    -- the reference point of the far side of `P₁` lies in the near side of `Q`
    have hxP_far : Work.EL.rayPt hN (P₁.a + Work.EL.arcLen P₁.a P₁.b / 2) 2
        ∈ Work.EL.pairSide P₁ := by
      have hpos1 : 0 < Work.EL.arcLen P₁.a P₁.b := by rw [hP1arc]; exact hpos
      exact rayPt_mem_pairSide hN P₁ (by linarith) (by linarith) (by norm_num)
    have hxP_nearQ : Work.EL.rayPt hN (P₁.a + Work.EL.arcLen P₁.a P₁.b / 2) 2
        ∈ Work.EL.pairSideNear Q := by
      have hmfarc : Work.EL.InArc (P₁.a + Work.EL.arcLen P₁.a P₁.b / 2) P₁.a P₁.b := by
        have hsub : P₁.a + Work.EL.arcLen P₁.a P₁.b / 2 - P₁.a
            = Work.EL.arcLen P₁.a P₁.b / 2 := by ring
        have h2lt : Work.EL.arcLen P₁.a P₁.b / 2 < 1 := by
          linarith [Work.EL.arcLen_lt_one P₁.a P₁.b]
        rw [Work.EL.InArc, hsub, Int.fract_eq_self.mpr ⟨by linarith, h2lt⟩]
        exact ⟨by linarith, by linarith⟩
      exact (paramRay_subset_pairSideNear hN hJ Q (harc1 _ hmfarc))
        (Work.EL.rayPt_mem_paramRay hN (θ := P₁.a + Work.EL.arcLen P₁.a P₁.b / 2) (t := 2)
          (by norm_num))
    rw [← hsideP]
    intro z hz
    have hzcomp : z ∈ connectedComponentIn (Work.EL.pairCurve Q)ᶜ
        (Work.EL.rayPt hN (P₁.a + Work.EL.arcLen P₁.a P₁.b / 2) 2) :=
      IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn hxP_far
        hsub_compl hz
    have heq : connectedComponentIn (Work.EL.pairCurve Q)ᶜ
          (Work.EL.rayPt hN (P₁.a + Work.EL.arcLen P₁.a P₁.b / 2) 2)
        = connectedComponentIn (Work.EL.pairCurve Q)ᶜ
          (Work.EL.rayPt hN (Q.b + Work.EL.arcLen Q.b Q.a / 2) 2) :=
      connectedComponentIn_eq (F := (Work.EL.pairCurve Q)ᶜ)
        (x := Work.EL.rayPt hN (Q.b + Work.EL.arcLen Q.b Q.a / 2) 2)
        (y := Work.EL.rayPt hN (P₁.a + Work.EL.arcLen P₁.a P₁.b / 2) 2) hxP_nearQ |>.symm
    rw [heq] at hzcomp
    exact hzcomp

end Work.ELTop
