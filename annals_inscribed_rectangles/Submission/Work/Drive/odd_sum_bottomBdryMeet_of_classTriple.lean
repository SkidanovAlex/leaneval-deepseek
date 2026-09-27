import Mathlib
import Submission.Work.Drive.classTripleRegular
import Submission.Work.Drive.endsParity

/-!
# The ends clause of the triple count, in stable parity form

The three radial sweeps `D k = clampedSweep (c k) ψ (P k)` of three plane presentations satisfy the
engine's parity identity `Σ_k top_k ≡ Σ_k bottom_k` (`even_sum_topBdryMeet_add_bottomBdryMeet_clamped`),
so the end contribution `Σ_k bottom_k` is the genuinely topological input of the triple count (the
paper's `n_{-λ}`, i.e. the cube `x³ ≠ 0` of `H^*(ℝP³;ℤ/2)`).

This file computes the end contribution in the vocabulary in which the design provides it
(`Submission/Work/Drive/endsParity.lean`): for truncation levels with `c 1 < c 0`, `c 2 < c 0` and all
levels below the planes' levels,

> `Σ_k bottom_k = #(classTripleSet P)`   (the count is in fact exact, not only a parity),

where `classTripleSet P` is the set of triples of class coordinates `y k` at which the three plane
presentations have a common projective class.  Consequently the oddness of the *class triple count*
(the mod-2 degree statement `⟨α ∪ α ∪ α, [ℝP³]⟩ = 1` for three projective planes representing the
generator of `H₂(ℝP³;ℤ/2)`) is exactly the oddness of the end contribution.

## The bijection behind the count

The bottom triple intersections of the block `0` are in bijection with the class triples:

* block `0` sits at its bottom face `x 0 2 = 0`, where the sweep is the **shadow** of the plane on the
  level `c 0` (`clampedSweep_face_zero`, `levelOf_shadow`), so all three shadows coincide there;
* conversely, at a class triple `y` the three shadows on the level `c 0` coincide
  (`shadow_congr` + `cls_clampedSweep`), and the other two blocks have a **unique** interior radial
  parameter realising the level `c 0` (`existsUnique_levelOf_clampedSweep_eq`).

The blocks `1` and `2` carry no bottom triple point at all: a bottom triple point of the block `k` is
at level `c k`, and the levels of the other blocks are bounded below by their own truncation levels,
the largest of which is `c 0 > c k` (`bottomBdryMeet_eq_empty_of_lt_level_local`).

Finally, the trichotomy `c 1 < c 0`, `c 2 < c 0` of the design is what makes the sum
`Σ_k bottom_k` collapse to the single block `0`, so the parity of the end contribution is the parity
of the class triple count.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- `1 ≠ 0` in `Fin 3`. -/
lemma fin3_one_ne_zero : (1 : Fin 3) ≠ 0 := by decide

/-- `2 ≠ 0` in `Fin 3`. -/
lemma fin3_two_ne_zero : (2 : Fin 3) ≠ 0 := by decide

/-- The design data of the ends clause: the truncation levels `c k`, the cutoff `ψ`, and the numbered
hypotheses of the consumer `odd_sum_bottomBdryMeet_of_classTriple`.  The design's strictness is
recorded in the form `k ≠ 0 → c k < c 0`, which is exactly `c 1 < c 0 ∧ c 2 < c 0`. -/
structure EndDesign (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace) where
  /-- the truncation levels -/
  c : Fin 3 → ℝ
  /-- the cutoff profile -/
  psi : ℝ → ℝ
  /-- the truncation levels are positive -/
  hcpos : ∀ k : Fin 3, 0 < c k
  /-- only the block `0` carries the maximal truncation level -/
  hcne : ∀ k : Fin 3, k ≠ 0 → c k < c 0
  /-- all truncation levels are below the planes' levels -/
  hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < levelOf (P k y)
  /-- the cutoff is `1` at `0` -/
  hψ0 : psi 0 = 1
  /-- the cutoff is `0` at `1` -/
  hψ1 : psi 1 = 0
  /-- the cutoff is `[0,1]`-valued on `[0,1]` -/
  hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, psi t ∈ Set.Icc (0 : ℝ) 1
  /-- the cutoff is continuous on `[0,1]` -/
  hcont : ContinuousOn psi (Set.Icc (0 : ℝ) 1)
  /-- the cutoff is strictly decreasing on `[0,1]` -/
  hanti : StrictAntiOn psi (Set.Icc (0 : ℝ) 1)

namespace EndDesign

variable {P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace}

/-- The three radial sweeps of the design. -/
def sweep (D : EndDesign P) (k : Fin 3) : EuclideanSpace ℝ (Fin 3) → CappingSpace :=
  clampedSweep (D.c k) D.psi (P k)

/-- **The unique interior radial parameter at which the `k`-th sweep (`k ≠ 0`) reaches the maximal
truncation level `c 0`.** -/
noncomputable def rad (D : EndDesign P) (k : Fin 3) (hk : k ≠ 0)
    (y : EuclideanSpace ℝ (Fin 2)) : ℝ :=
  (existsUnique_levelOf_clampedSweep_eq (L := D.c 0) (hc := D.hcpos k) (hψ0 := D.hψ0)
    (hψ1 := D.hψ1) (hcont := D.hcont) (hanti := D.hanti) (hLc := D.hcne k hk)
    (hLr := D.hlev k y)).choose

lemma rad_mem (D : EndDesign P) (k : Fin 3) (hk : k ≠ 0) (y : EuclideanSpace ℝ (Fin 2)) :
    D.rad k hk y ∈ Set.Ioo (0 : ℝ) 1 := by
  simpa only [rad] using
    (existsUnique_levelOf_clampedSweep_eq (L := D.c 0) (hc := D.hcpos k) (hψ0 := D.hψ0)
      (hψ1 := D.hψ1) (hcont := D.hcont) (hanti := D.hanti) (hLc := D.hcne k hk)
      (hLr := D.hlev k y)).choose_spec.1.1

lemma rad_level (D : EndDesign P) (k : Fin 3) (hk : k ≠ 0) (y : EuclideanSpace ℝ (Fin 2)) :
    levelOf (D.sweep k (radVec y (D.rad k hk y))) = D.c 0 := by
  simpa only [rad, sweep] using
    (existsUnique_levelOf_clampedSweep_eq (L := D.c 0) (hc := D.hcpos k) (hψ0 := D.hψ0)
      (hψ1 := D.hψ1) (hcont := D.hcont) (hanti := D.hanti) (hLc := D.hcne k hk)
      (hLr := D.hlev k y)).choose_spec.1.2

lemma rad_eq (D : EndDesign P) (k : Fin 3) (hk : k ≠ 0) (y : EuclideanSpace ℝ (Fin 2)) {t : ℝ}
    (ht : t ∈ Set.Ioo (0 : ℝ) 1) (h : levelOf (D.sweep k (radVec y t)) = D.c 0) :
    t = D.rad k hk y := by
  simpa only [rad] using
    (existsUnique_levelOf_clampedSweep_eq (L := D.c 0) (hc := D.hcpos k) (hψ0 := D.hψ0)
      (hψ1 := D.hψ1) (hcont := D.hcont) (hanti := D.hanti) (hLc := D.hcne k hk)
      (hLr := D.hlev k y)).choose_spec.2 t (by simpa only [sweep] using ⟨ht, h⟩)

/-- **The lift of a class triple to the bottom triple point of the block `0`**: block `0` at its
bottom face, the other two blocks at the unique interior radial parameter at which their sweeps reach
the level `c 0`. -/
noncomputable def endTriple (D : EndDesign P)
    (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) : Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  fun k => ![botVec (y 0 0) (y 0 1),
    radVec (y 1) (D.rad 1 fin3_one_ne_zero (y 1)),
    radVec (y 2) (D.rad 2 fin3_two_ne_zero (y 2))] k

lemma endTriple_apply_zero (D : EndDesign P) (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) :
    D.endTriple y 0 = botVec (y 0 0) (y 0 1) := rfl

lemma endTriple_apply_one (D : EndDesign P) (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) :
    D.endTriple y 1 = radVec (y 1) (D.rad 1 fin3_one_ne_zero (y 1)) := rfl

lemma endTriple_apply_two (D : EndDesign P) (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) :
    D.endTriple y 2 = radVec (y 2) (D.rad 2 fin3_two_ne_zero (y 2)) := rfl

/-- The class coordinates of the lift are the class triple: the first two coordinates of each block
recover `y k` (the three literal-index cases). -/
lemma mk2_endTriple_zero (D : EndDesign P) (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) :
    mk2 (D.endTriple y 0 0) (D.endTriple y 0 1) = y 0 := by
  rw [endTriple_apply_zero]
  simpa using mk2_eta (y 0)

lemma mk2_endTriple_one (D : EndDesign P) (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) :
    mk2 (D.endTriple y 1 0) (D.endTriple y 1 1) = y 1 := by
  rw [endTriple_apply_one]
  simpa using mk2_eta (y 1)

lemma mk2_endTriple_two (D : EndDesign P) (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) :
    mk2 (D.endTriple y 2 0) (D.endTriple y 2 1) = y 2 := by
  rw [endTriple_apply_two]
  simpa using mk2_eta (y 2)

/-- The class coordinates of the lift are the class triple, in `∀ k` form. -/
lemma mk2_endTriple (D : EndDesign P) (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) (k : Fin 3) :
    mk2 (D.endTriple y k 0) (D.endTriple y k 1) = y k := by
  fin_cases k
  · exact mk2_endTriple_zero D y
  · exact mk2_endTriple_one D y
  · exact mk2_endTriple_two D y

/-- At a class triple the three shadows of the planes on the level `c 0` coincide. -/
lemma shadow_eq (D : EndDesign P) (k : Fin 3) {y : Fin 3 → EuclideanSpace ℝ (Fin 2)}
    (hy : y ∈ classTripleSet P) :
    shadow (D.c 0) (D.hcpos 0) (P k (y k)) = shadow (D.c 0) (D.hcpos 0) (P 0 (y 0)) := by
  refine shadow_congr (D.c 0) (D.hcpos 0) ?_
  simpa only [planeClassMap] using (mem_classTripleSet.mp hy).2 k

/-- **The lift of a class triple is a bottom triple point of the block `0`.** -/
lemma endTriple_mem_bottomBdryMeet (D : EndDesign P)
    {y : Fin 3 → EuclideanSpace ℝ (Fin 2)} (hy : y ∈ classTripleSet P) :
    D.endTriple y ∈ bottomBdryMeet CappingSpace D.sweep 0 := by
  have hybox : ∀ k : Fin 3, y k ∈ Submission.Drive.unitBox 1 := (mem_classTripleSet.mp hy).1
  have hbox0 : D.endTriple y 0 ∈ Submission.Drive.unitBox 2 := by
    rw [endTriple_apply_zero]
    exact botVec_mem_unitBox (y 0 0) (y 0 1) (hybox 0 0) (hybox 0 1)
  have hbox1 : D.endTriple y 1 ∈ Submission.Drive.unitBox 2 := by
    rw [endTriple_apply_one]
    exact radVec_mem_unitBox (hybox 1)
      ⟨le_of_lt (D.rad_mem 1 fin3_one_ne_zero (y 1)).1,
        le_of_lt (D.rad_mem 1 fin3_one_ne_zero (y 1)).2⟩
  have hbox2 : D.endTriple y 2 ∈ Submission.Drive.unitBox 2 := by
    rw [endTriple_apply_two]
    exact radVec_mem_unitBox (hybox 2)
      ⟨le_of_lt (D.rad_mem 2 fin3_two_ne_zero (y 2)).1,
        le_of_lt (D.rad_mem 2 fin3_two_ne_zero (y 2)).2⟩
  have hbox : ∀ k : Fin 3, D.endTriple y k ∈ Submission.Drive.unitBox 2 := by
    intro k
    fin_cases k
    · exact hbox0
    · exact hbox1
    · exact hbox2
  have h01 : D.sweep 0 (D.endTriple y 0) = D.sweep 1 (D.endTriple y 1) := by
    simp only [sweep, endTriple_apply_zero, endTriple_apply_one]
    rw [clampedSweep_bottom (D.c 0) (D.hcpos 0) D.psi D.hψ0 (P 0) (y 0),
      clampedSweep_eq_shadow_of_level (D.c 1) (D.c 0) (D.hcpos 0) D.psi (P 1) (y 1)
        (D.rad 1 fin3_one_ne_zero (y 1)) (D.rad_level 1 fin3_one_ne_zero (y 1))]
    exact (D.shadow_eq 1 hy).symm
  have h02 : D.sweep 0 (D.endTriple y 0) = D.sweep 2 (D.endTriple y 2) := by
    simp only [sweep, endTriple_apply_zero, endTriple_apply_two]
    rw [clampedSweep_bottom (D.c 0) (D.hcpos 0) D.psi D.hψ0 (P 0) (y 0),
      clampedSweep_eq_shadow_of_level (D.c 2) (D.c 0) (D.hcpos 0) D.psi (P 2) (y 2)
        (D.rad 2 fin3_two_ne_zero (y 2)) (D.rad_level 2 fin3_two_ne_zero (y 2))]
    exact (D.shadow_eq 2 hy).symm
  have hzero : D.endTriple y 0 2 = 0 := by
    rw [endTriple_apply_zero]
    exact botVec_apply_two (y 0 0) (y 0 1)
  refine ⟨⟨hbox, h01, h02, ⟨hbox 0, 2, Or.inl hzero⟩⟩, hzero⟩

/-- **The radial data of a bottom triple point at the block `k ≠ 0`**: the radial parameter is
interior (the sweep is neither at its bottom face nor at the plane) and it realises the level
`c 0`. -/
lemma rad_data (D : EndDesign P) {x : Fin 3 → EuclideanSpace ℝ (Fin 3)}
    (hbox : ∀ j : Fin 3, x j ∈ Submission.Drive.unitBox 2) (k : Fin 3) (hk : k ≠ 0)
    (hEq : D.sweep k (x k) = D.sweep 0 (x 0))
    (h0lev : levelOf (D.sweep 0 (x 0)) = D.c 0) :
    x k 2 ∈ Set.Ioo (0 : ℝ) 1 ∧
      levelOf (D.sweep k (radVec (mk2 (x k 0) (x k 1)) (x k 2))) = D.c 0 := by
  have hklev : levelOf (D.sweep k (x k)) = D.c 0 := by rw [hEq]; exact h0lev
  have hxk : radVec (mk2 (x k 0) (x k 1)) (x k 2) = x k := by
    rw [radVec]
    ext i
    fin_cases i
    · simp
    · simp
    · simp
  have hkeq : D.c k < D.c 0 := D.hcne k hk
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rcases eq_or_lt_of_le (hbox k 2).1 with h | h
    · exfalso
      have hface : D.sweep k (x k) = shadow (D.c k) (D.hcpos k) (P k (mk2 (x k 0) (x k 1))) := by
        simpa only [sweep] using
          clampedSweep_face_zero (D.c k) (D.hcpos k) D.psi (P k) D.hψ0 (x k) h.symm
      have : D.c k = D.c 0 := by rw [← hklev, hface, levelOf_shadow]
      exact absurd this (ne_of_lt hkeq)
    · exact h
  · rcases eq_or_lt_of_le (hbox k 2).2 with h | h
    · exfalso
      have hface : D.sweep k (x k) = P k (mk2 (x k 0) (x k 1)) := by
        simpa only [sweep] using clampedSweep_face_one (D.c k) D.psi (P k) D.hψ1 (x k) h
      have : levelOf (P k (mk2 (x k 0) (x k 1))) = D.c 0 := by rw [← hface]; exact hklev
      exact absurd this (ne_of_gt (D.hlev k (mk2 (x k 0) (x k 1))))
    · exact h
  · rw [hxk]; exact hklev

/-- **Every bottom triple point of the block `0` is the lift of its own class triple.** -/
lemma endTriple_surj (D : EndDesign P) {x : Fin 3 → EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ bottomBdryMeet CappingSpace D.sweep 0) :
    ∃ y : Fin 3 → EuclideanSpace ℝ (Fin 2), y ∈ classTripleSet P ∧ D.endTriple y = x := by
  obtain ⟨⟨hbox, h01, h02, -⟩, hx0⟩ := hx
  set y : Fin 3 → EuclideanSpace ℝ (Fin 2) := fun k => mk2 (x k 0) (x k 1) with hydef
  have hyk : ∀ k, y k = mk2 (x k 0) (x k 1) := fun k => by simp [hydef]
  have hyk0 : ∀ k, y k 0 = x k 0 := fun k => by rw [hyk k]; exact mk2_apply_zero (x k 0) (x k 1)
  have hyk1 : ∀ k, y k 1 = x k 1 := fun k => by rw [hyk k]; exact mk2_apply_one (x k 0) (x k 1)
  have hEq : ∀ k : Fin 3, D.sweep k (x k) = D.sweep 0 (x 0) := by
    intro k
    fin_cases k
    · rfl
    · exact h01.symm
    · exact h02.symm
  have h0lev : levelOf (D.sweep 0 (x 0)) = D.c 0 := by
    have hface : D.sweep 0 (x 0) = shadow (D.c 0) (D.hcpos 0) (P 0 (y 0)) := by
      simpa only [sweep, ← hyk 0] using
        clampedSweep_face_zero (D.c 0) (D.hcpos 0) D.psi (P 0) D.hψ0 (x 0) hx0
    rw [hface, levelOf_shadow]
  have hybox0 : ∀ k : Fin 3, y k 0 ∈ Set.Icc (0 : ℝ) 1 :=
    fun k => by rw [hyk0 k]; exact (hbox k) 0
  have hybox1 : ∀ k : Fin 3, y k 1 ∈ Set.Icc (0 : ℝ) 1 :=
    fun k => by rw [hyk1 k]; exact (hbox k) 1
  have hybox : ∀ k : Fin 3, y k ∈ Submission.Drive.unitBox 1 := by
    intro k i
    fin_cases i
    · exact hybox0 k
    · exact hybox1 k
  have hycls : ∀ k : Fin 3, planeClassMap (P k) (y k) = planeClassMap (P 0) (y 0) := by
    intro k
    have h2 : (cappingSpaceHomeoProj (D.sweep k (x k))).2
        = (cappingSpaceHomeoProj (P k (mk2 (x k 0) (x k 1)))).2 := by
      simpa only [sweep] using cls_clampedSweep (D.c k) D.psi (P k) (x k)
    have h3 : (cappingSpaceHomeoProj (D.sweep 0 (x 0))).2
        = (cappingSpaceHomeoProj (P 0 (mk2 (x 0 0) (x 0 1)))).2 := by
      simpa only [sweep] using cls_clampedSweep (D.c 0) D.psi (P 0) (x 0)
    have h1 : (cappingSpaceHomeoProj (D.sweep k (x k))).2
        = (cappingSpaceHomeoProj (D.sweep 0 (x 0))).2 := by rw [hEq k]
    show (cappingSpaceHomeoProj (P k (y k))).2 = (cappingSpaceHomeoProj (P 0 (y 0))).2
    rw [hyk k, hyk 0]
    exact h2.symm.trans (h1.trans h3)
  -- block `0`
  have hx0' : x 0 = D.endTriple y 0 := by
    rw [endTriple_apply_zero]
    have h : x 0 = botVec (x 0 0) (x 0 1) := by
      rw [botVec]
      ext i
      fin_cases i
      · simp
      · simp
      · simpa using hx0
    rw [h, hyk0 0, hyk1 0]
  -- blocks `1` and `2`: the radial parameter is forced by the level
  have hx1' : x 1 = D.endTriple y 1 := by
    obtain ⟨hmem, hlev⟩ := D.rad_data hbox 1 fin3_one_ne_zero (hEq 1) h0lev
    have hlev' : levelOf (D.sweep 1 (radVec (y 1) (x 1 2))) = D.c 0 := by
      simpa only [← hyk 1] using hlev
    have hrad := D.rad_eq 1 fin3_one_ne_zero (y 1) hmem hlev'
    have hx1eq : radVec (y 1) (x 1 2) = x 1 := by
      rw [radVec]
      ext i
      fin_cases i
      · simpa [mk2_apply_zero] using congrArg (fun u : EuclideanSpace ℝ (Fin 2) => u 0) (hyk 1)
      · simpa [mk2_apply_one] using congrArg (fun u : EuclideanSpace ℝ (Fin 2) => u 1) (hyk 1)
      · simp
    rw [endTriple_apply_one, ← hrad]
    exact hx1eq.symm
  have hx2' : x 2 = D.endTriple y 2 := by
    obtain ⟨hmem, hlev⟩ := D.rad_data hbox 2 fin3_two_ne_zero (hEq 2) h0lev
    have hlev' : levelOf (D.sweep 2 (radVec (y 2) (x 2 2))) = D.c 0 := by
      simpa only [← hyk 2] using hlev
    have hrad := D.rad_eq 2 fin3_two_ne_zero (y 2) hmem hlev'
    have hx2eq : radVec (y 2) (x 2 2) = x 2 := by
      rw [radVec]
      ext i
      fin_cases i
      · simpa [mk2_apply_zero] using congrArg (fun u : EuclideanSpace ℝ (Fin 2) => u 0) (hyk 2)
      · simpa [mk2_apply_one] using congrArg (fun u : EuclideanSpace ℝ (Fin 2) => u 1) (hyk 2)
      · simp
    rw [endTriple_apply_two, ← hrad]
    exact hx2eq.symm
  refine ⟨y, mem_classTripleSet.mpr ⟨hybox, hycls⟩, ?_⟩
  funext k
  fin_cases k
  · exact hx0'.symm
  · exact hx1'.symm
  · exact hx2'.symm

/-- **The injectivity of the lift on the class triples**: the class coordinates of the lift recover the
triple. -/
lemma endTriple_injOn (D : EndDesign P) {a b : Fin 3 → EuclideanSpace ℝ (Fin 2)}
    (ha : a ∈ classTripleSet P) (hb : b ∈ classTripleSet P) (hab : D.endTriple a = D.endTriple b) :
    a = b := by
  funext k
  have h := congrArg (fun v : Fin 3 → EuclideanSpace ℝ (Fin 3) => mk2 (v k 0) (v k 1)) hab
  rw [mk2_endTriple, mk2_endTriple] at h
  exact h

/-- **The class triples are in bijection with the bottom triple points of the block `0`**, so their
cardinalities agree. -/
lemma ncard_bottomBdryMeet_zero_eq_ncard_classTripleSet (D : EndDesign P) :
    (classTripleSet P).ncard = (bottomBdryMeet CappingSpace D.sweep 0).ncard :=
  Set.ncard_congr
    (fun (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) (_ : y ∈ classTripleSet P) => D.endTriple y)
    (fun _ hy => D.endTriple_mem_bottomBdryMeet hy)
    (fun _ _ ha hb hab => D.endTriple_injOn ha hb hab)
    (fun x hx => by
      obtain ⟨y, hy, hyx⟩ := D.endTriple_surj hx
      exact ⟨y, hy, hyx⟩)

end EndDesign

theorem odd_sum_bottomBdryMeet_of_classTriple
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → Work.Drive.CappingSpace)
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (hreg : Work.Drive.ClassTripleRegular P)
    (hψ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1)) (hanti : StrictAntiOn ψ (Set.Icc (0 : ℝ) 1))
    (hcpos : ∀ k : Fin 3, 0 < c k) (hck : ∀ k : Fin 3, c k ≤ c 0)
    (hc1 : c 1 < c 0) (hc2 : c 2 < c 0)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < Work.Drive.levelOf (P k y))
    (hfin : (Work.Drive.classTripleSet P).Finite)
    (hodd : Odd (Work.Drive.classTripleSet P).ncard) :
    Odd ((Work.Drive.bottomBdryMeet Work.Drive.CappingSpace
            (fun k => Work.Drive.clampedSweep (c k) ψ (P k)) 0).ncard
      + (Work.Drive.bottomBdryMeet Work.Drive.CappingSpace
            (fun k => Work.Drive.clampedSweep (c k) ψ (P k)) 1).ncard
      + (Work.Drive.bottomBdryMeet Work.Drive.CappingSpace
            (fun k => Work.Drive.clampedSweep (c k) ψ (P k)) 2).ncard) := by
  classical
  let D : EndDesign P :=
    { c := c
      psi := ψ
      hcpos := hcpos
      hcne := by
        intro k hk
        fin_cases k
        · exact absurd rfl hk
        · exact hc1
        · exact hc2
      hlev := hlev
      hψ0 := hψ0
      hψ1 := hψ1
      hψ01 := hψ01
      hcont := hcont
      hanti := hanti }
  change Odd ((bottomBdryMeet CappingSpace D.sweep 0).ncard
    + (bottomBdryMeet CappingSpace D.sweep 1).ncard
    + (bottomBdryMeet CappingSpace D.sweep 2).ncard)
  have hlev' : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), D.c k ≤ levelOf (P k y) := by
    intro k y
    fin_cases k
    · exact le_of_lt (D.hlev 0 y)
    · exact le_trans (le_of_lt (D.hcne 1 fin3_one_ne_zero)) (le_of_lt (D.hlev 1 y))
    · exact le_trans (le_of_lt (D.hcne 2 fin3_two_ne_zero)) (le_of_lt (D.hlev 2 y))
  have hbot1 : bottomBdryMeet CappingSpace D.sweep 1 = ∅ :=
    bottomBdryMeet_eq_empty_of_lt_level_local D.c D.hcpos D.psi D.hψ0 D.hψ01 P hlev'
      (k := 1) (l := 0) (D.hcne 1 fin3_one_ne_zero)
  have hbot2 : bottomBdryMeet CappingSpace D.sweep 2 = ∅ :=
    bottomBdryMeet_eq_empty_of_lt_level_local D.c D.hcpos D.psi D.hψ0 D.hψ01 P hlev'
      (k := 2) (l := 0) (D.hcne 2 fin3_two_ne_zero)
  have hcard := D.ncard_bottomBdryMeet_zero_eq_ncard_classTripleSet
  rw [hbot1, hbot2, Set.ncard_empty]
  simp only [add_zero]
  rw [← hcard]
  exact hodd

end

end Work.Drive
