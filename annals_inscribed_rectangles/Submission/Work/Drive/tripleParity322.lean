import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.SeamSweep
import Submission.Work.Drive.classTripleRegular
import Submission.Work.Drive.cappingSpaceHomeoProj_rotCapping
import Submission.Work.Drive.linCapping

/-!
# The `(3,2,2)` case of the mod-2 boundary parity: vocabulary

**The `(3,2,2)` parity engine**: a one-parameter family of *triples of `2`-chains* in a `3`-manifold,
i.e. (in coordinates) maps `F k : ℝ × ℝ² → ℝ³`, and the parity of the number of *triple meets*
`y ↦ (F 0 (s, y 0) = F 1 (s, y 1) = F 2 (s, y 2))` over `(y 0, y 1, y 2) ∈ (unitBox 1)³`.

The count is the mod-2 degree of the difference map `famDiff F` on the `7`-box (the family parameter
plus the three parameter squares).  The engine's content is *homotopy invariance*:

> the parity of the triple-meet count at `s = 0` equals the parity at `s = 1`,

which is the bordism invariance of the triple count — the step that turns "three essential `2`-cycles in
`ℝP³` meet oddly" (Hugelmeyer's `n_{-λ}` odd, i.e. `x³ ≠ 0` in `ℤ/2[x]/(x⁴)`) into the parity of
`Work.Drive.classTripleSet` for the design's planes, with a *linear* projective plane as the base case
(`Work.Drive.projective_planes_meet_oddly`).

Why `(3,2,2)`: a bordism between a class image (a `2`-cycle) and a linear projective plane is a
`3`-chain, and the count to be shown invariant is a triple count of one `3`-chain against two closed
`2`-chains.  In the box language this is `ParityProp` with `m = 6` (`7`-box), and the seam of the plane
parameter squares plays the role of the "closed" direction: its boundary contributions cancel pairwise
under the seam involution.
-/

set_option autoImplicit false

namespace Work.Drive

noncomputable section

open Manifold
open scoped Manifold ContDiff Topology

/-! ## The coordinate bookkeeping of the `7`-box -/

/-- The family parameter as a coordinate of the `7`-box. -/
def famS : Fin 7 := 0

/-- The coordinate of the `i`-th coordinate of the `k`-th plane parameter in the `7`-box. -/
def famC (k : Fin 3) (i : Fin 2) : Fin 7 := ⟨1 + 2 * k.val + i.val, by omega⟩

lemma famC_val (k : Fin 3) (i : Fin 2) : (famC k i : ℕ) = 1 + 2 * k.val + i.val := rfl

lemma famC_ne_famS (k : Fin 3) (i : Fin 2) : famC k i ≠ famS := by
  intro h
  have := congrArg Fin.val h
  rw [famC_val, famS] at this
  omega

lemma famC_injective {k k' : Fin 3} {i i' : Fin 2} (h : famC k i = famC k' i') :
    k = k' ∧ i = i' := by
  have hv : 2 * k.val + i.val = 2 * k'.val + i'.val := by
    have := congrArg Fin.val h; rw [famC_val, famC_val] at this; omega
  have hk : k = k' := Fin.ext (by omega)
  subst hk
  exact ⟨rfl, Fin.ext (by omega)⟩

/-- The `k`-th plane parameter of a point of the `7`-box. -/
def famY (x : EuclideanSpace ℝ (Fin 7)) (k : Fin 3) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 fun i : Fin 2 => x (famC k i)

@[simp] lemma famY_apply (x : EuclideanSpace ℝ (Fin 7)) (k : Fin 3) (i : Fin 2) :
    famY x k i = x (famC k i) := by
  simp only [famY, WithLp.ofLp_toLp]

/-- The family parameter of a point of the `7`-box. -/
def famT (x : EuclideanSpace ℝ (Fin 7)) : ℝ := x famS

/-! ## The pairing `ℝ³ × ℝ³ → ℝ⁶` and the difference map -/

/-- Two vectors of `ℝ³` stacked into a vector of `ℝ⁶`. -/
def pair33 (a b : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 6) :=
  WithLp.toLp 2 fun k : Fin 6 =>
    if h : k.val < 3 then a ⟨k.val, h⟩ else b ⟨k.val - 3, by omega⟩

@[simp] lemma pair33_apply_fst (a b : EuclideanSpace ℝ (Fin 3)) (k : Fin 3) :
    pair33 a b (Fin.castAdd 3 k) = a k := by
  simp only [pair33, WithLp.ofLp_toLp]
  rw [dif_pos (by simp)]
  exact congrArg a (Fin.ext (by simp))

@[simp] lemma pair33_apply_snd (a b : EuclideanSpace ℝ (Fin 3)) (k : Fin 3) :
    pair33 a b (Fin.natAdd 3 k) = b k := by
  simp only [pair33, WithLp.ofLp_toLp]
  rw [dif_neg (by simp)]
  exact congrArg b (Fin.ext (by simp))

@[simp] lemma pair33_apply_lt (a b : EuclideanSpace ℝ (Fin 3)) {i : Fin 6} (h : i.val < 3) :
    pair33 a b i = a ⟨i.val, h⟩ := by
  simp only [pair33, WithLp.ofLp_toLp]
  rw [dif_pos h]

@[simp] lemma pair33_apply_ge (a b : EuclideanSpace ℝ (Fin 3)) {i : Fin 6} (h : ¬ i.val < 3) :
    pair33 a b i = b ⟨i.val - 3, by omega⟩ := by
  simp only [pair33, WithLp.ofLp_toLp]
  rw [dif_neg h]

/-- **The `(3,2,2)` difference map** of a family of triples of `2`-chains: at the point
`x = (s, y 0, y 1, y 2)` of the `7`-box it is `(F 0 (s, y 0) − F 1 (s, y 1), F 0 (s, y 0) − F 2 (s, y 2))`.
Its zeros are the triple meets of the three chains at the family parameter `s`. -/
def famDiff (F : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 7)) : EuclideanSpace ℝ (Fin 6) :=
  pair33 (F 0 (famT x, famY x 0) - F 1 (famT x, famY x 1))
    (F 0 (famT x, famY x 0) - F 2 (famT x, famY x 2))

lemma famDiff_eq_zero_iff (F : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (x : EuclideanSpace ℝ (Fin 7)) :
    famDiff F x = 0 ↔ F 0 (famT x, famY x 0) = F 1 (famT x, famY x 1) ∧
      F 0 (famT x, famY x 0) = F 2 (famT x, famY x 2) := by
  have hdiff : famDiff F x =
      pair33 (F 0 (famT x, famY x 0) - F 1 (famT x, famY x 1))
        (F 0 (famT x, famY x 0) - F 2 (famT x, famY x 2)) := rfl
  constructor
  · intro h
    have h1 : F 0 (famT x, famY x 0) - F 1 (famT x, famY x 1) = 0 := by
      ext j
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 6) => v (Fin.castAdd 3 j)) h
      rw [hdiff] at this
      simpa using this
    have h2 : F 0 (famT x, famY x 0) - F 2 (famT x, famY x 2) = 0 := by
      ext j
      have := congrArg (fun v : EuclideanSpace ℝ (Fin 6) => v (Fin.natAdd 3 j)) h
      rw [hdiff] at this
      simpa using this
    exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩
  · rintro ⟨h1, h2⟩
    rw [hdiff, sub_eq_zero.mpr h1, sub_eq_zero.mpr h2]
    ext i
    fin_cases i <;> simp [pair33]

/-! ## The triple-meet set -/

/-- **The triple-meet set** of a family of triples of `2`-chains at the family parameter `s`. -/
def tripleMeetFam (F : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (s : ℝ) : Set (Fin 3 → EuclideanSpace ℝ (Fin 2)) :=
  {y | (∀ k, y k ∈ Submission.Drive.unitBox 1) ∧
    (∀ k, F k (s, y k) = F 0 (s, y 0))}

lemma mem_tripleMeetFam {F : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    {s : ℝ} {y : Fin 3 → EuclideanSpace ℝ (Fin 2)} :
    y ∈ tripleMeetFam F s ↔ (∀ k, y k ∈ Submission.Drive.unitBox 1) ∧
      (∀ k, F k (s, y k) = F 0 (s, y 0)) := Iff.rfl


/-! ## The `(3,2,2)`-with-a-`3`-chain shape: one bordism of one chain, two fixed closed chains -/

/-- **The triple-meet set of three single `2`-chains** (in coordinates): the parameter triples at which
the three maps agree. -/
def tripleMeet3 (F : Fin 3 → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) :
    Set (Fin 3 → EuclideanSpace ℝ (Fin 2)) :=
  {y | (∀ k, y k ∈ Submission.Drive.unitBox 1) ∧ (∀ k, F k (y k) = F 0 (y 0))}

lemma mem_tripleMeet3 {F : Fin 3 → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    {y : Fin 3 → EuclideanSpace ℝ (Fin 2)} :
    y ∈ tripleMeet3 F ↔ (∀ k, y k ∈ Submission.Drive.unitBox 1) ∧
      (∀ k, F k (y k) = F 0 (y 0)) := Iff.rfl

/-- **The family of triples in which only the first chain moves**: `A` is the bordism (a one-parameter
family of `2`-chains), `B` and `C` are the two fixed closed `2`-chains. -/
def famOfHomotopy (A : ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (B C : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) :
    Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3) :=
  ![A, fun p => B p.2, fun p => C p.2]

@[simp] lemma famOfHomotopy_zero (A : ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (B C : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) :
    famOfHomotopy A B C 0 = A := rfl

@[simp] lemma famOfHomotopy_one (A : ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (B C : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) :
    famOfHomotopy A B C 1 = fun p => B p.2 := rfl

@[simp] lemma famOfHomotopy_two (A : ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (B C : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) :
    famOfHomotopy A B C 2 = fun p => C p.2 := rfl

/-- **The single-chain triple triple of the family at the parameter `s`**: the first chain at the
parameter `s`, the two fixed chains. -/
def tripleAt (A : ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (B C : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (s : ℝ) :
    Fin 3 → EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3) :=
  ![fun y => A (s, y), B, C]

@[simp] lemma tripleAt_zero (A : ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (B C : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (s : ℝ) :
    tripleAt A B C s 0 = fun y => A (s, y) := rfl

@[simp] lemma tripleAt_one (A : ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (B C : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (s : ℝ) :
    tripleAt A B C s 1 = B := rfl

@[simp] lemma tripleAt_two (A : ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (B C : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (s : ℝ) :
    tripleAt A B C s 2 = C := rfl

/-- **The identification of the family's meet set with the single-chain one.**  The triple meets of the
family `famOfHomotopy A B C` at the parameter `s` are exactly the triple meets of the three chains
`(A (s, ·), B, C)`. -/
lemma tripleMeetFam_famOfHomotopy
    (A : ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (B C : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) (s : ℝ) :
    tripleMeetFam (famOfHomotopy A B C) s = tripleMeet3 (tripleAt A B C s) := by
  ext y
  simp only [mem_tripleMeetFam, mem_tripleMeet3, famOfHomotopy, tripleAt]
  constructor
  · rintro ⟨hbox, hagree⟩
    refine ⟨hbox, ?_⟩
    intro k
    have hk := hagree k
    fin_cases k <;> simpa using hk
  · rintro ⟨hbox, hagree⟩
    refine ⟨hbox, ?_⟩
    intro k
    have hk := hagree k
    fin_cases k <;> simpa using hk


/-! ## The essentiality input, in the "homotopic to a linear plane" form -/

/-- **Hugelmeyer's standing hypothesis on the planes, in the form the ends parity consumes**: the
class map of the plane presentation is homotopic — through class maps satisfying the *seam* condition,
i.e. maps of `ℝP²` — to a *surjective* parametrisation of a **linear** projective plane `projLine L`
(`L ⊆ ℝ⁴` of dimension `3`).

This is the paper's "`[P]` generates `H₂(ℝP³; ℤ/2)`" (equivalently `n_{-λ}` odd, i.e. `x³ ≠ 0` in
`ℤ/2[x]/(x⁴)`) in the form in which it feeds the bordism parity of
`Work.Drive.even_ncard_tripleMeet3_add_of_bordism`: each class image is replaced, one at a time, by the
linear projective plane it is bordant to, and the linear case is
`Work.Drive.projective_planes_meet_oddly`.

For the design's planes this holds because the plane chart's plane is the capped configuration Möbius
strip (its seam is the `(2,1)` torus knot, so the class image is homologically non-trivial), and the
statement is preserved by `rotCapping` and by `linCapping`.  The frontier is that upgrading
"homologically non-trivial" to "homotopic to the inclusion" needs `[ℝP², ℝP³] ≅ ℤ/2`, which is
obstruction theory and not in Mathlib; the alternative is an explicit straightening of the chart's
class map `z ↦ [confProjVecOf u z d z]` to a linear one. -/
def IsLinearizableClass (P : EuclideanSpace ℝ (Fin 2) → CappingSpace) : Prop :=
  ∃ (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (L : Submodule ℝ (Eucl 3)),
    Module.finrank ℝ L = 3 ∧ Continuous H ∧
    (∀ y : EuclideanSpace ℝ (Fin 2), H (0, y) = planeClassMap P y) ∧
    (∀ (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y → H (s, y) = H (s, seamInv2 y)) ∧
    (∀ y : EuclideanSpace ℝ (Fin 2), H (1, y) ∈ projLine L) ∧
    (∀ q ∈ projLine L, ∃ y : EuclideanSpace ℝ (Fin 2), H (1, y) = q)


/-! ## The rotation is a class perturbation with `A = diagRotL u` -/

/-- **The rotation `rotCapping u` is the class perturbation by the diagonal rotation.**  Both acts on
the transparent coordinates `(level, class)` by `(level, projRot t ·)` and `(level, map (diagRotL t) ·)`
respectively, and `Work.Drive.projMap_diagRotL` identifies the two. -/
theorem rotCapping_eq_linCapping_diagRotL (t : ℝ) :
    rotCapping ((t : ℝ) : UnitAddCircle) = linCapping (diagRotL t) := by
  funext p
  apply cappingSpaceHomeoProj.injective
  rw [cappingSpaceHomeoProj_rotCapping t p, cappingSpaceHomeoProj_linCapping (diagRotL t) p]
  simp [projMap_diagRotL t]

end

end Work.Drive
