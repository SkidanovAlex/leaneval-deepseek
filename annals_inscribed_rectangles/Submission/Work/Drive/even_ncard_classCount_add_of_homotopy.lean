import Mathlib
import Submission.Work.Drive.projTimesLine
import Submission.Work.Drive.classTripleCount
import Submission.Work.Drive.even_ncard_meet32_encoded
import Submission.Work.Drive.meet32_bordism_invariance
import Submission.Work.Drive.intersection_bordism3
import Submission.Work.Drive.projCharted

/-!
# The bordism invariance of the class-triple count of the encoded homotopy chains

`Work.Drive.even_ncard_meet32_encoded` says that for a bordism `W` of `2`-cycles in `ℝP³` and two
`2`-cycles `A`, `B`, the *encoded* chains
`Work.Drive.encodedChains W A B c`
(the bordism pinned at the interior time `c ∈ (0,1)`, the two `2`-cycles thickened in their third
parameter) have the same mod-`2` triple intersection number at their two ends:

`Even ((topBdryMeet M D 0).ncard + (bottomBdryMeet M D 0).ncard)`.

Here we read the two ends as the **class-triple counts** of the two end class maps: for the homotopy
`W = homotopyChain H`, i.e. `W x = H (x 2, pt2 (x 0) (x 1))`, the top face of the block `0` is
`x 0 2 = 1` where `W (x 0) = H (1, ·)`, and the bottom face is `x 0 2 = 0` where `W (x 0) = H (0, ·)`.

The mathematical content is the **bijection** `Work.Drive.ncard_classCount_faceBdryMeet`:

* a triple of the unit cube at which the three encoded chains meet, with `x 0 2 = t` (`t ∈ {0,1}`),
  is exactly a triple of *class coordinates* `y k = pt2 (x k 0) (x k 1)` of the unit square at which
  the three class maps `W (· , t)`, `A`, `B` agree — the two other blocks are `2`-cycles thickened
  in their third parameter, so the triple point condition pins their third coordinates to `c` and
  forces the second coordinates back to the class coordinates;
* conversely a class triple lifts to the cube triple with third coordinates `t, c, c`.

Hence `(topBdryMeet M D 0).ncard = (classCount ![fun y => H (1, y), A, B]).ncard` and likewise at the
bottom face, and the parity statement for the encoded chains becomes the parity statement for the
class-triple counts of the two ends of the homotopy — the invariance which lets one replace a class
map by a homotopic one in the mod-`2` count (the paper's "`[P]` generates `H₂(ℝP³; ℤ/2)`" step of the
ends clause).

**Note for the consumer.**  The draft `Submission/Work/Drive/classTripleBordism.lean` declares a
declaration of the *same* name `Work.Drive.even_ncard_classCount_add_of_homotopy` (with a `sorry`).
Nothing imports it, but if both modules were ever imported into one file the two declarations would
clash, so that draft should be reduced to a bare `import` of this module.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-! ## Coordinate bookkeeping for the cube and the square -/

/-- `pt2` recovers a point of the parameter square from its two coordinates. -/
private lemma pt2_eta (y : EuclideanSpace ℝ (Fin 2)) : pt2 (y 0) (y 1) = y := by
  ext i
  fin_cases i <;> simp [pt2]

/-- The canonical enumeration of `Fin 2`.  Stated as a disjunction so that the case analysis
substitutes the *canonical* numerals `0`, `1` (rather than the `Fin.mk`-terms produced by
`fin_cases`), which is what the `simp` lemmas `Work.Drive.mk3t_zero` and friends match. -/
private lemma fin2_eq_zero_or_one (i : Fin 2) : i = 0 ∨ i = 1 := by revert i; decide

/-- The canonical enumeration of `Fin 3`, in the same form as `fin2_eq_zero_or_one`. -/
private lemma fin3_eq_zero_or_one_or_two (k : Fin 3) : k = 0 ∨ k = 1 ∨ k = 2 := by
  revert k; decide

/-- **The lift of a class triple to a cube triple at the face `x 0 2 = t`**: the first block takes
the third coordinate `t`, the two others the third coordinate `c` (the pinned time of the encoding). -/
private def faceLift (c t : ℝ) (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) :
    Fin 3 → EuclideanSpace ℝ (Fin 3) :=
  fun k => if k = 0 then mk3t (y 0) t else mk3t (y k) c

/-- **The class coordinates of a cube triple**: the two first coordinates of each block, read in the
parameter square. -/
private def faceProj (x : Fin 3 → EuclideanSpace ℝ (Fin 3)) :
    Fin 3 → EuclideanSpace ℝ (Fin 2) :=
  fun k => pt2 (x k 0) (x k 1)

@[simp] private lemma faceLift_zero (c t : ℝ) (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) :
    faceLift c t y 0 = mk3t (y 0) t := by simp [faceLift]

@[simp] private lemma faceLift_one (c t : ℝ) (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) :
    faceLift c t y 1 = mk3t (y 1) c := by simp [faceLift]

@[simp] private lemma faceLift_two (c t : ℝ) (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) :
    faceLift c t y 2 = mk3t (y 2) c := by simp [faceLift]

/-- The first coordinate of the lift is the first coordinate of the class triple. -/
private lemma faceLift_coord_zero (c t : ℝ) (y : Fin 3 → EuclideanSpace ℝ (Fin 2))
    (k : Fin 3) : (faceLift c t y k) 0 = (y k) 0 := by
  rcases fin3_eq_zero_or_one_or_two k with rfl | rfl | rfl <;> simp [faceLift]

/-- The second coordinate of the lift is the second coordinate of the class triple. -/
private lemma faceLift_coord_one (c t : ℝ) (y : Fin 3 → EuclideanSpace ℝ (Fin 2))
    (k : Fin 3) : (faceLift c t y k) 1 = (y k) 1 := by
  rcases fin3_eq_zero_or_one_or_two k with rfl | rfl | rfl <;> simp [faceLift]

/-! ## The bijection between the class triples and the face triple points -/

/-- **The class-triple count of the class maps `W (·, t)`, `A`, `B` is the count of the triple points
of the encoded chains at the face `x 0 2 = t` of the block `0`.**

For `t ∈ {0,1}` — the bottom and the top face of the bordism block — the triples of the unit cube at
which the three encoded chains meet are, after forgetting the third coordinates `(t, c, c)`, exactly
the triples of class coordinates of the square at which the three class maps agree: the meet
conditions are the class coincidences, and the box conditions are the box conditions of the class
triples. -/
private lemma ncard_classCount_faceBdryMeet
    (W : EuclideanSpace ℝ (Fin 3) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    {c t : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (ht : t = 0 ∨ t = 1) :
    (classCount ![(fun y => W (mk3t y t)), A, B]).ncard
      = ({x : Fin 3 → EuclideanSpace ℝ (Fin 3) |
          x ∈ tripleBdryMeet (Projectivization ℝ (Eucl 3) × ℝ)
                (encodedChains W A B c) 0 ∧ x 0 2 = t}).ncard := by
  classical
  have ht01 : t ∈ Set.Icc (0 : ℝ) 1 := by rcases ht with h | h <;> simp [h]
  have hc01 : c ∈ Set.Icc (0 : ℝ) 1 := ⟨hc0.le, hc1.le⟩
  refine Set.ncard_congr (fun y _ => faceLift c t y) ?_ ?_ ?_
  · -- the lift of a class triple is a face triple point
    intro y hy
    obtain ⟨hybox, hycls⟩ := mem_classCount.mp hy
    have hbox : ∀ k : Fin 3, faceLift c t y k ∈ Submission.Drive.unitBox 2 := by
      intro k i
      rcases fin3_eq_zero_or_one_or_two k with rfl | rfl | rfl <;>
        rcases fin3_eq_zero_or_one_or_two i with rfl | rfl | rfl <;>
        simp only [faceLift_zero, faceLift_one, faceLift_two, mk3t_zero, mk3t_one, mk3t_two]
      · exact hybox 0 0
      · exact hybox 0 1
      · exact ht01
      · exact hybox 1 0
      · exact hybox 1 1
      · exact hc01
      · exact hybox 2 0
      · exact hybox 2 1
      · exact hc01
    have hA : A (y 1) = W (mk3t (y 0) t) := by simpa using hycls 1
    have hB : B (y 2) = W (mk3t (y 0) t) := by simpa using hycls 2
    refine ⟨⟨hbox, ?_, ?_, ?_⟩, ?_⟩
    · -- the block `0` meets the block `1`
      simp only [encodedChains_zero, encodedChains_one, faceLift_zero, faceLift_one,
        mk3t_zero, mk3t_one, mk3t_two, pt2_eta]
      rw [hA]
    · -- the block `0` meets the block `2`
      simp only [encodedChains_zero, encodedChains_two, faceLift_zero, faceLift_two,
        mk3t_zero, mk3t_one, mk3t_two, pt2_eta]
      rw [hB]
    · -- the first block is on the face `x 0 2 = t`
      refine ⟨hbox 0, 2, ?_⟩
      simpa only [faceLift_zero, mk3t_two] using ht
    · simpa only [faceLift_zero, mk3t_two] using ht
  · -- the lift is injective on the class triples
    intro a b _ _ hab
    funext k
    have h0 : a k 0 = b k 0 := by
      have h := congrArg (fun v : Fin 3 → EuclideanSpace ℝ (Fin 3) => v k 0) hab
      simp only [faceLift_coord_zero] at h
      exact h
    have h1 : a k 1 = b k 1 := by
      have h := congrArg (fun v : Fin 3 → EuclideanSpace ℝ (Fin 3) => v k 1) hab
      simp only [faceLift_coord_one] at h
      exact h
    ext i
    rcases fin2_eq_zero_or_one i with rfl | rfl
    · exact h0
    · exact h1
  · -- every face triple point is the lift of its class coordinates
    rintro x ⟨⟨hbox, h01, h02, -⟩, hx0⟩
    have hf1 : W (x 0) = A (faceProj x 1) := by
      have h := h01
      simp only [encodedChains_zero, encodedChains_one] at h
      have := congrArg Prod.fst h
      simpa [faceProj] using this
    have hf2 : W (x 0) = B (faceProj x 2) := by
      have h := h02
      simp only [encodedChains_zero, encodedChains_two] at h
      have := congrArg Prod.fst h
      simpa [faceProj] using this
    have hc1 : x 1 2 = c := by
      have h := h01
      simp only [encodedChains_zero, encodedChains_one] at h
      exact (congrArg Prod.snd h).symm
    have hc2 : x 2 2 = c := by
      have h := h02
      simp only [encodedChains_zero, encodedChains_two] at h
      exact (congrArg Prod.snd h).symm
    have hx0' : x 0 = mk3t (faceProj x 0) t := by
      ext i
      rcases fin3_eq_zero_or_one_or_two i with rfl | rfl | rfl <;>
        simp [faceProj, pt2, mk3t, hx0]
    have hx1' : x 1 = mk3t (faceProj x 1) c := by
      ext i
      rcases fin3_eq_zero_or_one_or_two i with rfl | rfl | rfl <;>
        simp [faceProj, pt2, mk3t, hc1]
    have hx2' : x 2 = mk3t (faceProj x 2) c := by
      ext i
      rcases fin3_eq_zero_or_one_or_two i with rfl | rfl | rfl <;>
        simp [faceProj, pt2, mk3t, hc2]
    refine ⟨faceProj x, ?_, ?_⟩
    · -- the class coordinates of a face triple point are a class triple
      refine mem_classCount.mpr ⟨?_, ?_⟩
      · intro k i
        rcases fin2_eq_zero_or_one i with rfl | rfl
        · simp only [faceProj, pt2_zero]; exact hbox k 0
        · simp only [faceProj, pt2_one]; exact hbox k 1
      · intro k
        rcases fin3_eq_zero_or_one_or_two k with rfl | rfl | rfl
        · rfl
        · show A (faceProj x 1) = W (mk3t (faceProj x 0) t)
          exact hf1.symm.trans (congrArg W hx0')
        · show B (faceProj x 2) = W (mk3t (faceProj x 0) t)
          exact hf2.symm.trans (congrArg W hx0')
    · -- and the lift of those class coordinates is the point itself
      funext k
      rcases fin3_eq_zero_or_one_or_two k with rfl | rfl | rfl
      · rw [faceLift_zero]; exact hx0'.symm
      · rw [faceLift_one]; exact hx1'.symm
      · rw [faceLift_two]; exact hx2'.symm

/-- **The bordism invariance of the class-triple count**: for a homotopy `H` of the class map in the
first slot and two further class maps `A`, `B`, the class-triple counts at the two ends of the
homotopy have the same parity,

`#{H 0 = A = B} ≡ #{H 1 = A = B} (mod 2)`,

whenever the encoded chains of the homotopy satisfy the manifold hypotheses `Meet3Hyp`. -/
theorem even_ncard_classCount_add_of_homotopy
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) (Projectivization ℝ (Eucl 3) × ℝ)]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Projectivization ℝ (Eucl 3) × ℝ)]
    (H : ℝ × EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    (A B : EuclideanSpace ℝ (Fin 2) → Projectivization ℝ (Eucl 3))
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1)
    (h : Meet3Hyp (Projectivization ℝ (Eucl 3) × ℝ)
      (encodedChains (fun x => H (x 2, pt2 (x 0) (x 1))) A B c)) :
    Even ((classCount (fun k => ![fun y => H (0, y), A, B] k)).ncard
      + (classCount (fun k => ![fun y => H (1, y), A, B] k)).ncard) := by
  classical
  -- the homotopy as a bordism of `2`-cycles in `ℝP³`
  let W : EuclideanSpace ℝ (Fin 3) → Projectivization ℝ (Eucl 3) :=
    fun x => H (x 2, pt2 (x 0) (x 1))
  -- the `3 + 2 + 2` engine: the two ends of the encoded chains have the same parity
  have hmain : Even ((topBdryMeet (Projectivization ℝ (Eucl 3) × ℝ)
        (encodedChains W A B c) 0).ncard
      + (bottomBdryMeet (Projectivization ℝ (Eucl 3) × ℝ) (encodedChains W A B c) 0).ncard) :=
    even_ncard_meet32_encoded (Projectivization ℝ (Eucl 3)) W A B c hc0 hc1 h
  -- the two ends are class-triple counts
  have htop := ncard_classCount_faceBdryMeet W A B hc0 hc1 (c := c) (t := 1) (Or.inr rfl)
  have hbot := ncard_classCount_faceBdryMeet W A B hc0 hc1 (c := c) (t := 0) (Or.inl rfl)
  have htop' : (topBdryMeet (Projectivization ℝ (Eucl 3) × ℝ)
        (encodedChains W A B c) 0).ncard
      = (classCount ![(fun y => W (mk3t y 1)), A, B]).ncard := htop.symm
  have hbot' : (bottomBdryMeet (Projectivization ℝ (Eucl 3) × ℝ)
        (encodedChains W A B c) 0).ncard
      = (classCount ![(fun y => W (mk3t y 0)), A, B]).ncard := hbot.symm
  -- the two ends of `W` are the two class maps `H (0, ·)` and `H (1, ·)`
  have hfun0 : (fun y : EuclideanSpace ℝ (Fin 2) => W (mk3t y 0)) = fun y => H (0, y) := by
    funext y
    show H ((mk3t y 0) 2, pt2 ((mk3t y 0) 0) ((mk3t y 0) 1)) = H (0, y)
    simp [pt2_eta]
  have hfun1 : (fun y : EuclideanSpace ℝ (Fin 2) => W (mk3t y 1)) = fun y => H (1, y) := by
    funext y
    show H ((mk3t y 1) 2, pt2 ((mk3t y 1) 0) ((mk3t y 1) 1)) = H (1, y)
    simp [pt2_eta]
  have hvec0 : ![(fun y => H (0, y)), A, B] = ![(fun y => W (mk3t y 0)), A, B] := by
    funext k
    rcases fin3_eq_zero_or_one_or_two k with rfl | rfl | rfl <;> simp [hfun0]
  have hvec1 : ![(fun y => H (1, y)), A, B] = ![(fun y => W (mk3t y 1)), A, B] := by
    funext k
    rcases fin3_eq_zero_or_one_or_two k with rfl | rfl | rfl <;> simp [hfun1]
  rw [htop', hbot'] at hmain
  rw [← hvec1, ← hvec0] at hmain
  obtain ⟨hA, hB⟩ := Nat.even_add.mp hmain
  exact Nat.even_add.mpr ⟨hB, hA⟩

end

end Work.Drive
