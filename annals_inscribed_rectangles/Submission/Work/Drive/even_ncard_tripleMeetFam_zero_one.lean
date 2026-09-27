import Mathlib
import Submission.Work.Drive.tripleParity322
import Submission.Work.Drive.classTripleRegular
import Submission.Work.Drive.bdry_label_parity
import Submission.Work.Drive.boxParity

/-!
# Parity of the triple-meet count at the two ends of a family of triples of `2`-chains

`Work.Drive.even_ncard_tripleMeetFam_zero_one` is the box-level form of the `(3,2,2)` bordism
invariance of the triple count: for a smooth one-parameter family `F` of triples of `2`-chains in
`ℝ³` (with the plane parameter squares glued along their *seam* `y ↦ (1 - y 0, 1 - y 1)` as in the
disk presentation of a capped plane), the number of triple meets at the family parameter `s = 0` and
at `s = 1` have the *same parity*.

The proof is the boundary bookkeeping of `Submission.Drive.ParityProp` (`Work.Drive.boxParity`) for
the `(3,2,2)` difference map `Work.Drive.famDiff F : Amb 6 → Tgt 6`:

* the total number of boundary zeros of `famDiff F` in the `7`-box is even;
* the seam faces of the three plane parameter squares cancel pairwise under the seam involution
  (the hypothesis `hseam`), so the number of boundary zeros on the seam faces is even;
* what remains are the boundary zeros on the family-parameter faces `x 0 = 0`, `x 0 = 1`, which are
  in bijection with the triple-meet sets `Work.Drive.tripleMeetFam F 0` and
  `Work.Drive.tripleMeetFam F 1` (the hypothesis `hface` says a boundary zero has exactly one
  boundary coordinate, so no meet of the family faces lies on a seam face).

Hence the two triple-meet counts have the same parity.
-/

set_option autoImplicit false

namespace Work.Drive

open Submission.Drive
open scoped ContDiff Topology

noncomputable section

/-! The `(3,2,2)` triple-parameter box: the coordinate dictionary, the face labelling and the seam
involution used for the parity of the triple-meet counts. -/
namespace ETM

/-! ## The coordinate dictionary between `Amb 6` and `ℝ × (ℝ²)³` -/

/-- The plane parameter and the coordinate of a `Fin 6` index: `b = 2 * k + i`. -/
def unpair (b : Fin 6) : Fin 3 × Fin 2 :=
  (⟨b.val / 2, by have := b.isLt; omega⟩, ⟨b.val % 2, by have := b.isLt; omega⟩)

lemma unpair_pair (k : Fin 3) (i : Fin 2) :
    unpair ⟨2 * k.val + i.val, by have := k.isLt; have := i.isLt; omega⟩ = (k, i) := by
  refine Prod.ext ?_ ?_
  · ext; simp [unpair]; omega
  · ext; simp [unpair]; omega

/-- Every coordinate of `Fin 6` is a plane parameter coordinate. -/
lemma famC_unpair (b : Fin 6) : famC (unpair b).1 (unpair b).2 = b.succ := by
  ext
  simp only [famC_val, Fin.val_succ, unpair]
  omega

/-- The coordinate `famC k i` is the successor of `⟨2 * k + i⟩`. -/
lemma famC_eq_succ (k : Fin 3) (i : Fin 2) :
    famC k i = (⟨2 * k.val + i.val, by have := k.isLt; have := i.isLt; omega⟩ : Fin 6).succ := by
  ext
  simp only [famC_val, Fin.val_succ]
  omega

/-- Every coordinate of `Fin 7` other than `famS` is a plane parameter coordinate. -/
lemma famC_cases {j : Fin 7} (hj : j ≠ famS) : ∃ (k : Fin 3) (i : Fin 2), famC k i = j := by
  fin_cases j
  · exact absurd rfl hj
  · exact ⟨0, 0, by decide⟩
  · exact ⟨0, 1, by decide⟩
  · exact ⟨1, 0, by decide⟩
  · exact ⟨1, 1, by decide⟩
  · exact ⟨2, 0, by decide⟩
  · exact ⟨2, 1, by decide⟩

/-- **The coordinate level dictionary backwards**: the point of the `7`-box with family parameter
`s` and plane parameters `y 0, y 1, y 2`. -/
def mkAmb (s : ℝ) (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) : Amb 6 :=
  WithLp.toLp 2 (Fin.cons s fun b : Fin 6 => y (unpair b).1 (unpair b).2)

lemma ofLp_mkAmb (s : ℝ) (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) :
    WithLp.ofLp (mkAmb s y) = Fin.cons s (fun b : Fin 6 => y (unpair b).1 (unpair b).2) := rfl

@[simp] lemma mkAmb_apply_famS (s : ℝ) (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) :
    mkAmb s y famS = s := by
  show WithLp.ofLp (mkAmb s y) famS = s
  rw [ofLp_mkAmb]
  exact Fin.cons_zero _ _

@[simp] lemma mkAmb_apply_famC (s : ℝ) (y : Fin 3 → EuclideanSpace ℝ (Fin 2))
    (k : Fin 3) (i : Fin 2) : mkAmb s y (famC k i) = y k i := by
  show WithLp.ofLp (mkAmb s y) (famC k i) = y k i
  rw [ofLp_mkAmb, famC_eq_succ, Fin.cons_succ, unpair_pair]

@[simp] lemma famT_mkAmb (s : ℝ) (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) :
    famT (mkAmb s y) = s := mkAmb_apply_famS s y

@[simp] lemma famY_mkAmb (s : ℝ) (y : Fin 3 → EuclideanSpace ℝ (Fin 2)) (k : Fin 3) :
    famY (mkAmb s y) k = y k := by
  ext i
  rw [famY_apply, mkAmb_apply_famC]

/-- **The coordinate dictionary in the other direction**: every point of the `7`-box is recovered
from its family parameter and its three plane parameters. -/
lemma mkAmb_fam (x : Amb 6) : mkAmb (famT x) (fun k => famY x k) = x := by
  ext j
  by_cases hj : j = famS
  · subst hj
    show famT x = x famS
    rfl
  · obtain ⟨k, i, rfl⟩ := famC_cases hj
    rw [mkAmb_apply_famC, famY_apply]

/-- **The plane parameters do not determine the point** (the family coordinate is free), but together
with the family coordinate they do: on a level set of `famT`, the plane parameters are injective. -/
lemma famY_injOn_famT {x x' : Amb 6} (h : (fun k => famY x k) = fun k => famY x' k)
    (ht : famT x = famT x') : x = x' := by
  rw [← mkAmb_fam x, ← mkAmb_fam x', h, ht]

lemma mkAmb_injective (s : ℝ) : Function.Injective (mkAmb s · :
    (Fin 3 → EuclideanSpace ℝ (Fin 2)) → Amb 6) := by
  intro y y' h
  have h' := congrArg (fun x : Amb 6 => fun k => famY x k) h
  simpa using h'

@[simp] lemma mem_unitBox_mkAmb {s : ℝ} {y : Fin 3 → EuclideanSpace ℝ (Fin 2)} :
    mkAmb s y ∈ unitBox 6 ↔ s ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ k, y k ∈ unitBox 1 := by
  constructor
  · intro h
    refine ⟨by simpa [unitBox] using h famS, fun k i => by simpa [unitBox] using h (famC k i)⟩
  · rintro ⟨hs, hy⟩ j
    by_cases hj : j = famS
    · subst hj; simpa [unitBox] using hs
    · obtain ⟨k, i, rfl⟩ := famC_cases hj
      simpa [unitBox] using hy k i

/-- The plane parameters of a point of the box lie in the box. -/
lemma famY_mem_unitBox {x : Amb 6} (hx : x ∈ unitBox 6) (k : Fin 3) :
    famY x k ∈ unitBox 1 := fun i => by rw [famY_apply]; exact hx (famC k i)

/-! ## Smoothness of the difference map -/

/-- The stacking `pair33` of two smooth maps is smooth. -/
lemma contDiff_pair33 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {u v : E → EuclideanSpace ℝ (Fin 3)}
    (hu : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) u)
    (hv : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) v) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x => pair33 (u x) (v x)) := by
  rw [contDiff_piLp]
  intro i
  by_cases hi : i.val < 3
  · have h : (fun x => pair33 (u x) (v x) i) = fun x => u x ⟨i.val, hi⟩ := by
      funext x; exact pair33_apply_lt (u x) (v x) hi
    rw [h]
    exact (by fun_prop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun f : EuclideanSpace ℝ (Fin 3) => f ⟨i.val, hi⟩)).comp hu
  · have h : (fun x => pair33 (u x) (v x) i) = fun x => v x ⟨i.val - 3, by omega⟩ := by
      funext x; exact pair33_apply_ge (u x) (v x) hi
    rw [h]
    exact (by fun_prop : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun f : EuclideanSpace ℝ (Fin 3) => f ⟨i.val - 3, by omega⟩)).comp hv

/-- **Smoothness of the `(3,2,2)` difference map.** -/
theorem contDiff_famDiff
    (F : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hF : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => F k p)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (famDiff F) := by
  have hg : ∀ k : Fin 3, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Amb 6 => (famT x, famY x k)) := by
    intro k
    refine ContDiff.prodMk ?_ ?_
    · show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Amb 6 => x famS)
      fun_prop
    · show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : Amb 6 => WithLp.toLp 2 (fun i : Fin 2 => x (famC k i)))
      fun_prop
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Amb 6 => F 0 (famT x, famY x 0)) :=
    (hF 0).comp (hg 0)
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Amb 6 => F 1 (famT x, famY x 1)) :=
    (hF 1).comp (hg 1)
  have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Amb 6 => F 2 (famT x, famY x 2)) :=
    (hF 2).comp (hg 2)
  show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Amb 6 =>
    pair33 (F 0 (famT x, famY x 0) - F 1 (famT x, famY x 1))
      (F 0 (famT x, famY x 0) - F 2 (famT x, famY x 2)))
  exact contDiff_pair33 (h1.sub h2) (h1.sub h3)

/-! ## The family-parameter faces of the `7`-box -/

/-- The labelling of the `7`-box faces: the family parameter faces get `0`, the seam faces `1`. -/
def label322 : Fin 7 → Fin 2 := fun i => if i = famS then 0 else 1

lemma label322_eq_zero {i : Fin 7} : label322 i = 0 ↔ i = famS := by
  unfold label322
  by_cases h : i = famS <;> simp [h]

lemma label322_eq_one {i : Fin 7} : label322 i = 1 ↔ i ≠ famS := by
  unfold label322
  by_cases h : i = famS <;> simp [h]

/-- The boundary zeros of the difference map on the family-parameter face `x 0 = s`. -/
def endFace (F : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (s : ℝ) : Set (Amb 6) := {x | x ∈ bdyZeros (famDiff F) ∧ x famS = s}

@[simp] lemma mem_endFace {F : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    {s : ℝ} {x : Amb 6} : x ∈ endFace F s ↔ x ∈ bdyZeros (famDiff F) ∧ x famS = s := Iff.rfl

/-- The family-parameter faces are cut out by the labelling `label322` and the value `0`. -/
lemma labelMeet_zero_eq (F : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) :
    labelMeet (famDiff F) label322 0 = endFace F 0 ∪ endFace F 1 := by
  ext x
  simp only [labelMeet, endFace, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_union]
  constructor
  · rintro ⟨hx, i, hi, hxi⟩
    have hi' : i = famS := label322_eq_zero.mp hi
    subst hi'
    rcases hxi with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  · rintro (⟨hx, h⟩ | ⟨hx, h⟩)
    · exact ⟨hx, famS, label322_eq_zero.mpr rfl, Or.inl h⟩
    · exact ⟨hx, famS, label322_eq_zero.mpr rfl, Or.inr h⟩

lemma disjoint_endFace (F : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) :
    Disjoint (endFace F 0) (endFace F 1) := by
  rw [Set.disjoint_left]
  rintro x ⟨-, h0⟩ ⟨-, h1⟩
  rw [h0] at h1
  norm_num at h1

/-- **The family-parameter face at `s = 0` is the triple-meet set at `s = 0`.** -/
lemma ncard_endFace_zero (F : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) :
    (endFace F 0).ncard = (tripleMeetFam F 0).ncard := by
  refine Set.ncard_congr (fun x _ => fun k => famY x k) ?_ ?_ ?_
  · intro x hx
    rw [mem_endFace, mem_bdyZeros] at hx
    obtain ⟨⟨hxb, hxd⟩, hxs⟩ := hx
    rw [mem_tripleMeetFam]
    have hd := (famDiff_eq_zero_iff F x).mp hxd
    simp only [famT] at hd
    rw [hxs] at hd
    refine ⟨fun k => famY_mem_unitBox hxb.1 k, fun k => ?_⟩
    fin_cases k
    · rfl
    · exact hd.1.symm
    · exact hd.2.symm
  · intro x x' hx hx' h
    rw [mem_endFace] at hx hx'
    obtain ⟨⟨-, -⟩, hxs⟩ := hx
    obtain ⟨⟨-, -⟩, hxs'⟩ := hx'
    refine famY_injOn_famT h ?_
    simp only [famT]
    rw [hxs, hxs']
  · intro y hy
    refine ⟨mkAmb 0 y, ?_, ?_⟩
    · rw [mem_endFace, mem_bdyZeros]
      refine ⟨⟨?_, ?_⟩, mkAmb_apply_famS 0 y⟩
      · rw [unitBoxBdry, Set.mem_ofPred_eq]
        exact ⟨(mem_unitBox_mkAmb).mpr ⟨by norm_num, hy.1⟩, famS, Or.inl (mkAmb_apply_famS 0 y)⟩
      · rw [famDiff_eq_zero_iff]
        refine ⟨?_, ?_⟩
        · simpa using (hy.2 1).symm
        · simpa using (hy.2 2).symm
    · funext k
      exact famY_mkAmb 0 y k

/-- **The family-parameter face at `s = 1` is the triple-meet set at `s = 1`.** -/
lemma ncard_endFace_one (F : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) :
    (endFace F 1).ncard = (tripleMeetFam F 1).ncard := by
  refine Set.ncard_congr (fun x _ => fun k => famY x k) ?_ ?_ ?_
  · intro x hx
    rw [mem_endFace, mem_bdyZeros] at hx
    obtain ⟨⟨hxb, hxd⟩, hxs⟩ := hx
    rw [mem_tripleMeetFam]
    have hd := (famDiff_eq_zero_iff F x).mp hxd
    simp only [famT] at hd
    rw [hxs] at hd
    refine ⟨fun k => famY_mem_unitBox hxb.1 k, fun k => ?_⟩
    fin_cases k
    · rfl
    · exact hd.1.symm
    · exact hd.2.symm
  · intro x x' hx hx' h
    rw [mem_endFace] at hx hx'
    obtain ⟨⟨-, -⟩, hxs⟩ := hx
    obtain ⟨⟨-, -⟩, hxs'⟩ := hx'
    refine famY_injOn_famT h ?_
    simp only [famT]
    rw [hxs, hxs']
  · intro y hy
    refine ⟨mkAmb 1 y, ?_, ?_⟩
    · rw [mem_endFace, mem_bdyZeros]
      refine ⟨⟨?_, ?_⟩, mkAmb_apply_famS 1 y⟩
      · rw [unitBoxBdry, Set.mem_ofPred_eq]
        exact ⟨(mem_unitBox_mkAmb).mpr ⟨by norm_num, hy.1⟩, famS, Or.inr (mkAmb_apply_famS 1 y)⟩
      · rw [famDiff_eq_zero_iff]
        refine ⟨?_, ?_⟩
        · simpa using (hy.2 1).symm
        · simpa using (hy.2 2).symm
    · funext k
      exact famY_mkAmb 1 y k

/-! ## The seam involution of the plane parameter squares -/

lemma seamInv2_apply (y : EuclideanSpace ℝ (Fin 2)) (i : Fin 2) : seamInv2 y i = 1 - y i := by
  fin_cases i <;> simp [seamInv2]

lemma seamInv2_involutive (y : EuclideanSpace ℝ (Fin 2)) : seamInv2 (seamInv2 y) = y := by
  ext i
  rw [seamInv2_apply, seamInv2_apply]
  ring

lemma one_sub_mem_Icc_iff (c : ℝ) : 1 - c ∈ Set.Icc (0 : ℝ) 1 ↔ c ∈ Set.Icc (0 : ℝ) 1 := by
  constructor <;> intro h <;> exact ⟨by linarith [h.1, h.2], by linarith [h.1, h.2]⟩

lemma seamInv2_mem_unitBox {y : EuclideanSpace ℝ (Fin 2)} :
    seamInv2 y ∈ unitBox 1 ↔ y ∈ unitBox 1 := by
  simp only [unitBox, Set.mem_ofPred_eq]
  constructor
  · intro h i
    fin_cases i
    · exact (one_sub_mem_Icc_iff (y 0)).mp (by simpa [seamInv2_apply] using h 0)
    · exact (one_sub_mem_Icc_iff (y 1)).mp (by simpa [seamInv2_apply] using h 1)
  · intro h i
    fin_cases i
    · rw [seamInv2_apply]
      exact (one_sub_mem_Icc_iff (y 0)).mpr (h 0)
    · rw [seamInv2_apply]
      exact (one_sub_mem_Icc_iff (y 1)).mpr (h 1)

/-- The block of a bad coordinate of a point of the box, chosen canonically. -/
def badBlock (x : Amb 6) : Fin 3 :=
  if h : ∃ k : Fin 3, ∃ i : Fin 2, (x (famC k i) = 0 ∨ x (famC k i) = 1) then h.choose else 0

lemma badBlock_spec (x : Amb 6)
    (h : ∃ k : Fin 3, ∃ i : Fin 2, (x (famC k i) = 0 ∨ x (famC k i) = 1)) :
    ∃ i : Fin 2, (x (famC (badBlock x) i) = 0 ∨ x (famC (badBlock x) i) = 1) := by
  rw [badBlock, dif_pos h]
  exact h.choose_spec

/-- **Complementing the coordinates of one plane block**: the square involution `seamInv2` applied to
the `k`-th plane parameter of `x`. -/
def seamBlockInv (k : Fin 3) (x : Amb 6) : Amb 6 :=
  mkAmb (famT x) (Function.update (fun k' => famY x k') k (seamInv2 (famY x k)))

@[simp] lemma seamBlockInv_famT (k : Fin 3) (x : Amb 6) : famT (seamBlockInv k x) = famT x :=
  famT_mkAmb _ _

lemma seamBlockInv_famY (k k' : Fin 3) (x : Amb 6) :
    famY (seamBlockInv k x) k' = if k' = k then seamInv2 (famY x k) else famY x k' := by
  rw [seamBlockInv, famY_mkAmb, Function.update_apply]

lemma seamBlockInv_mem_unitBox {x : Amb 6} (hx : x ∈ unitBox 6) (k : Fin 3) :
    seamBlockInv k x ∈ unitBox 6 := by
  rw [seamBlockInv, mem_unitBox_mkAmb]
  refine ⟨by simpa [famT] using hx famS, fun k' => ?_⟩
  by_cases h : k' = k
  · subst h
    rw [Function.update_self]
    exact seamInv2_mem_unitBox.mpr (famY_mem_unitBox hx k')
  · rw [Function.update_of_ne h]
    exact famY_mem_unitBox hx k'

/-- The coordinate form of `seamBlockInv`: the `k`-th block is complemented, the rest is unchanged. -/
lemma seamBlockInv_apply_famC (k : Fin 3) (x : Amb 6) (k' : Fin 3) (i' : Fin 2) :
    seamBlockInv k x (famC k' i') =
      if k' = k then 1 - x (famC k' i') else x (famC k' i') := by
  rw [← famY_apply (seamBlockInv k x) k' i', seamBlockInv_famY]
  by_cases h : k' = k
  · subst h
    rw [if_pos rfl, if_pos rfl, seamInv2_apply, famY_apply]
  · rw [if_neg h, if_neg h, famY_apply]

/-- **The seam part**: the boundary zeros of the difference map on the seam faces of the plane
parameter squares. -/
def seamPart (F : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)) :
    Set (Amb 6) := labelMeet (famDiff F) label322 1

lemma mem_seamPart_iff {F : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    {x : Amb 6} :
    x ∈ seamPart F ↔ x ∈ bdyZeros (famDiff F) ∧
      ∃ k : Fin 3, ∃ i : Fin 2, (x (famC k i) = 0 ∨ x (famC k i) = 1) := by
  rw [seamPart, labelMeet]
  constructor
  · rintro ⟨hx, j, hj, hxj⟩
    obtain ⟨k, i, rfl⟩ := famC_cases (label322_eq_one.mp hj)
    exact ⟨hx, k, i, hxj⟩
  · rintro ⟨hx, k, i, hki⟩
    exact ⟨hx, famC k i, label322_eq_one.mpr (fun h => famC_ne_famS k i h), hki⟩

lemma exists_bad_of_mem_seamPart {F : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    {x : Amb 6} (hx : x ∈ seamPart F) :
    ∃ k : Fin 3, ∃ i : Fin 2, (x (famC k i) = 0 ∨ x (famC k i) = 1) :=
  (mem_seamPart_iff.mp hx).2

/-- The value of the difference map only depends on the family parameter and on the three values
`F k (famT x, famY x k)`. -/
lemma famDiff_congr_blocks
    {F : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)} {x x' : Amb 6}
    (ht : famT x' = famT x)
    (h : ∀ k, F k (famT x, famY x' k) = F k (famT x, famY x k)) :
    famDiff F x' = famDiff F x := by
  simp only [famDiff]
  rw [ht, h 0, h 1, h 2]

/-- **The seam involution preserves the zero set of the difference map.** -/
lemma famDiff_seamBlockInv
    {F : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    (hseam : ∀ (k : Fin 3) (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y →
      F k (s, y) = F k (s, seamInv2 y))
    (x : Amb 6) (k : Fin 3) (hz : onSeam2 (famY x k)) :
    famDiff F (seamBlockInv k x) = famDiff F x := by
  refine famDiff_congr_blocks (by rw [seamBlockInv_famT]) (fun k' => ?_)
  rw [seamBlockInv_famY]
  by_cases h : k' = k
  · subst h
    rw [if_pos rfl]
    exact (hseam k' (famT x) (famY x k') hz).symm
  · rw [if_neg h]

/-- **The seam involution** on the `7`-box: complement the coordinates of the block carrying the
(unique) seam coordinate of a boundary zero. -/
abbrev seamT (x : Amb 6) : Amb 6 := seamBlockInv (badBlock x) x

lemma onSeam2_of_exists_bad {y : EuclideanSpace ℝ (Fin 2)}
    (h : ∃ i : Fin 2, (y i = 0 ∨ y i = 1)) : onSeam2 y := by
  obtain ⟨i, hi⟩ := h
  fin_cases i
  · rcases hi with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · rcases hi with h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

/-- **The seam involution maps the seam part into itself.** -/
lemma seamT_mem
    {F : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    (hseam : ∀ (k : Fin 3) (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y →
      F k (s, y) = F k (s, seamInv2 y))
    {x : Amb 6} (hx : x ∈ seamPart F) : seamT x ∈ seamPart F := by
  obtain ⟨hbz, hex⟩ := mem_seamPart_iff.mp hx
  rw [mem_bdyZeros] at hbz
  obtain ⟨i0, hi0⟩ := badBlock_spec x hex
  have hz : onSeam2 (famY x (badBlock x)) :=
    onSeam2_of_exists_bad ⟨i0, by rw [famY_apply]; exact hi0⟩
  rw [mem_seamPart_iff]
  refine ⟨⟨?_, ?_⟩, badBlock x, i0, ?_⟩
  · rw [unitBoxBdry, Set.mem_ofPred_eq]
    refine ⟨seamBlockInv_mem_unitBox hbz.1.1 (badBlock x), famC (badBlock x) i0, ?_⟩
    rw [seamT, seamBlockInv_apply_famC, if_pos rfl]
    rcases hi0 with h | h <;> simp [h]
  · rw [seamT, famDiff_seamBlockInv hseam x (badBlock x) hz, hbz.2]
  · rw [seamT, seamBlockInv_apply_famC, if_pos rfl]
    rcases hi0 with h | h <;> simp [h]

/-- **The seam involution is an involution on the seam part.** -/
lemma seamT_invol
    {F : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    (hseam : ∀ (k : Fin 3) (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y →
      F k (s, y) = F k (s, seamInv2 y))
    (hface : ∀ x ∈ unitBoxBdry 6, famDiff F x = 0 → ∃ i : Fin 7,
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1))
    {x : Amb 6} (hx : x ∈ seamPart F) : seamT (seamT x) = x := by
  obtain ⟨hbz, hex⟩ := mem_seamPart_iff.mp hx
  rw [mem_bdyZeros] at hbz
  obtain ⟨i0, hi0⟩ := badBlock_spec x hex
  -- `x` has exactly one seam coordinate, and it lies in the block `badBlock x`
  obtain ⟨j₀, hj₀, hother⟩ := hface x hbz.1 hbz.2
  have hbad : ∀ {j : Fin 7}, (x j = 0 ∨ x j = 1) → j = famC (badBlock x) i0 := by
    intro j hj
    rw [eq_of_mem_Ioo_of_eq_zero_or_one' hother hj,
      eq_of_mem_Ioo_of_eq_zero_or_one' hother hi0]
  -- the bad block of `seamT x` is the bad block of `x`
  have hk : badBlock (seamT x) = badBlock x := by
    obtain ⟨i'', hi''⟩ :=
      badBlock_spec (seamT x) (exists_bad_of_mem_seamPart (seamT_mem hseam hx))
    by_cases h : badBlock (seamT x) = badBlock x
    · exact h
    · exfalso
      have hxbad : x (famC (badBlock (seamT x)) i'') = 0 ∨
          x (famC (badBlock (seamT x)) i'') = 1 := by
        have h' := hi''
        rw [seamT, seamBlockInv_apply_famC, if_neg h] at h'
        exact h'
      exact h (famC_injective (hbad hxbad)).1
  refine famY_injOn_famT ?_ ?_
  · funext k'
    show famY (seamBlockInv (badBlock (seamT x)) (seamT x)) k' = famY x k'
    rw [hk, seamBlockInv_famY]
    by_cases h : k' = badBlock x
    · subst h
      rw [if_pos rfl, seamBlockInv_famY, if_pos rfl, seamInv2_involutive]
    · rw [if_neg h, seamBlockInv_famY, if_neg h]
  · show famT (seamBlockInv (badBlock (seamT x)) (seamT x)) = famT x
    rw [hk, seamBlockInv_famT, seamBlockInv_famT]

/-- **The seam involution has no fixed point on the seam part.** -/
lemma seamT_ne
    {F : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    {x : Amb 6} (hx : x ∈ seamPart F) : seamT x ≠ x := by
  obtain ⟨hbz, hex⟩ := mem_seamPart_iff.mp hx
  obtain ⟨i0, hi0⟩ := badBlock_spec x hex
  intro hEq
  have hcoord := congrArg (fun z : Amb 6 => z (famC (badBlock x) i0)) hEq
  rw [seamT, seamBlockInv_apply_famC, if_pos rfl] at hcoord
  rcases hi0 with h | h <;> rw [h] at hcoord <;> norm_num at hcoord

/-- **The seam part has an even number of elements.** -/
lemma even_ncard_seamPart
    {F : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3)}
    (hseam : ∀ (k : Fin 3) (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)), onSeam2 y →
      F k (s, y) = F k (s, seamInv2 y))
    (hface : ∀ x ∈ unitBoxBdry 6, famDiff F x = 0 → ∃ i : Fin 7,
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1))
    (hfin : (seamPart F).Finite) :
    Even (seamPart F).ncard :=
  even_ncard_of_involution hfin seamT
    (fun _ hx => seamT_mem hseam hx)
    (fun _ hx => seamT_invol hseam hface hx)
    (fun _ hx => seamT_ne hx)

end ETM

open ETM

/-! ## The parity of the two end counts -/

theorem even_ncard_tripleMeetFam_zero_one
    (F : Fin 3 → ℝ × EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 3))
    (hF : ∀ k, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => F k p))
    (hseam : ∀ (k : Fin 3) (s : ℝ) (y : EuclideanSpace ℝ (Fin 2)),
      Work.Drive.onSeam2 y → F k (s, y) = F k (s, Work.Drive.seamInv2 y))
    (hreg : ∀ x ∈ Submission.Drive.unitBox 6, Work.Drive.famDiff F x = 0 →
      Function.Surjective (fderiv ℝ (Work.Drive.famDiff F) x))
    (hface : ∀ x ∈ Submission.Drive.unitBoxBdry 6, Work.Drive.famDiff F x = 0 →
      ∃ i : Fin 7, (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) ∧
        Function.Surjective (fun v : {v : Work.Drive.Amb 6 // v i = 0} =>
          fderiv ℝ (Work.Drive.famDiff F) x v.1)) :
    Even ((Work.Drive.tripleMeetFam F 0).ncard + (Work.Drive.tripleMeetFam F 1).ncard) := by
  have hFd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (famDiff F) := contDiff_famDiff F hF
  have hface' : ∀ x ∈ unitBoxBdry 6, famDiff F x = 0 → ∃ i : Fin 7,
      (x i = 0 ∨ x i = 1) ∧ (∀ j, j ≠ i → x j ∈ Set.Ioo (0 : ℝ) 1) :=
    fun x hx h0 => (hface x hx h0).imp fun _ h => ⟨h.1, h.2.1⟩
  -- the boundary count of `famDiff F` is even, and the seam part is even
  have hsum := even_sum_ncard_labelMeet (famDiff F) hFd hreg hface label322
  have hsplit : (∑ s : Fin 2, (labelMeet (famDiff F) label322 s).ncard)
      = (endFace F 0 ∪ endFace F 1).ncard + (seamPart F).ncard := by
    rw [Fin.sum_univ_two, labelMeet_zero_eq, seamPart]
  have hfin : (bdyZeros (famDiff F)).Finite := (boxParity 6 (famDiff F) hFd hreg hface).1
  have hfinS : (seamPart F).Finite := hfin.subset fun _ hx => (mem_seamPart_iff.mp hx).1
  have hseamEven : Even (seamPart F).ncard := even_ncard_seamPart hseam hface' hfinS
  have hendEven : Even ((endFace F 0 ∪ endFace F 1).ncard) :=
    (Nat.even_add.mp (hsplit ▸ hsum)).mpr hseamEven
  -- the family faces carry exactly the two triple-meet counts
  have hunion : (endFace F 0 ∪ endFace F 1).ncard
      = (endFace F 0).ncard + (endFace F 1).ncard :=
    Set.ncard_union_eq (disjoint_endFace F)
      (hfin.subset fun _ hx => hx.1) (hfin.subset fun _ hx => hx.1)
  rw [← ncard_endFace_zero F, ← ncard_endFace_one F, ← hunion]
  exact hendEven

end

end Work.Drive
