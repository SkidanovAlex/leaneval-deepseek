import Mathlib
import Submission.Work.ORBassSerre.Action.Structure.BSWalk

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORBassSerre.Action.Structure

open Quiver

universe u v

variable {G : Type*} {V : Type*} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

namespace TreeDatum
namespace PathWord

variable {d : TreeDatum G V}
variable [Fintype (Work.ORBassSerre.orbitV G V)] [Fintype (Work.ORBassSerre.orbitE G V)]

/-!
# Concatenation of path words

Given two path words `W₁`, `W₂` such that the last vertex orbit of `W₁` is the first vertex orbit
of `W₂`, this file constructs a path word `concat W₁ W₂ h` which is the concatenation of the two
walks and whose element of `Γ` is the product of the two elements.  The only subtlety is at the
junction: since a path word has a single letter at each vertex but the concatenation would carry
both the last letter of `W₁` and the first letter of `W₂`, these two letters (which live in the
same vertex group at the junction) are *multiplied*, and the resulting element is used as the
single letter of the concatenation at the junction.

The main theorem is `concat_elt`; `exists_concat` is its packaged form.
-/

/-- Elements of two vertex groups with the same underlying element of `G` and congruent vertex
orbits represent the same element of `Γ`. -/
lemma gEltHom_eq_of_eq {D : d.PresData} {A A' : Work.ORBassSerre.orbitV G V} (h : A = A')
    (x : ↥(d.vgroup A)) (y : ↥(d.vgroup A')) (hxy : (x : G) = (y : G)) :
    d.gEltHom D A x = d.gEltHom D A' y := by
  subst h
  exact congrArg _ (Subtype.ext hxy)

/-! ## The letter at the junction -/

/-- The first letter of `W₂` lies in the vertex group of the last lift of `W₁`. -/
theorem mergeMem (W₁ W₂ : PathWord d) (h : W₁.orb W₁.len = W₂.orb 0) :
    ((W₂.letter 0).2 : G) ∈ d.vgroup (W₁.letter W₁.len).1 := by
  rw [W₁.letter_orbit W₁.len le_rfl, h]
  exact MulAction.mem_stabilizer_iff.mpr (W₂.letter_smul_vert 0 (Nat.zero_le W₂.len))

/-- The letter of the concatenation at the junction: the product of the last letter of `W₁` and
the first letter of `W₂`. -/
noncomputable def mergeLetter (W₁ W₂ : PathWord d) (h : W₁.orb W₁.len = W₂.orb 0) : Letter d :=
  ⟨(W₁.letter W₁.len).1,
    (W₁.letter W₁.len).2 *
      (⟨((W₂.letter 0).2 : G), mergeMem W₁ W₂ h⟩ : ↥(d.vgroup (W₁.letter W₁.len).1))⟩

/-- The `Γ`-element of the junction letter is the product of the two `Γ`-elements. -/
theorem mergeLetter_gam (W₁ W₂ : PathWord d) (h : W₁.orb W₁.len = W₂.orb 0)
    (D : d.PresData) :
    (mergeLetter W₁ W₂ h).gam D = (W₁.letter W₁.len).gam D * (W₂.letter 0).gam D := by
  have hA : (W₁.letter W₁.len).1 = W₁.orb W₁.len := W₁.letter_orbit W₁.len le_rfl
  have hB : (W₂.letter 0).1 = W₂.orb 0 := W₂.letter_orbit 0 (Nat.zero_le W₂.len)
  have hkey := gEltHom_eq_of_eq (d := d) (D := D) (A := (W₁.letter W₁.len).1)
    (A' := (W₂.letter 0).1) (hA.trans (h.trans hB.symm))
    (⟨((W₂.letter 0).2 : G), mergeMem W₁ W₂ h⟩ : ↥(d.vgroup (W₁.letter W₁.len).1))
    (W₂.letter 0).2 rfl
  change (d.gEltHom D (W₁.letter W₁.len).1)
      ((W₁.letter W₁.len).2 *
        (⟨((W₂.letter 0).2 : G), mergeMem W₁ W₂ h⟩ : ↥(d.vgroup (W₁.letter W₁.len).1))) =
    (W₁.letter W₁.len).gam D * (W₂.letter 0).gam D
  rw [map_mul]
  rw [hkey]
  rfl

/-! ## The components of the concatenation -/

/-- The vertex orbit of the concatenated walk at position `k`: from `W₁` up to the junction,
from `W₂` afterwards. -/
noncomputable def cOrb (W₁ W₂ : PathWord d) : ℕ → Work.ORBassSerre.orbitV G V :=
  fun k => if k ≤ W₁.len then W₁.orb k else W₂.orb (k - W₁.len)

/-- The edge orbit of the concatenated walk at position `k`. -/
noncomputable def cStepE (W₁ W₂ : PathWord d) : ℕ → Work.ORBassSerre.orbitE G V :=
  fun k => if k < W₁.len then W₁.stepE k else W₂.stepE (k - W₁.len)

/-- The direction of the concatenated walk at position `k`. -/
noncomputable def cStepB (W₁ W₂ : PathWord d) : ℕ → Bool :=
  fun k => if k < W₁.len then W₁.stepB k else W₂.stepB (k - W₁.len)

/-- The letter of the concatenated walk at position `k`: the letters of `W₁` up to and including
the junction letter (the product of the two junction letters), then the letters of `W₂`. -/
noncomputable def cLetter (W₁ W₂ : PathWord d) (h : W₁.orb W₁.len = W₂.orb 0) : ℕ → Letter d :=
  fun k => if k < W₁.len then W₁.letter k
           else if k = W₁.len then mergeLetter W₁ W₂ h
           else W₂.letter (k - W₁.len)

theorem cOrb_eq_of_le {W₁ W₂ : PathWord d} {k : ℕ} (hk : k ≤ W₁.len) :
    cOrb W₁ W₂ k = W₁.orb k := by simp only [cOrb]; rw [if_pos hk]

theorem cOrb_eq_of_gt {W₁ W₂ : PathWord d} {k : ℕ} (hk : W₁.len < k) :
    cOrb W₁ W₂ k = W₂.orb (k - W₁.len) := by simp only [cOrb]; rw [if_neg (by omega)]

theorem cOrb_eq_of_ge (W₁ W₂ : PathWord d) (h : W₁.orb W₁.len = W₂.orb 0) {k : ℕ}
    (hk : W₁.len ≤ k) : cOrb W₁ W₂ k = W₂.orb (k - W₁.len) := by
  rcases eq_or_lt_of_le hk with hk' | hk'
  · obtain rfl : k = W₁.len := hk'.symm
    rw [cOrb_eq_of_le le_rfl, h, Nat.sub_self]
  · exact cOrb_eq_of_gt hk'

theorem cStepE_eq_of_lt {W₁ W₂ : PathWord d} {k : ℕ} (hk : k < W₁.len) :
    cStepE W₁ W₂ k = W₁.stepE k := by simp only [cStepE]; rw [if_pos hk]

theorem cStepE_eq_of_ge {W₁ W₂ : PathWord d} {k : ℕ} (hk : W₁.len ≤ k) :
    cStepE W₁ W₂ k = W₂.stepE (k - W₁.len) := by simp only [cStepE]; rw [if_neg (by omega)]

theorem cStepB_eq_of_lt {W₁ W₂ : PathWord d} {k : ℕ} (hk : k < W₁.len) :
    cStepB W₁ W₂ k = W₁.stepB k := by simp only [cStepB]; rw [if_pos hk]

theorem cStepB_eq_of_ge {W₁ W₂ : PathWord d} {k : ℕ} (hk : W₁.len ≤ k) :
    cStepB W₁ W₂ k = W₂.stepB (k - W₁.len) := by simp only [cStepB]; rw [if_neg (by omega)]

theorem cLetter_eq_of_lt {W₁ W₂ : PathWord d} {h : W₁.orb W₁.len = W₂.orb 0} {k : ℕ}
    (hk : k < W₁.len) : cLetter W₁ W₂ h k = W₁.letter k := by
  simp only [cLetter]; rw [if_pos hk]

theorem cLetter_eq_of_eq {W₁ W₂ : PathWord d} {h : W₁.orb W₁.len = W₂.orb 0} {k : ℕ}
    (hk : k = W₁.len) : cLetter W₁ W₂ h k = mergeLetter W₁ W₂ h := by
  simp only [cLetter]; rw [if_neg (by omega), if_pos hk]

theorem cLetter_eq_of_gt {W₁ W₂ : PathWord d} {h : W₁.orb W₁.len = W₂.orb 0} {k : ℕ}
    (hk : W₁.len < k) : cLetter W₁ W₂ h k = W₂.letter (k - W₁.len) := by
  simp only [cLetter]; rw [if_neg (by omega), if_neg (by omega)]

/-! ## The concatenation -/

/-- The concatenation of two path words whose junction orbits agree. -/
noncomputable def concat (W₁ W₂ : PathWord d) (h : W₁.orb W₁.len = W₂.orb 0) : PathWord d where
  len := W₁.len + W₂.len
  orb := cOrb W₁ W₂
  letter := cLetter W₁ W₂ h
  letter_orbit := by
    intro k hk
    by_cases hk1 : k < W₁.len
    · rw [cLetter_eq_of_lt hk1, cOrb_eq_of_le (le_of_lt hk1)]
      exact W₁.letter_orbit k (le_of_lt hk1)
    · by_cases hk2 : k = W₁.len
      · rw [cLetter_eq_of_eq hk2, cOrb_eq_of_le (le_of_eq hk2), hk2]
        exact W₁.letter_orbit W₁.len le_rfl
      · rw [cLetter_eq_of_gt (by omega), cOrb_eq_of_gt (by omega)]
        exact W₂.letter_orbit (k - W₁.len) (by omega)
  stepE := cStepE W₁ W₂
  stepB := cStepB W₁ W₂
  step_src := by
    intro k hk
    by_cases hk1 : k < W₁.len
    · rw [cStepE_eq_of_lt hk1, cStepB_eq_of_lt hk1, cOrb_eq_of_le (le_of_lt hk1)]
      exact W₁.step_src k hk1
    · have hge : W₁.len ≤ k := by omega
      rw [cStepE_eq_of_ge hge, cStepB_eq_of_ge hge, cOrb_eq_of_ge W₁ W₂ h hge]
      exact W₂.step_src (k - W₁.len) (by omega)
  step_tgt := by
    intro k hk
    by_cases hk1 : k < W₁.len
    · rw [cStepE_eq_of_lt hk1, cStepB_eq_of_lt hk1, cOrb_eq_of_le (by omega)]
      exact W₁.step_tgt k hk1
    · have hge : W₁.len ≤ k := by omega
      rw [cStepE_eq_of_ge hge, cStepB_eq_of_ge hge, cOrb_eq_of_ge W₁ W₂ h (by omega)]
      have heq : (k - W₁.len) + 1 = (k + 1) - W₁.len := by omega
      rw [← heq]
      exact W₂.step_tgt (k - W₁.len) (by omega)

@[simp] theorem concat_len (W₁ W₂ : PathWord d) (h : W₁.orb W₁.len = W₂.orb 0) :
    (concat W₁ W₂ h).len = W₁.len + W₂.len := rfl

@[simp] theorem concat_orb (W₁ W₂ : PathWord d) (h : W₁.orb W₁.len = W₂.orb 0) (k : ℕ) :
    (concat W₁ W₂ h).orb k = cOrb W₁ W₂ k := rfl

@[simp] theorem concat_letter (W₁ W₂ : PathWord d) (h : W₁.orb W₁.len = W₂.orb 0) (k : ℕ) :
    (concat W₁ W₂ h).letter k = cLetter W₁ W₂ h k := rfl

@[simp] theorem concat_stepE (W₁ W₂ : PathWord d) (h : W₁.orb W₁.len = W₂.orb 0) (k : ℕ) :
    (concat W₁ W₂ h).stepE k = cStepE W₁ W₂ k := rfl

@[simp] theorem concat_stepB (W₁ W₂ : PathWord d) (h : W₁.orb W₁.len = W₂.orb 0) (k : ℕ) :
    (concat W₁ W₂ h).stepB k = cStepB W₁ W₂ k := rfl

theorem concat_orb_zero (W₁ W₂ : PathWord d) (h : W₁.orb W₁.len = W₂.orb 0) :
    (concat W₁ W₂ h).orb 0 = W₁.orb 0 := by
  rw [concat_orb, cOrb_eq_of_le (Nat.zero_le _)]

theorem concat_orb_last (W₁ W₂ : PathWord d) (h : W₁.orb W₁.len = W₂.orb 0) :
    (concat W₁ W₂ h).orb (W₁.len + W₂.len) = W₂.orb W₂.len := by
  rw [concat_orb, cOrb_eq_of_ge W₁ W₂ h (Nat.le_add_right _ _),
    show (W₁.len + W₂.len) - W₁.len = W₂.len from by omega]

/-! ## The element of `Γ` -/

/-- Before the junction, the `Γ`-product of the concatenation agrees with that of `W₁`. -/
theorem concat_tpre_le (W₁ W₂ : PathWord d) (h : W₁.orb W₁.len = W₂.orb 0) (D : d.PresData) :
    ∀ k, k ≤ W₁.len → (concat W₁ W₂ h).tpre D k = W₁.tpre D k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    have hk1 : k < W₁.len := by omega
    rw [tpre_succ (concat W₁ W₂ h) D k, ih (le_of_lt hk1), tpre_succ W₁ D k]
    simp only [concat_letter, concat_stepE, concat_stepB]
    rw [cLetter_eq_of_lt hk1, cStepE_eq_of_lt hk1, cStepB_eq_of_lt hk1]

/-- Just after the junction, the `Γ`-product of the concatenation picks up the last letter of
`W₁` and the first step of `W₂`. -/
theorem concat_tpre_base (W₁ W₂ : PathWord d) (h : W₁.orb W₁.len = W₂.orb 0)
    (D : d.PresData) :
    (concat W₁ W₂ h).tpre D (W₁.len + 1) =
      W₁.tpre D W₁.len * (W₁.letter W₁.len).gam D * W₂.tpre D 1 := by
  rw [tpre_succ (concat W₁ W₂ h) D W₁.len]
  rw [concat_tpre_le W₁ W₂ h D W₁.len le_rfl]
  simp only [concat_letter, concat_stepE, concat_stepB]
  rw [cLetter_eq_of_eq rfl, mergeLetter_gam, cStepE_eq_of_ge le_rfl, cStepB_eq_of_ge le_rfl,
    Nat.sub_self]
  rw [show (1:ℕ) = 0 + 1 from rfl, tpre_succ W₂ D 0, tpre_zero, one_mul]
  group

/-- Past the junction, the `Γ`-product of the concatenation splits into that of `W₁`, the junction
letter, and that of `W₂`. -/
theorem concat_tpre_gt (W₁ W₂ : PathWord d) (h : W₁.orb W₁.len = W₂.orb 0)
    (D : d.PresData) :
    ∀ m, W₁.len < m → (concat W₁ W₂ h).tpre D m =
      W₁.tpre D W₁.len * (W₁.letter W₁.len).gam D * W₂.tpre D (m - W₁.len) := by
  intro m hm
  refine Nat.le_induction (m := W₁.len + 1)
    (P := fun n _ => (concat W₁ W₂ h).tpre D n =
      W₁.tpre D W₁.len * (W₁.letter W₁.len).gam D * W₂.tpre D (n - W₁.len)) ?_ ?_ m ?_
  · rw [Nat.add_sub_cancel_left]
    exact concat_tpre_base W₁ W₂ h D
  · intro n hn ih
    have hn1 : W₁.len < n := by omega
    have hge : W₁.len ≤ n := by omega
    rw [tpre_succ (concat W₁ W₂ h) D n, ih]
    simp only [concat_letter, concat_stepE, concat_stepB]
    rw [cLetter_eq_of_gt hn1, cStepE_eq_of_ge hge, cStepB_eq_of_ge hge]
    have heq : n + 1 - W₁.len = (n - W₁.len) + 1 := by omega
    rw [heq, tpre_succ W₂ D (n - W₁.len)]
    group
  · omega

/-- The `Γ`-element of the concatenation is the product of the `Γ`-elements. -/
theorem concat_elt (W₁ W₂ : PathWord d) (h : W₁.orb W₁.len = W₂.orb 0) (D : d.PresData) :
    (concat W₁ W₂ h).elt D = W₁.elt D * W₂.elt D := by
  rw [show (concat W₁ W₂ h).elt D = (concat W₁ W₂ h).tpre D ((concat W₁ W₂ h).len) *
      ((concat W₁ W₂ h).letter ((concat W₁ W₂ h).len)).gam D from rfl, concat_len]
  rcases Nat.eq_zero_or_pos W₂.len with hlen | hpos
  · have hlen' : W₁.len + W₂.len = W₁.len := by omega
    rw [hlen', concat_tpre_le W₁ W₂ h D W₁.len le_rfl]
    simp only [concat_letter]
    rw [cLetter_eq_of_eq rfl, mergeLetter_gam]
    rw [show W₁.elt D = W₁.tpre D W₁.len * (W₁.letter W₁.len).gam D from rfl,
        show W₂.elt D = W₂.tpre D W₂.len * (W₂.letter W₂.len).gam D from rfl,
        hlen, tpre_zero, one_mul]
    group
  · have hm : W₁.len < W₁.len + W₂.len := by omega
    rw [concat_tpre_gt W₁ W₂ h D (W₁.len + W₂.len) hm]
    simp only [concat_letter]
    rw [cLetter_eq_of_gt hm, show (W₁.len + W₂.len) - W₁.len = W₂.len from by omega]
    rw [show W₁.elt D = W₁.tpre D W₁.len * (W₁.letter W₁.len).gam D from rfl,
        show W₂.elt D = W₂.tpre D W₂.len * (W₂.letter W₂.len).gam D from rfl]
    group

end PathWord
end TreeDatum

theorem exists_concat {G : Type*} {V : Type*}
    [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V] [MulAction G V]
    [Work.ORBassSerre.GraphAction G V]
    {d : Work.ORBassSerre.Action.Structure.TreeDatum G V}
    [Fintype (Work.ORBassSerre.orbitV G V)] [Fintype (Work.ORBassSerre.orbitE G V)]
    (W₁ W₂ : Work.ORBassSerre.Action.Structure.TreeDatum.PathWord d)
    (h : W₁.orb W₁.len = W₂.orb 0) :
    ∃ W : Work.ORBassSerre.Action.Structure.TreeDatum.PathWord d,
      W.len = W₁.len + W₂.len ∧ W.orb 0 = W₁.orb 0 ∧
      W.orb W.len = W₂.orb W₂.len ∧
      (∀ (D : d.PresData), W.elt D = W₁.elt D * W₂.elt D) := by
  exact ⟨TreeDatum.PathWord.concat W₁ W₂ h,
    TreeDatum.PathWord.concat_len W₁ W₂ h,
    TreeDatum.PathWord.concat_orb_zero W₁ W₂ h,
    TreeDatum.PathWord.concat_orb_last W₁ W₂ h,
    fun D => TreeDatum.PathWord.concat_elt W₁ W₂ h D⟩

end Work.ORBassSerre.Action.Structure
