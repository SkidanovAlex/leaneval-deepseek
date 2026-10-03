import Mathlib
import Submission.Work.Peluse.Holds.SwapDefs

/-!
# Vocabulary and counting helpers for the generic-slot count

This module fixes the objects appearing in `Work.Peluse.SwapA.genericCount`:

* `Plug t H` — the plug space `(h,h') ∈ [H]^t × [H]^t`;
* `linForm ω h = ∑_{i : ω i} h_i` — the linear form `ω·h`;
* `qOf ω v = ω·(h − h')` — the slope attached to a plug;
* the elementary counting facts about these (`linForm_update_inj`, `linForm_fiber_card`,
  `card_fin_mod_le`), and the two structural facts about the ladder slots
  (`slotAt_mem`, `slotAt_ne`).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.SwapA

noncomputable section
open Work.Peluse

/-- The plug space of the regime swap: pairs of shift tuples `h, h' ∈ [H]^t`. -/
abbrev Plug (t H : ℕ) := (Fin t → Fin H) × (Fin t → Fin H)

/-- The linear form `ω · h = ∑_{i : ω i} h_i` on shift tuples. -/
def linForm {t H : ℕ} (ω : Fin t → Bool) (h : Fin t → Fin H) : ℤ :=
  ∑ i : Fin t, if ω i then ((h i : ℤ)) else 0

/-- The slope `ω·(h − h')` attached to a plug `v = (h,h')` and a sign pattern `ω`. -/
def qOf {t H : ℕ} (ω : Fin t → Bool) (v : Plug t H) : ℤ :=
  Concat.dotZ ω (Concat.tupSub v.1 v.2)

lemma qOf_eq_sum {t H : ℕ} (ω : Fin t → Bool) (v : Plug t H) :
    qOf ω v = ∑ i : Fin t, (if ω i then ((v.1 i : ℤ) - (v.2 i : ℤ)) else 0) := by
  simp only [qOf, Concat.dotZ, Concat.tupSub]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : ω i <;> simp [h]

lemma qOf_eq_linForm {t H : ℕ} (ω : Fin t → Bool) (v : Plug t H) :
    qOf ω v = linForm ω v.1 - linForm ω v.2 := by
  rw [qOf_eq_sum]
  simp only [linForm]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by by_cases h : ω i <;> simp [h]

lemma qOf_abs_le {t H : ℕ} (ω : Fin t → Bool) (v : Plug t H) :
    |qOf ω v| ≤ (t : ℤ) * (H : ℤ) := by
  have hterm : ∀ i : Fin t, |(if ω i then ((v.1 i : ℤ) - (v.2 i : ℤ)) else 0)| ≤ (H:ℤ) := by
    intro i
    by_cases h : ω i
    · simp only [h, ↓reduceIte]
      have h1 : (v.1 i : ℤ) < H := by
        have := (v.1 i).isLt; exact_mod_cast this
      have h2 : (v.2 i : ℤ) < H := by
        have := (v.2 i).isLt; exact_mod_cast this
      have h3 : 0 ≤ (v.1 i : ℤ) := by simp
      have h4 : 0 ≤ (v.2 i : ℤ) := by simp
      rw [abs_le]; constructor <;> linarith
    · simp [h]
  rw [qOf_eq_sum]
  calc |∑ i : Fin t, (if ω i then ((v.1 i : ℤ) - (v.2 i : ℤ)) else 0)|
      ≤ ∑ i : Fin t, |(if ω i then ((v.1 i : ℤ) - (v.2 i : ℤ)) else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin t, (H:ℤ) := Finset.sum_le_sum fun i _ => hterm i
    _ = (t:ℤ) * (H:ℤ) := by simp [Finset.sum_const]

/-- Changing one coordinate of a tuple that carries a `true` coefficient changes `linForm` by the
change of that coordinate (the remaining coordinates contribute a fixed amount). -/
lemma linForm_update_eq {t H : ℕ} (ω : Fin t → Bool) (g : Fin t → Fin H) (i₀ : Fin t) (x : Fin H)
    (hi₀ : ω i₀ = true) :
    linForm ω (Function.update g i₀ x)
      = (x : ℤ) + ∑ i ∈ Finset.univ.erase i₀, (if ω i then ((g i : ℤ)) else 0) := by
  have h1 : (∑ i ∈ Finset.univ.erase i₀,
      (if ω i then ((Function.update g i₀ x i : ℤ)) else 0))
      = ∑ i ∈ Finset.univ.erase i₀, (if ω i then ((g i : ℤ)) else 0) :=
    Finset.sum_congr rfl fun i hi =>
      by rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  have h2 : (if ω i₀ then ((Function.update g i₀ x i₀ : ℤ)) else 0) = (x : ℤ) := by
    rw [Function.update_self, hi₀, if_pos rfl]
  rw [linForm]
  rw [← Finset.sum_erase_add (Finset.univ : Finset (Fin t))
      (fun i => if ω i then ((Function.update g i₀ x i : ℤ)) else 0) (Finset.mem_univ i₀),
    h1, h2, add_comm]

/-- On a level set of `linForm ω` the values outside any coordinate of `ω` determine the tuple. -/
lemma linForm_update_inj {t H : ℕ} {ω : Fin t → Bool} {i₀ : Fin t} (hi₀ : ω i₀ = true)
    {g : Fin t → Fin H} {x y : Fin H}
    (h : linForm ω (Function.update g i₀ x) = linForm ω (Function.update g i₀ y)) : x = y := by
  rw [linForm_update_eq ω g i₀ x hi₀, linForm_update_eq ω g i₀ y hi₀] at h
  have hz : (x : ℤ) = (y : ℤ) := add_right_cancel h
  exact Fin.ext (by exact_mod_cast hz)

/-- There is always a coordinate of a nonzero sign pattern. -/
lemma exists_true_of_ne_zero {t : ℕ} {ω : Fin t → Bool} (hω : ω ≠ 0) : ∃ i, ω i = true := by
  by_contra h
  push Not at h
  apply hω
  funext i
  have : ω i = false := Bool.eq_false_iff.mpr (h i)
  rw [this]
  exact Bool.zero_eq_false

/-- The number of tuples of `[H]^t` on which `linForm ω` takes a prescribed value is at most
`H ^ (t-1)`. -/
lemma linForm_fiber_card {t H : ℕ} {ω : Fin t → Bool} (hω : ω ≠ 0) (c : ℤ) :
    ((Finset.univ.filter (fun h : Fin t → Fin H => linForm ω h = c)).card : ℝ)
      ≤ (H : ℝ) ^ (t - 1) := by
  classical
  obtain ⟨i₀, hi₀⟩ := exists_true_of_ne_zero hω
  set S : Finset (Fin t → Fin H) :=
    Finset.univ.filter (fun h : Fin t → Fin H => linForm ω h = c) with hS
  have hinj : Set.InjOn (fun h : Fin t → Fin H => fun i : {i // i ≠ i₀} => h i.1) ↑S := by
    intro h hh h' hh' heq
    rw [hS, Finset.mem_coe, Finset.mem_filter] at hh hh'
    have hch : linForm ω h = linForm ω h' := by rw [hh.2, hh'.2]
    have hval : h i₀ = h' i₀ := by
      have e1 := linForm_update_eq ω h i₀ (h i₀) hi₀
      have e2 := linForm_update_eq ω h' i₀ (h' i₀) hi₀
      rw [Function.update_eq_self] at e1 e2
      have heqC : (∑ i ∈ Finset.univ.erase i₀, (if ω i then ((h i : ℤ)) else 0))
                = (∑ i ∈ Finset.univ.erase i₀, (if ω i then ((h' i : ℤ)) else 0)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        have hi' : i ≠ i₀ := (Finset.mem_erase.mp hi).1
        rw [show h i = h' i from by simpa using congrFun heq ⟨i, hi'⟩]
      have hsum : (h i₀ : ℤ) + (∑ i ∈ Finset.univ.erase i₀, (if ω i then ((h i : ℤ)) else 0))
                = (h' i₀ : ℤ) + (∑ i ∈ Finset.univ.erase i₀, (if ω i then ((h' i : ℤ)) else 0)) := by
        rw [← e1, ← e2, hch]
      rw [heqC] at hsum
      have hz : ((h i₀ : ℕ) : ℤ) = ((h' i₀ : ℕ) : ℤ) := add_right_cancel hsum
      exact Fin.ext (by exact_mod_cast hz)
    funext i
    by_cases hi : i = i₀
    · rw [hi, hval]
    · simp only [Function.update_of_ne hi, congrFun heq ⟨i, hi⟩]
  have hmaps : Set.MapsTo (fun h : Fin t → Fin H => fun i : {i // i ≠ i₀} => h i.1)
      ↑S ↑(Finset.univ : Finset ({i : Fin t // i ≠ i₀} → Fin H)) := by
    intro h _
    rw [Finset.coe_univ]
    exact Set.mem_univ _
  have hcard := Finset.card_le_card_of_injOn
    (fun h : Fin t → Fin H => fun i : {i // i ≠ i₀} => h i.1) hmaps hinj
  have hc1 : (Fintype.card {i : Fin t // i ≠ i₀}) = t - 1 := by
    have := Fintype.card_subtype_compl (fun i : Fin t => i = i₀)
    simp only [Fintype.card_fin] at this
    simpa using this
  have hc2 : Fintype.card ({i : Fin t // i ≠ i₀} → Fin H) = H ^ (t - 1) := by
    rw [Fintype.card_fun, Fintype.card_fin, hc1]
  calc (S.card : ℝ) ≤ (Finset.univ.card : ℝ) := by exact_mod_cast hcard
    _ = (Fintype.card ({i : Fin t // i ≠ i₀} → Fin H) : ℝ) := by simp
    _ = (H : ℝ) ^ (t - 1) := by rw [hc2]; push_cast; ring


/-- Cast of the division algorithm to `ℤ`. -/
private lemma _mod_cast_aux {H d : ℕ} (x : Fin H) :
    (((x : ℕ) : ℤ)) = (d : ℤ) * ((x.val / d : ℕ) : ℤ) + ((x.val % d : ℕ) : ℤ) := by
  have := Nat.div_add_mod x.val d
  exact_mod_cast this.symm

/-- The number of `x : Fin H` in a fixed residue class modulo `d` is at most `H / d + 1`. -/
lemma card_fin_mod_le {H d : ℕ} (hd : 1 ≤ d) (k : ℤ) :
    ((Finset.univ.filter (fun x : Fin H => (d : ℤ) ∣ ((x : ℤ) - k))).card : ℝ)
      ≤ (H : ℝ) / (d : ℝ) + 1 := by
  classical
  set S : Finset (Fin H) := Finset.univ.filter (fun x : Fin H => (d : ℤ) ∣ ((x : ℤ) - k)) with hS
  have hinj : Set.InjOn (fun x : Fin H => x.val / d) ↑S := by
    intro x hx y hy hxy
    change x.val / d = y.val / d at hxy
    rw [hS, Finset.mem_coe, Finset.mem_filter] at hx hy
    have hxdiv : (d : ℤ) ∣ ((x : ℤ) - k) := hx.2
    have hydiv : (d : ℤ) ∣ ((y : ℤ) - k) := hy.2
    have hdvd : (d : ℤ) ∣ ((x : ℤ) - (y : ℤ)) := by
      obtain ⟨u, hu⟩ := hxdiv; obtain ⟨v, hv⟩ := hydiv
      exact ⟨u - v, by linear_combination hu - hv⟩
    have hmod : x.val % d = y.val % d := by
      have hcast : (((x : ℕ) : ℤ) - ((y : ℕ) : ℤ))
          = ((x.val % d : ℕ) : ℤ) - ((y.val % d : ℕ) : ℤ) := by
        have h1 : (((x : ℕ) : ℤ)) = (d:ℤ) * ((x.val / d : ℕ) : ℤ) + ((x.val % d : ℕ) : ℤ) :=
          _mod_cast_aux x
        have h2 : (((y : ℕ) : ℤ)) = (d:ℤ) * ((y.val / d : ℕ) : ℤ) + ((y.val % d : ℕ) : ℤ) :=
          _mod_cast_aux y
        rw [h1, h2, hxy]; ring
      have hdvd' : (d:ℤ) ∣ (((x.val % d : ℕ) : ℤ) - ((y.val % d : ℕ) : ℤ)) := by
        rw [hcast] at hdvd; exact hdvd
      have hxlt : x.val % d < d := Nat.mod_lt _ (by omega)
      have hylt : y.val % d < d := Nat.mod_lt _ (by omega)
      have hb1 : ((x.val % d : ℕ) : ℤ) < d := by exact_mod_cast hxlt
      have hb2 : ((y.val % d : ℕ) : ℤ) < d := by exact_mod_cast hylt
      have hb3 : 0 ≤ ((x.val % d : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le _
      have hb4 : 0 ≤ ((y.val % d : ℕ) : ℤ) := by exact_mod_cast Nat.zero_le _
      obtain ⟨w, hw⟩ := hdvd'
      have hdpos : (0:ℤ) < d := by exact_mod_cast hd
      have hw0 : w = 0 := by
        rcases lt_trichotomy w 0 with h | h | h
        · nlinarith [hw]
        · exact h
        · nlinarith [hw]
      have : ((x.val % d : ℕ) : ℤ) = ((y.val % d : ℕ) : ℤ) := by
        rw [hw0, mul_zero] at hw; linarith
      exact_mod_cast this
    exact Fin.ext (by
      have hxval : (x : ℕ) = d * (x.val / d) + x.val % d := (Nat.div_add_mod x.val d).symm
      have hyval : (y : ℕ) = d * (y.val / d) + y.val % d := (Nat.div_add_mod y.val d).symm
      rw [hxval, hyval, hxy, hmod])
  have hmaps : Set.MapsTo (fun x : Fin H => x.val / d) ↑S ↑(Finset.range (H / d + 1)) := by
    intro x _
    rw [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (Nat.le_of_lt x.isLt))
  have hle : S.card ≤ H / d + 1 := by
    have := Finset.card_le_card_of_injOn (fun x : Fin H => x.val / d) hmaps hinj
    simpa using this
  calc (S.card : ℝ) ≤ ((H / d + 1 : ℕ) : ℝ) := by exact_mod_cast hle
    _ = ((H / d : ℕ) : ℝ) + 1 := by push_cast; ring
    _ ≤ (H : ℝ) / d + 1 := by
        have := Nat.cast_div_le (α := ℝ) (m := H) (n := d)
        linarith

/-- Every ladder slot datum is a member of the slot set. -/
lemma slotAt_mem (s : ℕ) (k : Fin (LadderP.Swap.slotCard s)) :
    LadderP.Swap.slotAt s k ∈ LadderP.Swap.slotSet s := by
  unfold LadderP.Swap.slotAt
  exact Subtype.property _

/-- The two sign patterns of a ladder slot differ (at the pivot). -/
lemma slotAt_ne (s : ℕ) (k : Fin (LadderP.Swap.slotCard s)) :
    (LadderP.Swap.slotAt s k).2.1 ≠ (LadderP.Swap.slotAt s k).2.2 := by
  have hmem : LadderP.Swap.slotAt s k ∈ LadderP.Swap.slotSet s := slotAt_mem s k
  rw [LadderP.Swap.slotSet, Finset.mem_filter] at hmem
  obtain ⟨-, -, h2⟩ := hmem
  set p := LadderP.Swap.slotAt s k with hp
  set j : ℕ := p.1.val with hj
  have hjlt : j < s := p.1.isLt
  have hr : s - 1 - j < s := by omega
  set r : Fin s := ⟨s - 1 - j, hr⟩ with hrdef
  have hcond : r.val + p.1.val + 1 = s := by
    simp only [r, hj]; omega
  obtain ⟨hε, hε'⟩ := h2 r hcond
  intro hcontra
  have : p.2.1 r = p.2.2 r := by rw [hcontra]
  rw [hε, hε'] at this
  exact Bool.noConfusion this

end

end Work.Peluse.SwapA
