import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Rat.Star
import Mathlib.Data.ZMod.Basic

namespace Commons.NumberTheory.Sieve

open Finset

/-- Counting a single residue class modulo `D` in an integer interval `[a, b)`:
the number of `u ∈ [a,b)` with `u ≡ c (mod D)` lies within `1` of `(b-a)/D`. -/
theorem card_Ico_zmod_close (D : ℕ) [NeZero D] (a b : ℤ) (c : ZMod D)
    (hm : 0 ≤ b - a) :
    ((((Finset.Ico a b).filter (fun u : ℤ => (u : ZMod D) = c)).card : ℝ)
        ≤ ((b - a : ℤ) : ℝ) / (D : ℝ) + 1) ∧
    (((b - a : ℤ) : ℝ) / (D : ℝ) - 1
        ≤ (((Finset.Ico a b).filter (fun u : ℤ => (u : ZMod D) = c)).card : ℝ)) := by
  have hDZpos : (0:ℤ) < (D:ℤ) := by
    have h : 0 < D := Nat.pos_of_neZero D
    exact_mod_cast h
  have hDqpos : (0:ℚ) < (D:ℚ) := by exact_mod_cast Nat.pos_of_neZero D
  set v : ℤ := (c.val : ℤ) with hv
  have hvc : (v : ZMod D) = c := by
    rw [hv]; push_cast; exact ZMod.natCast_zmod_val c
  have hiff : ∀ u : ℤ, (u : ZMod D) = c ↔ u ≡ v [ZMOD (D:ℤ)] := by
    intro u
    rw [← hvc]
    exact ZMod.intCast_eq_intCast_iff u v D
  set k : ℕ := ((Finset.Ico a b).filter (fun u : ℤ => (u : ZMod D) = c)).card with hk_def
  have hk_alt : k = ((Finset.Ico a b).filter (fun u : ℤ => u ≡ v [ZMOD (D:ℤ)])).card := by
    rw [hk_def]
    congr 1
    apply Finset.filter_congr
    intro u _
    exact hiff u
  have hcard := Int.Ico_filter_modEq_card a b hDZpos v
  simp only [Int.cast_natCast] at hcard
  rw [← hk_alt] at hcard
  set xq : ℚ := ((b:ℚ) - (v:ℚ)) / (D:ℚ) with hxq
  set yq : ℚ := ((a:ℚ) - (v:ℚ)) / (D:ℚ) with hyq
  set A : ℤ := ⌈xq⌉ - ⌈yq⌉ with hA
  have hcardA : (k:ℤ) = max A 0 := hcard
  have hAcast : ((A:ℤ) : ℚ) = (⌈xq⌉:ℚ) - (⌈yq⌉:ℚ) := by rw [hA]; exact Int.cast_sub _ _
  have hn : ((b:ℚ) - (v:ℚ)) - ((a:ℚ) - (v:ℚ)) = ((b - a : ℤ) : ℚ) := by
    push_cast; ring
  have hxqyq : xq - (yq + 1) = ((b - a : ℤ):ℚ)/(D:ℚ) - 1 := by
    rw [hxq, hyq]
    have h : ((b:ℚ) - (v:ℚ)) / (D:ℚ) - (((a:ℚ) - (v:ℚ)) / (D:ℚ) + 1)
        = ((b:ℚ) - (v:ℚ)) / (D:ℚ) - ((a:ℚ) - (v:ℚ)) / (D:ℚ) - 1 := by ring
    rw [h, div_sub_div_same, hn]
  have hxqyq2 : (xq + 1) - yq = ((b - a : ℤ):ℚ)/(D:ℚ) + 1 := by
    rw [hxq, hyq]
    have h : ((b:ℚ) - (v:ℚ)) / (D:ℚ) + 1 - ((a:ℚ) - (v:ℚ)) / (D:ℚ)
        = ((b:ℚ) - (v:ℚ)) / (D:ℚ) - ((a:ℚ) - (v:ℚ)) / (D:ℚ) + 1 := by ring
    rw [h, div_sub_div_same, hn]
  have hAlow : xq - (yq + 1) < (A:ℚ) := by
    rw [hAcast]
    exact lt_of_le_of_lt (sub_le_sub_right (Int.le_ceil xq) (yq+1))
      (sub_lt_sub_left (Int.ceil_lt_add_one yq) (⌈xq⌉:ℚ))
  have hAhigh : (A:ℚ) < (xq + 1) - yq := by
    rw [hAcast]
    exact lt_of_lt_of_le (sub_lt_sub_right (Int.ceil_lt_add_one xq) (⌈yq⌉:ℚ))
      (sub_le_sub_left (Int.le_ceil yq) (xq+1))
  have hAlow' : ((b - a : ℤ):ℚ)/(D:ℚ) - 1 < (A:ℚ) := by rw [← hxqyq]; exact hAlow
  have hAhigh' : (A:ℚ) < ((b - a : ℤ):ℚ)/(D:ℚ) + 1 := by rw [← hxqyq2]; exact hAhigh
  have hAge0 : 0 ≤ A := by
    have hbq : (0:ℚ) ≤ ((b-a:ℤ):ℚ)/(D:ℚ) := div_nonneg (by exact_mod_cast hm) (le_of_lt hDqpos)
    have hneg : ((-1:ℤ):ℚ) < (A:ℚ) := by push_cast; linarith [hAlow', hbq]
    have : (-1:ℤ) < A := by exact_mod_cast hneg
    omega
  have hk : (k : ℤ) = A := hcardA.trans (max_eq_left hAge0)
  have hkR : (k:ℝ) = ((A:ℤ):ℝ) := by
    have := congrArg (fun z : ℤ => (z:ℝ)) hk
    simpa using this
  constructor
  · rw [hkR]
    have hR : ((A:ℤ):ℝ) < ((b-a:ℤ):ℝ)/(D:ℝ) + 1 := by
      have h := (Rat.cast_lt (K:=ℝ)).mpr hAhigh'
      simpa using h
    exact le_of_lt hR
  · rw [hkR]
    have hR : ((b-a:ℤ):ℝ)/(D:ℝ) - 1 < ((A:ℤ):ℝ) := by
      have h := (Rat.cast_lt (K:=ℝ)).mpr hAlow'
      simpa using h
    exact le_of_lt hR

/-- Green–Tao box/residue counting bound: the number of points of a box
`∏ⱼ [lⱼ, rⱼ) ∩ ℤᵗ` whose residue vector modulo `D` lies in `S` is, up to a
factor `∏ⱼ ((rⱼ - lⱼ)/D ± 1)`, equal to `|S|`. -/
theorem card_box_residue_close {t : ℕ} (l r : Fin t → ℤ) (D : ℕ) [NeZero D]
    (S : Finset (Fin t → ZMod D)) (hN : ∀ j, (D : ℤ) ≤ r j - l j) :
    (S.card : ℝ) * ∏ j, (((r j - l j : ℤ) : ℝ) / (D : ℝ) - 1)
        ≤ (((Fintype.piFinset (fun j => Finset.Ico (l j) (r j))).filter
            (fun x => (fun j => ((x j : ℤ) : ZMod D)) ∈ S)).card : ℝ) ∧
      (((Fintype.piFinset (fun j => Finset.Ico (l j) (r j))).filter
            (fun x => (fun j => ((x j : ℤ) : ZMod D)) ∈ S)).card : ℝ)
        ≤ (S.card : ℝ) * ∏ j, (((r j - l j : ℤ) : ℝ) / (D : ℝ) + 1) := by
  classical
  have hposR : (0:ℝ) < (D:ℝ) := by exact_mod_cast Nat.pos_of_neZero D
  have hjl : ∀ j, 0 ≤ r j - l j := fun j => le_trans (by exact_mod_cast Nat.zero_le D) (hN j)
  set B : Finset (Fin t → ℤ) := Fintype.piFinset (fun j => Finset.Ico (l j) (r j)) with hB
  have hfiber : ∀ c : Fin t → ZMod D,
      (B.filter (fun x => (fun j => ((x j : ℤ) : ZMod D)) = c)).card
        = ∏ j, ((Finset.Ico (l j) (r j)).filter (fun u : ℤ => (u : ZMod D) = c j)).card := by
    intro c
    have h1 : B.filter (fun x => (fun j => ((x j : ℤ) : ZMod D)) = c)
        = B.filter (fun x => ∀ j, ((x j : ℤ) : ZMod D) = c j) := by
      apply Finset.filter_congr
      intro x _
      exact funext_iff
    rw [h1, hB]
    have h2 : (Fintype.piFinset (fun j => Finset.Ico (l j) (r j))).filter
          (fun x => ∀ j, ((x j : ℤ) : ZMod D) = c j)
        = Fintype.piFinset (fun j => (Finset.Ico (l j) (r j)).filter (fun u : ℤ => ((u : ℤ) : ZMod D) = c j)) := by
      ext x
      simp only [Finset.mem_filter, Fintype.mem_piFinset]
      constructor
      · rintro ⟨hf, hp⟩ j; exact ⟨hf j, hp j⟩
      · intro h; exact ⟨fun j => (h j).1, fun j => (h j).2⟩
    rw [h2, Fintype.card_piFinset]
  have hNsum : (B.filter (fun x => (fun j => ((x j : ℤ) : ZMod D)) ∈ S)).card
      = ∑ c ∈ S, (B.filter (fun x => (fun j => ((x j : ℤ) : ZMod D)) = c)).card := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun x : Fin t → ℤ => (fun j => ((x j : ℤ) : ZMod D)))
      (s := B.filter (fun x => (fun j => ((x j : ℤ) : ZMod D)) ∈ S)) (t := S) ?_]
    · apply Finset.sum_congr rfl
      intro c hc
      congr 1
      rw [Finset.filter_filter]
      apply Finset.filter_congr
      intro x _
      constructor
      · rintro ⟨_, hxc⟩; exact hxc
      · intro hxc; exact ⟨by rw [hxc]; exact hc, hxc⟩
    · intro x hx
      exact (Finset.mem_filter.mp hx).2
  have hcast : ∀ c : Fin t → ZMod D,
      ((∏ j, ((Finset.Ico (l j) (r j)).filter (fun u : ℤ => (u : ZMod D) = c j)).card : ℕ) : ℝ)
        = ∏ j, (((Finset.Ico (l j) (r j)).filter (fun u : ℤ => (u : ZMod D) = c j)).card : ℝ) := by
    intro c
    rw [Nat.cast_prod]
  have hfiber_le : ∀ c : Fin t → ZMod D,
      ((∏ j, ((Finset.Ico (l j) (r j)).filter (fun u : ℤ => (u : ZMod D) = c j)).card : ℕ) : ℝ)
        ≤ ∏ j, (((r j - l j : ℤ) : ℝ) / (D : ℝ) + 1) := by
    intro c
    rw [hcast c]
    apply Finset.prod_le_prod
    · intro j _
      exact Nat.cast_nonneg _
    · intro j _
      exact (card_Ico_zmod_close D (l j) (r j) (c j) (hjl j)).1
  have hfiber_ge : ∀ c : Fin t → ZMod D,
      (∏ j, (((r j - l j : ℤ) : ℝ) / (D : ℝ) - 1))
        ≤ ((∏ j, ((Finset.Ico (l j) (r j)).filter (fun u : ℤ => (u : ZMod D) = c j)).card : ℕ) : ℝ) := by
    intro c
    rw [hcast c]
    apply Finset.prod_le_prod
    · intro j _
      have hj : (D:ℝ) ≤ ((r j - l j : ℤ) : ℝ) := by exact_mod_cast hN j
      have h1 : (1:ℝ) ≤ ((r j - l j : ℤ) : ℝ) / (D:ℝ) := (one_le_div hposR).mpr hj
      linarith
    · intro j _
      exact (card_Ico_zmod_close D (l j) (r j) (c j) (hjl j)).2
  have hsum_eq : ((B.filter (fun x => (fun j => ((x j : ℤ) : ZMod D)) ∈ S)).card : ℝ)
      = ∑ c ∈ S, ((∏ j, ((Finset.Ico (l j) (r j)).filter (fun u : ℤ => (u : ZMod D) = c j)).card : ℕ) : ℝ) := by
    rw [hNsum]
    push_cast
    apply Finset.sum_congr rfl
    intro c hc
    rw [hfiber c, hcast c]
  rw [hsum_eq]
  constructor
  · calc (S.card : ℝ) * ∏ j, (((r j - l j : ℤ) : ℝ) / (D : ℝ) - 1)
        = ∑ _c ∈ S, (∏ j, (((r j - l j : ℤ) : ℝ) / (D : ℝ) - 1)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ c ∈ S, ((∏ j, ((Finset.Ico (l j) (r j)).filter (fun u : ℤ => (u : ZMod D) = c j)).card : ℕ) : ℝ) :=
          Finset.sum_le_sum (fun c _ => hfiber_ge c)
  · calc ∑ c ∈ S, ((∏ j, ((Finset.Ico (l j) (r j)).filter (fun u : ℤ => (u : ZMod D) = c j)).card : ℕ) : ℝ)
        ≤ ∑ _c ∈ S, (∏ j, (((r j - l j : ℤ) : ℝ) / (D : ℝ) + 1)) :=
          Finset.sum_le_sum (fun c _ => hfiber_le c)
      _ = (S.card : ℝ) * ∏ j, (((r j - l j : ℤ) : ℝ) / (D : ℝ) + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]

end Commons.NumberTheory.Sieve