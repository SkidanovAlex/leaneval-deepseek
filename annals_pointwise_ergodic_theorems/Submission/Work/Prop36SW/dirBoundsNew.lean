import Mathlib
import Submission.Work.Prop36SW.stateSideBounds
import Submission.Work.Prop36SW.dirFamG_bound

namespace Work.Prop36SW

open scoped BigOperators

/-!
# The two direction-size bounds of the §5 chain state

This file proves `Work.Prop36SW.dirBoundsNew`, the pair of bounds that a state of the §5 chain of
`Work.Peluse.prop36SW_of_ladderA` inherits from the two chain invariants

* window: `M₁ ≤ (H+1)^{d-1-(m+1)}`, bumped to `M₁' ≤ M₁·(H+1)` at the round,
* ambient: `ambK D d c · (H+1)^d ≤ N`,

together with the datum bound `Λ ≤ (d-1)!`:

1. the *coefficient* bound `|pFlat D d c m (Λ·(d-(m+1))) i a| · M₁' · (H+1) ≤ N` on the whole closed
   box `Abox D (m+1) H`, i.e. the coefficient conjunct of the next state's `LStateBox`
   (this is `Work.Prop36SW.stateSideBounds` with the irrelevant hypothesis `1 ≤ H` removed);
2. the *direction* bound `|z| ≤ N` for every element `z` of the level-`(m+1)` direction family
   `pDirFamG (pFlat D d c m (Λ·(d-(m+1)))) M₁' a b` of the next state, for `a` in the closed box and
   `b` in the flat parameter box `paramBox (k := fun _ => 1) (H+1)`.

The second bound is the one the ladder does *not* carry (there the direction family is bundled into
the box norm), so it has to be extracted here from the `ℓ¹` direction bound `dirFamG_bound` (triangle
inequality over the slots of `ω`, with `|b s| ≤ H` from `paramBox (H+1)`), the coefficient bound
`pFlat_dirBound` and the arithmetic of the ambient constant `ambK`.
-/

/-- **The coefficient conjunct of the next state's `LStateBox`.**  `Work.Prop36SW.stateSideBounds`
without the (unused) hypothesis `1 ≤ H`. -/
private theorem flatCoeffBound (D : Work.Peluse.UControl.IdxDatum) (d : ℕ) (c : ℤ)
    (m Λ H M₁ M₁' N : ℕ)
    (hm : m + 2 ≤ d) (hΛ : Λ ≤ Nat.factorial (d - 1))
    (hM₁ : (M₁ : ℝ) ≤ ((H : ℝ) + 1) ^ (d - 1 - (m + 1)))
    (hM₁' : M₁' ≤ M₁ * (H + 1))
    (hN : Work.Prop36SW.ambK D d c * ((H : ℝ) + 1) ^ d ≤ (N : ℝ)) :
    ∀ (i : D.S (m + 1)) (a : Fin (Work.Peluse.Prop36SW.nD D (m + 1)) → ℤ),
        a ∈ Work.Peluse.Prop36SW.Abox D (m + 1) H →
        |Work.Peluse.Prop36SW.pFlat D d c m (Λ * (d - (m + 1))) i a| * (M₁' : ℤ) * ((H : ℤ) + 1)
          ≤ (N : ℤ) := by
  have hX1 : (1 : ℝ) ≤ (H : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) H; linarith
  have hCd_le : ∀ j : ℕ, j ≤ m → Fintype.card (D.S j) ≤ Work.Prop36SW.sSup D d :=
    fun j hj => Work.Prop36SW.card_le_sSup D (by omega)
  have hambK1 := Work.Prop36SW.one_le_ambK D d c
  have hconst := const_le_ambK (Work.Prop36SW.sSup D d) d m Λ c hm hΛ
  have hambK_eq : (2 : ℝ) ^ d * ((Work.Prop36SW.sSup D d : ℝ) + 1) ^ (d + 1)
      * ((Nat.factorial d : ℝ) + 1) ^ 2 * ((|(c : ℝ)|) + 1) * ((d : ℝ) + 1)
      = Work.Prop36SW.ambK D d c := by
    simp [Work.Prop36SW.ambK]
  set C0 : ℝ := ((Λ * (d - (m + 1)) : ℕ) : ℝ) * |(d : ℝ) - (m : ℝ)|
      * ((|(c : ℝ)|) * (Nat.factorial d : ℝ) * ((Work.Prop36SW.sSup D d : ℝ) + 1) ^ m) with hC0
  have hC0le : C0 ≤ Work.Prop36SW.ambK D d c := by
    rw [hC0, ← hambK_eq]
    exact hconst
  have hM₁'R : (M₁' : ℝ) ≤ ((H : ℝ) + 1) ^ (d - (m + 1)) := by
    have h2 : (M₁' : ℝ) ≤ (M₁ : ℝ) * ((H : ℝ) + 1) := by exact_mod_cast hM₁'
    have h3 : (M₁ : ℝ) * ((H : ℝ) + 1)
        ≤ ((H : ℝ) + 1) ^ (d - 1 - (m + 1)) * ((H : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hM₁ (by linarith)
    have h4 : ((H : ℝ) + 1) ^ (d - 1 - (m + 1)) * ((H : ℝ) + 1)
        = ((H : ℝ) + 1) ^ (d - (m + 1)) := by
      rw [← pow_succ]
      congr 1
      omega
    linarith [h2, h3, h4.le]
  intro i a ha
  have hdir := Work.Prop36SW.pFlat_dirBound D d c m (Λ * (d - (m + 1))) H
    (Work.Prop36SW.sSup D d) hCd_le i a ha
  have hdirR : (((|Work.Peluse.Prop36SW.pFlat D d c m (Λ * (d - (m + 1))) i a| : ℤ)) : ℝ)
      ≤ ((Λ * (d - (m + 1)) : ℕ) : ℝ) * |(d : ℝ) - (m : ℝ)|
        * ((|(c : ℝ)|) * (Nat.factorial d : ℝ)
            * (((Work.Prop36SW.sSup D d : ℝ) + 1) ^ m) * ((H : ℝ) + 1) ^ m) := by
    exact_mod_cast hdir
  have hdirR2 : (((|Work.Peluse.Prop36SW.pFlat D d c m (Λ * (d - (m + 1))) i a| : ℤ)) : ℝ)
      ≤ C0 * ((H : ℝ) + 1) ^ m := by
    have heq : C0 * ((H : ℝ) + 1) ^ m
        = ((Λ * (d - (m + 1)) : ℕ) : ℝ) * |(d : ℝ) - (m : ℝ)|
          * ((|(c : ℝ)|) * (Nat.factorial d : ℝ)
              * (((Work.Prop36SW.sSup D d : ℝ) + 1) ^ m) * ((H : ℝ) + 1) ^ m) := by
      rw [hC0]; ring
    rw [heq]; exact hdirR
  have hstep1 : (((|Work.Peluse.Prop36SW.pFlat D d c m (Λ * (d - (m + 1))) i a| : ℤ)) : ℝ)
        * (M₁' : ℝ) ≤ (C0 * ((H : ℝ) + 1) ^ m) * ((H : ℝ) + 1) ^ (d - (m + 1)) :=
    mul_le_mul hdirR2 hM₁'R (by positivity) (by positivity)
  have hstep2 : (((|Work.Peluse.Prop36SW.pFlat D d c m (Λ * (d - (m + 1))) i a| : ℤ)) : ℝ)
        * (M₁' : ℝ) * ((H : ℝ) + 1)
      ≤ (C0 * ((H : ℝ) + 1) ^ m) * ((H : ℝ) + 1) ^ (d - (m + 1)) * ((H : ℝ) + 1) :=
    mul_le_mul_of_nonneg_right hstep1 (by positivity)
  have hpow : ((H : ℝ) + 1) ^ m * ((H : ℝ) + 1) ^ (d - (m + 1)) * ((H : ℝ) + 1)
      = ((H : ℝ) + 1) ^ d := by
    rw [← pow_add, ← pow_succ]
    congr 1
    omega
  have hfin : (((|Work.Peluse.Prop36SW.pFlat D d c m (Λ * (d - (m + 1))) i a| : ℤ)) : ℝ)
        * (M₁' : ℝ) * ((H : ℝ) + 1)
      ≤ Work.Prop36SW.ambK D d c * ((H : ℝ) + 1) ^ d := by
    calc (((|Work.Peluse.Prop36SW.pFlat D d c m (Λ * (d - (m + 1))) i a| : ℤ)) : ℝ)
          * (M₁' : ℝ) * ((H : ℝ) + 1)
        ≤ (C0 * ((H : ℝ) + 1) ^ m) * ((H : ℝ) + 1) ^ (d - (m + 1)) * ((H : ℝ) + 1) := hstep2
      _ = C0 * (((H : ℝ) + 1) ^ m * ((H : ℝ) + 1) ^ (d - (m + 1)) * ((H : ℝ) + 1)) := by ring
      _ = C0 * ((H : ℝ) + 1) ^ d := by rw [hpow]
      _ ≤ Work.Prop36SW.ambK D d c * ((H : ℝ) + 1) ^ d :=
          mul_le_mul_of_nonneg_right hC0le (by positivity)
  have hR : (((|Work.Peluse.Prop36SW.pFlat D d c m (Λ * (d - (m + 1))) i a| : ℤ)) : ℝ)
        * (M₁' : ℝ) * ((H : ℝ) + 1) ≤ (N : ℝ) := le_trans hfin hN
  have hZ : ((|Work.Peluse.Prop36SW.pFlat D d c m (Λ * (d - (m + 1))) i a| * (M₁' : ℤ)
        * ((H : ℤ) + 1) : ℤ) : ℝ) ≤ ((N : ℤ) : ℝ) := by
    have hcast : ((|Work.Peluse.Prop36SW.pFlat D d c m (Λ * (d - (m + 1))) i a| * (M₁' : ℤ)
        * ((H : ℤ) + 1) : ℤ) : ℝ)
        = (((|Work.Peluse.Prop36SW.pFlat D d c m (Λ * (d - (m + 1))) i a| : ℤ)) : ℝ)
          * (M₁' : ℝ) * ((H : ℝ) + 1) := by push_cast; ring
    rw [hcast, Int.cast_natCast]
    exact hR
  exact_mod_cast hZ

/-- **The arithmetic of the ambient constant with the window factor.**  `Work.Prop36SW.ambK`
dominates the constant produced by `pFlat_dirBound` *multiplied by the slot count*: the `ℓ¹` bound
on the direction sum over the slots of `ω` produces the extra factor `card (D.S (m+1)) ≤ sSup D d`,
absorbed by `sSup·(sSup+1)^m ≤ (sSup+1)^{m+1} ≤ (sSup+1)^{d+1}`. -/
private theorem flatConstMulLeAmbK (D : Work.Peluse.UControl.IdxDatum) (d m Λ : ℕ) (c : ℤ)
    (hm : m + 2 ≤ d) (hΛ : Λ ≤ Nat.factorial (d - 1)) :
    ((Work.Prop36SW.sSup D d : ℝ))
      * (((Λ * (d - (m + 1)) : ℕ) : ℝ) * |(d : ℝ) - (m : ℝ)|
          * ((|(c : ℝ)|) * (Nat.factorial d : ℝ) * ((Work.Prop36SW.sSup D d : ℝ) + 1) ^ m))
    ≤ Work.Prop36SW.ambK D d c := by
  set S : ℝ := (Work.Prop36SW.sSup D d : ℝ) with hS
  have hS1 : (1 : ℝ) ≤ S + 1 := by
    have : (0 : ℝ) ≤ S := by rw [hS]; positivity
    linarith
  have hstep1 : S * (S + 1) ^ m ≤ (S + 1) ^ (d + 1) := by
    calc S * (S + 1) ^ m ≤ (S + 1) * (S + 1) ^ m :=
          mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (S + 1) ^ (m + 1) := (pow_succ' _ _).symm
      _ ≤ (S + 1) ^ (d + 1) := pow_le_pow_right₀ hS1 (by omega)
  have hA1 : ((Λ * (d - (m + 1)) : ℕ) : ℝ) ≤ (Nat.factorial d : ℝ) := by
    have hnat : Λ * (d - (m + 1)) ≤ Nat.factorial d := by
      have hd1 : 1 ≤ d := by omega
      have h1 : Λ * (d - (m + 1)) ≤ Nat.factorial (d - 1) * d :=
        Nat.mul_le_mul hΛ (Nat.sub_le d (m + 1))
      have h4 : Nat.factorial d = d * Nat.factorial (d - 1) := by
        have := Nat.factorial_succ (d - 1)
        rwa [Nat.sub_add_cancel hd1] at this
      rw [h4]
      calc Λ * (d - (m + 1)) ≤ Nat.factorial (d - 1) * d := h1
        _ = d * Nat.factorial (d - 1) := Nat.mul_comm _ _
    exact_mod_cast hnat
  have hA2 : |(d : ℝ) - (m : ℝ)| ≤ (d : ℝ) := by
    have h : (m : ℝ) ≤ (d : ℝ) := by
      have : m ≤ d := by omega
      exact_mod_cast this
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hA6 : (d : ℝ) ≤ (2 : ℝ) ^ d * ((d : ℝ) + 1) := by
    have h2d : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hF : (0 : ℝ) ≤ (Nat.factorial d : ℝ) := by positivity
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have hstep2 : ((Λ * (d - (m + 1)) : ℕ) : ℝ) * |(d : ℝ) - (m : ℝ)|
        * ((|(c : ℝ)|) * (Nat.factorial d : ℝ))
      ≤ (2 : ℝ) ^ d * ((Nat.factorial d : ℝ) + 1) ^ 2 * ((|(c : ℝ)|) + 1) * ((d : ℝ) + 1) := by
    have h1 : ((Λ * (d - (m + 1)) : ℕ) : ℝ) * |(d : ℝ) - (m : ℝ)|
        ≤ (Nat.factorial d : ℝ) * (d : ℝ) :=
      mul_le_mul hA1 hA2 (abs_nonneg _) hF
    have h2 : (|(c : ℝ)|) * (Nat.factorial d : ℝ) ≤ ((|(c : ℝ)|) + 1) * (Nat.factorial d : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith) hF
    have h3 : ((Λ * (d - (m + 1)) : ℕ) : ℝ) * |(d : ℝ) - (m : ℝ)|
          * ((|(c : ℝ)|) * (Nat.factorial d : ℝ))
        ≤ ((Nat.factorial d : ℝ) * (d : ℝ)) * (((|(c : ℝ)|) + 1) * (Nat.factorial d : ℝ)) :=
      mul_le_mul h1 h2 (mul_nonneg (abs_nonneg _) hF) (mul_nonneg hF hdnn)
    have h4 : ((Nat.factorial d : ℝ) * (d : ℝ)) * (((|(c : ℝ)|) + 1) * (Nat.factorial d : ℝ))
        = (Nat.factorial d : ℝ) ^ 2 * ((d : ℝ) * ((|(c : ℝ)|) + 1)) := by ring
    have h5 : (Nat.factorial d : ℝ) ^ 2 * ((d : ℝ) * ((|(c : ℝ)|) + 1))
        ≤ ((Nat.factorial d : ℝ) + 1) ^ 2
            * (((2 : ℝ) ^ d * ((d : ℝ) + 1)) * ((|(c : ℝ)|) + 1)) := by
      apply mul_le_mul
      · nlinarith [hF]
      · exact mul_le_mul_of_nonneg_right hA6 (by positivity)
      · positivity
      · positivity
    calc ((Λ * (d - (m + 1)) : ℕ) : ℝ) * |(d : ℝ) - (m : ℝ)|
          * ((|(c : ℝ)|) * (Nat.factorial d : ℝ))
        ≤ ((Nat.factorial d : ℝ) * (d : ℝ)) * (((|(c : ℝ)|) + 1) * (Nat.factorial d : ℝ)) := h3
      _ = (Nat.factorial d : ℝ) ^ 2 * ((d : ℝ) * ((|(c : ℝ)|) + 1)) := h4
      _ ≤ ((Nat.factorial d : ℝ) + 1) ^ 2
            * (((2 : ℝ) ^ d * ((d : ℝ) + 1)) * ((|(c : ℝ)|) + 1)) := h5
      _ = (2 : ℝ) ^ d * ((Nat.factorial d : ℝ) + 1) ^ 2 * ((|(c : ℝ)|) + 1) * ((d : ℝ) + 1) := by
          ring
  calc S * (((Λ * (d - (m + 1)) : ℕ) : ℝ) * |(d : ℝ) - (m : ℝ)|
        * ((|(c : ℝ)|) * (Nat.factorial d : ℝ) * (S + 1) ^ m))
      = (S * (S + 1) ^ m)
        * (((Λ * (d - (m + 1)) : ℕ) : ℝ) * |(d : ℝ) - (m : ℝ)|
            * ((|(c : ℝ)|) * (Nat.factorial d : ℝ))) := by ring
    _ ≤ (S + 1) ^ (d + 1)
        * ((2 : ℝ) ^ d * ((Nat.factorial d : ℝ) + 1) ^ 2 * ((|(c : ℝ)|) + 1) * ((d : ℝ) + 1)) :=
        mul_le_mul hstep1 hstep2 (by positivity) (by positivity)
    _ = Work.Prop36SW.ambK D d c := by
        rw [hS, Work.Prop36SW.ambK]
        ring

theorem dirBoundsNew (D : Work.Peluse.UControl.IdxDatum) (d : ℕ) (c : ℤ) (m Λ H M₁ M₁' N : ℕ)
    (hm : m + 2 ≤ d) (hΛ : Λ ≤ Nat.factorial (d - 1))
    (hM₁ : (M₁ : ℝ) ≤ ((H : ℝ) + 1) ^ (d - 1 - (m + 1)))
    (hM₁' : M₁' ≤ M₁ * (H + 1))
    (hN : Work.Prop36SW.ambK D d c * ((H : ℝ) + 1) ^ d ≤ (N : ℝ)) :
    (∀ (s : D.S (m + 1)) (a : Fin (Work.Peluse.Prop36SW.nD D (m + 1)) → ℤ),
        a ∈ Work.Peluse.Prop36SW.Abox D (m + 1) H →
        |Work.Peluse.Prop36SW.pFlat D d c m (Λ * (d - (m + 1))) s a| * (M₁' : ℤ) * ((H : ℤ) + 1)
          ≤ (N : ℤ)) ∧
    (∀ (kω' : Work.Peluse.UControl.SlotSet (D.S (m + 1)) (fun _ => 1) → ℕ)
        (a : Fin (Work.Peluse.Prop36SW.nD D (m + 1)) → ℤ)
        (b : Work.Peluse.UControl.Slot (D.S (m + 1)) (fun _ => 1) → ℤ),
        a ∈ Work.Peluse.Prop36SW.Abox D (m + 1) H →
        b ∈ Work.Peluse.UControl.paramBox (k := fun _ : D.S (m + 1) => 1) (H + 1) →
        ∀ j : Fin (Fintype.card (Work.Peluse.UControl.FamIdx kω')),
          ∀ z ∈ Work.Peluse.Prop36SW.pDirFamG
              (Work.Peluse.Prop36SW.pFlat D d c m (Λ * (d - (m + 1)))) M₁' a b
              ((Fintype.equivFin (Work.Peluse.UControl.FamIdx kω')).symm j), |z| ≤ (N : ℤ)) := by
  refine ⟨flatCoeffBound D d c m Λ H M₁ M₁' N hm hΛ hM₁ hM₁' hN, ?_⟩
  intro kω' a b ha hb j z hz
  set S : ℝ := (Work.Prop36SW.sSup D d : ℝ) with hS
  set C0 : ℝ := ((Λ * (d - (m + 1)) : ℕ) : ℝ) * |(d : ℝ) - (m : ℝ)|
      * ((|(c : ℝ)|) * (Nat.factorial d : ℝ) * (S + 1) ^ m) with hC0
  have hCd_le : ∀ j' : ℕ, j' ≤ m → Fintype.card (D.S j') ≤ Work.Prop36SW.sSup D d :=
    fun j' hj' => Work.Prop36SW.card_le_sSup D (by omega)
  have hcard : Fintype.card (D.S (m + 1)) ≤ Work.Prop36SW.sSup D d :=
    Work.Prop36SW.card_le_sSup D (by omega)
  have hp : ∀ s : Work.Peluse.UControl.Slot (D.S (m + 1)) (fun _ => 1),
      |(Work.Peluse.Prop36SW.pFlat D d c m (Λ * (d - (m + 1))) s.1 a : ℝ)|
        ≤ C0 * ((H : ℝ) + 1) ^ m := by
    intro s
    have h := Work.Prop36SW.pFlat_dirBound D d c m (Λ * (d - (m + 1))) H
      (Work.Prop36SW.sSup D d) hCd_le s.1 a ha
    have h' : (((|Work.Peluse.Prop36SW.pFlat D d c m (Λ * (d - (m + 1))) s.1 a| : ℤ)) : ℝ)
        ≤ ((Λ * (d - (m + 1)) : ℕ) : ℝ) * |(d : ℝ) - (m : ℝ)|
          * ((|(c : ℝ)|) * (Nat.factorial d : ℝ)
              * ((Work.Prop36SW.sSup D d : ℝ) + 1) ^ m * ((H : ℝ) + 1) ^ m) := by
      exact_mod_cast h
    rw [Int.cast_abs] at h'
    rw [hC0]
    calc |(Work.Peluse.Prop36SW.pFlat D d c m (Λ * (d - (m + 1))) s.1 a : ℝ)|
        ≤ ((Λ * (d - (m + 1)) : ℕ) : ℝ) * |(d : ℝ) - (m : ℝ)|
          * ((|(c : ℝ)|) * (Nat.factorial d : ℝ)
              * ((Work.Prop36SW.sSup D d : ℝ) + 1) ^ m * ((H : ℝ) + 1) ^ m) := h'
      _ = ((Λ * (d - (m + 1)) : ℕ) : ℝ) * |(d : ℝ) - (m : ℝ)|
            * ((|(c : ℝ)|) * (Nat.factorial d : ℝ) * (S + 1) ^ m) * ((H : ℝ) + 1) ^ m := by
          rw [hS]; ring
  have hz1 : |(z : ℝ)| ≤ (M₁' : ℝ)
      * (S * ((C0 * ((H : ℝ) + 1) ^ m) * ((H : ℝ) + 1))) := by
    have h := Work.Prop36SW.dirFamG_bound (ι := D.S (m + 1))
      (p := Work.Peluse.Prop36SW.pFlat D d c m (Λ * (d - (m + 1)))) a b M₁' H
      (Work.Prop36SW.sSup D d) (C0 * ((H : ℝ) + 1) ^ m) hb hp hcard kω' j z hz
    rwa [← hS] at h
  have hM₁'R : (M₁' : ℝ) ≤ ((H : ℝ) + 1) ^ (d - (m + 1)) := by
    have h2 : (M₁' : ℝ) ≤ (M₁ : ℝ) * ((H : ℝ) + 1) := by exact_mod_cast hM₁'
    have h3 : (M₁ : ℝ) * ((H : ℝ) + 1)
        ≤ ((H : ℝ) + 1) ^ (d - 1 - (m + 1)) * ((H : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hM₁ (by linarith)
    have h4 : ((H : ℝ) + 1) ^ (d - 1 - (m + 1)) * ((H : ℝ) + 1)
        = ((H : ℝ) + 1) ^ (d - (m + 1)) := by
      rw [← pow_succ]
      congr 1
      omega
    linarith [h2, h3, h4.le]
  have hSC0 : S * C0 ≤ Work.Prop36SW.ambK D d c := by
    have h := flatConstMulLeAmbK D d m Λ c hm hΛ
    rw [hS, hC0]
    exact h
  have hmain : |(z : ℝ)| ≤ Work.Prop36SW.ambK D d c * ((H : ℝ) + 1) ^ d := by
    have hpow : ((H : ℝ) + 1) ^ (d - (m + 1)) * (((H : ℝ) + 1) ^ m * ((H : ℝ) + 1))
        = ((H : ℝ) + 1) ^ d := by
      rw [← pow_succ, ← pow_add, Nat.sub_add_cancel (show m + 1 ≤ d by omega)]
    have hid : ((H : ℝ) + 1) ^ (d - (m + 1))
          * (S * ((C0 * ((H : ℝ) + 1) ^ m) * ((H : ℝ) + 1)))
        = (S * C0)
          * (((H : ℝ) + 1) ^ (d - (m + 1)) * (((H : ℝ) + 1) ^ m * ((H : ℝ) + 1))) := by
      ring
    have h2 : |(z : ℝ)| ≤ (S * C0) * ((H : ℝ) + 1) ^ d := by
      calc |(z : ℝ)| ≤ (M₁' : ℝ)
            * (S * ((C0 * ((H : ℝ) + 1) ^ m) * ((H : ℝ) + 1))) := hz1
        _ ≤ ((H : ℝ) + 1) ^ (d - (m + 1))
            * (S * ((C0 * ((H : ℝ) + 1) ^ m) * ((H : ℝ) + 1))) :=
            mul_le_mul_of_nonneg_right hM₁'R (by positivity)
        _ = (S * C0) * ((H : ℝ) + 1) ^ d := by rw [hid, hpow]
    exact le_trans h2 (mul_le_mul_of_nonneg_right hSC0 (by positivity))
  have hR : ((|z| : ℤ) : ℝ) ≤ ((N : ℤ) : ℝ) := by
    rw [Int.cast_abs, Int.cast_natCast]
    exact le_trans hmain hN
  exact_mod_cast hR

end Work.Prop36SW
