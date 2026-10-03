import Mathlib
import Submission.Work.Prop36SW.roundToNextDefs
import Submission.Work.Prop36SW.pFlat_dirBound

/-!
# The state's side conditions from the two chain invariants

The §5 chain carries, at slot level `m`, the two invariants

* the *window* invariant `M₁ ≤ (H+1)^{d-1-(m+1)}`, which is bumped by one power of `H+1` at every
  round (`M₁' ≤ M₁·(H+1)`);
* the *ambient* invariant `ambK D d c · (H+1)^d ≤ N`.

`stateSideBounds` records the two side conditions of the next state that follow *purely* from these
two invariants and the datum bound `Λ ≤ (d-1)!`:

* `M₁' · (H+1) ≤ N` (the new state's window fits in the ambient);
* `|pFlat D d c m (Λ·(d-(m+1))) i a| · M₁' · (H+1) ≤ N` on the whole closed box `Abox D (m+1) H`
  (the state's `LStateBox` coefficient bound, at the regrouped coefficient `Λ·(d-(m+1))` and the
  bumped window `M₁'`).

The whole content is the arithmetic of the ambient constant `ambK`: the direction bound
`pFlat_dirBound` produces the constant
`(Λ·(d-(m+1))) · |d-m| · |c| · d! · (Cd+1)^m` in front of the `(H+1)^m` power, and `Λ ≤ (d-1)!`,
`|d-m| ≤ d`, `|c| ≤ |c|+1` together with `d ≤ 2^d (d+1)` dominate it by `ambK`'s
`2^d (Cd+1)^{d+1} (d!+1)^2 (|c|+1) (d+1)`. The powers of `H+1` match exactly:
`m + (d-(m+1)) + 1 = d`.
-/

namespace Work.Prop36SW

/-- **The arithmetic of the ambient constant.**  The constant produced by the direction bound
`pFlat_dirBound` at slot level `m` (with datum `Λ ≤ (d-1)!`) is dominated by the ambient constant
built from `Cd`, `d` and `c`. -/
theorem const_le_ambK (Cd d m Λ : ℕ) (c : ℤ)
    (hm : m + 2 ≤ d) (hΛ : Λ ≤ Nat.factorial (d - 1)) :
    ((Λ * (d - (m + 1)) : ℕ) : ℝ) * |(d : ℝ) - (m : ℝ)|
      * ((|(c : ℝ)|) * (Nat.factorial d : ℝ) * ((Cd : ℝ) + 1) ^ m)
    ≤ (2 : ℝ) ^ d * ((Cd : ℝ) + 1) ^ (d + 1) * ((Nat.factorial d : ℝ) + 1) ^ 2
      * ((|(c : ℝ)|) + 1) * ((d : ℝ) + 1) := by
  have hmd : m ≤ d := by omega
  have hCd1 : (1 : ℝ) ≤ (Cd : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) Cd; linarith
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
    have h : (m : ℝ) ≤ (d : ℝ) := by exact_mod_cast hmd
    rw [abs_of_nonneg (by linarith)]
    linarith
  have hA3 : |(c : ℝ)| ≤ |(c : ℝ)| + 1 := by linarith
  have hA5 : ((Cd : ℝ) + 1) ^ m ≤ ((Cd : ℝ) + 1) ^ (d + 1) :=
    pow_le_pow_right₀ hCd1 (by omega)
  have hA6 : (d : ℝ) ≤ (2 : ℝ) ^ d * ((d : ℝ) + 1) := by
    have h2d : (1 : ℝ) ≤ (2 : ℝ) ^ d := one_le_pow₀ (by norm_num)
    nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hFnn : (0 : ℝ) ≤ (Nat.factorial d : ℝ) := by positivity
  have hA24 : ((Λ * (d - (m + 1)) : ℕ) : ℝ) * (Nat.factorial d : ℝ)
      ≤ ((Nat.factorial d : ℝ) + 1) ^ 2 := by
    calc ((Λ * (d - (m + 1)) : ℕ) : ℝ) * (Nat.factorial d : ℝ)
        ≤ (Nat.factorial d : ℝ) * (Nat.factorial d : ℝ) :=
          mul_le_mul hA1 le_rfl hFnn hFnn
      _ ≤ ((Nat.factorial d : ℝ) + 1) ^ 2 := by nlinarith
  have h2a : |(c : ℝ)| * ((Cd : ℝ) + 1) ^ m ≤ (|(c : ℝ)| + 1) * ((Cd : ℝ) + 1) ^ (d + 1) :=
    mul_le_mul hA3 hA5 (by positivity) (by positivity)
  have h2 : |(d : ℝ) - (m : ℝ)| * (|(c : ℝ)| * ((Cd : ℝ) + 1) ^ m)
      ≤ (d : ℝ) * ((|(c : ℝ)| + 1) * ((Cd : ℝ) + 1) ^ (d + 1)) :=
    mul_le_mul hA2 h2a (by positivity) (by positivity)
  have h2b : (d : ℝ) * ((|(c : ℝ)| + 1) * ((Cd : ℝ) + 1) ^ (d + 1))
      ≤ ((2 : ℝ) ^ d * ((d : ℝ) + 1)) * ((|(c : ℝ)| + 1) * ((Cd : ℝ) + 1) ^ (d + 1)) :=
    mul_le_mul_of_nonneg_right hA6 (by positivity)
  calc ((Λ * (d - (m + 1)) : ℕ) : ℝ) * |(d : ℝ) - (m : ℝ)|
        * ((|(c : ℝ)|) * (Nat.factorial d : ℝ) * ((Cd : ℝ) + 1) ^ m)
      = (((Λ * (d - (m + 1)) : ℕ) : ℝ) * (Nat.factorial d : ℝ))
        * (|(d : ℝ) - (m : ℝ)| * (|(c : ℝ)| * ((Cd : ℝ) + 1) ^ m)) := by ring
    _ ≤ (((Nat.factorial d : ℝ) + 1) ^ 2)
        * (((2 : ℝ) ^ d * ((d : ℝ) + 1)) * ((|(c : ℝ)| + 1) * ((Cd : ℝ) + 1) ^ (d + 1))) :=
        mul_le_mul hA24 (le_trans h2 h2b) (by positivity) (by positivity)
    _ = (2 : ℝ) ^ d * ((Cd : ℝ) + 1) ^ (d + 1) * ((Nat.factorial d : ℝ) + 1) ^ 2
        * ((|(c : ℝ)|) + 1) * ((d : ℝ) + 1) := by ring

theorem stateSideBounds (D : Work.Peluse.UControl.IdxDatum) (d : ℕ) (c : ℤ) (m Λ H M₁ M₁' N : ℕ)
    (hH : 1 ≤ H) (hm : m + 2 ≤ d) (hΛ : Λ ≤ Nat.factorial (d - 1))
    (hM₁ : (M₁ : ℝ) ≤ ((H : ℝ) + 1) ^ (d - 1 - (m + 1)))
    (hM₁' : M₁' ≤ M₁ * (H + 1))
    (hN : Work.Prop36SW.ambK D d c * ((H : ℝ) + 1) ^ d ≤ (N : ℝ)) :
    (M₁' : ℝ) * ((H : ℝ) + 1) ≤ (N : ℝ) ∧
      (∀ (i : D.S (m + 1)) (a : Fin (Work.Peluse.Prop36SW.nD D (m + 1)) → ℤ),
        a ∈ Work.Peluse.Prop36SW.Abox D (m + 1) H →
        |Work.Peluse.Prop36SW.pFlat D d c m (Λ * (d - (m + 1))) i a| * (M₁' : ℤ) * ((H : ℤ) + 1)
          ≤ (N : ℤ)) := by
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
  constructor
  · have hstep : (M₁' : ℝ) * ((H : ℝ) + 1) ≤ ((H : ℝ) + 1) ^ (d - (m + 1) + 1) := by
      calc (M₁' : ℝ) * ((H : ℝ) + 1) ≤ ((H : ℝ) + 1) ^ (d - (m + 1)) * ((H : ℝ) + 1) :=
            mul_le_mul_of_nonneg_right hM₁'R (by linarith)
        _ = ((H : ℝ) + 1) ^ (d - (m + 1) + 1) := (pow_succ _ _).symm
    have h5 : ((H : ℝ) + 1) ^ (d - (m + 1) + 1) ≤ ((H : ℝ) + 1) ^ d :=
      pow_le_pow_right₀ hX1 (by omega)
    have h6 : ((H : ℝ) + 1) ^ d ≤ Work.Prop36SW.ambK D d c * ((H : ℝ) + 1) ^ d :=
      le_mul_of_one_le_left (by positivity) hambK1
    linarith [hstep, h5, h6, hN]
  · intro i a ha
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

end Work.Prop36SW
