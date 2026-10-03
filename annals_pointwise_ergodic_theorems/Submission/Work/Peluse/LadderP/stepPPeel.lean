import Mathlib
import Submission.Work.Peluse.LadderP.stepPCore
import Submission.Work.Peluse.Ulower.iterDelta_finsupp

/-!
# The one-step lemma of the power-loss ladder: the peel

`boxLadderNorm (j+1) n` is an average over `h, h' ∈ [M₁]^{j+1}` of the level-`(2^{j+1}-1+n)`
box-norm power of `f` at the slots `c((h-h')·ω)[L]` (`ω` a nonzero pattern of `Fin (j+1)`) and `n`
copies of `c[D]`.  Splitting the patterns according to their last coordinate and peeling gives the
average over `h, h'` and over the shifts `(k, m)` of the `A`-slots and the long slots of the
level-`2^j` box-norm power of the iterated difference `Δ'_{(k,m)} f` at the `B`-slots, i.e. at the
directions `c(a + b_ω)[L]` where `a` is the parameter averaged by the Lemma 5.1 input.

The conclusion's state `boxLadderNorm j (n+s')` is peeled in the same way, leaving the `s'` long
slots of the uniformity norm: the two peeled forms involve the *same* iterated difference
`Δ'_{(k,m)} f`, which is what makes the two states comparable through the Lemma 5.1 input.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Work.Peluse.LadderP

noncomputable section

open Work.Peluse

/-- The short slots of the level-`j` state: `c((h-h')·ω)[L]` for `ω` a nonzero pattern of `Fin j`. -/
def ABlk0 (j M₁ : ℕ) (c : ℤ) (L : ℕ) (h h' : Fin j → Fin M₁) : Fin (2^j - 1) → Finset ℤ :=
  fun i => arithIcc (c * Concat.dotZ (Holds.omegaOf j i) (Concat.tupSub h h')) L

/-- The `A`-block of the peeled (j+1)-state: the slots of the `padL`-patterns (last coordinate
`false`), i.e. the short slots of the level-`j` state applied to the head of `(h,h')`. -/
def ABlk (j M₁ : ℕ) (c : ℤ) (L : ℕ) (h h' : Fin (j+1) → Fin M₁) : Fin (2^j - 1) → Finset ℤ :=
  ABlk0 j M₁ c L (headPart h) (headPart h')

/-- The `B`-block of the peeled (j+1)-state: the slots of the `padR`-patterns (last coordinate
`true`), i.e. the directions `c(a + b_ω)[L]` of the averaged parameter `a`. -/
def BBlk (j M₁ : ℕ) (c : ℤ) (L : ℕ) (E : Fin (2^j) ≃ (Fin j → Bool))
    (h h' : Fin (j+1) → Fin M₁) : Fin (2^j) → Finset ℤ :=
  fun i => arithIcc (c * Concat.dotZ (padR j (E i)) (Concat.tupSub h h')) L

/-- The long block: `n` copies of the long window `c[D]`. -/
def longBlk (n : ℕ) (c : ℤ) (D : ℕ) : Fin n → Finset ℤ := fun _ => arithIcc c D

/-- The level bookkeeping of the ladder step. -/
lemma lev_eq (j n : ℕ) : 2^(j+1) - 1 + n = (2^j - 1) + (2^j + n) := by
  have h : 2^(j+1) = 2 * 2^j := by rw [pow_succ']
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  omega

lemma pow_pred (j : ℕ) : 2^j - 1 + 2^j = 2^(j+1) - 1 := by
  have h : 2^(j+1) = 2 * 2^j := by rw [pow_succ']
  have h1 : 1 ≤ 2^j := Nat.one_le_two_pow
  omega

/-! ## The slot families as concatenations -/

/-- **The slots of the (j+1)-state with the enumeration `augEnum`.**  They are the concatenation of
the `A`-block with the concatenation of the `B`-block and the long block. -/
theorem ladderSlots_aug_eq (j n M₁ : ℕ) (c : ℤ) (L D : ℕ) (h h' : Fin (j+1) → Fin M₁) :
    (fun m : Fin (2^(j+1) - 1 + n) =>
        Holds.ladderSlots (j+1) n M₁ c (augEnum j) L D h h' m)
      = fun m : Fin (2^(j+1) - 1 + n) =>
          Fin.append (ABlk j M₁ c L h h')
            (Fin.append (BBlk j M₁ c L (enumAll j) h h') (longBlk n c D))
            (Fin.cast (lev_eq j n) m) := by
  funext m
  by_cases h1 : (m : ℕ) < 2^j - 1
  · have hcast : Fin.cast (lev_eq j n) m
        = Fin.castAdd (2^j + n) (⟨(m : ℕ), h1⟩ : Fin (2^j - 1)) := by
      ext
      simp [Fin.val_cast, Fin.val_castAdd]
    rw [hcast, Fin.append_left]
    rw [Holds.ladderSlots, dif_pos (by omega), augEnum_low h1, dotZ_padL]
    rfl

  · have hpred : 2^j - 1 + 2^j = 2^(j+1) - 1 := pow_pred j
    by_cases h2 : (m : ℕ) < 2^j - 1 + 2^j
    · have hlt : (m : ℕ) < 2^(j+1) - 1 := by omega
      have hcast : Fin.cast (lev_eq j n) m
          = Fin.natAdd (2^j - 1) (Fin.castAdd n
              (⟨(m : ℕ) - (2^j - 1), by omega⟩ : Fin (2^j))) := by
        ext
        simp only [Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd]
        omega
      conv_rhs => rw [hcast, Fin.append_right, Fin.append_left]
      rw [Holds.ladderSlots, dif_pos hlt, augEnum_high (i := ⟨(m : ℕ), hlt⟩) h1, dotZ_padR]
      simp only [BBlk, dotZ_padR]
    · have hge : 2^(j+1) - 1 ≤ (m : ℕ) := by omega
      have hcast : Fin.cast (lev_eq j n) m
          = Fin.natAdd (2^j - 1) (Fin.natAdd (2^j)
              (⟨(m : ℕ) - (2^j - 1) - 2^j, by omega⟩ : Fin n)) := by
        ext
        simp only [Fin.val_cast, Fin.val_natAdd]
        omega
      conv_rhs => rw [hcast, Fin.append_right, Fin.append_right]
      rw [Holds.ladderSlots, dif_neg (by
        have := pow_pred j; omega)]
      rfl

/-- **The slots of the j-state.**  They are the concatenation of the short block and the `n'` long
slots. -/
theorem ladderSlots_j_eq (j n' M₁ : ℕ) (c : ℤ) (L D : ℕ) (h h' : Fin j → Fin M₁) :
    Holds.ladderSlots j n' M₁ c (Holds.omegaOf j) L D h h'
      = Fin.append (ABlk0 j M₁ c L h h') (longBlk n' c D) := by
  funext m
  by_cases h1 : (m : ℕ) < 2^j - 1
  · have hcast : m = Fin.castAdd n' (⟨(m : ℕ), h1⟩ : Fin (2^j - 1)) := by
      ext
      simp [Fin.val_castAdd]
    conv_rhs => rw [hcast, Fin.append_left]
    rw [Holds.ladderSlots, dif_pos h1]
    rfl
  · have hcast : m = Fin.natAdd (2^j - 1) (⟨(m : ℕ) - (2^j - 1), by omega⟩ : Fin n') := by
      ext
      simp only [Fin.val_natAdd]
      omega
    conv_rhs => rw [hcast, Fin.append_right]
    rw [Holds.ladderSlots, dif_neg h1]
    rfl

/-- The tallied slot family of the (j+1)-state (the append form, with the level cast built in). -/
def augSlots (j n M₁ : ℕ) (c : ℤ) (L D : ℕ) (h h' : Fin (j+1) → Fin M₁) :
    Fin (2^(j+1) - 1 + n) → Finset ℤ :=
  fun m => Fin.append (ABlk j M₁ c L h h')
    (Fin.append (BBlk j M₁ c L (enumAll j) h h') (longBlk n c D)) (Fin.cast (lev_eq j n) m)

/-- The tallied slot family of the j-state. -/
def patSlots (j n' M₁ : ℕ) (c : ℤ) (L D : ℕ) (h h' : Fin j → Fin M₁) :
    Fin (2^j - 1 + n') → Finset ℤ :=
  Fin.append (ABlk0 j M₁ c L h h') (longBlk n' c D)

lemma augSlots_eq (j n M₁ : ℕ) (c : ℤ) (L D : ℕ) (h h' : Fin (j+1) → Fin M₁) :
    augSlots j n M₁ c L D h h' = Holds.ladderSlots (j+1) n M₁ c (augEnum j) L D h h' := by
  funext m
  exact (congrFun (ladderSlots_aug_eq j n M₁ c L D h h') m).symm

/-- The long block is independent of the block decomposition. -/
lemma longBlk_split (n s' : ℕ) (c : ℤ) (D : ℕ) :
    longBlk (n + s') c D = Fin.append (longBlk n c D) (longBlk s' c D) := by
  funext i
  refine Fin.addCases (motive := fun i => longBlk (n + s') c D i
    = Fin.append (longBlk n c D) (longBlk s' c D) i) ?_ ?_ i
  · intro a
    simp only [longBlk, Fin.append_left]
  · intro b
    simp only [longBlk, Fin.append_right]

/-! ## The block swap -/

/-- The permutation of `Fin (t+n)` that swaps the two blocks. -/
noncomputable def swapEquiv (t n : ℕ) : Fin (t + n) ≃ Fin (n + t) :=
  (finSumFinEquiv.symm.trans (Equiv.sumComm (Fin t) (Fin n))).trans finSumFinEquiv

lemma swapEquiv_castAdd (t n : ℕ) (j : Fin t) :
    swapEquiv t n (Fin.castAdd n j) = Fin.natAdd n j := by
  have h1 : finSumFinEquiv.symm (Fin.castAdd n j) = Sum.inl j := by
    rw [Equiv.symm_apply_eq]
    rfl
  simp only [swapEquiv, Equiv.trans_apply, h1]
  rfl

lemma swapEquiv_natAdd (t n : ℕ) (j : Fin n) :
    swapEquiv t n (Fin.natAdd t j) = Fin.castAdd t j := by
  have h1 : finSumFinEquiv.symm (Fin.natAdd t j) = Sum.inr j := by
    rw [Equiv.symm_apply_eq]
    rfl
  simp only [swapEquiv, Equiv.trans_apply, h1]
  rfl

/-- Swapping the two blocks of a concatenated direction family does not change the box-norm
power. -/
theorem boxNormPow_append_swap {t n : ℕ} (B : Fin t → Finset ℤ) (Dl : Fin n → Finset ℤ)
    (S : Finset ℤ) (f : ℤ → ℂ) :
    boxNormPow (n + t) (Fin.append Dl B) S f = boxNormPow (t + n) (Fin.append B Dl) S f := by
  have h := LadderA.boxNormPow_reindex (m := t + n) (m' := n + t) (Nat.add_comm n t)
    (swapEquiv t n) (Fin.append B Dl) S f
  have hf : (fun i : Fin (n + t) => Fin.append B Dl ((swapEquiv t n).symm i))
      = Fin.append Dl B := by
    funext i
    refine Fin.addCases (motive := fun i => Fin.append B Dl ((swapEquiv t n).symm i)
      = Fin.append Dl B i) ?_ ?_ i
    · intro j
      have h1 : (swapEquiv t n).symm (Fin.castAdd t j) = Fin.natAdd t j := by
        rw [Equiv.symm_apply_eq]
        exact (swapEquiv_natAdd t n j).symm
      rw [h1, Fin.append_right, Fin.append_left]
    · intro j
      have h1 : (swapEquiv t n).symm (Fin.natAdd n j) = Fin.castAdd n j := by
        rw [Equiv.symm_apply_eq]
        exact (swapEquiv_castAdd t n j).symm
      rw [h1, Fin.append_left, Fin.append_right]
  rw [hf] at h
  exact h

/-- Reindexing a family along a `Fin.cast` inside the box-norm power. -/
lemma boxNormPow_comp_cast {a b : ℕ} (h : a = b) (Q : Fin b → Finset ℤ) (S : Finset ℤ)
    (f : ℤ → ℂ) :
    boxNormPow a (fun i => Q (Fin.cast h i)) S f = boxNormPow b Q S f := by
  subst h
  exact BoxNorm.boxNormPow_perm (Equiv.refl _) Q S f

lemma prod_longBlk (n : ℕ) (c : ℤ) (D : ℕ) :
    (∏ i : Fin n, (((longBlk n c D i).card : ℝ))⁻¹ ^ 2)
      = (∏ _i : Fin n, (((arithIcc c D).card : ℝ))⁻¹ ^ 2) := by
  refine Finset.prod_congr rfl (fun i _ => ?_)
  simp only [longBlk]

/-! ## The peel of the two states -/

/-- **The peel of the (j+1)-state at fixed `(h,h')`.**  The `A`-slots and the `n` long slots are
peeled off; what remains is the level-`2^j` box-norm power of the iterated difference at the
`B`-slots. -/
theorem peel_succ_inner (j n M₁ : ℕ) (c : ℤ) (L D : ℕ) (N : ℕ) (f : ℤ → ℂ) (h h' : Fin (j+1) → Fin M₁)
    (hf : FinSuppZ f) :
    boxNormPow (2^(j+1) - 1 + n) (augSlots j n M₁ c L D h h') (symIcc N) f
      = (∏ i : Fin (2^j - 1), (((ABlk j M₁ c L h h' i).card : ℝ))⁻¹ ^ 2)
        * (∏ _i : Fin n, (((arithIcc c D).card : ℝ))⁻¹ ^ 2)
        * ∑ k : (i : Fin (2^j - 1)) → ↥(ABlk j M₁ c L h h' i) × ↥(ABlk j M₁ c L h h' i),
          ∑ m : (i : Fin n) → ↥(arithIcc c D) × ↥(arithIcc c D),
            boxNormPow (2^j) (BBlk j M₁ c L (enumAll j) h h') (symIcc N)
              (Ulower.iterDelta n (fun i : Fin n => (((m i).1 : ℤ), ((m i).2 : ℤ)))
                (Ulower.iterDelta (2^j - 1)
                  (fun i : Fin (2^j - 1) => (((k i).1 : ℤ), ((k i).2 : ℤ))) f)) := by
  rw [show augSlots j n M₁ c L D h h'
      = (fun m : Fin (2^(j+1) - 1 + n) => Fin.append (ABlk j M₁ c L h h')
          (Fin.append (BBlk j M₁ c L (enumAll j) h h') (longBlk n c D))
          (Fin.cast (lev_eq j n) m)) from rfl]
  rw [boxNormPow_comp_cast (lev_eq j n)
    (Fin.append (ABlk j M₁ c L h h')
      (Fin.append (BBlk j M₁ c L (enumAll j) h h') (longBlk n c D))) (symIcc N) f]
  rw [LadderA.boxNormPow_peel_append (a := 2^j + n) (b := 2^j - 1)
    (by have h := Nat.one_le_two_pow (n := j); omega)
    (Fin.append (BBlk j M₁ c L (enumAll j) h h') (longBlk n c D)) (ABlk j M₁ c L h h')
    (symIcc N) f hf]
  have hstep : ∀ k : (i : Fin (2^j - 1)) → ↥(ABlk j M₁ c L h h' i) × ↥(ABlk j M₁ c L h h' i),
      boxNormPow (2^j + n) (Fin.append (BBlk j M₁ c L (enumAll j) h h') (longBlk n c D))
          (symIcc N)
          (Ulower.iterDelta (2^j - 1)
            (fun i : Fin (2^j - 1) => (((k i).1 : ℤ), ((k i).2 : ℤ))) f)
        = (∏ _i : Fin n, (((arithIcc c D).card : ℝ))⁻¹ ^ 2)
          * ∑ m : (i : Fin n) → ↥(arithIcc c D) × ↥(arithIcc c D),
              boxNormPow (2^j) (BBlk j M₁ c L (enumAll j) h h') (symIcc N)
                (Ulower.iterDelta n (fun i : Fin n => (((m i).1 : ℤ), ((m i).2 : ℤ)))
                  (Ulower.iterDelta (2^j - 1)
                    (fun i : Fin (2^j - 1) => (((k i).1 : ℤ), ((k i).2 : ℤ))) f)) := by
    intro k
    set g : ℤ → ℂ := Ulower.iterDelta (2^j - 1)
      (fun i : Fin (2^j - 1) => (((k i).1 : ℤ), ((k i).2 : ℤ))) f with hg
    have hgf : FinSuppZ g := Ulower.iterDelta_finsupp (fun i : Fin (2^j - 1) => (((k i).1 : ℤ), ((k i).2 : ℤ))) hf
    rw [← boxNormPow_append_swap (BBlk j M₁ c L (enumAll j) h h') (longBlk n c D) (symIcc N) g]
    rw [LadderA.boxNormPow_peel_append (a := 2^j) (b := n)
      (by have h := Nat.one_le_two_pow (n := j); omega)
      (BBlk j M₁ c L (enumAll j) h h') (longBlk n c D) (symIcc N) g hgf]
    rw [prod_longBlk]
    simp only [longBlk]
    rfl
  rw [Finset.sum_congr rfl (fun k _ => hstep k)]
  rw [← Finset.mul_sum]
  ring

/-- **The peel of the j-state at fixed `(h,h')`.**  The short slots and the `n` long slots are peeled
off; what remains is the level-`s'` box-norm power of the *same* iterated difference at the `s'`
remaining long slots. -/
theorem peel_concl_inner (j n s' M₁ : ℕ) (c : ℤ) (L D : ℕ) (N : ℕ) (f : ℤ → ℂ)
    (h h' : Fin j → Fin M₁) (hs' : 1 ≤ s') (hf : FinSuppZ f) :
    boxNormPow (2^j - 1 + (n + s')) (patSlots j (n + s') M₁ c L D h h') (symIcc N) f
      = (∏ i : Fin (2^j - 1), (((ABlk0 j M₁ c L h h' i).card : ℝ))⁻¹ ^ 2)
        * (∏ _i : Fin n, (((arithIcc c D).card : ℝ))⁻¹ ^ 2)
        * ∑ k : (i : Fin (2^j - 1)) → ↥(ABlk0 j M₁ c L h h' i) × ↥(ABlk0 j M₁ c L h h' i),
          ∑ m : (i : Fin n) → ↥(arithIcc c D) × ↥(arithIcc c D),
            boxNormPow s' (longBlk s' c D) (symIcc N)
              (Ulower.iterDelta n (fun i : Fin n => (((m i).1 : ℤ), ((m i).2 : ℤ)))
                (Ulower.iterDelta (2^j - 1)
                  (fun i : Fin (2^j - 1) => (((k i).1 : ℤ), ((k i).2 : ℤ))) f)) := by
  rw [patSlots, longBlk_split]
  rw [LadderA.boxNormPow_peel_append (a := n + s') (b := 2^j - 1) (by omega)
    (Fin.append (longBlk n c D) (longBlk s' c D)) (ABlk0 j M₁ c L h h') (symIcc N) f hf]
  have hstep : ∀ k : (i : Fin (2^j - 1)) → ↥(ABlk0 j M₁ c L h h' i) × ↥(ABlk0 j M₁ c L h h' i),
      boxNormPow (n + s') (Fin.append (longBlk n c D) (longBlk s' c D)) (symIcc N)
          (Ulower.iterDelta (2^j - 1)
            (fun i : Fin (2^j - 1) => (((k i).1 : ℤ), ((k i).2 : ℤ))) f)
        = (∏ _i : Fin n, (((arithIcc c D).card : ℝ))⁻¹ ^ 2)
          * ∑ m : (i : Fin n) → ↥(arithIcc c D) × ↥(arithIcc c D),
              boxNormPow s' (longBlk s' c D) (symIcc N)
                (Ulower.iterDelta n (fun i : Fin n => (((m i).1 : ℤ), ((m i).2 : ℤ)))
                  (Ulower.iterDelta (2^j - 1)
                    (fun i : Fin (2^j - 1) => (((k i).1 : ℤ), ((k i).2 : ℤ))) f)) := by
    intro k
    set g : ℤ → ℂ := Ulower.iterDelta (2^j - 1)
      (fun i : Fin (2^j - 1) => (((k i).1 : ℤ), ((k i).2 : ℤ))) f with hg
    have hgf : FinSuppZ g := Ulower.iterDelta_finsupp (fun i : Fin (2^j - 1) => (((k i).1 : ℤ), ((k i).2 : ℤ))) hf
    rw [LadderA.boxNormPow_peel_append (a := s') (b := n) hs'
      (longBlk s' c D) (longBlk n c D) (symIcc N) g hgf]
    rw [prod_longBlk]
    simp only [longBlk]
    rfl
  rw [Finset.sum_congr rfl (fun k _ => hstep k)]
  rw [← Finset.mul_sum]
  ring

end

end Work.Peluse.LadderP
