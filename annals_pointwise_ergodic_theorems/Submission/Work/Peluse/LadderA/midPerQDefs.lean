import Mathlib
import Submission.Work.Peluse.ladderA_peel

/-!
# Plumbing for the per-pair bound of the ladder

This file collects the abbreviations and elementary bookkeeping used in
`Work.Peluse.LadderA.midPerQ`: the shift-tuple index type of the peel, its weight, the associated
iterated difference, and the numerical constants of the ladder's peel.  Everything is an `abbrev`
so that the definitional equalities with the raw expressions of the statement are automatic.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

open scoped BigOperators

namespace Work.Peluse.LadderA

noncomputable section

open Work.Peluse Work.Peluse.UControl Work.Peluse.Ulower

variable {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The constant `Kb = m·(#Slot·D + 1) + 1` of the ladder's peel. -/
abbrev Kbv (k : ι → ℕ) (D m : ℕ) : ℕ := m * (Fintype.card (Slot ι k) * D + 1) + 1

/-- The enlarged window `Nw = Kb·N` on which all the norms of the per-pair bound live. -/
abbrev Win (k : ι → ℕ) (D m N : ℕ) : ℕ := Kbv k D m * N

/-- The symmetric window `(-M₂, M₂) ∩ ℤ` of the peeled parameter. -/
abbrev IooV (M₂ : ℕ) : Finset ℤ := Finset.Ioo (-(M₂ : ℤ)) (M₂ : ℤ)

/-- The constant `c₀ = γ/((Kb+1)·2)` of the good-set threshold. -/
abbrev Cz (k : ι → ℕ) (D m : ℕ) (γ : ℝ) : ℝ := γ / ((((Kbv k D m : ℕ) : ℝ) + 1) * 2)

/-- The constant `c₁·γ^{2^m}`: the peel's per-pair input `δ₀`. -/
abbrev Dtv (c₁ γ : ℝ) (m : ℕ) : ℝ := c₁ * γ ^ (2 ^ m)

/-- The shift-tuple index of the ladder's peel: a choice of a pair `(h, h')` of elements of each
direction of the `B`-part. -/
abbrev ShiftTuple (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a'' : Slot ι k → ℤ) (s₀ : Slot ι k) : Type :=
  (j : Fin (Fintype.card (BIdx k kω s₀))) →
    ↥(QBfin k kω p M₁ a a'' s₀ j) × ↥(QBfin k kω p M₁ a a'' s₀ j)

/-- The `B`-weight `∏_j |Q_j|⁻²` of the peel. -/
abbrev peelWeight (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a'' : Slot ι k → ℤ) (s₀ : Slot ι k) : ℝ :=
  ∏ j : Fin (Fintype.card (BIdx k kω s₀)), ((QBfin k kω p M₁ a a'' s₀ j).card : ℝ)⁻¹ ^ 2

/-- The iterated difference of `f` along a shift tuple of the peel. -/
abbrev shiftId (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a'' : Slot ι k → ℤ) (s₀ : Slot ι k)
    (sh : ShiftTuple k kω p M₁ a a'' s₀) (f : ℤ → ℂ) : ℤ → ℂ :=
  iterDelta (Fintype.card (BIdx k kω s₀)) (fun j => (((sh j).1 : ℤ), ((sh j).2 : ℤ))) f

/-- The `A`-part direction family at the peeled parameter `a₀`. -/
abbrev AFam (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a'' : Slot ι k → ℤ) (s₀ : Slot ι k) (a₀ : ℤ) :
    Fin (Fintype.card (AIdx k kω s₀)) → Finset ℤ :=
  fun i => QAfin k kω p M₁ a (Function.update a'' s₀ a₀) s₀ i

/-- The `A`-level box-norm power of the shifted function at the peeled parameter `a₀`. -/
abbrev ANorm (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a'' : Slot ι k → ℤ) (s₀ : Slot ι k) (Nw : ℕ) (a₀ : ℤ)
    (sh : ShiftTuple k kω p M₁ a a'' s₀) (f : ℤ → ℂ) : ℝ :=
  boxNormPow (Fintype.card (AIdx k kω s₀)) (AFam k kω p M₁ a a'' s₀ a₀) (symIcc Nw)
    (shiftId k kω p M₁ a a'' s₀ sh f)

/-- The `A`-level box *norm* of the shifted function at the peeled parameter `a₀`. -/
abbrev ABox (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a'' : Slot ι k → ℤ) (s₀ : Slot ι k) (Nw : ℕ) (a₀ : ℤ)
    (sh : ShiftTuple k kω p M₁ a a'' s₀) (f : ℤ → ℂ) : ℝ :=
  boxNorm (Fintype.card (AIdx k kω s₀)) (AFam k kω p M₁ a a'' s₀ a₀) (symIcc Nw)
    (shiftId k kω p M₁ a a'' s₀ sh f)

/-- The long-direction box-norm power of the shifted function. -/
abbrev LNorm (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a'' : Slot ι k → ℤ) (s₀ : Slot ι k) (tbig M₂ Nw : ℕ) (γ' : ℝ)
    (sh : ShiftTuple k kω p M₁ a a'' s₀) (f : ℤ → ℂ) : ℝ :=
  boxNormPow tbig (fun _ : Fin tbig =>
      arithIcc (p s₀.1 a) (⌊γ' * (M₁ : ℝ) * (M₂ : ℝ)⌋).toNat) (symIcc Nw)
    (shiftId k kω p M₁ a a'' s₀ sh f)

/-- The per-shift line average of the `A`-level box norms: the quantity Theorem 3.5 consumes. -/
abbrev DSh (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a'' : Slot ι k → ℤ) (s₀ : Slot ι k) (M₂ Nw : ℕ)
    (sh : ShiftTuple k kω p M₁ a a'' s₀) (f : ℤ → ℂ) : ℝ :=
  ((IooV M₂).card : ℝ)⁻¹ * ∑ a₀ ∈ IooV M₂, ABox k kω p M₁ a a'' s₀ Nw a₀ sh f

/-- The number of shift tuples is the product of the squared sizes of the `B`-directions. -/
lemma card_shiftTuple (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a'' : Slot ι k → ℤ) (s₀ : Slot ι k) :
    Fintype.card (ShiftTuple k kω p M₁ a a'' s₀) =
      ∏ j : Fin (Fintype.card (BIdx k kω s₀)), (QBfin k kω p M₁ a a'' s₀ j).card ^ 2 := by
  change Fintype.card ((j : Fin (Fintype.card (BIdx k kω s₀))) →
      ↥(QBfin k kω p M₁ a a'' s₀ j) × ↥(QBfin k kω p M₁ a a'' s₀ j)) = _
  rw [Fintype.card_pi]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [Fintype.card_prod, Fintype.card_coe]
  ring

/-- A `B`-direction is nonempty as soon as `M₁ ≥ 1`. -/
lemma QBfin_nonempty' (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a'' : Slot ι k → ℤ) (s₀ : Slot ι k) (hM₁ : 1 ≤ M₁)
    (j : Fin (Fintype.card (BIdx k kω s₀))) :
    (QBfin k kω p M₁ a a'' s₀ j).Nonempty := by
  rw [QBfin, qB, pDir, arithIcc]
  exact Finset.Nonempty.image ⟨1, by simp [hM₁]⟩ _

/-- **The peel weight times the number of shift tuples is one.** -/
lemma peelWeight_mul_card (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ)
    (M₁ : ℕ) (a : Fin n → ℤ) (a'' : Slot ι k → ℤ) (s₀ : Slot ι k) (hM₁ : 1 ≤ M₁) :
    peelWeight k kω p M₁ a a'' s₀ * (Fintype.card (ShiftTuple k kω p M₁ a a'' s₀) : ℝ) = 1 := by
  rw [card_shiftTuple k kω p M₁ a a'' s₀]
  simp only [peelWeight, Nat.cast_prod, Nat.cast_pow]
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one (fun j _ => ?_)
  have hc : ((QBfin k kω p M₁ a a'' s₀ j).card : ℝ) ≠ 0 := by
    have h := Finset.card_ne_zero.mpr (QBfin_nonempty' k kω p M₁ a a'' s₀ hM₁ j)
    exact_mod_cast h
  rw [← mul_pow, inv_mul_cancel₀ hc, one_pow]

/-- The peel weight is nonnegative. -/
lemma peelWeight_nonneg (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a'' : Slot ι k → ℤ) (s₀ : Slot ι k) :
    0 ≤ peelWeight k kω p M₁ a a'' s₀ := by
  simp only [peelWeight]
  exact Finset.prod_nonneg (fun j _ => by positivity)

/-- A function supported in `[-N,N]` vanishes off `symIcc N`. -/
lemma eq_zero_of_not_mem_symIcc {N : ℕ} {g : ℤ → ℂ} (h : Work.Peluse.SupportIn g N) {x : ℤ}
    (hx : x ∉ Work.Peluse.symIcc N) : g x = 0 := by
  have h1 : ¬ (|x| ≤ (N : ℤ)) := fun hc => hx (Work.Peluse.PET.mem_symIcc_iff_abs.mpr hc)
  have h2 : (N : ℤ) < |x| := lt_of_not_ge h1
  rw [← Int.natCast_natAbs] at h2
  have h3 : N < x.natAbs := by omega
  exact h x h3

/-- For `0 ≤ x ≤ 1` and `r ≤ 1` one has `x ≤ x ^ r`. -/
lemma le_rpow_of_le_one {x r : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hr : r ≤ 1) : x ≤ x ^ r := by
  rcases eq_or_lt_of_le hx0 with h | h
  · rw [← h]
    exact Real.rpow_nonneg le_rfl _
  · calc x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
      _ ≤ x ^ r := Real.rpow_le_rpow_of_exponent_ge h hx1 hr

/-- The `A`-level box-norm power of a `1`-bounded, supported shifted function is at most one. -/
lemma ANorm_le_one (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a'' : Slot ι k → ℤ) (s₀ : Slot ι k) (Nw : ℕ) (a₀ : ℤ)
    (sh : ShiftTuple k kω p M₁ a a'' s₀) (f : ℤ → ℂ)
    (hsupp : Work.Peluse.SupportIn (shiftId k kω p M₁ a a'' s₀ sh f) Nw)
    (hnorm : ∀ x : ℤ, ‖shiftId k kω p M₁ a a'' s₀ sh f x‖ ≤ 1) :
    ANorm k kω p M₁ a a'' s₀ Nw a₀ sh f ≤ 1 := by
  simp only [ANorm]
  exact BoxNorm.boxNormPow_le_one hnorm (fun x hx => eq_zero_of_not_mem_symIcc hsupp hx)

/-- The `A`-level box-norm power of the shifted function is nonnegative. -/
lemma ANorm_nonneg (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a'' : Slot ι k → ℤ) (s₀ : Slot ι k) (Nw : ℕ) (a₀ : ℤ)
    (sh : ShiftTuple k kω p M₁ a a'' s₀) (f : ℤ → ℂ) :
    0 ≤ ANorm k kω p M₁ a a'' s₀ Nw a₀ sh f := by
  simp only [ANorm]
  exact norm_nonneg _

/-- The `A`-level box-norm power is at most the `A`-level box *norm* of a `1`-bounded, supported
shifted function (the root of a number in `[0,1]` is at least the number). -/
lemma ANorm_le_ABox (k : ι → ℕ) (kω : SlotSet ι k → ℕ) (p : ι → (Fin n → ℤ) → ℤ) (M₁ : ℕ)
    (a : Fin n → ℤ) (a'' : Slot ι k → ℤ) (s₀ : Slot ι k) (Nw : ℕ) (a₀ : ℤ)
    (sh : ShiftTuple k kω p M₁ a a'' s₀) (f : ℤ → ℂ)
    (hsupp : Work.Peluse.SupportIn (shiftId k kω p M₁ a a'' s₀ sh f) Nw)
    (hnorm : ∀ x : ℤ, ‖shiftId k kω p M₁ a a'' s₀ sh f x‖ ≤ 1) :
    ANorm k kω p M₁ a a'' s₀ Nw a₀ sh f ≤ ABox k kω p M₁ a a'' s₀ Nw a₀ sh f := by
  have hr : (1 / (2 : ℝ) ^ (Fintype.card (AIdx k kω s₀))) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact one_le_pow₀ (by norm_num)
  simpa only [ABox, ANorm, boxNorm] using
    le_rpow_of_le_one (ANorm_nonneg k kω p M₁ a a'' s₀ Nw a₀ sh f)
      (ANorm_le_one k kω p M₁ a a'' s₀ Nw a₀ sh f hsupp hnorm) hr

end

end Work.Peluse.LadderA
