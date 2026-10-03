import Mathlib
import Submission.Work.Peluse.TransferUp.RawPowDefs
import Submission.Work.Peluse.Concat.boxNormPow_succ_peel_gen
import Submission.Work.Peluse.BoxNormDilation.boxNormPow_two_eq
import Submission.Work.Peluse.Concat.pair_sum_mono_mixed

/-!
# Monotonicity of the level-two raw box quantity in the direction sets

The *raw* box quantity of order `t` is Peluse's `2^t`-th box-norm power with the normalising
factor `∏_i |Q i|²` removed (`Work.Peluse.TransferUp.rawPow`).  The point of the normalisation is
that, for `t ≥ 2`, `rawPow t` is monotone in each of the direction sets `Q i`.  This file proves
the case `t = 2`, which is the case used by the "transfer up" comparison of
`Submission/Work/Peluse/TransferUp/`.

## The mathematics

Peeling the first coordinate of the box sum (`Work.Peluse.Concat.boxNormPow_succ_peel_gen`) and
evaluating the resulting level-one box-norm power as a sum of squares
(`Work.Peluse.Peel.boxNormPow_one_tsum`) gives the level-two identity

`rawPow 2 Q S f = |S|⁻¹ ∑_{h,h' ∈ Q 0} ∑_x ‖∑_{k ∈ Q 1} f (x+h+k)·conj (f (x+h'+k))‖²`,

i.e. `rawPow 2 Q S f = |S|⁻¹ · P (Q 0) (Q 1) f` where

`P A B f = ∑_{a,b ∈ A} ∑_x ‖∑_{k ∈ B} f (x+a+k)·conj (f (x+b+k))‖²`.

The monotonicity of `P` in *both* arguments simultaneously is
`Work.Peluse.Concat.pair_sum_mono_mixed` (the two expansions of the square
`‖∑_k g_k‖² = ∑_{k,l} g_k conj(g_l)` and `‖∑_a h_a‖² = ∑_{a,b} h_a conj(h_b)` give the *same*
fourfold sum `∑_{a,b,k,l,x} T`, and `T` is invariant under the interchange of the pairs
`(a,b) ↔ (k,l)`).  Since `|S|⁻¹ ≥ 0`, the target follows at once.

## Main results

* `Work.Peluse.TransferUp.boxNormPow_two_eq_general` : the level-two box-norm power on two *distinct*
  direction sets, as the normalised pair sum;
* `Work.Peluse.TransferUp.rawPow_two_eq` : the level-two raw box quantity as the pair sum;
* `Work.Peluse.TransferUp.rawPow_mono_two` : its monotonicity in the direction sets.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.TransferUp

noncomputable section

/-! ## The support of the difference `Δ'_{h,h'} f` -/

/-- A product of `f` with the conjugate of a translate of `f` is supported in
`[-N - |h| - |h'|, N + |h| + |h'|]` whenever `f` is supported in `[-N,N]`. -/
private lemma supportIn_deltaP {f : ℤ → ℂ} {N : ℕ} (hN : Work.Peluse.SupportIn f N) (h h' : ℤ) :
    Work.Peluse.SupportIn (fun u : ℤ => f (u + h) * star (f (u + h')))
      (N + h.natAbs + h'.natAbs) := by
  intro u hu
  have h1 : N < (u + h).natAbs := by
    have htri : u.natAbs ≤ (u + h).natAbs + h.natAbs := by
      have hle := Int.natAbs_add_le (u + h) (-h)
      rw [show u + h + -h = u by ring, Int.natAbs_neg] at hle
      exact hle
    omega
  have h2 : N < (u + h').natAbs := by
    have htri : u.natAbs ≤ (u + h').natAbs + h'.natAbs := by
      have hle := Int.natAbs_add_le (u + h') (-h')
      rw [show u + h' + -h' = u by ring, Int.natAbs_neg] at hle
      exact hle
    omega
  show f (u + h) * star (f (u + h')) = 0
  rw [hN (u + h) h1, hN (u + h') h2, star_zero, mul_zero]

/-! ## The level-two box-norm power on two direction sets -/

/-- Pulling a constant out of a doubly indexed sum.  (Stated in this direction so that the
rewrite `Finset.mul_sum` matches syntactically.) -/
private lemma sum2_const_mul (s : Finset ℤ) (F : ℤ → ℤ → ℝ) (c : ℝ) :
    (∑ i ∈ s, ∑ j ∈ s, c * F i j) = c * ∑ i ∈ s, ∑ j ∈ s, F i j := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]

/-- **The level-two box-norm power on two distinct direction sets.**  For a finitely supported `f`,

`‖f‖^{4}_{□²_{Q₀,Q₁}(S)}
   = |S|⁻¹ |Q₀|⁻² |Q₁|⁻² ∑_{h,h' ∈ Q₀} ∑_x ‖∑_{k ∈ Q₁} f (x+h+k)·conj (f (x+h'+k))‖²`.

This is the peel of the first coordinate (`boxNormPow_succ_peel_gen`) combined with the evaluation
of each level-one box-norm power as a sum of squares (`boxNormPow_one_tsum`). -/
theorem boxNormPow_two_eq_general (Q : Fin 2 → Finset ℤ) (S : Finset ℤ) {f : ℤ → ℂ}
    (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.boxNormPow 2 Q S f
      = (((S.card : ℝ))⁻¹ * (((Q 0).card : ℝ))⁻¹ ^ 2 * (((Q 1).card : ℝ))⁻¹ ^ 2) *
        ∑ h ∈ Q 0, ∑ h' ∈ Q 0, ∑' x : ℤ,
          ‖∑ k ∈ Q 1, f (x + h + k) * star (f (x + h' + k))‖ ^ 2 := by
  obtain ⟨N, hN⟩ := hf
  have hQ1 : (fun i : Fin 1 => Q i.succ) = (fun _ : Fin 1 => Q 1) := by
    funext i
    fin_cases i
    rfl
  have hstep : ∀ h ∈ Q 0, ∀ h' ∈ Q 0,
      Work.Peluse.boxNormPow 1 (fun i : Fin 1 => Q i.succ) S
          (fun u : ℤ => f (u + h) * star (f (u + h')))
        = (((S.card : ℝ))⁻¹ * (((Q 1).card : ℝ))⁻¹ ^ 2) *
          ∑' x : ℤ, ‖∑ k ∈ Q 1, f (x + h + k) * star (f (x + h' + k))‖ ^ 2 := by
    intro h _ h' _
    rw [hQ1, Work.Peluse.Peel.boxNormPow_one_tsum (Q 1) S (supportIn_deltaP hN h h')]
    have hcongr : (∑' x : ℤ, ‖∑ a ∈ Q 1, f ((x + a) + h) * star (f ((x + a) + h'))‖ ^ 2)
        = ∑' x : ℤ, ‖∑ k ∈ Q 1, f (x + h + k) * star (f (x + h' + k))‖ ^ 2 := by
      refine tsum_congr (fun x => ?_)
      rw [Finset.sum_congr rfl (fun k _ => by
        rw [show (x + k) + h = x + h + k by ring,
          show (x + k) + h' = x + h' + k by ring])]
    rw [hcongr]
  rw [Work.Peluse.Concat.boxNormPow_succ_peel_gen (t := 1) (f := f) le_rfl Q S
    (⟨N, hN⟩ : Work.Peluse.FinSuppZ f)]
  rw [Finset.sum_congr rfl (fun h hh => Finset.sum_congr rfl (fun h' hh' => hstep h hh h' hh'))]
  have hpull : (∑ h ∈ Q 0, ∑ h' ∈ Q 0, (((S.card : ℝ))⁻¹ * (((Q 1).card : ℝ))⁻¹ ^ 2) *
        ∑' x : ℤ, ‖∑ k ∈ Q 1, f (x + h + k) * star (f (x + h' + k))‖ ^ 2)
      = (((S.card : ℝ))⁻¹ * (((Q 1).card : ℝ))⁻¹ ^ 2) *
        ∑ h ∈ Q 0, ∑ h' ∈ Q 0, ∑' x : ℤ,
          ‖∑ k ∈ Q 1, f (x + h + k) * star (f (x + h' + k))‖ ^ 2 :=
    sum2_const_mul (Q 0)
      (fun h h' => ∑' x : ℤ, ‖∑ k ∈ Q 1, f (x + h + k) * star (f (x + h' + k))‖ ^ 2) _
  rw [hpull]
  ring

/-! ## The level-two raw box quantity as a pair sum -/

/-- The **pair sum** `P A B f = ∑_{a,b ∈ A} ∑_x ‖∑_{k ∈ B} f (x+a+k)·conj (f (x+b+k))‖²`,
the unnormalised form of the level-two raw box quantity. -/
def pairSum (A B : Finset ℤ) (f : ℤ → ℂ) : ℝ :=
  ∑ a ∈ A, ∑ b ∈ A, ∑' x : ℤ, ‖∑ k ∈ B, f (x + a + k) * star (f (x + b + k))‖ ^ 2

lemma pairSum_nonneg (A B : Finset ℤ) (f : ℤ → ℂ) : 0 ≤ pairSum A B f := by
  rw [pairSum]
  refine Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => ?_))
  exact tsum_nonneg (fun x => by positivity)

/-- **The level-two raw box quantity as a pair sum.**

`rawPow 2 Q S f = |S|⁻¹ · P (Q 0) (Q 1) f` — the `∏_i |Q i|²` of the definition cancels the
`∏_i |Q i|⁻²` of the box-norm power. -/
theorem rawPow_two_eq (Q : Fin 2 → Finset ℤ) (S : Finset ℤ) {f : ℤ → ℂ}
    (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.TransferUp.rawPow 2 Q S f = ((S.card : ℝ))⁻¹ * pairSum (Q 0) (Q 1) f := by
  have hbox := boxNormPow_two_eq_general Q S hf
  show (∏ i : Fin 2, ((Q i).card : ℝ) ^ 2) * Work.Peluse.boxNormPow 2 Q S f
      = ((S.card : ℝ))⁻¹ * pairSum (Q 0) (Q 1) f
  rw [Fin.prod_univ_two, hbox]
  rw [pairSum]
  by_cases ha : ((Q 0).card : ℝ) = 0
  · have hQ0 : Q 0 = ∅ := Finset.card_eq_zero.mp (Nat.cast_eq_zero.mp ha)
    rw [ha, hQ0]
    simp
  · by_cases hb : ((Q 1).card : ℝ) = 0
    · have hQ1 : Q 1 = ∅ := Finset.card_eq_zero.mp (Nat.cast_eq_zero.mp hb)
      rw [hb, hQ1]
      simp
    · rw [inv_pow, inv_pow]
      have h1 : ((Q 0).card : ℝ) ^ 2 * (((Q 0).card : ℝ) ^ 2)⁻¹ = 1 :=
        mul_inv_cancel₀ (pow_ne_zero 2 ha)
      have h2 : ((Q 1).card : ℝ) ^ 2 * (((Q 1).card : ℝ) ^ 2)⁻¹ = 1 :=
        mul_inv_cancel₀ (pow_ne_zero 2 hb)
      calc ((Q 0).card : ℝ) ^ 2 * ((Q 1).card : ℝ) ^ 2 *
              ((((S.card : ℝ))⁻¹ * (((Q 0).card : ℝ) ^ 2)⁻¹ * (((Q 1).card : ℝ) ^ 2)⁻¹) *
                ∑ h ∈ Q 0, ∑ h' ∈ Q 0, ∑' x : ℤ,
                  ‖∑ k ∈ Q 1, f (x + h + k) * star (f (x + h' + k))‖ ^ 2)
          = ((S.card : ℝ))⁻¹ *
              ((((Q 0).card : ℝ) ^ 2 * (((Q 0).card : ℝ) ^ 2)⁻¹) *
                (((Q 1).card : ℝ) ^ 2 * (((Q 1).card : ℝ) ^ 2)⁻¹)) *
              (∑ h ∈ Q 0, ∑ h' ∈ Q 0, ∑' x : ℤ,
                ‖∑ k ∈ Q 1, f (x + h + k) * star (f (x + h' + k))‖ ^ 2) := by ring
        _ = ((S.card : ℝ))⁻¹ *
              (∑ h ∈ Q 0, ∑ h' ∈ Q 0, ∑' x : ℤ,
                ‖∑ k ∈ Q 1, f (x + h + k) * star (f (x + h' + k))‖ ^ 2) := by
            rw [h1, h2]
            ring

/-! ## The target -/

theorem rawPow_mono_two {Q Q' : Fin 2 → Finset ℤ} (S : Finset ℤ) {f : ℤ → ℂ} (hf : Work.Peluse.FinSuppZ f) (h : ∀ i, Q i ⊆ Q' i) : Work.Peluse.TransferUp.rawPow 2 Q S f ≤ Work.Peluse.TransferUp.rawPow 2 Q' S f := by
  rw [rawPow_two_eq Q S hf, rawPow_two_eq Q' S hf]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact Work.Peluse.Concat.pair_sum_mono_mixed (h 0) (h 1) hf

end

end Work.Peluse.TransferUp
