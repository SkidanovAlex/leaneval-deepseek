import Mathlib
import Submission.Work.FIArea7.WUniOmega6Pull6CharLow_aux
import Submission.Work.FIArea7.norm_ratWeight_charSum_le

namespace Work.FIArea7

open Finset
open scoped BigOperators

/-- **Plancherel / Parseval for finite abelian groups.**  For a function `f` on a finite abelian
group `A`, the squared `L²`-norm of the Fourier transform `f̂ ψ = Σ_a f a · ψ a` over the character
group equals `|A|` times the squared `L²`-norm of `f`.  This is the general identity underlying the
finite-group orthogonality `Σ_a ψ₁ a · conj (ψ₂ a) = |A| · [ψ₁ = ψ₂]`. -/
lemma plancherel_finite_abelian {A : Type*} [AddCommGroup A] [Fintype A] [DecidableEq A]
    (f : A → ℂ) :
    ∑ ψ : AddChar A ℂ, ‖∑ a, f a * ψ a‖ ^ 2
      = (Fintype.card A : ℝ) * ∑ a, ‖f a‖ ^ 2 := by
  have hchar : ∀ a b : A, (∑ ψ : AddChar A ℂ, ψ a * (starRingEnd ℂ) (ψ b))
      = if a = b then (Fintype.card A : ℂ) else 0 := by
    intro a b
    have key : ∀ ψ : AddChar A ℂ, ψ a * (starRingEnd ℂ) (ψ b) = ψ (a - b) := by
      intro ψ
      rw [← AddChar.map_neg_eq_conj, ← AddChar.map_add_eq_mul, sub_eq_add_neg]
    calc ∑ ψ : AddChar A ℂ, ψ a * (starRingEnd ℂ) (ψ b)
        = ∑ ψ : AddChar A ℂ, ψ (a - b) := Finset.sum_congr rfl fun ψ _ => key ψ
      _ = if a - b = 0 then (Fintype.card A : ℂ) else 0 := AddChar.sum_apply_eq_ite (a - b)
      _ = if a = b then (Fintype.card A : ℂ) else 0 := by simp only [sub_eq_zero]
  have hmain : ∑ ψ : AddChar A ℂ, (∑ a, f a * ψ a) * (starRingEnd ℂ) (∑ a, f a * ψ a)
      = (Fintype.card A : ℂ) * ∑ a, f a * (starRingEnd ℂ) (f a) := by
    have hc : ∀ ψ : AddChar A ℂ, (starRingEnd ℂ) (∑ a, f a * ψ a)
        = ∑ b, (starRingEnd ℂ) (f b) * ψ (-b) := by
      intro ψ
      rw [map_sum]
      exact Finset.sum_congr rfl fun b _ => by rw [map_mul, AddChar.map_neg_eq_conj]
    calc ∑ ψ : AddChar A ℂ, (∑ a, f a * ψ a) * (starRingEnd ℂ) (∑ a, f a * ψ a)
        = ∑ ψ : AddChar A ℂ, (∑ a, f a * ψ a) * (∑ b, (starRingEnd ℂ) (f b) * ψ (-b)) :=
            Finset.sum_congr rfl fun ψ _ => by rw [hc ψ]
      _ = ∑ ψ : AddChar A ℂ, ∑ a, ∑ b, (f a * ψ a) * ((starRingEnd ℂ) (f b) * ψ (-b)) := by
            refine Finset.sum_congr rfl fun ψ _ => ?_
            rw [Finset.sum_mul_sum]
      _ = ∑ a, ∑ b, ∑ ψ : AddChar A ℂ, (f a * ψ a) * ((starRingEnd ℂ) (f b) * ψ (-b)) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun a _ => by rw [Finset.sum_comm]
      _ = ∑ a, ∑ b, (f a * (starRingEnd ℂ) (f b)) * (∑ ψ : AddChar A ℂ, ψ (a - b)) := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            have hsum : ∀ ψ : AddChar A ℂ, (f a * ψ a) * ((starRingEnd ℂ) (f b) * ψ (-b))
                = (f a * (starRingEnd ℂ) (f b)) * ψ (a - b) := by
              intro ψ
              rw [show (f a * ψ a) * ((starRingEnd ℂ) (f b) * ψ (-b))
                    = (f a * (starRingEnd ℂ) (f b)) * (ψ a * ψ (-b)) by ring]
              rw [← AddChar.map_add_eq_mul, sub_eq_add_neg]
            rw [Finset.sum_congr rfl (fun ψ _ => hsum ψ), Finset.mul_sum]
      _ = ∑ a, ∑ b, (f a * (starRingEnd ℂ) (f b))
            * (if a = b then (Fintype.card A : ℂ) else 0) := by
            refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
            rw [AddChar.sum_apply_eq_ite]
            simp only [sub_eq_zero]
      _ = (Fintype.card A : ℂ) * ∑ a, f a * (starRingEnd ℂ) (f a) := by
            have hinner : ∀ a : A,
                (∑ b, (f a * (starRingEnd ℂ) (f b)) * (if a = b then (Fintype.card A : ℂ) else 0))
                = (f a * (starRingEnd ℂ) (f a)) * (Fintype.card A : ℂ) := by
              intro a
              rw [show (∑ b, (f a * (starRingEnd ℂ) (f b))
                      * (if a = b then (Fintype.card A : ℂ) else 0))
                    = ∑ b, (if a = b then (f a * (starRingEnd ℂ) (f b))
                        * (Fintype.card A : ℂ) else 0) by
                refine Finset.sum_congr rfl fun b _ => ?_
                by_cases h : a = b <;> simp [h]]
              rw [Finset.sum_ite_eq]
              simp
            rw [Finset.sum_congr rfl (fun a _ => hinner a), ← Finset.sum_mul, mul_comm]
  have h1 : ∀ ψ : AddChar A ℂ, ((‖∑ a, f a * ψ a‖ ^ 2 : ℝ) : ℂ)
      = (∑ a, f a * ψ a) * (starRingEnd ℂ) (∑ a, f a * ψ a) := by
    intro ψ
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  have h2 : ∀ a : A, ((‖f a‖ ^ 2 : ℝ) : ℂ) = f a * (starRingEnd ℂ) (f a) := by
    intro a
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
  have hcomplex : ((∑ ψ : AddChar A ℂ, ‖∑ a, f a * ψ a‖ ^ 2 : ℝ) : ℂ)
      = ((Fintype.card A : ℝ) * ∑ a, ‖f a‖ ^ 2 : ℝ) := by
    rw [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast, Complex.ofReal_sum]
    rw [Finset.sum_congr rfl (fun ψ _ => h1 ψ), hmain]
    rw [Finset.sum_congr rfl (fun a _ => h2 a)]
  exact_mod_cast hcomplex

/-- The `L²`-mass of `ratWeight Q e` is at most `Q`: the weight has modulus `≤ 1` and is supported
on the rational classes `(r, 0)`, of which there are at most `Q`. -/
lemma sum_normSq_ratWeight_le (Q e : ℕ) [NeZero Q] :
    ∑ a : Additive (GaussUnit Q), ‖ratWeight Q e (Additive.toMul a)‖ ^ 2 ≤ (Q : ℝ) := by
  classical
  have hmassG : ∑ p : GaussUnit Q, ‖ratWeight Q e p‖ ^ 2 ≤ (Q : ℝ) := by
    set s : Finset (GaussUnit Q) := Finset.univ.filter (fun p => p.1.2 = 0) with hs
    have hsubset : s ⊆ Finset.univ := Finset.subset_univ s
    have hsum : ∑ p : GaussUnit Q, ‖ratWeight Q e p‖ ^ 2 = ∑ p ∈ s, ‖ratWeight Q e p‖ ^ 2 := by
      rw [← Finset.sum_subset hsubset]
      intro p _ hp
      have h2 : p.1.2 ≠ 0 := by
        intro hh; exact hp (by rw [hs]; exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
      rw [ratWeight, if_neg h2, norm_zero]
      norm_num
    have hb : ∑ p ∈ s, ‖ratWeight Q e p‖ ^ 2 ≤ ∑ p ∈ s, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p _
      nlinarith [norm_ratWeight_le_one Q e p, norm_nonneg (ratWeight Q e p)]
    have hcard : s.card ≤ Q := by rw [hs]; exact card_ratWeight_support_le Q
    calc ∑ p : GaussUnit Q, ‖ratWeight Q e p‖ ^ 2 = ∑ p ∈ s, ‖ratWeight Q e p‖ ^ 2 := hsum
      _ ≤ ∑ p ∈ s, (1 : ℝ) := hb
      _ = (s.card : ℝ) := by simp
      _ ≤ (Q : ℝ) := by exact_mod_cast hcard
  have h : ∑ p : GaussUnit Q, ‖ratWeight Q e p‖ ^ 2
      = ∑ a : Additive (GaussUnit Q), ‖ratWeight Q e (Additive.toMul a)‖ ^ 2 :=
    Fintype.sum_equiv Additive.ofMul _ _ (fun p => rfl)
  rw [← h]
  exact hmassG

/-- **Plancherel for the §17 omega-weights.** `uniJChar Q e χ = Σ_{p : G} ratWeight Q e p · χ(p)` is
the Fourier transform of `ratWeight Q e` on the unit group `G = (ℤ[i]/Q)^*`, so
`Σ_χ ‖J(χ)‖² = |G| · Σ_p ‖ratWeight Q e p‖² ≤ |G| · Q` (`‖ratWeight‖ ≤ 1` and at most `Q` rational
classes).  This is the `L²` companion of the `L¹` bound `sum_norm_uniJChar_le`. -/
theorem sumChiNormUniJCharSq (Q e : ℕ) [NeZero Q] :
    ∑ χ : AddChar (Additive (Work.FIArea7.GaussUnit Q)) ℂ,
        ‖Work.FIArea7.uniJChar Q e χ‖ ^ 2
      ≤ (Fintype.card (Work.FIArea7.GaussUnit Q) : ℝ) * (Q : ℝ) := by
  have huni : ∀ χ : AddChar (Additive (GaussUnit Q)) ℂ,
      uniJChar Q e χ = ∑ a : Additive (GaussUnit Q), ratWeight Q e (Additive.toMul a) * χ a := by
    intro χ
    rw [uniJChar]
    exact Fintype.sum_equiv Additive.ofMul
      (fun p => ratWeight Q e p * χ (Additive.ofMul p))
      (fun a => ratWeight Q e (Additive.toMul a) * χ a) (fun p => rfl)
  have hpl := plancherel_finite_abelian (A := Additive (GaussUnit Q))
      (fun a => ratWeight Q e (Additive.toMul a))
  calc ∑ χ : AddChar (Additive (GaussUnit Q)) ℂ, ‖uniJChar Q e χ‖ ^ 2
      = ∑ χ : AddChar (Additive (GaussUnit Q)) ℂ,
          ‖∑ a : Additive (GaussUnit Q), ratWeight Q e (Additive.toMul a) * χ a‖ ^ 2 := by
        refine Finset.sum_congr rfl (fun χ _ => ?_)
        rw [huni χ]
    _ = (Fintype.card (Additive (GaussUnit Q)) : ℝ)
          * ∑ a : Additive (GaussUnit Q), ‖ratWeight Q e (Additive.toMul a)‖ ^ 2 := hpl
    _ = (Fintype.card (GaussUnit Q) : ℝ)
          * ∑ a : Additive (GaussUnit Q), ‖ratWeight Q e (Additive.toMul a)‖ ^ 2 := by
        rw [Fintype.card_congr Additive.toMul]
    _ ≤ (Fintype.card (GaussUnit Q) : ℝ) * (Q : ℝ) :=
        mul_le_mul_of_nonneg_left (sum_normSq_ratWeight_le Q e) (Nat.cast_nonneg _)

end Work.FIArea7
