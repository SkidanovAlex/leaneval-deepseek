import Mathlib
import Submission.Work.BW.est15defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- The triangle inequality for an infinite place applied to a finite sum: an infinite place is
an absolute value, so `w (∑ f i) ≤ ∑ w (f i)`. -/
lemma infplace_sum_le {K : Type*} [Field K] {ι : Type*}
    (w : NumberField.InfinitePlace K) (s : Finset ι) (f : ι → K) :
    w (∑ i ∈ s, f i) ≤ ∑ i ∈ s, w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (w.1.add_le (f a) (∑ i ∈ s, f i)).trans (add_le_add_right ih (w (f a)))

theorem est15_place_inf {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    {J : ℕ} {μ : Fin r → ℕ} {t0 : ℕ} {t : Fin (r - 1) → ℕ} {s : ℤ} {Bcoef : ℝ}
    (w : NumberField.InfinitePlace K)
    (hx : gKJ b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ t0 t s ≠ 0)
    (hcoef : ∀ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
      Real.log (w (coefKJ b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 t s lm))
        ≤ Bcoef) :
    Real.log (w (gKJ b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ t0 t s))
      ≤ Real.log (⨆ lm, w (p lm))
        + Real.log (Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℝ)
        + Bcoef := by
  classical
  -- there is at least one index `λ` with `λ ≡ μ (mod 2^J)`, otherwise `gKJ = 0`
  obtain ⟨lm0, -⟩ : ∃ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
      ∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j := by
    by_contra h
    refine hx ?_
    rw [gKJ]
    refine Finset.sum_eq_zero fun lm _ => ?_
    exact if_neg (fun hc => h ⟨lm, hc⟩)
  have hbdd : BddAbove (Set.range fun lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) =>
      w (p lm)) := Set.Finite.bddAbove (Set.finite_range _)
  have hMnn : 0 ≤ ⨆ lm, w (p lm) :=
    le_trans (AbsoluteValue.nonneg w.1 (p lm0)) (le_ciSup hbdd lm0)
  -- the supremum `M = ⨆ w (p λ)` is strictly positive, again by `hx`
  have hMpos : 0 < ⨆ lm, w (p lm) := by
    by_contra hcon
    rw [not_lt] at hcon
    have hM0 : (⨆ lm, w (p lm)) = 0 := le_antisymm hcon hMnn
    have hpz : ∀ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ), p lm = 0 := by
      intro lm
      refine (AbsoluteValue.eq_zero w.1).mp ?_
      exact le_antisymm (hM0 ▸ le_ciSup hbdd lm) (AbsoluteValue.nonneg w.1 (p lm))
    refine hx ?_
    rw [gKJ]
    refine Finset.sum_eq_zero fun lm _ => ?_
    by_cases hc : (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j)
    · rw [if_pos hc, hpz lm, zero_mul]
    · exact if_neg hc
  have hcard_pos : 0 < Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) :=
    Fintype.card_pos_iff.mpr ⟨lm0⟩
  -- each coefficient is bounded by `exp Bcoef`
  have hcoef_le : ∀ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
      w (coefKJ b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 t s lm)
        ≤ Real.exp Bcoef := by
    intro lm
    by_cases hz : w (coefKJ b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 t s lm) = 0
    · rw [hz]; exact le_of_lt (Real.exp_pos Bcoef)
    · refine (Real.log_le_iff_le_exp ?_).mp (hcoef lm)
      exact lt_of_le_of_ne (AbsoluteValue.nonneg w.1 _) (Ne.symm hz)
  -- `w (gKJ) ≤ ∑_λ w (p λ · coef λ)`
  have hstep : w (gKJ b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ t0 t s)
      ≤ ∑ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
          w (if (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j)
            then p lm * coefKJ b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 t s lm
            else 0) := by
    rw [gKJ]
    exact infplace_sum_le w Finset.univ _
  -- `w (gKJ) ≤ card · M · exp Bcoef`
  have hsum : w (gKJ b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) p J μ t0 t s)
      ≤ (Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℝ)
        * ((⨆ lm, w (p lm)) * Real.exp Bcoef) := by
    refine hstep.trans ?_
    calc ∑ lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
          w (if (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j)
            then p lm * coefKJ b k L ι α' (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) J t0 t s lm
            else 0)
        ≤ ∑ _lm : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ),
            ((⨆ lm, w (p lm)) * Real.exp Bcoef) := by
          refine Finset.sum_le_sum fun lm _ => ?_
          by_cases hc : (∀ j, (lm.2.2 j : ℕ) % 2 ^ J = μ j)
          · rw [if_pos hc, map_mul]
            exact mul_le_mul (le_ciSup hbdd lm) (hcoef_le lm)
              (AbsoluteValue.nonneg w.1 _) hMnn
          · rw [if_neg hc, map_zero]
            exact mul_nonneg hMnn (le_of_lt (Real.exp_pos Bcoef))
      _ = (Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℝ)
            * ((⨆ lm, w (p lm)) * Real.exp Bcoef) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine (Real.log_le_log (NumberField.InfinitePlace.pos_iff.mpr hx) hsum).trans_eq ?_
  have h1 : ((Fintype.card (AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ)) : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hcard_pos)
  have h2 : (⨆ lm, w (p lm)) ≠ 0 := ne_of_gt hMpos
  have h3 : Real.exp Bcoef ≠ 0 := Real.exp_ne_zero Bcoef
  rw [Real.log_mul h1 (mul_ne_zero h2 h3), Real.log_mul h2 h3, Real.log_exp]
  ring

end Work.BW
