import Mathlib
import Submission.Work.LinnikAreas.CorrAllR.Defs
import Submission.Commons.NumberTheory.DirichletCharacter.weil_local_bound
import Submission.Commons.Algebra.Polynomial.mult_modEq_of_const_mul_pow

open scoped BigOperators

namespace Work.LinnikAreas.CorrAllR

/-- The two halves `Fin.castAdd` and `Fin.natAdd` of `Fin (r + r)` are disjoint. -/
private lemma natAdd_ne_castAdd_fin {r : ℕ} (l i : Fin r) :
    (Fin.natAdd r l : Fin (r + r)) ≠ Fin.castAdd r i := by
  intro h
  have h2 : (Fin.natAdd r l : ℕ) = (Fin.castAdd r i : ℕ) := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at h2
  omega

/-- The two halves `Fin.castAdd` and `Fin.natAdd` of `Fin (r + r)` are disjoint. -/
private lemma castAdd_ne_natAdd_fin {r : ℕ} (l i : Fin r) :
    (Fin.castAdd r l : Fin (r + r)) ≠ Fin.natAdd r i := by
  intro h
  have h2 : (Fin.castAdd r l : ℕ) = (Fin.natAdd r i : ℕ) := congrArg Fin.val h
  simp only [Fin.val_natAdd, Fin.val_castAdd] at h2
  omega

/-- The local Weil bound in the "good" (non-degenerate) case, in its factor-wise form: if at some
residue the two multiplicity counts differ modulo `orderOf χ`, then the correlation of the two
products of `r` linear factors is at most `2r√p`. -/
private lemma corr_good_of_counts {p : ℕ} [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (hχ : χ ≠ 1) {r : ℕ} (hr : 1 ≤ r) (a b : Fin r → ZMod p)
    (hgood : ∃ x : ZMod p,
      (Finset.univ.filter (fun i : Fin r => a i = x)).card % orderOf χ
        ≠ (Finset.univ.filter (fun i : Fin r => b i = x)).card % orderOf χ) :
    ‖∑ x : ZMod p, (∏ i, χ (x + a i)) * (∏ i, (starRingEnd ℂ) (χ (x + b i)))‖
      ≤ (2 * r : ℝ) * Real.sqrt (p : ℝ) := by
  have hm2 : 2 ≤ orderOf χ := by
    have h1 : orderOf χ ≠ 1 := fun h => hχ (orderOf_eq_one_iff.mp h)
    have h2 : 1 ≤ orderOf χ := orderOf_pos χ
    omega
  refine Commons.NumberTheory.DirichletCharacter.weil_local_bound χ hχ r hr a b ?_
  intro c Q hcon
  obtain ⟨x, hx⟩ := hgood
  exact hx (Commons.Algebra.Polynomial.mult_modEq_of_const_mul_pow hm2 a b hcon x)

/-- Uniqueness of `v i` modulo `p` produces a residue `x` at which the two multiplicity counts
differ modulo `orderOf χ`. -/
private lemma counts_ne_of_isUniqModV (p : ℕ) [Fact p.Prime] (χ : DirichletCharacter ℂ p)
    (hχ : χ ≠ 1) {r : ℕ} (_hr : 0 < r) (v : Fin (r + r) → ℕ) (i : Fin (r + r))
    (huniq : IsUniqModV p v i) :
    ∃ x : ZMod p,
      (Finset.univ.filter (fun l : Fin r => (v (Fin.castAdd r l) : ZMod p) = x)).card
          % orderOf χ
        ≠ (Finset.univ.filter (fun l : Fin r => (v (Fin.natAdd r l) : ZMod p) = x)).card
          % orderOf χ := by
  have hm : 1 < orderOf χ := by
    have h1 : orderOf χ ≠ 1 := fun h => hχ (orderOf_eq_one_iff.mp h)
    have h2 : 1 ≤ orderOf χ := orderOf_pos χ
    omega
  have hmod : ∀ a b : ℕ, (a : ZMod p) = (b : ZMod p) → a % p = b % p :=
    fun a b h => (ZMod.natCast_eq_natCast_iff' a b p).mp h
  revert huniq
  refine Fin.addCases (m := r) (n := r) (motive := fun i : Fin (r + r) =>
    IsUniqModV p v i → ∃ x : ZMod p,
      (Finset.univ.filter (fun l : Fin r => (v (Fin.castAdd r l) : ZMod p) = x)).card
          % orderOf χ
        ≠ (Finset.univ.filter (fun l : Fin r => (v (Fin.natAdd r l) : ZMod p) = x)).card
          % orderOf χ) ?_ ?_ i
  · intro i' huniq
    refine ⟨(v (Fin.castAdd r i') : ZMod p), ?_⟩
    have ha : (Finset.univ.filter (fun l : Fin r =>
        (v (Fin.castAdd r l) : ZMod p) = (v (Fin.castAdd r i') : ZMod p))).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨i', ?_⟩
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hl
        by_contra hne
        exact huniq (Fin.castAdd r l) (by simpa using hne) (hmod _ _ hl)
      · intro hl
        rw [hl]
    have hb : (Finset.univ.filter (fun l : Fin r =>
        (v (Fin.natAdd r l) : ZMod p) = (v (Fin.castAdd r i') : ZMod p))).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro l hl
      have hle : (v (Fin.natAdd r l) : ZMod p) = (v (Fin.castAdd r i') : ZMod p) := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hl
      exact huniq (Fin.natAdd r l) (natAdd_ne_castAdd_fin l i') (hmod _ _ hle)
    rw [ha, hb]
    simp [Nat.mod_eq_of_lt hm]
  · intro i' huniq
    refine ⟨(v (Fin.natAdd r i') : ZMod p), ?_⟩
    have hb : (Finset.univ.filter (fun l : Fin r =>
        (v (Fin.natAdd r l) : ZMod p) = (v (Fin.natAdd r i') : ZMod p))).card = 1 := by
      rw [Finset.card_eq_one]
      refine ⟨i', ?_⟩
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · intro hl
        by_contra hne
        exact huniq (Fin.natAdd r l) (by simpa using hne) (hmod _ _ hl)
      · intro hl
        rw [hl]
    have ha : (Finset.univ.filter (fun l : Fin r =>
        (v (Fin.castAdd r l) : ZMod p) = (v (Fin.natAdd r i') : ZMod p))).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro l hl
      have hle : (v (Fin.castAdd r l) : ZMod p) = (v (Fin.natAdd r i') : ZMod p) := by
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hl
      exact huniq (Fin.castAdd r l) (castAdd_ne_natAdd_fin l i') (hmod _ _ hle)
    rw [ha, hb]
    simp [Nat.mod_eq_of_lt hm]

/-- **Local prime-modulus correlation bound (general `r`).**

For a non-trivial `χ` mod a prime `p`, a `2r`-tuple of shifts `v` and an index `i` whose value is
unique modulo `p`, the correlation sum is at most `2r √p`.  Route: rewrite the summand as
`χ ((A * B^(orderOf χ - 1)).eval x)` (`chi_mul_conj_eq_q`), check that uniqueness of `v i` mod `p`
forces that polynomial NOT to be a constant multiple of an `orderOf χ`-th power (contrapositive of
`Commons.Algebra.Polynomial.mult_modEq_of_const_mul_pow`), and apply
`Commons.NumberTheory.DirichletCharacter.weil_local_bound`.  The definitions `corrSumV` and
`IsUniqModV` come from `Submission.Work.LinnikAreas.CorrAllR.Defs`, which you should import. -/
theorem corrSumV_prime_good (p : ℕ) [Fact p.Prime] [NeZero p] (χ : DirichletCharacter ℂ p)
    (hχ : χ ≠ 1) {r : ℕ} (hr : 0 < r) (v : Fin (r + r) → ℕ) (i : Fin (r + r))
    (huniq : Work.LinnikAreas.IsUniqModV p v i) :
    ‖Work.LinnikAreas.corrSumV p χ r v‖ ≤ (2 * r : ℝ) * Real.sqrt (p : ℝ) := by
  have hr1 : 1 ≤ r := hr
  have hgood := counts_ne_of_isUniqModV p χ hχ hr v i huniq
  have hsum : Work.LinnikAreas.corrSumV p χ r v
      = ∑ x : ZMod p,
          (∏ l : Fin r, χ (x + (v (Fin.castAdd r l) : ZMod p)))
            * (∏ l : Fin r, (starRingEnd ℂ) (χ (x + (v (Fin.natAdd r l) : ZMod p)))) := by
    rw [Work.LinnikAreas.corrSumV]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [map_prod χ (fun l : Fin r => x + (v (Fin.castAdd r l) : ZMod p)) Finset.univ,
      map_prod χ (fun l : Fin r => x + (v (Fin.natAdd r l) : ZMod p)) Finset.univ,
      map_prod (starRingEnd ℂ)
        (fun l : Fin r => χ (x + (v (Fin.natAdd r l) : ZMod p))) Finset.univ]
  rw [hsum]
  exact corr_good_of_counts χ hχ hr1 _ _ hgood

end Work.LinnikAreas.CorrAllR
