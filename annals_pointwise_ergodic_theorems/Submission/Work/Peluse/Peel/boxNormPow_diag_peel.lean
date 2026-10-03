import Mathlib
import Submission.Work.Peluse.Peel.boxSumPow_peel
import Submission.Work.Peluse.BoxNorm.boxNormPow_shift
import Submission.Work.Peluse.Peel.boxNormPow_one_tsum
import Submission.Work.Peluse.Track.boxSumPow_comp_bij_proved

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Work.Peluse.Peel

noncomputable section

open Work.Peluse

/-! ## Auxiliary notions -/

/-- `pmod g k` is the `k`-th power of the modulus of `g`, as a complex-valued function. -/
def pmod (g : ℤ → ℂ) (k : ℕ) : ℤ → ℂ := fun u => (((‖g u‖ ^ k : ℝ)) : ℂ)

lemma pmod_pmod (g : ℤ → ℂ) (k : ℕ) : pmod (pmod g 2) k = pmod g (2 * k) := by
  funext u
  simp only [pmod]
  have h1 : ‖(((‖g u‖ ^ 2 : ℝ)) : ℂ)‖ = ‖g u‖ ^ 2 :=
    Work.Peluse.BoxNorm.norm_ofReal_of_nonneg (sq_nonneg _)
  rw [h1, ← pow_mul]

lemma finSuppZ_pmod {g : ℤ → ℂ} (k : ℕ) (hk : k ≠ 0) (hg : Work.Peluse.FinSuppZ g) :
    Work.Peluse.FinSuppZ (pmod g k) := by
  obtain ⟨N, hN⟩ := hg
  refine ⟨N, fun u hu => ?_⟩
  change (((‖g u‖ ^ k : ℝ)) : ℂ) = 0
  rw [hN u hu, norm_zero, zero_pow hk]
  simp

lemma finSuppZ_mul_star_self (f : ℤ → ℂ) (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.FinSuppZ (fun u : ℤ => f u * star (f u)) := by
  obtain ⟨N, hN⟩ := hf
  refine ⟨N, fun u hu => ?_⟩
  change f u * star (f u) = 0
  rw [hN u hu, zero_mul]

lemma finSuppZ_mul_star_shift (f : ℤ → ℂ) (hf : Work.Peluse.FinSuppZ f) (h h' : ℤ) :
    Work.Peluse.FinSuppZ (fun u : ℤ => f (u + h) * star (f (u + h'))) := by
  obtain ⟨N, hN⟩ := hf
  refine ⟨max (N + h.natAbs) (N + h'.natAbs), fun u hu => ?_⟩
  change f (u + h) * star (f (u + h')) = 0
  have h1 : f (u + h) = 0 := by
    apply hN
    have hle : u.natAbs ≤ (u + h).natAbs + h.natAbs := by
      have := Int.natAbs_add_le (u + h) (-h)
      simpa using this
    have h2 : N + h.natAbs < u.natAbs := lt_of_le_of_lt (le_max_left _ _) hu
    omega
  rw [h1, zero_mul]

/-- Splitting off the first factor of a product of reciprocal cardinalities. -/
lemma prod_castSucc_eq {j : ℕ} (R : Fin (j+2) → Finset ℤ) :
    (∏ i : Fin (j+1), (((R i.castSucc).card : ℝ))⁻¹)
      = ((R 0).card : ℝ)⁻¹ * ∏ i : Fin j, (((R i.castSucc.succ).card : ℝ))⁻¹ := by
  rw [Fin.prod_univ_succ]
  have h0 : (Fin.castSucc (0 : Fin (j+1)) : Fin (j+2)) = 0 := by ext; simp
  rw [h0, Finset.prod_congr rfl (fun i _ => by rw [Fin.castSucc_succ i])]

/-- The cyclic shift maps the `i`-th element of `Fin n` (embedded in `Fin (n+1)`) to its
successor. -/
lemma finRotate_castSucc (n : ℕ) (i : Fin n) :
    finRotate (n+1) (Fin.castSucc i) = Fin.succ i := by
  have h := finRotate_of_lt (n := n) i.isLt
  rwa [show (⟨↑i, i.isLt.trans_le n.le_succ⟩ : Fin (n+1)) = Fin.castSucc i from rfl] at h

/-- **Permutation invariance of the box-norm power.** -/
theorem boxNormPow_comp_bij {t : ℕ} (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ)
    (σ : Fin t → Fin t) (hσ : Function.Bijective σ) :
    boxNormPow t (fun i => Q (σ i)) S f = boxNormPow t Q S f := by
  rw [boxNormPow, boxNormPow, Work.Peluse.Track.boxSumPow_comp_bij_proved Q S f σ hσ]

/-! ## The diagonal of the peel identity -/

/-- **The diagonal of the peel identity.**  Keeping only the pairs `h = h'` in the peel identity
gives a lower bound for the `2^{k+1}`-th power of the box norm of `f` in terms of the `2^k`-th
power of the box norm of `‖f‖²`. -/
theorem boxNormPow_diag_step {k : ℕ} (hk : 1 ≤ k) (Q : Fin (k+1) → Finset ℤ) (S : Finset ℤ)
    (f : ℤ → ℂ) (hfs : Work.Peluse.FinSuppZ f) (hQ : (Q 0).Nonempty) :
    ((Q 0).card : ℝ)⁻¹ *
        boxNormPow k (fun i : Fin k => Q i.succ) S (pmod f 2)
      ≤ boxNormPow (k+1) Q S f := by
  classical
  have hsq : ∀ u : ℤ, f u * star (f u) = pmod f 2 u := by
    intro u
    simp only [pmod]
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hterm : ∀ h ∈ Q 0, ∀ h' ∈ Q 0,
      boxSumPow k (fun i : Fin k => Q i.succ) S (fun u : ℤ => f (u + h) * star (f (u + h')))
        = ((boxNormPow k (fun i : Fin k => Q i.succ) S
            (fun u : ℤ => f (u + h) * star (f (u + h'))) : ℝ) : ℂ) :=
    fun h _ h' _ => Work.Peluse.BoxNorm.boxSumPow_eq_boxNormPow hk
      (finSuppZ_mul_star_shift f hfs h h')
  have hnn2 : (0 : ℝ) ≤ ((Q 0).card : ℝ)⁻¹ * ((Q 0).card : ℝ)⁻¹ *
      ∑ h ∈ Q 0, ∑ h' ∈ Q 0, boxNormPow k (fun i : Fin k => Q i.succ) S
        (fun u : ℤ => f (u + h) * star (f (u + h'))) :=
    mul_nonneg (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (inv_nonneg.mpr (Nat.cast_nonneg _)))
      (Finset.sum_nonneg (fun h _ => Finset.sum_nonneg (fun h' _ => norm_nonneg _)))
  have hreal : boxNormPow (k+1) Q S f
      = ((Q 0).card : ℝ)⁻¹ * ((Q 0).card : ℝ)⁻¹ *
        ∑ h ∈ Q 0, ∑ h' ∈ Q 0, boxNormPow k (fun i : Fin k => Q i.succ) S
          (fun u : ℤ => f (u + h) * star (f (u + h'))) := by
    have hC : boxSumPow (k+1) Q S f = (((Q 0).card : ℝ)⁻¹ * ((Q 0).card : ℝ)⁻¹ *
        ∑ h ∈ Q 0, ∑ h' ∈ Q 0, boxNormPow k (fun i : Fin k => Q i.succ) S
          (fun u : ℤ => f (u + h) * star (f (u + h'))) : ℝ) := by
      rw [boxSumPow_peel]
      rw [Finset.sum_congr rfl (fun h hh => Finset.sum_congr rfl (fun h' hh' => hterm h hh h' hh'))]
      push_cast
      ring
    show ‖boxSumPow (k+1) Q S f‖ = _
    rw [hC, Work.Peluse.BoxNorm.norm_ofReal_of_nonneg hnn2]
  have hdiag : ∀ h ∈ Q 0,
      boxNormPow k (fun i : Fin k => Q i.succ) S (fun u : ℤ => f (u + h) * star (f (u + h)))
        = boxNormPow k (fun i : Fin k => Q i.succ) S (pmod f 2) := by
    intro h _
    rw [show (fun u : ℤ => f (u + h) * star (f (u + h)))
          = Work.Peluse.shift h (fun u : ℤ => f u * star (f u)) from rfl,
      Work.Peluse.BoxNorm.boxNormPow_shift k (fun i : Fin k => Q i.succ) S
        (fun u : ℤ => f u * star (f u)) h (finSuppZ_mul_star_self f hfs),
      show (fun u : ℤ => f u * star (f u)) = pmod f 2 from funext hsq]
  have hdiagsum : (∑ h ∈ Q 0, boxNormPow k (fun i : Fin k => Q i.succ) S
        (fun u : ℤ => f (u + h) * star (f (u + h))))
      = ((Q 0).card : ℝ) * boxNormPow k (fun i : Fin k => Q i.succ) S (pmod f 2) := by
    rw [Finset.sum_congr rfl (fun h hh => hdiag h hh), Finset.sum_const, nsmul_eq_mul]
  have hbound : (∑ h ∈ Q 0, boxNormPow k (fun i : Fin k => Q i.succ) S
        (fun u : ℤ => f (u + h) * star (f (u + h))))
      ≤ ∑ h ∈ Q 0, ∑ h' ∈ Q 0, boxNormPow k (fun i : Fin k => Q i.succ) S
        (fun u : ℤ => f (u + h) * star (f (u + h'))) := by
    refine Finset.sum_le_sum (fun h hh => ?_)
    exact Finset.single_le_sum (s := Q 0)
      (f := fun h' : ℤ => boxNormPow k (fun i : Fin k => Q i.succ) S
        (fun u : ℤ => f (u + h) * star (f (u + h')))) (fun h' _ => norm_nonneg _) hh
  have hcardpos : (0 : ℝ) < ((Q 0).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hQ
  have hkey : boxNormPow k (fun i : Fin k => Q i.succ) S (pmod f 2)
      ≤ ((Q 0).card : ℝ)⁻¹ * ∑ h ∈ Q 0, ∑ h' ∈ Q 0,
          boxNormPow k (fun i : Fin k => Q i.succ) S
            (fun u : ℤ => f (u + h) * star (f (u + h'))) := by
    have h1 : ((Q 0).card : ℝ) * boxNormPow k (fun i : Fin k => Q i.succ) S (pmod f 2)
        ≤ ∑ h ∈ Q 0, ∑ h' ∈ Q 0, boxNormPow k (fun i : Fin k => Q i.succ) S
          (fun u : ℤ => f (u + h) * star (f (u + h'))) := by
      rw [← hdiagsum]; exact hbound
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt (inv_pos.mpr hcardpos))
    rwa [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hcardpos), one_mul] at h2
  rw [hreal]
  calc ((Q 0).card : ℝ)⁻¹ * boxNormPow k (fun i : Fin k => Q i.succ) S (pmod f 2)
      ≤ ((Q 0).card : ℝ)⁻¹ * (((Q 0).card : ℝ)⁻¹ * ∑ h ∈ Q 0, ∑ h' ∈ Q 0,
          boxNormPow k (fun i : Fin k => Q i.succ) S
            (fun u : ℤ => f (u + h) * star (f (u + h')))) :=
        mul_le_mul_of_nonneg_left hkey (by positivity)
    _ = ((Q 0).card : ℝ)⁻¹ * ((Q 0).card : ℝ)⁻¹ * ∑ h ∈ Q 0, ∑ h' ∈ Q 0,
          boxNormPow k (fun i : Fin k => Q i.succ) S
            (fun u : ℤ => f (u + h) * star (f (u + h'))) := by ring

/-! ## Iterating the diagonal peel -/

/-- Iterating the diagonal peel `m - 1` times. -/
theorem diag_iterate {n : ℕ} (hn : 1 ≤ n) (S : Finset ℤ) (Q : Fin (n+1) → Finset ℤ)
    (f : ℤ → ℂ) (hf : Work.Peluse.FinSuppZ f) (hQ : ∀ i, (Q i).Nonempty) :
    (∏ i : Fin n, (((Q i.castSucc).card : ℝ))⁻¹) *
        boxNormPow 1 (fun _ : Fin 1 => Q (Fin.last n)) S (pmod f (2 ^ n))
      ≤ boxNormPow (n+1) Q S f := by
  classical
  have key : ∀ j : ℕ, 1 ≤ j → ∀ (R : Fin (j+1) → Finset ℤ), (∀ i, (R i).Nonempty) →
      ∀ (g : ℤ → ℂ), Work.Peluse.FinSuppZ g →
      (∏ i : Fin j, (((R i.castSucc).card : ℝ))⁻¹) *
        boxNormPow 1 (fun _ : Fin 1 => R (Fin.last j)) S (pmod g (2 ^ j))
      ≤ boxNormPow (j+1) R S g := by
    intro j
    induction j with
    | zero => intro hj; omega
    | succ j ih =>
      intro hj R hR g hg
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0
        have hstep := boxNormPow_diag_step (k := 1) le_rfl R S g hg (hR 0)
        have h1 : (∏ i : Fin 1, (((R i.castSucc).card : ℝ))⁻¹) = ((R 0).card : ℝ)⁻¹ := by
          rw [Fin.prod_univ_one]
          have h0 : (Fin.castSucc (0 : Fin 1) : Fin 2) = 0 := by ext; simp
          rw [h0]
        have h2 : (fun _ : Fin 1 => R (Fin.last 1)) = (fun i : Fin 1 => R i.succ) := by
          funext i; fin_cases i; rfl
        have h3 : pmod g (2 ^ 1) = pmod g 2 := by norm_num
        rw [h1, h2, h3]
        exact hstep
      · have hstep := boxNormPow_diag_step (k := j+1) (by omega) R S g hg (hR 0)
        have hih := ih hjpos (fun i : Fin (j+1) => R i.succ) (fun i => hR i.succ)
          (pmod g 2) (finSuppZ_pmod 2 (by norm_num) hg)
        have hih' : (∏ i : Fin j, (((R i.castSucc.succ).card : ℝ))⁻¹) *
            boxNormPow 1 (fun _ : Fin 1 => R (Fin.last (j+1))) S (pmod g (2 ^ (j+1)))
            ≤ boxNormPow (j+1) (fun i : Fin (j+1) => R i.succ) S (pmod g 2) := by
          simpa only [pmod_pmod, Fin.succ_last, Nat.mul_comm, Nat.pow_succ] using hih
        have hcomb : ((R 0).card : ℝ)⁻¹ * ((∏ i : Fin j, (((R i.castSucc.succ).card : ℝ))⁻¹) *
              boxNormPow 1 (fun _ : Fin 1 => R (Fin.last (j+1))) S (pmod g (2 ^ (j+1))))
            ≤ boxNormPow (j+2) R S g :=
          le_trans (mul_le_mul_of_nonneg_left hih' (by positivity)) hstep
        rw [prod_castSucc_eq R]
        have heq : ((R 0).card : ℝ)⁻¹ * (∏ i : Fin j, (((R i.castSucc.succ).card : ℝ))⁻¹) *
              boxNormPow 1 (fun _ : Fin 1 => R (Fin.last (j+1))) S (pmod g (2 ^ (j+1)))
            = ((R 0).card : ℝ)⁻¹ * ((∏ i : Fin j, (((R i.castSucc.succ).card : ℝ))⁻¹) *
              boxNormPow 1 (fun _ : Fin 1 => R (Fin.last (j+1))) S (pmod g (2 ^ (j+1)))) := by
          ring
        rw [heq]
        exact hcomb
  exact key n hn Q hQ f hf

/-! ## The main diagonal inequality -/

theorem boxNormPow_diag_peel_aux {n : ℕ} (hn : 1 ≤ n) {N : ℕ} (hN : 0 < N) (f : ℤ → ℂ)
    (hf : Work.Peluse.SupportIn f N) (Q : Fin (n+1) → Finset ℤ) (hQ : ∀ i, (Q i).Nonempty) :
    (∏ i : Fin (n+1), (((Q i).card : ℝ))⁻¹) *
        boxNormPow 1 (fun _ : Fin 1 => Q 0) (Work.Peluse.symIcc N)
          (fun u : ℤ => (((‖f u‖ ^ (2 ^ n) : ℝ)) : ℂ))
      ≤ boxNormPow (n+1) Q (Work.Peluse.symIcc N) f := by
  classical
  have hfs : Work.Peluse.FinSuppZ f := ⟨N, hf⟩
  set S : Finset ℤ := Work.Peluse.symIcc N
  set R : Fin (n+1) → Finset ℤ := fun i => Q (finRotate (n+1) i) with hRdef
  have hRne : ∀ i, (R i).Nonempty := by intro i; rw [hRdef]; exact hQ _
  have hiter := diag_iterate hn S R f hfs hRne
  have hrot : ∀ i : Fin n, R i.castSucc = Q i.succ := fun i => by
    change Q ((finRotate (n+1)) i.castSucc) = Q i.succ
    rw [finRotate_castSucc n i]
  have hprod : (∏ i : Fin n, (((R i.castSucc).card : ℝ))⁻¹)
      = ∏ i : Fin n, (((Q i.succ).card : ℝ))⁻¹ :=
    Finset.prod_congr rfl (fun i _ => by rw [hrot i])
  have hlastR : R (Fin.last n) = Q 0 := by
    change Q ((finRotate (n+1)) (Fin.last n)) = Q 0
    rw [finRotate_last]
  have hperm : boxNormPow (n+1) R S f = boxNormPow (n+1) Q S f := by
    rw [hRdef]
    exact boxNormPow_comp_bij Q S f (finRotate (n+1)) (finRotate (n+1)).bijective
  rw [hprod, hlastR, hperm] at hiter
  change (∏ i : Fin (n+1), (((Q i).card : ℝ))⁻¹) *
      boxNormPow 1 (fun _ : Fin 1 => Q 0) S (pmod f (2 ^ n)) ≤ boxNormPow (n+1) Q S f
  have hB1nn : (0:ℝ) ≤ boxNormPow 1 (fun _ : Fin 1 => Q 0) S (pmod f (2 ^ n)) := norm_nonneg _
  have hprodnn : (0:ℝ) ≤ ∏ i : Fin n, (((Q i.succ).card : ℝ))⁻¹ :=
    Finset.prod_nonneg (fun i _ => by positivity)
  have hinv0 : ((Q 0).card : ℝ)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact_mod_cast Finset.card_pos.mpr (hQ 0)
  rw [Fin.prod_univ_succ]
  have hfac : (0:ℝ) ≤ (∏ i : Fin n, (((Q i.succ).card : ℝ))⁻¹) *
      boxNormPow 1 (fun _ : Fin 1 => Q 0) S (pmod f (2 ^ n)) := mul_nonneg hprodnn hB1nn
  calc (((Q 0).card : ℝ)⁻¹ * ∏ i : Fin n, (((Q i.succ).card : ℝ))⁻¹) *
        boxNormPow 1 (fun _ : Fin 1 => Q 0) S (pmod f (2 ^ n))
      = ((Q 0).card : ℝ)⁻¹ * ((∏ i : Fin n, (((Q i.succ).card : ℝ))⁻¹) *
        boxNormPow 1 (fun _ : Fin 1 => Q 0) S (pmod f (2 ^ n))) := by ring
    _ ≤ 1 * ((∏ i : Fin n, (((Q i.succ).card : ℝ))⁻¹) *
        boxNormPow 1 (fun _ : Fin 1 => Q 0) S (pmod f (2 ^ n))) :=
        mul_le_mul_of_nonneg_right hinv0 hfac
    _ = (∏ i : Fin n, (((Q i.succ).card : ℝ))⁻¹) *
        boxNormPow 1 (fun _ : Fin 1 => Q 0) S (pmod f (2 ^ n)) := one_mul _
    _ ≤ boxNormPow (n+1) Q S f := hiter

/-! ## The target -/

theorem boxNormPow_diag_peel {m : ℕ} (hm : 2 ≤ m) {N : ℕ} (hN : 0 < N) (f : ℤ → ℂ)
    (hf : Work.Peluse.SupportIn f N) (Q : Fin m → Finset ℤ) (hQ : ∀ i, (Q i).Nonempty) :
    (∏ i : Fin m, (((Q i).card : ℝ))⁻¹) *
        Work.Peluse.boxNormPow 1 (fun _ : Fin 1 => Q ⟨0, by omega⟩) (Work.Peluse.symIcc N)
          (fun u : ℤ => (((‖f u‖ ^ (2 ^ (m - 1)) : ℝ)) : ℂ))
      ≤ Work.Peluse.boxNormPow m Q (Work.Peluse.symIcc N) f := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  have hfin : (⟨0, by omega⟩ : Fin (n+1)) = 0 := by ext; simp
  have heq : (fun _ : Fin 1 => Q ⟨0, by omega⟩) = (fun _ : Fin 1 => Q (0 : Fin (n+1))) := by
    funext i; exact congrArg Q hfin
  have hexp : (2 : ℕ) ^ ((n+1) - 1) = 2 ^ n := by rw [Nat.add_sub_cancel]
  rw [heq, hexp]
  exact boxNormPow_diag_peel_aux (n := n) hn (N := N) hN f hf Q hQ

end

end Work.Peluse.Peel
