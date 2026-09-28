import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.DiagDefs
import Submission.Work.HP.FM4.xi_sum_vero
import Submission.Work.HP.six_le_NN
import Submission.Work.HP.eNorm_veronese_bounds
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.DeltaMix_sum_reindex
import Submission.Work.HP.latOrth_inv_sum_le
import Submission.Work.HP.logW_le_div_log

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open Filter Finset

namespace Work.HP

/-! ## Elementary helpers -/

lemma hp_eNorm_nonneg {ι : Type*} [Fintype ι] (v : ι → ℤ) : 0 ≤ eNorm v := Real.sqrt_nonneg _

lemma hp_eNorm_pos {ι : Type*} [Fintype ι] {v : ι → ℤ} (hv : v ≠ 0) : 0 < eNorm v := by
  rw [eNorm, Real.sqrt_pos]
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  exact Finset.sum_pos' (fun j _ => sq_nonneg ((v j : ℝ))) ⟨i, Finset.mem_univ i,
    sq_pos_of_ne_zero (by exact_mod_cast hi)⟩

lemma hp_isPrim_ne_zero {ι : Type*} [Fintype ι] {v : ι → ℤ} (h : IsPrim v) : v ≠ 0 := by
  rintro rfl
  have h0 : Finset.univ.gcd (0 : ι → ℤ) = 0 := Finset.gcd_eq_zero_iff.mpr (fun x _ => rfl)
  rw [IsPrim, h0] at h
  exact one_ne_zero h.symm

/-- The exponent vector of the monomial `x_j ^ d`. -/
def hp_powMon (d n : ℕ) (j : Fin (n + 1)) : Mon d n :=
  ⟨fun i => ⟨if i = j then d else 0, by split <;> omega⟩, by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ j) h⟩

lemma hp_veronese_powMon (d n : ℕ) (x : Fin (n + 1) → ℤ) (j : Fin (n + 1)) :
    veronese d n x (hp_powMon d n j) = x j ^ d := by
  rw [veronese, Finset.prod_eq_single j]
  · simp [hp_powMon]
  · intro b _ hb; simp [hp_powMon, hb]
  · intro h; exact absurd (Finset.mem_univ j) h

lemma hp_veronese_ne_zero (d n : ℕ) (hd : 1 ≤ d) {x : Fin (n + 1) → ℤ} (hx : x ≠ 0) :
    veronese d n x ≠ 0 := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra h; push Not at h; exact hx (funext h)
  intro h0
  have h1 := hp_veronese_powMon d n x i
  rw [h0] at h1
  simp only [Pi.zero_apply] at h1
  exact hi ((pow_eq_zero_iff (by omega : d ≠ 0)).mp h1.symm)

lemma hp_formEval_eq_zero_iff (d n : ℕ) (a : Mon d n → ℤ) (x : Fin (n + 1) → ℤ) :
    (formEval d n a x = 0) ↔ a ∈ latOrth (veronese d n x) := by
  rw [latOrth, LinearMap.mem_ker, Fintype.linearCombination_apply]
  simp only [zsmul_eq_mul, formEval]

lemma hp_finsum_mem_le_of_le {α : Type*} {s : Set α} (hs : s.Finite) {f g : α → ℝ}
    (h : ∀ a ∈ s, f a ≤ g a) : (∑ᶠ a ∈ s, f a) ≤ ∑ᶠ a ∈ s, g a := by
  rw [finsum_mem_of_finite s hs, finsum_mem_of_finite s hs]
  exact Finset.sum_le_sum (fun i hi => h i ((Set.Finite.mem_toFinset hs).mp hi))

lemma hp_finsum_mem_le_of_subset {α : Type*} {s t : Set α} (hst : s ⊆ t) (ht : t.Finite)
    {f : α → ℝ} (hf : ∀ a, 0 ≤ f a) : (∑ᶠ a ∈ s, f a) ≤ ∑ᶠ a ∈ t, f a := by
  have hs : s.Finite := ht.subset hst
  rw [finsum_mem_of_finite s hs, finsum_mem_of_finite t ht]
  exact Finset.sum_le_sum_of_subset_of_nonneg ((Set.Finite.toFinset_subset_toFinset).2 hst)
    (fun a _ _ => hf a)

lemma hp_finsum_mem_filter_eq {α : Type*} (s : Set α) (hs : s.Finite) (Q : α → Prop)
    [DecidablePred Q] (f : α → ℝ) :
    (∑ᶠ x ∈ s, (if Q x then f x else 0)) = ∑ᶠ x ∈ ({x ∈ s | Q x} : Set α), f x := by
  have hfin : ({x ∈ s | Q x} : Set α).Finite := hs.subset (fun x hx => hx.1)
  have hfe : hs.toFinset.filter Q = hfin.toFinset := by
    ext x
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  rw [finsum_mem_of_finite s hs, ← Finset.sum_filter, hfe, finsum_mem_of_finite _ hfin]

lemma hp_finsum_mem_mul_right {α : Type*} (s : Set α) (hs : s.Finite) (c : ℝ) (f : α → ℝ) :
    (∑ᶠ a ∈ s, f a * c) = (∑ᶠ a ∈ s, f a) * c := by
  rw [finsum_mem_of_finite s hs, finsum_mem_of_finite s hs, Finset.sum_mul]

/-! ## The inner sum bound -/

/-- For a nonzero `x`, the sum of `1/‖a‖` over the primitive coefficient vectors `a` of norm
`≤ A` that vanish at `x` is `≪ A^{N-2}`.  Immediate from the general lattice bound
`latOrth_inv_sum_le` applied to `c = ν_{d,n}(x)`. -/
theorem primSet_latOrth_inv_sum_le (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ (x : Fin (n + 1) → ℤ), x ≠ 0 → ∀ A : ℝ, 1 ≤ A →
      (∑ᶠ a ∈ primSet d n A (fun _ => True),
         (if formEval d n a x = 0 then 1 / eNorm a else 0)) ≤ K * A ^ (NN d n - 2) := by
  obtain ⟨K, hK, hL⟩ := latOrth_inv_sum_le (Mon d n)
    (by have := six_le_NN d n hd hdn; simpa [NN] using (show 3 ≤ NN d n by omega))
  refine ⟨K, hK, fun x hx A hA => ?_⟩
  -- `ν_{d,n}(x) ≠ 0`
  have hν : veronese d n x ≠ 0 := hp_veronese_ne_zero d n (show 1 ≤ d by omega) hx
  have hsub : ({a ∈ primSet d n A (fun _ => True) | formEval d n a x = 0} : Set (Mon d n → ℤ))
      ⊆ ({a : Mon d n → ℤ | a ∈ latOrth (veronese d n x) ∧ 0 < eNorm a ∧ eNorm a ≤ A}
          : Set (Mon d n → ℤ)) := by
    intro a ha
    rw [Set.mem_setOf_eq] at ha
    obtain ⟨⟨hprim, hnorm, -⟩, hzero⟩ := ha
    exact ⟨(hp_formEval_eq_zero_iff d n a x).mp hzero,
      hp_eNorm_pos (hp_isPrim_ne_zero hprim), hnorm⟩
  have hsup : ({a : Mon d n → ℤ | a ∈ latOrth (veronese d n x) ∧ 0 < eNorm a ∧ eNorm a ≤ A}
      : Set (Mon d n → ℤ)).Finite :=
    (MDBasic.finite_eNorm_le A).subset (fun a ha => ha.2.2)
  calc (∑ᶠ a ∈ primSet d n A (fun _ => True),
          (if formEval d n a x = 0 then 1 / eNorm a else 0))
      = ∑ᶠ a ∈ ({a ∈ primSet d n A (fun _ => True) | formEval d n a x = 0}
          : Set (Mon d n → ℤ)), 1 / eNorm a :=
        hp_finsum_mem_filter_eq (primSet d n A (fun _ => True))
          (primSet_finite d n A _) (fun a => formEval d n a x = 0) (fun a => 1 / eNorm a)
    _ ≤ ∑ᶠ a ∈ ({a : Mon d n → ℤ | a ∈ latOrth (veronese d n x) ∧ 0 < eNorm a ∧ eNorm a ≤ A}
          : Set (Mon d n → ℤ)), 1 / eNorm a :=
        hp_finsum_mem_le_of_subset hsub hsup
          (fun a => div_nonneg zero_le_one (hp_eNorm_nonneg a))
    _ ≤ K * A ^ (NN d n - 2) := hL (veronese d n x) hν A hA

/-! ## The main theorem -/

theorem mix_sum_le (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ K B₀ : ℝ, 0 < K ∧ 0 < B₀ ∧ ∀ A B : ℝ, B₀ ≤ B → B / Real.log B ≤ A → A ≤ B ^ 2 →
      (∑ᶠ a ∈ primSet d n A (fun _ => True), DeltaMix d n a B)
        ≤ K * A ^ (NN d n - 1) * B := by
  classical
  obtain ⟨K5, hK5pos, h5⟩ := primSet_latOrth_inv_sum_le d n hd hdn
  obtain ⟨Cx, Bx, hCxpos, -, hXi⟩ := FM4.xi_sum_vero d n hd hdn
  obtain ⟨Bw, hBwpos, hBw⟩ := logW_le_div_log
  refine ⟨K5 * Cx, max Bx (max Bw 4), mul_pos hK5pos hCxpos, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num)
      (le_trans (le_max_right Bw 4) (le_max_right Bx (max Bw 4)))
  · intro A B hB hA hAB
    have hBx' : Bx ≤ B := le_trans (le_max_left Bx (max Bw 4)) hB
    have hBw'' : max Bw 4 ≤ B := le_trans (le_max_right Bx (max Bw 4)) hB
    have hBw' : Bw ≤ B := le_trans (le_max_left Bw 4) hBw''
    have hB4 : (4:ℝ) ≤ B := le_trans (le_max_right Bw 4) hBw''
    have hB1 : (1:ℝ) ≤ B := by linarith
    have hB0 : (0:ℝ) ≤ B := by linarith
    have hlogpos : 0 < Real.log B := Real.log_pos (by linarith)
    have hLnn : (0:ℝ) ≤ Real.log B := le_of_lt hlogpos
    have hWnn : (0:ℝ) ≤ (bigW (wOf B) : ℝ) := Nat.cast_nonneg _
    have hLW : Real.log B * (bigW (wOf B) : ℝ) ≤ A := le_trans (hBw B hBw') hA
    have hA1 : (1:ℝ) ≤ A := by
      have h1 : (1:ℝ) ≤ B / Real.log B := by
        rw [le_div_iff₀ hlogpos]
        have h2 := Real.log_le_sub_one_of_pos (show (0:ℝ) < B by linarith)
        linarith
      exact le_trans h1 hA
    have hA0 : (0:ℝ) ≤ A := le_trans zero_le_one hA1
    have hN2 : 2 ≤ NN d n := le_trans (by norm_num) (six_le_NN d n hd hdn)
    have hAmod : (0:ℝ) ≤ A ^ (NN d n - 2) := pow_nonneg hA0 _
    have hXfin : (Xi d n B).Finite := Xi_finite d n B
    rw [DeltaMix_sum_reindex d n A B]
    have hKA : (0:ℝ) ≤ K5 * A ^ (NN d n - 2) := mul_nonneg hK5pos.le hAmod
    have hS : (∑ᶠ x ∈ Xi d n B, (1 / eNorm (veronese d n x)) *
          (∑ᶠ a ∈ primSet d n A (fun _ => True),
            (if formEval d n a x = 0 then 1 / eNorm a else 0)))
        ≤ (K5 * A ^ (NN d n - 2)) * (Cx * B) := by
      calc (∑ᶠ x ∈ Xi d n B, (1 / eNorm (veronese d n x)) *
            (∑ᶠ a ∈ primSet d n A (fun _ => True),
              (if formEval d n a x = 0 then 1 / eNorm a else 0)))
          ≤ ∑ᶠ x ∈ Xi d n B, (1 / eNorm (veronese d n x)) * (K5 * A ^ (NN d n - 2)) :=
            hp_finsum_mem_le_of_le hXfin (fun x hx =>
              mul_le_mul_of_nonneg_left (h5 x (hp_isPrim_ne_zero hx.1) A hA1)
                (div_nonneg zero_le_one (hp_eNorm_nonneg _)))
        _ = (K5 * A ^ (NN d n - 2)) * (∑ᶠ x ∈ Xi d n B, (1 / eNorm (veronese d n x))) := by
            rw [hp_finsum_mem_mul_right (Xi d n B) hXfin (K5 * A ^ (NN d n - 2))
              (fun x => 1 / eNorm (veronese d n x)), mul_comm]
        _ ≤ (K5 * A ^ (NN d n - 2)) * (Cx * B) :=
            mul_le_mul_of_nonneg_left (hXi B hBx') hKA
    refine le_trans (mul_le_mul_of_nonneg_left hS (mul_nonneg (mul_nonneg (by norm_num) hLnn) hWnn)) ?_
    have hY0 : (0:ℝ) ≤ (K5 * A ^ (NN d n - 2)) * (Cx * B) :=
      mul_nonneg hKA (mul_nonneg hCxpos.le hB0)
    have h01 : (1/2) * Real.log B * (bigW (wOf B) : ℝ) ≤ (1/2) * A := by
      have hh := mul_le_mul_of_nonneg_left hLW (by norm_num : (0:ℝ) ≤ (1:ℝ)/2)
      linarith
    have hstep : (1/2) * Real.log B * (bigW (wOf B) : ℝ) * ((K5 * A ^ (NN d n - 2)) * (Cx * B))
        ≤ (1/2) * A * ((K5 * A ^ (NN d n - 2)) * (Cx * B)) :=
      mul_le_mul_of_nonneg_right h01 hY0
    refine le_trans hstep ?_
    have hpow : A ^ (NN d n - 2) * A = A ^ (NN d n - 1) := by
      rw [← pow_succ]
      congr 1
      omega
    have heq : (1/2) * A * ((K5 * A ^ (NN d n - 2)) * (Cx * B))
        = (1/2) * K5 * Cx * A ^ (NN d n - 1) * B := by
      rw [← hpow]; ring
    rw [heq]
    have hZ0 : (0:ℝ) ≤ K5 * Cx * A ^ (NN d n - 1) * B :=
      mul_nonneg (mul_nonneg (mul_nonneg hK5pos.le hCxpos.le) (pow_nonneg hA0 _)) hB0
    calc (1/2) * K5 * Cx * A ^ (NN d n - 1) * B
        = (1/2) * (K5 * Cx * A ^ (NN d n - 1) * B) := by ring
      _ ≤ 1 * (K5 * Cx * A ^ (NN d n - 1) * B) :=
          mul_le_mul_of_nonneg_right (by norm_num : ((1:ℝ)/2) ≤ 1) hZ0
      _ = K5 * Cx * A ^ (NN d n - 1) * B := by ring

end Work.HP
