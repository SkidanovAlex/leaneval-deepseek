import Mathlib
import Submission.Work.TMC16Core.Basic.pd_cheb_setup

/-!
# Total-degree bound for the continuant polynomial `P_k`

The bivariate polynomial `Pbiv α lam E k` is the continuant of a list of `k`
potentials `afun α lam E k j`, each of total degree `1` (in `X = cos 2πx`,
`Y = sin 2πx`).  The continuant satisfies `cont (b :: c :: l) = b * cont (c :: l) - cont l`,
so induction on the length of the list gives `DegLe (cont l) l.length`, hence
`DegLe (Pbiv α lam E k) k`.
-/

namespace Work.TMC16Core.Cheb

open Polynomial

variable {P Q : Polynomial (Polynomial ℂ)} {d e : ℕ}

/-- `DegLe` is monotone in the degree bound. -/
lemma DegLe.mono (h : DegLe P d) (hd : d ≤ e) : DegLe P e :=
  fun i hi => (h i hi).trans hd

/-- A polynomial satisfying `DegLe P d` has `natDegree ≤ d`. -/
lemma DegLe.natDegree_le (h : DegLe P d) : P.natDegree ≤ d := by
  have := h P.natDegree le_rfl
  omega

/-- `DegLe` is submultiplicative for the total-degree bound. -/
lemma DegLe.mul (hP : DegLe P d) (hQ : DegLe Q e) : DegLe (P * Q) (d + e) := by
  intro k hk
  have hPd : P.natDegree ≤ d := hP.natDegree_le
  have hQe : Q.natDegree ≤ e := hQ.natDegree_le
  have hkde : k ≤ d + e := hk.trans (natDegree_mul_le.trans (add_le_add hPd hQe))
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => P.coeff a * Q.coeff b) k]
  have hsum : (∑ i ∈ Finset.range (k + 1), P.coeff i * Q.coeff (k - i)).natDegree ≤ d + e - k := by
    refine natDegree_sum_le_of_forall_le (Finset.range (k + 1))
      (f := fun i : ℕ => P.coeff i * Q.coeff (k - i)) ?_
    intro i hi
    rw [Finset.mem_range] at hi
    have hik : i ≤ k := by omega
    by_cases h1 : i ≤ P.natDegree
    · by_cases h2 : k - i ≤ Q.natDegree
      · have hp := hP i h1
        have hq := hQ (k - i) h2
        have hmul := natDegree_mul_le (p := P.coeff i) (q := Q.coeff (k - i))
        omega
      · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp h2), mul_zero, natDegree_zero]
        omega
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp h1), zero_mul, natDegree_zero]
      omega
  have h2 : (∑ i ∈ Finset.range (k + 1), P.coeff i * Q.coeff (k - i)).natDegree + k ≤ d + e := by
    omega
  exact h2

/-- `DegLe` is closed under subtraction with the maximum of the two bounds. -/
lemma DegLe.sub (hP : DegLe P d) (hQ : DegLe Q e) : DegLe (P - Q) (max d e) := by
  intro k hk
  have hPd : P.natDegree ≤ d := hP.natDegree_le
  have hQe : Q.natDegree ≤ e := hQ.natDegree_le
  have hkmax : k ≤ max d e :=
    hk.trans (natDegree_sub_le P Q |>.trans (max_le_max hPd hQe))
  have ha : (P.coeff k).natDegree + k ≤ max d e := by
    by_cases h : k ≤ P.natDegree
    · exact (hP k h).trans (le_max_left _ _)
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp h), natDegree_zero]
      omega
  have hb : (Q.coeff k).natDegree + k ≤ max d e := by
    by_cases h : k ≤ Q.natDegree
    · exact (hQ k h).trans (le_max_right _ _)
    · rw [coeff_eq_zero_of_natDegree_lt (not_le.mp h), natDegree_zero]
      omega
  rw [coeff_sub]
  calc (P.coeff k - Q.coeff k).natDegree + k
      ≤ max ((P.coeff k).natDegree) ((Q.coeff k).natDegree) + k :=
        Nat.add_le_add_right (natDegree_sub_le _ _) k
    _ ≤ max d e := by
        rcases le_total (P.coeff k).natDegree (Q.coeff k).natDegree with h | h
        · rw [max_eq_right h]; exact hb
        · rw [max_eq_left h]; exact ha

/-- Constants have total degree `0`. -/
lemma DegLe_cst (z : ℂ) (d : ℕ) : DegLe (cst z) d := by
  intro i hi
  rw [cst, natDegree_C] at hi
  have h0 : i = 0 := by omega
  subst h0
  simp [cst]

/-- The `cos` variable `cX = X` has total degree `1`. -/
lemma DegLe_cX : DegLe cX 1 := by
  intro i hi
  rw [cX, natDegree_C] at hi
  have h0 : i = 0 := by omega
  subst h0
  simp [cX]

/-- The `sin` variable `sY = Y` has total degree `1`. -/
lemma DegLe_sY : DegLe sY 1 := by
  intro i hi
  rw [sY, natDegree_X] at hi
  interval_cases i <;> simp [sY]

/-- Each potential `afun α lam E k j` has total degree `1`. -/
lemma DegLe_afun (α lam : ℝ) (E : ℂ) (k j : ℕ) : DegLe (afun α lam E k j) 1 := by
  rw [afun]
  refine (DegLe.sub (d := 0) (e := 1) (DegLe_cst E 0) ?_).mono (by omega)
  refine (DegLe.mul (d := 0) (e := 1) (DegLe_cst ((2 * lam : ℝ) : ℂ) 0) ?_).mono (by omega)
  refine (DegLe.sub (d := 1) (e := 1) ?_ ?_).mono (by omega)
  · exact (DegLe.mul (DegLe_cst _ 0) DegLe_cX).mono (by omega)
  · exact (DegLe.mul (DegLe_cst _ 0) DegLe_sY).mono (by omega)

/-- The continuant of a list of total-degree-`1` polynomials of length `k` has total
degree `≤ k`. -/
lemma cont_degle (l : List (Polynomial (Polynomial ℂ)))
    (hdeg : ∀ b ∈ l, DegLe b 1) : DegLe (cont l) l.length := by
  suffices h : ∀ n, ∀ l : List (Polynomial (Polynomial ℂ)), l.length = n →
      (∀ b ∈ l, DegLe b 1) → DegLe (cont l) l.length by
    exact h l.length l rfl hdeg
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hlen hdeg
    rcases l with _ | ⟨b, tl⟩
    · rw [cont_nil]
      intro i hi
      rw [natDegree_one] at hi
      have h0 : i = 0 := by omega
      subst h0
      simp
    · rcases tl with _ | ⟨c, l'⟩
      · rw [cont_singleton]
        simpa using hdeg b (by simp)
      · have hb : DegLe b 1 := hdeg b (by simp)
        have hlen2 : (b :: c :: l').length = l'.length + 2 := rfl
        have hlen1 : (c :: l').length = l'.length + 1 := rfl
        have hdegl' : DegLe (cont l') l'.length :=
          ih l'.length (by omega) l' rfl (fun x hx => hdeg x (by simp [hx]))
        have hdegl : DegLe (cont (c :: l')) (l'.length + 1) := by
          have := ih (c :: l').length (by omega) (c :: l') rfl
            (fun x hx => hdeg x (by simp [hx]))
          rwa [hlen1] at this
        rw [cont_cons_cons]
        refine (DegLe.sub (d := 1 + (l'.length + 1)) (e := l'.length)
          (DegLe.mul hb hdegl) hdegl').mono (by omega)

end Work.TMC16Core.Cheb

namespace Work.TMC16Core.Basic

theorem pd_cheb_deg (α lam : ℝ) (E : ℂ) (k : ℕ) :
    Work.TMC16Core.Cheb.DegLe (Work.TMC16Core.Cheb.Pbiv α lam E k) k := by
  have h := Work.TMC16Core.Cheb.cont_degle
    ((List.range k).map (Work.TMC16Core.Cheb.afun α lam E k))
    (by
      intro b hb
      rw [List.mem_map] at hb
      obtain ⟨j, _, rfl⟩ := hb
      exact Work.TMC16Core.Cheb.DegLe_afun α lam E k j)
  rw [List.length_map, List.length_range] at h
  simpa only [Work.TMC16Core.Cheb.Pbiv, Work.TMC16Core.Cheb.listA] using h

end Work.TMC16Core.Basic
