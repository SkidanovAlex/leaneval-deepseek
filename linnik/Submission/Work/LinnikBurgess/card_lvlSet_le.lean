import Mathlib
import Submission.Work.LinnikBurgess.lf_defs
import Submission.Work.LinnikBurgess.card_hensel_le

namespace Work.LinnikBurgess

/-- If `v_p(n) = s` exactly (as a natural number), then `p^s ∣ n` in `ℤ`. -/
lemma dvd_of_padicValNat_eq {p n s : ℕ} (h : padicValNat p n = s) :
    ((p ^ s : ℕ) : ℤ) ∣ (n : ℤ) := by
  have h1 : p ^ s ∣ n := by rw [← h]; exact pow_padicValNat_dvd
  exact_mod_cast h1

/-- If `v_p(|d|) = s` exactly (`d ≠ 0`), then `p^(s+1) ∤ d` in `ℤ`. -/
lemma not_dvd_int_of_padicValNat {p s : ℕ} [Fact p.Prime] {d : ℤ} (hd : d ≠ 0)
    (h : padicValNat p d.natAbs = s) : ¬ ((p ^ (s + 1) : ℕ) : ℤ) ∣ d := by
  rw [← Int.dvd_natAbs]
  intro hdvd
  have hnat : p ^ (s + 1) ∣ d.natAbs := by exact_mod_cast hdvd
  have hne : d.natAbs ≠ 0 := fun hh => hd (Int.natAbs_eq_zero.1 hh)
  have := (padicValNat_dvd_iff_le hne).1 hnat
  omega

/-- For each level `s < T = capLevel p e`, at most `4 = natDegree N` elements `y < p^m` of the
support of Lemma A have `v_p(N'(y)) = s` exactly.  (`lvlSet p e a b s` is the set of `y` in the
support with `nval = s`, `N = critN a b`.)

Hints: `s < T ≤ m = cubeLevel p e` gives `s ≤ m - 1`; by the transfer hypothesis `hbt` such a `y` has
`b_y = min (nval y) T = s` and `p^(m+s) ∣ N(y)`, while `p^s ‖ N'(y)` follows from the definition of
`nval`.  Hence `y ∈ henselSet p (critN a b) m` (the exponent `max (2*s+1) (m+s) = m+s` divides `N(y)`),
and `card_hensel_le` bounds that set by `natDegree (critN a b) ≤ 4`. -/
theorem card_lvlSet_le {p e : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (he : 2 ≤ e)
    (a b : Fin 3 → ℕ) (hN : critN a b ≠ 0) (hdeg : (critN a b).natDegree ≤ 4)
    (hbt : SuppTransfer p e a b) {s : ℕ} (hs : s < capLevel p e) :
    (lvlSet p e a b s).card ≤ 4 := by
  classical
  have hm1 : 1 ≤ cubeLevel p e := one_le_cubeLevel hp5 (by omega)
  have hTle : capLevel p e ≤ cubeLevel p e := capLevel_le_cubeLevel hp5
  have hsub : lvlSet p e a b s ⊆ henselSet p (critN a b) (cubeLevel p e) := by
    intro y hy
    rw [lvlSet, Finset.mem_filter] at hy
    obtain ⟨hysupp, hnval⟩ := hy
    rw [suppSet, Finset.mem_filter] at hysupp
    obtain ⟨hyrange, hpred⟩ := hysupp
    have hyrange' : y < p ^ cubeLevel p e := Finset.mem_range.1 hyrange
    have hpred2 : suppPred p e a b y := hpred
    have hd0 : (critN a b).derivative.eval (y : ℤ) ≠ 0 := by
      intro h
      have hh : nval p e a b y = capLevel p e + 1 := by rw [nval, if_pos h]
      omega
    have hval : padicValNat p (((critN a b).derivative.eval (y : ℤ)).natAbs) = s := by
      rw [nval, if_neg hd0] at hnval
      exact hnval
    rw [henselSet, Finset.mem_filter]
    refine ⟨Finset.mem_range.2 hyrange', s, ?_, ?_, ?_⟩
    · exact (Int.dvd_natAbs).1 (dvd_of_padicValNat_eq hval)
    · exact not_dvd_int_of_padicValNat hd0 hval
    · rw [suppPred] at hpred2
      obtain ⟨hbval, hdvdeval⟩ := hbt y hpred2
      have hbval_s : bval p e a b y = s := by
        rw [hbval, hnval]
        exact min_eq_left (le_of_lt hs)
      have hdvd_eval : ((p ^ (cubeLevel p e + s) : ℕ) : ℤ) ∣ (critN a b).eval (y : ℤ) := by
        rwa [hbval_s] at hdvdeval
      have hmax : max (2 * s + 1) (cubeLevel p e + s) = cubeLevel p e + s := by
        apply max_eq_right
        have : s < cubeLevel p e := lt_of_lt_of_le hs hTle
        omega
      simpa [hmax] using hdvd_eval
  calc (lvlSet p e a b s).card
      ≤ (henselSet p (critN a b) (cubeLevel p e)).card := Finset.card_le_card hsub
    _ ≤ (critN a b).natDegree := card_hensel_le _ hN _ hm1
    _ ≤ 4 := hdeg

end Work.LinnikBurgess
