import Mathlib

open Complex
open scoped Real BigOperators

namespace Commons.NumberTheory.DirichletCharacter

noncomputable section

set_option maxHeartbeats 4000000

lemma le_add_mul_iff_div_le {N a q m : ℕ} (hq : 0 < q) (ha : a ≤ q) :
    N + 1 ≤ a + q * m ↔ (N + q - a) / q ≤ m := by
  constructor
  · intro h
    by_cases haN : a ≤ N + 1
    · have hx : N + 1 - a ≤ q * m := by omega
      have hkey : N + q - a = (N + 1 - a) + q - 1 := by omega
      rw [hkey, Nat.div_le_iff_le_mul hq]
      have hmq : N + 1 - a ≤ m * q := by rw [Nat.mul_comm]; exact hx
      omega
    · have hlt : N + q - a < q := by omega
      rw [Nat.div_eq_of_lt hlt]; exact Nat.zero_le _
  · intro h
    have hmono : a + q * ((N + q - a) / q) ≤ a + q * m :=
      Nat.add_le_add_left (Nat.mul_le_mul_left q h) a
    have hbound : N + 1 ≤ a + q * ((N + q - a) / q) := by
      have hd := Nat.div_add_mod (N + q - a) q
      have hmod : (N + q - a) % q ≤ q - 1 := by
        have := Nat.mod_lt (N + q - a) hq; omega
      omega
    omega


lemma add_mul_le_iff_le_div {N M a q m : ℕ} (hq : 0 < q) (ha : a ≤ N + M) :
    a + q * m ≤ N + M ↔ m ≤ (N + M - a) / q := by
  constructor
  · intro h
    have h1 : q * m ≤ N + M - a := by omega
    rw [Nat.le_div_iff_mul_le hq]
    rw [Nat.mul_comm]
    exact h1
  · intro h
    have h1 : m * q ≤ N + M - a := (Nat.le_div_iff_mul_le hq).mp h
    have h2 : q * m ≤ N + M - a := by rw [Nat.mul_comm]; exact h1
    omega


lemma add_mul_sub_one (a q m : ℕ) (ha : 1 ≤ a) : a + q*m - 1 = a - 1 + q*m := by
  omega


lemma div_interval_len_le {q Y N M a : ℕ} (hq : 1 ≤ q) (hY : 1 ≤ Y) (hMY : M ≤ q * Y)
    (hlo : N + 1 ≤ a + q * ((N + q - a) / q))
    (hhi : a + q * ((N + M - a) / q) ≤ N + M) :
    (N + M - a) / q - (N + q - a) / q + 1 ≤ Y := by
  by_cases hle : (N + q - a) / q ≤ (N + M - a) / q
  · have h3 : q * ((N + M - a) / q - (N + q - a) / q) ≤ M - 1 := by
      rw [Nat.mul_sub_left_distrib]
      have h2 : q * ((N + M - a) / q) - q * ((N + q - a) / q)
          = (a + q * ((N + M - a) / q)) - (a + q * ((N + q - a) / q)) :=
        (Nat.add_sub_add_left a (q * ((N + M - a) / q)) (q * ((N + q - a) / q))).symm
      rw [h2]; omega
    have h5 : (N + M - a) / q - (N + q - a) / q < Y := by
      by_contra hcon
      have hcon' : Y ≤ (N + M - a) / q - (N + q - a) / q := by omega
      have h6 : q * Y ≤ q * ((N + M - a) / q - (N + q - a) / q) :=
        Nat.mul_le_mul_left q hcon'
      have hqY1 : 1 ≤ q * Y := Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
      have hM1 : M - 1 < q * Y := by omega
      omega
    omega
  · have hz : (N + M - a) / q - (N + q - a) / q = 0 :=
      Nat.sub_eq_zero_of_le (le_of_not_ge hle)
    omega


lemma interval_residue_decomp (q N M : ℕ) (hq : 1 ≤ q) (f : ℕ → ℂ) :
    ∑ n ∈ Finset.Icc (N + 1) (N + M), f n
      = ∑ a ∈ Finset.Icc 1 (min q (N + M)),
          ∑ m ∈ Finset.Icc ((N + q - a) / q) ((N + M - a) / q), f (a + q * m) := by
  have hq0 : 0 < q := hq
  rw [Finset.sum_sigma' (Finset.Icc 1 (min q (N + M)))
        (fun a => Finset.Icc ((N + q - a) / q) ((N + M - a) / q))
        (fun a m => f (a + q * m))]
  have key : ∀ n : ℕ, 1 ≤ n → ((n - 1) % q + 1) + q * ((n - 1) / q) = n := by
    intro n hn
    have h1 : (n - 1) % q + q * ((n - 1) / q) = n - 1 := by
      have h := Nat.div_add_mod (n - 1) q; omega
    omega
  refine Finset.sum_bij (fun n _ => (⟨(n - 1) % q + 1, (n - 1) / q⟩ : Sigma (fun _ : ℕ => ℕ)))
    ?_ ?_ ?_ ?_
  · rintro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have hn1' : 1 ≤ n := by omega
    have hmodle : (n - 1) % q ≤ n - 1 := Nat.mod_le _ _
    have haq : (n - 1) % q + 1 ≤ q := by have := Nat.mod_lt (n - 1) hq0; omega
    have haNM : (n - 1) % q + 1 ≤ N + M := by
      have h2 : (n - 1) % q + 1 ≤ (n - 1) + 1 := by omega
      rw [Nat.sub_add_cancel hn1'] at h2
      exact le_trans h2 hn2
    have h1a : 1 ≤ (n - 1) % q + 1 := by omega
    have h2a : (n - 1) % q + 1 ≤ min q (N + M) := le_min haq haNM
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨h1a, h2a⟩, ?_⟩
    rw [Finset.mem_Icc]
    have hdec := key n hn1'
    exact ⟨(le_add_mul_iff_div_le hq0 haq).mp (by rw [hdec]; exact hn1),
           (add_mul_le_iff_le_div hq0 haNM).mp (by rw [hdec]; exact hn2)⟩
  · rintro n1 hn1 n2 hn2 h
    have hn1' : 1 ≤ n1 := by have := (Finset.mem_Icc.mp hn1).1; omega
    have hn2' : 1 ≤ n2 := by have := (Finset.mem_Icc.mp hn2).1; omega
    have e1 : (n1 - 1) % q + 1 = (n2 - 1) % q + 1 := by
      have := congrArg (fun x : Sigma (fun _ : ℕ => ℕ) => x.1) h; simpa using this
    have e2 : (n1 - 1) / q = (n2 - 1) / q := by
      have := congrArg (fun x : Sigma (fun _ : ℕ => ℕ) => x.2) h; simpa using this
    have k1 := key n1 hn1'
    have k2 := key n2 hn2'
    rw [e1, e2] at k1
    omega
  · rintro ⟨a, m⟩ hb
    obtain ⟨ha, hm⟩ := Finset.mem_sigma.mp hb
    obtain ⟨ha1, ha2⟩ := Finset.mem_Icc.mp ha
    obtain ⟨hmlo, hmhi⟩ := Finset.mem_Icc.mp hm
    have haq : a ≤ q := le_trans ha2 (min_le_left q (N + M))
    have haNM : a ≤ N + M := le_trans ha2 (min_le_right q (N + M))
    have hlt : a - 1 < q := by omega
    refine ⟨a + q * m, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      exact ⟨(le_add_mul_iff_div_le hq0 haq).mpr hmlo,
             (add_mul_le_iff_le_div hq0 haNM).mpr hmhi⟩
    · have hcomp1 : (a + q * m - 1) % q + 1 = a := by
        rw [add_mul_sub_one a q m ha1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
        exact Nat.sub_add_cancel ha1
      have hcomp2 : (a + q * m - 1) / q = m := by
        rw [add_mul_sub_one a q m ha1, Nat.add_mul_div_left _ _ hq0, Nat.div_eq_of_lt hlt,
            Nat.zero_add]
      exact Sigma.ext hcomp1 (heq_of_eq hcomp2)
  · rintro n hn
    have hn1 : 1 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
    show f n = f ((n - 1) % q + 1 + q * ((n - 1) / q))
    rw [key n hn1]


end
end Commons.NumberTheory.DirichletCharacter
