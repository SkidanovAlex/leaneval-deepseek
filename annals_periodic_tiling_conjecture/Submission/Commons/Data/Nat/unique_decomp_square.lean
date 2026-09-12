import Mathlib

namespace Commons.Data.Nat

private lemma sub_one_add (a b : ℕ) (ha : 1 ≤ a) : (a + b) - 1 = (a - 1) + b := by
  omega

private lemma euclid_unique (q a b j k : ℕ) (hq0 : 0 < q) (ha : a < q) (hb : b < q)
    (h : a + q * j = b + q * k) : a = b ∧ j = k := by
  have hmod := congrArg (fun z : ℕ => z % q) h
  have hL : (a + q * j) % q = a := by
    calc
      (a + q * j) % q = (a + j * q) % q := by rw [Nat.mul_comm]
      _ = a % q := by rw [Nat.add_mul_mod_self_right]
      _ = a := Nat.mod_eq_of_lt ha
  have hR : (b + q * k) % q = b := by
    calc
      (b + q * k) % q = (b + k * q) % q := by rw [Nat.mul_comm]
      _ = b % q := by rw [Nat.add_mul_mod_self_right]
      _ = b := Nat.mod_eq_of_lt hb
  have hab : a = b := by
    rw [hL, hR] at hmod
    exact hmod
  refine ⟨hab, ?_⟩
  subst b
  have hcancel : q * j = q * k := Nat.add_left_cancel h
  exact Nat.mul_left_cancel hq0 hcancel

theorem unique_decomp_square (q : ℕ) (hq : 1 ≤ q) (x : ℕ) (hx1 : 1 ≤ x) (hx2 : x ≤ q * q) :
    ∃! p : {n0 : ℕ // 1 ≤ n0 ∧ n0 ≤ q} × {j : ℕ // j < q}, x = p.1.1 + q * p.2.1 := by
  have hq0 : 0 < q := by omega
  have hmod_lt : (x - 1) % q < q := Nat.mod_lt (x - 1) hq0
  have hdiv_lt : (x - 1) / q < q := by
    exact (Nat.div_lt_iff_lt_mul hq0).2
      (lt_of_lt_of_le (Nat.sub_lt (by omega : 0 < x) (by norm_num : 0 < 1)) hx2)
  have hn0_one : 1 ≤ (x - 1) % q + 1 := by
    change Nat.succ 0 ≤ Nat.succ ((x - 1) % q)
    exact Nat.succ_le_succ (Nat.zero_le _)
  have hn0_le : (x - 1) % q + 1 ≤ q := by
    change Nat.succ ((x - 1) % q) ≤ q
    exact (Nat.succ_le_iff).2 hmod_lt
  have hdecomp : x = (x - 1) % q + 1 + q * ((x - 1) / q) := by
    calc
      x = (x - 1) + 1 := by exact (Nat.sub_add_cancel hx1).symm
      _ = ((x - 1) % q + q * ((x - 1) / q)) + 1 := by rw [Nat.mod_add_div]
      _ = (x - 1) % q + 1 + q * ((x - 1) / q) := by ring
  let p0 : {n0 : ℕ // 1 ≤ n0 ∧ n0 ≤ q} × {j : ℕ // j < q} :=
    (⟨(x - 1) % q + 1, ⟨hn0_one, hn0_le⟩⟩, ⟨(x - 1) / q, hdiv_lt⟩)
  refine ⟨p0, ?_, ?_⟩
  · change x = (x - 1) % q + 1 + q * ((x - 1) / q)
    exact hdecomp
  · intro p hp
    change x = p.1.1 + q * p.2.1 at hp
    rcases p with ⟨⟨n, hn⟩, ⟨j, hjq⟩⟩
    rcases hn with ⟨hn1, hnq⟩
    rw [hdecomp] at hp
    set c : ℕ := (x - 1) % q with hc_def
    set J : ℕ := (x - 1) / q with hJ_def
    have hminus0 := congrArg (fun z : ℕ => z - 1) hp
    rw [sub_one_add (c + 1) (q * J) (by omega : 1 ≤ c + 1)] at hminus0
    rw [sub_one_add n (q * j) hn1] at hminus0
    have hminus : c + q * J = (n - 1) + q * j := by
      simpa [Nat.add_sub_cancel] using hminus0
    have hc_lt : c < q := by simpa using hmod_lt
    have hb_lt : n - 1 < q := by omega
    have heucl := euclid_unique q c (n - 1) J j hq0 hc_lt hb_lt hminus
    rcases heucl with ⟨hc_eq, hJ_eq⟩
    have hn_eq : n = c + 1 := by
      rw [hc_eq]
      exact (Nat.sub_add_cancel hn1).symm
    subst c
    subst J
    apply Prod.ext
    · apply Subtype.ext
      exact hn_eq
    · apply Subtype.ext
      exact hJ_eq.symm

end Commons.Data.Nat
