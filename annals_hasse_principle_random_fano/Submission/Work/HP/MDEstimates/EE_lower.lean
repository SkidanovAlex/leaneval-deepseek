import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.BridgeDefs
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.PrimBoxDefs
import Submission.Work.HP.prim_box_lower
import Submission.Work.HP.div_count
import Submission.Work.HP.MDEstimates.detL_one_le
import Submission.Work.HP.Lat.detL_inf_latOrth
import Submission.Work.HP.det_gam_gen
import Submission.Work.HP.MDEstimates.veronese_linIndep
import Submission.Work.HP.Sig2.omega_li

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Classical Finset MvPolynomial

namespace Work.HP.MDEstimates

open Work.HP

/-! ## 1.  The `g`-sum of the box union bound -/

private lemma inv_pow4_telescope (g : ℕ) (hg : 3 ≤ g) :
    (1 : ℝ) / (g : ℝ) ^ 4
      ≤ (1 / 3) * (1 / (((g - 1 : ℕ) : ℝ)) ^ 3 - 1 / (g : ℝ) ^ 3) := by
  have hg1 : 1 ≤ g := by omega
  set x : ℝ := ((g - 1 : ℕ) : ℝ) with hxdef
  have hx : 0 < x := by
    rw [hxdef]; exact_mod_cast (by omega : 0 < g - 1)
  have hg' : (g : ℝ) = x + 1 := by
    rw [hxdef]
    have h : g - 1 + 1 = g := Nat.sub_add_cancel hg1
    rw [← h]; push_cast; ring
  rw [hg']
  have hp1 : (0 : ℝ) < (x + 1) ^ 4 := by positivity
  rw [div_le_iff₀ hp1]
  have hval : (1 / 3 : ℝ) * (1 / x ^ 3 - 1 / (x + 1) ^ 3) * (x + 1) ^ 4
      = ((x + 1) ^ 3 - x ^ 3) * (x + 1) / (3 * x ^ 3) := by
    field_simp
    first | ring | ring_nf | skip
  rw [hval]
  have hden : (0 : ℝ) < 3 * x ^ 3 := by positivity
  rw [le_div_iff₀ hden]
  nlinarith [sq_nonneg x, hx]

private lemma sum_Icc_sub_eq (f : ℕ → ℝ) {a B : ℕ} (ha : 1 ≤ a) (haB : a ≤ B) :
    ∑ g ∈ Finset.Icc a B, (f (g - 1) - f g) = f (a - 1) - f B := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le haB
  induction k with
  | zero => simp
  | succ k ih =>
    have haB' : a ≤ a + k := by omega
    rw [Nat.add_succ, Finset.sum_Icc_succ_top (by omega)]
    rw [ih haB']
    have h1 : (a + k + 1 - 1 : ℕ) = a + k := by omega
    rw [h1]
    ring

private lemma sum_inv_pow4_le (H : ℕ) :
    ∑ g ∈ Finset.Icc 2 H, (1 : ℝ) / (g : ℝ) ^ 4 ≤ 5 / 48 := by
  rcases lt_or_ge H 2 with hH | hH
  · have hempty : Finset.Icc 2 H = ∅ := by rw [Finset.Icc_eq_empty_iff]; omega
    rw [hempty, Finset.sum_empty]; norm_num
  · rcases lt_or_ge H 3 with hH3 | hH3
    · have h2 : H = 2 := by omega
      subst h2
      rw [Finset.Icc_self, Finset.sum_singleton]
      norm_num
    · have hsplit : Finset.Icc 2 H = insert 2 (Finset.Icc 3 H) := by
        ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      have htele : ∑ g ∈ Finset.Icc 3 H,
          (1 / (((g - 1 : ℕ) : ℝ)) ^ 3 - 1 / (g : ℝ) ^ 3)
          = 1 / (2 : ℝ) ^ 3 - 1 / (H : ℝ) ^ 3 := by
        have h := sum_Icc_sub_eq (fun j : ℕ => (1 : ℝ) / (j : ℝ) ^ 3) (a := 3) (B := H)
          (by norm_num) hH3
        simpa using h
      have hle : ∑ g ∈ Finset.Icc 3 H, (1 : ℝ) / (g : ℝ) ^ 4 ≤ 1 / 24 := by
        calc ∑ g ∈ Finset.Icc 3 H, (1 : ℝ) / (g : ℝ) ^ 4
            ≤ ∑ g ∈ Finset.Icc 3 H,
                (1 / 3) * (1 / (((g - 1 : ℕ) : ℝ)) ^ 3 - 1 / (g : ℝ) ^ 3) :=
              Finset.sum_le_sum (fun g hg => inv_pow4_telescope g (Finset.mem_Icc.mp hg).1)
          _ = (1 / 3) * ∑ g ∈ Finset.Icc 3 H,
                (1 / (((g - 1 : ℕ) : ℝ)) ^ 3 - 1 / (g : ℝ) ^ 3) := by rw [Finset.mul_sum]
          _ = (1 / 3) * (1 / (2 : ℝ) ^ 3 - 1 / (H : ℝ) ^ 3) := by rw [htele]
          _ ≤ 1 / 24 := by
              have hH0 : (0 : ℝ) < (H : ℝ) ^ 3 := by
                have : 0 < H := by omega
                positivity
              have hpos : (0 : ℝ) < 1 / (H : ℝ) ^ 3 := one_div_pos.mpr hH0
              linarith
      rw [hsplit, Finset.sum_insert (by rw [Finset.mem_Icc]; omega)]
      have h2 : (1 : ℝ) / (((2 : ℕ) : ℝ)) ^ 4 = 1 / 16 := by norm_num
      rw [h2]
      linarith

private lemma one_div_two_pow (m : ℕ) : ((1 : ℝ) / 2) ^ m = ((2 : ℝ) ^ m)⁻¹ := by
  rw [one_div, inv_pow]

private lemma sum_inv_pow_le (k H : ℕ) (hk : 4 ≤ k) :
    ∑ g ∈ Finset.Icc 2 H, (1 : ℝ) / (g : ℝ) ^ k ≤ 5 / (3 * (2 : ℝ) ^ k) := by
  have hmain : ∑ g ∈ Finset.Icc 2 H, (1 : ℝ) / (g : ℝ) ^ k
      ≤ (1 / 2 : ℝ) ^ (k - 4) * (5 / 48) := by
    have hterm : ∀ g ∈ Finset.Icc 2 H,
        (1 : ℝ) / (g : ℝ) ^ k ≤ (1 / 2 : ℝ) ^ (k - 4) * (1 / (g : ℝ) ^ 4) := by
      intro g hg
      have hg2 : 2 ≤ g := (Finset.mem_Icc.mp hg).1
      have hg0 : (0 : ℝ) < (g : ℝ) := by exact_mod_cast (by omega : 0 < g)
      have h2g : (2 : ℝ) ^ (k - 4) ≤ (g : ℝ) ^ (k - 4) := by
        apply pow_le_pow_left₀ (by norm_num)
        exact_mod_cast hg2
      have hgk : (g : ℝ) ^ k = (g : ℝ) ^ 4 * (g : ℝ) ^ (k - 4) := by
        rw [← pow_add]; congr 1; omega
      have hkey : (1 : ℝ) / (g : ℝ) ^ k
          ≤ (1 : ℝ) / ((g : ℝ) ^ 4 * (2 : ℝ) ^ (k - 4)) := by
        rw [hgk]
        exact one_div_le_one_div_of_le (by positivity)
          (mul_le_mul_of_nonneg_left h2g (by positivity))
      have heq : (1 : ℝ) / ((g : ℝ) ^ 4 * (2 : ℝ) ^ (k - 4))
          = (1 / 2 : ℝ) ^ (k - 4) * (1 / (g : ℝ) ^ 4) := by
        rw [one_div_two_pow]
        rw [one_div, one_div, mul_inv]
        ring
      rw [← heq]
      exact hkey
    calc ∑ g ∈ Finset.Icc 2 H, (1 : ℝ) / (g : ℝ) ^ k
        ≤ ∑ g ∈ Finset.Icc 2 H, (1 / 2 : ℝ) ^ (k - 4) * (1 / (g : ℝ) ^ 4) :=
          Finset.sum_le_sum hterm
      _ = (1 / 2 : ℝ) ^ (k - 4) * ∑ g ∈ Finset.Icc 2 H, (1 / (g : ℝ) ^ 4) := by
          rw [Finset.mul_sum]
      _ ≤ (1 / 2 : ℝ) ^ (k - 4) * (5 / 48) := by
          apply mul_le_mul_of_nonneg_left (sum_inv_pow4_le H)
          positivity
  have hconst : (1 / 2 : ℝ) ^ (k - 4) * (5 / 48) = 5 / (3 * (2 : ℝ) ^ k) := by
    rw [one_div_two_pow]
    have hk4 : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 4) * 16 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, ← pow_add]
      congr 1
      omega
    rw [hk4]
    field_simp
    first | ring | ring_nf | skip
  linarith [hmain, hconst.le]

/-- The `g`-sum of the box union bound is at most a quarter of the leading term, for `k ≥ 4`. -/
private theorem sum_box_bound_k (k M : ℕ) (hk : 4 ≤ k) (hM : 14 ≤ M) :
    ∑ g ∈ Finset.Icc 2 M, (2 * ((M / g : ℕ) : ℝ) + 1) ^ k ≤ (1 / 4) * (2 * (M : ℝ)) ^ k := by
  have hsplit : Finset.Icc 2 M = Finset.Icc 2 (M / 4) ∪ Finset.Icc (M / 4 + 1) M := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj : Disjoint (Finset.Icc 2 (M / 4)) (Finset.Icc (M / 4 + 1) M) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    rw [Finset.mem_Icc] at hx1 hx2; omega
  rw [hsplit, Finset.sum_union hdisj]
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast (by omega : 0 < M)
  have hM14 : (14 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  -- Part 1: `g ≤ M/4`
  have hpart1 : ∑ g ∈ Finset.Icc 2 (M / 4), (2 * ((M / g : ℕ) : ℝ) + 1) ^ k
      ≤ ((9 / 4) * (M : ℝ)) ^ k * ∑ g ∈ Finset.Icc 2 (M / 4), (1 : ℝ) / (g : ℝ) ^ k := by
    have hterm : ∀ g ∈ Finset.Icc 2 (M / 4),
        (2 * ((M / g : ℕ) : ℝ) + 1) ^ k ≤ ((9 / 4) * (M : ℝ) / g) ^ k := by
      intro g hg
      obtain ⟨hg2, hgq⟩ := Finset.mem_Icc.mp hg
      have hg0 : (0 : ℝ) < (g : ℝ) := by exact_mod_cast (by omega : 0 < g)
      have h4g : 4 * g ≤ M := by omega
      have hMg : (4 : ℝ) ≤ (M : ℝ) / g := by
        rw [le_div_iff₀ hg0]
        have h : ((4 * g : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast h4g
        push_cast at h
        linarith
      have h1 : ((M / g : ℕ) : ℝ) ≤ (M : ℝ) / g := by
        rw [le_div_iff₀ hg0]
        have hd : (((M / g : ℕ) : ℝ)) * (g : ℝ) ≤ (M : ℝ) := by
          exact_mod_cast Nat.div_mul_le_self M g
        linarith
      have h2 : 2 * ((M / g : ℕ) : ℝ) + 1 ≤ (9 / 4) * ((M : ℝ) / g) := by
        nlinarith [hMg, h1]
      have hnn : 0 ≤ 2 * ((M / g : ℕ) : ℝ) + 1 := by positivity
      calc (2 * ((M / g : ℕ) : ℝ) + 1) ^ k ≤ ((9 / 4) * ((M : ℝ) / g)) ^ k :=
            pow_le_pow_left₀ hnn h2 k
        _ = ((9 / 4) * (M : ℝ) / g) ^ k := by ring_nf
    calc ∑ g ∈ Finset.Icc 2 (M / 4), (2 * ((M / g : ℕ) : ℝ) + 1) ^ k
        ≤ ∑ g ∈ Finset.Icc 2 (M / 4), ((9 / 4) * (M : ℝ) / g) ^ k :=
          Finset.sum_le_sum hterm
      _ = ((9 / 4) * (M : ℝ)) ^ k * ∑ g ∈ Finset.Icc 2 (M / 4), (1 : ℝ) / (g : ℝ) ^ k := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun g hg => ?_)
          rw [div_eq_mul_inv, mul_pow, inv_pow, one_div]
  have hA : ((9 : ℝ) / 4) ^ k / (2 : ℝ) ^ k = ((9 : ℝ) / 8) ^ k := by
    rw [← div_pow]
    norm_num
  have hconst2 : ((9 : ℝ) / 4) ^ k * (5 / (3 * (2 : ℝ) ^ k)) = (5 / 3) * ((9 : ℝ) / 8) ^ k := by
    rw [show (5 : ℝ) / (3 * (2 : ℝ) ^ k) = (5 / 3) / (2 : ℝ) ^ k by ring]
    rw [← hA]
    ring
  have hpart1b : ∑ g ∈ Finset.Icc 2 (M / 4), (2 * ((M / g : ℕ) : ℝ) + 1) ^ k
      ≤ (5 / 3) * ((9 : ℝ) / 8) ^ k * (M : ℝ) ^ k := by
    refine le_trans hpart1 ?_
    calc ((9 / 4) * (M : ℝ)) ^ k * ∑ g ∈ Finset.Icc 2 (M / 4), (1 : ℝ) / (g : ℝ) ^ k
        ≤ ((9 / 4) * (M : ℝ)) ^ k * (5 / (3 * (2 : ℝ) ^ k)) := by
          apply mul_le_mul_of_nonneg_left (sum_inv_pow_le k (M / 4) hk)
          positivity
      _ = (((9 : ℝ) / 4) ^ k * (5 / (3 * (2 : ℝ) ^ k))) * (M : ℝ) ^ k := by
          rw [mul_pow]
          ring
      _ = (5 / 3) * ((9 : ℝ) / 8) ^ k * (M : ℝ) ^ k := by
          rw [hconst2]
  -- Part 2: `g > M/4`
  have hpart2 : ∑ g ∈ Finset.Icc (M / 4 + 1) M, (2 * ((M / g : ℕ) : ℝ) + 1) ^ k
      ≤ (M : ℝ) * 7 ^ k := by
    have hterm : ∀ g ∈ Finset.Icc (M / 4 + 1) M,
        (2 * ((M / g : ℕ) : ℝ) + 1) ^ k ≤ (7 : ℝ) ^ k := by
      intro g hg
      obtain ⟨hg1, hg2⟩ := Finset.mem_Icc.mp hg
      have hg0 : 0 < g := by omega
      have hdiv : M / g ≤ 3 := by
        rw [Nat.div_le_iff_le_mul_add_pred hg0]
        omega
      have h7 : 2 * ((M / g : ℕ) : ℝ) + 1 ≤ 7 := by
        have : ((M / g : ℕ) : ℝ) ≤ 3 := by exact_mod_cast hdiv
        linarith
      exact pow_le_pow_left₀ (by positivity) h7 k
    calc ∑ g ∈ Finset.Icc (M / 4 + 1) M, (2 * ((M / g : ℕ) : ℝ) + 1) ^ k
        ≤ ∑ _g ∈ Finset.Icc (M / 4 + 1) M, (7 : ℝ) ^ k := Finset.sum_le_sum hterm
      _ = ((Finset.Icc (M / 4 + 1) M).card : ℝ) * 7 ^ k := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (M : ℝ) * 7 ^ k := by
          have hcard : (Finset.Icc (M / 4 + 1) M).card ≤ M := by
            rw [Nat.card_Icc]; omega
          have h7k : (0 : ℝ) ≤ (7 : ℝ) ^ k := by positivity
          have hcast : ((Finset.Icc (M / 4 + 1) M).card : ℝ) ≤ (M : ℝ) := by exact_mod_cast hcard
          exact mul_le_mul_of_nonneg_right hcast h7k
  -- the two numerical bounds
  have hP2 : (M : ℝ) * 7 ^ k ≤ (14 / (4 : ℝ) ^ k) * (2 * (M : ℝ)) ^ k := by
    have e1 : (14 / (4 : ℝ) ^ k) * (2 * (M : ℝ)) ^ k = 14 * (M : ℝ) ^ k / 2 ^ k := by
      rw [div_mul_eq_mul_div]
      rw [show (14 : ℝ) * (2 * (M : ℝ)) ^ k / (4 : ℝ) ^ k
          = 14 * ((2 * (M : ℝ)) ^ k / (4 : ℝ) ^ k) by ring]
      rw [← div_pow]
      rw [show (2 * (M : ℝ)) / 4 = (M : ℝ) / 2 by ring]
      rw [div_pow]
      ring
    rw [e1, le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ k)]
    have e2 : (M : ℝ) * 7 ^ k * 2 ^ k = 14 ^ k * (M : ℝ) := by
      rw [mul_assoc, ← mul_pow, show ((7 : ℝ) * 2) = 14 by norm_num, mul_comm]
    rw [e2]
    have h14 : (14 : ℝ) ^ (k - 1) ≤ (M : ℝ) ^ (k - 1) :=
      pow_le_pow_left₀ (by norm_num) hM14 (k - 1)
    have h14k : (14 : ℝ) ^ k = 14 * 14 ^ (k - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hMk : (M : ℝ) ^ k = M ^ (k - 1) * M := by
      rw [← pow_succ]; congr 1; omega
    rw [h14k, hMk]
    nlinarith [h14, hM0, pow_pos hM0 (k - 1)]
  have hP1 : (5 / 3 : ℝ) * ((9 : ℝ) / 8) ^ k * (M : ℝ) ^ k
      ≤ (3 / 16) * (2 * (M : ℝ)) ^ k := by
    have h94 : ((9 : ℝ) / 16) ^ k ≤ 6561 / 65536 := by
      have h := pow_le_pow_of_le_one (a := (9 : ℝ) / 16) (by norm_num) (by norm_num) hk
      have h3 : ((9 : ℝ) / 16) ^ 4 = 6561 / 65536 := by norm_num
      rwa [h3] at h
    have e1 : (5 / 3 : ℝ) * ((9 : ℝ) / 8) ^ k * (M : ℝ) ^ k
        = ((5 / 3) * ((9 : ℝ) / 16) ^ k) * (2 * (M : ℝ)) ^ k := by
      rw [show ((9 : ℝ) / 8) ^ k = ((9 : ℝ) / 16) ^ k * 2 ^ k by
        rw [show ((9 : ℝ) / 16) ^ k * 2 ^ k = ((9 : ℝ) / 8) ^ k by rw [← mul_pow]; norm_num]]
      rw [mul_pow]
      ring
    rw [e1]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc (5 / 3 : ℝ) * ((9 : ℝ) / 16) ^ k ≤ (5 / 3) * (6561 / 65536) :=
          mul_le_mul_of_nonneg_left h94 (by norm_num)
      _ ≤ 3 / 16 := by norm_num
  have hfin : (3 / 16) * (2 * (M : ℝ)) ^ k + (14 / (4 : ℝ) ^ k) * (2 * (M : ℝ)) ^ k
      ≤ (1 / 4) * (2 * (M : ℝ)) ^ k := by
    rw [← add_mul]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    have h4 : (224 : ℝ) ≤ (4 : ℝ) ^ k := by
      have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hk
      norm_num at h
      linarith
    have h14 : (14 : ℝ) / (4 : ℝ) ^ k ≤ 1 / 16 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (4 : ℝ) ^ k)]
      linarith
    linarith
  have h12 : ∑ g ∈ Finset.Icc 2 (M / 4), (2 * ((M / g : ℕ) : ℝ) + 1) ^ k
      + ∑ g ∈ Finset.Icc (M / 4 + 1) M, (2 * ((M / g : ℕ) : ℝ) + 1) ^ k
      ≤ (3 / 16) * (2 * (M : ℝ)) ^ k + (14 / (4 : ℝ) ^ k) * (2 * (M : ℝ)) ^ k :=
    add_le_add (le_trans hpart1b hP1) (le_trans hpart2 hP2)
  linarith [h12, hfin]

private lemma prim_box_lower_k (k M : ℕ) (hk : 4 ≤ k) (hM : 14 ≤ M) :
    (1 / 2) * (2 * (M : ℝ)) ^ k ≤ (((boxFinset M k).filter IsPrim).card : ℝ) := by
  have hEq : ((Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(M : ℤ)) (M : ℤ))).filter
      (fun a => Finset.univ.gcd a = 1)).card = ((boxFinset M k).filter IsPrim).card := by
    rw [show Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(M : ℤ)) (M : ℤ)) = boxFinset M k
      from rfl]
    exact congrArg Finset.card (Finset.filter_congr (s := boxFinset M k) (fun a _ => Iff.rfl))
  have h1 : ((Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(M : ℤ)) (M : ℤ))).card : ℝ)
      - 1 - ∑ g ∈ Finset.Icc 2 M, (2 * ((M / g : ℕ) : ℝ) + 1) ^ k
      ≤ (((boxFinset M k).filter IsPrim).card : ℝ) := by
    have h := prim_box_lower (ι := Fin k) M
    simp only [Fintype.card_fin, hEq] at h
    exact h
  have h2 : ∑ g ∈ Finset.Icc 2 M, (2 * ((M / g : ℕ) : ℝ) + 1) ^ k
      ≤ (1 / 4) * (2 * (M : ℝ)) ^ k := sum_box_bound_k k M hk hM
  have h3 : ((Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(M : ℤ)) (M : ℤ))).card : ℝ)
      = (2 * (M : ℝ) + 1) ^ k := by
    rw [show Fintype.piFinset (fun _ : Fin k => Finset.Icc (-(M : ℤ)) (M : ℤ)) = boxFinset M k
      from rfl]
    rw [card_boxFinset M k]
    push_cast
    ring
  have hM14 : (14 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
  have h4 : (4 : ℝ) ≤ (2 * (M : ℝ)) ^ k := by
    have h28 : (28 : ℝ) ≤ 2 * (M : ℝ) := by linarith
    have h1' : (28 : ℝ) ^ 4 ≤ (2 * (M : ℝ)) ^ 4 := pow_le_pow_left₀ (by norm_num) h28 4
    have h2' : (2 * (M : ℝ)) ^ 4 ≤ (2 * (M : ℝ)) ^ k :=
      pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ 2 * (M : ℝ)) hk
    norm_num at h1'
    linarith
  have h5 : (2 * (M : ℝ)) ^ k ≤ (2 * (M : ℝ) + 1) ^ k :=
    pow_le_pow_left₀ (by positivity) (by linarith) k
  linarith [h1, h2, h3, h4, h5]

private lemma rpow_nat_inv (B : ℝ) (hB : 0 ≤ B) (m : ℕ) (hm : 0 < m) :
    (B ^ (1 / (m : ℝ))) ^ m = B := by
  have hmne : ((m : ℕ) : ℝ) ≠ 0 := by positivity
  rw [← Real.rpow_natCast (B ^ (1 / (m : ℝ))) m]
  rw [← Real.rpow_mul hB (1 / (m : ℝ)) (m : ℝ)]
  have h1 : (1 / (m : ℝ)) * (m : ℝ) = 1 := by field_simp
  rw [h1, Real.rpow_one]

private lemma rpow_inv_nat (B : ℝ) (hB : 0 < B) (m : ℕ) (hm : 0 < m) :
    (B ^ m) ^ (1 / (m : ℝ)) = B := by
  have hmne : ((m : ℕ) : ℝ) ≠ 0 := by positivity
  rw [← Real.rpow_natCast B m]
  rw [← Real.rpow_mul (le_of_lt hB) (m : ℝ) (1 / (m : ℝ))]
  have h1 : (m : ℝ) * (1 / (m : ℝ)) = 1 := by field_simp
  rw [h1, Real.rpow_one]

theorem prim_ball_count_lower (k : ℕ) (hk : 4 ≤ k) :
    ∃ c R₀ : ℝ, 0 < c ∧ 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R →
      c * R ^ k ≤ ((({v : Fin k → ℤ | IsPrim v ∧ eNorm v ≤ R}).ncard : ℕ) : ℝ) := by
  have hsk : (0 : ℝ) < Real.sqrt k := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < k))
  refine ⟨1 / (2 * (Real.sqrt k) ^ k), 14 * Real.sqrt k, by positivity, by positivity, ?_⟩
  intro R hR
  have hR0 : 0 ≤ R := by
    have : (0 : ℝ) < 14 * Real.sqrt k := by positivity
    linarith
  set M : ℕ := ⌊R / Real.sqrt k⌋₊ with hMdef
  have hRdiv : (14 : ℝ) ≤ R / Real.sqrt k := by
    rw [le_div_iff₀ hsk]; linarith [hR]
  have hM14 : 14 ≤ M := by
    rw [hMdef]
    exact Nat.le_floor hRdiv
  have hstep : (1 / 2) * (2 * (M : ℝ)) ^ k ≤ (((boxFinset M k).filter IsPrim).card : ℝ) :=
    prim_box_lower_k k M hk hM14
  have hsub : ((boxFinset M k).filter IsPrim : Set (Fin k → ℤ))
      ⊆ {v : Fin k → ℤ | IsPrim v ∧ eNorm v ≤ R} := by
    intro v hv
    rw [Finset.mem_coe, Finset.mem_filter] at hv
    obtain ⟨hvbox, hvprim⟩ := hv
    refine ⟨hvprim, ?_⟩
    have hvv : eNorm v ≤ (M : ℝ) * Real.sqrt k := eNorm_le_of_mem_boxFinset hvbox
    have hMle : (M : ℝ) ≤ R / Real.sqrt k := by
      rw [hMdef]; exact Nat.floor_le (by positivity)
    have hle : (M : ℝ) * Real.sqrt k ≤ R := by
      rw [le_div_iff₀ hsk] at hMle
      linarith
    linarith
  have hfin : ({v : Fin k → ℤ | IsPrim v ∧ eNorm v ≤ R}).Finite :=
    (MDBasic.finite_eNorm_le (ι := Fin k) R).subset (fun v hv => hv.2)
  have hcard : (((boxFinset M k).filter IsPrim).card : ℝ)
      ≤ ((({v : Fin k → ℤ | IsPrim v ∧ eNorm v ≤ R}).ncard : ℕ) : ℝ) := by
    have h := Set.ncard_le_ncard hsub hfin
    rw [Set.ncard_coe_finset] at h
    exact_mod_cast h
  have h2M : R / Real.sqrt k ≤ 2 * (M : ℝ) := by
    have hfloor : R / Real.sqrt k - 1 ≤ (M : ℝ) := by
      have h := Nat.lt_floor_add_one (R / Real.sqrt k)
      rw [hMdef]; linarith
    have hM1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : 1 ≤ M)
    linarith
  have hpow : (R / Real.sqrt k) ^ k ≤ (2 * (M : ℝ)) ^ k :=
    pow_le_pow_left₀ (by positivity) h2M k
  have hRk : R ^ k = (R / Real.sqrt k) ^ k * (Real.sqrt k) ^ k := by
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero k (ne_of_gt hsk))]
  have hfinal : 1 / (2 * (Real.sqrt k) ^ k) * R ^ k ≤ (1 / 2) * (2 * (M : ℝ)) ^ k := by
    rw [hRk]
    rw [show (1 / (2 * (Real.sqrt k) ^ k)) * ((R / Real.sqrt k) ^ k * (Real.sqrt k) ^ k)
        = (1 / 2) * (R / Real.sqrt k) ^ k by field_simp; first | ring | ring_nf | skip]
    linarith [hpow]
  linarith [hstep, hcard, hfinal]

/-! ## 2.  The pointwise upper bound for `detL Γ_{x,y}` -/

private lemma eNorm_veronese_le' (d n : ℕ) (z : Fin (n + 1) → ℤ) :
    eNorm (veronese d n z) ≤ ((NN d n : ℝ) + 1) * ((n : ℝ) + 1) ^ d * eNorm z ^ d := by
  set S : ℝ := ∑ i, |((z i : ℝ))| with hS
  have hSnn : 0 ≤ S := by rw [hS]; positivity
  have hvc : ∀ i : Fin (n + 1), |((z i : ℝ))| ≤ S := fun i => by
    rw [hS]
    exact Finset.single_le_sum (f := fun j : Fin (n+1) => |((z j : ℝ))|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
  have hvz : ∀ i : Fin (n + 1), |((z i : ℝ))| ≤ eNorm z := fun i => by
    have h1 : ((z i : ℝ)) ^ 2 ≤ ∑ j, ((z j : ℝ)) ^ 2 :=
      Finset.single_le_sum (f := fun j : Fin (n+1) => ((z j : ℝ)) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    calc |((z i : ℝ))| = Real.sqrt (((z i : ℝ)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (∑ j, ((z j : ℝ)) ^ 2) := Real.sqrt_le_sqrt h1
      _ = eNorm z := rfl
  have hSle : S ≤ ((n : ℝ) + 1) * eNorm z := by
    rw [hS]
    calc ∑ i : Fin (n + 1), |((z i : ℝ))| ≤ ∑ _i : Fin (n + 1), eNorm z :=
          Finset.sum_le_sum (fun i _ => hvz i)
      _ = ((n : ℝ) + 1) * eNorm z := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hcoord : ∀ m : Mon d n, |(((veronese d n z m : ℤ)) : ℝ)| ≤ S ^ d := fun m => by
    have hvm : (((veronese d n z m : ℤ)) : ℝ) = ∏ i, ((z i : ℝ)) ^ ((m.1 i : ℕ)) := by
      simp only [veronese]
      push_cast
      rfl
    rw [hvm, Finset.abs_prod]
    calc ∏ i : Fin (n + 1), |((z i : ℝ)) ^ ((m.1 i : ℕ))|
        = ∏ i : Fin (n + 1), |((z i : ℝ))| ^ ((m.1 i : ℕ)) :=
          Finset.prod_congr rfl (fun i _ => abs_pow _ _)
      _ ≤ ∏ i : Fin (n + 1), S ^ ((m.1 i : ℕ)) :=
          Finset.prod_le_prod₀ (fun i _ => pow_nonneg (abs_nonneg _) _)
            (fun i _ => pow_le_pow_left₀ (abs_nonneg _) (hvc i) _)
      _ = S ^ (∑ i : Fin (n + 1), ((m.1 i : ℕ))) :=
          Finset.prod_pow_eq_pow_sum Finset.univ (fun i => ((m.1 i : ℕ))) S
      _ = S ^ d := by rw [m.2]
  have hsum : ∑ m : Mon d n, (((veronese d n z m : ℤ)) : ℝ) ^ 2
      ≤ (NN d n : ℝ) * S ^ (2 * d) := by
    have hterm : ∀ m : Mon d n, (((veronese d n z m : ℤ)) : ℝ) ^ 2 ≤ S ^ (2 * d) := fun m => by
      have h2 := hcoord m
      rw [show (((veronese d n z m : ℤ)) : ℝ) ^ 2
          = |(((veronese d n z m : ℤ)) : ℝ)| ^ 2 by rw [sq_abs]]
      calc |(((veronese d n z m : ℤ)) : ℝ)| ^ 2 ≤ (S ^ d) ^ 2 :=
            pow_le_pow_left₀ (abs_nonneg _) h2 2
        _ = S ^ (2 * d) := by
            rw [show S ^ (2 * d) = (S ^ d) ^ 2 by rw [two_mul, pow_add, pow_two]]
    calc ∑ m : Mon d n, (((veronese d n z m : ℤ)) : ℝ) ^ 2
        ≤ ∑ _m : Mon d n, S ^ (2 * d) := Finset.sum_le_sum (fun m _ => hterm m)
      _ = (NN d n : ℝ) * S ^ (2 * d) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have h1 : eNorm (veronese d n z) ≤ Real.sqrt (NN d n : ℝ) * S ^ d := by
    calc eNorm (veronese d n z)
        = Real.sqrt (∑ m : Mon d n, (((veronese d n z m : ℤ)) : ℝ) ^ 2) := rfl
      _ ≤ Real.sqrt ((NN d n : ℝ) * S ^ (2 * d)) := Real.sqrt_le_sqrt hsum
      _ = Real.sqrt (NN d n : ℝ) * S ^ d := by
          rw [Real.sqrt_mul (by positivity)]
          congr 1
          rw [show S ^ (2 * d) = (S ^ d) ^ 2 by rw [two_mul, pow_add, pow_two],
            Real.sqrt_sq (pow_nonneg hSnn d)]
  have h2 : Real.sqrt (NN d n : ℝ) ≤ (NN d n : ℝ) + 1 := by
    have h3 : Real.sqrt (NN d n : ℝ) ≤ Real.sqrt (((NN d n : ℝ) + 1) ^ 2) := by
      apply Real.sqrt_le_sqrt
      have hN : (0 : ℝ) ≤ (NN d n : ℝ) := Nat.cast_nonneg _
      nlinarith [hN]
    rwa [Real.sqrt_sq (by positivity)] at h3
  have h4 : Real.sqrt (NN d n : ℝ) * S ^ d
      ≤ ((NN d n : ℝ) + 1) * (((n : ℝ) + 1) * eNorm z) ^ d :=
    mul_le_mul h2 (pow_le_pow_left₀ hSnn hSle d) (pow_nonneg hSnn d) (by positivity)
  rw [mul_pow] at h4
  calc eNorm (veronese d n z) ≤ Real.sqrt (NN d n : ℝ) * S ^ d := h1
    _ ≤ ((NN d n : ℝ) + 1) * (((n : ℝ) + 1) ^ d * eNorm z ^ d) := h4
    _ = ((NN d n : ℝ) + 1) * ((n : ℝ) + 1) ^ d * eNorm z ^ d := by ring

private lemma wedgeNorm_le_mul {ι : Type*} [Fintype ι] (v w : ι → ℤ) :
    wedgeNorm v w ≤ eNorm v * eNorm w := by
  have hv : (0 : ℝ) ≤ eNorm v := Real.sqrt_nonneg _
  have hw : (0 : ℝ) ≤ eNorm w := Real.sqrt_nonneg _
  have e1 : Real.sqrt (eNorm v ^ 2 * eNorm w ^ 2) = eNorm v * eNorm w := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ eNorm v ^ 2), Real.sqrt_sq hv, Real.sqrt_sq hw]
  rw [wedgeNorm]
  calc Real.sqrt (eNorm v ^ 2 * eNorm w ^ 2 - (dotR (toR v) (toR w)) ^ 2)
      ≤ Real.sqrt (eNorm v ^ 2 * eNorm w ^ 2) :=
        Real.sqrt_le_sqrt (by linarith [sq_nonneg (dotR (toR v) (toR w))])
    _ = eNorm v * eNorm w := e1

private lemma detL_Gam_le (d n : ℕ) (x y : Fin (n + 1) → ℤ)
    (h : LinearIndependent ℤ ![veronese d n x, veronese d n y]) :
    detL (Gam d n x y)
      ≤ (((NN d n : ℝ) + 1) * ((n : ℝ) + 1) ^ d) ^ 2 * (eNorm x * eNorm y) ^ d := by
  have hg : gcdMinors2 (veronese d n x) (veronese d n y) ≠ 0 :=
    DGG.gcdMinors2_ne_zero (veronese d n x) (veronese d n y) h
  have hg1 : (1 : ℝ) ≤ |(((gcdMinors2 (veronese d n x) (veronese d n y) : ℤ)) : ℝ)| := by
    have : (1 : ℤ) ≤ |gcdMinors2 (veronese d n x) (veronese d n y)| := Int.one_le_abs hg
    exact_mod_cast this
  have hwn : (0 : ℝ) ≤ wedgeNorm (veronese d n x) (veronese d n y) := by
    rw [wedgeNorm]; positivity
  have h1 : detL (Gam d n x y) ≤ wedgeNorm (veronese d n x) (veronese d n y) := by
    have hdet := Lat.detL_inf_latOrth (veronese d n x) (veronese d n y) h
    simp only [Gam]
    rw [hdet, div_le_iff₀ (lt_of_lt_of_le one_pos hg1)]
    nlinarith [hwn, hg1]
  have h2 : wedgeNorm (veronese d n x) (veronese d n y)
      ≤ eNorm (veronese d n x) * eNorm (veronese d n y) := wedgeNorm_le_mul _ _
  have h3 : eNorm (veronese d n x) ≤ ((NN d n : ℝ) + 1) * ((n : ℝ) + 1) ^ d * eNorm x ^ d :=
    eNorm_veronese_le' d n x
  have h4 : eNorm (veronese d n y) ≤ ((NN d n : ℝ) + 1) * ((n : ℝ) + 1) ^ d * eNorm y ^ d :=
    eNorm_veronese_le' d n y
  have h5 : eNorm (veronese d n x) * eNorm (veronese d n y)
      ≤ (((NN d n : ℝ) + 1) * ((n : ℝ) + 1) ^ d) ^ 2 * (eNorm x * eNorm y) ^ d := by
    have hmul := mul_le_mul h3 h4 (Real.sqrt_nonneg _)
      (mul_nonneg (by positivity) (pow_nonneg (Real.sqrt_nonneg _) d))
    calc eNorm (veronese d n x) * eNorm (veronese d n y)
        ≤ (((NN d n : ℝ) + 1) * ((n : ℝ) + 1) ^ d * eNorm x ^ d)
          * (((NN d n : ℝ) + 1) * ((n : ℝ) + 1) ^ d * eNorm y ^ d) := hmul
      _ = (((NN d n : ℝ) + 1) * ((n : ℝ) + 1) ^ d) ^ 2 * (eNorm x * eNorm y) ^ d := by
          rw [mul_pow]; ring
  linarith [h1, h2, h5]

private lemma eNorm_neg_aux {ι : Type*} [Fintype ι] (v : ι → ℤ) : eNorm (-v) = eNorm v := by
  have h : ∀ i : ι, ((-v) i : ℝ) ^ 2 = ((v i : ℝ)) ^ 2 := by
    intro i
    simp
  simp only [eNorm]
  rw [Finset.sum_congr rfl (fun i _ => h i)]

theorem EE_lower (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) (h22 : (d, n) ≠ (2, 2)) :
    ∃ c B₀ : ℝ, 0 < c ∧ 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B → c * B ^ 2 ≤ Work.HP.EE d n B := by
  classical
  have hn2 : 2 ≤ n := le_trans hd hdn
  have hn3 : 3 ≤ n := by
    by_contra h
    push_neg at h
    have hn_eq : n = 2 := by omega
    have hd_eq : d = 2 := by omega
    exact h22 (by rw [hn_eq, hd_eq])
  obtain ⟨c₁, R₁, hc₁, hR₁, hcount⟩ := prim_ball_count_lower (n + 1) (by omega)
  set N : ℝ := (NN d n : ℝ) + 1 with hNdef
  set C : ℝ := N * ((n : ℝ) + 1) ^ d with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  set Rth : ℝ := max R₁ (max 1 (4 / c₁)) with hRthdef
  have hRth1 : 1 ≤ Rth := le_trans (le_max_left _ _) (le_max_right _ _)
  have hRthR : R₁ ≤ Rth := le_max_left _ _
  have hRth4 : 4 / c₁ ≤ Rth := le_trans (le_max_right _ _) (le_max_right _ _)
  have hRthpos : 0 < Rth := lt_of_lt_of_le one_pos hRth1
  refine ⟨c₁ ^ 2 / (2 * C ^ 2), max 1 (Rth ^ (n + 1 - d)), by positivity, by positivity, ?_⟩
  intro B hB
  have hB1 : 1 ≤ B := le_trans (le_max_left 1 _) hB
  have hBpos : 0 < B := lt_of_lt_of_le one_pos hB1
  have hRthm : Rth ^ (n + 1 - d) ≤ B := le_trans (le_max_right 1 _) hB
  set R : ℝ := B ^ (1 / ((n : ℝ) + 1 - d)) with hRdef
  have hRpos : 0 < R := Real.rpow_pos_of_pos hBpos _
  have hcast : ((n + 1 - d : ℕ) : ℝ) = (n : ℝ) + 1 - d := by
    have h : d ≤ n + 1 := by omega
    push_cast [Nat.cast_sub h]
    ring
  have hRpow : R ^ (n + 1 - d) = B := by
    rw [hRdef, ← hcast]
    exact rpow_nat_inv B hBpos.le (n + 1 - d) (by omega)
  have hRge : Rth ≤ R := by
    have h1 : Rth ^ (n + 1 - d) ≤ B := hRthm
    have hz : (0 : ℝ) < 1 / ((n : ℝ) + 1 - d) := by
      apply one_div_pos.mpr
      rw [← hcast]
      exact_mod_cast (by omega : 0 < n + 1 - d)
    have h2 : (Rth ^ (n + 1 - d)) ^ (1 / ((n : ℝ) + 1 - d)) ≤ R := by
      rw [hRdef]
      exact Real.rpow_le_rpow (pow_nonneg hRthpos.le _) h1 hz.le
    have h3 : (Rth ^ (n + 1 - d)) ^ (1 / ((n : ℝ) + 1 - d)) = Rth := by
      rw [← hcast]
      exact rpow_inv_nat Rth hRthpos (n + 1 - d) (by omega)
    rw [h3] at h2
    exact h2
  -- the counting bound for `Xi d n B = {x prim, ‖x‖ ≤ R}`
  have hXcard : c₁ * R ^ (n + 1) ≤ ((Xi d n B).ncard : ℝ) := hcount R (le_trans hRthR hRge)
  have hXfin : (Xi d n B).Finite := (MDBasic.finite_sets d n 0 B (fun _ => True)).2.1
  -- the number of pairs
  set Bad : Set ((Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :=
    {p | p.1 ∈ Xi d n B ∧ p.2 ∈ Xi d n B ∧ (p.1 = p.2 ∨ p.1 = -p.2)} with hBaddef
  have hOmeq : Omega d n B = (Xi d n B ×ˢ Xi d n B) \ Bad := by
    ext p
    simp only [Omega, Bad, Set.mem_setOf_eq, Set.mem_prod, Set.mem_sdiff, Set.mem_sep_iff]
    tauto
  have hBadsub : Bad ⊆ Xi d n B ×ˢ Xi d n B := fun p hp => ⟨hp.1, hp.2.1⟩
  have hBadfin : Bad.Finite := (hXfin.prod hXfin).subset hBadsub
  have hdiag : {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) |
      p.1 ∈ Xi d n B ∧ p.2 ∈ Xi d n B ∧ p.1 = p.2}.ncard = (Xi d n B).ncard := by
    have heq : {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) |
        p.1 ∈ Xi d n B ∧ p.2 ∈ Xi d n B ∧ p.1 = p.2}
        = (fun x : Fin (n + 1) → ℤ => (x, x)) '' (Xi d n B) := by
      ext p
      constructor
      · rintro ⟨h1, h2, h3⟩
        obtain ⟨a, b⟩ := p
        have h3' : a = b := h3
        exact ⟨a, h1, Prod.ext rfl h3'⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨hx, hx, rfl⟩
    rw [heq, Set.ncard_image_of_injective _ (fun a b h => congrArg Prod.fst h)]
  have hanti : {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) |
      p.1 ∈ Xi d n B ∧ p.2 ∈ Xi d n B ∧ p.1 = -p.2}.ncard = (Xi d n B).ncard := by
    have heq : {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) |
        p.1 ∈ Xi d n B ∧ p.2 ∈ Xi d n B ∧ p.1 = -p.2}
        = (fun x : Fin (n + 1) → ℤ => (x, -x)) '' (Xi d n B) := by
      ext p
      constructor
      · rintro ⟨h1, h2, h3⟩
        obtain ⟨a, b⟩ := p
        have h3' : a = -b := h3
        exact ⟨a, h1, Prod.ext rfl (by simp only [h3', neg_neg])⟩
      · rintro ⟨x, hx, rfl⟩
        refine ⟨hx, ?_, ?_⟩
        · rw [Xi] at hx ⊢
          exact ⟨IsPrim_neg x |>.mpr hx.1, by rw [eNorm_neg_aux]; exact hx.2⟩
        · simp
    rw [heq, Set.ncard_image_of_injective _ (fun a b h => congrArg Prod.fst h)]
  have hBadle : Bad.ncard ≤ 2 * (Xi d n B).ncard := by
    have hsub : Bad ⊆ {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) |
        p.1 ∈ Xi d n B ∧ p.2 ∈ Xi d n B ∧ p.1 = p.2} ∪
        {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) |
          p.1 ∈ Xi d n B ∧ p.2 ∈ Xi d n B ∧ p.1 = -p.2} := by
      intro p hp
      rcases hp.2.2 with h | h
      · exact Or.inl ⟨hp.1, hp.2.1, h⟩
      · exact Or.inr ⟨hp.1, hp.2.1, h⟩
    have hfin' : ({p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) |
        p.1 ∈ Xi d n B ∧ p.2 ∈ Xi d n B ∧ p.1 = p.2} ∪
        {p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) |
          p.1 ∈ Xi d n B ∧ p.2 ∈ Xi d n B ∧ p.1 = -p.2}).Finite :=
      ((hXfin.prod hXfin).subset (fun p hp => ⟨hp.1, hp.2.1⟩)).union
        ((hXfin.prod hXfin).subset (fun p hp => ⟨hp.1, hp.2.1⟩))
    calc Bad.ncard ≤ _ := Set.ncard_le_ncard hsub hfin'
      _ ≤ _ + _ := Set.ncard_union_le _ _
      _ = (Xi d n B).ncard + (Xi d n B).ncard := by rw [hdiag, hanti]
      _ = 2 * (Xi d n B).ncard := by ring
  have hOmcard : ((Omega d n B).ncard : ℝ)
      = ((Xi d n B).ncard : ℝ) * ((Xi d n B).ncard : ℝ) - (Bad.ncard : ℝ) := by
    have hle : Bad.ncard ≤ (Xi d n B ×ˢ Xi d n B).ncard :=
      Set.ncard_le_ncard hBadsub (hXfin.prod hXfin)
    rw [hOmeq, Set.ncard_sdiff hBadsub hBadfin, Nat.cast_sub hle, Set.ncard_prod]
    push_cast
    ring
  have hOmge : (1 / 2) * ((Xi d n B).ncard : ℝ) ^ 2 ≤ ((Omega d n B).ncard : ℝ) := by
    have hb : (Bad.ncard : ℝ) ≤ 2 * ((Xi d n B).ncard : ℝ) := by exact_mod_cast hBadle
    have h4 : (4 : ℝ) ≤ ((Xi d n B).ncard : ℝ) := by
      have hR1 : 1 ≤ R := le_trans hRth1 hRge
      have h4R : (4 : ℝ) ≤ c₁ * R := by
        have h4c : (4 : ℝ) / c₁ ≤ R := le_trans hRth4 hRge
        have := (div_le_iff₀ hc₁).mp h4c
        linarith
      have hRk : R ≤ R ^ (n + 1) := by
        have := pow_le_pow_right₀ hR1 (by omega : 1 ≤ n + 1)
        simpa using this
      have hc1R : (4 : ℝ) ≤ c₁ * R ^ (n + 1) :=
        le_trans h4R (mul_le_mul_of_nonneg_left hRk hc₁.le)
      linarith [hXcard, hc1R]
    rw [hOmcard]
    nlinarith [hb, h4]
  -- the per-pair determinant bound
  have hper : ∀ p ∈ Omega d n B, (C ^ 2 * R ^ (2 * d))⁻¹ ≤ 1 / detL (Gam d n p.1 p.2) := by
    intro p hp
    obtain ⟨hp1, hp2, hne, hne'⟩ := hp
    have hν : LinearIndependent ℤ ![veronese d n p.1, veronese d n p.2] :=
      veronese_linIndep d n hd p.1 p.2 hp1.1 hp2.1 hne hne'
    have hdet := detL_Gam_le d n p.1 p.2 hν
    have hle1 : (eNorm p.1 * eNorm p.2) ^ d ≤ (R * R) ^ d :=
      pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (mul_le_mul hp1.2 hp2.2 (Real.sqrt_nonneg _) hRpos.le) d
    have hdet' : detL (Gam d n p.1 p.2) ≤ C ^ 2 * R ^ (2 * d) := by
      have h1 : C ^ 2 * (eNorm p.1 * eNorm p.2) ^ d ≤ C ^ 2 * (R * R) ^ d :=
        mul_le_mul_of_nonneg_left hle1 (by positivity)
      have h2 : (R * R) ^ d = R ^ (2 * d) := by rw [mul_pow]; ring_nf
      calc detL (Gam d n p.1 p.2) ≤ C ^ 2 * (eNorm p.1 * eNorm p.2) ^ d := by
            rw [hCdef]; exact hdet
        _ ≤ C ^ 2 * (R * R) ^ d := h1
        _ = C ^ 2 * R ^ (2 * d) := by rw [h2]
    have hpos : 0 < detL (Gam d n p.1 p.2) := lt_of_lt_of_le zero_lt_one (detL_one_le _)
    rw [one_div]
    exact (inv_le_inv₀ (by positivity : (0 : ℝ) < C ^ 2 * R ^ (2 * d)) hpos).mpr hdet'
  -- the finsum lower bound
  set g : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ) → ℝ :=
    fun p => 1 / detL (Gam d n p.1 p.2) with hgdef
  have hΩfin : (Omega d n B).Finite := (MDBasic.finite_sets d n 0 B (fun _ => True)).2.2
  have hsupp : (Omega d n B ∩ Function.support g).Finite := hΩfin.subset Set.inter_subset_left
  have hm : 0 < (C ^ 2 * R ^ (2 * d))⁻¹ := by positivity
  have hsub_supp : Omega d n B ⊆ Function.support g := by
    intro p hp
    rw [Function.mem_support]
    exact ne_of_gt (by linarith [hper p hp, hm])
  have hkey : ((Omega d n B).ncard : ℝ) * (C ^ 2 * R ^ (2 * d))⁻¹ ≤ EE d n B := by
    rw [EE, finsum_mem_eq_sum g hsupp]
    have h1 : (hsupp.toFinset.card : ℝ) * (C ^ 2 * R ^ (2 * d))⁻¹
        ≤ ∑ p ∈ hsupp.toFinset, g p := by
      have hcs := Finset.card_nsmul_le_sum hsupp.toFinset g ((C ^ 2 * R ^ (2 * d))⁻¹)
        (fun p hp => hper p (((hsupp.mem_toFinset).mp hp).1))
      simpa [nsmul_eq_mul] using hcs
    have h2 : ((hsupp.toFinset.card : ℕ) : ℝ) = ((Omega d n B).ncard : ℝ) := by
      have h3 : hsupp.toFinset.card = (Omega d n B ∩ Function.support g).ncard :=
        (Set.ncard_eq_toFinset_card _ hsupp).symm
      have h4 : (Omega d n B ∩ Function.support g) = Omega d n B :=
        Set.inter_eq_left.mpr hsub_supp
      rw [h3, h4]
    rw [h2] at h1
    exact h1
  -- final arithmetic
  have hRd : R ^ (2 * d) = (R ^ d) ^ 2 := by
    rw [show (2 : ℕ) * d = d + d by omega, pow_add, pow_two]
  have hRd2 : R ^ (n + 1) = R ^ d * R ^ (n + 1 - d) := by
    rw [← pow_add]; congr 1; omega
  have hstep2 : (1 / 2) * (c₁ * R ^ (n + 1)) ^ 2 * (C ^ 2 * R ^ (2 * d))⁻¹
      = (c₁ ^ 2 / (2 * C ^ 2)) * B ^ 2 := by
    rw [hRd2, hRd, hRpow]
    field_simp
    first | ring | ring_nf | skip
  have hstep1 : (1 / 2) * (c₁ * R ^ (n + 1)) ^ 2 * (C ^ 2 * R ^ (2 * d))⁻¹
      ≤ ((Omega d n B).ncard : ℝ) * (C ^ 2 * R ^ (2 * d))⁻¹ := by
    have h1 : (c₁ * R ^ (n + 1)) ^ 2 ≤ ((Xi d n B).ncard : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hXcard 2
    have h2 := hOmge
    have h3 : (0 : ℝ) ≤ (C ^ 2 * R ^ (2 * d))⁻¹ := le_of_lt hm
    nlinarith [h1, h2, h3]
  calc c₁ ^ 2 / (2 * C ^ 2) * B ^ 2
      = (1 / 2) * (c₁ * R ^ (n + 1)) ^ 2 * (C ^ 2 * R ^ (2 * d))⁻¹ := hstep2.symm
    _ ≤ ((Omega d n B).ncard : ℝ) * (C ^ 2 * R ^ (2 * d))⁻¹ := hstep1
    _ ≤ EE d n B := hkey

end Work.HP.MDEstimates
