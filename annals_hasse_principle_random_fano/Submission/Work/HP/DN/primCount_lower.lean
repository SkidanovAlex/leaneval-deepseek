import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.box_card
import Submission.Work.HP.prim_box_lower
import Submission.Work.HP.count_basic
import Submission.Work.HP.MDEstimates.pairS0_arith
import Submission.Work.HP.DN.sum_div_bound_DN

/-!
# `N_{d,n} ≥ 6` and the lower bound `#prim(A) ≫ A^{N_{d,n}}`

The node `primCount_lower` of the Hasse-principle formalisation proves that the number of
primitive coefficient vectors of height `≤ A` grows at least like `A^{N_{d,n}}`, for all
`d ≥ 2`, `n ≥ 3` (no relation between `d` and `n` is assumed).

The statement is the same as `Work.HP.count_basic`, except that the latter assumes
`d ≤ n`.  The only place that hypothesis was used there is the lower bound
`six_le_NN : 6 ≤ N_{d,n}`; here we prove the stronger `NN_ge_six : 6 ≤ N_{d,n}` from
`2 ≤ d` and `3 ≤ n` (via `N_{d,n} = C(n+d,d) ≥ C(5,3) = 10`), and then the argument of
`count_basic` goes through verbatim.

The auxiliary arithmetic bound on the `g`-adic union-bound sum is proved in the sibling
module `Submission.Work.HP.DN.sum_div_bound_DN`.
-/

namespace Work.HP.DN

open Filter Finset

/-- `N_{d,n} = C(n+d, d) ≥ C(5,3) = 10 ≥ 6` whenever `2 ≤ d` and `3 ≤ n`. -/
theorem NN_ge_six (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) : 6 ≤ NN d n := by
  have hfin : (10 : ℕ) ≤ (n + d).choose d := by
    have htop : d + 3 ≤ n + d := by omega
    have h1 : (d + 3).choose d ≤ (n + d).choose d := Nat.choose_le_choose d htop
    have hsymm : (d + 3).choose d = (d + 3).choose 3 := by
      have h := Nat.choose_symm (n := d + 3) (k := 3) (by omega)
      simpa using h
    have htop2 : 5 ≤ d + 3 := by omega
    have h2 : (5 : ℕ).choose 3 ≤ (d + 3).choose 3 := Nat.choose_le_choose 3 htop2
    calc (10 : ℕ) = (5 : ℕ).choose 3 := by decide
      _ ≤ (d + 3).choose 3 := h2
      _ = (d + 3).choose d := hsymm.symm
      _ ≤ (n + d).choose d := h1
  have hcast : (6 : ℝ) ≤ (NN d n : ℝ) := by
    rw [Work.HP.MDEstimates.NN_eq_choose d n]
    exact_mod_cast (by omega : (6 : ℕ) ≤ (n + d).choose d)
  exact_mod_cast hcast

/-- Lower bound for the number of primitive vectors in the coordinate box
`∏_m [-B, B] ⊂ (Mon d n → ℤ)`: at least half of `(2B)^N`.

Route: `prim_box_lower` gives `#box - 1 - Σ_{g=2}^{B} #(g-divisible) ≤ #prim`, `box_card`
computes the two cardinalities, and `sum_div_bound_DN` bounds the `g`-adic sum by a quarter
of `(2B)^N`; the rest is arithmetic. -/
theorem box_prim_lower (d n : ℕ) (hN6 : 6 ≤ NN d n) (B : ℕ) (hB : 5 ≤ B) :
    (1 / 2) * (2 * (B : ℝ)) ^ (NN d n) ≤
      (((Fintype.piFinset (fun _ : Mon d n => Finset.Icc (-(B : ℤ)) (B : ℤ))).filter
        (fun a => Finset.univ.gcd a = 1)).card : ℝ) := by
  classical
  have hcard : ((Fintype.piFinset (fun _ : Mon d n => Finset.Icc (-(B : ℤ)) (B : ℤ))).card : ℝ)
      = (2 * (B:ℝ) + 1) ^ (NN d n) := (box_card (ι := Mon d n) B).1
  have hlow : ((Fintype.piFinset (fun _ : Mon d n => Finset.Icc (-(B : ℤ)) (B : ℤ))).card : ℝ)
      - 1 - ∑ g ∈ Finset.Icc 2 B, (2 * ((B / g : ℕ) : ℝ) + 1) ^ (NN d n)
      ≤ (((Fintype.piFinset (fun _ : Mon d n => Finset.Icc (-(B : ℤ)) (B : ℤ))).filter
          (fun a => Finset.univ.gcd a = 1)).card : ℝ) := prim_box_lower (ι := Mon d n) B
  have hsumB : (∑ g ∈ Finset.Icc 2 B, (2 * ((B / g : ℕ) : ℝ) + 1) ^ (NN d n))
      ≤ (2 * (B : ℝ)) ^ (NN d n) / 4 := sum_div_bound_DN (NN d n) B hN6 hB
  rw [hcard] at hlow
  have hB10 : (10:ℝ) ≤ 2*(B:ℝ) := by
    have : (5:ℝ) ≤ (B:ℝ) := by exact_mod_cast hB
    linarith
  have hx4 : (4:ℝ) ≤ (2*(B:ℝ)) ^ (NN d n) := by
    have h1 : (10:ℝ)^6 ≤ (2*(B:ℝ))^6 := pow_le_pow_left₀ (by norm_num) hB10 6
    have h2 : (2*(B:ℝ))^6 ≤ (2*(B:ℝ))^(NN d n) :=
      pow_le_pow_right₀ (by linarith) hN6
    linarith [h1, h2]
  have hmono : (2*(B:ℝ)) ^ (NN d n) ≤ (2*(B:ℝ)+1) ^ (NN d n) :=
    pow_le_pow_left₀ (by positivity) (by linarith) _
  linarith [hlow, hsumB, hx4, hmono]

/-- `primCount_lower`: the number of primitive coefficient vectors of height `≤ A` is at
least `c · A^{N_{d,n}}` for some `c > 0` and all large `A`, for all `2 ≤ d`, `3 ≤ n`. -/
theorem primCount_lower (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ A in atTop,
      c * A ^ Work.HP.NN d n ≤ Work.HP.primCount d n A (fun _ => True) := by
  classical
  have hN6 : 6 ≤ NN d n := NN_ge_six d n hd hn
  have hNpos : (0:ℝ) < (NN d n : ℝ) := by exact_mod_cast (by omega : 0 < NN d n)
  have hs : 0 < Real.sqrt (NN d n : ℝ) := Real.sqrt_pos.mpr hNpos
  refine ⟨1 / (2 * Real.sqrt (NN d n : ℝ) ^ NN d n), ?_, ?_⟩
  · exact div_pos one_pos (mul_pos two_pos (pow_pos hs _))
  · filter_upwards [eventually_ge_atTop (5 * Real.sqrt (NN d n : ℝ))] with A hA
    set B : ℕ := ⌊A / Real.sqrt (NN d n : ℝ)⌋₊ with hB
    have hAs : (0:ℝ) ≤ A := le_trans (by positivity) hA
    have hdiv_nonneg : 0 ≤ A / Real.sqrt (NN d n : ℝ) := div_nonneg hAs (le_of_lt hs)
    have hBle : (B : ℝ) ≤ A / Real.sqrt (NN d n : ℝ) := by
      rw [hB]; exact Nat.floor_le hdiv_nonneg
    have hBlt : A / Real.sqrt (NN d n : ℝ) < (B:ℝ) + 1 := by
      rw [hB]; exact Nat.lt_floor_add_one _
    have hB5 : 5 ≤ B := by
      have h5 : (5:ℝ) ≤ A / Real.sqrt (NN d n : ℝ) := by
        rw [le_div_iff₀ hs]; linarith [hA]
      exact Nat.le_floor h5
    -- Step 1: the primitive vectors of the box lie in the height ball.
    have hcount1 : (((Fintype.piFinset (fun _ : Mon d n => Finset.Icc (-(B : ℤ)) (B : ℤ))).filter
        (fun a => Finset.univ.gcd a = 1)).card : ℝ) ≤ primCount d n A (fun _ => True) := by
      have hsub : ((Fintype.piFinset (fun _ : Mon d n => Finset.Icc (-(B : ℤ)) (B : ℤ))).filter
          (fun a => Finset.univ.gcd a = 1) : Set (Mon d n → ℤ)) ⊆
            primSet d n A (fun _ => True) := by
        intro a ha
        rw [Finset.mem_coe, Finset.mem_filter] at ha
        obtain ⟨hain, hprim⟩ := ha
        rw [Fintype.mem_piFinset] at hain
        refine ⟨hprim, ?_, trivial⟩
        have hcoord : ∀ m, |(a m : ℝ)| ≤ (B : ℝ) := by
          intro m
          have h' : (|a m| : ℤ) ≤ (B : ℤ) := abs_le.mpr (Finset.mem_Icc.mp (hain m))
          exact_mod_cast h'
        have hsq : ∑ m, ((a m : ℝ))^2 ≤ (NN d n : ℝ) * (B:ℝ)^2 := by
          calc ∑ m, ((a m : ℝ))^2 ≤ ∑ m, (B:ℝ)^2 :=
                Finset.sum_le_sum (fun m _ => by rw [sq_le_sq]; simpa using hcoord m)
            _ = (NN d n : ℝ) * (B:ℝ)^2 := by
                rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        calc eNorm a = Real.sqrt (∑ m, ((a m : ℝ))^2) := rfl
          _ ≤ Real.sqrt ((NN d n : ℝ) * (B:ℝ)^2) := Real.sqrt_le_sqrt hsq
          _ = Real.sqrt (NN d n : ℝ) * B := by
                rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity)]
          _ ≤ A := by
                have h := hBle
                rw [le_div_iff₀ hs] at h
                linarith
      have h := Set.ncard_le_ncard hsub (primSet_finite d n A (fun _ => True))
      simp only [Set.ncard_coe_finset] at h
      have hh : (((Fintype.piFinset (fun _ : Mon d n => Finset.Icc (-(B : ℤ)) (B : ℤ))).filter
          (fun a => Finset.univ.gcd a = 1)).card : ℝ) ≤
            ((primSet d n A (fun _ => True)).ncard : ℝ) := by
        exact_mod_cast h
      simpa only [primCount] using hh
    -- Step 2: the box lower bound.
    have hPB : (1/2) * (2*(B:ℝ)) ^ (NN d n) ≤
        (((Fintype.piFinset (fun _ : Mon d n => Finset.Icc (-(B : ℤ)) (B : ℤ))).filter
          (fun a => Finset.univ.gcd a = 1)).card : ℝ) :=
      box_prim_lower d n hN6 B hB5
    -- Step 3: compare `A` with `2B`, where `B = ⌊A / √N⌋`.
    have hB2 : A / Real.sqrt (NN d n : ℝ) ≤ 2*(B:ℝ) := by
      have h2 : (2:ℝ) ≤ A / Real.sqrt (NN d n : ℝ) := by
        rw [le_div_iff₀ hs]; linarith [hA]
      linarith [hBlt, hB5, h2]
    have hstep : 1 / (2 * Real.sqrt (NN d n : ℝ) ^ NN d n) * A ^ (NN d n) ≤
        (1/2) * (2*(B:ℝ)) ^ (NN d n) := by
      have h0 : (0:ℝ) ≤ A / Real.sqrt (NN d n : ℝ) := div_nonneg hAs (le_of_lt hs)
      have hpow := pow_le_pow_left₀ h0 hB2 (NN d n)
      have heq : 1 / (2 * Real.sqrt (NN d n : ℝ) ^ NN d n) * A ^ (NN d n)
          = (1/2) * (A / Real.sqrt (NN d n : ℝ)) ^ (NN d n) := by
        rw [div_pow]
        field_simp
      rw [heq]
      linarith [hpow]
    exact le_trans hstep (le_trans hPB hcount1)

end Work.HP.DN
