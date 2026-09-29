import Mathlib
import Submission.Work.MainP.basic

namespace Work.MainP

/-- Product of a family of nonnegative reals strictly dominated pointwise by another family. -/
lemma prod_lt_prod_of_nonneg {ι : Type*} [DecidableEq ι] {s : Finset ι} (hs : s.Nonempty)
    {f g : ι → ℝ} (hf : ∀ i ∈ s, 0 ≤ f i) (h : ∀ i ∈ s, f i < g i) :
    ∏ i ∈ s, f i < ∏ i ∈ s, g i := by
  obtain ⟨j, hj⟩ := hs
  rw [← Finset.mul_prod_erase _ _ hj, ← Finset.mul_prod_erase _ _ hj]
  rcases eq_or_lt_of_le (hf j hj) with h0 | h0
  · rw [← h0, zero_mul]
    have hposg : 0 < g j := lt_of_le_of_lt (hf j hj) (h j hj)
    have hposP : 0 < ∏ i ∈ s.erase j, g i := by
      apply Finset.prod_pos
      intro i hi
      exact lt_of_le_of_lt (hf i (Finset.mem_of_mem_erase hi)) (h i (Finset.mem_of_mem_erase hi))
    positivity
  · have hPle : ∏ x ∈ s.erase j, f x ≤ ∏ x ∈ s.erase j, g x := by
      apply Finset.prod_le_prod₀
      · intro i hi; exact hf i (Finset.mem_of_mem_erase hi)
      · intro i hi; exact le_of_lt (h i (Finset.mem_of_mem_erase hi))
    have hPg : 0 < ∏ x ∈ s.erase j, g x := by
      apply Finset.prod_pos
      intro i hi
      exact lt_of_le_of_lt (hf i (Finset.mem_of_mem_erase hi)) (h i (Finset.mem_of_mem_erase hi))
    calc f j * ∏ x ∈ s.erase j, f x
        ≤ f j * ∏ x ∈ s.erase j, g x := mul_le_mul_of_nonneg_left hPle (le_of_lt h0)
      _ < g j * ∏ x ∈ s.erase j, g x := mul_lt_mul_of_pos_right (h j hj) hPg

/-- A list of naturals of length `m`, read off with `getD`, has its `ℝ`-product as the product
over `Fin m`. -/
lemma prod_cast_ofFn {l : List ℕ} {m : ℕ} (h : l.length = m) :
    (l.prod : ℝ) = ∏ i : Fin m, (l.getD i 0 : ℝ) := by
  rw [Work.MainP.List.prod_eq_ofFn_getD h, List.prod_ofFn]
  exact Nat.cast_prod _ _

/-- `⌈n/b⌉ = (n+b-1)/b` is strictly below `n/b + 1` in `ℝ` (for `b ≥ 1`). -/
lemma ceilDiv_cast_lt (n b : ℕ) (hb : 1 ≤ b) :
    (((n + b - 1) / b : ℕ) : ℝ) < (n : ℝ) / b + 1 := by
  have hb0 : (0 : ℝ) < b := by exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hb
  have h1 : (n + b - 1) / b * b ≤ n + b - 1 := Nat.div_mul_le_self _ _
  have h2 : (n + b - 1) / b * b < n + b := lt_of_le_of_lt h1 (by omega)
  have h3 : (((n + b - 1) / b : ℕ) : ℝ) * b < (n : ℝ) + b := by
    calc (((n + b - 1) / b : ℕ) : ℝ) * b
        = (((n + b - 1) / b * b : ℕ) : ℝ) := by push_cast; ring
      _ < ((n + b : ℕ) : ℝ) := by exact_mod_cast h2
      _ = (n : ℝ) + b := by push_cast; ring
  have h5 : ((n : ℝ) / b + 1) * b = (n : ℝ) + b := by
    rw [add_mul, div_mul_cancel₀ _ (ne_of_gt hb0), one_mul]
  have h6 : (((n + b - 1) / b : ℕ) : ℝ) * b < ((n : ℝ) / b + 1) * b := by
    rw [h5]; exact h3
  exact lt_of_mul_lt_mul_right h6 (le_of_lt hb0)

/-- The size of `S = ∏ sᵢ` for `ParamOK n ts ss`, with `T = Tpar n`, `S = ss.prod`:
`S ≤ T` (each `sᵢ ≤ (1-1/(4d))tᵢ ≤ tᵢ`), `T < 2S` (each `sᵢ > (1-1/(2d))tᵢ`, so
`S > (1-1/(2d))^d T ≥ T/2` by Bernoulli `one_add_mul_le_pow`, strict), and
`2⌈n/b⌉ ≤ S+1` (`S > T/2 ≥ 2n/b` from `4n ≤ T·b` and `2⌈n/b⌉ < 2n/b + 2`).
Products over ℝ: compare `∏ (2d·sᵢ) > ∏ ((2d-1)tᵢ)` in `ℕ` instead, then `((2d-1)/(2d))^d·T < S`. -/
theorem prodWindow (n : ℕ) (ts ss : List ℕ) (hOK : HvdH.ParamOK n ts ss)
    (h4n : 4 * n ≤ HvdH.Tpar n * HvdH.bpar n) (hb1 : 1 ≤ HvdH.bpar n) :
    ss.prod ≤ HvdH.Tpar n ∧ HvdH.Tpar n < 2 * ss.prod ∧
    2 * ((n + HvdH.bpar n - 1) / HvdH.bpar n) ≤ ss.prod + 1 := by
  obtain ⟨hlen_t, hlen_s, hpair_t, hprod_t, hmem, hbound, hcop, hodd⟩ := hOK
  have hDpos : 0 < HvdH.D := by norm_num [HvdH.D]
  have hDne : (HvdH.D : ℝ) ≠ 0 := by positivity
  -- windows
  set B : ℝ := 1 - 1 / (2 * (HvdH.D : ℝ)) with hBdef
  set A : ℝ := 1 - 1 / (4 * (HvdH.D : ℝ)) with hAdef
  have hBcast : (2 : ℝ) / (4 * (HvdH.D : ℝ)) = 1 / (2 * (HvdH.D : ℝ)) := by
    field_simp; ring
  have hA_le_one : A ≤ 1 := by
    have : (0 : ℝ) ≤ 1 / (4 * (HvdH.D : ℝ)) := by positivity
    rw [hAdef]; linarith
  have hA_nonneg : 0 ≤ A := by
    have hle : 1 / (4 * (HvdH.D : ℝ)) ≤ 1 := by
      rw [div_le_one (by positivity)]; norm_num [HvdH.D]
    rw [hAdef]; linarith
  have hB_pos : 0 < B := by
    have hlt : 1 / (2 * (HvdH.D : ℝ)) < 1 := by
      rw [div_lt_one (by positivity)]; norm_num [HvdH.D]
    rw [hBdef]; linarith
  have hptB : ∀ i : Fin HvdH.D, B * (ts.getD i 0 : ℝ) < (ss.getD i 0 : ℝ) := by
    intro i
    have h := (hbound i.val i.isLt).1
    rw [hBcast] at h
    exact h
  have hptA : ∀ i : Fin HvdH.D, (ss.getD i 0 : ℝ) ≤ A * (ts.getD i 0 : ℝ) := by
    intro i
    have h := (hbound i.val i.isLt).2
    rw [hAdef] at h
    exact h
  have hssprod : (ss.prod : ℝ) = ∏ i : Fin HvdH.D, (ss.getD i 0 : ℝ) := prod_cast_ofFn hlen_s
  have htsprod : (ts.prod : ℝ) = ∏ i : Fin HvdH.D, (ts.getD i 0 : ℝ) := prod_cast_ofFn hlen_t
  have hone : (1 : ℝ) ≤ (HvdH.Tpar n : ℝ) := by
    rw [HvdH.Tpar]; push_cast; exact_mod_cast Nat.one_le_two_pow
  -- Part 1: S ≤ T
  have hstep1 : ∏ i : Fin HvdH.D, (ss.getD i 0 : ℝ) ≤ ∏ i : Fin HvdH.D, (ts.getD i 0 : ℝ) := by
    calc ∏ i : Fin HvdH.D, (ss.getD i 0 : ℝ)
        ≤ ∏ i : Fin HvdH.D, A * (ts.getD i 0 : ℝ) :=
          Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hptA i)
      _ ≤ ∏ i : Fin HvdH.D, (ts.getD i 0 : ℝ) := by
          apply Finset.prod_le_prod₀
          · intro i _
            exact mul_nonneg hA_nonneg (Nat.cast_nonneg _)
          · intro i _
            calc A * (ts.getD i 0 : ℝ) ≤ 1 * (ts.getD i 0 : ℝ) :=
                  mul_le_mul_of_nonneg_right hA_le_one (Nat.cast_nonneg _)
              _ = (ts.getD i 0 : ℝ) := one_mul _
  have hpart1 : ss.prod ≤ HvdH.Tpar n := by
    have hreal : (ss.prod : ℝ) ≤ (HvdH.Tpar n : ℝ) := by
      rw [hssprod, ← hprod_t, htsprod]
      exact hstep1
    exact_mod_cast hreal
  -- Part 2: T < 2 S
  have huniv : (Finset.univ : Finset (Fin HvdH.D)).Nonempty :=
    ⟨⟨0, hDpos⟩, Finset.mem_univ _⟩
  have hstep2 : ∏ i : Fin HvdH.D, B * (ts.getD i 0 : ℝ) <
      ∏ i : Fin HvdH.D, (ss.getD i 0 : ℝ) :=
    prod_lt_prod_of_nonneg huniv (fun i _ => mul_nonneg (le_of_lt hB_pos) (Nat.cast_nonneg _))
      (fun i _ => hptB i)
  have hsplit2 : ∏ i : Fin HvdH.D, B * (ts.getD i 0 : ℝ) =
      B ^ HvdH.D * ∏ i : Fin HvdH.D, (ts.getD i 0 : ℝ) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hS_gt : B ^ HvdH.D * (HvdH.Tpar n : ℝ) < (ss.prod : ℝ) := by
    rw [hssprod, ← hprod_t, htsprod, ← hsplit2]
    exact hstep2
  have hbern : (1 : ℝ) / 2 ≤ B ^ HvdH.D := by
    have ha : (-2 : ℝ) ≤ -(1 / (2 * (HvdH.D : ℝ))) := by
      have hle : 1 / (2 * (HvdH.D : ℝ)) ≤ 2 := by
        rw [div_le_iff₀ (by positivity)]; norm_num [HvdH.D]
      linarith
    have h := one_add_mul_le_pow ha HvdH.D
    have hc : (HvdH.D : ℝ) * (1 / (2 * (HvdH.D : ℝ))) = 1 / 2 := by
      field_simp
    have hbase : (1 : ℝ) + -(1 / (2 * (HvdH.D : ℝ))) = B := by rw [hBdef]; ring
    rw [hbase] at h
    have hlhs : (1 : ℝ) + (HvdH.D : ℝ) * (-(1 / (2 * (HvdH.D : ℝ)))) = 1 / 2 := by
      rw [mul_neg, hc]; norm_num
    linarith
  have hhalf : (1 / 2 : ℝ) * (HvdH.Tpar n : ℝ) < (ss.prod : ℝ) :=
    calc (1 / 2 : ℝ) * (HvdH.Tpar n : ℝ) ≤ B ^ HvdH.D * (HvdH.Tpar n : ℝ) :=
          mul_le_mul_of_nonneg_right hbern (le_trans zero_le_one hone)
      _ < (ss.prod : ℝ) := hS_gt
  have hpart2 : HvdH.Tpar n < 2 * ss.prod := by
    have : (HvdH.Tpar n : ℝ) < 2 * (ss.prod : ℝ) := by linarith
    exact_mod_cast this
  -- Part 3
  have hb0 : (0 : ℝ) < (HvdH.bpar n : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one hb1
  have h4nr : (4 : ℝ) * (n : ℝ) ≤ (HvdH.Tpar n : ℝ) * (HvdH.bpar n : ℝ) := by
    exact_mod_cast h4n
  have hTge : (4 * (n : ℝ)) / (HvdH.bpar n : ℝ) ≤ (HvdH.Tpar n : ℝ) := by
    rw [div_le_iff₀ hb0]
    linarith
  have h2nb : 2 * ((n : ℝ) / (HvdH.bpar n : ℝ)) < (ss.prod : ℝ) := by
    have h4 : (4 * (n : ℝ)) / (HvdH.bpar n : ℝ) =
        4 * ((n : ℝ) / (HvdH.bpar n : ℝ)) := by ring
    rw [h4] at hTge
    linarith [hTge, hhalf]
  have hceil := ceilDiv_cast_lt n (HvdH.bpar n) hb1
  have hmain : (2 : ℝ) * (((n + HvdH.bpar n - 1) / HvdH.bpar n : ℕ) : ℝ) <
      (ss.prod : ℝ) + 2 := by
    linarith [hceil, h2nb]
  have hpart3 : 2 * ((n + HvdH.bpar n - 1) / HvdH.bpar n) ≤ ss.prod + 1 := by
    have h' : ((2 * ((n + HvdH.bpar n - 1) / HvdH.bpar n) : ℕ) : ℝ) <
        ((ss.prod + 2 : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      exact hmain
    have := Nat.cast_lt.mp h'
    omega
  exact ⟨hpart1, hpart2, hpart3⟩

end Work.MainP
