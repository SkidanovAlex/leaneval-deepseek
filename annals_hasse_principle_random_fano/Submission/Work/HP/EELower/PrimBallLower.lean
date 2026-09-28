import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.PairsAux
import Submission.Work.HP.PrimBoxDefs
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.MDEstimates.PrimDecomp

/-!
# Primitive vectors in a Euclidean ball

For `k ≥ 4` the Euclidean ball of radius `X` in `ℤ^k` contains `≫ X^k` primitive vectors.

The proof is the standard box count.  Put `N = ⌊X/(2√k)⌋`, so that the coordinate box
`[-N,N]^k` is contained in the ball of radius `X`.  A vector of the box is either `0`, primitive,
or non-primitive with `2 ≤ g ≤ N` where `g` is its coordinate gcd; in the last case it is
`g • b` with `b` primitive and `b` in the box of radius `⌊N/g⌋` (`Work.HP.MDEstimates.pFac`,
`pDir`, `scale`).  Hence

`#prim(box N) ≥ (2N+1)^k − 1 − Σ_{g=2}^{N} (2⌊N/g⌋+1)^k`,

and the sum is at most `(1/2)(2N+1)^k` because `2⌊N/g⌋+1 ≤ 3N/g` and
`Σ_{g≥2} g^{-k} ≤ 2^{-(k-4)} Σ_{g≥2} g^{-4}` with `Σ_{g≥2} g^{-4} ≤ 1/16 + 1/81 + 1/81`, the last
bound coming from the telescoping inequality `1/g^4 ≤ (1/3)(1/(g-1)^3 − 1/g^3)` for `g ≥ 3`.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

open Finset

namespace Work.HP.EELower

open Work.HP
open Work.HP.MDEstimates

/-! ## A telescoping bound for `∑ g^{-4}` -/

private lemma sum_Icc_sub_eq (f : ℕ → ℝ) {a B : ℕ} (haB : a ≤ B) :
    ∑ g ∈ Finset.Icc a B, (f (g - 1) - f g) = f (a - 1) - f B := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le haB
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.add_succ, Finset.sum_Icc_succ_top (by omega)]
      rw [ih (by omega)]
      have h1 : (a + m + 1 - 1 : ℕ) = a + m := by omega
      rw [h1]
      ring

private lemma inv_pow4_telescope (g : ℕ) (hg : 3 ≤ g) :
    (1 / (g : ℝ)) ^ 4
      ≤ (1 / 3) * (1 / (((g - 1 : ℕ) : ℝ)) ^ 3 - 1 / (g : ℝ) ^ 3) := by
  rw [div_pow, one_pow]
  have hg1 : 1 ≤ g := by omega
  set x : ℝ := ((g - 1 : ℕ) : ℝ) with hxdef
  have hx0 : 0 < x := by
    rw [hxdef]
    exact_mod_cast (by omega : 0 < g - 1)
  have hg' : (g : ℝ) = x + 1 := by
    rw [hxdef]
    have h : g - 1 + 1 = g := Nat.sub_add_cancel hg1
    rw [← h]
    push_cast
    ring
  rw [hg', div_le_iff₀ (by positivity : (0 : ℝ) < (x + 1) ^ 4)]
  have hval : (1 / 3 : ℝ) * (1 / x ^ 3 - 1 / (x + 1) ^ 3) * (x + 1) ^ 4
      = ((x + 1) ^ 3 - x ^ 3) * (x + 1) / (3 * x ^ 3) := by
    field_simp
  rw [hval, le_div_iff₀ (by positivity : (0 : ℝ) < 3 * x ^ 3)]
  nlinarith [sq_nonneg x, hx0]

/-- `∑_{g=2}^{N} g^{-4} ≤ 1/16 + 1/81 + 1/81`. -/
private lemma sum_four_le (N : ℕ) :
    ∑ g ∈ Finset.Icc 2 N, (1 / (g : ℝ)) ^ 4 ≤ 1 / 16 + 1 / 81 + 1 / 81 := by
  rcases lt_or_ge N 4 with hN | hN
  · have hsub : Finset.Icc 2 N ⊆ Finset.Icc 2 3 := by
      intro g hg
      rw [Finset.mem_Icc] at hg ⊢
      omega
    have h3 : ∑ g ∈ Finset.Icc 2 N, (1 / (g : ℝ)) ^ 4
        ≤ ∑ g ∈ (Finset.Icc 2 3 : Finset ℕ), (1 / (g : ℝ)) ^ 4 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro g _ _
      positivity
    have hval : ∑ g ∈ (Finset.Icc 2 3 : Finset ℕ), (1 / (g : ℝ)) ^ 4 = 1 / 16 + 1 / 81 := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num]
      rw [Finset.sum_Icc_succ_top (by norm_num : 2 ≤ (2 : ℕ) + 1)]
      rw [Finset.Icc_self, Finset.sum_singleton]
      norm_num
    linarith [h3, hval]
  · have hsplit1 : Finset.Icc 2 N = insert 2 (Finset.Icc 3 N) := by
      ext g
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have h2n : (2 : ℕ) ∉ Finset.Icc 3 N := by simp [Finset.mem_Icc]
    have hsplit2 : Finset.Icc 3 N = insert 3 (Finset.Icc 4 N) := by
      ext g
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have h3n : (3 : ℕ) ∉ Finset.Icc 4 N := by simp [Finset.mem_Icc]
    rw [hsplit1, Finset.sum_insert h2n, hsplit2, Finset.sum_insert h3n]
    have htail : ∑ g ∈ Finset.Icc 4 N, (1 / (g : ℝ)) ^ 4 ≤ 1 / 81 := by
      have hb : ∑ g ∈ Finset.Icc 4 N, (1 / (g : ℝ)) ^ 4
          ≤ ∑ g ∈ Finset.Icc 4 N,
              (1 / 3) * (1 / (((g - 1 : ℕ) : ℝ)) ^ 3 - 1 / (g : ℝ) ^ 3) :=
        Finset.sum_le_sum (fun g hg => by
          have hg4 : 3 ≤ g := by rw [Finset.mem_Icc] at hg; omega
          exact inv_pow4_telescope g hg4)
      have hsum := sum_Icc_sub_eq (fun g : ℕ => 1 / ((g : ℝ)) ^ 3) (a := 4) (B := N) hN
      rw [← Finset.mul_sum, hsum] at hb
      have h43 : (1 : ℝ) / (((4 - 1 : ℕ) : ℝ)) ^ 3 = 1 / 27 := by norm_num
      rw [h43] at hb
      have hN0 : (0 : ℝ) < (N : ℝ) := by positivity
      have hpos : 0 < 1 / (N : ℝ) ^ 3 := by positivity
      have hle : (1 / 3 : ℝ) * (1 / 27 - 1 / (N : ℝ) ^ 3) ≤ 1 / 81 := by nlinarith [hpos]
      linarith [hb, hle]
    linarith [htail]

/-! ## The coordinate box contains many primitive vectors -/

/-- `#prim([-N,N]^k) ≥ (1/4)(2N+1)^k` for `k ≥ 4` and `N ≥ 100`. -/
private lemma box_prim_count (N k : ℕ) (hk : 4 ≤ k) (hN : 100 ≤ N) :
    (1 / 4) * (2 * (N : ℝ) + 1) ^ k
      ≤ (((boxFinset N k).filter IsPrim).card : ℝ) := by
  classical
  set B : Finset (Fin k → ℤ) := boxFinset N k with hBdef
  set U : Finset (Fin k → ℤ) :=
    (Finset.Icc 2 N).biUnion
      (fun g : ℕ => ((boxFinset (N / g) k).filter IsPrim).image (fun b => scale g b))
    with hUdef
  -- every non-primitive vector of the box other than `0` is a scaled primitive box vector
  have hcover : B.filter (fun a => ¬ IsPrim a) ⊆ insert (0 : Fin k → ℤ) U := by
    intro a ha
    rw [Finset.mem_filter] at ha
    obtain ⟨haB, haP⟩ := ha
    rw [Finset.mem_insert]
    by_cases h0 : a = 0
    · exact Or.inl h0
    · refine Or.inr ?_
      rw [hUdef, Finset.mem_biUnion]
      set g : ℕ := pFac a with hgdef
      set b : Fin k → ℤ := pDir a with hbdef
      have hcoe : ((g : ℕ) : ℤ) = Finset.univ.gcd a := by
        rw [hgdef]
        exact coe_pFac a
      have hgz : Finset.univ.gcd a ≠ 0 := gcd_ne_zero_of_ne_zero h0
      have hscale : scale g b = a := by
        rw [hgdef, hbdef]
        exact scale_pFac_pDir h0
      have hg2 : 2 ≤ g := by
        have hgnz : g ≠ 0 := by
          intro hgg
          have h : Finset.univ.gcd a = 0 := by rw [← hcoe, hgg]; norm_num
          exact hgz h
        have hgne1 : g ≠ 1 := by
          intro hgg
          apply haP
          show Finset.univ.gcd a = 1
          rw [← hcoe, hgg]
          norm_num
        omega
      have hgN : g ≤ N := by
        have ha0 : ∃ i, a i ≠ 0 := by
          by_contra h
          push Not at h
          exact h0 (funext h)
        obtain ⟨i, hi⟩ := ha0
        have hdvd : Finset.univ.gcd a ∣ a i := Finset.gcd_dvd (Finset.mem_univ i)
        have hle : (Finset.univ.gcd a).natAbs ≤ (a i).natAbs :=
          Int.natAbs_le_of_dvd_ne_zero hdvd hi
        have h2 : (a i).natAbs ≤ N := by
          have h3 := mem_boxFinset.mp haB i
          rw [Int.abs_eq_natAbs] at h3
          exact_mod_cast h3
        calc g = (Finset.univ.gcd a).natAbs := hgdef
          _ ≤ (a i).natAbs := hle
          _ ≤ N := h2
      have hbmem : b ∈ boxFinset (N / g) k := by
        rw [mem_boxFinset]
        intro i
        have hcoord : ((a i).natAbs : ℤ) ≤ (N : ℤ) := by
          have h3 := mem_boxFinset.mp haB i
          rw [Int.abs_eq_natAbs] at h3
          exact h3
        have hmul : (g : ℤ) * b i = a i := congrFun hscale i
        have h1 : (b i).natAbs * g ≤ N := by
          have h2 : ((g : ℤ) * b i).natAbs = g * (b i).natAbs := by
            rw [Int.natAbs_mul, Int.natAbs_natCast]
          have h3 : g * (b i).natAbs ≤ N := by
            rw [← h2, hmul]
            exact_mod_cast hcoord
          rwa [mul_comm] at h3
        have h3 : (b i).natAbs ≤ N / g :=
          (Nat.le_div_iff_mul_le (by omega : 0 < g)).mpr h1
        show |b i| ≤ (((N / g : ℕ)) : ℤ)
        rw [Int.abs_eq_natAbs]
        exact_mod_cast h3
      exact ⟨g, Finset.mem_Icc.mpr ⟨hg2, hgN⟩,
        Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨hbmem, isPrim_pDir h0⟩, hscale⟩⟩
  -- `#U` is at most the sum of the box sizes
  have hUcard : (U.card : ℝ)
      ≤ ∑ g ∈ Finset.Icc 2 N, (2 * (((N / g : ℕ)) : ℝ) + 1) ^ k := by
    have h1 : U.card ≤ ∑ g ∈ Finset.Icc 2 N,
        (((boxFinset (N / g) k).filter IsPrim).image (fun b => scale g b)).card := by
      rw [hUdef]
      exact Finset.card_biUnion_le
    have h2 : ∀ g ∈ Finset.Icc 2 N,
        ((((boxFinset (N / g) k).filter IsPrim).image (fun b => scale g b)).card : ℝ)
          ≤ (2 * (((N / g : ℕ)) : ℝ) + 1) ^ k := by
      intro g _
      have h3 := Finset.card_image_le (s := (boxFinset (N / g) k).filter IsPrim)
        (f := fun b => scale g b)
      have h4 := Finset.card_filter_le (s := boxFinset (N / g) k) (p := IsPrim)
      have h5 : ((((boxFinset (N / g) k).filter IsPrim).image (fun b => scale g b)).card : ℝ)
          ≤ ((boxFinset (N / g) k).card : ℝ) := by
        exact_mod_cast le_trans h3 h4
      rw [card_boxFinset] at h5
      push_cast at h5
      exact h5
    calc (U.card : ℝ)
        ≤ ((∑ g ∈ Finset.Icc 2 N,
            (((boxFinset (N / g) k).filter IsPrim).image (fun b => scale g b)).card : ℕ) : ℝ) := by
          exact_mod_cast h1
      _ = ∑ g ∈ Finset.Icc 2 N,
            ((((boxFinset (N / g) k).filter IsPrim).image (fun b => scale g b)).card : ℝ) := by
          push_cast
          rfl
      _ ≤ ∑ g ∈ Finset.Icc 2 N, (2 * (((N / g : ℕ)) : ℝ) + 1) ^ k := Finset.sum_le_sum h2
  -- the sum is at most half of the leading term
  have hsum : ∑ g ∈ Finset.Icc 2 N, (2 * (((N / g : ℕ)) : ℝ) + 1) ^ k
      ≤ (1 / 2) * (2 * (N : ℝ) + 1) ^ k := by
    have hterm : ∀ g ∈ Finset.Icc 2 N,
        (2 * (((N / g : ℕ)) : ℝ) + 1) ^ k ≤ (3 * (N : ℝ) / g) ^ k := by
      intro g hg
      have hg2 : 2 ≤ g := (Finset.mem_Icc.mp hg).1
      have hgN : g ≤ N := (Finset.mem_Icc.mp hg).2
      have hgpos : (0 : ℝ) < (g : ℝ) := by exact_mod_cast (by omega : 1 ≤ g)
      have h1 : (((N / g : ℕ)) : ℝ) ≤ (N : ℝ) / g := Nat.cast_div_le
      have h3 : (1 : ℝ) ≤ (N : ℝ) / g :=
        (one_le_div hgpos).mpr (by exact_mod_cast hgN)
      have h4 : 3 * (N : ℝ) / g = 3 * ((N : ℝ) / g) := by ring
      have hlin : 2 * (((N / g : ℕ)) : ℝ) + 1 ≤ 3 * (N : ℝ) / g := by
        rw [h4]
        linarith
      exact pow_le_pow_left₀ (by positivity) hlin k
    have hstep1 : ∑ g ∈ Finset.Icc 2 N, (2 * (((N / g : ℕ)) : ℝ) + 1) ^ k
        ≤ (3 * (N : ℝ)) ^ k * ∑ g ∈ Finset.Icc 2 N, (1 / (g : ℝ)) ^ k := by
      calc ∑ g ∈ Finset.Icc 2 N, (2 * (((N / g : ℕ)) : ℝ) + 1) ^ k
          ≤ ∑ g ∈ Finset.Icc 2 N, (3 * (N : ℝ) / g) ^ k := Finset.sum_le_sum hterm
        _ = (3 * (N : ℝ)) ^ k * ∑ g ∈ Finset.Icc 2 N, (1 / (g : ℝ)) ^ k := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun g hg => ?_)
            rw [div_pow, div_pow, one_pow, mul_one_div]
    have hstep2 : ∑ g ∈ Finset.Icc 2 N, (1 / (g : ℝ)) ^ k
        ≤ (1 / 2) ^ (k - 4) * (1 / 16 + 1 / 81 + 1 / 81) := by
      have hpoint : ∀ g ∈ Finset.Icc 2 N,
          (1 / (g : ℝ)) ^ k ≤ (1 / 2) ^ (k - 4) * (1 / (g : ℝ)) ^ 4 := by
        intro g hgmem
        have hg2 : (2 : ℝ) ≤ (g : ℝ) := by
          exact_mod_cast (Finset.mem_Icc.mp hgmem).1
        have hgpos : (0 : ℝ) < (g : ℝ) := by linarith
        have hle : (1 : ℝ) / (g : ℝ) ≤ 1 / 2 := by
          rw [div_le_div_iff₀ hgpos (by norm_num : (0 : ℝ) < 2)]
          linarith
        have hsplit : (1 / (g : ℝ)) ^ k = (1 / (g : ℝ)) ^ (k - 4) * (1 / (g : ℝ)) ^ 4 := by
          rw [← pow_add]
          congr 1
          omega
        have h2 : (1 / (g : ℝ)) ^ (k - 4) ≤ (1 / 2) ^ (k - 4) :=
          pow_le_pow_left₀ (by positivity) hle (k - 4)
        calc (1 / (g : ℝ)) ^ k
            = (1 / (g : ℝ)) ^ (k - 4) * (1 / (g : ℝ)) ^ 4 := hsplit
          _ ≤ (1 / 2) ^ (k - 4) * (1 / (g : ℝ)) ^ 4 :=
              mul_le_mul_of_nonneg_right h2 (by positivity)
      calc ∑ g ∈ Finset.Icc 2 N, (1 / (g : ℝ)) ^ k
          ≤ ∑ g ∈ Finset.Icc 2 N, (1 / 2) ^ (k - 4) * (1 / (g : ℝ)) ^ 4 :=
            Finset.sum_le_sum hpoint
        _ = (1 / 2) ^ (k - 4) * ∑ g ∈ Finset.Icc 2 N, (1 / (g : ℝ)) ^ 4 := by
            rw [Finset.mul_sum]
        _ ≤ (1 / 2) ^ (k - 4) * (1 / 16 + 1 / 81 + 1 / 81) :=
            mul_le_mul_of_nonneg_left (sum_four_le N) (by positivity)
    have hconst : (3 * (N : ℝ)) ^ k * ((1 / 2) ^ (k - 4) * (1 / 16 + 1 / 81 + 1 / 81))
        ≤ (1 / 2) * (2 * (N : ℝ) + 1) ^ k := by
      set C : ℝ := 1 / 16 + 1 / 81 + 1 / 81 with hCdef
      have h34 : (3 / 4 : ℝ) ^ k ≤ (3 / 4) ^ 4 :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hk
      have hkey : 16 * C * (3 / 4 : ℝ) ^ k ≤ 1 / 2 := by
        calc 16 * C * (3 / 4 : ℝ) ^ k ≤ 16 * C * (3 / 4) ^ 4 :=
              mul_le_mul_of_nonneg_left h34 (by positivity)
          _ ≤ 1 / 2 := by rw [hCdef]; norm_num
      have hhalf : (1 / 2 : ℝ) ^ (k - 4) = 16 * (1 / 2) ^ k := by
        have h1 : (1 / 2 : ℝ) ^ k = (1 / 2) ^ (k - 4) * (1 / 2) ^ 4 := by
          rw [← pow_add]
          congr 1
          omega
        have h2 : ((1 / 2 : ℝ)) ^ 4 = 1 / 16 := by norm_num
        rw [h2] at h1
        linarith
      have hprod : (3 * (N : ℝ)) ^ k * ((1 / 2) ^ (k - 4) * C)
          = 16 * C * ((3 * (N : ℝ)) * (1 / 2)) ^ k := by
        have h2 : (3 * (N : ℝ)) ^ k * (1 / 2) ^ k
            = ((3 * (N : ℝ)) * (1 / 2)) ^ k := by rw [← mul_pow]
        rw [hhalf]
        rw [show (3 * (N : ℝ)) ^ k * (16 * (1 / 2) ^ k * C)
            = 16 * C * ((3 * (N : ℝ)) ^ k * (1 / 2) ^ k) by ring]
        rw [h2]
      rw [hprod]
      have h100 : (100 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hle : (3 * (N : ℝ)) * (1 / 2) ≤ (3 / 4) * (2 * (N : ℝ) + 1) := by linarith
      calc 16 * C * ((3 * (N : ℝ)) * (1 / 2)) ^ k
          ≤ 16 * C * ((3 / 4) * (2 * (N : ℝ) + 1)) ^ k :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hle k) (by positivity)
        _ = (16 * C * (3 / 4 : ℝ) ^ k) * (2 * (N : ℝ) + 1) ^ k := by
            rw [mul_pow]
            ring
        _ ≤ (1 / 2) * (2 * (N : ℝ) + 1) ^ k :=
            mul_le_mul_of_nonneg_right hkey (by positivity)
    calc ∑ g ∈ Finset.Icc 2 N, (2 * (((N / g : ℕ)) : ℝ) + 1) ^ k
        ≤ (3 * (N : ℝ)) ^ k * ∑ g ∈ Finset.Icc 2 N, (1 / (g : ℝ)) ^ k := hstep1
      _ ≤ (3 * (N : ℝ)) ^ k * ((1 / 2) ^ (k - 4) * (1 / 16 + 1 / 81 + 1 / 81)) :=
          mul_le_mul_of_nonneg_left hstep2 (by positivity)
      _ ≤ (1 / 2) * (2 * (N : ℝ) + 1) ^ k := hconst
  -- assemble
  have hBcard : ((B.card : ℕ) : ℝ) = (2 * (N : ℝ) + 1) ^ k := by
    rw [hBdef]
    exact_mod_cast card_boxFinset N k
  have hpart := Finset.card_filter_add_card_filter_not (s := B) (p := IsPrim)
  have hpartR : (((B.filter IsPrim).card : ℕ) : ℝ)
      + (((B.filter (fun a => ¬ IsPrim a)).card : ℕ) : ℝ) = (2 * (N : ℝ) + 1) ^ k := by
    rw [← hBcard]
    exact_mod_cast hpart
  have hU2 : (((B.filter (fun a => ¬ IsPrim a)).card : ℕ) : ℝ)
      ≤ (1 / 2) * (2 * (N : ℝ) + 1) ^ k + 1 := by
    have h1 : (B.filter (fun a => ¬ IsPrim a)).card
        ≤ (insert (0 : Fin k → ℤ) U).card := Finset.card_le_card hcover
    have h2 : (insert (0 : Fin k → ℤ) U).card ≤ U.card + 1 := Finset.card_insert_le _ _
    have h3 : (((insert (0 : Fin k → ℤ) U).card : ℕ) : ℝ) ≤ (U.card : ℝ) + 1 := by
      exact_mod_cast h2
    have h4 : (((B.filter (fun a => ¬ IsPrim a)).card : ℕ) : ℝ)
        ≤ ((insert (0 : Fin k → ℤ) U).card : ℝ) := by exact_mod_cast h1
    linarith [h4, h3, hUcard, hsum]
  have hbig : (4 : ℝ) ≤ (2 * (N : ℝ) + 1) ^ k := by
    have h100 : (100 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have h2 : (1 : ℝ) ≤ 2 * (N : ℝ) + 1 := by linarith
    have h1 : (4 : ℝ) ≤ 2 * (N : ℝ) + 1 := by linarith
    have h3 : (2 * (N : ℝ) + 1) ^ 1 ≤ (2 * (N : ℝ) + 1) ^ k :=
      pow_le_pow_right₀ h2 (by omega)
    have h4 : (2 * (N : ℝ) + 1) ≤ (2 * (N : ℝ) + 1) ^ k := by simpa using h3
    exact le_trans h1 h4
  linarith [hpartR, hU2, hbig]

/-! ## The lower bound -/

/-- The Euclidean ball of radius `X` in `ℤ^k` contains `≫ X^k` primitive vectors, for `k ≥ 4`
and all large `X`. -/
theorem prim_ball_lower_all (k : ℕ) (hk : 4 ≤ k) :
    ∃ c X₀ : ℝ, 0 < c ∧ 0 < X₀ ∧ ∀ X : ℝ, X₀ ≤ X →
      c * X ^ k ≤ ((({v : Fin k → ℤ | IsPrim v ∧ eNorm v ≤ X}).ncard : ℕ) : ℝ) := by
  have hsk : 0 < Real.sqrt (k : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < k))
  refine ⟨1 / (4 * (2 * Real.sqrt (k : ℝ)) ^ k), max 1 (400 * Real.sqrt (k : ℝ)), ?_, ?_, ?_⟩
  · positivity
  · positivity
  · intro X hX
    have hX1 : (1 : ℝ) ≤ X := le_trans (le_max_left _ _) hX
    have hX400 : 400 * Real.sqrt (k : ℝ) ≤ X := le_trans (le_max_right _ _) hX
    set N : ℕ := ⌊X / (2 * Real.sqrt (k : ℝ))⌋₊ with hNdef
    have hdiv : (200 : ℝ) ≤ X / (2 * Real.sqrt (k : ℝ)) := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 2 * Real.sqrt (k : ℝ))]
      linarith
    have hN100 : 100 ≤ N := by
      rw [hNdef]
      exact Nat.le_floor (by linarith : (100 : ℝ) ≤ X / (2 * Real.sqrt (k : ℝ)))
    have hNle : (N : ℝ) ≤ X / (2 * Real.sqrt (k : ℝ)) := by
      rw [hNdef]
      exact Nat.floor_le (by positivity)
    -- the box lies in the ball
    have hsub : ((((boxFinset N k).filter IsPrim) : Finset (Fin k → ℤ)) : Set (Fin k → ℤ))
        ⊆ {v : Fin k → ℤ | IsPrim v ∧ eNorm v ≤ X} := by
      intro v hv
      rw [Finset.mem_coe, Finset.mem_filter] at hv
      obtain ⟨hvbox, hvprim⟩ := hv
      refine ⟨hvprim, ?_⟩
      calc eNorm v ≤ (N : ℝ) * Real.sqrt k := eNorm_le_of_mem_boxFinset hvbox
        _ ≤ X := by
            have h1 : (N : ℝ) * Real.sqrt (k : ℝ) ≤ X / 2 := by
              have h2 := mul_le_mul_of_nonneg_right hNle (le_of_lt hsk)
              have h3 : (X / (2 * Real.sqrt (k : ℝ))) * Real.sqrt (k : ℝ) = X / 2 := by
                rw [div_mul_eq_mul_div, mul_div_mul_right X 2 (ne_of_gt hsk)]
              linarith [h2, h3]
            linarith
    have hfinite : ({v : Fin k → ℤ | IsPrim v ∧ eNorm v ≤ X}).Finite :=
      (MDBasic.finite_eNorm_le (ι := Fin k) X).subset (fun v hv => hv.2)
    have hcard : (((boxFinset N k).filter IsPrim).card : ℝ)
        ≤ ((({v : Fin k → ℤ | IsPrim v ∧ eNorm v ≤ X}).ncard : ℕ) : ℝ) := by
      have h := Set.ncard_le_ncard hsub hfinite
      rw [Set.ncard_coe_finset] at h
      exact_mod_cast h
    have hbox := box_prim_count N k hk hN100
    -- `2N + 1 ≥ X/(2√k)`
    have hNbig : X / (2 * Real.sqrt (k : ℝ)) ≤ 2 * (N : ℝ) + 1 := by
      have h1 : X / (2 * Real.sqrt (k : ℝ)) - 1 < (N : ℝ) := by
        have h := Nat.lt_floor_add_one (X / (2 * Real.sqrt (k : ℝ)))
        rw [hNdef]
        linarith
      have h2 : (1 : ℝ) ≤ X / (2 * Real.sqrt (k : ℝ)) := by linarith
      linarith
    have hpow : (X / (2 * Real.sqrt (k : ℝ))) ^ k ≤ (2 * (N : ℝ) + 1) ^ k :=
      pow_le_pow_left₀ (by positivity) hNbig k
    have hfinal : 1 / (4 * (2 * Real.sqrt (k : ℝ)) ^ k) * X ^ k
        ≤ (1 / 4) * (2 * (N : ℝ) + 1) ^ k := by
      have hXeq : X ^ k = (X / (2 * Real.sqrt (k : ℝ))) ^ k * (2 * Real.sqrt (k : ℝ)) ^ k := by
        rw [div_pow]
        field_simp
      rw [hXeq]
      have hne : (0 : ℝ) < 4 * (2 * Real.sqrt (k : ℝ)) ^ k := by positivity
      rw [div_mul_eq_mul_div, div_le_iff₀ hne]
      nlinarith [hpow]
    linarith [hfinal, hbox, hcard]

end Work.HP.EELower
