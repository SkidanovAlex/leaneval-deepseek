import Mathlib
import Submission.Work.HP.MM2.Defs
import Submission.Work.HP.eNorm_veronese_bounds
import Submission.Work.FM.dmin_two_singleton_ge_one
import Submission.Work.HP.MMReindex
import Submission.Work.HP.Sig2.NN_ge_add_two
import Submission.Work.HP.MM2.degen_shell_sum_pos
import Submission.Work.HP.MM2.bad_term_le

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open Filter Finset MeasureTheory

namespace Work.HP.MM2

open Work.HP

/-! ## Helpers -/

/-- A `finsum` over a finite set is the sum over the corresponding `Finset`. -/
private lemma ps_finsum_mem_toFinset {α : Type*} (s : Set α) (hs : s.Finite) (f : α → ℝ) :
    (∑ᶠ x ∈ s, f x) = ∑ x ∈ hs.toFinset, f x := by
  have hsupp : Function.support (s.indicator f) ⊆ ↑(hs.toFinset) := by
    intro x hx
    by_contra hxS
    refine hx (Set.indicator_of_notMem (fun h => hxS ?_) _)
    exact Finset.mem_coe.mpr (hs.mem_toFinset.mpr h)
  rw [finsum_mem_def, finsum_eq_finsetSum_of_support_subset (s.indicator f) hsupp]
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [Set.indicator_of_mem (hs.mem_toFinset.mp (Finset.mem_coe.mp hx))]

/-- A primitive integer vector is nonzero. -/
private lemma ps_isPrim_ne_zero {n : ℕ} {x : Fin (n + 1) → ℤ} (hx : IsPrim x) : x ≠ 0 := by
  intro h
  have hg : Finset.univ.gcd x = 0 := by
    rw [Finset.gcd_eq_zero_iff]
    intro i _
    simp [h]
  rw [IsPrim] at hx
  rw [hg] at hx
  exact one_ne_zero hx.symm

/-- A nonzero integer vector has Euclidean norm at least `1`. -/
private lemma ps_one_le_eNorm {ι : Type*} [Fintype ι] {v : ι → ℤ} (hv : v ≠ 0) :
    1 ≤ eNorm v := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra h
    simp only [not_exists, not_not] at h
    exact hv (funext h)
  have h1 : (1 : ℝ) ≤ |(v i : ℝ)| := by
    have : (1 : ℤ) ≤ |v i| := Int.one_le_abs hi
    exact_mod_cast this
  have h2 : |(v i : ℝ)| ≤ eNorm v := eNorm_coord_abs_le v i
  linarith

/-- `W(w) ≥ 1`. -/
private lemma ps_one_le_bigW (w : ℝ) : 1 ≤ (bigW w : ℝ) := by
  have h : 1 ≤ bigW w := by
    rw [bigW]
    exact Finset.one_le_prod₀ fun p hp =>
      Nat.one_le_pow _ p (Nat.Prime.pos (Finset.mem_filter.mp hp).2)
  exact_mod_cast h

/-! ## The degenerate pair sum of `Σ₂^{mix}` -/

/-- The degenerate pair sum of `Σ₂^{mix}`.  With `W = bigW (wOf B)`, `X = B^{1/(n+1-d)}`, `t = A^{3/4}/(CW)` and `μ(x) = max A (C‖x‖/𝔡₂(x))`, the `S1ball_le` bound summed over the bad `x`-set (`x ∈ Ξ(B)` primitive with `Wλ(x) > A^{3/4}`) is `≪` the same expression with each sum replaced by its single-vector degenerate shell bound.  Route: `(max a b)^{n-1} ≤ a^{n-1}+b^{n-1}`; `𝔡₂(x) ≥ 1` kills the denominator in the `C‖x‖/𝔡₂` term; `A^{N-n-1}·A^{n-1} = A^{N-2}` (since `n+1 ≤ NN d n`); `c₁‖x‖^d ≤ ‖ν(x)‖` turns `‖ν(x)‖⁻¹` into `≪ ‖x‖^{-d}`, leaving the three sums `Σ 1/‖ν(x)‖`, `Σ ‖x‖^{n-1-d}` and `ncard`, each bounded by its shell.  The hypothesis `1 ≤ B` (as everywhere in this node family) makes `X ≥ 1`, so the right-hand side is nonnegative. -/
theorem Sigma2mix_pair_sum_le (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) :
    ∃ K : ℝ, 0 < K ∧ ∀ A B C : ℝ, 1 ≤ A → 1 ≤ B → B ^ ((5 : ℝ) / 6) ≤ A → 1 ≤ C →
      (∀ x : Fin (n + 1) → ℤ, IsPrim x →
        lamX d n x ≤ C * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ))) →
      let X := B ^ (1 / ((n : ℝ) + 1 - d))
      let t := A ^ ((3 : ℝ) / 4) / (C * (bigW (wOf B) : ℝ))
      (∑ᶠ x ∈ {x : Fin (n + 1) → ℤ | x ∈ Xi d n B ∧ IsPrim x ∧
            A ^ ((3 : ℝ) / 4) < (bigW (wOf B) : ℝ) * lamX d n x},
          ((A ^ (NN d n - 2) + A ^ (NN d n - n - 1) *
                (max A (C * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)))) ^ (n - 1)) /
              eNorm (veronese d n x)
            + A ^ (NN d n - n - 2) * (1 + Real.log A)))
        ≤ K * ((2 * A ^ (NN d n - 2) + A ^ (NN d n - n - 1) * C ^ (n - 1)) *
                (X ^ ((n : ℝ) + 2 - d) * (1 + Real.log X) / t ^ n)
              + A ^ (NN d n - n - 1) * C ^ (n - 1) *
                (X ^ (2 * (n : ℝ) + 1 - d) * (1 + Real.log X) / t ^ n)
              + A ^ (NN d n - n - 2) * (1 + Real.log A) *
                (X ^ ((n : ℝ) + 2) * (1 + Real.log X) / t ^ n)) := by
  classical
  have hn2 : 2 ≤ n := le_trans hd hdn
  have hn1 : 1 ≤ n := by omega
  have hd1 : 1 ≤ d := by omega
  obtain ⟨c₁, c₂, hc₁pos, hc₂pos, hver⟩ := eNorm_veronese_bounds d n hd1
  obtain ⟨Kb, hKbpos, hKble⟩ := bad_term_le d n hd hdn
  have hdR : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdn
  have hs1 : (0 : ℝ) < (n : ℝ) + 2 + (-(d : ℝ)) := by linarith
  have hs2 : (0 : ℝ) < (n : ℝ) + 2 + ((n : ℝ) - 1 - d) := by linarith
  have hs3 : (0 : ℝ) < (n : ℝ) + 2 + 0 := by
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  obtain ⟨K₁, hK₁pos, hK₁⟩ := degen_shell_sum_pos n hn2 (-(d : ℝ)) hs1
  obtain ⟨K₂, hK₂pos, hK₂⟩ := degen_shell_sum_pos n hn2 ((n : ℝ) - 1 - d) hs2
  obtain ⟨K₃, hK₃pos, hK₃⟩ := degen_shell_sum_pos n hn2 0 hs3
  have hKc1 : (1 : ℝ) ≤ max 1 (1 / c₁) := le_max_left _ _
  have hKc2 : 1 / c₁ ≤ max 1 (1 / c₁) := le_max_right _ _
  have hKcpos : (0 : ℝ) < max 1 (1 / c₁) := lt_of_lt_of_le zero_lt_one hKc1
  let Kbig : ℝ := max 1 (max (Kb * max 1 (1 / c₁) * K₁) (max (Kb * K₂) K₃))
  have hKbigpos : 0 < Kbig := by
    show 0 < max 1 (max (Kb * max 1 (1 / c₁) * K₁) (max (Kb * K₂) K₃))
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hKbig1 : (1 : ℝ) ≤ Kbig := by
    show 1 ≤ max 1 (max (Kb * max 1 (1 / c₁) * K₁) (max (Kb * K₂) K₃))
    exact le_max_left _ _
  have hKbig_a : Kb * max 1 (1 / c₁) * K₁ ≤ Kbig := by
    show Kb * max 1 (1 / c₁) * K₁
      ≤ max 1 (max (Kb * max 1 (1 / c₁) * K₁) (max (Kb * K₂) K₃))
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hKbig_b : Kb * K₂ ≤ Kbig := by
    show Kb * K₂ ≤ max 1 (max (Kb * max 1 (1 / c₁) * K₁) (max (Kb * K₂) K₃))
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hKbig_c : K₃ ≤ Kbig := by
    show K₃ ≤ max 1 (max (Kb * max 1 (1 / c₁) * K₁) (max (Kb * K₂) K₃))
    exact le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  refine ⟨Kbig, hKbigpos, ?_⟩
  intro A B C hA hB hAB hC hkey
  dsimp only
  set X : ℝ := B ^ (1 / ((n : ℝ) + 1 - d)) with hXdef
  set t : ℝ := A ^ ((3 : ℝ) / 4) / (C * (bigW (wOf B) : ℝ)) with htdef
  set S : Set (Fin (n + 1) → ℤ) := {x | x ∈ Xi d n B ∧ IsPrim x ∧
      A ^ ((3 : ℝ) / 4) < (bigW (wOf B) : ℝ) * lamX d n x} with hSdef
  set Sh : Set (Fin (n + 1) → ℤ) := {x | x ≠ 0 ∧ eNorm x ≤ X ∧
      t * dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ eNorm x} with hShdef
  set S1 : ℝ := X ^ ((n : ℝ) + 2 - d) * (1 + Real.log X) / t ^ n with hS1def
  set S2 : ℝ := X ^ (2 * (n : ℝ) + 1 - d) * (1 + Real.log X) / t ^ n with hS2def
  set S3 : ℝ := X ^ ((n : ℝ) + 2) * (1 + Real.log X) / t ^ n with hS3def
  have hB0 : 0 < B := lt_of_lt_of_le zero_lt_one hB
  have hA0 : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hW1 : 1 ≤ (bigW (wOf B) : ℝ) := ps_one_le_bigW (wOf B)
  have hWpos : 0 < (bigW (wOf B) : ℝ) := lt_of_lt_of_le zero_lt_one hW1
  have hexpX : 0 ≤ 1 / ((n : ℝ) + 1 - d) := by
    apply div_nonneg (by norm_num)
    linarith
  have hX1 : 1 ≤ X := by
    rw [hXdef]
    exact Real.one_le_rpow hB hexpX
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX1
  have ht0 : 0 < t := by
    rw [htdef]
    exact div_pos (Real.rpow_pos_of_pos hA0 _) (mul_pos hC0 hWpos)
  have hSfin : S.Finite := (Xi_finite d n B).subset (fun x hx => hx.1)
  have hShfin : Sh.Finite :=
    (finite_of_eNorm_le (ι := Fin (n + 1)) X).subset (fun x hx => hx.2.1)
  -- membership in `S` unfolds to the conjunction
  have hSmem : ∀ x, x ∈ S ↔ x ∈ Xi d n B ∧ IsPrim x ∧
      A ^ ((3 : ℝ) / 4) < (bigW (wOf B) : ℝ) * lamX d n x := by
    intro x; simp only [hSdef, Set.mem_ofPred_eq]
  have hShmem : ∀ x, x ∈ Sh ↔ x ≠ 0 ∧ eNorm x ≤ X ∧
      t * dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) ≤ eNorm x := by
    intro x; simp only [hShdef, Set.mem_ofPred_eq]
  -- the bad set is contained in the shell
  have hsub : S ⊆ Sh := by
    intro x hx
    rw [hShmem, hSmem] at *
    obtain ⟨hxXi, hxprim, hxbad⟩ := hx
    have hx0 : x ≠ 0 := ps_isPrim_ne_zero hxprim
    have hxe : eNorm x ≤ X := by
      have h := hxXi.2
      rw [hXdef]
      exact h
    set d₂ : ℝ := dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) with hd₂def
    have hd2ge : 1 ≤ d₂ := by
      rw [hd₂def]
      exact Work.FM.dmin_two_singleton_ge_one n hn1 x hxprim
    have hd2pos : 0 < d₂ := lt_of_lt_of_le zero_lt_one hd2ge
    have hkeyx : lamX d n x ≤ C * eNorm x / d₂ := by
      rw [hd₂def]
      exact hkey x hxprim
    have ha : A ^ ((3 : ℝ) / 4) < ((bigW (wOf B) : ℝ) * C * eNorm x) / d₂ := by
      have h1 : A ^ ((3 : ℝ) / 4) < (bigW (wOf B) : ℝ) * (C * eNorm x / d₂) :=
        lt_of_lt_of_le hxbad (mul_le_mul_of_nonneg_left hkeyx (le_of_lt hWpos))
      convert h1 using 2
      ring
    have hb : A ^ ((3 : ℝ) / 4) * d₂ < eNorm x * (C * (bigW (wOf B) : ℝ)) := by
      have h := (lt_div_iff₀ hd2pos).mp ha
      nlinarith [h]
    have hmain : t * d₂ < eNorm x := by
      have hCW : 0 < C * (bigW (wOf B) : ℝ) := mul_pos hC0 hWpos
      rw [htdef, div_mul_eq_mul_div]
      exact (div_lt_iff₀ hCW).mpr hb
    exact ⟨hx0, hxe, le_of_lt hmain⟩
  have hFsub : hSfin.toFinset ⊆ hShfin.toFinset := by
    intro x hx
    exact hShfin.mem_toFinset.mpr (hsub (hSfin.mem_toFinset.mp hx))
  -- positivity of the Veronese norms
  have hνpos : ∀ x ∈ hSfin.toFinset, 0 < eNorm (veronese d n x) := by
    intro x hx
    have hxS := hSfin.mem_toFinset.mp hx
    rw [hSmem] at hxS
    obtain ⟨hxXi, hxprim, -⟩ := hxS
    have hx0 : x ≠ 0 := ps_isPrim_ne_zero hxprim
    have hxpos : 0 < eNorm x := lt_of_lt_of_le zero_lt_one (ps_one_le_eNorm hx0)
    have h1 := (hver x).1
    have h2 : 0 < c₁ * eNorm x ^ d := mul_pos hc₁pos (pow_pos hxpos d)
    linarith
  -- pointwise bound of `bad_term_le`
  have hpoint : ∀ x ∈ hSfin.toFinset,
      (A ^ (NN d n - 2) + A ^ (NN d n - n - 1) *
            (max A (C * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)))) ^ (n - 1)) /
          eNorm (veronese d n x)
        ≤ Kb * (2 * A ^ (NN d n - 2) / eNorm (veronese d n x)
            + A ^ (NN d n - n - 1) * C ^ (n - 1) * eNorm x ^ ((n : ℝ) - 1 - d)) := by
    intro x hx
    have hxS := hSfin.mem_toFinset.mp hx
    rw [hSmem] at hxS
    obtain ⟨hxXi, hxprim, -⟩ := hxS
    have hx0 : x ≠ 0 := ps_isPrim_ne_zero hxprim
    have hd2ge : 1 ≤ dmin 2 ({x} : Set (Fin (n + 1) → ℤ)) :=
      Work.FM.dmin_two_singleton_ge_one n hn1 x hxprim
    exact hKble A C x hA hC hx0 hd2ge
  -- (1) the sum of `1 / ‖ν(x)‖`
  have hT₁ : (∑ x ∈ hSfin.toFinset, 1 / eNorm (veronese d n x))
      ≤ max 1 (1 / c₁) * K₁ * S1 := by
    have hpt : ∀ x ∈ hSfin.toFinset,
        1 / eNorm (veronese d n x) ≤ max 1 (1 / c₁) * eNorm x ^ (-(d : ℝ)) := by
      intro x hx
      have hxS := hSfin.mem_toFinset.mp hx
      rw [hSmem] at hxS
      obtain ⟨hxXi, hxprim, -⟩ := hxS
      have hx0 : x ≠ 0 := ps_isPrim_ne_zero hxprim
      have hxpos : 0 < eNorm x := lt_of_lt_of_le zero_lt_one (ps_one_le_eNorm hx0)
      have hν := hνpos x hx
      have hverx : c₁ * eNorm x ^ (d : ℝ) ≤ eNorm (veronese d n x) := by
        rw [Real.rpow_natCast]
        exact (hver x).1
      have hpow : eNorm x ^ (-(d : ℝ)) * eNorm x ^ (d : ℝ) = 1 := by
        rw [← Real.rpow_add hxpos, neg_add_cancel, Real.rpow_zero]
      have hone : (1 / c₁) * eNorm x ^ (-(d : ℝ)) * (c₁ * eNorm x ^ (d : ℝ)) = 1 := by
        calc (1 / c₁) * eNorm x ^ (-(d : ℝ)) * (c₁ * eNorm x ^ (d : ℝ))
            = (1 / c₁) * c₁ * (eNorm x ^ (-(d : ℝ)) * eNorm x ^ (d : ℝ)) := by ring
          _ = 1 * 1 := by rw [one_div_mul_cancel (ne_of_gt hc₁pos), hpow]
          _ = 1 := one_mul 1
      have hstep : 1 ≤ (1 / c₁) * eNorm x ^ (-(d : ℝ)) * eNorm (veronese d n x) := by
        calc (1 : ℝ) = (1 / c₁) * eNorm x ^ (-(d : ℝ)) * (c₁ * eNorm x ^ (d : ℝ)) :=
              hone.symm
          _ ≤ (1 / c₁) * eNorm x ^ (-(d : ℝ)) * eNorm (veronese d n x) :=
              mul_le_mul_of_nonneg_left hverx (by positivity)
      have hmain : (eNorm (veronese d n x))⁻¹ ≤ (1 / c₁) * eNorm x ^ (-(d : ℝ)) := by
        rw [inv_le_iff_one_le_mul₀ hν]
        exact hstep
      calc 1 / eNorm (veronese d n x) = (eNorm (veronese d n x))⁻¹ := one_div _
        _ ≤ (1 / c₁) * eNorm x ^ (-(d : ℝ)) := hmain
        _ ≤ max 1 (1 / c₁) * eNorm x ^ (-(d : ℝ)) :=
            mul_le_mul_of_nonneg_right hKc2 (Real.rpow_nonneg (le_of_lt hxpos) _)
    have hfin : (∑ x ∈ hSfin.toFinset, max 1 (1 / c₁) * eNorm x ^ (-(d : ℝ)))
        = max 1 (1 / c₁) * (∑ x ∈ hSfin.toFinset, eNorm x ^ (-(d : ℝ))) :=
      (Finset.mul_sum _ _ _).symm
    have hconv : (∑ x ∈ hShfin.toFinset, eNorm x ^ (-(d : ℝ)))
        = ∑ᶠ x ∈ Sh, eNorm x ^ (-(d : ℝ)) :=
      (ps_finsum_mem_toFinset Sh hShfin _).symm
    have hmono : (∑ x ∈ hSfin.toFinset, eNorm x ^ (-(d : ℝ)))
        ≤ ∑ᶠ x ∈ Sh, eNorm x ^ (-(d : ℝ)) := by
      rw [← hconv]
      exact Finset.sum_le_sum_of_subset_of_nonneg hFsub
        (fun x _ _ => Real.rpow_nonneg (eNorm_toR_nonneg x) _)
    have hsh := hK₁ X t hX1 ht0
    have hexp : (n : ℝ) + 2 + (-(d : ℝ)) = (n : ℝ) + 2 - d := by ring
    rw [hexp] at hsh
    have hsh' : (∑ᶠ x ∈ Sh, eNorm x ^ (-(d : ℝ))) ≤ K₁ * S1 := by
      have hEq : K₁ * X ^ ((n : ℝ) + 2 - d) * (1 + Real.log X) / t ^ n = K₁ * S1 := by
        rw [hS1def]; ring
      rw [hEq] at hsh
      exact hsh
    calc (∑ x ∈ hSfin.toFinset, 1 / eNorm (veronese d n x))
        ≤ ∑ x ∈ hSfin.toFinset, max 1 (1 / c₁) * eNorm x ^ (-(d : ℝ)) :=
          Finset.sum_le_sum hpt
      _ = max 1 (1 / c₁) * (∑ x ∈ hSfin.toFinset, eNorm x ^ (-(d : ℝ))) := hfin
      _ ≤ max 1 (1 / c₁) * (∑ᶠ x ∈ Sh, eNorm x ^ (-(d : ℝ))) :=
          mul_le_mul_of_nonneg_left hmono (le_of_lt hKcpos)
      _ ≤ max 1 (1 / c₁) * (K₁ * S1) := mul_le_mul_of_nonneg_left hsh' (le_of_lt hKcpos)
      _ = max 1 (1 / c₁) * K₁ * S1 := by ring
  -- (2) the sum of `‖x‖^{n-1-d}`
  have hT₂ : (∑ x ∈ hSfin.toFinset, eNorm x ^ ((n : ℝ) - 1 - d)) ≤ K₂ * S2 := by
    have hconv : (∑ x ∈ hShfin.toFinset, eNorm x ^ ((n : ℝ) - 1 - d))
        = ∑ᶠ x ∈ Sh, eNorm x ^ ((n : ℝ) - 1 - d) :=
      (ps_finsum_mem_toFinset Sh hShfin _).symm
    have hmono : (∑ x ∈ hSfin.toFinset, eNorm x ^ ((n : ℝ) - 1 - d))
        ≤ ∑ᶠ x ∈ Sh, eNorm x ^ ((n : ℝ) - 1 - d) := by
      rw [← hconv]
      exact Finset.sum_le_sum_of_subset_of_nonneg hFsub
        (fun x _ _ => Real.rpow_nonneg (eNorm_toR_nonneg x) _)
    have hsh := hK₂ X t hX1 ht0
    have hexp : (n : ℝ) + 2 + ((n : ℝ) - 1 - d) = 2 * (n : ℝ) + 1 - d := by ring
    rw [hexp] at hsh
    have hsh' : (∑ᶠ x ∈ Sh, eNorm x ^ ((n : ℝ) - 1 - d)) ≤ K₂ * S2 := by
      have hEq : K₂ * X ^ (2 * (n : ℝ) + 1 - d) * (1 + Real.log X) / t ^ n = K₂ * S2 := by
        rw [hS2def]; ring
      rw [hEq] at hsh
      exact hsh
    exact le_trans hmono hsh'
  -- (3) the number of bad vectors
  have hT₃ : ((hSfin.toFinset.card : ℕ) : ℝ) ≤ K₃ * S3 := by
    have h1 : hSfin.toFinset.card ≤ hShfin.toFinset.card := Finset.card_le_card hFsub
    have h1' : ((hSfin.toFinset.card : ℕ) : ℝ) ≤ ((hShfin.toFinset.card : ℕ) : ℝ) := by
      exact_mod_cast h1
    have h2 : ((hShfin.toFinset.card : ℕ) : ℝ) ≤ ∑ᶠ x ∈ Sh, eNorm x ^ (0 : ℝ) := by
      rw [ps_finsum_mem_toFinset Sh hShfin]
      have hEq : (∑ x ∈ hShfin.toFinset, eNorm x ^ (0 : ℝ))
          = ∑ x ∈ hShfin.toFinset, (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun x _ => ?_)
        rw [Real.rpow_zero]
      rw [hEq, Finset.sum_const, nsmul_eq_mul, mul_one]
    have hsh := hK₃ X t hX1 ht0
    have hexp : (n : ℝ) + 2 + 0 = (n : ℝ) + 2 := by ring
    rw [hexp] at hsh
    have hsh' : (∑ᶠ x ∈ Sh, eNorm x ^ (0 : ℝ)) ≤ K₃ * S3 := by
      have hEq : K₃ * X ^ ((n : ℝ) + 2) * (1 + Real.log X) / t ^ n = K₃ * S3 := by
        rw [hS3def]; ring
      rw [hEq] at hsh
      exact hsh
    linarith
  -- the first sum of the target
  have hf : (∑ x ∈ hSfin.toFinset,
        (A ^ (NN d n - 2) + A ^ (NN d n - n - 1) *
              (max A (C * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)))) ^ (n - 1)) /
            eNorm (veronese d n x))
      ≤ Kbig * ((2 * A ^ (NN d n - 2) + A ^ (NN d n - n - 1) * C ^ (n - 1)) * S1
          + A ^ (NN d n - n - 1) * C ^ (n - 1) * S2) := by
    have hfa : (∑ x ∈ hSfin.toFinset, 2 * A ^ (NN d n - 2) / eNorm (veronese d n x))
        = 2 * A ^ (NN d n - 2) * (∑ x ∈ hSfin.toFinset, 1 / eNorm (veronese d n x)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      rw [mul_one_div]
    have hfb : (∑ x ∈ hSfin.toFinset,
          A ^ (NN d n - n - 1) * C ^ (n - 1) * eNorm x ^ ((n : ℝ) - 1 - d))
        = A ^ (NN d n - n - 1) * C ^ (n - 1)
          * (∑ x ∈ hSfin.toFinset, eNorm x ^ ((n : ℝ) - 1 - d)) := by
      rw [Finset.mul_sum]
    have hstep1 : (∑ x ∈ hSfin.toFinset,
          (A ^ (NN d n - 2) + A ^ (NN d n - n - 1) *
                (max A (C * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)))) ^ (n - 1)) /
              eNorm (veronese d n x))
        ≤ ∑ x ∈ hSfin.toFinset, Kb * (2 * A ^ (NN d n - 2) / eNorm (veronese d n x)
              + A ^ (NN d n - n - 1) * C ^ (n - 1) * eNorm x ^ ((n : ℝ) - 1 - d)) :=
      Finset.sum_le_sum hpoint
    have hstep2 : (∑ x ∈ hSfin.toFinset, Kb * (2 * A ^ (NN d n - 2) / eNorm (veronese d n x)
              + A ^ (NN d n - n - 1) * C ^ (n - 1) * eNorm x ^ ((n : ℝ) - 1 - d)))
        = Kb * (2 * A ^ (NN d n - 2) * (∑ x ∈ hSfin.toFinset, 1 / eNorm (veronese d n x))
              + A ^ (NN d n - n - 1) * C ^ (n - 1)
                * (∑ x ∈ hSfin.toFinset, eNorm x ^ ((n : ℝ) - 1 - d))) := by
      have hL : (∑ x ∈ hSfin.toFinset, Kb * (2 * A ^ (NN d n - 2) / eNorm (veronese d n x)
              + A ^ (NN d n - n - 1) * C ^ (n - 1) * eNorm x ^ ((n : ℝ) - 1 - d)))
          = Kb * (∑ x ∈ hSfin.toFinset, (2 * A ^ (NN d n - 2) / eNorm (veronese d n x)
              + A ^ (NN d n - n - 1) * C ^ (n - 1) * eNorm x ^ ((n : ℝ) - 1 - d))) :=
        (Finset.mul_sum _ _ _).symm
      rw [hL, Finset.sum_add_distrib, hfa, hfb]
    have hstep3 : Kb * (2 * A ^ (NN d n - 2) * (∑ x ∈ hSfin.toFinset, 1 / eNorm (veronese d n x))
              + A ^ (NN d n - n - 1) * C ^ (n - 1)
                * (∑ x ∈ hSfin.toFinset, eNorm x ^ ((n : ℝ) - 1 - d)))
        ≤ Kb * (2 * A ^ (NN d n - 2) * (max 1 (1 / c₁) * K₁ * S1)
              + A ^ (NN d n - n - 1) * C ^ (n - 1) * (K₂ * S2)) := by
      refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hKbpos)
      have h1 : 2 * A ^ (NN d n - 2) * (∑ x ∈ hSfin.toFinset, 1 / eNorm (veronese d n x))
          ≤ 2 * A ^ (NN d n - 2) * (max 1 (1 / c₁) * K₁ * S1) :=
        mul_le_mul_of_nonneg_left hT₁ (by positivity)
      have h2 : A ^ (NN d n - n - 1) * C ^ (n - 1)
              * (∑ x ∈ hSfin.toFinset, eNorm x ^ ((n : ℝ) - 1 - d))
          ≤ A ^ (NN d n - n - 1) * C ^ (n - 1) * (K₂ * S2) :=
        mul_le_mul_of_nonneg_left hT₂ (by positivity)
      linarith
    have hstep4 : Kb * (2 * A ^ (NN d n - 2) * (max 1 (1 / c₁) * K₁ * S1)
              + A ^ (NN d n - n - 1) * C ^ (n - 1) * (K₂ * S2))
        ≤ Kbig * (2 * A ^ (NN d n - 2) * S1 + A ^ (NN d n - n - 1) * C ^ (n - 1) * S2) := by
      have hSA : 0 ≤ 2 * A ^ (NN d n - 2) * S1 := by positivity
      have hSB : 0 ≤ A ^ (NN d n - n - 1) * C ^ (n - 1) * S2 := by positivity
      calc Kb * (2 * A ^ (NN d n - 2) * (max 1 (1 / c₁) * K₁ * S1)
              + A ^ (NN d n - n - 1) * C ^ (n - 1) * (K₂ * S2))
          = Kb * max 1 (1 / c₁) * K₁ * (2 * A ^ (NN d n - 2) * S1)
              + Kb * K₂ * (A ^ (NN d n - n - 1) * C ^ (n - 1) * S2) := by ring
        _ ≤ Kbig * (2 * A ^ (NN d n - 2) * S1)
              + Kbig * (A ^ (NN d n - n - 1) * C ^ (n - 1) * S2) :=
            add_le_add (mul_le_mul_of_nonneg_right hKbig_a hSA)
              (mul_le_mul_of_nonneg_right hKbig_b hSB)
        _ = Kbig * (2 * A ^ (NN d n - 2) * S1 + A ^ (NN d n - n - 1) * C ^ (n - 1) * S2) := by
            ring
    have hstep5 : 2 * A ^ (NN d n - 2) * S1 + A ^ (NN d n - n - 1) * C ^ (n - 1) * S2
        ≤ (2 * A ^ (NN d n - 2) + A ^ (NN d n - n - 1) * C ^ (n - 1)) * S1
          + A ^ (NN d n - n - 1) * C ^ (n - 1) * S2 := by
      have hSA : 0 ≤ A ^ (NN d n - n - 1) * C ^ (n - 1) * S1 := by positivity
      nlinarith [hSA]
    have hstep6 : Kbig * (2 * A ^ (NN d n - 2) * S1 + A ^ (NN d n - n - 1) * C ^ (n - 1) * S2)
        ≤ Kbig * ((2 * A ^ (NN d n - 2) + A ^ (NN d n - n - 1) * C ^ (n - 1)) * S1
          + A ^ (NN d n - n - 1) * C ^ (n - 1) * S2) :=
      mul_le_mul_of_nonneg_left hstep5 (le_of_lt hKbigpos)
    exact le_trans hstep1 (le_trans (le_of_eq hstep2) (le_trans hstep3 (le_trans hstep4 hstep6)))
  -- the second sum of the target
  have hg : (∑ x ∈ hSfin.toFinset, A ^ (NN d n - n - 2) * (1 + Real.log A))
      ≤ Kbig * (A ^ (NN d n - n - 2) * (1 + Real.log A) * S3) := by
    rw [Finset.sum_const, nsmul_eq_mul]
    have hc : 0 ≤ A ^ (NN d n - n - 2) * (1 + Real.log A) := by
      have h1 : 0 ≤ Real.log A := Real.log_nonneg hA
      positivity
    have hcard : ((hSfin.toFinset.card : ℕ) : ℝ) ≤ K₃ * S3 := hT₃
    have hS3 : 0 ≤ S3 := by rw [hS3def]; positivity
    calc ((hSfin.toFinset.card : ℕ) : ℝ) * (A ^ (NN d n - n - 2) * (1 + Real.log A))
        ≤ (K₃ * S3) * (A ^ (NN d n - n - 2) * (1 + Real.log A)) :=
          mul_le_mul_of_nonneg_right hcard hc
      _ ≤ Kbig * (A ^ (NN d n - n - 2) * (1 + Real.log A) * S3) := by
          have h1 : (K₃ * S3) * (A ^ (NN d n - n - 2) * (1 + Real.log A))
              = K₃ * ((A ^ (NN d n - n - 2) * (1 + Real.log A)) * S3) := by ring
          rw [h1]
          exact mul_le_mul_of_nonneg_right hKbig_c (by positivity)
  -- assemble
  rw [ps_finsum_mem_toFinset S hSfin, Finset.sum_add_distrib]
  have hfinal : Kbig * ((2 * A ^ (NN d n - 2) + A ^ (NN d n - n - 1) * C ^ (n - 1)) * S1
        + A ^ (NN d n - n - 1) * C ^ (n - 1) * S2)
      + Kbig * (A ^ (NN d n - n - 2) * (1 + Real.log A) * S3)
      = Kbig * (((2 * A ^ (NN d n - 2) + A ^ (NN d n - n - 1) * C ^ (n - 1)) * S1
        + A ^ (NN d n - n - 1) * C ^ (n - 1) * S2)
        + A ^ (NN d n - n - 2) * (1 + Real.log A) * S3) := by ring
  calc (∑ x ∈ hSfin.toFinset,
        (A ^ (NN d n - 2) + A ^ (NN d n - n - 1) *
              (max A (C * eNorm x / dmin 2 ({x} : Set (Fin (n + 1) → ℤ)))) ^ (n - 1)) /
            eNorm (veronese d n x))
      + (∑ x ∈ hSfin.toFinset, A ^ (NN d n - n - 2) * (1 + Real.log A))
      ≤ Kbig * ((2 * A ^ (NN d n - 2) + A ^ (NN d n - n - 1) * C ^ (n - 1)) * S1
          + A ^ (NN d n - n - 1) * C ^ (n - 1) * S2)
        + Kbig * (A ^ (NN d n - n - 2) * (1 + Real.log A) * S3) := add_le_add hf hg
    _ = Kbig * (((2 * A ^ (NN d n - 2) + A ^ (NN d n - n - 1) * C ^ (n - 1)) * S1
          + A ^ (NN d n - n - 1) * C ^ (n - 1) * S2)
          + A ^ (NN d n - n - 2) * (1 + Real.log A) * S3) := hfinal

end Work.HP.MM2
