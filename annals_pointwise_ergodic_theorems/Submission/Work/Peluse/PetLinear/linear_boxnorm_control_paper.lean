import Mathlib
import Submission.Work.Peluse.Pairing.boxSumPow_star
import Submission.Work.Peluse.PetLinear.linear_boxnorm_control
import Submission.Work.Peluse.PetLinear.linear_boxnorm_control_one
import Submission.Work.Peluse.PetLinear.pet_step_prod_reorg
import Submission.Work.Peluse.PetLinear.boxNormPow_peel_muL_all
import Submission.Work.Peluse.PetLinear.weighted_sum_pow_le

/-!
# Peluse, Lemma 4.10, in the paper's gauge

See the docstring of the target theorem `linear_boxnorm_control_paper` below.

## The induction

The proof is an induction on the level `m`, following S. Peluse, *Bounds for sets with no polynomial
progressions*, Forum Math. Pi **8** (2020), e16, Lemma 4.10.

* `LevelBound m K C` is the target statement with the constants `K`, `C` fixed (so that it can be
  used as an induction hypothesis).
* `levelBound_one` is the base case, obtained from
  `Work.Peluse.PetLinear.linear_boxnorm_control_one`.
* `levelBound_succ` is the induction step: from `LevelBound n K' C'` one gets
  `LevelBound (n+1) (2K') C` for `C = max 2000 (max (C' * 8000^{K'}) (8000 * sqrt C'))`.  It is the
  PET step (`Work.Peluse.PET.pet_step`) at the level `n+1`, whose output is the `μ_H`-average of the
  level-`n` configuration averages of the difference functions `Δ'_{c_{j+1} a, 0} F_{j+1}`
  (`pet_step_prod_reorg`), followed by the peel of the *first* direction of the box norm
  (`Work.Peluse.Peel.boxNormPow_peel_muL`) which restores the `μ_H`-weighted average over the
  differences `c_{n+1} a`, and finished with Jensen's inequality in `a`.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000

open scoped BigOperators

namespace Work.Peluse.PetLinear

noncomputable section

open Work.Peluse

/-! ## Conjugation invariance of the box-norm power -/

/-- The box-norm power is invariant under conjugation. -/
theorem boxNormPow_star' {t : ℕ} (Q : Fin t → Finset ℤ) (S : Finset ℤ) (f : ℤ → ℂ) :
    Work.Peluse.boxNormPow t Q S (fun x => star (f x)) = Work.Peluse.boxNormPow t Q S f := by
  rw [Work.Peluse.boxNormPow, Work.Peluse.boxNormPow, Work.Peluse.Pairing.boxSumPow_star,
    norm_star]

/-! ## The difference functions of the PET step -/

/-- The difference function `Δ'_{c_{j+1}a, 0} F_{j+1}` of the PET step: for `c : Fin (n+2) → ℤ`,
`F : Fin (n+2) → ℤ → ℂ` and a shift `a`, `diffFun F c a j` is the `j`-th factor of the level-`n`
configuration produced by the step. -/
def diffFun {n : ℕ} (F : Fin (n + 2) → ℤ → ℂ) (c : Fin (n + 2) → ℤ) (a : ℤ) (j : Fin (n + 1)) :
    ℤ → ℂ :=
  fun u => star (F (j.succ) (u + c (j.succ) * a)) * F (j.succ) u

/-- The shift coefficients `c_{j+1} - c_1` of the level-`n` configuration of the difference
functions. -/
def diffShift {n : ℕ} (c : Fin (n + 2) → ℤ) (j : Fin (n + 1)) : ℤ := c (j.succ) - c 1

lemma diffShift_zero {n : ℕ} (c : Fin (n + 2) → ℤ) : diffShift c 0 = 0 := by
  simp [diffShift]

lemma diffFun_zero {n : ℕ} (F : Fin (n + 2) → ℤ → ℂ) (c : Fin (n + 2) → ℤ) (a : ℤ) :
    diffFun F c a 0 = fun u => star (F 1 (u + c 1 * a)) * F 1 u := by
  funext u
  simp [diffFun]

lemma diffFun_last {n : ℕ} (F : Fin (n + 2) → ℤ → ℂ) (c : Fin (n + 2) → ℤ) (a : ℤ) :
    diffFun F c a ⟨n, by omega⟩
      = fun u => star (F ⟨n + 1, by omega⟩ (u + c ⟨n + 1, by omega⟩ * a))
          * F ⟨n + 1, by omega⟩ u := by
  funext u
  simp [diffFun]

/-! ## The direction family and the level predicate -/

/-- The direction family of the target: for `c : Fin (m+1) → ℤ` and a shift scale `H`, the sets
`(c_m - c_i)[H]`, `i = 0, …, m-1`, where `c_m = c ⟨m, _⟩`. -/
def dirFamily {m : ℕ} (c : Fin (m + 1) → ℤ) (H : ℕ) : Fin m → Finset ℤ :=
  fun i => Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩ - c i.castSucc) H

/-- **The target statement with fixed constants.**  This is Peulue's Lemma 4.10 in the paper's
gauge `γ' ≪ γ^{O_m(1)}` (here: `γ' ≤ γ^K/C`), asserting that a multilinear average of size `γ` for
the linear configuration `(x + c_i y)` forces the `2^m`-th power of the Gowers box norm of the last
function, at the direction family `(c_m - c_i)[⌊γ'M⌋]`, to be at least `(γ/C)^K`. -/
def LevelBound (m : ℕ) (K : ℕ) (C : ℝ) : Prop :=
  1 ≤ K ∧ 0 < C ∧
    ∀ (c : Fin (m + 1) → ℤ), c 0 = 0 → ∀ {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
      (F : Fin (m + 1) → ℤ → ℂ) {γ γ' : ℝ}, 0 < γ → 0 < γ' → γ ≤ 1 →
      (∀ i x, ‖F i x‖ ≤ 1) → (∀ i, Work.Peluse.SupportIn (F i) N) →
      (∀ y ∈ Finset.Icc 1 M, ∀ i : Fin (m + 1), |c i * (y : ℤ)| ≤ (N : ℤ)) →
      γ' ≤ γ ^ K / C → 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat →
      γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
          ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ ^ 2 →
      (γ / C) ^ K ≤ Work.Peluse.boxNormPow m
        (dirFamily c (⌊γ' * (M : ℝ)⌋).toNat) (Work.Peluse.symIcc N)
        (F ⟨m, Nat.lt_succ_self m⟩)


/-- Elimination form of `LevelBound`, with all hypotheses named. -/
private lemma LevelBound.apply {m : ℕ} {K : ℕ} {C : ℝ} (h : LevelBound m K C)
    (c : Fin (m + 1) → ℤ) (hc0 : c 0 = 0) {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (F : Fin (m + 1) → ℤ → ℂ) {γ γ' : ℝ} (hγ : 0 < γ) (hγ' : 0 < γ') (hγ1 : γ ≤ 1)
    (hF : ∀ i x, ‖F i x‖ ≤ 1) (hFs : ∀ i, Work.Peluse.SupportIn (F i) N)
    (hcy : ∀ y ∈ Finset.Icc 1 M, ∀ i : Fin (m + 1), |c i * (y : ℤ)| ≤ (N : ℤ))
    (hg : γ' ≤ γ ^ K / C) (hH : 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat)
    (hLam : γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
        ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ ^ 2) :
    (γ / C) ^ K ≤ Work.Peluse.boxNormPow m (dirFamily c (⌊γ' * (M : ℝ)⌋).toNat)
      (Work.Peluse.symIcc N) (F ⟨m, Nat.lt_succ_self m⟩) :=
  h.2.2 c hc0 hN hM F hγ hγ' hγ1 hF hFs hcy hg hH hLam

/-! ## The pointwise identification of the PET step output with a level-`n` configuration -/

private lemma pet_pointwise {n : ℕ} (F : Fin (n + 2) → ℤ → ℂ) (c : Fin (n + 2) → ℤ) (a x y : ℤ) :
    F 1 x * (∏ i : Fin (n + 1), ∏ ε : Bool,
        (if ((i, ε) = ((0 : Fin (n + 1)), false)) then (1 : ℂ)
          else (if ε then star (F (i.succ) (x + (c (i.succ) * (y + a) - c 1 * y)))
                else F (i.succ) (x + (c (i.succ) * y - c 1 * y)))))
      = diffFun F c a 0 x *
        ∏ i : Fin n, diffFun F c a i.succ (x + diffShift c i.succ * y) := by
  rw [pet_step_prod_reorg F c x y a]
  simp only [diffFun, diffShift, Fin.succ_zero_eq_one]
  ring

private lemma pet_summand_eq {n : ℕ} (F : Fin (n + 2) → ℤ → ℂ) (c : Fin (n + 2) → ℤ)
    (N M : ℕ) (a : ℤ) :
    ((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 1 x * ∑ y ∈ Finset.Icc 1 M,
        ∏ i : Fin (n + 1), ∏ ε : Bool,
          (if ((i, ε) = ((0 : Fin (n + 1)), false)) then (1 : ℂ)
            else (if ε then star (F (i.succ) (x + (c (i.succ) * ((y : ℤ) + a) - c 1 * (y : ℤ))))
                  else F (i.succ) (x + (c (i.succ) * (y : ℤ) - c 1 * (y : ℤ)))))
      = ((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, diffFun F c a 0 x *
          ∑ y ∈ Finset.Icc 1 M,
            ∏ i : Fin n, diffFun F c a i.succ (x + diffShift c i.succ * (y : ℤ)) := by
  congr 1
  refine tsum_congr fun x => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => pet_pointwise F c a x y


/-! ## Elementary facts about the difference functions -/

/-! ## Elementary facts about the difference functions -/

private lemma norm_diffFun_le_one {n : ℕ} (F : Fin (n + 2) → ℤ → ℂ) (c : Fin (n + 2) → ℤ)
    (a : ℤ) (hF : ∀ i x, ‖F i x‖ ≤ 1) (j : Fin (n + 1)) (x : ℤ) :
    ‖diffFun F c a j x‖ ≤ 1 := by
  rw [diffFun, norm_mul, norm_star]
  exact mul_le_one₀ (hF _ _) (norm_nonneg _) (hF _ _)

private lemma supportIn_diffFun {n : ℕ} {N : ℕ} (F : Fin (n + 2) → ℤ → ℂ) (c : Fin (n + 2) → ℤ)
    (a : ℤ) (hFs : ∀ i, Work.Peluse.SupportIn (F i) N)
    (ha : ∀ i : Fin (n + 2), |c i * a| ≤ (N : ℤ)) (j : Fin (n + 1)) :
    Work.Peluse.SupportIn (diffFun F c a j) (2 * N) := by
  intro x hx
  have h0 : F (j.succ) x = 0 := by
    apply hFs
    omega
  have h1 : F (j.succ) (x + c (j.succ) * a) = 0 := by
    apply hFs
    have h2 : |c (j.succ) * a| ≤ (N : ℤ) := ha _
    have h3 : |x| ≤ |x + c (j.succ) * a| + |c (j.succ) * a| := by
      have h4 := abs_add_le (x + c (j.succ) * a) (-(c (j.succ) * a))
      simpa [abs_neg, add_assoc] using h4
    have h4 : (2 * N : ℤ) < |x| := by
      have h5 := Int.natCast_natAbs x
      rw [← h5]
      exact_mod_cast hx
    have h5 : (N : ℤ) < ((x + c (j.succ) * a).natAbs : ℤ) := by
      rw [Int.natCast_natAbs]
      omega
    exact_mod_cast h5
  rw [diffFun]
  simp [h0, h1]

private lemma diffShift_abs_le {n : ℕ} {N : ℕ} {M : ℕ} (c : Fin (n + 2) → ℤ)
    (hcy : ∀ y ∈ Finset.Icc 1 M, ∀ i : Fin (n + 2), |c i * (y : ℤ)| ≤ (N : ℤ))
    {y : ℕ} (hy : y ∈ Finset.Icc 1 M) (j : Fin (n + 1)) :
    |diffShift c j * (y : ℤ)| ≤ (2 * N : ℤ) := by
  have h1 : |c (j.succ) * (y : ℤ)| ≤ (N : ℤ) := hcy y hy _
  have h2 : |c 1 * (y : ℤ)| ≤ (N : ℤ) := hcy y hy _
  have h3 : diffShift c j * (y : ℤ) = c (j.succ) * (y : ℤ) - c 1 * (y : ℤ) := by
    rw [diffShift]; ring
  rw [h3]
  calc |c (j.succ) * (y : ℤ) - c 1 * (y : ℤ)|
      ≤ |c (j.succ) * (y : ℤ)| + |c 1 * (y : ℤ)| := abs_sub _ _
    _ ≤ (N : ℤ) + (N : ℤ) := add_le_add h1 h2
    _ = (2 * N : ℤ) := by ring

/-! ## The crude bound on the level-`n` averages -/

private lemma norm_tsum_diffFun_le {n : ℕ} {N M : ℕ} (F : Fin (n + 2) → ℤ → ℂ)
    (c : Fin (n + 2) → ℤ) (a : ℤ) (hF : ∀ i x, ‖F i x‖ ≤ 1)
    (hFs : ∀ i, Work.Peluse.SupportIn (F i) N)
    (ha : ∀ i : Fin (n + 2), |c i * a| ≤ (N : ℤ)) :
    ‖∑' x : ℤ, diffFun F c a 0 x *
        ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin n, diffFun F c a i.succ (x + diffShift c i.succ * (y : ℤ))‖
      ≤ (4 * (N : ℝ) + 1) * (M : ℝ) := by
  have hsupp0 : Work.Peluse.SupportIn (diffFun F c a 0) (2 * N) :=
    supportIn_diffFun F c a hFs ha 0
  have hinner : ∀ x : ℤ, ‖∑ y ∈ Finset.Icc 1 M,
      ∏ i : Fin n, diffFun F c a i.succ (x + diffShift c i.succ * (y : ℤ))‖ ≤ (M : ℝ) := by
    intro x
    calc ‖∑ y ∈ Finset.Icc 1 M,
          ∏ i : Fin n, diffFun F c a i.succ (x + diffShift c i.succ * (y : ℤ))‖
        ≤ ∑ y ∈ Finset.Icc 1 M,
            ‖∏ i : Fin n, diffFun F c a i.succ (x + diffShift c i.succ * (y : ℤ))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ y ∈ Finset.Icc 1 M, (1 : ℝ) := by
          refine Finset.sum_le_sum fun y hy => ?_
          rw [norm_prod]
          exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _)
            (fun i _ => norm_diffFun_le_one F c a hF i.succ _)
      _ = (M : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.card_Icc]
          norm_num
  have htsum : ∑' x : ℤ, diffFun F c a 0 x *
        (∑ y ∈ Finset.Icc 1 M, ∏ i : Fin n, diffFun F c a i.succ (x + diffShift c i.succ * (y : ℤ)))
      = ∑ x ∈ Work.Peluse.symIcc (2 * N), diffFun F c a 0 x *
        (∑ y ∈ Finset.Icc 1 M, ∏ i : Fin n, diffFun F c a i.succ (x + diffShift c i.succ * (y : ℤ))) := by
    refine tsum_eq_sum fun x hx => ?_
    have hxN : 2 * N < x.natAbs := by
      by_contra hcon
      push_neg at hcon
      exact hx ((mem_symIcc_iff (2 * N) x).mpr hcon)
    rw [hsupp0 x hxN, zero_mul]
  rw [htsum]
  calc ‖∑ x ∈ Work.Peluse.symIcc (2 * N), diffFun F c a 0 x *
        (∑ y ∈ Finset.Icc 1 M, ∏ i : Fin n, diffFun F c a i.succ (x + diffShift c i.succ * (y : ℤ)))‖
      ≤ ∑ x ∈ Work.Peluse.symIcc (2 * N), ‖diffFun F c a 0 x *
          (∑ y ∈ Finset.Icc 1 M, ∏ i : Fin n, diffFun F c a i.succ (x + diffShift c i.succ * (y : ℤ)))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ x ∈ Work.Peluse.symIcc (2 * N), 1 * (M : ℝ) := by
        refine Finset.sum_le_sum fun x hx => ?_
        rw [norm_mul]
        exact mul_le_mul (norm_diffFun_le_one F c a hF 0 x) (hinner x) (norm_nonneg _) zero_le_one
    _ = (4 * (N : ℝ) + 1) * (M : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        have hc : ((Work.Peluse.symIcc (2 * N)).card : ℝ) = 4 * (N : ℝ) + 1 := by
          rw [symIcc_card]; push_cast; ring
        rw [hc]
        ring

/-! ## The induction step -/

private lemma levelBound_succ_aux {n : ℕ} {K' : ℕ} {C' C : ℝ} (hn : 1 ≤ n) (hIH : LevelBound n K' C')
    (hC2000 : 2000 ≤ C) (hCbig : C' * (8000 : ℝ) ^ (2 * K') ≤ C)
    (hCroot : 16000 * (Real.sqrt C' + 1) ≤ C) :
    LevelBound (n + 1) (2 * K') C := by
  classical
  have hIHcopy : LevelBound n K' C' := hIH
  obtain ⟨hK'1, hC'pos, hIHmain⟩ := hIH
  have hCpos : 0 < C := by linarith
  refine ⟨by omega, hCpos, ?_⟩
  intro c hc0 N M hN hM F γ γ' hγ hγ' hγ1 hF hFs hcy hgauge hHge hLam
  -- ## numerical preliminaries
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (show 1 ≤ N by omega)
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  generalize hHdef : ⌊γ' * (M : ℝ)⌋.toNat = H at hHge
  have hH1 : 1 ≤ H := hHge
  have hHcast : (H : ℤ) = ⌊γ' * (M : ℝ)⌋ := by
    rw [← hHdef]; exact Int.toNat_of_nonneg (Int.floor_nonneg.mpr (by positivity))
  have hHle : (H : ℝ) ≤ γ' * (M : ℝ) := by
    have h2 : (⌊γ' * (M : ℝ)⌋ : ℝ) ≤ γ' * (M : ℝ) := Int.floor_le _
    calc (H : ℝ) = ((H : ℤ) : ℝ) := by simp
      _ = (⌊γ' * (M : ℝ)⌋ : ℝ) := by rw [hHcast]
      _ ≤ γ' * (M : ℝ) := h2
  have hγpow : γ ^ (2 * K') ≤ γ := by
    calc γ ^ (2 * K') ≤ γ ^ 1 := pow_le_pow_of_le_one hγ.le hγ1 (by omega)
      _ = γ := pow_one γ
  have hγ'2000 : γ' ≤ γ / 2000 := by
    have h1 : γ' ≤ γ / C := le_trans hgauge (div_le_div_of_nonneg_right hγpow hCpos.le)
    have h2 : γ / C ≤ γ / 2000 := div_le_div_of_nonneg_left hγ.le (by norm_num) hC2000
    linarith
  have hγ'1 : γ' ≤ 1 := by
    have h2 : γ / 2000 ≤ (1 : ℝ) := by
      have h3 : γ / 2000 ≤ 1 / 2000 := div_le_div_of_nonneg_right hγ1 (by norm_num)
      linarith
    linarith [hγ'2000, h2]
  have hHM : H ≤ M := by
    have h2 : (H : ℝ) ≤ (M : ℝ) := by
      have h3 : γ' * (M : ℝ) ≤ (M : ℝ) := by nlinarith [hγ'1, hMpos.le]
      linarith [hHle, h3]
    exact_mod_cast h2
  have hca : ∀ (i : Fin (n + 2)) (a : ℤ), |a| ≤ (M : ℤ) → |c i * a| ≤ (N : ℤ) := by
    intro i a ha
    have hMem : M ∈ Finset.Icc 1 M := Finset.mem_Icc.mpr ⟨by omega, le_refl M⟩
    have hMi : |c i * (M : ℤ)| ≤ (N : ℤ) := hcy M hMem i
    have hMnn : (0 : ℤ) ≤ (M : ℤ) := by positivity
    calc |c i * a| = |c i| * |a| := abs_mul _ _
      _ ≤ |c i| * (M : ℤ) := mul_le_mul_of_nonneg_left ha (abs_nonneg _)
      _ = |c i * (M : ℤ)| := by rw [abs_mul, abs_of_nonneg hMnn]
      _ ≤ (N : ℤ) := hMi
  have hmemIcc : ∀ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), |a| ≤ (M : ℤ) := by
    intro a ha
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp ha
    have hHM' : (H : ℤ) ≤ (M : ℤ) := by exact_mod_cast hHM
    rw [abs_le]
    exact ⟨by omega, by omega⟩
  have hC'le : C' ≤ C := by
    have h8 : (1 : ℝ) ≤ 8000 ^ (2 * K') := one_le_pow₀ (by norm_num)
    calc C' = C' * 1 := by ring
      _ ≤ C' * 8000 ^ (2 * K') := by nlinarith [hC'pos.le, h8]
      _ ≤ C := hCbig
  have hC'g' : C' * γ' ≤ 1 := by
    have h1 : γ' ≤ γ ^ (2 * K') / C := hgauge
    have h2 : γ ^ (2 * K') / C ≤ 1 / C := div_le_div_of_nonneg_right (by linarith [hγ1, hγ]) hCpos.le
    have h3 : γ' ≤ 1 / C := le_trans h1 h2
    have h4 : C' * (1 / C) ≤ 1 := by
      rw [mul_one_div, div_le_one hCpos]
      exact hC'le
    nlinarith [h3, h4, hC'pos.le]
  -- ## the PET step
  have hpet := Work.Peluse.PET.pet_step (ι := Fin (n + 1)) (i₀ := (0 : Fin (n + 1)))
    (N := N) (M := M) (Cne := 1) (γ := γ) (γ' := γ')
    (Q := fun (i : Fin (n + 1)) (y : ℤ) => c (i.succ) * y)
    (f := F 0) (F := fun (i : Fin (n + 1)) => F (i.succ))
    hN hM hγ hγ'
    (by
      have h4 : (1000 : ℝ) * (((1 : ℕ) : ℝ) + 1) = 2000 := by norm_num
      rw [h4]; exact hγ'2000)
    (by rw [hHdef]; exact hHge) (hF 0) (hFs 0) (fun i => hF (i.succ)) (fun i => hFs (i.succ))
    (fun i y hy => by
      have h := hcy y hy (i.succ)
      simpa using h)
    hLam
  -- ## the level-`n` averages
  set S : ℤ → ℂ := fun a => ∑' x : ℤ, diffFun F c a 0 x *
      ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin n, diffFun F c a i.succ (x + diffShift c i.succ * (y : ℤ))
    with hSdef
  set Lavg : ℤ → ℂ := fun a => ((((2 * N : ℕ)) : ℂ) * (M : ℂ))⁻¹ * S a with hLdef
  set gtil : ℤ → ℝ := fun a => min (‖Lavg a‖ ^ 2) 1 with hgdef
  set Agood : Finset ℤ := (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter (fun a => γ' ≤ gtil a ^ K' / C')
    with hAdef
  -- ### (i) the PET step, identified as the `μ_H`-average of the level-`n` averages
  have hpetS : γ / 1000 ≤
      ∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H a * ‖((N : ℂ) * (M : ℂ))⁻¹ * S a‖ := by
    have hpet' := hpet
    rw [hHdef] at hpet'
    simp only [Fin.succ_zero_eq_one] at hpet'
    refine le_trans hpet' ?_
    refine Finset.sum_le_sum fun a ha => ?_
    refine mul_le_mul_of_nonneg_left ?_ (Work.Peluse.PET.muL_nonneg H a)
    simp only [hSdef]
    exact le_of_eq (congrArg norm (pet_summand_eq F c N M a))
  -- ### (ii) the relation between the PET normalisation and the instance normalisation
  have hSrel : ∀ a : ℤ, ‖((N : ℂ) * (M : ℂ))⁻¹ * S a‖ = 2 * ‖Lavg a‖ := by
    intro a
    have h1 : ‖((N : ℂ) * (M : ℂ))⁻¹ * S a‖ = ((N : ℝ) * (M : ℝ))⁻¹ * ‖S a‖ := by
      rw [norm_mul, norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    have h2 : ‖(((((2 * N : ℕ)) : ℂ)) * (M : ℂ))⁻¹ * S a‖
        = (((2 * N : ℕ) : ℝ) * (M : ℝ))⁻¹ * ‖S a‖ := by
      rw [norm_mul, norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    rw [hLdef]
    simp only []
    rw [h1, h2]
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
    push_cast
    field_simp
  -- ### (iii) the crude bound on the level of the instances
  have hcrude : ∀ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), ‖Lavg a‖ ≤ 3 := by
    intro a ha
    have hSab : ‖S a‖ ≤ (4 * (N : ℝ) + 1) * (M : ℝ) := by
      rw [hSdef]
      simp only []
      exact norm_tsum_diffFun_le F c a hF hFs (fun i => hca i a (hmemIcc a ha))
    have h2 : ‖(((((2 * N : ℕ)) : ℂ)) * (M : ℂ))⁻¹ * S a‖
        = (((2 * N : ℕ) : ℝ) * (M : ℝ))⁻¹ * ‖S a‖ := by
      rw [norm_mul, norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
    have h4 : (((2 * N : ℕ) : ℝ) * (M : ℝ))⁻¹ * ((4 * (N : ℝ) + 1) * (M : ℝ))
        = (4 * (N : ℝ) + 1) / (2 * (N : ℝ)) := by
      have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
      have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
      push_cast
      field_simp
    have h5 : (4 * (N : ℝ) + 1) / (2 * (N : ℝ)) ≤ 3 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hN1]
    have h6 : ‖(((((2 * N : ℕ)) : ℂ)) * (M : ℂ))⁻¹ * S a‖ ≤ 3 := by
      rw [h2]
      calc (((2 * N : ℕ) : ℝ) * (M : ℝ))⁻¹ * ‖S a‖
          ≤ (((2 * N : ℕ) : ℝ) * (M : ℝ))⁻¹ * ((4 * (N : ℝ) + 1) * (M : ℝ)) :=
            mul_le_mul_of_nonneg_left hSab (by positivity)
        _ = (4 * (N : ℝ) + 1) / (2 * (N : ℝ)) := h4
        _ ≤ 3 := h5
    rw [hLdef]
    simp only []
    exact h6
  -- ### (iv) the value of `‖Lavg a‖`
  have hLval : ∀ a : ℤ, ‖Lavg a‖ ^ 2 = ‖(((((2 * N : ℕ)) : ℂ)) * (M : ℂ))⁻¹ *
      ∑' x : ℤ, diffFun F c a 0 x *
        ∑ y ∈ Finset.Icc 1 M,
          ∏ i : Fin n, diffFun F c a i.succ (x + diffShift c i.succ * (y : ℤ))‖ ^ 2 := by
    intro a
    rw [hLdef, hSdef]
  -- ### (v) the inductive hypothesis, applied to each good `a`
  have hInst : ∀ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), γ' ≤ gtil a ^ K' / C' →
      (gtil a / C') ^ K' ≤ Work.Peluse.boxNormPow n (dirFamily (diffShift c) H)
        (Work.Peluse.symIcc (2 * N)) (diffFun F c a ⟨n, by omega⟩) := by
    intro a ha hga
    have hgtil_nn : 0 ≤ gtil a := by
      rw [hgdef]; exact le_min (sq_nonneg _) zero_le_one
    have hgtil_pos : 0 < gtil a := by
      rcases eq_or_lt_of_le hgtil_nn with h | h
      · exfalso
        have h0 : gtil a ^ K' = 0 := by rw [← h]; exact zero_pow (Nat.pos_iff_ne_zero.mp hK'1)
        have h1 : (0 : ℝ) < gtil a ^ K' / C' := lt_of_lt_of_le hγ' hga
        rw [h0, zero_div] at h1
        exact absurd h1 (lt_irrefl 0)
      · exact h
    have hres : (gtil a / C') ^ K' ≤ Work.Peluse.boxNormPow n
        (dirFamily (diffShift c) (⌊γ' * (M : ℝ)⌋.toNat))
        (Work.Peluse.symIcc (2 * N)) (diffFun F c a ⟨n, by omega⟩) := by
      refine LevelBound.apply hIHcopy (diffShift c) (diffShift_zero c) (N := 2 * N) (M := M)
        (hN := by positivity) (hM := hM) (F := diffFun F c a) (γ := gtil a) (γ' := γ')
        (hγ := hgtil_pos) (hγ' := hγ') (hγ1 := min_le_right _ _) (hF := ?_) (hFs := ?_)
        (hcy := ?_) (hg := hga) (hH := by rw [hHdef]; exact hHge) (hLam := ?_)
      · intro i x; exact norm_diffFun_le_one F c a hF i x
      · intro i; exact supportIn_diffFun F c a hFs (fun i => hca i a (hmemIcc a ha)) i
      · intro y hy i; exact diffShift_abs_le c hcy hy i
      · have h1 : gtil a ≤ ‖Lavg a‖ ^ 2 := by rw [hgdef]; exact min_le_left _ _
        exact h1
    rw [hHdef] at hres
    exact hres
  -- ## the peel
  have hpeel : Work.Peluse.boxNormPow (n + 1) (dirFamily c H) (Work.Peluse.symIcc N)
        (F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩)
      = ∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H a *
          Work.Peluse.boxNormPow n
            (fun j : Fin ((n + 1) - 1) => dirFamily c H ⟨j.1 + 1, by omega⟩)
            (Work.Peluse.symIcc N)
            (fun u : ℤ => F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩
                (u + c ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ * a) *
              star (F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ u)) :=
    boxNormPow_peel_muL_all (m := n + 1) (by omega)
      (F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩)
      (hFs ⟨n + 1, Nat.lt_succ_self (n + 1)⟩) (dirFamily c H)
      (c ⟨n + 1, Nat.lt_succ_self (n + 1)⟩) hH1 (by
        rw [dirFamily]
        have hcs : (((⟨0, by omega⟩ : Fin (n + 1)).castSucc) : Fin (n + 2)) = 0 := by
          apply Fin.ext; simp
        rw [hcs, hc0, sub_zero])
  -- ## the family identification
  have hfam : (fun j : Fin ((n + 1) - 1) => dirFamily c H ⟨j.1 + 1, by omega⟩)
      = dirFamily (diffShift c) H := by
    funext i
    simp only [dirFamily, diffShift]
    have h1 : ((⟨n, by omega⟩ : Fin (n + 1)).succ : Fin (n + 2))
        = (⟨n + 1, by omega⟩ : Fin (n + 2)) := by
      apply Fin.ext; simp
    have h2 : (((⟨i.1 + 1, by omega⟩ : Fin (n + 1)).castSucc) : Fin (n + 2))
        = i.castSucc.succ := by
      apply Fin.ext; simp
    rw [h1, ← h2]
    congr 1
    ring
  -- ## the function identification
  have hfun : ∀ a : ℤ, diffFun F c a ⟨n, by omega⟩
      = fun u : ℤ => star (F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩
            (u + c ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ * a) *
          star (F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ u)) := by
    intro a
    funext u
    rw [diffFun_last]
    simp only []
    rw [star_mul, star_star]
    ring
  -- ## the box-norm chain
  have hbox : ∑ a ∈ Agood, Work.Peluse.muL H a * (gtil a / C') ^ K' ≤
      Work.Peluse.boxNormPow (n + 1) (dirFamily c H) (Work.Peluse.symIcc N)
        (F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩) := by
    rw [hpeel]
    calc ∑ a ∈ Agood, Work.Peluse.muL H a * (gtil a / C') ^ K'
        ≤ ∑ a ∈ Agood, Work.Peluse.muL H a *
            Work.Peluse.boxNormPow n (dirFamily (diffShift c) H) (Work.Peluse.symIcc (2 * N))
              (diffFun F c a ⟨n, by omega⟩) := by
          refine Finset.sum_le_sum fun a ha => ?_
          rw [hAdef] at ha
          obtain ⟨hIcc, hga⟩ := Finset.mem_filter.mp ha
          exact mul_le_mul_of_nonneg_left (hInst a hIcc hga) (Work.Peluse.PET.muL_nonneg H a)
      _ = ∑ a ∈ Agood, Work.Peluse.muL H a *
            Work.Peluse.boxNormPow n
              (fun j : Fin ((n + 1) - 1) => dirFamily c H ⟨j.1 + 1, by omega⟩)
              (Work.Peluse.symIcc (2 * N))
              (fun u : ℤ => F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩
                  (u + c ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ * a) *
                star (F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ u)) := by
          refine Finset.sum_congr rfl fun a ha => ?_
          refine congrArg (fun z => Work.Peluse.muL H a * z) ?_
          rw [hfam]
          conv_rhs => rw [← boxNormPow_star', ← hfun a]
      _ ≤ ∑ a ∈ Agood, Work.Peluse.muL H a *
            Work.Peluse.boxNormPow n
              (fun j : Fin ((n + 1) - 1) => dirFamily c H ⟨j.1 + 1, by omega⟩)
              (Work.Peluse.symIcc N)
              (fun u : ℤ => F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩
                  (u + c ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ * a) *
                star (F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ u)) := by
          refine Finset.sum_le_sum fun a ha => ?_
          refine mul_le_mul_of_nonneg_left ?_ (Work.Peluse.PET.muL_nonneg H a)
          have hcard1 : 0 < (Work.Peluse.symIcc (2 * N)).card := by
            rw [symIcc_card]; omega
          have hscal := boxNormPow_support_scaling (t := n)
            (fun j : Fin ((n + 1) - 1) => dirFamily c H ⟨j.1 + 1, by omega⟩)
            (Work.Peluse.symIcc (2 * N)) (Work.Peluse.symIcc N)
            (fun u : ℤ => F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩
                (u + c ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ * a) *
              star (F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ u)) hcard1
          have hρ : (1 : ℝ) ≤ ((Work.Peluse.symIcc (2 * N)).card : ℝ) *
              (((Work.Peluse.symIcc N).card : ℝ))⁻¹ := by
            have h1 : ((Work.Peluse.symIcc N).card : ℝ) ≤ ((Work.Peluse.symIcc (2 * N)).card : ℝ) := by
              rw [symIcc_card, symIcc_card]; push_cast; linarith
            have h2 : (0 : ℝ) < ((Work.Peluse.symIcc N).card : ℝ) := by
              rw [symIcc_card]; push_cast; positivity
            rw [← div_eq_mul_inv]
            exact (le_div_iff₀ h2).mpr (by linarith)
          have hnn : (0 : ℝ) ≤ Work.Peluse.boxNormPow n
              (fun j : Fin ((n + 1) - 1) => dirFamily c H ⟨j.1 + 1, by omega⟩)
              (Work.Peluse.symIcc (2 * N))
              (fun u : ℤ => F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩
                  (u + c ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ * a) *
                star (F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ u)) := norm_nonneg _
          have hstep := mul_le_mul_of_nonneg_right hρ hnn
          simp only [one_mul] at hstep
          rw [hscal]
          exact hstep
      _ ≤ ∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H a *
            Work.Peluse.boxNormPow n
              (fun j : Fin ((n + 1) - 1) => dirFamily c H ⟨j.1 + 1, by omega⟩)
              (Work.Peluse.symIcc N)
              (fun u : ℤ => F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩
                  (u + c ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ * a) *
                star (F ⟨n + 1, Nat.lt_succ_self (n + 1)⟩ u)) := by
          rw [hAdef]
          refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
          intro a _ _
          exact mul_nonneg (Work.Peluse.PET.muL_nonneg H a) (norm_nonneg _)
  -- ## the per-`a` lower bound
  have hper : ∀ a ∈ Agood, ‖((N : ℂ) * (M : ℂ))⁻¹ * S a‖ ^ (2 * K') /
        (6 ^ (2 * K') * C' ^ K') ≤ (gtil a / C') ^ K' := by
    intro a ha
    have hIcc : a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ) := by
      rw [hAdef] at ha; exact (Finset.mem_filter.mp ha).1
    have hcr := hcrude a hIcc
    rw [hSrel a]
    have hC'K : (0 : ℝ) < C' ^ K' := pow_pos hC'pos K'
    have hupos : (0 : ℝ) ≤ ‖Lavg a‖ := norm_nonneg _
    by_cases h1 : ‖Lavg a‖ ≤ 1
    · have hg : gtil a = ‖Lavg a‖ ^ 2 := by
        rw [hgdef]
        exact min_eq_left (by nlinarith [h1, hupos])
      rw [hg, div_pow, ← pow_mul, div_le_div_iff₀ (by positivity) hC'K, mul_pow]
      have h6 : (2 : ℝ) ^ (2 * K') ≤ 6 ^ (2 * K') :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) _
      have hu : (0 : ℝ) ≤ ‖Lavg a‖ ^ (2 * K') := pow_nonneg hupos _
      calc (2 ^ (2 * K') * ‖Lavg a‖ ^ (2 * K')) * C' ^ K'
          ≤ (6 ^ (2 * K') * ‖Lavg a‖ ^ (2 * K')) * C' ^ K' :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h6 hu) hC'K.le
        _ = ‖Lavg a‖ ^ (2 * K') * (6 ^ (2 * K') * C' ^ K') := by ring
    · push_neg at h1
      have hg : gtil a = 1 := by
        rw [hgdef]
        exact min_eq_right (by nlinarith [h1, hupos])
      rw [hg, div_le_iff₀ (by positivity)]
      have h2 : (1 / C') ^ K' * (6 ^ (2 * K') * C' ^ K') = 6 ^ (2 * K') := by
        have hne : C' ^ K' ≠ 0 := pow_ne_zero _ hC'pos.ne'
        rw [div_pow, one_pow]
        field_simp
      rw [h2]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      linarith [hcr]
  -- ## the mass of the good set
  have hmass : γ / 1000 ≤
      ∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H a * ‖((N : ℂ) * (M : ℂ))⁻¹ * S a‖ :=
    hpetS
  have hbad : ∑ a ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter
        (fun a => ¬ (γ' ≤ gtil a ^ K' / C')),
        Work.Peluse.muL H a * ‖((N : ℂ) * (M : ℂ))⁻¹ * S a‖ ≤ γ / 4000 := by
    have hterm : ∀ a ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter
        (fun a => ¬ (γ' ≤ gtil a ^ K' / C')),
        Work.Peluse.muL H a * ‖((N : ℂ) * (M : ℂ))⁻¹ * S a‖ ≤
          Work.Peluse.muL H a * (γ / 4000) := by
      intro a ha
      obtain ⟨hIcc, hnot⟩ := Finset.mem_filter.mp ha
      have hcr := hcrude a hIcc
      have hlt : gtil a ^ K' < C' * γ' := by
        have h2 : gtil a ^ K' / C' < γ' := lt_of_not_ge hnot
        rw [div_lt_iff₀ hC'pos] at h2
        linarith
      have hlt1 : gtil a < 1 := by
        by_contra hcon
        push_neg at hcon
        have h3 : (1 : ℝ) ≤ gtil a ^ K' := one_le_pow₀ hcon
        nlinarith [hlt, hC'g']
      have hlt1' : ‖Lavg a‖ ^ 2 < 1 := by
        have h : min (‖Lavg a‖ ^ 2) 1 < 1 := by
          have h2 := hlt1
          rw [hgdef] at h2
          simpa using h2
        rcases min_lt_iff.mp h with h' | h'
        · exact h'
        · exact absurd h' (lt_irrefl 1)
      have hgl : gtil a = ‖Lavg a‖ ^ 2 := by
        rw [hgdef]
        exact min_eq_left hlt1'.le
      have hpow : ‖Lavg a‖ ^ (2 * K') < (γ / 8000) ^ (2 * K') := by
        have h4 : ‖Lavg a‖ ^ (2 * K') < C' * γ' := by
          rw [hgl] at hlt
          rw [← pow_mul] at hlt
          exact hlt
        have h5 : C' * γ' ≤ (γ / 8000) ^ (2 * K') := by
          have h6 : C' * (γ ^ (2 * K') / C) ≤ γ ^ (2 * K') / 8000 ^ (2 * K') := by
            rw [← mul_div_assoc, div_le_div_iff₀ hCpos (pow_pos (by norm_num) (2 * K'))]
            have hγp : (0 : ℝ) < γ ^ (2 * K') := pow_pos hγ (2 * K')
            calc C' * γ ^ (2 * K') * 8000 ^ (2 * K')
                = (C' * 8000 ^ (2 * K')) * γ ^ (2 * K') := by ring
              _ ≤ C * γ ^ (2 * K') := mul_le_mul_of_nonneg_right hCbig hγp.le
              _ = γ ^ (2 * K') * C := by ring
          calc C' * γ' ≤ C' * (γ ^ (2 * K') / C) := by
                refine mul_le_mul_of_nonneg_left hgauge hC'pos.le
            _ ≤ γ ^ (2 * K') / 8000 ^ (2 * K') := h6
            _ = (γ / 8000) ^ (2 * K') := by rw [div_pow]
        linarith [h4, h5]
      have hu : ‖Lavg a‖ < γ / 8000 := by
        by_contra hcon
        push_neg at hcon
        have hge : (γ / 8000) ^ (2 * K') ≤ ‖Lavg a‖ ^ (2 * K') :=
          pow_le_pow_left₀ (by positivity) hcon _
        exact absurd hge (not_le.mpr hpow)
      rw [hSrel a]
      refine mul_le_mul_of_nonneg_left ?_ (Work.Peluse.PET.muL_nonneg H a)
      linarith
    calc ∑ a ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter
            (fun a => ¬ (γ' ≤ gtil a ^ K' / C')),
            Work.Peluse.muL H a * ‖((N : ℂ) * (M : ℂ))⁻¹ * S a‖
        ≤ ∑ a ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter
            (fun a => ¬ (γ' ≤ gtil a ^ K' / C')),
            Work.Peluse.muL H a * (γ / 4000) := Finset.sum_le_sum hterm
      _ = (∑ a ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter
            (fun a => ¬ (γ' ≤ gtil a ^ K' / C')), Work.Peluse.muL H a) * (γ / 4000) :=
          (Finset.sum_mul _ _ _).symm
      _ ≤ 1 * (γ / 4000) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          calc ∑ a ∈ (Finset.Icc (-(H : ℤ)) (H : ℤ)).filter
                (fun a => ¬ (γ' ≤ gtil a ^ K' / C')), Work.Peluse.muL H a
              ≤ ∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H a :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
                  (fun a _ _ => Work.Peluse.PET.muL_nonneg H a)
            _ = 1 := Work.Peluse.PET.sum_muL_Icc H hH1
      _ = γ / 4000 := by ring
  have hAgood : 3 * γ / 4000 ≤
      ∑ a ∈ Agood, Work.Peluse.muL H a * ‖((N : ℂ) * (M : ℂ))⁻¹ * S a‖ := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.Icc (-(H : ℤ)) (H : ℤ))
      (fun a => γ' ≤ gtil a ^ K' / C')
      (fun a => Work.Peluse.muL H a * ‖((N : ℂ) * (M : ℂ))⁻¹ * S a‖)
    rw [hAdef]
    linarith [hsplit, hmass, hbad]
  -- ## Jensen
  have hjensen : (∑ a ∈ Agood, Work.Peluse.muL H a * ‖((N : ℂ) * (M : ℂ))⁻¹ * S a‖) ^ (2 * K')
      ≤ ∑ a ∈ Agood, Work.Peluse.muL H a * ‖((N : ℂ) * (M : ℂ))⁻¹ * S a‖ ^ (2 * K') := by
    refine weighted_sum_pow_le Agood (fun a => Work.Peluse.muL H a)
      (fun a => ‖((N : ℂ) * (M : ℂ))⁻¹ * S a‖) (2 * K') (by omega)
      (fun a _ => Work.Peluse.PET.muL_nonneg H a) (fun a _ => norm_nonneg _) ?_
    calc ∑ a ∈ Agood, Work.Peluse.muL H a
        ≤ ∑ a ∈ Finset.Icc (-(H : ℤ)) (H : ℤ), Work.Peluse.muL H a := by
          rw [hAdef]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun a _ _ => Work.Peluse.PET.muL_nonneg H a)
      _ = 1 := Work.Peluse.PET.sum_muL_Icc H hH1
  -- ## the final arithmetic
  have hsum_lower : (γ / C) ^ (2 * K')
      ≤ ∑ a ∈ Agood, Work.Peluse.muL H a * (gtil a / C') ^ K' := by
    have hC8 : C' ≤ (C / 8000) ^ 2 := by
      have h4 : 8000 * Real.sqrt C' ≤ C := by linarith [hCroot]
      have h5 : Real.sqrt C' ≤ C / 8000 := by
        rw [le_div_iff₀ (by norm_num)]; linarith
      have h6 : (Real.sqrt C') ^ 2 ≤ (C / 8000) ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) h5 2
      rwa [Real.sq_sqrt hC'pos.le] at h6
    have hkey : (8000 : ℝ) ^ (2 * K') * C' ^ K' ≤ C ^ (2 * K') := by
      calc (8000 : ℝ) ^ (2 * K') * C' ^ K'
          ≤ 8000 ^ (2 * K') * ((C / 8000) ^ 2) ^ K' :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hC'pos.le hC8 K') (by positivity)
        _ = 8000 ^ (2 * K') * (C / 8000) ^ (2 * K') := by rw [← pow_mul]
        _ = C ^ (2 * K') := by
            rw [← mul_pow]
            congr 1
            field_simp
    have hcmp : (γ / C) ^ (2 * K')
        ≤ (1 / (6 ^ (2 * K') * C' ^ K')) * ((3 * γ) / 4000) ^ (2 * K') := by
      have hD : (0 : ℝ) < 6 ^ (2 * K') * C' ^ K' := by positivity
      have h40 : (0 : ℝ) < (4000 : ℝ) ^ (2 * K') := by positivity
      rw [div_pow,
        show (1 / (6 ^ (2 * K') * C' ^ K')) * ((3 * γ) / 4000) ^ (2 * K')
            = (3 ^ (2 * K') * γ ^ (2 * K')) / (6 ^ (2 * K') * 4000 ^ (2 * K') * C' ^ K') by
          rw [div_pow, mul_pow]
          field_simp]
      rw [div_le_div_iff₀ (pow_pos hCpos _) (by positivity)]
      have hmul : (6 : ℝ) ^ (2 * K') * 4000 ^ (2 * K') = 3 ^ (2 * K') * 8000 ^ (2 * K') := by
        rw [← mul_pow, ← mul_pow]; norm_num
      calc γ ^ (2 * K') * (6 ^ (2 * K') * 4000 ^ (2 * K') * C' ^ K')
          = 3 ^ (2 * K') * γ ^ (2 * K') * ((8000 : ℝ) ^ (2 * K') * C' ^ K') := by
            rw [hmul]; ring
        _ ≤ 3 ^ (2 * K') * γ ^ (2 * K') * C ^ (2 * K') :=
            mul_le_mul_of_nonneg_left hkey (by positivity)
    calc (γ / C) ^ (2 * K')
        ≤ (1 / (6 ^ (2 * K') * C' ^ K')) * ((3 * γ) / 4000) ^ (2 * K') := hcmp
      _ ≤ (1 / (6 ^ (2 * K') * C' ^ K')) *
            (∑ a ∈ Agood, Work.Peluse.muL H a * ‖((N : ℂ) * (M : ℂ))⁻¹ * S a‖) ^ (2 * K') := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          refine pow_le_pow_left₀ (by positivity) ?_ _
          linarith [hAgood]
      _ ≤ (1 / (6 ^ (2 * K') * C' ^ K')) *
            ∑ a ∈ Agood, Work.Peluse.muL H a * ‖((N : ℂ) * (M : ℂ))⁻¹ * S a‖ ^ (2 * K') :=
          mul_le_mul_of_nonneg_left hjensen (by positivity)
      _ = ∑ a ∈ Agood, Work.Peluse.muL H a *
            (‖((N : ℂ) * (M : ℂ))⁻¹ * S a‖ ^ (2 * K') / (6 ^ (2 * K') * C' ^ K')) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a ha => ?_
          field_simp
      _ ≤ ∑ a ∈ Agood, Work.Peluse.muL H a * (gtil a / C') ^ K' := by
          refine Finset.sum_le_sum fun a ha => ?_
          exact mul_le_mul_of_nonneg_left (hper a ha) (Work.Peluse.PET.muL_nonneg H a)
  exact le_trans hsum_lower hbox

/-! ## The base case `m = 1` -/

theorem levelBound_one : ∃ K : ℕ, ∃ C : ℝ, LevelBound 1 K C := by
  obtain ⟨K, hK, hlem⟩ := Work.Peluse.PetLinear.linear_boxnorm_control_one (m := 1) rfl
  refine ⟨K, 2000, hK, by norm_num, ?_⟩
  intro c hc0 N M hN hM F γ γ' hγ hγ' hγ1 hF hFs hcy hgauge hH hLam
  have hgauge' : γ' ≤ γ / (1000 * (((1 : ℕ) : ℝ) + 1)) := by
    have h2 : γ ^ K ≤ γ := by simpa using pow_le_pow_of_le_one hγ.le hγ1 hK
    have h3 : γ ^ K / 2000 ≤ γ / 2000 := by linarith
    have h4 : (1000 : ℝ) * (((1 : ℕ) : ℝ) + 1) = 2000 := by norm_num
    rw [h4]
    linarith
  have hmain := hlem c hc0 hN hM F hγ hγ' hγ1 hF hFs hcy hgauge' hH hLam
  refine le_trans ?_ hmain
  apply pow_le_pow_left₀ (by positivity)
  linarith

/-! ## The induction -/

theorem levelBound_succ {n : ℕ} (hn : 1 ≤ n) {K' : ℕ} {C' : ℝ} (hIH : LevelBound n K' C') :
    ∃ K : ℕ, ∃ C : ℝ, LevelBound (n + 1) K C := by
  refine ⟨2 * K', max 2000 (max (C' * (8000 : ℝ) ^ (2 * K')) (16000 * (Real.sqrt C' + 1))),
    levelBound_succ_aux hn hIH (le_max_left _ _) ?_ ?_⟩
  · exact le_trans (le_max_left _ _) (le_max_right _ _)
  · exact le_trans (le_max_right _ _) (le_max_right _ _)

theorem levelBound_all : ∀ m : ℕ, 0 < m → ∃ K : ℕ, ∃ C : ℝ, LevelBound m K C := by
  intro m hm
  induction m with
  | zero => exact absurd hm (Nat.lt_irrefl 0)
  | succ n ih =>
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; exact levelBound_one
      · obtain ⟨K', C', hL⟩ := ih hn
        exact levelBound_succ hn hL

/-- **Peluse, Lemma 4.10** (the base case of her PET induction, and the "pivot" of
`Work.Peluse.UControl.Theorem37Chapter`), specialised to polynomial shifts with zero constant term
and with the hypothesis `c 0 = 0` (without which the statement is false).

This is the *paper's* gauge: `γ' ≪_m γ^{O_m(1)}`, i.e. `γ' ≤ γ^K / C` for some `K ≪ 1`, `C > 0`
depending only on `m`.  The conclusion is the level-`m` box-norm power of the *last* function at the
direction sets `(c_m - c_i)[⌊γ'M⌋]`. -/
theorem linear_boxnorm_control_paper {m : ℕ} (hm : 0 < m) :
    ∃ K : ℕ, 1 ≤ K ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (c : Fin (m + 1) → ℤ), c 0 = 0 → ∀ {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
      (F : Fin (m + 1) → ℤ → ℂ) {γ γ' : ℝ}, 0 < γ → 0 < γ' → γ ≤ 1 →
      (∀ i x, ‖F i x‖ ≤ 1) → (∀ i, Work.Peluse.SupportIn (F i) N) →
      (∀ y ∈ Finset.Icc 1 M, ∀ i : Fin (m + 1), |c i * (y : ℤ)| ≤ (N : ℤ)) →
      γ' ≤ γ ^ K / C → 1 ≤ ⌊γ' * (M : ℝ)⌋.toNat →
      γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
          ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ ^ 2 →
      (γ / C) ^ K ≤ Work.Peluse.boxNormPow m
        (fun i : Fin m => Work.Peluse.arithIcc (c ⟨m, Nat.lt_succ_self m⟩ - c i.castSucc)
          (⌊γ' * (M : ℝ)⌋).toNat) (Work.Peluse.symIcc N) (F ⟨m, Nat.lt_succ_self m⟩) := by
  obtain ⟨K, C, hL⟩ := levelBound_all m hm
  exact ⟨K, hL.1, C, hL.2.1, hL.2.2⟩

end

end Work.Peluse.PetLinear
