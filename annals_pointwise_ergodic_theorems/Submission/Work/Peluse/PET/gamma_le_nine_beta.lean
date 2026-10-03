import Mathlib
import Submission.Work.Peluse.PET.sum_symIcc_shift_le
import Submission.Work.Peluse.PET.prod_norm_le_last

/-!
# `γ/9` is bounded by the normalised `L²` mass of the last function

The elementary Cauchy–Schwarz step of Peluse's inverse theorem, in the normalisation of
Krause–Mirek–Tao's §5: from the lower bound `γ ≤ ‖Λ‖²` for the linear multilinear average
`Λ = (NM)⁻¹ ∑_x F₀(x) ∑_{y∈[M]} ∏_{i<m} F_{i+1}(x + c_{i+1} y)` one gets

`γ/9 ≤ (∑_{x ∈ [-N,N]} ‖F_m(x)‖²) / |[-N,N]|`

whenever the `F_i` are `1`-bounded and supported in `[-N,N]`.

The proof is a two-fold Cauchy–Schwarz: in `x` first (isolating the inner `y`-sum), and then, for
each `x`, in `y`.  The last factor `F_m` dominates the product of the others (`prod_norm_le_last`)
and its averaged shifts are controlled by the unshifted `L²` mass
(`sum_symIcc_shift_le`).  Both steps lose nothing in the `y`-sum, which cancels against the
`M⁻¹` of the normalisation, and the arithmetic constant is exactly `9`: `(2N+1)² ≤ 9N²` for
`N ≥ 1`.
-/

open scoped BigOperators

namespace Work.Peluse.PET

private lemma pet_mem_symIcc_iff {N : ℕ} {x : ℤ} :
    x ∈ Work.Peluse.symIcc N ↔ x.natAbs ≤ N := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc]
  constructor
  · intro h
    have h' : |x| ≤ (N : ℤ) := abs_le.mpr h
    rw [← Int.natCast_natAbs] at h'
    exact_mod_cast h'
  · intro hx
    have h' : (x.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hx
    rw [Int.natCast_natAbs] at h'
    exact abs_le.mp h'

private lemma pet_card_symIcc (N : ℕ) : (Work.Peluse.symIcc N).card = 2 * N + 1 := by
  rw [Work.Peluse.symIcc, Int.card_Icc]
  omega

private lemma pet_card_symIcc_real (N : ℕ) :
    (((Work.Peluse.symIcc N).card : ℕ) : ℝ) = 2 * (N : ℝ) + 1 := by
  rw [pet_card_symIcc N]
  push_cast
  ring

private lemma pet_card_Icc_one (M : ℕ) : (Finset.Icc 1 M).card = M := by
  rw [Nat.card_Icc]
  omega

/-- Cauchy–Schwarz for a complex-valued finite sum: `‖∑ u v‖² ≤ (∑ ‖u‖²)(∑ ‖v‖²)`. -/
private lemma pet_cs {ι : Type*} (s : Finset ι) (u v : ι → ℂ) :
    ‖∑ x ∈ s, u x * v x‖ ^ 2 ≤ (∑ x ∈ s, ‖u x‖ ^ 2) * (∑ x ∈ s, ‖v x‖ ^ 2) := by
  have h1 : ‖∑ x ∈ s, u x * v x‖ ≤ ∑ x ∈ s, ‖u x‖ * ‖v x‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul]
  calc ‖∑ x ∈ s, u x * v x‖ ^ 2
      ≤ (∑ x ∈ s, ‖u x‖ * ‖v x‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ (∑ x ∈ s, ‖u x‖ ^ 2) * (∑ x ∈ s, ‖v x‖ ^ 2) :=
        Finset.sum_mul_sq_le_sq_mul_sq s (fun x => ‖u x‖) (fun x => ‖v x‖)

theorem gamma_le_nine_beta {m : ℕ} (hm : 0 < m) {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (c : Fin (m + 1) → ℤ) (F : Fin (m + 1) → ℤ → ℂ) {γ : ℝ} (hγ : 0 < γ)
    (hF : ∀ i x, ‖F i x‖ ≤ 1) (hFs : ∀ i, Work.Peluse.SupportIn (F i) N)
    (hLam : γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * ∑' x : ℤ, F 0 x *
        ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ ^ 2) :
    γ / 9 ≤ (∑ x ∈ Work.Peluse.symIcc N, ‖F ⟨m, Nat.lt_succ_self m⟩ x‖ ^ 2)
      / (((Work.Peluse.symIcc N).card : ℕ) : ℝ) := by
  classical
  set W : ℤ → ℂ := fun x => ∑ y ∈ Finset.Icc 1 M,
      ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ)) with hW
  set S : ℝ := ∑ x ∈ Work.Peluse.symIcc N, ‖F ⟨m, Nat.lt_succ_self m⟩ x‖ ^ 2 with hS
  set Z : ℂ := ∑ x ∈ Work.Peluse.symIcc N, F 0 x * W x with hZ
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hSnn : 0 ≤ S := by rw [hS]; positivity
  -- ### Step 0: the `tsum` over `ℤ` is a finite sum over the support of `F 0`
  have htsum : (∑' x : ℤ, F 0 x * ∑ y ∈ Finset.Icc 1 M,
        ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))) = Z := by
    have hside : ∀ x : ℤ, x ∉ Work.Peluse.symIcc N → F 0 x *
        ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ)) = 0 := by
      intro x hx
      have hxN : N < x.natAbs := lt_of_not_ge fun hle => hx (pet_mem_symIcc_iff.mpr hle)
      rw [hFs 0 x hxN, zero_mul]
    rw [hZ, tsum_eq_sum (s := Work.Peluse.symIcc N) hside]
  have hLamZ : γ ≤ ‖((N : ℂ) * (M : ℂ))⁻¹ * Z‖ ^ 2 := by
    rw [← htsum]
    exact hLam
  -- ### Step 1: peel off the normalising factor
  have hnorm : ‖((N : ℂ) * (M : ℂ))⁻¹ * Z‖ = ((N : ℝ) * (M : ℝ))⁻¹ * ‖Z‖ := by
    rw [norm_mul, norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have hγ1 : γ ≤ (((N : ℝ) * (M : ℝ))⁻¹ * ‖Z‖) ^ 2 := by
    rw [← hnorm]
    exact hLamZ
  -- ### Step 2: Cauchy–Schwarz, first in `x` and then in `y`
  have hZbd : ‖Z‖ ^ 2 ≤ (2 * (N : ℝ) + 1) * ((M : ℝ) ^ 2 * S) := by
    have hFA : ∑ x ∈ Work.Peluse.symIcc N, ‖F 0 x‖ ^ 2 ≤ 2 * (N : ℝ) + 1 := by
      calc ∑ x ∈ Work.Peluse.symIcc N, ‖F 0 x‖ ^ 2
          ≤ ∑ x ∈ Work.Peluse.symIcc N, (1 : ℝ) :=
            Finset.sum_le_sum fun x _ => pow_le_one₀ (norm_nonneg _) (hF 0 x)
        _ = 2 * (N : ℝ) + 1 := by
            rw [Finset.sum_const, nsmul_eq_mul, mul_one, pet_card_symIcc_real]
    have hFB : ∑ x ∈ Work.Peluse.symIcc N, ‖W x‖ ^ 2 ≤ (M : ℝ) ^ 2 * S := by
      -- for each `x`, Cauchy–Schwarz in `y`
      have hstep1 : ∀ x : ℤ, ‖W x‖ ^ 2 ≤ (M : ℝ) *
          ∑ y ∈ Finset.Icc 1 M,
            ‖∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ ^ 2 := by
        intro x
        have hcs := pet_cs (Finset.Icc 1 M) (fun _ : ℕ => (1 : ℂ))
          (fun y : ℕ => ∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ)))
        simp only [one_mul, norm_one, one_pow] at hcs
        have hcard : (∑ _y ∈ Finset.Icc 1 M, (1 : ℝ)) = (M : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_one, pet_card_Icc_one]
        rw [hcard] at hcs
        rw [hW]
        exact hcs
      -- the product is dominated by its last factor
      have hstep2 : ∑ x ∈ Work.Peluse.symIcc N, ∑ y ∈ Finset.Icc 1 M,
            ‖∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ ^ 2
          ≤ ∑ x ∈ Work.Peluse.symIcc N, ∑ y ∈ Finset.Icc 1 M,
            ‖F ⟨m, Nat.lt_succ_self m⟩
              (x + c ⟨m, Nat.lt_succ_self m⟩ * (y : ℤ))‖ ^ 2 := by
        refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => ?_
        have hp := prod_norm_le_last hm c F hF x y
        rw [norm_prod Finset.univ]
        exact pow_le_pow_left₀ (Finset.prod_nonneg fun i _ => norm_nonneg _) hp 2
      -- the shifted `L²` mass of the last factor
      have hstep3 : ∀ y ∈ Finset.Icc 1 M,
          ∑ x ∈ Work.Peluse.symIcc N,
            ‖F ⟨m, Nat.lt_succ_self m⟩
              (x + c ⟨m, Nat.lt_succ_self m⟩ * (y : ℤ))‖ ^ 2 ≤ S := by
        intro y _
        have hsupp : Work.Peluse.SupportIn
            (fun z : ℤ => ((‖F ⟨m, Nat.lt_succ_self m⟩ z‖ ^ 2 : ℝ) : ℂ)) N := by
          intro z hz
          simp only [hFs ⟨m, Nat.lt_succ_self m⟩ z hz, norm_zero]
          norm_num
        have hG : ∀ t : ℤ,
            ‖((‖F ⟨m, Nat.lt_succ_self m⟩ t‖ ^ 2 : ℝ) : ℂ)‖
              = ‖F ⟨m, Nat.lt_succ_self m⟩ t‖ ^ 2 :=
          fun t => Complex.norm_of_nonneg (sq_nonneg _)
        have h := sum_symIcc_shift_le hsupp (c ⟨m, Nat.lt_succ_self m⟩) (y : ℤ)
        rw [hS]
        simpa only [hG] using h
      calc ∑ x ∈ Work.Peluse.symIcc N, ‖W x‖ ^ 2
          ≤ ∑ x ∈ Work.Peluse.symIcc N, (M : ℝ) *
              ∑ y ∈ Finset.Icc 1 M,
                ‖∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ ^ 2 :=
            Finset.sum_le_sum fun x _ => hstep1 x
        _ = (M : ℝ) * ∑ x ∈ Work.Peluse.symIcc N, ∑ y ∈ Finset.Icc 1 M,
                ‖∏ i : Fin m, F i.succ (x + c i.succ * (y : ℤ))‖ ^ 2 := by
            rw [Finset.mul_sum]
        _ ≤ (M : ℝ) * ∑ x ∈ Work.Peluse.symIcc N, ∑ y ∈ Finset.Icc 1 M,
                ‖F ⟨m, Nat.lt_succ_self m⟩
                  (x + c ⟨m, Nat.lt_succ_self m⟩ * (y : ℤ))‖ ^ 2 :=
            mul_le_mul_of_nonneg_left hstep2 (by positivity)
        _ = (M : ℝ) * ∑ y ∈ Finset.Icc 1 M, ∑ x ∈ Work.Peluse.symIcc N,
                ‖F ⟨m, Nat.lt_succ_self m⟩
                  (x + c ⟨m, Nat.lt_succ_self m⟩ * (y : ℤ))‖ ^ 2 := by
            rw [Finset.sum_comm]
        _ ≤ (M : ℝ) * ∑ _y ∈ Finset.Icc 1 M, S :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum hstep3) (by positivity)
        _ = (M : ℝ) ^ 2 * S := by
            rw [Finset.sum_const, nsmul_eq_mul, pet_card_Icc_one]
            ring
    calc ‖Z‖ ^ 2
        = ‖∑ x ∈ Work.Peluse.symIcc N, F 0 x * W x‖ ^ 2 := by rw [hZ]
      _ ≤ (∑ x ∈ Work.Peluse.symIcc N, ‖F 0 x‖ ^ 2) *
            (∑ x ∈ Work.Peluse.symIcc N, ‖W x‖ ^ 2) :=
          pet_cs (Work.Peluse.symIcc N) (fun x => F 0 x) W
      _ ≤ (2 * (N : ℝ) + 1) * ((M : ℝ) ^ 2 * S) :=
          mul_le_mul hFA hFB (by positivity) (by positivity)
  -- ### Step 3: the arithmetic
  have hγ2 : γ ≤ ((2 * (N : ℝ) + 1) * S) / (N : ℝ) ^ 2 := by
    have hNM : (((N : ℝ) * (M : ℝ))⁻¹) ^ 2 * ((2 * (N : ℝ) + 1) * ((M : ℝ) ^ 2 * S))
        = ((2 * (N : ℝ) + 1) * S) / (N : ℝ) ^ 2 := by
      have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
      have hMne : (M : ℝ) ≠ 0 := ne_of_gt hMpos
      field_simp
    calc γ ≤ (((N : ℝ) * (M : ℝ))⁻¹ * ‖Z‖) ^ 2 := hγ1
      _ = (((N : ℝ) * (M : ℝ))⁻¹) ^ 2 * ‖Z‖ ^ 2 := by ring
      _ ≤ (((N : ℝ) * (M : ℝ))⁻¹) ^ 2 * ((2 * (N : ℝ) + 1) * ((M : ℝ) ^ 2 * S)) :=
          mul_le_mul_of_nonneg_left hZbd (by positivity)
      _ = ((2 * (N : ℝ) + 1) * S) / (N : ℝ) ^ 2 := hNM
  have h9 : (2 * (N : ℝ) + 1) ^ 2 ≤ 9 * (N : ℝ) ^ 2 := by
    have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith
  have hfinal : γ / 9 ≤ S / (2 * (N : ℝ) + 1) := by
    have hmain : ((2 * (N : ℝ) + 1) * S) / (N : ℝ) ^ 2 ≤ (S / (2 * (N : ℝ) + 1)) * 9 := by
      rw [div_le_iff₀ (pow_pos hNpos 2), div_mul_eq_mul_div, div_mul_eq_mul_div,
        le_div_iff₀ (by positivity : (0 : ℝ) < 2 * (N : ℝ) + 1)]
      nlinarith [h9, hSnn]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 9)]
    linarith
  rw [pet_card_symIcc_real]
  exact hfinal

end Work.Peluse.PET
