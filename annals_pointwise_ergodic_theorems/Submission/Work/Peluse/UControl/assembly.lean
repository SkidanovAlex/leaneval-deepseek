import Mathlib
import Submission.Work.Peluse.Concat.boxNormPow_succ_ge_general
import Submission.Work.Peluse.UControl.assemblyDefs

/-!
# Assembling `CoreChapter` from its two chapters

`Submission/Work/Peluse/UControl/assemblyDefs.lean` defines the data hypotheses `Hyp`, the
conclusion `Concl`, and the two chapters `PiecePet` (the paper's Propositions 3.4 + 3.6 at a fixed
level) and `PieceBand` (the complementary regime).  This module proves the *level bookkeeping* that
combines them into `CoreChapter P`:

* the Gowers–Cauchy–Schwarz level raising `uNormPow_level_raise`: a lower bound at level `s₀` gives
  one at every level `s ≥ s₀`, at the price of raising the `γ`-exponent by `2^{s-s₀}`;
* the exponent reduction (`Hyp.mono_exp`): the data's hypotheses at exponent `K` imply those at any
  smaller positive exponent, because `γ ≤ 1` and `γδ' ≤ 1`;
* the direction bound (`dir_bound_of_ge`): in the regime `C ≥ |κ|` the smallness hypothesis
  `C·L ≤ γ^K N₁` forces `κL ≤ N₁`, so that the AP `κ[L]` lies inside the ambient interval and the
  level raising applies;
* the arithmetic of the assembly (`assembly_arith`).
-/

set_option autoImplicit false
open scoped BigOperators
open Polynomial

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-! ## Elementary consequences of `Hyp` -/

/-- The data's hypotheses at exponent `K` imply those at any smaller positive exponent (because
`γ ≤ 1` and `γδ' ≤ 1`). -/
theorem Hyp.mono_exp {P : Polynomial ℤ} {A' C : ℝ} {K K' : ℕ} {N N₁ : ℕ} {g₀ g₁ g₂ : ℤ → ℂ}
    {γ δ' : ℝ} (h : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ') (hK : K' ≤ K) (hK1 : 1 ≤ K') :
    Hyp P A' C K' N N₁ g₀ g₁ g₂ γ δ' := by
  obtain ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2, hC1, hK1', hsm, hnd, hs0, hs1, hs2,
    hb0, hb1, hb2, hΛ⟩ := h
  refine ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2, hC1, hK1, ?_, ?_, hs0, hs1, hs2,
    hb0, hb1, hb2, hΛ⟩
  · have hγ : γ ^ K ≤ γ ^ K' := pow_le_pow_of_le_one hγ0.le hγ1 hK
    have hN₁nn : (0 : ℝ) ≤ (N₁ : ℝ) := Nat.cast_nonneg _
    calc C * (dirLen P δ' N : ℝ) ≤ γ ^ K * (N₁ : ℝ) := hsm
      _ ≤ γ ^ K' * (N₁ : ℝ) := mul_le_mul_of_nonneg_right hγ hN₁nn
  · have hγδ0 : 0 ≤ γ * δ' := by positivity
    have hγδ1 : γ * δ' ≤ 1 := by nlinarith
    have h2 : (0 : ℝ) ≤ (δ' * (N : ℝ)) ^ 2 := sq_nonneg _
    have h : (γ * δ') ^ K ≤ (γ * δ') ^ K' := pow_le_pow_of_le_one hγδ0 hγδ1 hK
    calc C ≤ (γ * δ') ^ K * (δ' * (N : ℝ)) ^ 2 := hnd
      _ ≤ (γ * δ') ^ K' * (δ' * (N : ℝ)) ^ 2 := mul_le_mul_of_nonneg_right h h2

/-- The direction length is positive: the side condition `C ≤ (γδ')^K(δ'N)²` forces `δ'N ≥ 1`. -/
theorem Hyp.one_le_dirLen {P : Polynomial ℤ} {A' C : ℝ} {K : ℕ} {N N₁ : ℕ} {g₀ g₁ g₂ : ℤ → ℂ}
    {γ δ' : ℝ} (h : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ') : 1 ≤ dirLen P δ' N := by
  obtain ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2, hC1, hK1, hsm, hnd, hs0, hs1, hs2,
    hb0, hb1, hb2, hΛ⟩ := h
  have hγδ0 : 0 ≤ γ * δ' := by positivity
  have hγδ1 : γ * δ' ≤ 1 := by nlinarith
  have hpow : (γ * δ') ^ K ≤ 1 := pow_le_one₀ hγδ0 hγδ1
  have hN₁pos : (0 : ℝ) < (N₁ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN₁)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hside : (1 : ℝ) ≤ (δ' * (N : ℝ)) ^ 2 := by
    have hC1' : (1 : ℝ) ≤ C := hC1
    nlinarith [hnd, hC1', hpow, sq_nonneg (δ' * (N:ℝ)), hδ0, hNpos]
  have hδN : 1 ≤ δ' * (N : ℝ) := by nlinarith [hside, mul_pos hδ0 hNpos]
  have hδNp : 1 ≤ δ' * (N : ℝ) ^ P.natDegree := by
    have hNd1 : (1 : ℝ) ≤ (N : ℝ) ^ (P.natDegree - 1) :=
      one_le_pow₀ (show (1 : ℝ) ≤ (N : ℝ) by exact_mod_cast hN)
    have h1 : (1 : ℝ) ≤ (δ' * (N : ℝ)) * (N : ℝ) ^ (P.natDegree - 1) :=
      by simpa using (mul_le_mul hδN hNd1 zero_le_one (le_trans zero_le_one hδN))
    have h2 : (δ' * (N : ℝ)) * (N : ℝ) ^ (P.natDegree - 1) = δ' * (N : ℝ) ^ P.natDegree := by
      have hp : (P.natDegree - 1) + 1 = P.natDegree := Nat.sub_add_cancel (by omega)
      calc (δ' * (N : ℝ)) * (N : ℝ) ^ (P.natDegree - 1)
          = δ' * ((N : ℝ) ^ (P.natDegree - 1) * (N : ℝ)) := by ring
        _ = δ' * (N : ℝ) ^ ((P.natDegree - 1) + 1) := by rw [← pow_succ]
        _ = δ' * (N : ℝ) ^ P.natDegree := by rw [hp]
    linarith [h1, h2.le, h2.ge]
  have hfloor : (1 : ℤ) ≤ ⌊δ' * (N : ℝ) ^ P.natDegree⌋ := Int.le_floor.mpr (by exact_mod_cast hδNp)
  have h0 : (0 : ℤ) ≤ ⌊δ' * (N : ℝ) ^ P.natDegree⌋ := le_trans (by norm_num) hfloor
  have h2 : (1 : ℤ) ≤ ((⌊δ' * (N : ℝ) ^ P.natDegree⌋).toNat : ℤ) := by
    rw [Int.toNat_of_nonneg h0]; exact hfloor
  have : (1 : ℕ) ≤ dirLen P δ' N := by
    rw [dirLen]; exact_mod_cast h2
  exact this

/-- In the regime `C ≥ |κ|`, the data's smallness hypothesis implies the direction bound in the
absolute-value form `|κ|·L ≤ N₁`. -/
theorem abs_dir_bound_of_ge {P : Polynomial ℤ} {A' C : ℝ} {K : ℕ} {N N₁ : ℕ} {g₀ g₁ g₂ : ℤ → ℂ}
    {γ δ' : ℝ} (h : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ')
    (hC : ((|dirCoeff P| : ℤ) : ℝ) ≤ C) :
    ((|dirCoeff P| : ℤ) : ℝ) * (dirLen P δ' N : ℝ) ≤ (N₁ : ℝ) := by
  obtain ⟨hd, hN, hN₁, hγ0, hγ1, hδ0, hδ1, hwin, hsc1, hsc2, hC1, hK1, hsm, hnd, hs0, hs1, hs2,
    hb0, hb1, hb2, hΛ⟩ := h
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le zero_lt_one hC1
  have hN₁pos : (0 : ℝ) < (N₁ : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN₁)
  have hγK : γ ^ K ≤ 1 := pow_le_one₀ hγ0.le hγ1
  have hCL : ((|dirCoeff P| : ℤ) : ℝ) * (dirLen P δ' N : ℝ) ≤ C * (dirLen P δ' N : ℝ) :=
    mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg _)
  have hsplit : C * (dirLen P δ' N : ℝ) ≤ γ ^ K * (N₁ : ℝ) := hsm
  have hle : γ ^ K * (N₁ : ℝ) ≤ (N₁ : ℝ) := mul_le_of_le_one_left hN₁pos.le hγK
  exact le_trans hCL (le_trans hsplit hle)

/-- In the regime `C ≥ |κ|`, the data's smallness hypothesis implies the direction bound
`κ·L ≤ N₁` (the form in which `PiecePet` needs it). -/
theorem dir_bound_of_ge {P : Polynomial ℤ} {A' C : ℝ} {K : ℕ} {N N₁ : ℕ} {g₀ g₁ g₂ : ℤ → ℂ}
    {γ δ' : ℝ} (h : Hyp P A' C K N N₁ g₀ g₁ g₂ γ δ')
    (hC : ((|dirCoeff P| : ℤ) : ℝ) ≤ C) :
    (dirCoeff P) * (dirLen P δ' N : ℤ) ≤ (N₁ : ℤ) := by
  have hkey := abs_dir_bound_of_ge h hC
  have h2 : ((dirCoeff P : ℝ) * (dirLen P δ' N : ℝ)) ≤ (N₁ : ℝ) := by
    have h1 : (dirCoeff P : ℝ) ≤ ((|dirCoeff P| : ℤ) : ℝ) := by
      exact_mod_cast (le_abs_self (dirCoeff P))
    calc (dirCoeff P : ℝ) * (dirLen P δ' N : ℝ)
        ≤ ((|dirCoeff P| : ℤ) : ℝ) * (dirLen P δ' N : ℝ) :=
          mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg _)
      _ ≤ (N₁ : ℝ) := hkey
  have h3 : (((dirCoeff P) * (dirLen P δ' N : ℤ) : ℤ) : ℝ) ≤ (N₁ : ℝ) := by
    push_cast
    exact h2
  exact_mod_cast h3

/-! ## The Gowers–Cauchy–Schwarz level raising -/

/-- **Level raising for the uniformity-norm power.**  For `1 ≤ s₀ ≤ s`, a nonempty direction set
`Q` contained in the ambient interval `[-N,N]`, and a `1`-bounded `f` supported in `[-N,N]`, there
is `c > 0` (depending only on `s₀, s`) with

  `c · (‖f‖^{2^{s₀}}_{U^{s₀}_Q([-N,N])})^{2^{s-s₀}} ≤ ‖f‖^{2^s}_{U^s_Q([-N,N])}`.

This is `Work.Peluse.Concat.boxNormPow_succ_ge_general` iterated `s - s₀` times. -/
theorem uNormPow_level_raise (s₀ s : ℕ) (hs : 1 ≤ s₀) (hss : s₀ ≤ s) :
    ∃ c : ℝ, 0 < c ∧ ∀ (Q : Finset ℤ) (N : ℕ) (f : ℤ → ℂ),
      Q.Nonempty → 0 < N → (∀ a ∈ Q, |a| ≤ (N : ℤ)) → SupportIn f N →
      (∀ x : ℤ, ‖f x‖ ≤ 1) →
      c * (uNormPow s₀ Q (symIcc N) f) ^ (2 ^ (s - s₀)) ≤ uNormPow s Q (symIcc N) f := by
  induction s, hss using Nat.le_induction with
  | base =>
      refine ⟨1, one_pos, ?_⟩
      intro Q N f hQ hN hbd hsupp hbdd
      have hpow : (2 : ℕ) ^ (s₀ - s₀) = 1 := by rw [Nat.sub_self, pow_zero]
      rw [hpow, pow_one, one_mul]
  | succ s hs₀s ih =>
      obtain ⟨c, hc0, hc⟩ := ih
      obtain ⟨C, hC0, hC⟩ := Concat.boxNormPow_succ_ge_general s
      refine ⟨C * c ^ 2, by positivity, ?_⟩
      intro Q N f hQ hN hbd hsupp hbdd
      have hstep := hC (fun _ : Fin (s + 1) => Q) f
        (fun _ => hQ) hN (fun _ a ha => hbd a ha) hsupp hbdd
      have hstep' : C * (uNormPow s Q (symIcc N) f) ^ 2 ≤ uNormPow (s + 1) Q (symIcc N) f := by
        simpa only [uNormPow] using hstep
      have hprev := hc Q N f hQ hN hbd hsupp hbdd
      have hpow : (2 : ℕ) ^ (s + 1 - s₀) = 2 ^ (s - s₀) * 2 := by
        rw [show s + 1 - s₀ = (s - s₀) + 1 by omega, pow_succ]
      have hU0 : (0 : ℝ) ≤ uNormPow s₀ Q (symIcc N) f := by
        rw [uNormPow, boxNormPow]
        exact norm_nonneg _
      calc C * c ^ 2 * (uNormPow s₀ Q (symIcc N) f) ^ (2 ^ (s + 1 - s₀))
          = C * (c * (uNormPow s₀ Q (symIcc N) f) ^ (2 ^ (s - s₀))) ^ 2 := by
            rw [hpow, mul_pow]; ring
        _ ≤ C * (uNormPow s Q (symIcc N) f) ^ 2 :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_nonneg hc0.le (pow_nonneg hU0 _)) hprev 2)
              hC0.le
        _ ≤ uNormPow (s + 1) Q (symIcc N) f := hstep'

/-! ## The arithmetic of the assembly -/

/-- From a fixed-level conclusion `γ^{K'} ≤ Cp·A'^{K'}·γ^{-K'}·U₀` (i.e. the box-norm power is at
least `γ^{2K'}/(Cp·A'^{K'})`). -/
theorem pet_arith {A' Cp γ U₀ : ℝ} {K' : ℕ} (hA' : 0 < A') (hCp : 0 < Cp) (hγ0 : 0 < γ)
    (h : γ ^ K' ≤ Cp * A' ^ K' * γ⁻¹ ^ K' * U₀) :
    γ ^ (2 * K') / (Cp * A' ^ K') ≤ U₀ := by
  have hden : (0 : ℝ) < Cp * A' ^ K' := mul_pos hCp (pow_pos hA' _)
  have hγ3 : γ ^ K' * γ⁻¹ ^ K' = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (ne_of_gt hγ0), one_pow]
  have h2 : γ ^ K' * γ ^ K' ≤ U₀ * (Cp * A' ^ K') := by
    nlinarith [h, hγ3, pow_pos hCp K', pow_pos hA' K', pow_pos hγ0 K',
      mul_pos (mul_pos hCp (pow_pos hA' K')) (pow_pos hγ0 K'), mul_pos hCp (pow_pos hA' K')]
  rw [div_le_iff₀ hden]
  calc γ ^ (2 * K') = γ ^ K' * γ ^ K' := by
        rw [two_mul, pow_add]
    _ ≤ U₀ * (Cp * A' ^ K') := h2

/-- The arithmetic of the level-raising assembly: applying the fixed-level chapter at the reduced
exponent `K'` and raising the level from `s₀` to `s` (a factor `2^{s-s₀} = Δ` in the exponent)
produces the target's inequality. -/
theorem assembly_arith {A' C Cp c C₂ γ U₀ U_s : ℝ} {K K' Δ : ℕ}
    (hA' : 1 ≤ A') (hC : 1 ≤ C) (hCp : 0 < Cp) (hc : 0 < c) (hC₂0 : 0 < C₂)
    (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hU0 : γ ^ (2 * K') / (Cp * A' ^ K') ≤ U₀)
    (hraise : c * U₀ ^ Δ ≤ U_s)
    (hKΔ : K' * Δ ≤ K) (hC2 : Cp ^ Δ / c ≤ C₂) :
    γ ^ K ≤ C₂ * C * A' ^ K * γ⁻¹ ^ K * U_s := by
  have hApos : (0 : ℝ) < A' := lt_of_lt_of_le zero_lt_one hA'
  have hden : (0 : ℝ) < Cp * A' ^ K' := mul_pos hCp (pow_pos hApos _)
  -- (1) raise the fixed-level bound to the power `Δ`
  have h1 : γ ^ (2 * K' * Δ) ≤ U₀ ^ Δ * (Cp ^ Δ * A' ^ (K' * Δ)) := by
    have h0 : γ ^ (2 * K') ≤ U₀ * (Cp * A' ^ K') := (div_le_iff₀ hden).mp hU0
    have h := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ γ ^ (2 * K')) h0 Δ
    rwa [mul_pow, mul_pow, ← pow_mul, ← pow_mul] at h
  -- (2) insert the level raising
  have h2 : c * (γ ^ (2 * K' * Δ) / (Cp ^ Δ * A' ^ (K' * Δ))) ≤ U_s := by
    have hden2 : (0 : ℝ) < Cp ^ Δ * A' ^ (K' * Δ) := by positivity
    have h4 : c * γ ^ (2 * K' * Δ) ≤ U_s * (Cp ^ Δ * A' ^ (K' * Δ)) := by
      calc c * γ ^ (2 * K' * Δ) ≤ c * (U₀ ^ Δ * (Cp ^ Δ * A' ^ (K' * Δ))) :=
            mul_le_mul_of_nonneg_left h1 hc.le
        _ = (c * U₀ ^ Δ) * (Cp ^ Δ * A' ^ (K' * Δ)) := by ring
        _ ≤ U_s * (Cp ^ Δ * A' ^ (K' * Δ)) := mul_le_mul_of_nonneg_right hraise (le_of_lt hden2)
    rw [show c * (γ ^ (2 * K' * Δ) / (Cp ^ Δ * A' ^ (K' * Δ)))
        = (c * γ ^ (2 * K' * Δ)) / (Cp ^ Δ * A' ^ (K' * Δ)) by ring]
    exact (div_le_iff₀ hden2).mpr h4
  -- (3) the two comparison factors
  have hγK : γ ^ K ≤ γ ^ (2 * K' * Δ) * γ⁻¹ ^ K := by
    have hle : 2 * (K' * Δ) ≤ 2 * K := by omega
    have h2' : γ ^ (2 * K) ≤ γ ^ (2 * (K' * Δ)) := pow_le_pow_of_le_one hγ0.le hγ1 hle
    rw [show 2 * (K' * Δ) = 2 * K' * Δ by ring] at h2'
    have hid : γ ^ (2 * K) * γ⁻¹ ^ K = γ ^ K := by
      rw [show 2 * K = K + K by ring, pow_add, inv_pow]
      field_simp
    rw [← hid]
    exact mul_le_mul_of_nonneg_right h2' (pow_nonneg (le_of_lt (inv_pos.mpr hγ0)) K)
  have hA3 : (1 : ℝ) ≤ A' ^ K / A' ^ (K' * Δ) := by
    rw [one_le_div (pow_pos hApos _)]
    exact pow_le_pow_right₀ hA' hKΔ
  have hstep : γ ^ K / Cp ^ Δ ≤
      A' ^ K * γ⁻¹ ^ K * (γ ^ (2 * K' * Δ) / (Cp ^ Δ * A' ^ (K' * Δ))) := by
    have h3 : γ ^ K * 1 ≤ (γ ^ (2 * K' * Δ) * γ⁻¹ ^ K) * (A' ^ K / A' ^ (K' * Δ)) :=
      mul_le_mul hγK hA3 zero_le_one (by positivity)
    have h4 : γ ^ K ≤ (γ ^ (2 * K' * Δ) * γ⁻¹ ^ K) * (A' ^ K / A' ^ (K' * Δ)) := by
      simpa using h3
    calc γ ^ K / Cp ^ Δ
        ≤ ((γ ^ (2 * K' * Δ) * γ⁻¹ ^ K) * (A' ^ K / A' ^ (K' * Δ))) / Cp ^ Δ :=
          div_le_div_of_nonneg_right h4 (le_of_lt (pow_pos hCp Δ))
      _ = A' ^ K * γ⁻¹ ^ K * (γ ^ (2 * K' * Δ) / (Cp ^ Δ * A' ^ (K' * Δ))) := by
          field_simp
          try ring
  have hcK : c * (γ ^ K / Cp ^ Δ) ≤ A' ^ K * γ⁻¹ ^ K * U_s := by
    have h3 : c * (γ ^ K / Cp ^ Δ)
        ≤ c * (A' ^ K * γ⁻¹ ^ K * (γ ^ (2 * K' * Δ) / (Cp ^ Δ * A' ^ (K' * Δ)))) :=
      mul_le_mul_of_nonneg_left hstep hc.le
    refine le_trans h3 ?_
    calc c * (A' ^ K * γ⁻¹ ^ K * (γ ^ (2 * K' * Δ) / (Cp ^ Δ * A' ^ (K' * Δ))))
        = A' ^ K * γ⁻¹ ^ K * (c * (γ ^ (2 * K' * Δ) / (Cp ^ Δ * A' ^ (K' * Δ)))) := by ring
      _ ≤ A' ^ K * γ⁻¹ ^ K * U_s := mul_le_mul_of_nonneg_left h2 (by positivity)
  -- (4) conclude
  have hC2' : (1 : ℝ) ≤ C₂ * C * c / Cp ^ Δ := by
    have h4 : Cp ^ Δ ≤ C₂ * c := by
      have h5 : (Cp ^ Δ / c) * c ≤ C₂ * c := mul_le_mul_of_nonneg_right hC2 hc.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hc)] at h5
    have h6 : (1 : ℝ) ≤ C₂ * c / Cp ^ Δ := (one_le_div (pow_pos hCp Δ)).mpr h4
    have h7 : C₂ * c / Cp ^ Δ ≤ C₂ * C * c / Cp ^ Δ := by
      have h8 : C₂ * c ≤ C₂ * C * c := by
        calc C₂ * c = C₂ * c * 1 := (mul_one _).symm
          _ ≤ C₂ * c * C := by
              exact mul_le_mul_of_nonneg_left hC
                (mul_nonneg (le_of_lt hC₂0) (by linarith : (0:ℝ) ≤ c))
          _ = C₂ * C * c := by ring
      exact div_le_div_of_nonneg_right h8 (le_of_lt (pow_pos hCp Δ))
    exact le_trans h6 h7
  have hfin : γ ^ K ≤ C₂ * C * (c * (γ ^ K / Cp ^ Δ)) := by
    have h9 : γ ^ K ≤ (C₂ * C * c / Cp ^ Δ) * γ ^ K := by
      calc γ ^ K = 1 * γ ^ K := (one_mul _).symm
        _ ≤ (C₂ * C * c / Cp ^ Δ) * γ ^ K :=
            mul_le_mul_of_nonneg_right hC2' (pow_nonneg hγ0.le K)
    calc γ ^ K ≤ (C₂ * C * c / Cp ^ Δ) * γ ^ K := h9
      _ = C₂ * C * (c * (γ ^ K / Cp ^ Δ)) := by ring
  calc γ ^ K ≤ C₂ * C * (c * (γ ^ K / Cp ^ Δ)) := hfin
    _ ≤ C₂ * C * (A' ^ K * γ⁻¹ ^ K * U_s) := mul_le_mul_of_nonneg_left hcK (by positivity)
    _ = C₂ * C * A' ^ K * γ⁻¹ ^ K * U_s := by ring

end

end Work.Peluse.UControl
