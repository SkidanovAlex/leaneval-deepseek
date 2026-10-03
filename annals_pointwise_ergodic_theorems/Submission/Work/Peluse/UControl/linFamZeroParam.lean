import Mathlib
import Submission.Work.Peluse.UControl.peluseProp34Defs
import Submission.Work.Peluse.UControl.linFamAvg_zero_term
import Submission.Work.Peluse.Crux.boxNormPow_singleton
import Submission.Work.Peluse.BoxNormDilation.dilated_directions_ge
import Submission.Work.Peluse.Peel.arithIcc_sum_window_eq
import Submission.Work.Peluse.Peel.tsum_sq_eq_sum_symIcc
import Submission.Work.Peluse.Track.boxNormPow_v2_degenerate
import Submission.Work.Peluse.UControl.assemblyDefs

/-!
# `Work.Peluse.UControl.linFamZeroParam`

The PET chapter of Peluse's Proposition 3.4 produces, for a datum `D` and a parameter-dependent
constant term `β`, the lower bound `γ ≤ linFamAvg D l c N M H f b β` for the *average*, over the
parameter box `D.parBox l H`, of the moduli of the multilinear correlations along the linear
configuration with the datum's own directions `petDir D l c a i`.

The present file extracts from that average a **box-norm** lower bound, and it does so at the
*zero* parameter.  The point is that at the zero parameter every direction of the datum vanishes:

* `petDir D l c (0 : D.Idx l) i = 0` (`linFamAvg_zero_term.lean`, from the factor `a (l-1) s` carried
  by every summand of the level-`(l-1)` direction), and
* `arithIcc 0 H = {0}` for `H ≥ 1`,

so the direction family of the box norm is the constant family of singletons `{0}` and the box-norm
power collapses to the normalised `ℓ^{2^t}`-mass of `f`
(`Work.Peluse.Crux.boxNormPow_singleton`, at `t := Fintype.card (D.I (l-1))`).

What remains is the passage from the average to the mass.  Every fibre `linCore a` is bounded by the
`ℓ¹`-mass over `N`, `‖linCore a‖ ≤ (∑_{x∈[-N,N]} ‖f x‖)/N`, so the average bound `γ ≤ linFamAvg`
forces that mass to be at least `γ N`; the power-mean (Hölder) inequality

`(∑ ‖f x‖)^p ≤ (2N+1)^{p-1} ∑ ‖f x‖^p`

then converts it into the mass bound `γ^p N / 3^{p-1} ≤ ∑_x ‖f x‖^p` that the collapsed box norm
needs.  With `p := 2^{|I_{l-1}|}` and the window `(4 Cne + 1) N ≥ 2 ((4 Cne + 1) N)` the constants
close because `(4C+2)^p ≥ 3^{p-1}(8C+3)` for `C ≥ 1`, `p ≥ 4`.

Note that the *shift* hypothesis of the statement (the bound on `petDir a i · y + β a i` at the zero
parameter) is not needed for this consequence: at the zero parameter the directions vanish and the
collapse of the box norm is a purely algebraic fact about `f`.

**What the conclusion says, unwound.**  For `t := Fintype.card (D.I (l-1))` and the window
`S := symIcc ((4 Cne + 1) N)`,

`(γ/(4 Cne + 2))^K ≤ boxNormPow t dirs S f`

is *equivalent* to the mass bound

`(γ/(4 Cne + 2))^K ≤ (1/|S|) · ∑_{x ∈ symIcc N} ‖f x‖^{2^t}`,

so the lemma is a lower bound for the `ℓ^{2^t}`-mass of `f` rather than a bound for a
non-degenerate box norm.  It is proved here with `K := 2^{|I_{l-1}|}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Peluse.UControl

noncomputable section

open Work.Peluse

/-! ## 1. Two elementary set facts -/

/-- `0[H] = {0}` for `H ≥ 1`. -/
private lemma zp_arithIcc_zero (H : ℕ) (hH : 1 ≤ H) : arithIcc (0 : ℤ) H = {0} := by
  ext x
  simp only [arithIcc, Finset.mem_image, Finset.mem_Icc, Finset.mem_singleton]
  constructor
  · rintro ⟨n, -, hnx⟩
    rw [← hnx]; ring
  · intro hx
    exact ⟨1, ⟨le_refl 1, hH⟩, by rw [hx]; ring⟩

/-- The cardinality of the symmetric interval. -/
private lemma zp_card_symIcc (L : ℕ) : (symIcc L).card = 2 * L + 1 := by
  rw [symIcc, Int.card_Icc,
    show (L : ℤ) + 1 - (-(L : ℤ)) = ((2 * L + 1 : ℕ) : ℤ) by push_cast; ring,
    Int.toNat_natCast]

/-! ## 2. The mass bound for a fibre of `linFamAvg` -/

/-- A function supported in `[-N,N]` has its `tsum` over `ℤ` concentrated on `symIcc N`. -/
private lemma zp_tsum_eq_sum_symIcc {N : ℕ} {g : ℤ → ℂ} (h : SupportIn g N) :
    ∑' x : ℤ, g x = ∑ x ∈ symIcc N, g x := by
  refine tsum_eq_sum (fun x hx => ?_)
  have hxN : N < x.natAbs := by
    by_contra hcon
    exact hx ((symIcc_mem_iff_natAbs N x).mpr (by omega))
  exact h x hxN

/-- **The mass bound for the fibre of `linFamAvg`.**  The modulus of the multilinear correlation at
the parameter `a` is bounded by `‖f‖_{ℓ¹}/N`: every slot function is a translate of `f` or of its
conjugate, hence `1`-bounded, and the `y`-sum has exactly `M` terms. -/
private lemma zp_linCore_le_mass {D : IdxDatum} {l N M : ℕ} {c : ℤ} {f : ℤ → ℂ}
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
    (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ) (hN : 0 < N) (hM : 0 < M)
    (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (hfs : SupportIn f N) (a : D.Idx l) :
    ‖linCore D l c N M f b β a‖ ≤ (∑ x ∈ symIcc N, ‖f x‖) / (N : ℝ) := by
  classical
  have hstep : linCore D l c N M f b β a
      = ((N : ℂ) * (M : ℂ))⁻¹ * ∑ x ∈ symIcc N, f x *
          ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin (Fintype.card (D.I (l - 1))),
            (if b i then star (f (x + (petDir D l c a i * (y : ℤ) + β a i)))
              else f (x + (petDir D l c a i * (y : ℤ) + β a i))) := by
    unfold linCore
    congr 1
    exact zp_tsum_eq_sum_symIcc (g := fun x : ℤ => f x *
      ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin (Fintype.card (D.I (l - 1))),
        (if b i then star (f (x + (petDir D l c a i * (y : ℤ) + β a i)))
          else f (x + (petDir D l c a i * (y : ℤ) + β a i))))
      (fun x hx => by simp only [hfs x hx, zero_mul])
  rw [hstep, norm_mul]
  have hnorm : ‖((N : ℂ) * (M : ℂ))⁻¹‖ = ((N : ℝ) * (M : ℝ))⁻¹ := by
    rw [norm_inv, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  rw [hnorm]
  have hZ : ‖∑ x ∈ symIcc N, f x *
        ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin (Fintype.card (D.I (l - 1))),
          (if b i then star (f (x + (petDir D l c a i * (y : ℤ) + β a i)))
            else f (x + (petDir D l c a i * (y : ℤ) + β a i)))‖
      ≤ (M : ℝ) * ∑ x ∈ symIcc N, ‖f x‖ := by
    calc ‖∑ x ∈ symIcc N, f x *
          ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin (Fintype.card (D.I (l - 1))),
            (if b i then star (f (x + (petDir D l c a i * (y : ℤ) + β a i)))
              else f (x + (petDir D l c a i * (y : ℤ) + β a i)))‖
        ≤ ∑ x ∈ symIcc N, ‖f x *
            ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin (Fintype.card (D.I (l - 1))),
              (if b i then star (f (x + (petDir D l c a i * (y : ℤ) + β a i)))
                else f (x + (petDir D l c a i * (y : ℤ) + β a i)))‖ := norm_sum_le _ _
      _ ≤ ∑ x ∈ symIcc N, ‖f x‖ * (M : ℝ) := by
          refine Finset.sum_le_sum fun x _ => ?_
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
          calc ‖∑ y ∈ Finset.Icc 1 M, ∏ i : Fin (Fintype.card (D.I (l - 1))),
                (if b i then star (f (x + (petDir D l c a i * (y : ℤ) + β a i)))
                  else f (x + (petDir D l c a i * (y : ℤ) + β a i)))‖
              ≤ ∑ y ∈ Finset.Icc 1 M, ‖∏ i : Fin (Fintype.card (D.I (l - 1))),
                  (if b i then star (f (x + (petDir D l c a i * (y : ℤ) + β a i)))
                    else f (x + (petDir D l c a i * (y : ℤ) + β a i)))‖ := norm_sum_le _ _
            _ ≤ ∑ _y ∈ Finset.Icc 1 M, (1 : ℝ) := by
                refine Finset.sum_le_sum fun y _ => ?_
                rw [norm_prod]
                refine Finset.prod_le_one₀ (fun i _ => norm_nonneg _) fun i _ => ?_
                by_cases hbi : b i
                · simp only [hbi, if_true, norm_star]; exact hf _
                · simp only [hbi, if_false]; exact hf _
            _ = (M : ℝ) := by
                rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
                norm_num
      _ = (M : ℝ) * ∑ x ∈ symIcc N, ‖f x‖ := by
          rw [← Finset.sum_mul, mul_comm]
  calc ((N : ℝ) * (M : ℝ))⁻¹ * ‖∑ x ∈ symIcc N, f x *
        ∑ y ∈ Finset.Icc 1 M, ∏ i : Fin (Fintype.card (D.I (l - 1))),
          (if b i then star (f (x + (petDir D l c a i * (y : ℤ) + β a i)))
            else f (x + (petDir D l c a i * (y : ℤ) + β a i)))‖
      ≤ ((N : ℝ) * (M : ℝ))⁻¹ * ((M : ℝ) * ∑ x ∈ symIcc N, ‖f x‖) :=
        mul_le_mul_of_nonneg_left hZ (by positivity)
    _ = (∑ x ∈ symIcc N, ‖f x‖) / (N : ℝ) := by
        have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
        field_simp

/-! ## 3. The average is bounded by the mass -/

/-- **`linFamAvg` is bounded by the `ℓ¹`-mass over `N`.** -/
private lemma zp_linFamAvg_le_mass {D : IdxDatum} {l N M H : ℕ} {c : ℤ} {f : ℤ → ℂ}
    (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
    (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ) (hN : 0 < N) (hM : 0 < M)
    (hf : ∀ x : ℤ, ‖f x‖ ≤ 1) (hfs : SupportIn f N) :
    linFamAvg D l c N M H f b β ≤ (∑ x ∈ symIcc N, ‖f x‖) / (N : ℝ) := by
  classical
  rw [linFamAvg_eq_card_mul_sum]
  have hz : (0 : D.Idx l) ∈ D.parBox l H := by
    rw [IdxDatum.mem_parBox]
    intro j s
    simp
  have hBpos : (0 : ℝ) < ((D.parBox l H).card : ℝ) := by
    have h : 0 < (D.parBox l H).card := Finset.card_pos.mpr ⟨_, hz⟩
    exact_mod_cast h
  calc ((D.parBox l H).card : ℝ)⁻¹ * ∑ a ∈ D.parBox l H, ‖linCore D l c N M f b β a‖
      ≤ ((D.parBox l H).card : ℝ)⁻¹ *
          ∑ _a ∈ D.parBox l H, (∑ x ∈ symIcc N, ‖f x‖) / (N : ℝ) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => ?_) (by positivity)
        exact zp_linCore_le_mass b β hN hM hf hfs a
    _ = (∑ x ∈ symIcc N, ‖f x‖) / (N : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul, inv_mul_cancel_left₀ (ne_of_gt hBpos)]

/-! ## 4. The collapse of the box norm at the zero parameter -/

/-- **The box-norm power at the zero parameter is the normalised `ℓ^{2^t}`-mass of `f`.**  At the
zero parameter every direction vanishes, so the direction family is the constant family `{0}`. -/
private lemma zp_boxPow_zero {D : IdxDatum} {l N' H : ℕ} {c : ℤ} {f : ℤ → ℂ}
    (hl : 2 ≤ l) (hH : 1 ≤ H) (hcard : 2 ≤ Fintype.card (D.I (l - 1)))
    (hfs : SupportIn f N') :
    boxNormPow (Fintype.card (D.I (l - 1)))
        (fun i : Fin (Fintype.card (D.I (l - 1))) =>
          arithIcc (petDir D l c (0 : D.Idx l) i) H)
        (symIcc N') f
      = ((symIcc N').card : ℝ)⁻¹ *
          ∑' x : ℤ, ‖f x‖ ^ (2 ^ (Fintype.card (D.I (l - 1)))) := by
  have ht1 : 1 ≤ Fintype.card (D.I (l - 1)) := by omega
  have hdirs : (fun i : Fin (Fintype.card (D.I (l - 1))) =>
        arithIcc (petDir D l c (0 : D.Idx l) i) H)
      = (fun _ : Fin (Fintype.card (D.I (l - 1))) => ({0} : Finset ℤ)) := by
    funext i
    rw [IdxDatum.petDir_zero D hl c i, zp_arithIcc_zero H hH]
  rw [hdirs]
  exact Crux.boxNormPow_singleton ht1 (0 : ℤ) (symIcc N') f (FinSuppZ.of_supportIn hfs)

/-! ## 5. The real arithmetic -/

/-- The power-mean (Hölder) inequality in the form needed here. -/
private lemma zp_holder {s : Finset ℤ} {g : ℤ → ℝ} (hg : ∀ x ∈ s, 0 ≤ g x)
    {p : ℕ} (hp : 1 ≤ p) :
    (∑ x ∈ s, g x) ^ p ≤ ((s.card : ℝ)) ^ (p - 1) * ∑ x ∈ s, g x ^ p := by
  have h := pow_sum_le_card_mul_sum_pow (s := s) (f := g) hg (p - 1)
  simpa [Nat.sub_add_cancel hp] using h

/-- `(4C+2)^p ≥ 3^{p-1}(8C+3)` for `C ≥ 1`, `p ≥ 4`. -/
private lemma zp_pow_big {C : ℝ} {p : ℕ} (hC : 1 ≤ C) (hp : 4 ≤ p) :
    3 ^ (p - 1) * (8 * C + 3) ≤ (4 * C + 2) ^ p := by
  have hp1 : 1 ≤ p := by omega
  have hC6 : 6 ≤ 4 * C + 2 := by linarith
  have h2 : (6 : ℝ) ^ (p - 1) ≤ (4 * C + 2) ^ (p - 1) :=
    pow_le_pow_left₀ (by norm_num) hC6 (p - 1)
  have h3 : (8 : ℝ) ≤ (2 : ℝ) ^ (p - 1) := by
    have h : (2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ (p - 1) := pow_le_pow_right₀ (by norm_num) (by omega)
    norm_num at h
    exact h
  have h4 : (6 : ℝ) ^ (p - 1) = (2 : ℝ) ^ (p - 1) * (3 : ℝ) ^ (p - 1) := by
    rw [← mul_pow]; norm_num
  have h5 : 8 * C + 3 ≤ (4 * C + 2) * (2 : ℝ) ^ (p - 1) := by
    have h6 : (4 * C + 2) * 8 ≤ (4 * C + 2) * (2 : ℝ) ^ (p - 1) :=
      mul_le_mul_of_nonneg_left h3 (by linarith)
    nlinarith [h6]
  have hsucc : (4 * C + 2) ^ (p - 1) * (4 * C + 2) = (4 * C + 2) ^ p := by
    rw [← pow_succ, Nat.sub_add_cancel hp1]
  calc 3 ^ (p - 1) * (8 * C + 3)
      ≤ 3 ^ (p - 1) * ((4 * C + 2) * 2 ^ (p - 1)) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)
    _ = (4 * C + 2) * ((2 : ℝ) ^ (p - 1) * 3 ^ (p - 1)) := by ring
    _ = (4 * C + 2) * (6 : ℝ) ^ (p - 1) := by rw [h4]
    _ ≤ (4 * C + 2) * (4 * C + 2) ^ (p - 1) :=
        mul_le_mul_of_nonneg_left h2 (by linarith)
    _ = (4 * C + 2) ^ p := by rw [mul_comm, hsucc]

/-- **The mass lower bound.**  From `γ · N ≤ A` and the power-mean inequality for `A` one gets the
lower bound `γ^p N/3^{p-1}` for the `p`-th mass of `f` on `symIcc N`. -/
private lemma zp_mass_lower {γ : ℝ} {N p : ℕ} {A T : ℝ}
    (hN : 1 ≤ N) (hγ : 0 < γ) (hp : 1 ≤ p)
    (hA : γ * (N : ℝ) ≤ A)
    (hH : A ^ p ≤ (((2 * N + 1 : ℕ) : ℝ)) ^ (p - 1) * T) :
    γ ^ p * (N : ℝ) / 3 ^ (p - 1) ≤ T := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have h3N : (0 : ℝ) < 3 * (N : ℝ) := by linarith
  have hcard : (((2 * N + 1 : ℕ) : ℝ)) = 2 * (N : ℝ) + 1 := by push_cast; ring
  have hcardpos : (0 : ℝ) < (((2 * N + 1 : ℕ) : ℝ)) := by rw [hcard]; linarith
  have hγN : 0 ≤ γ * (N : ℝ) := by positivity
  have h1 : (γ * (N : ℝ)) ^ p ≤ A ^ p := pow_le_pow_left₀ hγN hA p
  have h2 : (γ * (N : ℝ)) ^ p / (((2 * N + 1 : ℕ) : ℝ)) ^ (p - 1) ≤ T := by
    have hdiv := div_le_div_of_nonneg_right h1 (le_of_lt (pow_pos hcardpos (p - 1)))
    have hH' : A ^ p ≤ T * (((2 * N + 1 : ℕ) : ℝ)) ^ (p - 1) := by linarith [hH]
    have hT := (div_le_iff₀ (pow_pos hcardpos (p - 1))).mpr hH'
    linarith [hdiv, hT]
  have h3 : (((2 * N + 1 : ℕ) : ℝ)) ^ (p - 1) ≤ (3 * (N : ℝ)) ^ (p - 1) := by
    rw [hcard]
    exact pow_le_pow_left₀ (by linarith) (by linarith) (p - 1)
  have h4 : (γ * (N : ℝ)) ^ p / (3 * (N : ℝ)) ^ (p - 1)
      ≤ (γ * (N : ℝ)) ^ p / (((2 * N + 1 : ℕ) : ℝ)) ^ (p - 1) := by
    rw [div_le_div_iff₀ (by positivity) (pow_pos hcardpos (p - 1))]
    have hmul := mul_le_mul_of_nonneg_left h3 (pow_nonneg hγN p)
    linarith [hmul]
  have h5 : (γ * (N : ℝ)) ^ p / (3 * (N : ℝ)) ^ (p - 1) = γ ^ p * (N : ℝ) / 3 ^ (p - 1) := by
    rw [mul_pow, mul_pow,
      show (N : ℝ) ^ p = (N : ℝ) ^ (p - 1) * (N : ℝ) by
        rw [← pow_succ, Nat.sub_add_cancel hp]]
    have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    field_simp
  exact le_trans (h5 ▸ h4) h2

/-- **The final arithmetic.**  From the mass lower bound `γ^p N/3^{p-1} ≤ T` one gets the box-norm
bound with the window `symIcc ((4C+1)N)` and the constant `(γ/(4C+2))^p`. -/
private lemma zp_final_arith {C : ℝ} {N : ℕ} {γ T : ℝ} {p : ℕ}
    (hC : 1 ≤ C) (hN : 1 ≤ N) (hγ : 0 < γ) (hp : 4 ≤ p)
    (hT0 : 0 ≤ T) (hT : γ ^ p * (N : ℝ) / 3 ^ (p - 1) ≤ T) :
    (γ / (4 * C + 2)) ^ p ≤ (1 / (2 * ((4 * C + 1) * (N : ℝ)) + 1)) * T := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hCpos : (0 : ℝ) < C := lt_of_lt_of_le one_pos hC
  have hd1 : (0 : ℝ) < 2 * ((4 * C + 1) * (N : ℝ)) + 1 := by positivity
  have hd2 : (0 : ℝ) < (8 * C + 3) * (N : ℝ) := by nlinarith
  have hd : 2 * ((4 * C + 1) * (N : ℝ)) + 1 ≤ (8 * C + 3) * (N : ℝ) := by nlinarith [hN1]
  have hinv : 1 / ((8 * C + 3) * (N : ℝ)) ≤ 1 / (2 * ((4 * C + 1) * (N : ℝ)) + 1) :=
    (one_div_le_one_div hd2 hd1).mpr hd
  have hstep : 1 / ((8 * C + 3) * (N : ℝ)) * (γ ^ p * (N : ℝ) / 3 ^ (p - 1))
      ≤ (1 / (2 * ((4 * C + 1) * (N : ℝ)) + 1)) * T := by
    have hx : 1 / ((8 * C + 3) * (N : ℝ)) * (γ ^ p * (N : ℝ) / 3 ^ (p - 1))
        ≤ 1 / ((8 * C + 3) * (N : ℝ)) * T :=
      mul_le_mul_of_nonneg_left hT (by positivity)
    have hy : 1 / ((8 * C + 3) * (N : ℝ)) * T
        ≤ (1 / (2 * ((4 * C + 1) * (N : ℝ)) + 1)) * T :=
      mul_le_mul_of_nonneg_right hinv hT0
    linarith [hx, hy]
  have hval : 1 / ((8 * C + 3) * (N : ℝ)) * (γ ^ p * (N : ℝ) / 3 ^ (p - 1))
      = γ ^ p / (3 ^ (p - 1) * (8 * C + 3)) := by
    have h1 : (8 * C + 3) ≠ 0 := by positivity
    have h2 : (N : ℝ) ≠ 0 := ne_of_gt hNpos
    have h3 : (3 : ℝ) ^ (p - 1) ≠ 0 := pow_ne_zero _ (by norm_num)
    field_simp
  have hle : (γ / (4 * C + 2)) ^ p ≤ γ ^ p / (3 ^ (p - 1) * (8 * C + 3)) := by
    rw [div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
    have hbig := zp_pow_big hC hp
    have hmul := mul_le_mul_of_nonneg_left hbig (le_of_lt (pow_pos hγ p))
    linarith [hmul]
  exact le_trans hle (hval ▸ hstep)

/-! ## 6. The theorem -/

theorem linFamZeroParam {l : ℕ} (D : Work.Peluse.UControl.IdxDatum) (c : ℤ) (hl : 2 ≤ l) :
    ∃ K : ℕ, 1 ≤ K ∧
      ∀ (N M H : ℕ) (f : ℤ → ℂ) (Cne : ℕ) (γ : ℝ)
        (b : Fin (Fintype.card (D.I (l - 1))) → Bool)
        (β : D.Idx l → Fin (Fintype.card (D.I (l - 1))) → ℤ),
        2 ≤ Fintype.card (D.I (l - 1)) → 1 ≤ N → 2 ≤ M → 1 ≤ Cne → 1 ≤ H →
        0 < γ → γ ≤ 1 → (∀ x : ℤ, ‖f x‖ ≤ 1) → Work.Peluse.SupportIn f N →
        (∀ i : Fin (Fintype.card (D.I (l - 1))), ∀ y ∈ Finset.Icc 1 M,
          |Work.Peluse.UControl.petDir D l c (0 : D.Idx l) i * (y : ℤ) + β 0 i|
            ≤ (Cne : ℤ) * (N : ℤ)) →
        γ ≤ Work.Peluse.UControl.linFamAvg D l c N M H f b β →
        (γ / (4 * (Cne : ℝ) + 2)) ^ K ≤
          Work.Peluse.boxNormPow (Fintype.card (D.I (l - 1)))
            (fun i : Fin (Fintype.card (D.I (l - 1))) =>
              Work.Peluse.arithIcc (Work.Peluse.UControl.petDir D l c (0 : D.Idx l) i) H)
            (Work.Peluse.symIcc ((4 * Cne + 1) * N)) f := by
  refine ⟨2 ^ Fintype.card (D.I (l - 1)), one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2), ?_⟩
  intro N M H f Cne γ b β hcard hN hM hCne hH hγ _hγ1 hf hfs _hsh havg
  have hNpos : 0 < N := by omega
  have hMpos : 0 < M := by omega
  have hp1 : 1 ≤ 2 ^ Fintype.card (D.I (l - 1)) := one_le_pow₀ (by norm_num : (1 : ℕ) ≤ 2)
  have hp4 : 4 ≤ 2 ^ Fintype.card (D.I (l - 1)) := by
    have h : 2 ^ 2 ≤ 2 ^ Fintype.card (D.I (l - 1)) :=
      Nat.pow_le_pow_right (by norm_num) hcard
    simpa using h
  -- the `ℓ¹`-mass dominates `γ N`
  have hγN : γ * (N : ℝ) ≤ ∑ x ∈ symIcc N, ‖f x‖ := by
    have h1 : γ ≤ (∑ x ∈ symIcc N, ‖f x‖) / (N : ℝ) :=
      le_trans havg (zp_linFamAvg_le_mass b β hNpos hMpos hf hfs)
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < (N : ℝ))).mp h1
  -- the power-mean inequality
  have hholder : (∑ x ∈ symIcc N, ‖f x‖) ^ (2 ^ Fintype.card (D.I (l - 1)))
      ≤ (((2 * N + 1 : ℕ) : ℝ)) ^ (2 ^ Fintype.card (D.I (l - 1)) - 1) *
        (∑ x ∈ symIcc N, ‖f x‖ ^ (2 ^ Fintype.card (D.I (l - 1)))) := by
    have h := zp_holder (s := symIcc N) (g := fun x : ℤ => ‖f x‖)
      (fun x _ => norm_nonneg _) (p := 2 ^ Fintype.card (D.I (l - 1))) hp1
    rwa [zp_card_symIcc] at h
  -- the `p`-th mass, as a `tsum`
  have hTfinset : (∑' x : ℤ, ‖f x‖ ^ (2 ^ Fintype.card (D.I (l - 1))))
      = ∑ x ∈ symIcc N, ‖f x‖ ^ (2 ^ Fintype.card (D.I (l - 1))) := by
    refine tsum_eq_sum (fun x hx => ?_)
    have hxN : N < x.natAbs := by
      by_contra hcon
      exact hx ((symIcc_mem_iff_natAbs N x).mpr (by omega))
    rw [hfs x hxN, norm_zero, zero_pow (by positivity : 2 ^ Fintype.card (D.I (l - 1)) ≠ 0)]
  have hmass : γ ^ (2 ^ Fintype.card (D.I (l - 1))) * (N : ℝ)
        / 3 ^ (2 ^ Fintype.card (D.I (l - 1)) - 1)
      ≤ ∑' x : ℤ, ‖f x‖ ^ (2 ^ Fintype.card (D.I (l - 1))) := by
    rw [hTfinset]
    exact zp_mass_lower hN hγ hp1 hγN hholder
  have hT0 : 0 ≤ ∑' x : ℤ, ‖f x‖ ^ (2 ^ Fintype.card (D.I (l - 1))) :=
    tsum_nonneg fun x => by positivity
  -- the collapse of the box norm
  have hle4 : N ≤ (4 * Cne + 1) * N := by
    calc N = 1 * N := (one_mul N).symm
      _ ≤ (4 * Cne + 1) * N := Nat.mul_le_mul_right N (by omega)
  have hcollapse := zp_boxPow_zero (D := D) (l := l) (N' := (4 * Cne + 1) * N) (H := H)
    (c := c) (f := f) hl hH hcard (SupportIn.mono hfs hle4)
  have hS : ((symIcc ((4 * Cne + 1) * N)).card : ℝ)
      = 2 * ((4 * (Cne : ℝ) + 1) * (N : ℝ)) + 1 := by
    rw [zp_card_symIcc]; push_cast; ring
  have hCneR : (1 : ℝ) ≤ (Cne : ℝ) := by exact_mod_cast hCne
  calc (γ / (4 * (Cne : ℝ) + 2)) ^ (2 ^ Fintype.card (D.I (l - 1)))
      ≤ (1 / (2 * ((4 * (Cne : ℝ) + 1) * (N : ℝ)) + 1)) *
          (∑' x : ℤ, ‖f x‖ ^ (2 ^ Fintype.card (D.I (l - 1)))) :=
        zp_final_arith hCneR hN hγ hp4 hT0 hmass
    _ = boxNormPow (Fintype.card (D.I (l - 1)))
          (fun i : Fin (Fintype.card (D.I (l - 1))) =>
            arithIcc (petDir D l c (0 : D.Idx l) i) H)
          (symIcc ((4 * Cne + 1) * N)) f := by
        rw [hcollapse, hS, inv_eq_one_div]

end

end Work.Peluse.UControl
