import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.large_sieve_bessel

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option maxHeartbeats 1000000
set_option linter.unnecessarySimpa false

namespace Work.BMF

open Polynomial Finset Real Complex

/-! ### Elementary facts about the additive character `eC t = exp(2πit)` -/

private lemma lsm_eC_add (a b : ℝ) : eC (a + b) = eC a * eC b := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma lsm_norm_eC (t : ℝ) : ‖eC t‖ = 1 := by
  unfold eC
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]

private lemma lsm_conj_eC (t : ℝ) : star (eC t) = eC (-t) := by
  change (starRingEnd ℂ) (eC t) = eC (-t)
  unfold eC
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private lemma lsm_eC_star_sub (a b : ℝ) :
    eC (-a) * star (eC (-b)) = star (eC (a - b)) := by
  have h1 : star (eC (-b)) = eC b := by
    rw [lsm_conj_eC]; congr 1; ring
  have h2 : star (eC (a - b)) = eC (b - a) := by
    rw [lsm_conj_eC]; congr 1; ring
  rw [h1, h2, ← lsm_eC_add (-a) b]
  congr 1
  ring

/-- Every complex number can be rotated onto its (nonnegative real) norm by a unit `eC θ`. -/
private lemma lsm_exists_eC_mul_eq_norm (z : ℂ) : ∃ θ : ℝ, eC θ * z = (‖z‖ : ℂ) := by
  rcases eq_or_ne z 0 with hz | hz
  · rw [hz]; exact ⟨0, by simp [eC]⟩
  · refine ⟨-(z.arg) / (2 * Real.pi), ?_⟩
    have hzarg : (‖z‖ : ℂ) * Complex.exp (↑z.arg * Complex.I) = z :=
      Complex.norm_mul_exp_arg_mul_I z
    have hpi : (Real.pi : ℂ) ≠ 0 := by
      intro h
      exact Real.pi_ne_zero (Complex.ofReal_injective (by simpa using h))
    have hexp : eC (-(z.arg) / (2 * Real.pi)) = Complex.exp (-(↑z.arg) * Complex.I) := by
      unfold eC
      rw [show (2 : ℂ) * ↑Real.pi * I * ↑(-(z.arg) / (2 * Real.pi)) = -(↑z.arg) * I by
        push_cast
        field_simp]
    rw [hexp]
    calc Complex.exp (-(↑z.arg) * Complex.I) * z
        = Complex.exp (-(↑z.arg) * Complex.I)
            * ((‖z‖ : ℂ) * Complex.exp (↑z.arg * Complex.I)) := by rw [hzarg]
      _ = (‖z‖ : ℂ)
            * (Complex.exp (-(↑z.arg) * Complex.I) * Complex.exp (↑z.arg * Complex.I)) := by ring
      _ = (‖z‖ : ℂ) * Complex.exp (-(↑z.arg) * Complex.I + ↑z.arg * Complex.I) := by
            rw [Complex.exp_add]
      _ = (‖z‖ : ℂ) * Complex.exp 0 := by
            rw [show -(↑z.arg) * Complex.I + ↑z.arg * Complex.I = 0 by ring]
      _ = (‖z‖ : ℂ) := by rw [Complex.exp_zero, mul_one]

private lemma lsm_norm_ofReal_of_nonneg (a : ℝ) (ha : 0 ≤ a) : ‖((a : ℝ) : ℂ)‖ = a := by
  have hsq : ‖((a : ℝ) : ℂ)‖ ^ 2 = a ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal]; ring
  calc ‖((a : ℝ) : ℂ)‖ = Real.sqrt (‖((a : ℝ) : ℂ)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (a ^ 2) := by rw [hsq]
    _ = a := Real.sqrt_sq ha

/-! ### The Gram / difference-phase identity -/

private lemma lsm_eC_conj_sum (s : Finset ℕ) (P Q : ℝ[X]) :
    (∑ n ∈ s, eC (-(P.eval (n : ℝ))) * star (eC (-(Q.eval (n : ℝ)))))
      = star (∑ n ∈ s, eC (P.eval (n : ℝ) - Q.eval (n : ℝ))) := by
  rw [star_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [lsm_eC_star_sub]

/-! ### Counting naturals in real intervals -/

private lemma lsm_natIcc_subset {a₁ a₂ b₁ b₂ : ℝ} (ha : a₂ ≤ a₁) (hb : b₁ ≤ b₂) :
    natIcc a₁ b₁ ⊆ natIcc a₂ b₂ := by
  rw [natIcc, natIcc]
  exact Finset.Icc_subset_Icc (Nat.ceil_mono ha) (Nat.floor_mono hb)

private lemma lsm_natIcc_card_le (a b : ℝ) (hb : 0 ≤ b) (hab : a ≤ b) :
    ((natIcc a b).card : ℝ) ≤ b - a + 1 := by
  rw [natIcc]
  rcases le_or_gt (Nat.ceil a) (Nat.floor b) with h | h
  · rw [Nat.card_Icc,
      Nat.cast_sub (by omega : Nat.ceil a ≤ Nat.floor b + 1), Nat.cast_add, Nat.cast_one]
    have h1 : ((Nat.floor b : ℕ) : ℝ) ≤ b := Nat.floor_le hb
    have h2 : a ≤ ((Nat.ceil a : ℕ) : ℝ) := Nat.le_ceil a
    linarith
  · rw [Finset.Icc_eq_empty (by omega : ¬ Nat.ceil a ≤ Nat.floor b)]
    simp only [Finset.card_empty, Nat.cast_zero]
    linarith

/-! ### Main theorem -/

/-- **Large-sieve second-moment (Cauchy–Schwarz) reduction.** If `N ≥ 1` degree-`≤ k` phases `Ps i`
each correlate with a 1-bounded `f` at relative strength `η'` on intervals `[xs i, xs i + Ls i]` which
all have length comparable to `H` with constant `C₀ ≥ 1` and lie within `C₀ H` of `x₀`, then there is
an index `i` whose row of intersection correlations is large:
`δ N H ≤ ∑_j |∑_{n ∈ I_i ∩ I_j} e(P_i(n) - P_j(n))|` for some `δ = δ(η', C₀) > 0`.

Proof: pick `θ_i` with `e(θ_i) * corr f P_i x_i L_i = ‖corr f P_i x_i L_i‖`, put
`G(n) = ∑_i 1_{I_i}(n) e(θ_i) e(-P_i(n))` on the ambient interval `I = [x₀ - C₀H, x₀ + 2C₀H]`;
`∑_n f(n) G(n) = ∑_i ‖corr_i‖ ≥ η' N H / C₀`; Cauchy–Schwarz and `#I ≤ 4C₀H` give
`∑_{i,j} |S_{ij}| ≥ η'^2 N^2 H/(4C₀^3)`, then average over rows. -/
theorem large_sieve_moment (k : ℕ) (η' C₀ : ℝ) (hη' : 0 < η') (hC₀ : 1 ≤ C₀) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ (N : ℕ) (f : ℕ → ℂ) (x₀ H : ℝ) (xs Ls : Fin N → ℝ) (Ps : Fin N → Polynomial ℝ),
        (∀ n, ‖f n‖ ≤ 1) → 1 ≤ H → 1 ≤ N → (∀ i, 1 ≤ xs i) →
        (∀ i, Ls i ≤ C₀ * H ∧ H ≤ C₀ * Ls i ∧ |xs i - x₀| ≤ C₀ * H) →
        (∀ i, Ps i ∈ Polynomial.degreeLE ℝ (k : WithBot ℕ)) →
        (∀ i, η' * Ls i ≤ ‖Work.BMF.corr f (Ps i) (xs i) (Ls i)‖) →
        ∃ i : Fin N, δ * (N : ℝ) * H ≤
          ∑ j : Fin N, ‖∑ n ∈ (Work.BMF.natIcc (xs i) (xs i + Ls i)) ∩ (Work.BMF.natIcc (xs j) (xs j + Ls j)),
              Work.BMF.eC ((Ps i).eval (n : ℝ) - (Ps j).eval (n : ℝ))‖ := by
  have hC₀pos : 0 < C₀ := lt_of_lt_of_le zero_lt_one hC₀
  refine ⟨η' ^ 2 / (4 * C₀ ^ 3), by positivity, ?_⟩
  intro N f x₀ H xs Ls Ps hf hH hN hxs hgeo hdeg hcorr
  have hHpos : 0 < H := lt_of_lt_of_le zero_lt_one hH
  -- unit phases rotating each correlation onto its modulus
  choose θ hθ using fun i : Fin N =>
    lsm_exists_eC_mul_eq_norm (corr f (Ps i) (xs i) (Ls i))
  -- ambient window and the data entering the abstract Bessel inequality
  let J : Finset ℕ := natIcc (x₀ - C₀ * H) (x₀ + 2 * C₀ * H)
  let Is : Fin N → Finset ℕ := fun i => natIcc (xs i) (xs i + Ls i)
  let g : Fin N → ℕ → ℂ := fun i n => eC (-((Ps i).eval (n : ℝ)))
  let cc : Fin N → ℂ := fun i => eC (θ i)
  have hIs : ∀ i, Is i ⊆ J := by
    intro i
    have hx1 : x₀ - C₀ * H ≤ xs i := by
      have h := (hgeo i).2.2
      rw [abs_le] at h
      linarith [h.1]
    have hx2 : xs i + Ls i ≤ x₀ + 2 * C₀ * H := by
      have h := (hgeo i).2.2
      rw [abs_le] at h
      linarith [h.2, (hgeo i).1]
    exact lsm_natIcc_subset hx1 hx2
  have hcc : ∀ i, ‖cc i‖ = 1 := fun i => lsm_norm_eC (θ i)
  -- the abstract Bessel inequality
  have hbess := large_sieve_bessel N J Is hIs f hf g cc hcc
  -- rewrite its two sides
  have hci : ∀ i, (∑ n ∈ Is i, f n * g i n) = corr f (Ps i) (xs i) (Ls i) := by
    intro i
    simp only [Is, g, corr]
  have hLHSnorm : ‖∑ i, cc i * (∑ n ∈ Is i, f n * g i n)‖
      = ∑ i, ‖corr f (Ps i) (xs i) (Ls i)‖ := by
    have h1 : (∑ i, cc i * (∑ n ∈ Is i, f n * g i n))
        = ∑ i, (((‖corr f (Ps i) (xs i) (Ls i)‖ : ℝ)) : ℂ) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [cc, hci i]
      exact hθ i
    rw [h1, ← Complex.ofReal_sum]
    exact lsm_norm_ofReal_of_nonneg _ (Finset.sum_nonneg fun i _ => norm_nonneg _)
  have hRHS : (∑ i, ∑ j, ‖∑ n ∈ Is i ∩ Is j, g i n * star (g j n)‖)
      = ∑ i, ∑ j, ‖∑ n ∈ Is i ∩ Is j,
            eC ((Ps i).eval (n : ℝ) - (Ps j).eval (n : ℝ))‖ := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [g]
    rw [lsm_eC_conj_sum (Is i ∩ Is j) (Ps i) (Ps j), norm_star]
  -- the pairwise overlap total, abbreviated
  set S : ℝ := ∑ i, ∑ j, ‖∑ n ∈ Is i ∩ Is j,
      eC ((Ps i).eval (n : ℝ) - (Ps j).eval (n : ℝ))‖ with hSdef
  have hbessM : (∑ i, ‖corr f (Ps i) (xs i) (Ls i)‖) ^ 2
      ≤ (J.card : ℝ) * ∑ i, ∑ j, ‖∑ n ∈ Is i ∩ Is j,
            eC ((Ps i).eval (n : ℝ) - (Ps j).eval (n : ℝ))‖ := by
    rw [hLHSnorm, hRHS] at hbess
    exact hbess
  have hbess' : (∑ i, ‖corr f (Ps i) (xs i) (Ls i)‖) ^ 2 ≤ (J.card : ℝ) * S := by
    rw [hSdef]
    exact hbessM
  -- cardinality of the ambient window
  have hbJ : 0 ≤ x₀ + 2 * C₀ * H := by
    have h1 : (1 : ℝ) ≤ xs (⟨0, by omega⟩ : Fin N) := hxs _
    have h2 : |xs (⟨0, by omega⟩ : Fin N) - x₀| ≤ C₀ * H := (hgeo _).2.2
    rw [abs_le] at h2
    have hCH : 0 ≤ C₀ * H := by positivity
    linarith [h2.2, h1, hCH]
  have habJ : x₀ - C₀ * H ≤ x₀ + 2 * C₀ * H := by
    have hCH : 0 ≤ C₀ * H := by positivity
    linarith
  have hJcard : (J.card : ℝ) ≤ 4 * C₀ * H := by
    have h0 := lsm_natIcc_card_le (x₀ - C₀ * H) (x₀ + 2 * C₀ * H) hbJ habJ
    have hsimp : (x₀ + 2 * C₀ * H) - (x₀ - C₀ * H) + 1 = 3 * C₀ * H + 1 := by ring
    rw [hsimp] at h0
    have hJ : (J.card : ℝ) ≤ 3 * C₀ * H + 1 := h0
    have h4 : 1 ≤ C₀ * H := by nlinarith [hC₀, hH]
    linarith
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have key : (∑ i, ‖corr f (Ps i) (xs i) (Ls i)‖) ^ 2 ≤ 4 * C₀ * H * S :=
    le_trans hbess' (mul_le_mul_of_nonneg_right hJcard hSnn)
  -- lower bound for the total mass of the correlations
  have hAc : η' * (N : ℝ) * H / C₀ ≤ ∑ i, ‖corr f (Ps i) (xs i) (Ls i)‖ := by
    have hLs : ∀ i, H / C₀ ≤ Ls i := by
      intro i
      rw [div_le_iff₀ hC₀pos]
      linarith [mul_comm C₀ (Ls i), (hgeo i).2.1]
    have hsumLs : (N : ℝ) * (H / C₀) ≤ ∑ i, Ls i := by
      calc (N : ℝ) * (H / C₀) = ∑ _i : Fin N, H / C₀ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ ∑ i, Ls i := Finset.sum_le_sum fun i _ => hLs i
    calc η' * (N : ℝ) * H / C₀ = η' * ((N : ℝ) * (H / C₀)) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]; ring
      _ ≤ η' * ∑ i, Ls i := mul_le_mul_of_nonneg_left hsumLs hη'.le
      _ = ∑ i, η' * Ls i := by rw [Finset.mul_sum]
      _ ≤ ∑ i, ‖corr f (Ps i) (xs i) (Ls i)‖ := Finset.sum_le_sum fun i _ => hcorr i
  have hA2 : (η' * (N : ℝ) * H / C₀) ^ 2 ≤ 4 * C₀ * H * S :=
    le_trans (pow_le_pow_left₀ (by positivity) hAc 2) key
  have h4C0H : 0 < 4 * C₀ * H := by positivity
  have hmain : (N : ℝ) * (η' ^ 2 / (4 * C₀ ^ 3) * (N : ℝ) * H) ≤ S := by
    have hdiv : (η' * (N : ℝ) * H / C₀) ^ 2 / (4 * C₀ * H) ≤ S := by
      rw [div_le_iff₀ h4C0H, mul_comm S (4 * C₀ * H)]
      exact hA2
    have heq : (η' * (N : ℝ) * H / C₀) ^ 2 / (4 * C₀ * H)
        = (N : ℝ) * (η' ^ 2 / (4 * C₀ ^ 3) * (N : ℝ) * H) := by
      have h1 : C₀ ≠ 0 := ne_of_gt hC₀pos
      have h2 : H ≠ 0 := ne_of_gt hHpos
      have h3 : (4 * C₀ * H) ≠ 0 := by positivity
      have h4 : (4 * C₀ ^ 3) ≠ 0 := by positivity
      field_simp
    rwa [heq] at hdiv
  -- average over rows
  by_contra hcon
  push Not at hcon
  have hne : (Finset.univ : Finset (Fin N)).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, by omega⟩⟩
  have hlt : ∑ i : Fin N, (∑ j : Fin N, ‖∑ n ∈ Is i ∩ Is j,
        eC ((Ps i).eval (n : ℝ) - (Ps j).eval (n : ℝ))‖)
      < ∑ _i : Fin N, η' ^ 2 / (4 * C₀ ^ 3) * (N : ℝ) * H :=
    Finset.sum_lt_sum_of_nonempty hne fun i _ => hcon i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hlt
  rw [hSdef] at hmain
  linarith [hmain, hlt]

end Work.BMF
