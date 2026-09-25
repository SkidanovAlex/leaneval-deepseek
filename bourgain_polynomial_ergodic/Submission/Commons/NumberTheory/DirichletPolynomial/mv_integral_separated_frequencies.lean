import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.mv_hilbert_separated

open scoped Real BigOperators ComplexConjugate
open MeasureTheory intervalIntegral Complex

noncomputable section

namespace Commons.NumberTheory.DirichletPolynomial

/-- The exponential character `e^{I·(α·t)}`. -/
private def E (α : ℝ) (t : ℝ) : ℂ := Complex.exp (Complex.I * ((α : ℂ) * (t : ℂ)))

private lemma E_add (α β t : ℝ) : E α t * E β t = E (α + β) t := by
  unfold E
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma E_conj (α t : ℝ) : conj (E α t) = E (-α) t := by
  unfold E
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private lemma E_zero (t : ℝ) : E 0 t = 1 := by
  unfold E
  simp

private lemma E_ofReal_mul_I (α t : ℝ) :
    E α t = Complex.exp (((α * t : ℝ) : ℂ) * Complex.I) := by
  unfold E
  congr 1
  push_cast
  ring

private lemma E_norm (α t : ℝ) : ‖E α t‖ = 1 := by
  rw [E_ofReal_mul_I]
  exact Complex.norm_exp_ofReal_mul_I (α * t)

private lemma E_pair (α β t : ℝ) : E α t * conj (E β t) = E (α - β) t := by
  rw [E_conj, E_add]
  congr 1

private lemma E_eq_form (ω t : ℝ) :
    E ω t = Complex.exp (((ω : ℂ) * Complex.I) * (t : ℂ)) := by
  unfold E; congr 1; ring

private lemma E_integral (a b ω : ℝ) (hω : ω ≠ 0) :
    (∫ t in a..b, E ω t) = (E ω b - E ω a) / ((ω : ℂ) * Complex.I) := by
  have hc : (ω : ℂ) * Complex.I ≠ 0 := by
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hω) Complex.I_ne_zero
  rw [show (∫ t in a..b, E ω t) = ∫ t in a..b, Complex.exp (((ω:ℂ)*Complex.I) * (t:ℂ)) from by
        apply intervalIntegral.integral_congr; intro t _; exact E_eq_form ω t]
  rw [integral_exp_mul_complex (a := a) (b := b) (c := (ω:ℂ)*Complex.I) hc]
  rw [← E_eq_form ω b, ← E_eq_form ω a]

private lemma integral_normsq_eq_norm_integral (F : ℝ → ℂ) (A B : ℝ) (hAB : A ≤ B) :
    (∫ t in A..B, ‖F t‖ ^ 2) = ‖∫ t in A..B, F t * conj (F t)‖ := by
  have hcongr : (∫ t in A..B, F t * conj (F t))
      = ∫ t in A..B, ((‖F t‖ ^ 2 : ℝ) : ℂ) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hcongr, intervalIntegral.integral_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (intervalIntegral.integral_nonneg_of_forall hAB (fun u => sq_nonneg _))]

/-- `Σ_{m∈s.erase n} h m = Σ_{m∈s} (if n = m then 0 else h m)` when `h n = 0`. -/
private lemma sum_erase_eq_ite {ι : Type*} [DecidableEq ι] (s : Finset ι) (n : ι)
    (h : ι → ℂ) :
    (∑ m ∈ s.erase n, h m) = ∑ m ∈ s, if n = m then 0 else h m := by
  have h1 : (∑ m ∈ s.filter (fun m => n ≠ m), h m) = ∑ m ∈ s, if n ≠ m then h m else 0 :=
    Finset.sum_filter (s := s) (fun m => n ≠ m) h
  have h2 : (∑ m ∈ s, if n ≠ m then h m else 0) = ∑ m ∈ s, if n = m then 0 else h m := by
    apply Finset.sum_congr rfl
    intro m _
    by_cases hnm : n = m <;> simp [hnm]
  have h3 : s.filter (fun m => n ≠ m) = s.erase n := by
    ext m; simp [Finset.mem_filter, Finset.mem_erase, and_comm, eq_comm]
  rw [← h2, ← h1, h3]

/-- The δ-separated Hilbert form bound, reindexed onto `Fin X`. -/
private lemma hilbert_fin {C_H : ℝ}
    (hCH : ∀ (δ : ℝ), 0 < δ → ∀ (S : Finset ℝ) (z : ℝ → ℂ),
      (∀ a ∈ S, ∀ b ∈ S, a ≠ b → δ ≤ |a - b|) →
        ‖∑ a ∈ S, ∑ b ∈ S, if a = b then 0 else z a * conj (z b) * (((a - b : ℝ)⁻¹ : ℝ) : ℂ)‖ ≤
          C_H / δ * ∑ a ∈ S, ‖z a‖ ^ 2)
    {δ : ℝ} (hδ : 0 < δ) {X : ℕ} (μ : Fin X → ℝ) (z : Fin X → ℂ)
    (hsep : ∀ i j : Fin X, i ≠ j → δ ≤ |μ i - μ j|) :
    ‖∑ n : Fin X, ∑ m : Fin X,
        if n = m then 0 else z n * conj (z m) * (((μ n - μ m : ℝ)⁻¹ : ℝ) : ℂ)‖
      ≤ C_H / δ * ∑ n : Fin X, ‖z n‖ ^ 2 := by
  classical
  have hinj : ∀ n m : Fin X, μ n = μ m → n = m := by
    intro n m hm
    by_contra hne
    have hs := hsep n m hne
    rw [hm] at hs
    simp at hs
    linarith
  let S : Finset ℝ := Finset.univ.image μ
  let z' : ℝ → ℂ := fun a => if h : a ∈ S then z (Classical.choose (Finset.mem_image.mp h)) else 0
  have hz' : ∀ n : Fin X, z' (μ n) = z n := by
    intro n
    have hmem : μ n ∈ S := Finset.mem_image.mpr ⟨n, Finset.mem_univ n, rfl⟩
    have hspec := Classical.choose_spec (Finset.mem_image.mp hmem)
    have hmm : z' (μ n) = z (Classical.choose (Finset.mem_image.mp hmem)) := by
      simp only [z']
      exact dif_pos hmem
    rw [hmm, hinj _ _ hspec.2]
  have hinjOn : Set.InjOn μ (↑(Finset.univ : Finset (Fin X)) : Set (Fin X)) := by
    intro n _ m _ hm; exact hinj n m hm
  have hSsep : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → δ ≤ |a - b| := by
    intro a ha b hb hab
    rcases Finset.mem_image.mp ha with ⟨n, _, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨m, _, rfl⟩
    refine hsep n m ?_
    intro hm; exact hab (by rw [hm])
  have hsum : (∑ a ∈ S, ∑ b ∈ S, if a = b then 0 else z' a * conj (z' b) * (((a - b : ℝ)⁻¹ : ℝ) : ℂ))
      = ∑ n : Fin X, ∑ m : Fin X,
          if n = m then 0 else z n * conj (z m) * (((μ n - μ m : ℝ)⁻¹ : ℝ) : ℂ) := by
    calc
      (∑ a ∈ S, ∑ b ∈ S, if a = b then 0 else z' a * conj (z' b) * (((a - b : ℝ)⁻¹ : ℝ) : ℂ))
          = ∑ n ∈ (Finset.univ : Finset (Fin X)), ∑ b ∈ S,
              (if μ n = b then 0 else z' (μ n) * conj (z' b) * (((μ n - b : ℝ)⁻¹ : ℝ) : ℂ)) := by
            rw [Finset.sum_image hinjOn]
      _ = ∑ n ∈ (Finset.univ : Finset (Fin X)), ∑ m ∈ (Finset.univ : Finset (Fin X)),
              (if μ n = μ m then 0 else z' (μ n) * conj (z' (μ m)) * (((μ n - μ m : ℝ)⁻¹ : ℝ) : ℂ)) := by
            apply Finset.sum_congr rfl; intro n _
            rw [Finset.sum_image hinjOn]
      _ = ∑ n : Fin X, ∑ m : Fin X,
          if n = m then 0 else z n * conj (z m) * (((μ n - μ m : ℝ)⁻¹ : ℝ) : ℂ) := by
            apply Finset.sum_congr rfl; intro n _
            apply Finset.sum_congr rfl; intro m _
            rw [hz' n, hz' m]
            by_cases h : n = m
            · subst h; simp
            · have hμ : μ n ≠ μ m := fun hh => h (hinj n m hh)
              simp [h, hμ]
  have hnorm : (∑ a ∈ S, ‖z' a‖ ^ 2) = ∑ n : Fin X, ‖z n‖ ^ 2 := by
    rw [Finset.sum_image hinjOn]
    apply Finset.sum_congr rfl; intro n _
    rw [hz' n]
  calc
    ‖∑ n : Fin X, ∑ m : Fin X,
        if n = m then 0 else z n * conj (z m) * (((μ n - μ m : ℝ)⁻¹ : ℝ) : ℂ)‖
        = ‖∑ a ∈ S, ∑ b ∈ S, if a = b then 0 else z' a * conj (z' b) * (((a - b : ℝ)⁻¹ : ℝ) : ℂ)‖ := by
          rw [hsum]
    _ ≤ C_H / δ * ∑ a ∈ S, ‖z' a‖ ^ 2 := hCH δ hδ S z' hSsep
    _ = C_H / δ * ∑ n : Fin X, ‖z n‖ ^ 2 := by rw [hnorm]

private lemma continuous_E (α : ℝ) : Continuous (E α) := by
  unfold E; fun_prop

private lemma coeff_eq {X : ℕ} (μ : Fin X → ℝ) (b : Fin X → ℂ) (c : ℝ) (n m : Fin X) :
    b n * conj (b m) * E (μ n - μ m) c = (b n * E (μ n) c) * conj (b m * E (μ m) c) := by
  rw [map_mul, ← E_pair]
  ring

private lemma inv_mul_I (ω : ℝ) :
    (((ω : ℂ) * Complex.I)⁻¹) = Complex.I⁻¹ * (((ω⁻¹ : ℝ) : ℝ) : ℂ) := by
  rw [mul_inv, ← Complex.ofReal_inv]
  ring

private lemma Fmulconj_pointwise {X : ℕ} (μ : Fin X → ℝ) (b : Fin X → ℂ) (t : ℝ) :
    (∑ n : Fin X, b n * E (μ n) t) * conj (∑ m : Fin X, b m * E (μ m) t)
      = ∑ n : Fin X, ∑ m : Fin X, b n * conj (b m) * E (μ n - μ m) t := by
  rw [map_sum]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl; intro n _
  apply Finset.sum_congr rfl; intro m _
  exact (coeff_eq μ b t n m).symm

private lemma pair_term_eq {X : ℕ} (μ : Fin X → ℝ) (b : Fin X → ℂ) (A B : ℝ)
    (n m : Fin X) (hω : μ n - μ m ≠ 0) :
    b n * conj (b m) * (∫ t in A..B, E (μ n - μ m) t)
      = (Complex.I)⁻¹ *
        ((b n * E (μ n) B) * conj (b m * E (μ m) B) * (((μ n - μ m : ℝ)⁻¹ : ℝ) : ℂ)
         - (b n * E (μ n) A) * conj (b m * E (μ m) A) * (((μ n - μ m : ℝ)⁻¹ : ℝ) : ℂ)) := by
  rw [E_integral A B (μ n - μ m) hω, div_eq_mul_inv, inv_mul_I]
  rw [show b n * conj (b m) * ((E (μ n - μ m) B - E (μ n - μ m) A) *
          (Complex.I⁻¹ * (((μ n - μ m : ℝ)⁻¹ : ℝ) : ℂ)))
        = (b n * conj (b m) * E (μ n - μ m) B) * (Complex.I⁻¹ * (((μ n - μ m : ℝ)⁻¹ : ℝ) : ℂ))
          - (b n * conj (b m) * E (μ n - μ m) A) * (Complex.I⁻¹ * (((μ n - μ m : ℝ)⁻¹ : ℝ) : ℂ)) by ring]
  rw [coeff_eq μ b B n m, coeff_eq μ b A n m]
  ring

theorem mv_integral_separated_frequencies :
    ∃ C : ℝ, 0 < C ∧
      ∀ (δ : ℝ), 0 < δ → ∀ (X : ℕ) (μ : Fin X → ℝ) (b : Fin X → ℂ),
        (∀ i j, i ≠ j → δ ≤ |μ i - μ j|) → ∀ (A B : ℝ), A ≤ B →
        (∫ t in A..B, ‖∑ n, b n * Complex.exp (Complex.I * ((μ n : ℂ) * (t : ℂ)))‖ ^ 2)
          ≤ (B - A + C / δ) * (∑ n, ‖b n‖ ^ 2) := by
  obtain ⟨C_H, hCHpos, hCH⟩ := Commons.LinearAlgebra.Matrix.mv_hilbert_separated
  refine ⟨2 * C_H, by positivity, ?_⟩
  intro δ hδ X μ b hsep A B hAB
  classical
  let F : ℝ → ℂ := fun t => ∑ n, b n * E (μ n) t
  let Y : Fin X → ℂ := fun n => b n * E (μ n) B
  let D : Fin X → ℂ := fun n => b n * E (μ n) A
  let Hf : (Fin X → ℂ) → ℂ := fun z =>
    ∑ n : Fin X, ∑ m ∈ (Finset.univ.erase n), z n * conj (z m) * (((μ n - μ m : ℝ)⁻¹ : ℝ) : ℂ)
  have hYnorm : (∑ n : Fin X, ‖Y n‖ ^ 2) = ∑ n : Fin X, ‖b n‖ ^ 2 := by
    apply Finset.sum_congr rfl; intro n _
    dsimp only [Y]; rw [norm_mul, E_norm, mul_one]
  have hDnorm : (∑ n : Fin X, ‖D n‖ ^ 2) = ∑ n : Fin X, ‖b n‖ ^ 2 := by
    apply Finset.sum_congr rfl; intro n _
    dsimp only [D]; rw [norm_mul, E_norm, mul_one]
  -- expansion of the integral
  have hIntegral : (∫ t in A..B, F t * conj (F t))
      = ∑ n : Fin X, ∑ m : Fin X, b n * conj (b m) * (∫ t in A..B, E (μ n - μ m) t) := by
    rw [show (∫ t in A..B, F t * conj (F t))
          = ∫ t in A..B, ∑ n : Fin X, ∑ m : Fin X, b n * conj (b m) * E (μ n - μ m) t from by
        apply intervalIntegral.integral_congr; intro t _
        exact Fmulconj_pointwise μ b t]
    rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
          (f := fun n : Fin X => fun t : ℝ => ∑ m : Fin X, b n * conj (b m) * E (μ n - μ m) t)]
    · apply Finset.sum_congr rfl; intro n _
      rw [intervalIntegral.integral_finsetSum (s := Finset.univ)
            (f := fun m : Fin X => fun t : ℝ => b n * conj (b m) * E (μ n - μ m) t)]
      · apply Finset.sum_congr rfl; intro m _
        rw [intervalIntegral.integral_const_mul]
      · intro m _
        exact ((continuous_E (μ n - μ m)).const_mul (b n * conj (b m))).intervalIntegrable A B
    · intro n _
      exact (continuous_finsetSum Finset.univ
        (fun m _ => (continuous_E (μ n - μ m)).const_mul (b n * conj (b m)))).intervalIntegrable A B
  -- diagonal evaluation
  have hdiagint : ∀ n : Fin X, (∫ t in A..B, E (μ n - μ n) t) = ((B - A : ℝ) : ℂ) := by
    intro n
    have h0 : (μ n - μ n) = 0 := by ring
    rw [h0, show (∫ t in A..B, E 0 t) = ∫ t in A..B, (1 : ℂ) from by
          apply intervalIntegral.integral_congr; intro t _; rw [E_zero]]
    rw [intervalIntegral.integral_const, Complex.real_smul, mul_one]
  have hdiag_val : (∑ n : Fin X, b n * conj (b n) * (∫ t in A..B, E (μ n - μ n) t))
      = (((B - A) * ∑ n : Fin X, ‖b n‖ ^ 2 : ℝ) : ℂ) := by
    have hterm : ∀ n : Fin X, b n * conj (b n) * (∫ t in A..B, E (μ n - μ n) t)
        = (((B - A) * ‖b n‖ ^ 2 : ℝ) : ℂ) := by
      intro n
      rw [hdiagint n, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast; ring
    simp_rw [hterm]
    push_cast
    rw [Finset.mul_sum]
  have hdiag_bound : ‖(∑ n : Fin X, b n * conj (b n) * (∫ t in A..B, E (μ n - μ n) t))‖
      ≤ (B - A) * ∑ n : Fin X, ‖b n‖ ^ 2 := by
    rw [hdiag_val, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    exact mul_nonneg (sub_nonneg.mpr hAB) (Finset.sum_nonneg (fun n _ => sq_nonneg _))
  -- off-diagonal factorization
  have hoff_eq : (∑ n : Fin X, ∑ m ∈ (Finset.univ.erase n),
        b n * conj (b m) * (∫ t in A..B, E (μ n - μ m) t))
      = (Complex.I)⁻¹ * (Hf Y - Hf D) := by
    have hterm : ∀ n : Fin X, ∀ m ∈ Finset.univ.erase n,
        b n * conj (b m) * (∫ t in A..B, E (μ n - μ m) t)
        = (Complex.I)⁻¹ * ((Y n * conj (Y m) * (((μ n - μ m : ℝ)⁻¹ : ℝ) : ℂ))
            - (D n * conj (D m) * (((μ n - μ m : ℝ)⁻¹ : ℝ) : ℂ))) := by
      intro n m hm
      have hne : n ≠ m := (Finset.mem_erase.mp hm).1.symm
      have hω : μ n - μ m ≠ 0 := by
        intro h0
        have hle := hsep n m hne
        rw [h0, abs_zero] at hle
        linarith
      have hp := pair_term_eq μ b A B n m hω
      dsimp only [Y, D]
      exact hp
    rw [show (∑ n : Fin X, ∑ m ∈ (Finset.univ.erase n),
          b n * conj (b m) * (∫ t in A..B, E (μ n - μ m) t))
        = ∑ n : Fin X, ∑ m ∈ (Finset.univ.erase n),
            (Complex.I)⁻¹ * ((Y n * conj (Y m) * (((μ n - μ m : ℝ)⁻¹ : ℝ) : ℂ))
              - (D n * conj (D m) * (((μ n - μ m : ℝ)⁻¹ : ℝ) : ℂ))) from by
        apply Finset.sum_congr rfl; intro n _
        apply Finset.sum_congr rfl; intro m hm
        exact hterm n m hm]
    dsimp only [Hf]
    rw [show (∑ n : Fin X, ∑ m ∈ (Finset.univ.erase n),
            (Complex.I)⁻¹ * ((Y n * conj (Y m) * (((μ n - μ m : ℝ)⁻¹ : ℝ) : ℂ))
              - (D n * conj (D m) * (((μ n - μ m : ℝ)⁻¹ : ℝ) : ℂ))))
        = (Complex.I)⁻¹ * ((∑ n : Fin X, ∑ m ∈ (Finset.univ.erase n),
              Y n * conj (Y m) * (((μ n - μ m : ℝ)⁻¹ : ℝ) : ℂ))
            - (∑ n : Fin X, ∑ m ∈ (Finset.univ.erase n),
              D n * conj (D m) * (((μ n - μ m : ℝ)⁻¹ : ℝ) : ℂ))) from by
        simp_rw [mul_sub]
        simp_rw [Finset.sum_sub_distrib]
        simp_rw [← Finset.mul_sum]]
  have hHY : ‖Hf Y‖ ≤ C_H / δ * ∑ n : Fin X, ‖b n‖ ^ 2 := by
    have hh := hilbert_fin hCH hδ μ Y hsep
    have heq : Hf Y = ∑ n : Fin X, ∑ m : Fin X,
        if n = m then 0 else Y n * conj (Y m) * (((μ n - μ m : ℝ)⁻¹ : ℝ) : ℂ) := by
      dsimp only [Hf]
      apply Finset.sum_congr rfl; intro n _
      rw [sum_erase_eq_ite]
    rw [heq, ← hYnorm]
    exact hh
  have hHD : ‖Hf D‖ ≤ C_H / δ * ∑ n : Fin X, ‖b n‖ ^ 2 := by
    have hh := hilbert_fin hCH hδ μ D hsep
    have heq : Hf D = ∑ n : Fin X, ∑ m : Fin X,
        if n = m then 0 else D n * conj (D m) * (((μ n - μ m : ℝ)⁻¹ : ℝ) : ℂ) := by
      dsimp only [Hf]
      apply Finset.sum_congr rfl; intro n _
      rw [sum_erase_eq_ite]
    rw [heq, ← hDnorm]
    exact hh
  have hoff_bound : ‖(∑ n : Fin X, ∑ m ∈ (Finset.univ.erase n),
        b n * conj (b m) * (∫ t in A..B, E (μ n - μ m) t))‖
      ≤ 2 * C_H / δ * ∑ n : Fin X, ‖b n‖ ^ 2 := by
    rw [hoff_eq, norm_mul, show ‖(Complex.I)⁻¹‖ = 1 by rw [Complex.inv_I, norm_neg, Complex.norm_I], one_mul]
    calc ‖Hf Y - Hf D‖ ≤ ‖Hf Y‖ + ‖Hf D‖ := norm_sub_le _ _
      _ ≤ C_H / δ * (∑ n : Fin X, ‖b n‖ ^ 2) + C_H / δ * (∑ n : Fin X, ‖b n‖ ^ 2) :=
            add_le_add hHY hHD
      _ = 2 * C_H / δ * ∑ n : Fin X, ‖b n‖ ^ 2 := by ring
  -- split integral into diagonal + off-diagonal
  have hsplit : (∑ n : Fin X, ∑ m : Fin X, b n * conj (b m) * (∫ t in A..B, E (μ n - μ m) t))
      = (∑ n : Fin X, b n * conj (b n) * (∫ t in A..B, E (μ n - μ n) t))
        + (∑ n : Fin X, ∑ m ∈ (Finset.univ.erase n),
            b n * conj (b m) * (∫ t in A..B, E (μ n - μ m) t)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro n _
    rw [← Finset.sum_erase_add (Finset.univ)
          (fun m => b n * conj (b m) * (∫ t in A..B, E (μ n - μ m) t)) (Finset.mem_univ n),
        add_comm]
  calc (∫ t in A..B, ‖∑ n, b n * Complex.exp (Complex.I * ((μ n : ℂ) * (t : ℂ)))‖ ^ 2)
      = ‖∫ t in A..B, F t * conj (F t)‖ :=
        integral_normsq_eq_norm_integral F A B hAB
    _ = ‖(∑ n : Fin X, b n * conj (b n) * (∫ t in A..B, E (μ n - μ n) t))
            + (∑ n : Fin X, ∑ m ∈ (Finset.univ.erase n),
                b n * conj (b m) * (∫ t in A..B, E (μ n - μ m) t))‖ := by
          rw [hIntegral, hsplit]
    _ ≤ ‖(∑ n : Fin X, b n * conj (b n) * (∫ t in A..B, E (μ n - μ n) t))‖
          + ‖(∑ n : Fin X, ∑ m ∈ (Finset.univ.erase n),
                b n * conj (b m) * (∫ t in A..B, E (μ n - μ m) t))‖ := norm_add_le _ _
    _ ≤ (B - A) * ∑ n : Fin X, ‖b n‖ ^ 2 + 2 * C_H / δ * ∑ n : Fin X, ‖b n‖ ^ 2 :=
          add_le_add hdiag_bound hoff_bound
    _ = (B - A + 2 * C_H / δ) * ∑ n : Fin X, ‖b n‖ ^ 2 := by ring

end Commons.NumberTheory.DirichletPolynomial
