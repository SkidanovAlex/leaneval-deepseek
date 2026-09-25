import Mathlib
import Submission.Commons.Analysis.Fourier.max_finset_exponential_sum_l2
import Submission.Commons.Analysis.Fourier.separated_exponentials_near_orthogonal
import Submission.Commons.Analysis.Fourier.exists_dyadic_chain_decomposition
import Submission.Commons.Analysis.Fourier.lintegral_sq_sum_le_of_class_bounds

namespace Commons.Analysis.Fourier

open MeasureTheory Finset
open scoped BigOperators ENNReal

noncomputable section

/-- The additive character `y ↦ e^{I λ y}` has modulus one. -/
private lemma norm_cexp_lin (lam y : ℝ) :
    ‖Complex.exp (Complex.I * (lam : ℂ) * (y : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  have h : (Complex.I * (lam : ℂ) * (y : ℂ)).re = 0 := by
    rw [Complex.mul_re, Complex.mul_re]; simp
  rw [h, Real.exp_zero]

/-- Cauchy–Schwarz: `∑ ‖d k‖ ≤ √K · √(∑ ‖d k‖²)`. -/
private lemma sum_norm_le_sqrt_card_mul_sqrt_sum_sq {K : ℕ} (d : Fin K → ℂ) :
    ∑ k : Fin K, ‖d k‖ ≤ Real.sqrt K * Real.sqrt (∑ k : Fin K, ‖d k‖ ^ 2) := by
  have h1 : (∑ k : Fin K, ‖d k‖ * 1) ^ 2
      ≤ (∑ k : Fin K, ‖d k‖ ^ 2) * (∑ _ : Fin K, (1 : ℝ) ^ 2) :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖d k‖) (fun _ => 1)
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h1
  have h3 : 0 ≤ ∑ k : Fin K, ‖d k‖ := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  calc ∑ k : Fin K, ‖d k‖ ≤ Real.sqrt ((∑ k : Fin K, ‖d k‖ ^ 2) * (K : ℝ)) := by
        rw [← Real.sqrt_sq h3]; exact Real.sqrt_le_sqrt h1
    _ = Real.sqrt K * Real.sqrt (∑ k : Fin K, ‖d k‖ ^ 2) := by
        rw [Real.sqrt_mul (by positivity), mul_comm]

/-- A member of a finite family of nonnegative reals is at most the finite supremum. -/
private lemma le_iSup_finset {α : Type*} (B : Finset α) (u : α → ℝ) (h : ∀ a, 0 ≤ u a)
    {a : α} (ha : a ∈ B) : u a ≤ ⨆ b ∈ B, u b := by
  have hbdd : BddAbove (Set.range (fun b => ⨆ (_ : b ∈ B), u b)) := by
    refine ⟨∑ b ∈ B, u b, ?_⟩
    rintro _ ⟨b, rfl⟩
    change (⨆ (_ : b ∈ B), u b) ≤ ∑ b ∈ B, u b
    by_cases hb : b ∈ B
    · rw [show (⨆ (_ : b ∈ B), u b) = u b from ciSup_pos (f := fun _ => u b) hb]
      exact Finset.single_le_sum (fun i _ => h i) hb
    · rw [show (⨆ (_ : b ∈ B), u b) = sSup (∅ : Set ℝ) from ciSup_neg (f := fun _ => u b) hb,
        Real.sSup_empty]
      exact Finset.sum_nonneg (fun _ _ => h _)
  calc u a = ⨆ (_ : a ∈ B), u a := (ciSup_pos (f := fun _ => u a) ha).symm
    _ ≤ ⨆ b, ⨆ (_ : b ∈ B), u b := le_ciSup hbdd a

/-- For a nonempty finset, the bi-supremum of a nonnegative family equals its `sup'`. -/
private lemma iSup_finset_eq_sup' {ι : Type*} (F : Finset ι) (hF : F.Nonempty) (f : ι → ℝ)
    (hf : ∀ i, 0 ≤ f i) : (⨆ i ∈ F, f i) = F.sup' hF f := by
  have hFne : F.Nonempty := hF
  obtain ⟨i₀, hi₀⟩ := hFne
  haveI : Nonempty ι := ⟨i₀⟩
  have hsupnn : 0 ≤ F.sup' hF f := le_trans (hf i₀) (Finset.le_sup' f hi₀)
  refine le_antisymm ?_ (Finset.sup'_le hF f (fun i hi => le_iSup_finset F f hf hi))
  refine ciSup_le (fun i => ?_)
  by_cases hi : i ∈ F
  · rw [ciSup_pos (f := fun _ => f i) hi]
    exact Finset.le_sup' f hi
  · rw [ciSup_neg (f := fun _ => f i) hi, Real.sSup_empty]
    exact hsupnn

/-- **The entropy chain bound for a finite family.**  Let `lam : Fin K → ℝ` be `1`-separated and
`a : Fin (N+1) → (Fin K → ℂ)` a family of coefficient vectors that is approximately constant along
each net `σ t` at the dyadic accuracy `2·2^{-t}`.  Then the `L²` norm over `[0,1]` of the maximal
exponential sum `sup_i ‖∑ k, a i k · e^{I λ_k y}‖` is bounded by the square of
`√(∑ ‖a (σ 0 0) k‖²) + ∑_{t ≤ S} 2^{-t} √(min (K, M t + 1))`.

This is the entropy/chaining estimate (4.24)–(4.26) in Bourgain's proof of Lemma 4.13: the
telescoping along a dyadic chain of nets decomposes the family into at most `M t` classes at level
`t`, each class is handled by the mean-square bound for a maximal exponential sum
(`Commons.Analysis.Fourier.max_finset_exponential_sum_l2`), the `√K` term is Cauchy–Schwarz, and
the classes are then recombined with the abstract `L²` class bound
(`Commons.Analysis.Fourier.lintegral_sq_sum_le_of_class_bounds`). -/
theorem chain_exp_sum_le_entropy (K : ℕ) (lam : Fin K → ℝ)
    (hsep : ∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N S : ℕ) (a : Fin (N+1) → Fin K → ℂ)
        (σ : ℕ → Fin (N+1) → Fin (N+1)) (M : ℕ → ℕ), 1 ≤ S →
      (∀ i : Fin (N+1), σ 0 i = σ 0 0) →
      (N+1) ≤ M S →
      (∀ t, t ≤ S → (Finset.univ.image (σ t)).card ≤ M t) →
      (∀ t, t ≤ S → ∀ i : Fin (N+1),
        ∑ k : Fin K, ‖a i k - a (σ t i) k‖ ^ 2 ≤ (2 * (1/2:ℝ)^t)^2) →
      ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal
          (⨆ i : Fin (N+1), ‖∑ k : Fin K, a i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖) ^ 2
        ≤ ENNReal.ofReal ((C * (Real.sqrt (∑ k : Fin K, ‖a (σ 0 0) k‖ ^ 2)
            + ∑ t ∈ Finset.range (S+1),
                (1/2:ℝ)^t * Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1)))) ^ 2) := by
  classical
  rcases Nat.eq_zero_or_pos K with hK0 | hKpos
  · subst hK0
    refine ⟨1, one_pos, ?_⟩
    intro N S a σ M hS hconst hNM hcard hnet2
    have hz : (fun y : ℝ => ENNReal.ofReal
        (⨆ i : Fin (N+1), ‖∑ k : Fin 0,
          a i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖) ^ 2)
        = fun _ => (0 : ℝ≥0∞) := by
      funext y
      simp
    rw [hz, lintegral_zero]
    exact bot_le
  obtain ⟨c₀, hc₀pos, hc₀⟩ := max_finset_exponential_sum_l2 K lam hsep
  obtain ⟨c₁, hc₁pos, hc₁⟩ := separated_exponentials_near_orthogonal
  refine ⟨200 * (c₀ + c₁ + 1), by positivity, ?_⟩
  intro N S a σ M hS hconst hNM hcard hnet2
  -- Convert the `ℓ²` hypothesis into a uniform norm bound.
  have hnet : ∀ t, t ≤ S → ∀ i : Fin (N+1), ‖a i - a (σ t i)‖ ≤ 2 * (1/2:ℝ)^t := by
    intro t ht i
    have h2 := hnet2 t ht i
    have hsqrt : Real.sqrt (∑ k : Fin K, ‖a i k - a (σ t i) k‖^2) ≤ 2 * (1/2:ℝ)^t := by
      rw [← Real.sqrt_sq (by positivity : (0:ℝ) ≤ 2 * (1/2:ℝ)^t)]
      exact Real.sqrt_le_sqrt h2
    refine le_trans ?_ hsqrt
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro m
    calc ‖(a i - a (σ t i)) m‖ = ‖a i m - a (σ t i) m‖ := by rw [Pi.sub_apply]
      _ = Real.sqrt (‖a i m - a (σ t i) m‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt (∑ x : Fin K, ‖a i x - a (σ t i) x‖^2) :=
          Real.sqrt_le_sqrt (Finset.single_le_sum
            (fun x (_ : x ∈ Finset.univ) => sq_nonneg (‖a i x - a (σ t i) x‖))
            (Finset.mem_univ m))
  -- The dyadic chain and the finite difference classes.
  let q : ℕ → Fin (N+1) → Fin (N+1) := dyadicChain (N+1) S σ
  let B : ℕ → Finset (Fin K → ℂ) := dyadicDiff (N+1) S a σ
  have hqmem : ∀ k, 1 ≤ k → k ≤ S → ∀ i, q k i ∈ Finset.univ.image (σ (S - k)) := by
    intro k hk _ i
    exact dyadicChain_mem_image (N+1) S σ hk i
  have hqdiff : ∀ k, k < S → ∀ i, a (q k i) - a (q (k+1) i) ∈ B k := by
    intro k _ i
    have hqsucc : q (k+1) i = σ (S - k - 1) (q k i) := dyadicChain_succ_apply (N+1) S σ k i
    rw [hqsucc]
    simp only [B]
    refine Finset.mem_image.mpr ⟨q k i, ?_, rfl⟩
    by_cases hk0 : k = 0
    · subst hk0; simp [dyadicDiff_def]
    · rw [if_neg hk0]
      exact dyadicChain_mem_image (N+1) S σ (by omega) i
  have hqcard : ∀ k, 1 ≤ k → k < S →
      (B k).card ≤ (Finset.univ.image (σ (S - k))).card := by
    intro k hk1 _
    have hk0 : k ≠ 0 := by omega
    simp only [B]
    rw [dyadicDiff_def, if_neg hk0]
    exact Finset.card_image_le
  have hqcard0 : (B 0).card ≤ N+1 := by
    simp only [B]
    rw [dyadicDiff_def, if_pos rfl]
    calc (Finset.univ.image (fun v => a v - a (σ (S - 0 - 1) v))).card
        ≤ (Finset.univ : Finset (Fin (N+1))).card := Finset.card_image_le
      _ = N+1 := by simp
  have hqnorm : ∀ k, k < S → ∀ b ∈ B k, ‖b‖ ≤ 2 * (1/2:ℝ)^(S-k-1) := by
    intro k _ b hb
    simp only [B] at hb
    rw [dyadicDiff_def] at hb
    rw [Finset.mem_image] at hb
    obtain ⟨v, _, hv⟩ := hb
    rw [← hv]
    exact hnet (S - k - 1) (by omega) v
  have hqdecomp : ∀ i, a i = a (q S i) + ∑ k ∈ Finset.range S, (a (q k i) - a (q (k+1) i)) := by
    intro i
    have hsum := Finset.sum_range_sub' (fun k => a (q k i)) S
    rw [hsum]
    rw [show q 0 i = i from dyadicChain_zero_apply (N+1) S σ i]
    exact (add_sub_cancel (a (q S i)) (a i)).symm
  have hqS : ∀ i : Fin (N+1), q S i = σ 0 0 := by
    intro i
    have hmem := hqmem S hS le_rfl i
    rw [Nat.sub_self] at hmem
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hmem
    rw [← hj, hconst j]
  let p : Fin K → ℂ := a (σ 0 0)
  let D : ℝ := Real.sqrt (∑ k : Fin K, ‖p k‖ ^ 2)
  let Φ : ℝ → (Fin K → ℂ) → ℂ :=
    fun y v => ∑ k : Fin K, v k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))
  have hΦadd : ∀ y (u v : Fin K → ℂ), Φ y (u + v) = Φ y u + Φ y v := by
    intro y u v
    simp only [Φ, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  have hΦsum : ∀ y (s : Finset ℕ) (u : ℕ → Fin K → ℂ),
      Φ y (∑ k ∈ s, u k) = ∑ k ∈ s, Φ y (u k) := by
    intro y s u
    simp only [Φ, Finset.sum_apply, Finset.sum_mul]
    exact Finset.sum_comm
  have hΦcont : ∀ b : Fin K → ℂ, Continuous (fun y : ℝ => Φ y b) := by
    intro b
    simp only [Φ]
    exact continuous_finsetSum _ (fun k _ => by fun_prop)
  have hB_ne : ∀ k, k < S → (B k).Nonempty := fun k hk => ⟨_, hqdiff k hk 0⟩
  let cls : ℕ → Finset (Fin K → ℂ) := fun j => if j < S then B j else {p}
  have hcls_ne : ∀ j, (cls j).Nonempty := by
    intro j
    by_cases hj : j < S
    · have h1 : cls j = B j := by simp [cls, hj]
      rw [h1]
      exact hB_ne j hj
    · have h1 : cls j = {p} := by simp [cls, hj]
      rw [h1]
      exact ⟨p, Finset.mem_singleton_self p⟩
  have hclsS : cls S = {p} := by simp [cls]
  have hclsj : ∀ j, j < S → cls j = B j := fun j hj => by simp [cls, hj]
  let Acls : ℕ → ℝ → ℝ := fun j y => (cls j).sup' (hcls_ne j) (fun b => ‖Φ y b‖)
  have hAcls_cont : ∀ j, Continuous (Acls j) := by
    intro j
    exact Continuous.finset_sup'_apply (hcls_ne j) (fun b _ => (hΦcont b).norm)
  have hAcls_nn : ∀ j y, 0 ≤ Acls j y := by
    intro j y
    exact le_trans (norm_nonneg _) (Finset.le_sup' (fun b => ‖Φ y b‖) (hcls_ne j).choose_spec)
  have hAeqS : ∀ y, Acls S y = (⨆ b ∈ cls S, ‖Φ y b‖) := by
    intro y
    simp only [Acls]
    exact (iSup_finset_eq_sup' (cls S) (hcls_ne S) (fun b => ‖Φ y b‖)
      (fun b => norm_nonneg _)).symm
  have hAeqk : ∀ k, k < S → ∀ y, Acls k y = (⨆ b ∈ B k, ‖Φ y b‖) := by
    intro k hk y
    simp only [Acls, hclsj k hk]
    exact (iSup_finset_eq_sup' (B k) (hB_ne k hk) (fun b => ‖Φ y b‖)
      (fun b => norm_nonneg _)).symm
  have hAeqS' : ∀ y, Acls S y = ‖Φ y p‖ := by
    intro y
    simp only [Acls, hclsS]
    rw [Finset.sup'_singleton]
  have hper : ∀ y i, ‖Φ y (a i)‖ ≤ Acls S y + ∑ k ∈ Finset.range S, Acls k y := by
    intro y i
    have hsumk : ∑ k ∈ Finset.range S, Acls k y
        = ∑ k ∈ Finset.range S, (⨆ b ∈ B k, ‖Φ y b‖) :=
      Finset.sum_congr rfl (fun k hk => hAeqk k (Finset.mem_range.mp hk) y)
    rw [hAeqS y, hsumk]
    have hsplit2 : Φ y (a i) = Φ y (a (q S i))
        + ∑ k ∈ Finset.range S, Φ y (a (q k i) - a (q (k+1) i)) := by
      conv_lhs => rw [hqdecomp i]
      rw [hΦadd, hΦsum]
    calc ‖Φ y (a i)‖
        = ‖Φ y (a (q S i)) + ∑ k ∈ Finset.range S, Φ y (a (q k i) - a (q (k+1) i))‖ := by
          rw [hsplit2]
      _ ≤ ‖Φ y (a (q S i))‖
            + ‖∑ k ∈ Finset.range S, Φ y (a (q k i) - a (q (k+1) i))‖ := norm_add_le _ _
      _ ≤ (⨆ b ∈ cls S, ‖Φ y b‖) + ∑ k ∈ Finset.range S, (⨆ b ∈ B k, ‖Φ y b‖) := by
          apply add_le_add
          · refine le_iSup_finset (cls S) (fun b => ‖Φ y b‖) (fun b => norm_nonneg _) ?_
            rw [hqS i, hclsS]
            exact Finset.mem_singleton_self p
          · refine (norm_sum_le _ _).trans ?_
            apply Finset.sum_le_sum; intro k hk
            exact le_iSup_finset (B k) (fun b => ‖Φ y b‖) (fun b => norm_nonneg _)
              (hqdiff k (Finset.mem_range.mp hk) i)
  have hdom : ∀ y, (⨆ i : Fin (N+1), ‖Φ y (a i)‖) ≤ ∑ j ∈ Finset.range (S+1), Acls j y := by
    intro y
    rw [Finset.sum_range_succ]
    exact ciSup_le (fun i => (hper y i).trans (le_of_eq (add_comm _ _)))
  have hsup0 : ∀ y, (0:ℝ) ≤ ⨆ i : Fin (N+1), ‖Φ y (a i)‖ := by
    intro y
    have hbdd : BddAbove (Set.range (fun i : Fin (N+1) => ‖Φ y (a i)‖)) := by
      refine ⟨Acls S y + ∑ k ∈ Finset.range S, Acls k y, ?_⟩
      rintro z ⟨i, rfl⟩
      exact hper y i
    exact le_trans (norm_nonneg _) (le_ciSup hbdd 0)
  -- Per-class mean-square bounds.
  have hcls_bound : ∀ k, k < S →
      ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls k y) ^ 2
        ≤ ENNReal.ofReal ((2 * (1/2:ℝ)^(S-k-1)) ^ 2
            * min (K:ℝ) (c₀ * ((B k).card : ℝ) + 1)) := by
    intro k hk
    set R : ℝ := 2 * (1/2:ℝ)^(S-k-1) with hRdef
    have hRpos : 0 < R := by rw [hRdef]; positivity
    have hmemB : ∀ b ∈ B k, ∑ j : Fin K, ‖b j‖ ^ 2 ≤ R ^ 2 := by
      intro b hb
      simp only [B] at hb
      rw [dyadicDiff_def] at hb
      rw [Finset.mem_image] at hb
      obtain ⟨v, _, hv⟩ := hb
      rw [← hv, hRdef]
      exact hnet2 (S-k-1) (by omega) v
    have hpt : ∀ y, Acls k y ≤ Real.sqrt (K:ℝ) * R := by
      intro y
      have hsup : Acls k y = (B k).sup' (hB_ne k hk) (fun b => ‖Φ y b‖) := by
        simp only [Acls, hclsj k hk]
      rw [hsup]
      refine Finset.sup'_le (hB_ne k hk) (fun b => ‖Φ y b‖) (fun b hb => ?_)
      have hb2 := hmemB b hb
      have hnorm : ‖Φ y b‖ ≤ Real.sqrt (K:ℝ) * Real.sqrt (∑ j : Fin K, ‖b j‖ ^ 2) := by
        have h1 : ‖Φ y b‖ ≤ ∑ j : Fin K, ‖b j‖ := by
          calc ‖Φ y b‖
              = ‖∑ j : Fin K, b j * Complex.exp (Complex.I * (lam j:ℂ) * (y:ℂ))‖ := rfl
            _ ≤ ∑ j : Fin K, ‖b j * Complex.exp (Complex.I * (lam j:ℂ) * (y:ℂ))‖ :=
                norm_sum_le _ _
            _ = ∑ j : Fin K, ‖b j‖ := by
                apply Finset.sum_congr rfl; intro j _
                rw [norm_mul, norm_cexp_lin, mul_one]
        exact h1.trans (sum_norm_le_sqrt_card_mul_sqrt_sum_sq b)
      calc ‖Φ y b‖ ≤ Real.sqrt (K:ℝ) * Real.sqrt (∑ j : Fin K, ‖b j‖ ^ 2) := hnorm
        _ ≤ Real.sqrt (K:ℝ) * Real.sqrt (R^2) :=
            mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hb2) (Real.sqrt_nonneg _)
        _ = Real.sqrt (K:ℝ) * R := by rw [Real.sqrt_sq hRpos.le]
    have hpt_int : ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls k y) ^ 2
        ≤ ENNReal.ofReal (K * R^2) := by
      have hstep : ∀ y : ℝ, ENNReal.ofReal (Acls k y) ^ 2
          ≤ ENNReal.ofReal (Real.sqrt (K:ℝ) * R) ^ 2 := by
        intro y
        rw [← ENNReal.ofReal_pow (hAcls_nn k y) 2,
          ← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ Real.sqrt (K:ℝ) * R) 2]
        exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hAcls_nn k y) (hpt y) 2)
      calc ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls k y) ^ 2
          ≤ ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Real.sqrt (K:ℝ) * R) ^ 2 :=
            lintegral_mono hstep
        _ = ENNReal.ofReal (Real.sqrt (K:ℝ) * R) ^ 2 * volume (Set.Ioc (0:ℝ) 1) := by
            rw [setLIntegral_const]
        _ = ENNReal.ofReal (K * R^2) := by
            rw [Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one]
            rw [← ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ Real.sqrt (K:ℝ) * R) 2]
            congr 1
            rw [mul_pow, Real.sq_sqrt (by positivity : (0:ℝ) ≤ (K:ℝ))]
    have hlev : ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls k y) ^ 2
        ≤ ENNReal.ofReal (c₀ * R^2 * ((B k).card : ℝ)) := by
      have hAeq : Acls k = fun y => (⨆ b ∈ B k, ‖Φ y b‖) := funext (fun y => hAeqk k hk y)
      rw [hAeq]
      exact hc₀ (B k) R hRpos.le hmemB
    refine le_trans (le_min hpt_int hlev) ?_
    rw [← ENNReal.ofReal_min]
    apply ENNReal.ofReal_le_ofReal
    rcases le_total (K:ℝ) (c₀ * ((B k).card : ℝ) + 1) with hle | hle
    · rw [min_eq_left hle]
      calc min (K * R^2) (c₀ * R^2 * ((B k).card : ℝ)) ≤ K * R^2 := min_le_left _ _
        _ = R^2 * K := by ring
    · rw [min_eq_right hle]
      have h2 : c₀ * R^2 * ((B k).card : ℝ) ≤ R^2 * (c₀ * ((B k).card : ℝ) + 1) := by
        nlinarith [hRpos, sq_nonneg R, (Nat.cast_nonneg ((B k).card) : (0:ℝ) ≤ ((B k).card : ℝ)),
          mul_pos hc₀pos hRpos]
      calc min (K * R^2) (c₀ * R^2 * ((B k).card : ℝ)) ≤ c₀ * R^2 * ((B k).card : ℝ) :=
            min_le_right _ _
        _ ≤ R^2 * (c₀ * ((B k).card : ℝ) + 1) := h2
  -- Top class bound.
  have htop_bound : ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls S y) ^ 2
      ≤ ENNReal.ofReal ((Real.sqrt c₁ * D) ^ 2) := by
    have hAeq : Acls S = fun y => ‖Φ y p‖ := funext hAeqS'
    rw [hAeq]
    have hcont : Continuous (fun y : ℝ => (‖Φ y p‖) ^ 2) := (hΦcont p).norm.pow 2
    have hint : Integrable (fun y : ℝ => (‖Φ y p‖) ^ 2)
        (volume.restrict (Set.Ioc (0:ℝ) 1)) :=
      (hcont.continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    have hrepr : (fun y : ℝ => ENNReal.ofReal (‖Φ y p‖) ^ 2)
        = fun y : ℝ => ENNReal.ofReal ((‖Φ y p‖) ^ 2) := by
      funext y
      rw [ENNReal.ofReal_pow (norm_nonneg _) 2]
    rw [hrepr]
    have h2 := ofReal_integral_eq_lintegral_ofReal (μ := volume.restrict (Set.Ioc (0:ℝ) 1))
      (f := fun y : ℝ => (‖Φ y p‖) ^ 2) hint (ae_of_all _ (fun y => sq_nonneg _))
    rw [← h2]
    rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
    apply ENNReal.ofReal_le_ofReal
    have hc1 := hc₁ K lam hsep p
    have hD2 : D ^ 2 = ∑ k : Fin K, ‖p k‖ ^ 2 := by
      rw [show D = Real.sqrt (∑ k : Fin K, ‖p k‖ ^ 2) from rfl,
        Real.sq_sqrt (Finset.sum_nonneg (fun k _ => sq_nonneg _))]
    calc ∫ u in (0:ℝ)..1, (‖Φ u p‖) ^ 2
        ≤ c₁ * ∑ k : Fin K, ‖p k‖ ^ 2 := hc1
      _ = (Real.sqrt c₁ * D) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt hc₁pos.le, hD2]
  -- The weights.
  let X : ℕ → ℝ := fun t => Real.sqrt (min (K:ℝ) ((M t : ℝ) + 1))
  let Tsum : ℝ := ∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * X t
  let w : ℕ → ℝ := fun j => if j < S
      then (2 * (1/2:ℝ)^(S-j-1)) * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1))
      else Real.sqrt c₁ * D
  let uu : ℕ → ℝ := fun j => w j + (1/2:ℝ)^(j+1)
  have hXnn : ∀ t, 0 ≤ X t := fun t => Real.sqrt_nonneg _
  have hwnn : ∀ j, 0 ≤ w j := by
    intro j
    by_cases hj : j < S
    · have h1 : w j = (2 * (1/2:ℝ)^(S-j-1))
          * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1)) := by
        simp only [w]; rw [if_pos hj]
      rw [h1]
      exact mul_nonneg (by positivity) (Real.sqrt_nonneg _)
    · have h1 : w j = Real.sqrt c₁ * D := by simp only [w]; rw [if_neg hj]
      rw [h1]
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have huun : ∀ j, 0 ≤ uu j := fun j =>
    add_nonneg (hwnn j) (by positivity)
  have huu_pos : ∀ j ∈ Finset.range (S+1), 0 < uu j := by
    intro j _
    have h1 : 0 < (1/2:ℝ)^(j+1) := by positivity
    have h2 : 0 ≤ w j := hwnn j
    exact lt_of_lt_of_le h1 (le_add_of_nonneg_left h2)
  have hminKnn : ∀ j, (0:ℝ) ≤ min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1) := fun j =>
    le_min (by positivity) (add_nonneg (mul_nonneg hc₀pos.le (Nat.cast_nonneg _)) zero_le_one)
  have huu_bound : ∀ j ∈ Finset.range (S+1),
      ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (Acls j y) ^ 2
        ≤ ENNReal.ofReal ((uu j) ^ 2) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hlt | heq
    · have h1 : uu j = (2 * (1/2:ℝ)^(S-j-1))
          * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1)) + (1/2:ℝ)^(j+1) := by
        have hwj : w j = (2 * (1/2:ℝ)^(S-j-1))
            * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1)) := by
          dsimp only [w]
          rw [if_pos hlt]
        show w j + (1/2:ℝ)^(j+1) = _
        rw [hwj]
      rw [h1]
      refine (hcls_bound j hlt).trans (ENNReal.ofReal_le_ofReal ?_)
      have hb : 0 ≤ (2 * (1/2:ℝ)^(S-j-1))
          * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1)) :=
        mul_nonneg (by positivity) (Real.sqrt_nonneg _)
      have hsq : ((2 * (1/2:ℝ)^(S-j-1))
          * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1))) ^ 2
          = (2 * (1/2:ℝ)^(S-j-1)) ^ 2 * min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1) := by
        rw [mul_pow, Real.sq_sqrt (hminKnn j)]
      rw [← hsq]
      exact pow_le_pow_left₀ hb (le_add_of_nonneg_right (by positivity)) 2
    · rw [heq]
      have h1 : uu S = Real.sqrt c₁ * D + (1/2:ℝ)^(S+1) := by
        have hwS : w S = Real.sqrt c₁ * D := by
          dsimp only [w]
          rw [if_neg (lt_irrefl S)]
        show w S + (1/2:ℝ)^(S+1) = _
        rw [hwS]
      rw [h1]
      refine htop_bound.trans ?_
      apply ENNReal.ofReal_le_ofReal
      exact pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        (le_add_of_nonneg_right (by positivity)) 2
  obtain hmain := lintegral_sq_sum_le_of_class_bounds (Finset.range (S+1)) Acls uu huu_pos
    (fun j _ y => hAcls_nn j y)
    (fun j _ => ((hAcls_cont j).measurable.ennreal_ofReal.pow_const 2).aemeasurable)
    huu_bound
  have hstep1 : ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal
      (⨆ i : Fin (N+1), ‖∑ k : Fin K, a i k * Complex.exp (Complex.I * (lam k:ℂ) * (y:ℂ))‖) ^ 2
      ≤ ∫⁻ y in Set.Ioc (0:ℝ) 1, ENNReal.ofReal (∑ j ∈ Finset.range (S+1), Acls j y) ^ 2 := by
    apply lintegral_mono
    intro y
    simp only
    have hsum0 : (0:ℝ) ≤ ∑ j ∈ Finset.range (S+1), Acls j y :=
      Finset.sum_nonneg (fun j _ => hAcls_nn j y)
    rw [← ENNReal.ofReal_pow hsum0 2, ← ENNReal.ofReal_pow (hsup0 y) 2]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hsup0 y) (hdom y) 2)
  refine le_trans hstep1 (le_trans hmain ?_)
  apply ENNReal.ofReal_le_ofReal
  -- Numerical bound on `(∑ uu)²`.
  have hDnn : 0 ≤ D := Real.sqrt_nonneg _
  have hTsum_ge_one : 1 ≤ Tsum := by
    have hmem : 0 ∈ Finset.range (S+1) := Finset.mem_range.mpr (by omega)
    have hX0 : 1 ≤ X 0 := by
      have hK1 : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hKpos
      have hM1 : 1 ≤ M 0 := by
        have h1 : 1 ≤ (Finset.univ.image (σ 0)).card :=
          Finset.card_pos.mpr (Finset.image_nonempty.mpr ⟨0, Finset.mem_univ 0⟩)
        exact le_trans h1 (hcard 0 (by omega))
      have hM01 : (1:ℝ) ≤ (M 0 : ℝ) := by exact_mod_cast hM1
      have hmin1 : (1:ℝ) ≤ min (K:ℝ) ((M 0 : ℝ) + 1) := le_min hK1 (by linarith)
      show (1:ℝ) ≤ Real.sqrt (min (K:ℝ) ((M 0 : ℝ) + 1))
      rw [Real.le_sqrt (by norm_num) (by linarith [hmin1])]
      simpa using hmin1
    calc (1:ℝ) ≤ X 0 := hX0
      _ = (1/2:ℝ)^0 * X 0 := by rw [pow_zero, one_mul]
      _ ≤ Tsum := Finset.single_le_sum (f := fun t => (1/2:ℝ)^t * X t)
          (fun t _ => mul_nonneg (by positivity) (hXnn t)) hmem
  have hgeom2 : ∑ j ∈ Finset.range S, (1/2:ℝ)^(j+1) ≤ 1 := by
    rw [show (∑ j ∈ Finset.range S, (1/2:ℝ)^(j+1))
        = (1/2:ℝ) * ∑ j ∈ Finset.range S, (1/2:ℝ)^j from by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro j _
          rw [pow_succ]; ring]
    have hgs : ∑ j ∈ Finset.range S, (1/2:ℝ)^j ≤ 2 := by
      have h1 : ∑ j ∈ Finset.range S, ((1/2:ℝ)^j - (1/2:ℝ)^(j+1)) = 1 - (1/2:ℝ)^S := by
        have h3 := Finset.sum_range_sub (fun j => (1/2:ℝ)^j) S
        rw [pow_zero] at h3
        have h4 : ∑ j ∈ Finset.range S, ((1/2:ℝ)^j - (1/2:ℝ)^(j+1))
            = -∑ j ∈ Finset.range S, ((1/2:ℝ)^(j+1) - (1/2:ℝ)^j) := by
          rw [← Finset.sum_neg_distrib]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        rw [h4, h3]; ring
      have h2 : ∑ j ∈ Finset.range S, ((1/2:ℝ)^j - (1/2:ℝ)^(j+1))
          = (1/2) * ∑ j ∈ Finset.range S, (1/2:ℝ)^j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro j _
        rw [pow_succ]; ring
      rw [h2] at h1
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) S]
    linarith
  have hBcard_le : ∀ j, j < S → (B j).card ≤ M (S-j) := by
    intro j hj
    rcases Nat.eq_zero_or_pos j with hj0 | hjpos
    · subst hj0
      rw [Nat.sub_zero]
      exact le_trans hqcard0 hNM
    · exact le_trans (hqcard j hjpos hj) (hcard (S-j) (by omega))
  have hwbound : ∑ j ∈ Finset.range S, w j ≤ 4 * Real.sqrt (c₀ + 1) * Tsum := by
    have hterm : ∀ j ∈ Finset.range S, w j
        ≤ 2 * (1/2:ℝ)^(S-j-1) * Real.sqrt (c₀+1) * X (S-j) := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hweq : w j = (2 * (1/2:ℝ)^(S-j-1))
          * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1)) := by
        dsimp only [w]; rw [if_pos hj]
      rw [hweq]
      have h1 : Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1))
          ≤ Real.sqrt (c₀+1) * X (S-j) := by
        have h4 : ((B j).card : ℝ) ≤ (M (S-j) : ℝ) := by exact_mod_cast hBcard_le j hj
        have hx : c₀ * ((B j).card : ℝ) + 1 ≤ (c₀+1) * ((M (S-j) : ℝ) + 1) := by
          have hM' : (0:ℝ) ≤ (M (S-j) : ℝ) := Nat.cast_nonneg _
          have h5 := mul_le_mul_of_nonneg_left h4 hc₀pos.le
          nlinarith [h5, hM', hc₀pos]
        have hmin : min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1)
            ≤ (c₀+1) * min (K:ℝ) ((M (S-j) : ℝ) + 1) := by
          rcases le_total ((M (S-j) : ℝ) + 1) (K:ℝ) with hle | hle
          · rw [min_eq_right hle]
            exact le_trans (min_le_right _ _) hx
          · rw [min_eq_left hle]
            calc min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1) ≤ (K:ℝ) := min_le_left _ _
              _ ≤ (c₀+1) * K := by nlinarith [mul_nonneg hc₀pos.le (Nat.cast_nonneg K)]
        calc Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1))
            ≤ Real.sqrt ((c₀+1) * min (K:ℝ) ((M (S-j) : ℝ) + 1)) := Real.sqrt_le_sqrt hmin
          _ = Real.sqrt (c₀+1) * X (S-j) := by
              rw [Real.sqrt_mul (show (0:ℝ) ≤ c₀+1 by linarith)]
      calc (2 * (1/2:ℝ)^(S-j-1)) * Real.sqrt (min (K:ℝ) (c₀ * ((B j).card : ℝ) + 1))
          ≤ (2 * (1/2:ℝ)^(S-j-1)) * (Real.sqrt (c₀+1) * X (S-j)) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = 2 * (1/2:ℝ)^(S-j-1) * Real.sqrt (c₀+1) * X (S-j) := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    have hcongr : (∑ j ∈ Finset.range S,
          2 * (1/2:ℝ)^(S-j-1) * Real.sqrt (c₀+1) * X (S-j))
        = ∑ j ∈ Finset.range S,
            2 * (1/2:ℝ)^(S-1-j) * Real.sqrt (c₀+1) * X (S-1-j+1) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mem_range] at hj
      have h4 : S - j - 1 = S - 1 - j := tsub_right_comm
      have h5 : S - j = S - 1 - j + 1 := by
        rw [← h4, Nat.sub_add_cancel (by omega : 1 ≤ S - j)]
      rw [h4, h5]
    have hrefl : (∑ j ∈ Finset.range S,
          2 * (1/2:ℝ)^(S-j-1) * Real.sqrt (c₀+1) * X (S-j))
        = ∑ i ∈ Finset.range S, 2 * (1/2:ℝ)^i * Real.sqrt (c₀+1) * X (i+1) := by
      rw [hcongr]
      exact Finset.sum_range_reflect
        (fun i => 2 * (1/2:ℝ)^i * Real.sqrt (c₀+1) * X (i+1)) S
    rw [hrefl]
    have himg : (∑ i ∈ Finset.range S, 2 * (1/2:ℝ)^i * Real.sqrt (c₀+1) * X (i+1))
        = 4 * Real.sqrt (c₀+1)
          * ∑ i ∈ Finset.range S, (1/2:ℝ)^(i+1) * X (i+1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _
      rw [pow_succ]; ring
    rw [himg]
    have hsubset : (∑ i ∈ Finset.range S, (1/2:ℝ)^(i+1) * X (i+1))
        ≤ ∑ t ∈ Finset.range (S+1), (1/2:ℝ)^t * X t := by
      rw [Finset.sum_range_succ']
      have h0 : 0 ≤ (1/2:ℝ)^0 * X 0 := mul_nonneg (by norm_num) (hXnn 0)
      have hsum0 : 0 ≤ ∑ i ∈ Finset.range S, (1/2:ℝ)^(i+1) * X (i+1) :=
        Finset.sum_nonneg (fun i _ => mul_nonneg (by positivity) (hXnn (i+1)))
      linarith [h0, hsum0]
    calc 4 * Real.sqrt (c₀+1) * (∑ i ∈ Finset.range S, (1/2:ℝ)^(i+1) * X (i+1))
        ≤ 4 * Real.sqrt (c₀+1) * Tsum := by
          apply mul_le_mul_of_nonneg_left hsubset (by positivity)
      _ = 4 * Real.sqrt (c₀+1) * Tsum := rfl
  have hsum_uu : ∑ j ∈ Finset.range (S+1), uu j ≤ 100 * (c₀ + c₁ + 1) * (D + Tsum) := by
    rw [Finset.sum_range_succ]
    have hfirst : ∑ j ∈ Finset.range S, uu j ≤ 4 * Real.sqrt (c₀+1) * Tsum + 1 := by
      have h2 : ∑ j ∈ Finset.range S, uu j
          ≤ ∑ j ∈ Finset.range S, w j + ∑ j ∈ Finset.range S, (1/2:ℝ)^(j+1) := by
        have h2' : ∑ j ∈ Finset.range S, uu j
            = ∑ j ∈ Finset.range S, (w j + (1/2:ℝ)^(j+1)) := rfl
        rw [h2', Finset.sum_add_distrib]
      linarith [h2, hwbound, hgeom2]
    have hlast : uu S ≤ Real.sqrt c₁ * D + 1 := by
      have h1 : uu S = w S + (1/2:ℝ)^(S+1) := rfl
      have hwS : w S = Real.sqrt c₁ * D := by
        dsimp only [w]; rw [if_neg (lt_irrefl S)]
      rw [h1, hwS]
      have : (1/2:ℝ)^(S+1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      linarith
    have hsqrtc01 : Real.sqrt (c₀+1) ≤ c₀ + 1 := by
      nlinarith [Real.sq_sqrt (by positivity : (0:ℝ) ≤ c₀+1), Real.sqrt_nonneg (c₀+1),
        sq_nonneg (Real.sqrt (c₀+1) - 1)]
    have hsqrtc1 : Real.sqrt c₁ ≤ c₁ + 1 := by
      nlinarith [Real.sq_sqrt hc₁pos.le, Real.sqrt_nonneg c₁, sq_nonneg (Real.sqrt c₁ - 1)]
    have hDsum : 1 ≤ D + Tsum := le_trans hTsum_ge_one (le_add_of_nonneg_left hDnn)
    have hTnn : 0 ≤ Tsum := Finset.sum_nonneg (fun t _ => mul_nonneg (by positivity) (hXnn t))
    have hTle : Tsum ≤ D + Tsum := le_add_of_nonneg_left hDnn
    have hDle : D ≤ D + Tsum := le_add_of_nonneg_right hTnn
    nlinarith [hfirst, hlast, hsqrtc01, hsqrtc1, hDsum, hDle, hTle, hDnn, hTnn,
      Real.sqrt_nonneg (c₀+1), Real.sqrt_nonneg c₁, mul_nonneg hc₀pos.le hTnn,
      mul_nonneg (Real.sqrt_nonneg (c₀+1)) hTnn]
  have hnn : 0 ≤ ∑ j ∈ Finset.range (S+1), uu j := Finset.sum_nonneg (fun j hj => (huu_pos j hj).le)
  calc (∑ j ∈ Finset.range (S+1), uu j) ^ 2
      ≤ (100 * (c₀ + c₁ + 1) * (D + Tsum)) ^ 2 := pow_le_pow_left₀ hnn hsum_uu 2
    _ ≤ (200 * (c₀ + c₁ + 1) * (D + Tsum)) ^ 2 := by
        have hDsum0 : 0 ≤ D + Tsum :=
          le_trans (le_trans zero_le_one hTsum_ge_one) (le_add_of_nonneg_left hDnn)
        have hnn1 : 0 ≤ 100 * (c₀ + c₁ + 1) * (D + Tsum) :=
          mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hDsum0
        have hle2 : 100 * (c₀ + c₁ + 1) * (D + Tsum) ≤ 200 * (c₀ + c₁ + 1) * (D + Tsum) := by
          nlinarith [hc₀pos, hc₁pos, hDsum0]
        exact pow_le_pow_left₀ hnn1 hle2 2

end

end Commons.Analysis.Fourier
