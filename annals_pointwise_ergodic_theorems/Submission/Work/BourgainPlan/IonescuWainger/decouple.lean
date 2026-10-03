import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.decouple_defs

/-!
# Probabilistic decoupling for the hypersystem Khintchine inequality: orthogonality

This file proves the Type II `2r`-superorthogonality of the decoupled family `(hvec a)` at level
`i`: for a `2r`-tuple of indices carrying a nonce, the integral of the product of inner products
vanishes.  This is the input needed to apply the (Hilbert-space-valued) system form at each level.
-/

set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.IonescuWainger

open MeasureTheory Finset Filter
open scoped ENNReal BigOperators

variable {X : Type*} [MeasurableSpace X] {α : Type*} [DecidableEq α]

/-- The pairs of transversal tuples attached to the `j`-th factor of the level-`i+1` expansion: the
first component indexes the fibre of `snocConst τ (s (inr j))` (the unstarred sum) and the second
the fibre of `snocConst τ (s (inl j))` (the starred sum). -/
def Pj (S : Finset α) (k : ℕ) (c : S → Fin k) {r : ℕ} (s : Fin r ⊕ Fin r → S) {i : ℕ}
    (hi' : i + 1 ≤ k) (τ : Fin r → (Fin i → S)) (j : Fin r) :
    Finset ((Fin k → S) × (Fin k → S)) :=
  fib S k c (i + 1) hi' (snocConst (τ j) (s (Sum.inr j))) ×ˢ
    fib S k c (i + 1) hi' (snocConst (τ j) (s (Sum.inl j)))

/-- The monomial attached to a tuple of pairs of transversal tuples. -/
def mono (S : Finset α) {k r : ℕ} (f : Finset α → X → ℂ)
    (P : (j : Fin r) → (Fin k → S) × (Fin k → S)) (x : X) : ℂ :=
  ∏ j : Fin r, f (tupleSet S (P j).1) x * star (f (tupleSet S (P j).2) x)

/-- **The nonce transfers from the index tuple to the set tuple.** -/
theorem nonce_transfer {S : Finset α} {k r : ℕ} {c : S → Fin k} {i : ℕ} (hi : i < k)
    {a : Fin r ⊕ Fin r → S} (ha : HasNonceTuple a)
    {σ : Fin r ⊕ Fin r → (Fin k → S)}
    (hTT : ∀ m, σ m ∈ transversalTuples S k c)
    (hcoord : ∀ m, σ m ⟨i, hi⟩ = a m) :
    HasNonce (fun m : Fin r ⊕ Fin r => tupleSet S (σ m)) := by
  classical
  obtain ⟨j₀, hj₀⟩ := ha
  by_cases hci : c (a j₀) = ⟨i, hi⟩
  · refine ⟨(a j₀).1, j₀, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, by rw [hcoord j₀]⟩
    · intro m hm
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
      have hσmj : σ m j = a j₀ := Subtype.coe_injective hj
      have hcm : c (σ m j) = j := (Finset.mem_filter.mp (hTT m)).2 j
      rw [hσmj, hci] at hcm
      have hj_eq : j = ⟨i, hi⟩ := hcm.symm
      rw [hj_eq, hcoord m] at hσmj
      by_contra hne
      exact absurd hσmj (hj₀ m hne)
  · exact absurd ((Finset.mem_filter.mp (hTT j₀)).2 ⟨i, hi⟩) (by rw [hcoord j₀]; exact hci)

/-- **Inner product of two level-`i+1` vectors.** -/
theorem inner_hvec_hvec' (S : Finset α) (k : ℕ) (c : S → Fin k) {i : ℕ} (hi' : i + 1 ≤ k)
    (f : Finset α → X → ℂ) (a b : S) (x : X) :
    inner ℂ (hvec S k c i hi' f a x) (hvec S k c i hi' f b x)
      = ∑ τ : Fin i → S,
          lvl S k c (i + 1) hi' f (snocConst τ b) x *
            star (lvl S k c (i + 1) hi' f (snocConst τ a) x) := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro τ _
  rw [RCLike.inner_apply]
  rfl

/-- **The level-`i` superorthogonality of the decoupled family.** -/
theorem hvec_orthogonal (S : Finset α) (k r : ℕ) (c : S → Fin k) {i : ℕ} (hi' : i + 1 ≤ k)
    (f : Finset α → X → ℂ) (μ : Measure X)
    (hm : ∀ A, A ⊆ S → A.card ≤ k → AEMeasurable (f A) μ)
    (hint : ∀ A : Fin r ⊕ Fin r → Finset α, (∀ m, A m ⊆ S ∧ (A m).card ≤ k) →
      Integrable (fun x => ∏ j : Fin r, ‖f (A (Sum.inl j)) x‖ * ‖f (A (Sum.inr j)) x‖) μ)
    (horth : ∀ A : Fin r ⊕ Fin r → Finset α, (∀ m, A m ⊆ S ∧ (A m).card ≤ k) → HasNonce A →
      ∫ x, (∏ j : Fin r, star (f (A (Sum.inl j)) x) * f (A (Sum.inr j)) x) ∂μ = 0)
    (s : Fin r ⊕ Fin r → S) (hs : HasNonceTuple s) :
    ∫ x, (∏ j : Fin r, inner ℂ (hvec S k c i hi' f (s (Sum.inl j)) x)
        (hvec S k c i hi' f (s (Sum.inr j)) x)) ∂μ = 0 := by
  classical
  have hik : i < k := by omega
  -- The tuple of transversal tuples and the set-tuple attached to a tuple of pairs
  set σf : ((j : Fin r) → (Fin k → S) × (Fin k → S)) → Fin r ⊕ Fin r → Fin k → S :=
    (fun P => Sum.elim (fun j => (P j).2) (fun j => (P j).1)) with hσf
  set A : ((j : Fin r) → (Fin k → S) × (Fin k → S)) → Fin r ⊕ Fin r → Finset α :=
    (fun P m => tupleSet S (σf P m)) with hA
  have hAad : ∀ P m, A P m ⊆ S ∧ (A P m).card ≤ k := by
    intro P m
    rw [hA]
    cases m <;> exact ⟨tupleSet_subset S _, tupleSet_card_le S _⟩
  -- Integrability of the monomials
  have hmono_int : ∀ (P : (j : Fin r) → (Fin k → S) × (Fin k → S)), Integrable (mono S f P) μ := by
    intro P
    refine Integrable.mono' (hint (A P) (hAad P)) ?_ ?_
    · apply AEMeasurable.aestronglyMeasurable
      show AEMeasurable (fun x : X => ∏ j : Fin r,
        f (tupleSet S (P j).1) x * star (f (tupleSet S (P j).2) x)) μ
      refine Finset.aemeasurable_fun_prod _ (fun j _ => ?_)
      exact (hm _ (tupleSet_subset S _) (tupleSet_card_le S _)).mul
        (continuous_star.measurable.comp_aemeasurable
          (hm _ (tupleSet_subset S _) (tupleSet_card_le S _)))
    · filter_upwards with x
      rw [mono]
      calc ‖∏ j : Fin r, f (tupleSet S (P j).1) x * star (f (tupleSet S (P j).2) x)‖
          ≤ ∏ j : Fin r, ‖f (tupleSet S (P j).1) x * star (f (tupleSet S (P j).2) x)‖ :=
            Finset.norm_prod_le _ _
        _ = ∏ j : Fin r, ‖f (tupleSet S (P j).1) x‖ * ‖f (tupleSet S (P j).2) x‖ := by
            apply Finset.prod_congr rfl
            intro j _
            rw [norm_mul, norm_star]
        _ = ∏ j : Fin r, ‖f (A P (Sum.inl j)) x‖ * ‖f (A P (Sum.inr j)) x‖ := by
            apply Finset.prod_congr rfl
            intro j _
            simp only [hA, hσf, Sum.elim_inl, Sum.elim_inr]
            rw [mul_comm]
  -- Vanishing of the monomial integrals
  have hmono_zero : ∀ (τ : Fin r → (Fin i → S))
      (P : (j : Fin r) → (Fin k → S) × (Fin k → S)),
      P ∈ Fintype.piFinset (Pj S k c s hi' τ) → ∫ x, mono S f P x ∂μ = 0 := by
    intro τ P hP
    have hmem : ∀ j : Fin r, (P j).1 ∈ fib S k c (i + 1) hi' (snocConst (τ j) (s (Sum.inr j))) ∧
        (P j).2 ∈ fib S k c (i + 1) hi' (snocConst (τ j) (s (Sum.inl j))) := by
      intro j
      have h1 := Fintype.mem_piFinset.mp hP j
      rw [Pj, Finset.mem_product] at h1
      exact h1
    have hTT : ∀ m : Fin r ⊕ Fin r, σf P m ∈ transversalTuples S k c := by
      intro m
      cases m with
      | inl j => exact (mem_fib.mp (hmem j).2).1
      | inr j => exact (mem_fib.mp (hmem j).1).1
    have hcoord : ∀ m : Fin r ⊕ Fin r, σf P m ⟨i, hik⟩ = s m := by
      intro m
      cases m with
      | inl j =>
          rw [hσf]
          simp only [Sum.elim_inl]
          rw [coord_fib S k c hik hi' (hmem j).2, snocConst_last]
      | inr j =>
          rw [hσf]
          simp only [Sum.elim_inr]
          rw [coord_fib S k c hik hi' (hmem j).1, snocConst_last]
    have hn : HasNonce (A P) := nonce_transfer hik hs hTT hcoord
    have horth' := horth (A P) (hAad P) hn
    rw [show (∫ x, mono S f P x ∂μ)
        = ∫ x, (∏ j : Fin r, star (f (A P (Sum.inl j)) x) * f (A P (Sum.inr j)) x) ∂μ from by
      congr 1
      funext x
      rw [mono]
      apply Finset.prod_congr rfl
      intro j _
      simp only [hA, hσf, Sum.elim_inl, Sum.elim_inr]
      rw [mul_comm]]
    exact horth'
  -- Pointwise expansion of each factor
  have hfac : ∀ (τ : Fin r → (Fin i → S)) (j : Fin r) (x : X),
      lvl S k c (i + 1) hi' f (snocConst (τ j) (s (Sum.inr j))) x *
          star (lvl S k c (i + 1) hi' f (snocConst (τ j) (s (Sum.inl j))) x)
        = ∑ p ∈ Pj S k c s hi' τ j, f (tupleSet S p.1) x * star (f (tupleSet S p.2) x) := by
    intro τ j x
    rw [lvl_eq_sum_fib, lvl_eq_sum_fib, star_sum, Finset.sum_mul_sum]
    rw [Pj, Finset.sum_product]
  -- The expansion of a product of `r` such factors
  have hexp : ∀ (τ : Fin r → (Fin i → S)) (x : X),
      (∏ j : Fin r, (lvl S k c (i + 1) hi' f (snocConst (τ j) (s (Sum.inr j))) x *
          star (lvl S k c (i + 1) hi' f (snocConst (τ j) (s (Sum.inl j))) x)))
        = ∑ P ∈ Fintype.piFinset (Pj S k c s hi' τ), mono S f P x := by
    intro τ x
    rw [Finset.prod_congr rfl (fun j _ => hfac τ j x), Finset.prod_univ_sum]
    apply Finset.sum_congr rfl
    intro P _
    rw [mono]
  -- Integrability of the level-`i+1` products
  have hG_int : ∀ τ : Fin r → (Fin i → S),
      Integrable (fun x => ∏ j : Fin r,
        (lvl S k c (i + 1) hi' f (snocConst (τ j) (s (Sum.inr j))) x *
          star (lvl S k c (i + 1) hi' f (snocConst (τ j) (s (Sum.inl j))) x))) μ := by
    intro τ
    rw [show (fun x => ∏ j : Fin r,
        (lvl S k c (i + 1) hi' f (snocConst (τ j) (s (Sum.inr j))) x *
          star (lvl S k c (i + 1) hi' f (snocConst (τ j) (s (Sum.inl j))) x)))
        = (fun x => ∑ P ∈ Fintype.piFinset (Pj S k c s hi' τ), mono S f P x) from
      funext (hexp τ)]
    exact integrable_finsetSum _ (fun P _ => hmono_int P)
  calc ∫ x, (∏ j : Fin r, inner ℂ (hvec S k c i hi' f (s (Sum.inl j)) x)
          (hvec S k c i hi' f (s (Sum.inr j)) x)) ∂μ
      = ∫ x, (∑ τ : Fin r → (Fin i → S), ∏ j : Fin r,
          (lvl S k c (i + 1) hi' f (snocConst (τ j) (s (Sum.inr j))) x *
            star (lvl S k c (i + 1) hi' f (snocConst (τ j) (s (Sum.inl j))) x))) ∂μ := by
        congr 1
        funext x
        rw [Finset.prod_congr rfl (fun j _ => inner_hvec_hvec' S k c hi' f _ _ x)]
        rw [Finset.prod_univ_sum]
        simp
    _ = ∑ τ : Fin r → (Fin i → S), ∫ x, (∏ j : Fin r,
          (lvl S k c (i + 1) hi' f (snocConst (τ j) (s (Sum.inr j))) x *
            star (lvl S k c (i + 1) hi' f (snocConst (τ j) (s (Sum.inl j))) x))) ∂μ :=
        integral_finsetSum _ (fun τ _ => hG_int τ)
    _ = ∑ τ : Fin r → (Fin i → S),
          ∑ P ∈ Fintype.piFinset (Pj S k c s hi' τ), ∫ x, mono S f P x ∂μ := by
        apply Finset.sum_congr rfl
        intro τ _
        rw [show (fun x => ∏ j : Fin r,
            (lvl S k c (i + 1) hi' f (snocConst (τ j) (s (Sum.inr j))) x *
              star (lvl S k c (i + 1) hi' f (snocConst (τ j) (s (Sum.inl j))) x)))
            = (fun x => ∑ P ∈ Fintype.piFinset (Pj S k c s hi' τ), mono S f P x) from
          funext (hexp τ)]
        exact integral_finsetSum _ (fun P _ => hmono_int P)
    _ = 0 := by
        apply Finset.sum_eq_zero
        intro τ _
        apply Finset.sum_eq_zero
        intro P hP
        exact hmono_zero τ P hP


/-- Integrability of the total mass of the transversal tuples, to the power `2r`. -/
theorem V_pow_integrable (S : Finset α) (k r : ℕ) (hr : 1 ≤ r) (c : S → Fin k)
    (f : Finset α → X → ℂ) (μ : Measure X)
    (hm : ∀ A, A ⊆ S → A.card ≤ k → AEMeasurable (f A) μ)
    (hint : ∀ A : Fin r ⊕ Fin r → Finset α, (∀ m, A m ⊆ S ∧ (A m).card ≤ k) →
      Integrable (fun x => ∏ j : Fin r, ‖f (A (Sum.inl j)) x‖ * ‖f (A (Sum.inr j)) x‖) μ) :
    Integrable (fun x => Vmass S k c f x ^ (2 * r)) μ := by
  classical
  have hpow : ∀ x : X, Vmass S k c f x ^ (2 * r)
      ≤ ((transversalTuples S k c).card : ℝ) ^ (2 * r - 1) *
        ∑ ρ ∈ transversalTuples S k c, ‖f (tupleSet S ρ) x‖ ^ (2 * r) := by
    intro x
    exact sum_pow_le_card_mul _ (fun ρ => ‖f (tupleSet S ρ) x‖)
      (fun ρ _ => norm_nonneg _) (by omega)
  have hint' : ∀ ρ ∈ transversalTuples S k c,
      Integrable (fun x => ‖f (tupleSet S ρ) x‖ ^ (2 * r)) μ := by
    intro ρ _
    have hA : ∀ m : Fin r ⊕ Fin r, (fun _ : Fin r ⊕ Fin r => tupleSet S ρ) m ⊆ S ∧
        ((fun _ : Fin r ⊕ Fin r => tupleSet S ρ) m).card ≤ k :=
      fun _ => ⟨tupleSet_subset S _, tupleSet_card_le S _⟩
    have h := hint (fun _ => tupleSet S ρ) hA
    rw [show (fun x => ∏ _j : Fin r, ‖f (tupleSet S ρ) x‖ * ‖f (tupleSet S ρ) x‖)
        = (fun x => ‖f (tupleSet S ρ) x‖ ^ (2 * r)) from by
      funext x
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← sq, ← pow_mul]] at h
    exact h
  have hdom : Integrable (fun x : X => ((transversalTuples S k c).card : ℝ) ^ (2 * r - 1) *
      ∑ ρ ∈ transversalTuples S k c, ‖f (tupleSet S ρ) x‖ ^ (2 * r)) μ :=
    (integrable_finsetSum _ (fun ρ hρ => hint' ρ hρ)).const_mul _
  refine hdom.mono' ?_ ?_
  · apply AEMeasurable.aestronglyMeasurable
    show AEMeasurable (fun x : X => (∑ ρ ∈ transversalTuples S k c,
      ‖f (tupleSet S ρ) x‖) ^ (2 * r)) μ
    exact (Finset.aemeasurable_fun_sum (transversalTuples S k c) (fun ρ _ =>
      (hm _ (tupleSet_subset S _) (tupleSet_card_le S _)).norm)).pow_const (2 * r)
  · filter_upwards with x
    have hnn : (0 : ℝ) ≤ Vmass S k c f x ^ (2 * r) :=
      pow_nonneg (Finset.sum_nonneg (fun ρ _ => norm_nonneg _)) _
    rw [Real.norm_of_nonneg hnn]
    exact hpow x

/-- Integrability of the level-`i` square function to the power `r`. -/
theorem sqfR_integrable (S : Finset α) (k r : ℕ) (hr : 1 ≤ r) (c : S → Fin k)
    (f : Finset α → X → ℂ) (μ : Measure X)
    (hm : ∀ A, A ⊆ S → A.card ≤ k → AEMeasurable (f A) μ)
    (hint : ∀ A : Fin r ⊕ Fin r → Finset α, (∀ m, A m ⊆ S ∧ (A m).card ≤ k) →
      Integrable (fun x => ∏ j : Fin r, ‖f (A (Sum.inl j)) x‖ * ‖f (A (Sum.inr j)) x‖) μ)
    {i : ℕ} (hi : i ≤ k) :
    Integrable (fun x => sqfR S k c i hi f x ^ r) μ := by
  have hV := V_pow_integrable S k r hr c f μ hm hint
  have hdom : Integrable (fun x : X => ((Finset.univ : Finset (Fin i → S)).card : ℝ) ^ r *
      Vmass S k c f x ^ (2 * r)) μ := (hV.const_mul _)
  refine hdom.mono' ?_ ?_
  · apply AEMeasurable.aestronglyMeasurable
    show AEMeasurable (fun x : X => (∑ τ : Fin i → S, ‖lvl S k c i hi f τ x‖ ^ 2) ^ r) μ
    exact (Finset.aemeasurable_fun_sum (Finset.univ : Finset (Fin i → S)) (fun τ _ =>
      (lvl_aemeasurable S k c i hi f τ μ hm).norm.pow_const 2)).pow_const r
  · filter_upwards with x
    have h1 := sqfR_le S k c i hi f x
    have hnn : 0 ≤ sqfR S k c i hi f x := Finset.sum_nonneg (fun τ _ => sq_nonneg _)
    rw [Real.norm_of_nonneg (pow_nonneg hnn r)]
    calc sqfR S k c i hi f x ^ r
        ≤ (((Finset.univ : Finset (Fin i → S)).card : ℝ) * Vmass S k c f x ^ 2) ^ r :=
          pow_le_pow_left₀ hnn h1 r
      _ = ((Finset.univ : Finset (Fin i → S)).card : ℝ) ^ r * Vmass S k c f x ^ (2 * r) := by
          rw [mul_pow, ← pow_mul]

/-- **One step of the decoupling iteration**: the system form applied at level `i`. -/
theorem sqf_step (S : Finset α) (k r : ℕ) (hr : 1 ≤ r) (c : S → Fin k) {i : ℕ} (hi : i ≤ k)
    (hi' : i + 1 ≤ k) (f : Finset α → X → ℂ) (μ : Measure X)
    (hm : ∀ A, A ⊆ S → A.card ≤ k → AEMeasurable (f A) μ)
    (hint : ∀ A : Fin r ⊕ Fin r → Finset α, (∀ m, A m ⊆ S ∧ (A m).card ≤ k) →
      Integrable (fun x => ∏ j : Fin r, ‖f (A (Sum.inl j)) x‖ * ‖f (A (Sum.inr j)) x‖) μ)
    (horth : ∀ A : Fin r ⊕ Fin r → Finset α, (∀ m, A m ⊆ S ∧ (A m).card ≤ k) → HasNonce A →
      ∫ x, (∏ j : Fin r, star (f (A (Sum.inl j)) x) * f (A (Sum.inr j)) x) ∂μ = 0)
    {C : ℝ}
    (hsys : ∀ (ν : Measure X) (g : S → X → EuclideanSpace ℂ (Fin i → S)),
      (∀ a, AEMeasurable (g a) ν) →
      (Integrable (fun x => (∑ a, ‖g a x‖ ^ 2) ^ r) ν) →
      (∀ s : Fin r ⊕ Fin r → S, HasNonceTuple s →
        ∫ x, (∏ j : Fin r, inner ℂ (g (s (Sum.inl j)) x) (g (s (Sum.inr j)) x)) ∂ν = 0) →
      ∫⁻ x, ‖∑ a, g a x‖ₑ ^ (2 * (r : ℝ)) ∂ν
        ≤ ENNReal.ofReal (C ^ r) * ∫⁻ x, (∑ a, ‖g a x‖ₑ ^ (2 : ℝ)) ^ r ∂ν) :
    ∫⁻ x, sqf S k c i hi f x ^ r ∂μ
      ≤ ENNReal.ofReal (C ^ r) * ∫⁻ x, sqf S k c (i + 1) hi' f x ^ r ∂μ := by
  have hmeas : ∀ a : S, AEMeasurable (hvec S k c i hi' f a) μ := by
    intro a
    have h1 : AEMeasurable (fun x : X => (fun τ : Fin i → S =>
        lvl S k c (i + 1) hi' f (snocConst τ a) x)) μ :=
      AEMeasurable.of_eval (fun τ =>
        lvl_aemeasurable S k c (i + 1) hi' f (snocConst τ a) μ hm)
    show AEMeasurable (fun x : X => WithLp.toLp 2 (fun τ : Fin i → S =>
        lvl S k c (i + 1) hi' f (snocConst τ a) x)) μ
    exact Measurable.comp_aemeasurable (μ := μ)
      (WithLp.measurable_toLp 2 ((Fin i → S) → ℂ)) h1
  have hint' : Integrable (fun x => (∑ a : S, ‖hvec S k c i hi' f a x‖ ^ 2) ^ r) μ := by
    rw [show (fun x => (∑ a : S, ‖hvec S k c i hi' f a x‖ ^ 2) ^ r)
        = (fun x => sqfR S k c (i + 1) hi' f x ^ r) from by
      funext x
      rw [sqfR, sum_norm_sq_hvec S k c hi' f x]]
    exact sqfR_integrable S k r hr c f μ hm hint hi'
  have horth' : ∀ s : Fin r ⊕ Fin r → S, HasNonceTuple s →
      ∫ x, (∏ j : Fin r, inner ℂ (hvec S k c i hi' f (s (Sum.inl j)) x)
        (hvec S k c i hi' f (s (Sum.inr j)) x)) ∂μ = 0 :=
    fun s hs => hvec_orthogonal S k r c hi' f μ hm hint horth s hs
  have hmain := hsys μ (fun a => hvec S k c i hi' f a) hmeas hint' horth'
  have hL : ∫⁻ x, sqf S k c i hi f x ^ r ∂μ
      = ∫⁻ x, ‖∑ a : S, hvec S k c i hi' f a x‖ₑ ^ (2 * (r : ℝ)) ∂μ := by
    apply lintegral_congr
    intro x
    rw [← enorm_sq_sum_hvec S k c hi hi' f x, ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  have hR : ∫⁻ x, (∑ a : S, ‖hvec S k c i hi' f a x‖ₑ ^ (2 : ℝ)) ^ r ∂μ
      = ∫⁻ x, sqf S k c (i + 1) hi' f x ^ r ∂μ := by
    apply lintegral_congr
    intro x
    rw [sum_enorm_sq_hvec S k c hi' f x]
  rw [← hL, hR] at hmain
  exact hmain

/-- **Chaining the decoupling steps** from level `k - m` up to level `k`. -/
theorem decoupled_bound (S : Finset α) (k r : ℕ) (c : S → Fin k) (f : Finset α → X → ℂ)
    (μ : Measure X) {C : ℝ} (hC : 0 < C)
    (hstep : ∀ (i : ℕ) (hi : i ≤ k) (hi' : i + 1 ≤ k),
      ∫⁻ x, sqf S k c i hi f x ^ r ∂μ ≤
        ENNReal.ofReal (C ^ r) * ∫⁻ x, sqf S k c (i + 1) hi' f x ^ r ∂μ) :
    ∀ m ≤ k, ∫⁻ x, sqf S k c (k - m) (Nat.sub_le k m) f x ^ r ∂μ ≤
      ENNReal.ofReal (C ^ (r * m)) * ∫⁻ x, sqf S k c k le_rfl f x ^ r ∂μ := by
  intro m
  induction m with
  | zero =>
      intro _
      simp
  | succ m ih =>
      intro hm
      have hmk : m ≤ k := by omega
      have hi' : k - (m + 1) + 1 ≤ k := by omega
      have h1 := hstep (k - (m + 1)) (Nat.sub_le _ _) hi'
      have h2 := ih hmk
      have hsub : k - (m + 1) + 1 = k - m := by omega
      calc ∫⁻ x, sqf S k c (k - (m + 1)) (Nat.sub_le k (m + 1)) f x ^ r ∂μ
          ≤ ENNReal.ofReal (C ^ r) *
              ∫⁻ x, sqf S k c (k - (m + 1) + 1) hi' f x ^ r ∂μ := h1
        _ = ENNReal.ofReal (C ^ r) *
              ∫⁻ x, sqf S k c (k - m) (Nat.sub_le k m) f x ^ r ∂μ := by
            refine congrArg (fun t => ENNReal.ofReal (C ^ r) * t) ?_
            apply lintegral_congr
            intro x
            rw [sqf_congr hsub hi' (Nat.sub_le k m)]
        _ ≤ ENNReal.ofReal (C ^ r) * (ENNReal.ofReal (C ^ (r * m)) *
              ∫⁻ x, sqf S k c k le_rfl f x ^ r ∂μ) :=
            mul_le_mul_of_nonneg_left h2 zero_le
        _ = ENNReal.ofReal (C ^ (r * (m + 1))) *
              ∫⁻ x, sqf S k c k le_rfl f x ^ r ∂μ := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg hC.le _), ← pow_add,
              show r + r * m = r * (m + 1) by ring]

/-- The level-`0` partial sum is the sum over all transversal tuples. -/
theorem lvl_zero (S : Finset α) (k : ℕ) (c : S → Fin k) (f : Finset α → X → ℂ) (x : X)
    (h0 : 0 ≤ k) (τ : Fin 0 → S) :
    lvl S k c 0 h0 f τ x = ∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x := by
  rw [lvl]
  congr 1
  ext σ
  simp

/-- The level-`0` square function. -/
theorem sqf_zero (S : Finset α) (k : ℕ) (c : S → Fin k) (f : Finset α → X → ℂ) (x : X)
    (h0 : 0 ≤ k) :
    sqf S k c 0 h0 f x = ‖∑ σ ∈ transversalTuples S k c, f (tupleSet S σ) x‖ₑ ^ (2 : ℝ) := by
  rw [sqf]
  rw [Finset.sum_eq_single (fun j : Fin 0 => j.elim0)
    (fun b _ hb => absurd (Subsingleton.elim b _) hb)
    (fun h => absurd (Finset.mem_univ _) h)]
  rw [lvl_zero S k c f x h0 (fun j : Fin 0 => j.elim0)]

/-- The level-`k` square function is the square function of the transversal tuples. -/
theorem sqf_top (S : Finset α) (k : ℕ) (c : S → Fin k) (f : Finset α → X → ℂ) (x : X) :
    sqf S k c k le_rfl f x
      = ∑ σ ∈ transversalTuples S k c, ‖f (tupleSet S σ) x‖ₑ ^ (2 : ℝ) := by
  have h1 : ∀ σ ∈ transversalTuples S k c,
      ‖lvl S k c k le_rfl f σ x‖ₑ ^ (2 : ℝ) = ‖f (tupleSet S σ) x‖ₑ ^ (2 : ℝ) := by
    intro σ hσ
    congr 1
    rw [lvl, Finset.sum_eq_single σ]
    · intro b hb hne
      simp only [Finset.mem_filter] at hb
      exact absurd (by funext j; simpa using hb.2 j) hne
    · intro h
      exact absurd (Finset.mem_filter.mpr ⟨hσ, fun j => by simp⟩) h
  have h2 : ∀ σ : Fin k → S, σ ∉ transversalTuples S k c → lvl S k c k le_rfl f σ x = 0 := by
    intro σ hσ
    rw [lvl]
    have hempty : (transversalTuples S k c).filter
        (fun b => ∀ j : Fin k, b (Fin.castLE le_rfl j) = σ j) = ∅ := by
      apply Finset.filter_false_of_mem
      intro b hbTT hbs
      exact hσ (by
        have hbs' : σ = b := funext (fun j => by
          have hj := hbs j
          rw [show Fin.castLE le_rfl j = j from Fin.ext rfl] at hj
          exact hj.symm)
        rw [hbs']
        exact hbTT)
    rw [hempty, Finset.sum_empty]
  rw [sqf]
  have : ∑ σ : Fin k → S, ‖lvl S k c k le_rfl f σ x‖ₑ ^ (2 : ℝ)
      = ∑ σ ∈ (Finset.univ : Finset (Fin k → S)).filter
          (fun σ => σ ∈ transversalTuples S k c), ‖f (tupleSet S σ) x‖ₑ ^ (2 : ℝ) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro σ _
    by_cases hσ : σ ∈ transversalTuples S k c
    · rw [if_pos hσ, h1 σ hσ]
    · rw [if_neg hσ, h2 σ hσ]
      simp
  rw [this, show (Finset.univ : Finset (Fin k → S)).filter
      (fun σ => σ ∈ transversalTuples S k c) = transversalTuples S k c from by ext; simp]


/-- **The decoupled bound for a single colouring**: the sum over the transversal tuples of `c` obeys
the Khintchine bound with constant `C₀^{r j}`, where `j` is the number of colour classes. -/
theorem decoupled_colouring (S : Finset α) (j r : ℕ) (hr : 1 ≤ r) (c : S → Fin j)
    (f : Finset α → X → ℂ) (μ : Measure X)
    (hm : ∀ A, A ⊆ S → A.card ≤ j → AEMeasurable (f A) μ)
    (hint : ∀ A : Fin r ⊕ Fin r → Finset α, (∀ m, A m ⊆ S ∧ (A m).card ≤ j) →
      Integrable (fun x => ∏ i : Fin r, ‖f (A (Sum.inl i)) x‖ * ‖f (A (Sum.inr i)) x‖) μ)
    (horth : ∀ A : Fin r ⊕ Fin r → Finset α, (∀ m, A m ⊆ S ∧ (A m).card ≤ j) → HasNonce A →
      ∫ x, (∏ i : Fin r, star (f (A (Sum.inl i)) x) * f (A (Sum.inr i)) x) ∂μ = 0)
    {C₀ : ℝ} (hC₀ : 0 < C₀)
    (hsys : ∀ (i : ℕ) (hi : i ≤ j) (hi' : i + 1 ≤ j)
      (ν : Measure X) (g : S → X → EuclideanSpace ℂ (Fin i → S)),
      (∀ a, AEMeasurable (g a) ν) →
      (Integrable (fun x => (∑ a, ‖g a x‖ ^ 2) ^ r) ν) →
      (∀ s : Fin r ⊕ Fin r → S, HasNonceTuple s →
        ∫ x, (∏ m : Fin r, inner ℂ (g (s (Sum.inl m)) x) (g (s (Sum.inr m)) x)) ∂ν = 0) →
      ∫⁻ x, ‖∑ a, g a x‖ₑ ^ (2 * (r : ℝ)) ∂ν
        ≤ ENNReal.ofReal (C₀ ^ r) * ∫⁻ x, (∑ a, ‖g a x‖ₑ ^ (2 : ℝ)) ^ r ∂ν) :
    ∫⁻ x, ‖∑ σ ∈ transversalTuples S j c, f (tupleSet S σ) x‖ₑ ^ (2 * (r : ℝ)) ∂μ
      ≤ ENNReal.ofReal (C₀ ^ (r * j)) *
        ∫⁻ x, (∑ σ ∈ transversalTuples S j c, ‖f (tupleSet S σ) x‖ₑ ^ (2 : ℝ)) ^ r ∂μ := by
  have hstep : ∀ (i : ℕ) (hi : i ≤ j) (hi' : i + 1 ≤ j),
      ∫⁻ x, sqf S j c i hi f x ^ r ∂μ ≤
        ENNReal.ofReal (C₀ ^ r) * ∫⁻ x, sqf S j c (i + 1) hi' f x ^ r ∂μ :=
    fun i hi hi' => sqf_step S j r hr c hi hi' f μ hm hint horth (hsys i hi hi')
  have hchain := decoupled_bound S j r c f μ hC₀ hstep j le_rfl
  have hL : ∫⁻ x, sqf S j c (j - j) (Nat.sub_le j j) f x ^ r ∂μ
      = ∫⁻ x, ‖∑ σ ∈ transversalTuples S j c, f (tupleSet S σ) x‖ₑ ^ (2 * (r : ℝ)) ∂μ := by
    apply lintegral_congr
    intro x
    rw [sqf_congr (Nat.sub_self j) (Nat.sub_le j j) (Nat.zero_le j),
      sqf_zero S j c f x (Nat.zero_le j), ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  have hR : ∫⁻ x, sqf S j c j le_rfl f x ^ r ∂μ
      = ∫⁻ x, (∑ σ ∈ transversalTuples S j c, ‖f (tupleSet S σ) x‖ₑ ^ (2 : ℝ)) ^ r ∂μ := by
    apply lintegral_congr
    intro x
    rw [sqf_top S j c f x]
  rw [hL, hR] at hchain
  exact hchain

end Work.BourgainPlan.IonescuWainger
