import Mathlib
import Submission.Work.Peluse.Ulower.dualFn_norm_le_one
import Submission.Work.Peluse.Ulower.lemma74_cubeTerm_iterDelta
import Submission.Work.Peluse.Ulower.dualFn_iterDelta_pieces
import Submission.Work.Peluse.Ulower.conclTerm_uniform_bound
import Submission.Work.Peluse.Ulower.StepLe.sharpMassDDI_all
import Submission.Work.Peluse.Ulower.StepLe.sharpMassDDI_one_v2

namespace Work.Peluse.Ulower.ss74

open scoped BigOperators

noncomputable section

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Reindexing the slice average `∑_{y ∈ [1,M]}` as a sum over `Fin M` -/

/-- `∑_{z : Fin M} f (z+1) = ∑_{y ∈ [1,M]} f y`. -/
lemma sum_fin_succ {β : Type*} [AddCommMonoid β] (M : ℕ) (f : ℕ → β) :
    (∑ z : Fin M, f (z.1 + 1)) = ∑ y ∈ Finset.Icc 1 M, f y := by
  induction M with
  | zero => simp
  | succ n ih =>
      rw [Fin.sum_univ_eq_sum_range (fun i => f (i + 1)) (n + 1), Finset.sum_range_succ]
      rw [Fin.sum_univ_eq_sum_range (fun i => f (i + 1)) n] at ih
      rw [ih, ← Finset.sum_Icc_succ_top (a := 1) (b := n) (by omega) f]

/-! ## The slices as a `1`-bounded, translate-supported family -/

/-- The slice `sl P f₀ f₁ y` is `1`-bounded. -/
lemma sl_norm_le_one {P : Polynomial ℤ} {f₀ f₁ : ℤ → ℂ}
    (h0 : ∀ x : ℤ, ‖f₀ x‖ ≤ 1) (h1 : ∀ x : ℤ, ‖f₁ x‖ ≤ 1) (y : ℕ) (x : ℤ) :
    ‖Work.Peluse.Ulower.sl P f₀ f₁ y x‖ ≤ 1 := by
  rw [Work.Peluse.Ulower.sl, norm_mul]
  have ha := h0 (x - P.eval (y : ℤ))
  have hb := h1 (x + (y : ℤ) - P.eval (y : ℤ))
  have hna : (0 : ℝ) ≤ ‖f₀ (x - P.eval (y : ℤ))‖ := norm_nonneg _
  have hnb : (0 : ℝ) ≤ ‖f₁ (x + (y : ℤ) - P.eval (y : ℤ))‖ := norm_nonneg _
  nlinarith

/-- A translate of the slice `sl P f₀ f₁ y` (by `P y`) is supported in `symIcc L`. -/
lemma sl_translate_support {P : Polynomial ℤ} {f₀ f₁ : ℤ → ℂ} {L : ℕ}
    (hs0 : ∀ x : ℤ, x ∉ Work.Peluse.symIcc L → f₀ x = 0) (y : ℕ) :
    ∀ x : ℤ, x ∉ Work.Peluse.symIcc L →
      Work.Peluse.Ulower.sl P f₀ f₁ y (x + P.eval (y : ℤ)) = 0 := by
  intro x hx
  rw [Work.Peluse.Ulower.sl]
  have h : x + P.eval (y : ℤ) - P.eval (y : ℤ) = x := by ring
  rw [h, hs0 x hx, zero_mul]

/-- The mean of the slice family is Peluse's dual function. -/
lemma mean_sl_eq_dualFn {M : ℕ} (hM : 1 ≤ M) (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ) (x : ℤ) :
    ((M : ℂ))⁻¹ * (∑ z : Fin M, Work.Peluse.Ulower.sl P f₀ f₁ (z.1 + 1) x)
      = Work.Peluse.dualFn M P f₀ f₁ x := by
  rw [Work.Peluse.dualFn, sum_fin_succ M (fun y => Work.Peluse.Ulower.sl P f₀ f₁ y x)]
  rfl

/-- The mean of the cube terms of the slice family is `dualFn` of the iterated differences. -/
lemma mean_cubeTerm_eq_dualFn {σ M : ℕ} (hM : 1 ≤ M) (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ)
    (k : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ)) :
    (fun x : ℤ => ((M : ℂ))⁻¹ *
        ∑ z : Fin M, Work.Peluse.cubeTerm k.2.1 k.2.2 (Work.Peluse.Ulower.sl P f₀ f₁ (z.1 + 1)) x)
      = Work.Peluse.dualFn M P
          (Work.Peluse.Ulower.iterDelta' σ (fun i => (k.2.1 i, k.2.2 i)) f₀)
          (Work.Peluse.Ulower.iterDelta' σ (fun i => (k.2.1 i, k.2.2 i)) f₁) := by
  funext x
  rw [Work.Peluse.Ulower.dualFn_iterDelta_pieces σ M P f₀ f₁
        (fun i => (k.2.1 i, k.2.2 i)) x]
  congr 1
  rw [sum_fin_succ M (fun y => Work.Peluse.cubeTerm k.2.1 k.2.2
        (Work.Peluse.Ulower.sl P f₀ f₁ y) x)]
  refine Finset.sum_congr rfl fun y _ => ?_
  exact (Work.Peluse.Ulower.lemma74_cubeTerm_iterDelta (fun i => (k.2.1 i, k.2.2 i))
    (Work.Peluse.Ulower.sl P f₀ f₁ y) x).symm

/-- Membership in `[1,D]` gives the `D`-bound of the absolute value. -/
lemma abs_le_of_mem_Icc {D : ℕ} {x : ℤ} (h : x ∈ Finset.Icc (1 : ℤ) (D : ℤ)) :
    |x| ≤ (D : ℤ) := by
  rw [Finset.mem_Icc] at h
  obtain ⟨h1, h2⟩ := h
  rw [abs_of_nonneg (by omega : (0 : ℤ) ≤ x)]
  exact h2

/-- The `□`-completeness condition puts both shift tuples in `H₁`. -/
lemma fst_mem_of_mem_ThetaSet {σ D : ℕ}
    {H : Finset ((Fin σ → ℤ) × (Fin σ → ℤ))}
    {k : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ)}
    (hk : k ∈ Work.Peluse.Ulower.ThetaSet σ D H) :
    (k.1, k.2.1) ∈ H ∧ (k.1, k.2.2) ∈ H := by
  rw [Work.Peluse.Ulower.ThetaSet, Finset.mem_filter] at hk
  obtain ⟨-, hcond⟩ := hk
  constructor
  · have h := hcond (fun _ : Fin σ => true)
    simpa using h
  · have h := hcond (fun _ : Fin σ => false)
    simpa using h

/-- Casting the cube-difference phase of the conclusion from `ℝ` to `ℂ`. -/
lemma phase_cast {σ : ℕ} (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ)
    (a b c : Fin σ → ℤ) :
    (∑ ω, (-1 : ℂ) ^ Work.Peluse.weight ω *
        (β a (fun i => if ω i = true then b i else c i) : ℂ))
      = (((∑ ω, (-1 : ℝ) ^ Work.Peluse.weight ω *
            β a (fun i => if ω i = true then b i else c i)) : ℝ) : ℂ) := by
  rw [Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg, Complex.ofReal_one]

/-- The conclusion term: the correlation of the `σ`-fold cube term of the slices of the dual
function at the triple `k`. -/
def dCorr (σ L M : ℕ) (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ)
    (β : (Fin σ → ℤ) → (Fin σ → ℤ) → ℝ)
    (k : (Fin σ → ℤ) × (Fin σ → ℤ) × (Fin σ → ℤ)) : ℂ :=
  ((L : ℂ))⁻¹ * ∑' x : ℤ,
    Work.Peluse.dualFn M P (Work.Peluse.Ulower.iterDelta' σ (fun i => (k.2.1 i, k.2.2 i)) f₀)
      (Work.Peluse.Ulower.iterDelta' σ (fun i => (k.2.1 i, k.2.2 i)) f₁) x *
    Complex.exp (2 * Real.pi * Complex.I *
      ((∑ ω, (-1) ^ Work.Peluse.weight ω * β k.1 (fun i => if ω i = true then k.2.1 i else k.2.2 i)) : ℂ) *
      (x : ℂ))

/-- Markov/filter extraction: from a lower bound on the mean square of `X` over `Θ` (with `X`
bounded by `S`), one extracts a sub-family of density at least `cc * TT` on which `X ≥ cc * TT`. -/
lemma filter_card_ge {α : Type*} [DecidableEq α] (Θ : Finset α) (X : α → ℝ)
    {B S cc TT : ℝ} (hS1 : 1 ≤ S) (hccTT0 : 0 ≤ cc * TT) (hccTT1 : cc * TT ≤ 1)
    (hkey : cc * TT * (1 + S ^ 2) ≤ B)
    (hsum : B * (Θ.card : ℝ) ≤ ∑ k ∈ Θ, (X k) ^ 2)
    (huni : ∀ k ∈ Θ, X k ≤ S) (hX0 : ∀ k, 0 ≤ X k) :
    cc * TT * (Θ.card : ℝ) ≤ ((Θ.filter (fun k => cc * TT ≤ X k)).card : ℝ) := by
  classical
  set H₂ : Finset α := Θ.filter (fun k => cc * TT ≤ X k) with hH2
  have hsub : H₂ ⊆ Θ := Finset.filter_subset _ _
  have hsplit : (∑ k ∈ Θ, (X k) ^ 2) = (∑ k ∈ H₂, (X k) ^ 2) + ∑ k ∈ Θ \ H₂, (X k) ^ 2 := by
    rw [← Finset.sum_sdiff hsub, add_comm]
  have hH2le : (∑ k ∈ H₂, (X k) ^ 2) ≤ (H₂.card : ℝ) * S ^ 2 := by
    calc (∑ k ∈ H₂, (X k) ^ 2) ≤ ∑ _k ∈ H₂, S ^ 2 := by
          refine Finset.sum_le_sum fun k hk => ?_
          exact pow_le_pow_left₀ (hX0 k) (huni k (hsub hk)) 2
      _ = (H₂.card : ℝ) * S ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hDle : (∑ k ∈ Θ \ H₂, (X k) ^ 2) ≤ ((Θ \ H₂).card : ℝ) * (cc * TT) ^ 2 := by
    calc (∑ k ∈ Θ \ H₂, (X k) ^ 2) ≤ ∑ _k ∈ Θ \ H₂, (cc * TT) ^ 2 := by
          refine Finset.sum_le_sum fun k hk => ?_
          obtain ⟨hkΘ, hkH⟩ := Finset.mem_sdiff.mp hk
          have hlt : X k < cc * TT := by
            by_contra hcon
            exact hkH (Finset.mem_filter.mpr ⟨hkΘ, not_lt.mp hcon⟩)
          nlinarith [hccTT0, hX0 k, hlt]
      _ = ((Θ \ H₂).card : ℝ) * (cc * TT) ^ 2 := by rw [Finset.sum_const, nsmul_eq_mul]
  have hcard_le : ((Θ \ H₂).card : ℝ) ≤ (Θ.card : ℝ) := by
    exact_mod_cast Finset.card_le_card (Finset.sdiff_subset : Θ \ H₂ ⊆ Θ)
  have hBa : (cc * TT) ^ 2 + (cc * TT) * S ^ 2 ≤ B := by
    nlinarith [hccTT1, hccTT0, hkey, sq_nonneg (cc * TT)]
  have h2 : B * (Θ.card : ℝ) ≤ (H₂.card : ℝ) * S ^ 2 + (Θ.card : ℝ) * (cc * TT) ^ 2 := by
    rw [hsplit] at hsum
    have h3 := add_le_add hH2le hDle
    nlinarith [hsum, h3, hcard_le, sq_nonneg (cc * TT), hccTT0]
  have h4 : (Θ.card : ℝ) * (cc * TT) * S ^ 2 ≤ (H₂.card : ℝ) * S ^ 2 := by
    nlinarith [h2, hBa, hccTT0, sq_nonneg S]
  calc cc * TT * (Θ.card : ℝ) = (Θ.card : ℝ) * (cc * TT) := by ring
    _ ≤ (H₂.card : ℝ) := le_of_mul_le_mul_right h4 (by positivity : (0:ℝ) < S ^ 2)

end

end Work.Peluse.Ulower.ss74
