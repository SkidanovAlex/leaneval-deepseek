import Mathlib
import Submission.Work.LT.lr_Mpar_defs
import Submission.Work.LT.lr_Mpar_form_decomp
import Submission.Work.LT.lr_Mpar_disp_decomp
import Submission.Work.LT.lr_class_quad_decomp
import Submission.Work.LT.lr_classOpB_basic
import Submission.Work.LT.lr_classOpA_basic

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.LT

open Classical
open scoped BigOperators

/-! ## Auxiliary lemmas (mine). -/

/-- Variance identity: `∑ (f - q)² = ∑ f² - 2q ∑ f + |ι| q²`. -/
private theorem sum_sq_sub {ι : Type*} [Fintype ι] (f : ι → ℝ) (q : ℝ) :
    ∑ i, (f i - q) ^ 2
      = (∑ i, f i ^ 2) - 2 * q * (∑ i, f i) + (Fintype.card ι : ℝ) * q ^ 2 := by
  have h1 : ∀ i, (f i - q) ^ 2 = f i ^ 2 - 2 * q * f i + q ^ 2 := fun i => by ring
  calc ∑ i, (f i - q) ^ 2
      = ∑ i, (f i ^ 2 - 2 * q * f i + q ^ 2) := Finset.sum_congr rfl (fun i _ => h1 i)
    _ = (∑ i, f i ^ 2) - (∑ i, 2 * q * f i) + ∑ i, q ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    _ = (∑ i, f i ^ 2) - 2 * q * (∑ i, f i) + (Fintype.card ι : ℝ) * q ^ 2 := by
          rw [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- **The label-class spectral bound.** Let `s ≥ 0` be `0/1`-valued on `Fin 2 × G`, `op` a
linear, mass-preserving operator fixing the constants, and assume `op` contracts mean-zero
vectors by `μ`.  If `⟨s, op s⟩ ≥ c ‖s‖₁` and `s ≠ 0` then `(c - μ) |G| ≤ ‖s‖₁`. -/
private theorem class_bound {G : Type} [Group G] [Fintype G] (μ c : ℝ) (hμ : 0 ≤ μ)
    (s : Fin 2 × G → ℝ) (op : (Fin 2 × G → ℝ) → (Fin 2 × G → ℝ)) (Q : ℝ)
    (h01 : ∀ p, s p = 0 ∨ s p = 1)
    (hadd : ∀ x y, op (x + y) = op x + op y)
    (hsmul : ∀ (a : ℝ) x, op (a • x) = a • op x)
    (hone : op (fun _ => (1 : ℝ)) = fun _ => (1 : ℝ))
    (hsum : ∀ x, ∑ p, op x p = ∑ p, x p)
    (hgap : ∀ h : Fin 2 × G → ℝ, (∑ p, h p) = 0 →
      ∑ p, h p * op h p ≤ μ * ∑ p, h p ^ 2)
    (hQ : Q = ∑ p, s p * op s p)
    (hcle : c * (∑ p, s p) ≤ Q)
    (hpos : 0 < ∑ p, s p) :
    (c - μ) * (Fintype.card G : ℝ) ≤ ∑ p, s p := by
  have hcard : (Fintype.card (Fin 2 × G) : ℝ) = 2 * (Fintype.card G : ℝ) := by
    rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat]
  have hGpos : (0 : ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast Fintype.card_pos
  have hGnn : (0 : ℝ) ≤ (Fintype.card G : ℝ) := le_of_lt hGpos
  set q : ℝ := (∑ p, s p) / (2 * (Fintype.card G : ℝ)) with hq_def
  have hqnn : 0 ≤ q := by rw [hq_def]; positivity
  have hqmul : q * (Fintype.card (Fin 2 × G) : ℝ) = ∑ p, s p := by
    have hne : (2 : ℝ) * (Fintype.card G : ℝ) ≠ 0 := by positivity
    rw [hcard, hq_def]
    exact div_mul_cancel₀ _ hne
  have hquad := lr_class_quad_decomp op hadd hsmul hone hsum s q hqmul
  have hhsum : ∑ p, (s p - q) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [mul_comm]
    linarith [hqmul]
  have hbnd : ∑ p, (s p - q) * op (fun p => s p - q) p ≤ μ * ∑ p, (s p - q) ^ 2 :=
    hgap (fun p => s p - q) hhsum
  have hsq : ∑ p, (s p - q) ^ 2 = (∑ p, s p) * (1 - q) := by
    have h01sq : ∀ p, s p ^ 2 = s p := by
      intro p; rcases h01 p with h | h <;> rw [h] <;> norm_num
    rw [sum_sq_sub]
    rw [Finset.sum_congr rfl (fun p _ => h01sq p)]
    nlinarith [hqmul, hcard]
  have hQle : Q ≤ (∑ p, s p) * (q + μ * (1 - q)) := by
    rw [hQ, hquad]
    rw [hsq] at hbnd
    nlinarith [hbnd]
  have hc_le : c ≤ q + μ * (1 - q) := by
    have h1 : (∑ p, s p) * c ≤ (∑ p, s p) * (q + μ * (1 - q)) := by
      rw [mul_comm (∑ p, s p) c]
      exact hcle.trans hQle
    exact le_of_mul_le_mul_left h1 hpos
  have hqge : c - μ ≤ q := by nlinarith [hc_le, hμ, hqnn]
  have hLx : ∑ p, s p = 2 * (Fintype.card G : ℝ) * q := by
    rw [← hqmul, hcard]; ring
  calc (c - μ) * (Fintype.card G : ℝ) ≤ q * (Fintype.card G : ℝ) :=
        mul_le_mul_of_nonneg_right hqge hGnn
    _ ≤ 2 * (Fintype.card G : ℝ) * q := by nlinarith [mul_nonneg hqnn hGnn]
    _ = ∑ p, s p := hLx.symm

/-! ## The main theorem. -/

/-- **The label-class case for the parallel operator.** `MparForm = ⟨1_R, M‖ 1_R⟩` splits as a sum
over the `2Δ` label classes: for a fixed A-label `i` the class indicator is
`s_i (β,g) = [disputeA A W β g i]` and its quadratic form is
`∑_{(β,g)} s_i(β,g)·classOpB B s_i (β,g)` (by `disputeA_aIdx`,
`aIdx A (nB B (0,β,g) j) i = (1-β, g*(B j)^{±1}, i)`), and symmetrically for B-labels with
`classOpA`. If the total form is at least `c|R|` then some class satisfies `⟨s,Ms⟩ ≥ c·‖s‖₁`
(with `‖s‖₁ = ∑ s`, and `|R| = Σ_classes ‖s‖₁`); for a `0/1`-valued `s` write `s = q·1 + h`,
`q = ‖s‖₁/(2|G|)`, so `⟨s,Ms⟩ = q‖s‖₁ + ⟨h,Mh⟩ ≤ q‖s‖₁ + μ(‖s‖₁ - q‖s‖₁)` by the gap hypotheses;
hence `c ≤ q + μ(1-q)`, i.e. `q(1-μ) ≥ c-μ`; if `c-μ ≤ 0` the result is trivial, otherwise
`1-μ > 0` and `q ≥ c-μ`, giving `dispCount ≥ ‖s‖₁ = 2|G|q ≥ (c-μ)|G|`. -/
theorem lr_Mpar_case {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) (μ c : ℝ)
    (hΔ : 0 < Δ) (hμ : 0 ≤ μ)
    (hgapA : ∀ s : Fin 2 × G → ℝ, (∑ p, s p) = 0 →
      ∑ p, s p * classOpA A s p ≤ μ * ∑ p, s p ^ 2)
    (hgapB : ∀ s : Fin 2 × G → ℝ, (∑ p, s p) = 0 →
      ∑ p, s p * classOpB B s p ≤ μ * ∑ p, s p ^ 2)
    (hpos : 0 < dispCount A B W)
    (hlarge : c * (dispCount A B W : ℝ) ≤ MparForm A B W) :
    (c - μ) * (Fintype.card G : ℝ) ≤ (dispCount A B W : ℝ) := by
  rcases le_or_gt (c - μ) 0 with htriv | hcμ
  · have h1 : (c - μ) * (Fintype.card G : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg htriv (by positivity)
    have h2 : (0 : ℝ) ≤ (dispCount A B W : ℝ) := by positivity
    linarith
  have hGnn : (0 : ℝ) ≤ (Fintype.card G : ℝ) := by positivity
  have hdisppos : (0 : ℝ) < (dispCount A B W : ℝ) := by exact_mod_cast hpos
  let Lf : Fin Δ ⊕ Fin Δ → ℝ := Sum.elim (fun i => l1 (sA A W i)) (fun j => l1 (sB B W j))
  let Qf : Fin Δ ⊕ Fin Δ → ℝ := Sum.elim (fun i => QA A B W i) (fun j => QB A B W j)
  have hLf_inl : ∀ i, Lf (Sum.inl i) = l1 (sA A W i) := fun i => rfl
  have hLf_inr : ∀ j, Lf (Sum.inr j) = l1 (sB B W j) := fun j => rfl
  have hQf_inl : ∀ i, Qf (Sum.inl i) = QA A B W i := fun i => rfl
  have hQf_inr : ∀ j, Qf (Sum.inr j) = QB A B W j := fun j => rfl
  have hsumL : ∑ x, Lf x = (dispCount A B W : ℝ) := by
    rw [Fintype.sum_sum_type,
      Finset.sum_congr rfl (fun i _ => hLf_inl i), Finset.sum_congr rfl (fun j _ => hLf_inr j)]
    exact (lr_Mpar_disp_decomp A B W).symm
  have hsumQ : ∑ x, Qf x = MparForm A B W := by
    rw [Fintype.sum_sum_type,
      Finset.sum_congr rfl (fun i _ => hQf_inl i), Finset.sum_congr rfl (fun j _ => hQf_inr j)]
    exact (lr_Mpar_form_decomp A B W).symm
  have hsA01 : ∀ i (p : Fin 2 × G), sA A W i p = 0 ∨ sA A W i p = 1 := by
    intro i p
    by_cases h : disputeA A W p.1 p.2 i <;> simp [sA, h]
  have hsB01 : ∀ j (p : Fin 2 × G), sB B W j p = 0 ∨ sB B W j p = 1 := by
    intro j p
    by_cases h : disputeB B W p.1 p.2 j <;> simp [sB, h]
  have hsAnn : ∀ i (p : Fin 2 × G), 0 ≤ sA A W i p := fun i p => by
    rcases hsA01 i p with h | h <;> linarith
  have hsBnn : ∀ j (p : Fin 2 × G), 0 ≤ sB B W j p := fun j p => by
    rcases hsB01 j p with h | h <;> linarith
  have hLnn : ∀ x, 0 ≤ Lf x := by
    intro x
    rcases x with i | j
    · change 0 ≤ l1 (sA A W i)
      exact Finset.sum_nonneg (fun p _ => hsAnn i p)
    · change 0 ≤ l1 (sB B W j)
      exact Finset.sum_nonneg (fun p _ => hsBnn j p)
  have hQzero : ∀ x, Lf x = 0 → Qf x = 0 := by
    intro x hx
    rcases x with i | j
    · change ∑ p, sA A W i p = 0 at hx
      change ∑ p : Fin 2 × G, sA A W i p * classOpB B (sA A W i) p = 0
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun p _ => hsAnn i p)] at hx
      exact Finset.sum_eq_zero (fun p _ => by rw [hx p (Finset.mem_univ p), zero_mul])
    · change ∑ p, sB B W j p = 0 at hx
      change ∑ p : Fin 2 × G, sB B W j p * classOpA A (sB B W j) p = 0
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun p _ => hsBnn j p)] at hx
      exact Finset.sum_eq_zero (fun p _ => by rw [hx p (Finset.mem_univ p), zero_mul])
  -- there is a class with `0 < Lf x`
  have hex : ∃ x : Fin Δ ⊕ Fin Δ, 0 < Lf x := by
    by_contra h
    simp only [not_exists, not_lt] at h
    have hle : ∑ x, Lf x ≤ 0 := Finset.sum_nonpos (fun x _ => h x)
    rw [hsumL] at hle
    linarith
  obtain ⟨x0, hx0⟩ := hex
  have hTne : (Finset.univ.filter (fun x : Fin Δ ⊕ Fin Δ => 0 < Lf x)).Nonempty :=
    ⟨x0, by simp [hx0]⟩
  have hTL : ∑ x ∈ Finset.univ.filter (fun x : Fin Δ ⊕ Fin Δ => 0 < Lf x), Lf x = ∑ x, Lf x := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro x _ hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hx
    exact le_antisymm hx (hLnn x)
  have hTQ : ∑ x ∈ Finset.univ.filter (fun x : Fin Δ ⊕ Fin Δ => 0 < Lf x), Qf x = ∑ x, Qf x := by
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro x _ hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hx
    exact hQzero x (le_antisymm hx (hLnn x))
  have hineq : ∑ x ∈ Finset.univ.filter (fun x : Fin Δ ⊕ Fin Δ => 0 < Lf x), c * Lf x
      ≤ ∑ x ∈ Finset.univ.filter (fun x : Fin Δ ⊕ Fin Δ => 0 < Lf x), Qf x := by
    have e1 : ∑ x ∈ Finset.univ.filter (fun x : Fin Δ ⊕ Fin Δ => 0 < Lf x), c * Lf x
        = c * (dispCount A B W : ℝ) := by
      rw [← Finset.mul_sum, hTL, hsumL]
    have e2 : ∑ x ∈ Finset.univ.filter (fun x : Fin Δ ⊕ Fin Δ => 0 < Lf x), Qf x
        = MparForm A B W := by rw [hTQ, hsumQ]
    rw [e1, e2]; exact hlarge
  obtain ⟨x, hxT, hxle⟩ := Finset.exists_le_of_sum_le hTne hineq
  have hLx : 0 < Lf x := (Finset.mem_filter.mp hxT).2
  have hLxle : Lf x ≤ (dispCount A B W : ℝ) := by
    rw [← hsumL]
    exact Finset.single_le_sum (fun y _ => hLnn y) (Finset.mem_univ x)
  rcases x with i | j
  · obtain ⟨haddB, hsmulB, honeB, hsumB⟩ := lr_classOpB_basic hΔ B
    have hgb := class_bound μ c hμ (sA A W i) (classOpB B) (Qf (Sum.inl i)) (hsA01 i)
      haddB hsmulB honeB hsumB hgapB rfl hxle hLx
    exact le_trans hgb hLxle
  · obtain ⟨haddA, hsmulA, honeA, hsumA⟩ := lr_classOpA_basic hΔ A
    have hgb := class_bound μ c hμ (sB B W j) (classOpA A) (Qf (Sum.inr j)) (hsB01 j)
      haddA hsmulA honeA hsumA hgapA rfl hxle hLx
    exact le_trans hgb hLxle

end Work.LT
