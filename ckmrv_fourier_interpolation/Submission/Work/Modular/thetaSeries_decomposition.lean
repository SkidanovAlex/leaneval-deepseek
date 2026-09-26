import Mathlib
import Submission.Work.Modular.Basic
import Submission.Work.Modular.Lattice
import Submission.Work.Modular.ThetaCharDefs

namespace Work.Modular

open UpperHalfPlane
open scoped Real MatrixGroups BigOperators

set_option maxHeartbeats 800000

/-! ## Basic properties of `thetaSign` and the one-dimensional sums -/

lemma thetaSign_eq_zpow (n : ℤ) : thetaSign n = (-1 : ℂ) ^ n := by
  rw [thetaSign]
  rw [show π * Complex.I * (n : ℂ) = (n : ℂ) * (π * Complex.I) by ring]
  rw [Complex.exp_int_mul, Complex.exp_pi_mul_I]

lemma thetaSign_eq_ite (n : ℤ) : thetaSign n = if Even n then 1 else -1 := by
  rw [thetaSign_eq_zpow, neg_one_zpow_eq_ite]

lemma thetaSign_norm (n : ℤ) : ‖thetaSign n‖ = 1 := by
  rw [thetaSign_eq_zpow, norm_zpow]
  simp

lemma thetaSign_negSucc (n : ℤ) : thetaSign (-n - 1) = - thetaSign n := by
  rw [thetaSign_eq_ite, thetaSign_eq_ite]
  have h : Even (-n - 1) ↔ ¬ Even n := by
    have : -n - 1 = -(n + 1) := by ring
    rw [this, even_neg, Int.even_add_one]
  by_cases hn : Even n
  · have h2 : ¬ Even (-n - 1) := fun hh => (h.mp hh) hn
    simp [hn, h2]
  · have h2 : Even (-n - 1) := h.mpr hn
    simp [hn, h2]

lemma thetaSign_prod (m : Fin 8 → ℤ) :
    (∏ i : Fin 8, thetaSign (m i)) = if Even (∑ i : Fin 8, m i) then 1 else -1 := by
  have h : (∏ i : Fin 8, thetaSign (m i)) = thetaSign (∑ i : Fin 8, m i) := by
    simp only [thetaSign]
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    rw [Finset.mul_sum]
  rw [h, thetaSign_eq_ite]

lemma tsum_thetaChar_zero (τ : ℍ) :
    ∑' n : ℤ, thetaChar (τ : ℂ) 0 n = jacobiTheta (τ : ℂ) := by
  rw [jacobiTheta]
  apply tsum_congr
  intro n
  simp only [thetaChar, Complex.ofReal_zero, add_zero]
  congr 1
  ring

lemma tsum_sign_thetaChar_zero (τ : ℍ) :
    ∑' n : ℤ, thetaSign n * thetaChar (τ : ℂ) 0 n = jacobiTheta₂ (1 / 2) (τ : ℂ) := by
  rw [jacobiTheta₂]
  apply tsum_congr
  intro n
  rw [jacobiTheta₂_term, thetaSign, thetaChar]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

lemma tsum_thetaChar_half (τ : ℍ) :
    ∑' n : ℤ, thetaChar (τ : ℂ) (1 / 2) n =
      Complex.exp (π * Complex.I * (τ : ℂ) / 4) * jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ) := by
  rw [jacobiTheta₂, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [jacobiTheta₂_term, thetaChar]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

lemma tsum_sign_thetaChar_half (τ : ℍ) :
    ∑' n : ℤ, thetaSign n * thetaChar (τ : ℂ) (1 / 2) n = 0 := by
  let F : ℤ → ℂ := fun n => thetaSign n * thetaChar (τ : ℂ) (1 / 2) n
  let e : ℤ ≃ ℤ := ⟨fun n => -n - 1, fun n => -n - 1, by intro n; ring, by intro n; ring⟩
  have hee : ∀ n, e n = -n - 1 := fun n => rfl
  have he : ∀ n, F (e n) = - F n := by
    intro n
    have hc : thetaChar (τ : ℂ) (1 / 2) (e n) = thetaChar (τ : ℂ) (1 / 2) n := by
      rw [hee n, thetaChar, thetaChar]
      congr 1
      push_cast
      ring
    have hs : thetaSign (e n) = - thetaSign n := by
      rw [hee n, thetaSign_negSucc]
    change thetaSign (e n) * thetaChar (τ : ℂ) (1 / 2) (e n) =
      -(thetaSign n * thetaChar (τ : ℂ) (1 / 2) n)
    rw [hc, hs]
    ring
  have h1 : ∑' n : ℤ, F (e n) = ∑' n : ℤ, F n := Equiv.tsum_eq e F
  have hsum : ∑' n : ℤ, F n = - ∑' n : ℤ, F n := by
    calc ∑' n : ℤ, F n = ∑' n : ℤ, F (e n) := h1.symm
      _ = ∑' n : ℤ, -F n := tsum_congr he
      _ = - ∑' n : ℤ, F n := tsum_neg
  have hsum2 : (∑' n : ℤ, F n) + ∑' n : ℤ, F n = 0 := eq_neg_iff_add_eq_zero.mp hsum
  exact add_self_eq_zero.mp hsum2

lemma summable_thetaChar (τ : ℍ) (c : ℝ) :
    Summable (fun n : ℤ => thetaChar (τ : ℂ) c n) := by
  have h : Summable (fun n : ℤ => jacobiTheta₂_term n ((c : ℂ) * (τ : ℂ)) (τ : ℂ)) :=
    (summable_jacobiTheta₂_term_iff ((c : ℂ) * (τ : ℂ)) (τ : ℂ)).mpr τ.2
  refine (h.mul_left (Complex.exp (π * Complex.I * (τ : ℂ) * (c : ℂ) ^ 2))).congr ?_
  intro n
  rw [thetaChar, jacobiTheta₂_term]
  rw [← Complex.exp_add]
  congr 1
  ring_nf

lemma summable_sign_thetaChar (τ : ℍ) (c : ℝ) :
    Summable (fun n : ℤ => thetaSign n * thetaChar (τ : ℂ) c n) := by
  refine Summable.of_norm_bounded (summable_thetaChar τ c).norm ?_
  intro n
  rw [norm_mul, thetaSign_norm, one_mul]

/-! ## The `E₈` parametrisation -/

lemma charOf_eq_zero_or_half (δ : Fin 2) : charOf δ = 0 ∨ charOf δ = 1 / 2 := by
  have := δ.isLt
  simp only [charOf]
  rcases (by omega : (δ : ℕ) = 0 ∨ (δ : ℕ) = 1) with h | h <;> rw [h] <;> norm_num

lemma charOf_injective : Function.Injective charOf := by
  intro a b h
  have h2 : (a : ℕ) = (b : ℕ) := by
    have h3 : ((a : ℕ) : ℝ) = ((b : ℕ) : ℝ) := by
      simp only [charOf] at h
      linarith
    exact_mod_cast h3
  exact Fin.ext h2

@[simp] lemma charOf_zero : charOf 0 = 0 := by simp [charOf]
@[simp] lemma charOf_one : charOf 1 = 1 / 2 := by simp [charOf]

lemma e8ParamMap_injective : Function.Injective e8ParamMap := by
  rintro ⟨m, δ⟩ ⟨m', δ'⟩ hpq
  have hfun : ∀ i, (m i : ℝ) + charOf δ = (m' i : ℝ) + charOf δ' := by
    intro i
    have := congrArg (fun x : EuclideanSpace ℝ (Fin 8) => x.ofLp i) hpq
    simpa [e8ParamMap_apply] using this
  have hδ : charOf δ = charOf δ' := by
    have h0 := hfun 0
    have hint : (m 0 : ℝ) - (m' 0 : ℝ) = charOf δ' - charOf δ := by linarith
    rcases charOf_eq_zero_or_half δ with h | h <;> rcases charOf_eq_zero_or_half δ' with h' | h'
    · rw [h, h']
    · exfalso
      have h2 : (2 : ℝ) * ((m 0 : ℝ) - (m' 0 : ℝ)) = 1 := by rw [hint, h, h']; norm_num
      have h3 : (2 * (m 0 - m' 0) : ℤ) = 1 := by
        have : ((2 * (m 0 - m' 0) : ℤ) : ℝ) = 1 := by push_cast; exact h2
        exact_mod_cast this
      omega
    · exfalso
      have h2 : (2 : ℝ) * ((m 0 : ℝ) - (m' 0 : ℝ)) = -1 := by rw [hint, h, h']; norm_num
      have h3 : (2 * (m 0 - m' 0) : ℤ) = -1 := by
        have : ((2 * (m 0 - m' 0) : ℤ) : ℝ) = -1 := by push_cast; exact h2
        exact_mod_cast this
      omega
    · rw [h, h']
  have h1 : m = m' := by
    funext i
    have := hfun i
    rw [hδ] at this
    exact_mod_cast (by linarith : (m i : ℝ) = (m' i : ℝ))
  exact Prod.ext h1 (charOf_injective hδ)

lemma e8ParamMap_mem_iff (p : E8Idx) :
    e8ParamMap p ∈ E8 ↔ Even (∑ i : Fin 8, p.1 i) := by
  rw [mem_E8]
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨s, hs⟩ := h3
    have hsum : ∑ i : Fin 8, (e8ParamMap p).ofLp i =
        ((∑ i : Fin 8, p.1 i : ℤ) : ℝ) + 4 * ((p.2 : ℕ) : ℝ) := by
      simp only [e8ParamMap_apply, charOf]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ← Int.cast_sum]
      simp only [nsmul_eq_mul]
      push_cast
      ring
    rw [hsum] at hs
    refine ⟨s - 2 * (p.2 : ℕ), ?_⟩
    have hreal : ((∑ i : Fin 8, p.1 i : ℤ) : ℝ) =
        ((s - 2 * (p.2 : ℕ)) + (s - 2 * (p.2 : ℕ)) : ℤ) := by
      have : (((s - 2 * (p.2 : ℕ)) + (s - 2 * (p.2 : ℕ)) : ℤ) : ℝ) =
          2 * ((s : ℝ) - 2 * ((p.2 : ℕ) : ℝ)) := by push_cast; ring
      rw [this]
      linarith
    exact_mod_cast hreal
  · intro he
    refine ⟨?_, ?_, ?_⟩
    · intro i
      refine ⟨2 * p.1 i + (p.2 : ℕ), ?_⟩
      simp only [e8ParamMap_apply, charOf]
      push_cast
      ring
    · intro i j
      refine ⟨p.1 i - p.1 j, ?_⟩
      simp only [e8ParamMap_apply, charOf]
      push_cast
      ring
    · obtain ⟨k, hk⟩ := he
      refine ⟨k + 2 * (p.2 : ℕ), ?_⟩
      have hca : ((∑ i : Fin 8, p.1 i : ℤ) : ℝ) = 2 * (k : ℝ) := by
        rw [hk]; push_cast; ring
      simp only [e8ParamMap_apply, charOf]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ← Int.cast_sum]
      simp only [nsmul_eq_mul]
      rw [hca]
      push_cast
      ring

lemma thetaTerm_e8ParamMap (τ : ℍ) (p : E8Idx) :
    thetaTerm τ (e8ParamMap p) = ∏ i : Fin 8, thetaChar (τ : ℂ) (charOf p.2) (p.1 i) := by
  rw [thetaTerm]
  have hnorm' : ‖e8ParamMap p‖ ^ 2 = ∑ i : Fin 8, ((p.1 i : ℝ) + charOf p.2) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    rw [e8ParamMap_apply, Real.norm_eq_abs, sq_abs]
  have hnorm : ((‖e8ParamMap p‖ ^ 2 : ℝ) : ℂ) =
      ∑ i : Fin 8, (((p.1 i : ℝ) + charOf p.2) ^ 2 : ℂ) := by
    rw [hnorm']; push_cast; rfl
  rw [hnorm, Finset.mul_sum, Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [thetaChar]
  congr 1

lemma e8ParamMap_surj (x : EuclideanSpace ℝ (Fin 8)) (hx : x ∈ E8) :
    ∃ p : E8Idx, Even (∑ i : Fin 8, p.1 i) ∧ e8ParamMap p = x := by
  obtain ⟨h1, h2, h3⟩ := mem_E8.mp hx
  choose n hn using h1
  obtain ⟨s, hs⟩ := h3
  have hpar : ∀ i, (2 : ℤ) ∣ (n i - n 0) := by
    intro i
    obtain ⟨c, hc⟩ := h2 i 0
    refine ⟨c, ?_⟩
    have hcast : ((n i - n 0 : ℤ) : ℝ) = (2 * c : ℤ) := by
      push_cast
      rw [← hn i, ← hn 0]
      linarith
    exact_mod_cast hcast
  have hnsum : ((∑ i : Fin 8, n i : ℤ) : ℝ) = 4 * (s : ℝ) := by
    have ha : ((∑ i : Fin 8, n i : ℤ) : ℝ) = ∑ i, (n i : ℝ) := by rw [Int.cast_sum]
    rw [ha]
    have hb : (∑ i : Fin 8, (n i : ℝ)) = 2 * (∑ i : Fin 8, x.ofLp i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [← hn i]
    rw [hb, hs]; ring
  by_cases h0e : Even (n 0)
  · have hev : ∀ i, Even (n i) := by
      intro i
      obtain ⟨c, hc⟩ := hpar i
      obtain ⟨k, hk⟩ := h0e
      exact ⟨c + k, by omega⟩
    choose m hm using hev
    refine ⟨(m, 0), ?_, ?_⟩
    · change Even (∑ i : Fin 8, m i)
      have hsum2 : ((2 * (∑ i : Fin 8, m i) : ℤ) : ℝ) = 4 * (s : ℝ) := by
        rw [← hnsum]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hm i]; ring
      have hgoal : (2 * (∑ i : Fin 8, m i) : ℤ) = 4 * s := by exact_mod_cast hsum2
      refine ⟨s, ?_⟩
      omega
    · ext i
      have h1' : (n i : ℝ) = 2 * (m i : ℝ) := by rw [hm i]; push_cast; ring
      have h2' : 2 * x.ofLp i = (n i : ℝ) := hn i
      simp only [e8ParamMap_apply, charOf, Fin.val_zero, Nat.cast_zero]
      linarith
  · have hod : ∀ i, Odd (n i) := by
      intro i
      obtain ⟨c, hc⟩ := hpar i
      have h0o : Odd (n 0) := Int.not_even_iff_odd.mp h0e
      obtain ⟨k, hk⟩ := h0o
      exact ⟨c + k, by omega⟩
    choose m hm using hod
    refine ⟨(m, 1), ?_, ?_⟩
    · change Even (∑ i : Fin 8, m i)
      have hkey : (∑ i : Fin 8, n i) = 2 * (∑ i : Fin 8, m i) + 8 := by
        rw [show (∑ i : Fin 8, n i) = ∑ i : Fin 8, (2 * m i + 1) from
          Finset.sum_congr rfl (fun i _ => by rw [hm i])]
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          ← Finset.mul_sum]
        norm_num
      have hsum2 : ((2 * (∑ i : Fin 8, m i) + 8 : ℤ) : ℝ) = 4 * (s : ℝ) := by
        rw [← hnsum, hkey]
      have hgoal : (2 * (∑ i : Fin 8, m i) + 8 : ℤ) = 4 * s := by exact_mod_cast hsum2
      refine ⟨s - 2, ?_⟩
      omega
    · ext i
      have h1' : (n i : ℝ) = 2 * (m i : ℝ) + 1 := by rw [hm i]; push_cast; ring
      have h2' : 2 * x.ofLp i = (n i : ℝ) := hn i
      simp only [e8ParamMap_apply, charOf, Fin.val_one, Nat.cast_one]
      norm_num
      linarith


/-! ## The product factorisation over `Fin n → ℤ` -/

lemma summable_pi_prod {n : ℕ} (f : Fin n → ℤ → ℂ) (hf : ∀ i, Summable (f i)) :
    Summable (fun m : Fin n → ℤ => ∏ i, f i (m i)) := by
  induction n with
  | zero => exact Summable.of_finite
  | succ n ih =>
      have hg := ih (fun i => f i.succ) (fun i => hf i.succ)
      have hprod := summable_mul_of_summable_norm (hf 0).norm hg.norm
      have hF : Summable ((fun m : Fin (n+1) → ℤ => ∏ i : Fin (n+1), f i (m i)) ∘
          (Fin.consEquiv (fun _ : Fin (n+1) => ℤ))) := by
        refine hprod.congr ?_
        intro q
        simp only [Function.comp_apply, Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero,
          Fin.cons_succ]
      exact (Equiv.summable_iff (f := fun m : Fin (n+1) → ℤ => ∏ i : Fin (n+1), f i (m i))
        (Fin.consEquiv (fun _ : Fin (n+1) => ℤ))).mp hF

lemma tsum_pi_prod {n : ℕ} (f : Fin n → ℤ → ℂ) (hf : ∀ i, Summable (f i)) :
    ∑' m : Fin n → ℤ, ∏ i : Fin n, f i (m i) = ∏ i : Fin n, ∑' k : ℤ, f i k := by
  induction n with
  | zero =>
      rw [tsum_eq_single (0 : Fin 0 → ℤ) (fun b hb => absurd (Subsingleton.elim b 0) hb)]
      simp
  | succ n ih =>
      have hg := summable_pi_prod (fun i => f i.succ) (fun i => hf i.succ)
      have hprod := summable_mul_of_summable_norm (hf 0).norm hg.norm
      have hgtsum := ih (fun i => f i.succ) (fun i => hf i.succ)
      rw [← Equiv.tsum_eq (Fin.consEquiv (fun _ : Fin (n+1) => ℤ))
        (fun m : Fin (n+1) → ℤ => ∏ i : Fin (n+1), f i (m i))]
      have hterm : ∀ q : ℤ × (Fin n → ℤ),
          (∏ i : Fin (n+1), f i ((Fin.consEquiv (fun _ : Fin (n+1) => ℤ)) q i))
            = f 0 q.1 * ∏ i : Fin n, f i.succ (q.2 i) := by
        intro q
        change (∏ i : Fin (n+1), f i (Fin.cons (α := fun _ : Fin (n+1) => ℤ) q.1 q.2 i))
            = f 0 q.1 * ∏ i : Fin n, f i.succ (q.2 i)
        rw [Fin.prod_univ_succ]
        simp [Fin.cons_zero, Fin.cons_succ]
      simp_rw [hterm]
      rw [Summable.tsum_prod hprod]
      have hstep : ∀ k : ℤ, (∑' m : Fin n → ℤ, f 0 k * ∏ i : Fin n, f i.succ (m i))
          = f 0 k * ∏ i : Fin n, ∑' j : ℤ, f i.succ j := by
        intro k
        rw [Summable.tsum_mul_left (f 0 k) hg, hgtsum]
      simp_rw [hstep]
      rw [Summable.tsum_mul_right (∏ i : Fin n, ∑' j : ℤ, f i.succ j) (hf 0),
        Fin.prod_univ_succ]

/-! ## Splitting the `ℤ⁸ × {0,1}` index into the two cosets -/

/-- The index set of the parametrisation, split into the integral and the half-integral
coset. -/
def idxEquivSum : E8Idx ≃ (Fin 8 → ℤ) ⊕ (Fin 8 → ℤ) where
  toFun p := if p.2 = 0 then Sum.inl p.1 else Sum.inr p.1
  invFun s := match s with
    | Sum.inl m => (m, 0)
    | Sum.inr m => (m, 1)
  left_inv := by
    rintro ⟨m, δ⟩
    fin_cases δ <;> simp
  right_inv := by
    rintro (m | m) <;> simp

/-- The product of one-dimensional theta summands along the `δ`-th coset. -/
noncomputable def gg (τ : ℍ) (δ : Fin 2) (m : Fin 8 → ℤ) : ℂ :=
  ∏ i : Fin 8, thetaChar (τ : ℂ) (charOf δ) (m i)

/-- The same, with the sign twist `∏ (-1)^{m i}`. -/
noncomputable def hh (τ : ℍ) (δ : Fin 2) (m : Fin 8 → ℤ) : ℂ :=
  ∏ i : Fin 8, thetaSign (m i) * thetaChar (τ : ℂ) (charOf δ) (m i)

lemma summable_gg (τ : ℍ) (δ : Fin 2) : Summable (gg τ δ) :=
  summable_pi_prod (fun _ : Fin 8 => fun n : ℤ => thetaChar (τ : ℂ) (charOf δ) n)
    (fun _ => summable_thetaChar τ (charOf δ))

lemma summable_hh (τ : ℍ) (δ : Fin 2) : Summable (hh τ δ) :=
  summable_pi_prod
    (fun _ : Fin 8 => fun n : ℤ => thetaSign n * thetaChar (τ : ℂ) (charOf δ) n)
    (fun _ => summable_sign_thetaChar τ (charOf δ))

lemma tsum_gg (τ : ℍ) (δ : Fin 2) :
    ∑' m : Fin 8 → ℤ, gg τ δ m = (∑' n : ℤ, thetaChar (τ : ℂ) (charOf δ) n) ^ 8 := by
  simp only [gg]
  rw [tsum_pi_prod (fun _ : Fin 8 => fun n : ℤ => thetaChar (τ : ℂ) (charOf δ) n)
    (fun _ => summable_thetaChar τ (charOf δ))]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma tsum_hh (τ : ℍ) (δ : Fin 2) :
    ∑' m : Fin 8 → ℤ, hh τ δ m
      = (∑' n : ℤ, thetaSign n * thetaChar (τ : ℂ) (charOf δ) n) ^ 8 := by
  simp only [hh]
  rw [tsum_pi_prod
    (fun _ : Fin 8 => fun n : ℤ => thetaSign n * thetaChar (τ : ℂ) (charOf δ) n)
    (fun _ => summable_sign_thetaChar τ (charOf δ))]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma summable_idx_prod (τ : ℍ) (g : Fin 2 → (Fin 8 → ℤ) → ℂ) (hg : ∀ δ, Summable (g δ)) :
    Summable (fun p : E8Idx => g p.2 p.1) := by
  let F : (Fin 8 → ℤ) ⊕ (Fin 8 → ℤ) → ℂ := Sum.elim (g 0) (g 1)
  have hF : Summable F := Summable.sum F (by simpa [F] using hg 0) (by simpa [F] using hg 1)
  have hcomp : F ∘ idxEquivSum = (fun p : E8Idx => g p.2 p.1) := by
    funext p
    rcases p with ⟨m, δ⟩
    fin_cases δ <;> simp [F, idxEquivSum]
  rw [← hcomp]
  exact (Equiv.summable_iff (f := F) idxEquivSum).mpr hF

lemma summable_gg_idx (τ : ℍ) : Summable (fun p : E8Idx => gg τ p.2 p.1) :=
  summable_idx_prod τ (gg τ) (summable_gg τ)

lemma summable_hh_idx (τ : ℍ) : Summable (fun p : E8Idx => hh τ p.2 p.1) :=
  summable_idx_prod τ (hh τ) (summable_hh τ)

lemma tsum_idx_split (τ : ℍ) (g : Fin 2 → (Fin 8 → ℤ) → ℂ) (hg : ∀ δ, Summable (g δ)) :
    ∑' p : E8Idx, g p.2 p.1 = (∑' m : Fin 8 → ℤ, g 0 m) + (∑' m : Fin 8 → ℤ, g 1 m) := by
  rw [← Equiv.tsum_eq idxEquivSum.symm (fun p : E8Idx => g p.2 p.1)]
  rw [Summable.tsum_sum
      (by
        have h : ((fun s : (Fin 8 → ℤ) ⊕ (Fin 8 → ℤ) =>
            g (idxEquivSum.symm s).2 (idxEquivSum.symm s).1) ∘ Sum.inl) = g 0 := by
          funext m; simp [idxEquivSum, Function.comp_apply]
        rw [h]; exact hg 0)
      (by
        have h : ((fun s : (Fin 8 → ℤ) ⊕ (Fin 8 → ℤ) =>
            g (idxEquivSum.symm s).2 (idxEquivSum.symm s).1) ∘ Sum.inr) = g 1 := by
          funext m; simp [idxEquivSum, Function.comp_apply]
        rw [h]; exact hg 1)]
  congr 1 <;> apply tsum_congr <;> intro m <;> simp [idxEquivSum, Function.comp_apply]



/-- The classical decomposition of the `E₈` theta series into eighth powers of the Jacobi
theta functions:
`Θ_{E₈}(τ) = (1/2) (θ₃(τ)^8 + θ₄(τ)^8 + θ₂(τ)^8)`,
where `θ₃ = jacobiTheta`, `θ₄(τ) = jacobiTheta₂ (1/2) τ` and
`θ₂(τ) = exp (π i τ / 4) * jacobiTheta₂ (τ / 2) τ`.

This follows by splitting `E₈ = D₈ ⊔ (D₈ + s)` with `s = (1/2, …, 1/2)` and using the
factorisation of sums over `ℤ⁸` into products of one-dimensional sums. -/
theorem thetaSeries_decomposition (τ : ℍ) :
    thetaSeries E8 τ = (1 / 2) * (jacobiTheta (τ : ℂ) ^ 8 +
      (jacobiTheta₂ (1 / 2) (τ : ℂ)) ^ 8 +
      (Complex.exp (π * Complex.I * (τ : ℂ) / 4) * jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ)) ^ 8) := by
  have h1 : thetaSeries E8 τ = ∑' p : E8Idx,
      (1 / 2) * (1 + ∏ i : Fin 8, thetaSign (p.1 i)) * gg τ p.2 p.1 := by
    let S : Set E8Idx := {p | Even (∑ i : Fin 8, p.1 i)}
    have hbij : Function.Bijective
        (fun p : S => (⟨e8ParamMap p.1, (e8ParamMap_mem_iff p.1).mpr p.2⟩ : E8)) := by
      constructor
      · rintro p q hpq
        refine Subtype.ext ?_
        apply e8ParamMap_injective
        exact congrArg (fun x : E8 => (x : EuclideanSpace ℝ (Fin 8))) hpq
      · intro x
        obtain ⟨p, hpS, hpx⟩ := e8ParamMap_surj x.1 x.2
        exact ⟨⟨p, hpS⟩, Subtype.ext hpx⟩
    let e : S ≃ E8 := Equiv.ofBijective
      (fun p : S => (⟨e8ParamMap p.1, (e8ParamMap_mem_iff p.1).mpr p.2⟩ : E8)) hbij
    rw [thetaSeries,
      ← Equiv.tsum_eq e (fun x : E8 => thetaTerm τ (x : EuclideanSpace ℝ (Fin 8)))]
    trans ∑' p : S, gg τ p.1.2 p.1.1
    · apply tsum_congr
      intro p
      show thetaTerm τ (e8ParamMap p.1) = gg τ p.1.2 p.1.1
      rw [thetaTerm_e8ParamMap]
      simp only [gg]
    · rw [tsum_subtype S (fun p : E8Idx => gg τ p.2 p.1)]
      apply tsum_congr
      intro p
      by_cases hp : p ∈ S
      · rw [Set.indicator_of_mem hp]
        have hw : (∏ i : Fin 8, thetaSign (p.1 i)) = 1 := by
          rw [thetaSign_prod]
          exact if_pos (show Even (∑ i : Fin 8, p.1 i) from hp)
        rw [hw]; ring
      · rw [Set.indicator_of_notMem hp]
        have hw : (∏ i : Fin 8, thetaSign (p.1 i)) = -1 := by
          rw [thetaSign_prod]
          exact if_neg (show ¬ Even (∑ i : Fin 8, p.1 i) from hp)
        rw [hw]; ring
  have hWG : ∀ p : E8Idx,
      (∏ i : Fin 8, thetaSign (p.1 i)) * gg τ p.2 p.1 = hh τ p.2 p.1 := by
    intro p
    simp only [gg, hh, Finset.prod_mul_distrib]
  have hsplit : ∑' p : E8Idx,
      (1 / 2) * (1 + ∏ i : Fin 8, thetaSign (p.1 i)) * gg τ p.2 p.1
      = (1 / 2) * (∑' p : E8Idx, gg τ p.2 p.1)
        + (1 / 2) * (∑' p : E8Idx, hh τ p.2 p.1) := by
    rw [show (∑' p : E8Idx,
          (1 / 2) * (1 + ∏ i : Fin 8, thetaSign (p.1 i)) * gg τ p.2 p.1)
        = ∑' p : E8Idx, ((1 / 2) * gg τ p.2 p.1 + (1 / 2) * hh τ p.2 p.1) from by
      apply tsum_congr
      intro p
      rw [← hWG p]; ring]
    rw [Summable.tsum_add (Summable.mul_left (1 / 2) (summable_gg_idx τ))
      (Summable.mul_left (1 / 2) (summable_hh_idx τ))]
    rw [Summable.tsum_mul_left (1 / 2) (summable_gg_idx τ),
      Summable.tsum_mul_left (1 / 2) (summable_hh_idx τ)]
  have hGsplit := tsum_idx_split τ (gg τ) (summable_gg τ)
  have hHsplit := tsum_idx_split τ (hh τ) (summable_hh τ)
  have hG0 : (∑' m : Fin 8 → ℤ, gg τ 0 m) = jacobiTheta (τ : ℂ) ^ 8 := by
    rw [tsum_gg, charOf_zero, tsum_thetaChar_zero]
  have hG1 : (∑' m : Fin 8 → ℤ, gg τ 1 m) =
      (Complex.exp (π * Complex.I * (τ : ℂ) / 4) * jacobiTheta₂ ((τ : ℂ) / 2) (τ : ℂ)) ^ 8 := by
    rw [tsum_gg, charOf_one, tsum_thetaChar_half]
  have hH0 : (∑' m : Fin 8 → ℤ, hh τ 0 m) = (jacobiTheta₂ (1 / 2) (τ : ℂ)) ^ 8 := by
    rw [tsum_hh, charOf_zero, tsum_sign_thetaChar_zero]
  have hH1 : (∑' m : Fin 8 → ℤ, hh τ 1 m) = 0 := by
    rw [tsum_hh, charOf_one, tsum_sign_thetaChar_half, zero_pow (by norm_num : (8 : ℕ) ≠ 0)]
  rw [h1, hsplit, hGsplit, hHsplit, hG0, hG1, hH0, hH1]
  ring

end Work.Modular
