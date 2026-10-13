/-
  WilC4aCS: the algebraic identity `YwL = BasicSA`.

  Under simultaneous real Weierstrass preparation in the linear coordinate `L`, the basic
  semianalytic set `BasicSA F g` (pulled back to the `x`-coordinates) agrees, near `0`, with the
  set `YwL = L⁻¹ Yw` of coefficient/last-variable points whose Weierstrass polynomials satisfy the
  sign conditions prescribed by `SAcoef`.  The only content is bookkeeping: unfold `Yw`/`SAcoef`
  down to the polynomial sign conditions, replace `Qeval ∘ coefFun` by `wpoly`, and compare the two
  sign systems using `sign (u i x) = sign (u i 0) = sign (τ j)`.
-/
import Mathlib
import Submission.Work.WilC4aCS.Defs

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open WilkiesConjecture WilkiesDesign WilkiesDesign.E WilkiesDesign.CG.C4a
open scoped BigOperators

namespace Work.WilC4aCS

/-! ## Helper lemmas -/

/-- `eaEval` over the empty EA chain is `ev0`. -/
lemma ywl_eaEval_nil_eq_ev0 {D : ℕ} (p : EAPoly D 0) (v : Fin D → ℝ) :
    eaEval (EAChain.nil D) p v = ev0 v p := by
  have h : Sum.elim v (fun j : Fin 0 => Real.exp ((EAChain.nil D).ell j v))
      = Sum.elim v (fun _ : Fin 0 => (0 : ℝ)) := by
    funext s
    rcases s with i | j
    · rfl
    · exact Fin.elim0 j
  rw [ev0, eaEval, h]

/-- `ev0` is multiplicative in a constant factor. -/
lemma ywl_ev0_C_mul {D : ℕ} (c : ℝ) (p : EAPoly D 0) (v : Fin D → ℝ) :
    ev0 v (MvPolynomial.C c * p) = c * ev0 v p := by
  simp only [ev0, MvPolynomial.eval_mul, MvPolynomial.eval_C]

/-- `eaEval` over the empty EA chain of a constant multiple. -/
lemma ywl_eaEval_nil_C_mul {D : ℕ} (c : ℝ) (p : EAPoly D 0) (v : Fin D → ℝ) :
    eaEval (EAChain.nil D) (MvPolynomial.C c * p) v = c * ev0 v p := by
  rw [ywl_eaEval_nil_eq_ev0, ywl_ev0_C_mul]

/-- Evaluating the monic polynomial `Qpoly d i` at `Fin.snoc A z` gives `Qeval d A z i`. -/
lemma ywl_eval_Qpoly {K : ℕ} (d : Fin K → ℕ) (A : Fin (∑ i, d i) → ℝ) (z : ℝ) (i : Fin K) :
    ev0 (Fin.snoc A z) (Qpoly d i) = Qeval d A z i := by
  unfold ev0 Qpoly Qeval zIdx cIdx
  simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
    MvPolynomial.eval_pow, MvPolynomial.eval_sum, Sum.elim_inl, Fin.snoc_last,
    Fin.snoc_castSucc]

/-- Unfolding `coefFun` at `coefIdx`. -/
lemma ywl_coefFun_coefIdx {n K : ℕ} (d : Fin K → ℕ)
    (a : ∀ i, Fin (d i) → (Fin n → ℝ) → ℝ) (x' : Fin n → ℝ) (i : Fin K) (j : Fin (d i)) :
    (coefFun d a x') (coefIdx d i j) = a i j x' := by
  have h1 : finSigmaFinEquiv.symm (finSigmaFinEquiv (⟨i, j⟩ : (k : Fin K) × Fin (d k))) =
      ⟨i, j⟩ := Equiv.symm_apply_apply finSigmaFinEquiv ⟨i, j⟩
  show a (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨i, j⟩)).1
      (finSigmaFinEquiv.symm (finSigmaFinEquiv ⟨i, j⟩)).2 x' = a i j x'
  rw [h1]

/-- `wpoly` evaluated on `Fin.snoc x' z` is `Qeval` at the coefficient vector `coefFun d a x'`. -/
lemma ywl_wpoly_eq_Qeval {n K : ℕ} (d : Fin K → ℕ)
    (a : ∀ i, Fin (d i) → (Fin n → ℝ) → ℝ) (x' : Fin n → ℝ) (z : ℝ) (i : Fin K) :
    wpoly (a i) (Fin.snoc x' z) = Qeval d (coefFun d a x') z i := by
  rw [wpoly, Qeval, Fin.snoc_last, Fin.init_snoc]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [ywl_coefFun_coefIdx]

/-- `Qeval` at the coefficient vector of `y` and the last coordinate of `y` is `wpoly`. -/
lemma ywl_Qeval_eq_wpoly {n K : ℕ} (d : Fin K → ℕ)
    (a : ∀ i, Fin (d i) → (Fin n → ℝ) → ℝ) (z : Fin (n + 1) → ℝ) (i : Fin K) :
    Qeval d (coefFun d a (Fin.init z)) (z (Fin.last n)) i = wpoly (a i) z := by
  rw [← ywl_wpoly_eq_Qeval d a (Fin.init z) (z (Fin.last n)) i, Fin.snoc_init_self]

/-- The `SAcoef` set, written as the system of sign conditions on the `Qeval` polynomials. -/
lemma ywl_SAcoef_set (l : ℕ) (d : Fin (l + 1) → ℕ) (τ : Fin l → ℝ) :
    (SAcoef l d τ).set =
      {v : Fin (∑ i, d i + 1) → ℝ |
        ev0 v (Qpoly d 0) = 0 ∧
        ∀ j : Fin l, 0 < τ j * ev0 v (Qpoly d (Fin.succ j))} := by
  ext v
  let B0 : Basic (∑ i, d i + 1) 0 :=
    ⟨[Qpoly d 0],
      List.ofFn (fun j : Fin l => MvPolynomial.C (τ j) * Qpoly d (Fin.succ j))⟩
  have hb : (SAcoef l d τ).basics = [B0] := rfl
  have hm : v ∈ (SAcoef l d τ).set ↔ B0.holds (EAChain.nil (∑ i, d i + 1)) v := by
    rw [SA.set, Set.mem_setOf_eq, hb]
    constructor
    · rintro ⟨B, hB, hh⟩
      rw [List.mem_singleton] at hB
      subst hB
      exact hh
    · intro hh
      exact ⟨B0, List.mem_singleton.mpr rfl, hh⟩
  have hh : B0.holds (EAChain.nil (∑ i, d i + 1)) v ↔
      ev0 v (Qpoly d 0) = 0 ∧
        ∀ j : Fin l, 0 < τ j * ev0 v (Qpoly d (Fin.succ j)) := by
    simp only [B0, Basic.holds]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, fun j => ?_⟩
      · have h1' := h1 (Qpoly d 0) (by simp)
        rw [ywl_eaEval_nil_eq_ev0] at h1'
        exact h1'
      · have h2' := h2 (MvPolynomial.C (τ j) * Qpoly d (Fin.succ j))
          (List.mem_ofFn.mpr ⟨j, rfl⟩)
        rw [ywl_eaEval_nil_C_mul] at h2'
        exact h2'
    · rintro ⟨h1, h2⟩
      constructor
      · intro f hf
        rw [List.mem_singleton] at hf
        subst hf
        rw [ywl_eaEval_nil_eq_ev0]
        exact h1
      · intro g hg
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
        rw [ywl_eaEval_nil_C_mul]
        exact h2 j
  exact hm.trans hh

/-- Membership in `Yw` is exactly the system of sign conditions on the Weierstrass polynomials. -/
lemma ywl_Yw_iff {n l : ℕ} (d : Fin (l + 1) → ℕ)
    (a : ∀ i, Fin (d i) → (Fin n → ℝ) → ℝ) (τ : Fin l → ℝ) (y : Fin (n + 1) → ℝ) :
    y ∈ Yw d a τ ↔
      Qeval d (coefFun d a (Fin.init y)) (y (Fin.last n)) 0 = 0 ∧
      ∀ j : Fin l, 0 < τ j * Qeval d (coefFun d a (Fin.init y)) (y (Fin.last n)) (Fin.succ j) := by
  rw [Yw, Set.mem_setOf_eq, ywl_SAcoef_set]
  simp only [Set.mem_setOf_eq, ywl_eval_Qpoly]

/-- Two nonzero numbers with the same sign have positive product. -/
lemma ywl_pos_mul_of_sign_eq {a b : ℝ} (h : SignType.sign a = SignType.sign b) (ha : a ≠ 0) :
    0 < a * b := by
  rcases lt_trichotomy a 0 with ha' | ha' | ha'
  · have h1 : SignType.sign a = -1 := sign_neg ha'
    have h2 : SignType.sign b = -1 := by rw [← h, h1]
    exact mul_pos_of_neg_of_neg ha' (sign_eq_neg_one_iff.mp h2)
  · exact absurd ha' ha
  · have h1 : SignType.sign a = 1 := sign_pos ha'
    have h2 : SignType.sign b = 1 := by rw [← h, h1]
    exact mul_pos ha' (sign_eq_one_iff.mp h2)

/-- Multiplying by two numbers of equal sign preserves positivity. -/
lemma ywl_pos_mul_iff_of_sign_eq {a b w : ℝ}
    (h : SignType.sign a = SignType.sign b) (ha : a ≠ 0) :
    (0 < a * w ↔ 0 < b * w) := by
  have hab : 0 < a * b := ywl_pos_mul_of_sign_eq h ha
  have ha2 : 0 < a * a := mul_self_pos.mpr ha
  calc (0 < a * w) ↔ 0 < (a * b) * (a * w) := (mul_pos_iff_of_pos_left hab).symm
    _ ↔ 0 < (a * a) * (b * w) := by
        rw [show (a * b) * (a * w) = (a * a) * (b * w) by ring]
    _ ↔ 0 < b * w := mul_pos_iff_of_pos_left ha2

/-! ## The main identity -/

/-- Pointwise form of `YwL = BasicSA` in the coordinates `z` (so that `x = L z`). -/
lemma ywl_aux {n l : ℕ} (F : (Fin (n + 1) → ℝ) → ℝ)
    (g : Fin l → (Fin (n + 1) → ℝ) → ℝ) (h : Fin (l + 1) → (Fin (n + 1) → ℝ) → ℝ)
    (h0 : h 0 = F) (hs : ∀ j, h (Fin.succ j) = g j)
    (L : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ))
    (d : Fin (l + 1) → ℕ) (a : ∀ i, Fin (d i) → (Fin n → ℝ) → ℝ)
    (u : Fin (l + 1) → (Fin (n + 1) → ℝ) → ℝ) (δ : ℝ)
    (hid : ∀ x, ‖x‖ < δ → ∀ i, h i (L x) = u i x * wpoly (a i) x)
    (hu : ∀ x, ‖x‖ < δ → ∀ i, u i x ≠ 0)
    (hus : ∀ x, ‖x‖ < δ → ∀ i, SignType.sign (u i x) = SignType.sign (u i 0))
    (τ : Fin l → ℝ) (hτ : ∀ j, SignType.sign (τ j) = SignType.sign (u (Fin.succ j) 0))
    (z : Fin (n + 1) → ℝ) (hz : ‖z‖ < δ) :
    (L z ∈ YwL L d a τ) ↔ (L z ∈ BasicSA F g) := by
  have hsz : L.symm (L z) = z := L.symm_apply_apply z
  have hmemY : (L z ∈ YwL L d a τ) ↔ (z ∈ Yw d a τ) := by
    rw [YwL, Set.mem_setOf_eq, hsz]
  have hYz : (z ∈ Yw d a τ) ↔
      (wpoly (a 0) z = 0 ∧ ∀ j : Fin l, 0 < τ j * wpoly (a (Fin.succ j)) z) := by
    rw [ywl_Yw_iff d a τ z]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, fun j => ?_⟩
      · have h1' := h1
        rw [ywl_Qeval_eq_wpoly d a z 0] at h1'
        exact h1'
      · have h2' := h2 j
        rw [ywl_Qeval_eq_wpoly d a z (Fin.succ j)] at h2'
        exact h2'
    · rintro ⟨h1, h2⟩
      refine ⟨?_, fun j => ?_⟩
      · rw [ywl_Qeval_eq_wpoly d a z 0]
        exact h1
      · rw [ywl_Qeval_eq_wpoly d a z (Fin.succ j)]
        exact h2 j
  have hmemB : (L z ∈ BasicSA F g) ↔
      (u 0 z * wpoly (a 0) z = 0 ∧
        ∀ j : Fin l, 0 < u (Fin.succ j) z * wpoly (a (Fin.succ j)) z) := by
    have hFz : F (L z) = u 0 z * wpoly (a 0) z := by
      rw [← h0]
      exact hid z hz 0
    have hgz : ∀ j : Fin l, g j (L z) = u (Fin.succ j) z * wpoly (a (Fin.succ j)) z := by
      intro j
      rw [← hs j]
      exact hid z hz (Fin.succ j)
    simp only [BasicSA, Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [← hFz]; exact h1, fun j => by rw [← hgz j]; exact h2 j⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [hFz]; exact h1, fun j => by rw [hgz j]; exact h2 j⟩
  have hiff : ∀ j : Fin l,
      (0 < u (Fin.succ j) z * wpoly (a (Fin.succ j)) z) ↔
      (0 < τ j * wpoly (a (Fin.succ j)) z) := by
    intro j
    have hsign : SignType.sign (τ j) = SignType.sign (u (Fin.succ j) z) :=
      (hτ j).trans (hus z hz (Fin.succ j)).symm
    have huz : u (Fin.succ j) z ≠ 0 := hu z hz (Fin.succ j)
    have hne : SignType.sign (u (Fin.succ j) z) ≠ 0 := sign_ne_zero.mpr huz
    have hτne : τ j ≠ 0 := by
      intro hzero
      rw [hzero, sign_zero] at hsign
      exact hne hsign.symm
    exact (ywl_pos_mul_iff_of_sign_eq hsign hτne).symm
  rw [hmemY, hYz, hmemB]
  constructor
  · rintro ⟨hw0, hws⟩
    exact ⟨by rw [hw0, mul_zero], fun j => (hiff j).mpr (hws j)⟩
  · rintro ⟨hu0, hus'⟩
    exact ⟨(mul_eq_zero.mp hu0).resolve_left (hu z hz 0), fun j => (hiff j).mp (hus' j)⟩

theorem YwL_eq_BasicSA {n l : ℕ} (F : (Fin (n + 1) → ℝ) → ℝ)
    (g : Fin l → (Fin (n + 1) → ℝ) → ℝ) (h : Fin (l + 1) → (Fin (n + 1) → ℝ) → ℝ)
    (h0 : h 0 = F) (hs : ∀ j, h (Fin.succ j) = g j)
    (L : (Fin (n + 1) → ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ))
    (d : Fin (l + 1) → ℕ) (a : ∀ i, Fin (d i) → (Fin n → ℝ) → ℝ)
    (u : Fin (l + 1) → (Fin (n + 1) → ℝ) → ℝ) (δ : ℝ)
    (hid : ∀ x, ‖x‖ < δ → ∀ i, h i (L x) = u i x * WilkiesDesign.CG.C4a.wpoly (a i) x)
    (hu : ∀ x, ‖x‖ < δ → ∀ i, u i x ≠ 0)
    (hus : ∀ x, ‖x‖ < δ → ∀ i, SignType.sign (u i x) = SignType.sign (u i 0))
    (τ : Fin l → ℝ) (hτ : ∀ j, SignType.sign (τ j) = SignType.sign (u (Fin.succ j) 0)) :
    ∀ x : Fin (n + 1) → ℝ, ‖L.symm x‖ < δ →
      (x ∈ Work.WilC4aCS.YwL L d a τ ↔ x ∈ WilkiesDesign.CG.C4a.BasicSA F g) := by
  intro x hx
  have h := ywl_aux F g h h0 hs L d a u δ hid hu hus τ hτ (L.symm x) hx
  have hx' : L (L.symm x) = x := L.apply_symm_apply x
  rwa [hx'] at h

end Work.WilC4aCS
