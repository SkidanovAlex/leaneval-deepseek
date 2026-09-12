import Mathlib
import Submission.Commons.Analysis.MvPolynomial.homogenization_stable_of_stable_nonneg
import Submission.Commons.Analysis.MvPolynomial.pderiv_stable

noncomputable section

open Finsupp MvPolynomial UpperHalfPlane
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Commons.Analysis.MvPolynomial

/-! # Stability of homogeneous components

We prove (Borcea--Br\"and\'en--Liggett, Lemma 4.16, special case `p = q = k`):
every homogeneous component of a real stable polynomial with nonnegative
coefficients is stable (or zero).

The proof follows BBL: homogenize `p` (add a fresh variable `y`), then apply a
chain of stability preserving operations (partial derivatives in `y`, and the
"reciprocal" operation), which produces a non-zero scalar multiple of the
`k`-th homogeneous component of `p`, embedded by `rename succ`.
-/

/-- Partial derivative with respect to the homogenizing variable (index `0`). -/
abbrev hcs_pd0 {m : ℕ} : MvPolynomial (Fin (m + 1)) ℝ → MvPolynomial (Fin (m + 1)) ℝ :=
  fun q => MvPolynomial.pderiv (R := ℝ) (0 : Fin (m + 1)) q

/-- Falling factorial `∏_{t < r} (e - t)`, as a natural number. -/
def hcs_fallFact (e r : ℕ) : ℕ := ∏ t ∈ Finset.range r, (e - t)

/-- Falling factorial vanishes when `e < r`. -/
lemma hcs_fallFact_eq_zero_of_lt {e r : ℕ} (h : e < r) : hcs_fallFact e r = 0 := by
  unfold hcs_fallFact
  have he : e ∈ Finset.range r := Finset.mem_range.mpr h
  have hzero : (e - e) = 0 := by simp
  rw [← Finset.prod_eq_zero he hzero]

/-- Falling factorial is positive when `r ≤ e`. -/
lemma hcs_fallFact_pos {e r : ℕ} (h : r ≤ e) : 0 < hcs_fallFact e r := by
  classical
  unfold hcs_fallFact
  refine Finset.prod_pos (fun t ht => ?_)
  have htlt : t < r := (Finset.mem_range.mp ht)
  have : t < e := lt_of_lt_of_le htlt h
  omega

lemma hcs_fallFact_self_pos (r : ℕ) : 0 < hcs_fallFact r r := hcs_fallFact_pos (le_rfl)

lemma hcs_pd0_monomial_cons {n : ℕ} (e : ℕ) (m : Fin n →₀ ℕ) (c : ℝ) :
    MvPolynomial.pderiv (R := ℝ) (0 : Fin (n + 1))
      (MvPolynomial.monomial (Finsupp.cons e m) c) =
        MvPolynomial.monomial (Finsupp.cons (e - 1) m) (c * (e : ℝ)) := by
  classical
  rw [MvPolynomial.pderiv_monomial]
  have hExp : Finsupp.cons e m - Finsupp.single (0 : Fin (n + 1)) 1 =
      Finsupp.cons (e - 1) m := by
    apply Finsupp.ext
    intro j
    cases j using Fin.cases with
    | zero => simp [Finsupp.cons_zero]
    | succ i => simp [Finsupp.cons_succ, Finsupp.single_eq_of_ne]
  have hCoef : (Finsupp.cons e m) 0 = e := by simp [Finsupp.cons_zero]
  simp [hExp, hCoef]

/-- `pd0^[r]` distributes over finite sums. -/
lemma hcs_pd0_iterate_sum {α : Type*} (n r : ℕ) (s : Finset α)
    (f : α → MvPolynomial (Fin (n + 1)) ℝ) :
    hcs_pd0^[r] (∑ a ∈ s, f a) = ∑ a ∈ s, hcs_pd0^[r] (f a) := by
  classical
  revert f
  induction r with
  | zero => intro f; simp
  | succ r ih =>
      intro f
      calc
        hcs_pd0^[r + 1] (∑ a ∈ s, f a) = hcs_pd0^[r] (hcs_pd0 (∑ a ∈ s, f a)) := by
          rw [Function.iterate_succ_apply]
        _ = hcs_pd0^[r] (∑ a ∈ s, hcs_pd0 (f a)) := by
              congr 1
              simp [hcs_pd0, map_sum]
        _ = ∑ a ∈ s, hcs_pd0^[r] (hcs_pd0 (f a)) := by
              exact ih (fun a => hcs_pd0 (f a))
        _ = ∑ a ∈ s, hcs_pd0^[r + 1] (f a) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [← Function.iterate_succ_apply]

lemma hcs_pd0_iterate_monomial_cons (n : ℕ) (r : ℕ) : ∀ (e : ℕ) (m : Fin n →₀ ℕ) (c : ℝ),
    hcs_pd0^[r] (MvPolynomial.monomial (Finsupp.cons e m) c) =
      MvPolynomial.monomial (Finsupp.cons (e - r) m) (c * (hcs_fallFact e r : ℝ)) := by
  classical
  induction r with
  | zero =>
      intro e m c
      simp [hcs_fallFact]
  | succ r ih =>
      intro e m c
      rw [Function.iterate_succ_apply]
      change hcs_pd0^[r] (MvPolynomial.pderiv (R := ℝ) (0 : Fin (n + 1))
        (MvPolynomial.monomial (Finsupp.cons e m) c)) = _
      rw [hcs_pd0_monomial_cons]
      rw [ih (e - 1) m (c * (e : ℝ))]
      have hExp : Finsupp.cons ((e - 1) - r) m = Finsupp.cons (e - (r + 1)) m := by
        apply Finsupp.ext
        intro j
        cases j using Fin.cases with
        | zero =>
            change ((e - 1) - r) = (e - (r + 1))
            rw [Nat.sub_sub]
            omega
        | succ i => rfl
      rw [hExp]
      congr 1
      rw [mul_assoc]
      congr 1
      rw [← Nat.cast_mul]
      congr 1
      unfold hcs_fallFact
      have hA : (∏ t ∈ Finset.range r, ((e - 1) - t)) =
          (∏ t ∈ Finset.range r, (e - (t + 1))) := by
        apply Finset.prod_congr rfl
        intro t ht
        rw [Nat.sub_sub]
        omega
      rw [hA]
      calc
        e * (∏ t ∈ Finset.range r, (e - (t + 1))) = (∏ t ∈ Finset.range r, (e - (t + 1))) * e := by
          exact Nat.mul_comm e _
        _ = ∏ t ∈ Finset.range (r + 1), (e - t) := by
            rw [Finset.prod_range_succ']
            simp

/-- Iterated partial derivatives preserve (degenerate) stability. -/
lemma hcs_pderiv_iterate_stable {m : ℕ} (p : MvPolynomial (Fin m) ℝ) (j : Fin m) (r : ℕ)
    (hstab : p = 0 ∨ ∀ z : Fin m → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin m => ((z i : UpperHalfPlane) : ℂ)) p ≠ 0) :
    ((fun q : MvPolynomial (Fin m) ℝ => MvPolynomial.pderiv (R := ℝ) j q)^[r] p) = 0 ∨
      ∀ z : Fin m → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin m => ((z i : UpperHalfPlane) : ℂ))
          ((fun q : MvPolynomial (Fin m) ℝ => MvPolynomial.pderiv (R := ℝ) j q)^[r] p) ≠ 0 := by
  classical
  let f : MvPolynomial (Fin m) ℝ → MvPolynomial (Fin m) ℝ :=
    fun q => MvPolynomial.pderiv (R := ℝ) j q
  change (f^[r] p = 0 ∨ ∀ z : Fin m → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin m => ((z i : UpperHalfPlane) : ℂ)) (f^[r] p) ≠ 0)
  induction r with
  | zero => simpa using hstab
  | succ r ih =>
      rw [Function.iterate_succ']
      change f ((f^[r]) p) = 0 ∨ ∀ z : Fin m → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin m => ((z i : UpperHalfPlane) : ℂ))
          (f ((f^[r]) p)) ≠ 0
      exact pderiv_stable ((f^[r]) p) j (by simpa [f] using ih)

/-- Exponent vector for reciprocal operations: `(a, d, …, d)`. -/
def yxExpo (n : ℕ) (a d : ℕ) : Fin (n + 1) → ℕ :=
  fun j => Fin.cases a (fun _ : Fin n => d) j

/-- The exponent shift map used by `recip`. -/
def hcs_expMap {m : ℕ} (e : Fin m → ℕ) (b : Fin m →₀ ℕ) : Fin m →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun j : Fin m => e j - b j)

@[simp] lemma hcs_expMap_apply {m : ℕ} (e : Fin m → ℕ) (b : Fin m →₀ ℕ) (j : Fin m) :
    hcs_expMap e b j = e j - b j := by
  rfl

/-- Reciprocal of a polynomial with respect to exponent vector `e`: each monomial
`X^b` is sent to `X^(e - b)`. -/
def recip {m : ℕ} (q : MvPolynomial (Fin m) ℝ) (e : Fin m → ℕ) : MvPolynomial (Fin m) ℝ :=
  ∑ b ∈ q.support, MvPolynomial.monomial (hcs_expMap e b) (q.coeff b)

/-- `recip` of a sum distributes over the coefficients at each exponent. -/
lemma hcs_recip_coeff_sum {m : ℕ} (q : MvPolynomial (Fin m) ℝ) (e : Fin m → ℕ) (a : Fin m →₀ ℕ) :
    MvPolynomial.coeff a (recip q e) =
      q.support.sum (fun b : Fin m →₀ ℕ => if a = hcs_expMap e b then q.coeff b else 0) := by
  classical
  unfold recip
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [MvPolynomial.coeff_monomial]
  by_cases h : hcs_expMap e b = a
  · simp [h]
  · have h' : ¬ a = hcs_expMap e b := fun hx => h hx.symm
    simp [h, h']

/-- `recip` is additive. -/
lemma hcs_recip_add {m : ℕ} (p q : MvPolynomial (Fin m) ℝ) (e : Fin m → ℕ) :
    recip (p + q) e = recip p e + recip q e := by
  classical
  apply MvPolynomial.ext
  intro a
  rw [hcs_recip_coeff_sum (p + q) e a]
  rw [MvPolynomial.coeff_add]
  rw [hcs_recip_coeff_sum p e a, hcs_recip_coeff_sum q e a]
  have hsplit : ∀ b : Fin m →₀ ℕ,
      (if a = hcs_expMap e b then (p + q).coeff b else 0)
        = (if a = hcs_expMap e b then p.coeff b else 0)
          + (if a = hcs_expMap e b then q.coeff b else 0) := by
    intro b
    by_cases h : a = hcs_expMap e b
    · simp [h, MvPolynomial.coeff_add]
    · simp [h]
  calc
    (∑ b ∈ (p + q).support, (if a = hcs_expMap e b then (p + q).coeff b else 0))
        = ∑ b ∈ p.support ∪ q.support, (if a = hcs_expMap e b then (p + q).coeff b else 0) := by
          rw [Finset.sum_subset (MvPolynomial.support_add (p := p) (q := q))]
          intro b hb hb'
          have hc0 : (p + q).coeff b = 0 := by
            by_contra hc
            exact hb' (MvPolynomial.mem_support_iff.mpr hc)
          simp [hc0]
    _ = ∑ b ∈ p.support ∪ q.support,
          ((if a = hcs_expMap e b then p.coeff b else 0)
           + (if a = hcs_expMap e b then q.coeff b else 0)) := by
          apply Finset.sum_congr rfl
          intro b hb
          exact hsplit b
    _ = (∑ b ∈ p.support ∪ q.support, (if a = hcs_expMap e b then p.coeff b else 0))
        + (∑ b ∈ p.support ∪ q.support, (if a = hcs_expMap e b then q.coeff b else 0)) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ b ∈ p.support, (if a = hcs_expMap e b then p.coeff b else 0))
        + (∑ b ∈ q.support, (if a = hcs_expMap e b then q.coeff b else 0)) := by
          congr 1
          · rw [Finset.sum_subset (s₁ := p.support) (s₂ := p.support ∪ q.support)
                (Finset.subset_union_left (s₁ := p.support) (s₂ := q.support))
                (fun x hx hx' => by
                  have hp0 : p.coeff x = 0 := by
                    by_contra hc
                    exact hx' (MvPolynomial.mem_support_iff.mpr hc)
                  simp [hp0])]
          · rw [Finset.sum_subset (s₁ := q.support) (s₂ := p.support ∪ q.support)
                (Finset.subset_union_right (s₁ := p.support) (s₂ := q.support))
                (fun x hx hx' => by
                  have hq0 : q.coeff x = 0 := by
                    by_contra hc
                    exact hx' (MvPolynomial.mem_support_iff.mpr hc)
                  simp [hq0])]
/-- `recip` of zero is zero. -/
lemma hcs_recip_zero {m : ℕ} (e : Fin m → ℕ) : recip (0 : MvPolynomial (Fin m) ℝ) e = 0 := by
  unfold recip
  simp

/-- `recip` distributes over finite sums. -/
lemma hcs_recip_sum {m : ℕ} {α : Type*} (s : Finset α)
    (f : α → MvPolynomial (Fin m) ℝ) (e : Fin m → ℕ) :
    recip (∑ a ∈ s, f a) e = ∑ a ∈ s, recip (f a) e := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [hcs_recip_zero]
  · intro a s' has' ih
    rw [Finset.sum_insert has']
    rw [hcs_recip_add, ih]
    rw [Finset.sum_insert has']

/-- `recip` acts on monomials by shifting the exponent. -/
lemma hcs_recip_monomial {m : ℕ} (b : Fin m →₀ ℕ) (c : ℝ) (e : Fin m → ℕ) :
    recip (monomial b c) e = monomial (hcs_expMap e b) c := by
  classical
  by_cases hc : c = 0
  · simp [hc, hcs_recip_zero]
  · unfold recip
    rw [MvPolynomial.support_monomial, if_neg hc]
    simp

-- conj commutes with evaluation of real polynomials
lemma hcs_aeval_conj {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (z : Fin n → ℂ) :
    (starRingEnd ℂ) (MvPolynomial.aeval (R := ℝ) z p) =
      MvPolynomial.aeval (R := ℝ) (fun i => starRingEnd ℂ (z i)) p := by
  rw [MvPolynomial.map_aeval]
  have hcomp : (starRingEnd ℂ).comp (algebraMap ℝ ℂ) = (algebraMap ℝ ℂ) := by
    ext r
    simp [algebraMap, Complex.conj_ofReal]
  rw [hcomp]
  rw [← MvPolynomial.aeval_eq_eval₂Hom]

lemma hcs_UHP_ne_zero (z : ℂ) (hz : 0 < z.im) : z ≠ 0 := by
  intro hz0
  rw [hz0] at hz
  simp at hz

lemma hcs_im_invConj_pos {z : ℂ} (hz : 0 < z.im) : 0 < (((starRingEnd ℂ) z)⁻¹).im := by
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0] at hz
    simp at hz
  have hz1 : (((starRingEnd ℂ) z)⁻¹).im = z.im / z.normSq := by
    rw [← (map_inv₀ (starRingEnd ℂ) z)]
    rw [Complex.conj_im]
    rw [Complex.inv_im]
    ring_nf
  rw [hz1]
  exact div_pos hz (Complex.normSq_pos.mpr hz0)

/-- Evaluating a monomial at complex values factors through the exponent product. -/
lemma hcs_aeval_monomial {n : ℕ} (m : Fin n →₀ ℕ) (c : ℝ) (z : Fin n → ℂ) :
    MvPolynomial.aeval (R := ℝ) z (MvPolynomial.monomial m c) =
      (c : ℂ) * ∏ i : Fin n, (z i) ^ (m i) := by
  classical
  rw [MvPolynomial.aeval_monomial]
  rw [Finsupp.prod_pow]
  simp

/-- Evaluating the reciprocal at invertible points factors out the monomial factor. -/
lemma hcs_aeval_recip {m : ℕ} (q : MvPolynomial (Fin m) ℝ) (e : Fin m → ℕ)
    (hdeg : ∀ b : Fin m →₀ ℕ, b ∈ q.support → ∀ i : Fin m, b i ≤ e i)
    (z : Fin m → ℂ) (hz : ∀ i : Fin m, z i ≠ 0) :
    MvPolynomial.aeval (R := ℝ) z (recip q e) =
      (∏ i : Fin m, z i ^ e i) *
        MvPolynomial.aeval (R := ℝ) (fun i => (z i)⁻¹) q := by
  classical
  unfold recip
  rw [map_sum]
  conv_rhs => rw [← q.support_sum_monomial_coeff]
  rw [map_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [hcs_aeval_monomial, hcs_aeval_monomial]
  have hmain : ∏ i : Fin m, z i ^ (hcs_expMap e b i) =
      (∏ i : Fin m, z i ^ e i) * ∏ i : Fin m, (z i)⁻¹ ^ b i := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hcs_expMap_apply]
    rw [pow_sub₀ (z i) (hz i) (hdeg b hb i)]
    rw [inv_pow]
  rw [hmain]
  ring

/-- The reciprocal of a stable polynomial is stable. -/
lemma hcs_stable_recip {m : ℕ} (q : MvPolynomial (Fin m) ℝ) (e : Fin m → ℕ)
    (hdeg : ∀ b : Fin m →₀ ℕ, b ∈ q.support → ∀ i : Fin m, b i ≤ e i)
    (hstab : q = 0 ∨ ∀ z : Fin m → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin m => ((z i : UpperHalfPlane) : ℂ)) q ≠ 0) :
    recip q e = 0 ∨ ∀ z : Fin m → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin m => ((z i : UpperHalfPlane) : ℂ)) (recip q e) ≠ 0 := by
  classical
  by_cases hq0 : q = 0
  · left
    subst q
    simp [recip]
  · right
    intro z
    let zc : Fin m → ℂ := fun i => ((z i : UpperHalfPlane) : ℂ)
    have hz_ne : ∀ i : Fin m, zc i ≠ 0 := by
      intro i
      exact hcs_UHP_ne_zero (zc i) (z i).coe_im_pos
    have hfac := hcs_aeval_recip q e hdeg zc hz_ne
    rw [hfac]
    have hprod_ne : (∏ i : Fin m, zc i ^ e i) ≠ 0 := by
      exact Finset.prod_ne_zero_iff.mpr (fun i hi => pow_ne_zero _ (hz_ne i))
    let zinvc : Fin m → ℂ := fun i => (zc i)⁻¹
    let zstarc : Fin m → ℂ := fun i => (starRingEnd ℂ) (zinvc i)
    have hzstar_im : ∀ i : Fin m, 0 < (zstarc i).im := by
      intro i
      have hc : (starRingEnd ℂ) ((zc i)⁻¹) = (starRingEnd ℂ (zc i))⁻¹ := by
        exact map_inv₀ (starRingEnd ℂ) (zc i)
      change 0 < ((starRingEnd ℂ) ((zc i)⁻¹)).im
      rw [hc]
      exact hcs_im_invConj_pos (z i).coe_im_pos
    have hstar_val : MvPolynomial.aeval (R := ℝ) zstarc q ≠ 0 := by
      let z' : Fin m → UpperHalfPlane := fun i => ⟨zstarc i, hzstar_im i⟩
      have hz' : MvPolynomial.aeval (R := ℝ) (fun i : Fin m => ((z' i : UpperHalfPlane) : ℂ)) q ≠ 0 :=
        (hstab.resolve_left hq0) z'
      simpa [z', zstarc, zinvc] using hz'
    have h_inv_ne : MvPolynomial.aeval (R := ℝ) zinvc q ≠ 0 := by
      intro hz0
      have hc := hcs_aeval_conj q zinvc
      have hc' : MvPolynomial.aeval (R := ℝ) zstarc q = 0 := by
        rw [← hc]
        simp [zinvc, hz0]
      exact hstar_val hc'
    exact mul_ne_zero hprod_ne h_inv_ne

end Commons.Analysis.MvPolynomial

-- =========================================================
-- The stability chain and the polynomial identity
-- =========================================================

namespace Commons.Analysis.MvPolynomial

/-- First step: `d - k` partial derivatives of the homogenization in `y`. -/
def hcs_P2 (n k d : ℕ) (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin (n + 1)) ℝ :=
  hcs_pd0^[d - k] (homogenization d p)

/-- Second step: reciprocal with exponents `(k, d, …, d)`. -/
def hcs_P3 (n k d : ℕ) (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin (n + 1)) ℝ :=
  recip (hcs_P2 n k d p) (yxExpo n k d)

/-- Third step: `k` partial derivatives of the reciprocal. -/
def hcs_P4 (n k d : ℕ) (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin (n + 1)) ℝ :=
  hcs_pd0^[k] (hcs_P3 n k d p)

/-- Fourth step: reciprocal with exponents `(0, d, …, d)`. -/
def hcs_P5 (n k d : ℕ) (p : MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin (n + 1)) ℝ :=
  recip (hcs_P4 n k d p) (yxExpo n 0 d)

/-- The scalar in the final identity: `(d-k)! · k!` (as falling factorials). -/
def hcs_kappa (a b : ℕ) : ℕ := hcs_fallFact a a * hcs_fallFact b b

/-- Tail (excluding index `0`) of an exponent on `Fin (n+1)`. -/
def hcs_tailExp {n : ℕ} (a : Fin (n + 1) →₀ ℕ) : Fin n →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i : Fin n => a i.succ)

/-- Exponent of the `F3`-monomial attached to `m`. -/
def hcs_gam (n k d : ℕ) (m : Fin n →₀ ℕ) : Fin (n + 1) →₀ ℕ :=
  hcs_expMap (yxExpo n k d) (Finsupp.cons ((d - m.degree) - (d - k)) m)

/-- Exponent of the `F4`-monomial attached to `m`. -/
def hcs_del (n k d : ℕ) (m : Fin n →₀ ℕ) : Fin (n + 1) →₀ ℕ :=
  Finsupp.cons ((hcs_gam n k d m 0) - k) (hcs_tailExp (hcs_gam n k d m))

/-- Expansion of `P2`: after `d-k` `y`-derivatives each monomial keeps the tail and
drops `d-k` from the `y`-exponent. -/
lemma hcs_P2_eq (n k : ℕ) (p : MvPolynomial (Fin n) ℝ) (d : ℕ) :
    hcs_P2 n k d p =
      ∑ m ∈ p.support,
        monomial (Finsupp.cons ((d - m.degree) - (d - k)) m)
          (p.coeff m * (hcs_fallFact (d - m.degree) (d - k) : ℝ)) := by
  classical
  unfold hcs_P2
  rw [homogenization]
  rw [hcs_pd0_iterate_sum (n := n) (r := d - k) (s := p.support)
    (f := fun m : Fin n →₀ ℕ => monomial (Finsupp.cons (d - m.degree) m) (p.coeff m))]
  apply Finset.sum_congr rfl
  intro m hm
  exact hcs_pd0_iterate_monomial_cons n (d - k) (d - m.degree) m (p.coeff m)

/-- Expansion of `P3`: each monomial of the `P2`-expansion gets its exponent shifted. -/
lemma hcs_P3_eq (n k : ℕ) (p : MvPolynomial (Fin n) ℝ) (d : ℕ) :
    hcs_P3 n k d p =
      ∑ m ∈ p.support,
        monomial (hcs_gam n k d m)
          (p.coeff m * (hcs_fallFact (d - m.degree) (d - k) : ℝ)) := by
  classical
  unfold hcs_P3
  rw [hcs_P2_eq]
  rw [hcs_recip_sum (s := p.support)
    (f := fun m : Fin n →₀ ℕ =>
      monomial (Finsupp.cons ((d - m.degree) - (d - k)) m)
        (p.coeff m * (hcs_fallFact (d - m.degree) (d - k) : ℝ)))
    (e := yxExpo n k d)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [hcs_recip_monomial]
  rfl

/-- Any exponent on `Fin (n+1)` is `cons` of its first coordinate and its tail. -/
lemma hcs_cons_tailExp {n : ℕ} (a : Fin (n + 1) →₀ ℕ) :
    a = Finsupp.cons (a 0) (hcs_tailExp a) := by
  apply Finsupp.ext
  intro j
  cases j using Fin.cases with
  | zero => simp [hcs_tailExp]
  | succ i => simp [hcs_tailExp]

/-- Expansion of `P4`: after `k` `y`-derivatives, only the tails of the `P3` exponents
survive, with a falling-factorial coefficient. -/
lemma hcs_P4_eq (n k : ℕ) (p : MvPolynomial (Fin n) ℝ) (d : ℕ) :
    hcs_P4 n k d p =
      ∑ m ∈ p.support,
        monomial (hcs_del n k d m)
          ((p.coeff m * (hcs_fallFact (d - m.degree) (d - k) : ℝ)) *
            (hcs_fallFact (hcs_gam n k d m 0) k : ℝ)) := by
  classical
  unfold hcs_P4
  rw [hcs_P3_eq]
  rw [hcs_pd0_iterate_sum (n := n) (r := k) (s := p.support)
    (f := fun m : Fin n →₀ ℕ => monomial (hcs_gam n k d m)
      (p.coeff m * (hcs_fallFact (d - m.degree) (d - k) : ℝ)))]
  apply Finset.sum_congr rfl
  intro m hm
  rw [hcs_cons_tailExp (hcs_gam n k d m)]
  exact hcs_pd0_iterate_monomial_cons n k (hcs_gam n k d m 0) (hcs_tailExp (hcs_gam n k d m))
    (p.coeff m * (hcs_fallFact (d - m.degree) (d - k) : ℝ))

/-- Expansion of `P5`: `P4`'s monomials get their exponents shifted once more. -/
lemma hcs_P5_eq (n k : ℕ) (p : MvPolynomial (Fin n) ℝ) (d : ℕ) :
    hcs_P5 n k d p =
      ∑ m ∈ p.support,
        monomial (hcs_expMap (yxExpo n 0 d) (hcs_del n k d m))
          ((p.coeff m * (hcs_fallFact (d - m.degree) (d - k) : ℝ)) *
            (hcs_fallFact (hcs_gam n k d m 0) k : ℝ)) := by
  classical
  unfold hcs_P5
  rw [hcs_P4_eq]
  rw [hcs_recip_sum (s := p.support)
    (f := fun m : Fin n →₀ ℕ => monomial (hcs_del n k d m)
      ((p.coeff m * (hcs_fallFact (d - m.degree) (d - k) : ℝ)) *
        (hcs_fallFact (hcs_gam n k d m 0) k : ℝ)))
    (e := yxExpo n 0 d)]
  apply Finset.sum_congr rfl
  intro m hm
  rw [hcs_recip_monomial]

/-- A coordinate of a finitely supported function of naturals is at most its degree. -/
lemma hcs_coord_le_degree {t : Type*} [Fintype t] (a : t →₀ ℕ) (j : t) :
    a j ≤ Finsupp.degree a := by
  classical
  rw [Finsupp.degree_eq_sum]
  exact Finset.single_le_sum (fun i hi => Nat.zero_le (a i)) (Finset.mem_univ j)

/-- First coordinate of `hcs_gam`. -/
lemma hcs_gam_zero (n k d : ℕ) (m : Fin n →₀ ℕ) :
    hcs_gam n k d m 0 = k - ((d - m.degree) - (d - k)) := by
  simp [hcs_gam, yxExpo]

/-- Successor coordinates of `hcs_gam`. -/
lemma hcs_gam_succ (n k d : ℕ) (m : Fin n →₀ ℕ) (i : Fin n) :
    hcs_gam n k d m i.succ = d - m i := by
  simp [hcs_gam, yxExpo]

/-- Successor coordinates of `hcs_del`. -/
lemma hcs_del_succ (n k d : ℕ) (m : Fin n →₀ ℕ) (i : Fin n) :
    hcs_del n k d m i.succ = d - m i := by
  unfold hcs_del
  simp [hcs_gam_succ, hcs_tailExp]

/-- First coordinate of `hcs_del` is `0` when the `y`-exponent of `hcs_gam` is at most `k`. -/
lemma hcs_del_zero (n k d : ℕ) (m : Fin n →₀ ℕ) :
    hcs_del n k d m 0 = 0 := by
  unfold hcs_del
  simp [hcs_gam_zero]

/-- The final `P5`-exponent attached to a monomial of `p` is `cons 0 m`. -/
lemma hcs_P5_exponent_final (n k d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hd : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d) {m : Fin n →₀ ℕ} (hm : m ∈ p.support) :
    hcs_expMap (yxExpo n 0 d) (hcs_del n k d m) = Finsupp.cons 0 m := by
  apply Finsupp.ext
  intro j
  cases j using Fin.cases with
  | zero =>
      simp [hcs_expMap, yxExpo, hcs_del_zero]
  | succ i =>
      have hmi : m i ≤ d := by
        exact le_trans (hcs_coord_le_degree m i) (hd m hm)
      simp [hcs_expMap, yxExpo, hcs_del_succ]
      omega

/-- The `P5`-coefficient attached to a monomial of `p` is `(d-k)!·k! · coeff` when the
degree is `k`, and zero otherwise. -/
lemma hcs_P5_coeff_final (n k d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hd : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d) (hk : k ≤ d) {m : Fin n →₀ ℕ}
    (hm : m ∈ p.support) :
    (p.coeff m * (hcs_fallFact (d - m.degree) (d - k) : ℝ)) *
        (hcs_fallFact (hcs_gam n k d m 0) k : ℝ)
      = if m.degree = k then (hcs_kappa (d - k) k : ℝ) * p.coeff m else 0 := by
  classical
  by_cases h : m.degree = k
  · rw [h]
    have hgam : hcs_gam n k d m 0 = k := by
      rw [hcs_gam_zero, h]
      simp
    rw [hgam]
    unfold hcs_kappa
    simp
    ring
  · have hmle : m.degree ≤ d := hd m hm
    rcases lt_or_gt_of_ne h with hlt | hgt
    · have hgam : hcs_gam n k d m 0 = m.degree := by
        rw [hcs_gam_zero]
        omega
      have hff2 : hcs_fallFact (hcs_gam n k d m 0) k = 0 := by
        rw [hgam]
        exact hcs_fallFact_eq_zero_of_lt hlt
      rw [hff2]
      simp [h]
    · have hff1 : hcs_fallFact (d - m.degree) (d - k) = 0 := by
        apply hcs_fallFact_eq_zero_of_lt
        omega
      rw [hff1]
      simp [h]

/-- `mapDomain succ` embeds a `Fin n`-exponent into `Fin (n+1)`. -/
lemma hcs_mapDomain_succ_cons {n : ℕ} (m : Fin n →₀ ℕ) :
    Finsupp.mapDomain (fun i : Fin n => i.succ) m = Finsupp.cons 0 m := by
  apply Finsupp.ext
  intro j
  cases j using Fin.cases with
  | zero =>
      rw [Finsupp.mapDomain_of_notMem_range m 0]
      · rfl
      · rintro ⟨i, hi⟩
        exact Fin.succ_ne_zero i hi
  | succ i =>
      rw [Finsupp.mapDomain_apply (Fin.succ_injective n)]
      rfl

/-- `rename succ` sends the monomial `m` to the monomial `cons 0 m`. -/
lemma hcs_rename_succ_monomial {n : ℕ} (m : Fin n →₀ ℕ) (c : ℝ) :
    MvPolynomial.rename (fun i : Fin n => i.succ) (monomial m c) = monomial (Finsupp.cons 0 m) c := by
  rw [MvPolynomial.rename_monomial]
  rw [hcs_mapDomain_succ_cons]

/-- Real scalar multiplication distributes into monomial coefficients. -/
lemma hcs_smul_monomial {σ : Type*} (κ c : ℝ) (b : σ →₀ ℕ) :
    κ • monomial b c = monomial b (κ * c) := by
  classical
  ext a
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_monomial, MvPolynomial.coeff_monomial]
  by_cases h : a = b
  · simp [h]
  · simp [h]

/-- The chain closes: `P5` is a non-zero scalar multiple of the renamed `k`-th
homogeneous component of `p`. -/
lemma hcs_P5_eq_homogeneousComponent (n k : ℕ) (p : MvPolynomial (Fin n) ℝ) (d : ℕ)
    (hd : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d) (hk : k ≤ d) :
    hcs_P5 n k d p =
      (hcs_kappa (d - k) k : ℝ) •
        MvPolynomial.rename (fun i : Fin n => i.succ) (MvPolynomial.homogeneousComponent k p) := by
  classical
  rw [hcs_P5_eq]
  trans ∑ m ∈ p.support,
      monomial (Finsupp.cons 0 m)
        (if m.degree = k then (hcs_kappa (d - k) k : ℝ) * p.coeff m else 0)
  · apply Finset.sum_congr rfl
    intro m hm
    rw [hcs_P5_exponent_final n k d p hd hm]
    rw [hcs_P5_coeff_final n k d p hd hk hm]
  · symm
    calc
      (hcs_kappa (d - k) k : ℝ) •
          MvPolynomial.rename (fun i : Fin n => i.succ) (MvPolynomial.homogeneousComponent k p)
          = (hcs_kappa (d - k) k : ℝ) •
              MvPolynomial.rename (fun i : Fin n => i.succ)
                (∑ m ∈ p.support with m.degree = k, monomial m (p.coeff m)) := by
              rw [MvPolynomial.homogeneousComponent_apply]
      _ = (hcs_kappa (d - k) k : ℝ) •
            (∑ m ∈ p.support with m.degree = k,
              monomial (Finsupp.mapDomain (fun i : Fin n => i.succ) m) (p.coeff m)) := by
              rw [map_sum]
              apply congr_arg (fun q : MvPolynomial (Fin (n + 1)) ℝ =>
                (hcs_kappa (d - k) k : ℝ) • q)
              apply Finset.sum_congr rfl
              intro m hm
              rw [MvPolynomial.rename_monomial]
      _ = ∑ m ∈ p.support with m.degree = k,
            (hcs_kappa (d - k) k : ℝ) • monomial (Finsupp.mapDomain (fun i : Fin n => i.succ) m)
              (p.coeff m) := by
              rw [Finset.smul_sum]
      _ = ∑ m ∈ p.support with m.degree = k,
            monomial (Finsupp.cons 0 m) ((hcs_kappa (d - k) k : ℝ) * p.coeff m) := by
              apply Finset.sum_congr rfl
              intro m hm
              rw [hcs_smul_monomial]
              rw [hcs_mapDomain_succ_cons]
      _ = ∑ m ∈ p.support,
            monomial (Finsupp.cons 0 m)
              (if m.degree = k then (hcs_kappa (d - k) k : ℝ) * p.coeff m else 0) := by
              rw [Finset.sum_filter]
              apply Finset.sum_congr rfl
              intro m hm
              by_cases h : m.degree = k <;> simp [h]

/-- Exponents occurring in `recip q e` are bounded pointwise by `e`. -/
lemma hcs_recip_mem_support_le {m : ℕ} (q : MvPolynomial (Fin m) ℝ) (e : Fin m → ℕ)
    (a : Fin m →₀ ℕ) (ha : a ∈ support (recip q e)) : ∀ i : Fin m, a i ≤ e i := by
  classical
  intro i
  by_contra hle
  have hcoeff : MvPolynomial.coeff a (recip q e) = 0 := by
    rw [hcs_recip_coeff_sum]
    apply Finset.sum_eq_zero
    intro b hb
    by_cases h : a = hcs_expMap e b
    · exfalso
      have hbi : a i ≤ e i := by
        have ha_i : a i = e i - b i := by
          rw [h]
          simp
        rw [ha_i]
        exact Nat.sub_le _ _
      omega
    · simp [h]
  exact (MvPolynomial.mem_support_iff.mp ha) hcoeff

/-- Partial derivatives enlarge the support by one unit of `j`. -/
lemma hcs_pderiv_mem_support_add {m : ℕ} (q : MvPolynomial (Fin m) ℝ) (j : Fin m)
    (b : Fin m →₀ ℕ) (hb : b ∈ support (MvPolynomial.pderiv (R := ℝ) j q)) :
    b + Finsupp.single j 1 ∈ support q := by
  classical
  rw [MvPolynomial.mem_support_iff] at hb ⊢
  rw [MvPolynomial.coeff_pderiv] at hb
  intro hz
  apply hb
  rw [hz]
  simp

/-- Iterated partial derivatives enlarge the support by `r` units of `j`. -/
lemma hcs_pderiv_iterate_mem_support {m : ℕ} (j : Fin m) :
    ∀ (r : ℕ) (q : MvPolynomial (Fin m) ℝ) (b : Fin m →₀ ℕ),
      b ∈ support ((fun qq : MvPolynomial (Fin m) ℝ => MvPolynomial.pderiv (R := ℝ) j qq)^[r] q) →
      b + Finsupp.single j r ∈ support q := by
  classical
  let f : MvPolynomial (Fin m) ℝ → MvPolynomial (Fin m) ℝ :=
    fun qq => MvPolynomial.pderiv (R := ℝ) j qq
  change ∀ (r : ℕ) (q : MvPolynomial (Fin m) ℝ) (b : Fin m →₀ ℕ),
      b ∈ support (f^[r] q) → b + Finsupp.single j r ∈ support q
  intro r
  induction r with
  | zero =>
      intro q b hb
      simpa using hb
  | succ r ih =>
      intro q b hb
      rw [Function.iterate_succ_apply] at hb
      have hb1 : b + Finsupp.single j r ∈ support (f q) := ih (f q) b hb
      have hb2 := hcs_pderiv_mem_support_add q j (b + Finsupp.single j r) hb1
      have hrew : (b + Finsupp.single j r) + Finsupp.single j 1 =
          b + Finsupp.single j (r + 1) := by
        rw [add_assoc, ← Finsupp.single_add]
      rwa [hrew] at hb2

/-- Support of `P2` is `y`-bounded by `k` and coordinate-wise bounded by `d`. -/
lemma hcs_P2_mem_support_bound (n k d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hd : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d) {b : Fin (n + 1) →₀ ℕ}
    (hb : b ∈ support (hcs_P2 n k d p)) : b 0 ≤ k ∧ ∀ i : Fin n, b i.succ ≤ d := by
  classical
  have hFh : (homogenization d p).IsHomogeneous d := hom_isHomogeneous p hd
  have hmem : b + Finsupp.single (0 : Fin (n + 1)) (d - k) ∈ support (homogenization d p) :=
    hcs_pderiv_iterate_mem_support (m := n + 1) (0 : Fin (n + 1)) (d - k)
      (homogenization d p) b (by simpa [hcs_P2] using hb)
  have had : Finsupp.degree (b + Finsupp.single (0 : Fin (n + 1)) (d - k)) = d := by
    by_contra h
    exact (MvPolynomial.mem_support_iff.mp hmem)
      (MvPolynomial.IsHomogeneous.coeff_eq_zero hFh h)
  constructor
  · have ha0le : (b + Finsupp.single (0 : Fin (n + 1)) (d - k)) 0 ≤ d := by
      have h := hcs_coord_le_degree (t := Fin (n + 1))
        (b + Finsupp.single (0 : Fin (n + 1)) (d - k)) (0 : Fin (n + 1))
      rwa [had] at h
    have ha0eq : (b + Finsupp.single (0 : Fin (n + 1)) (d - k)) 0 = b 0 + (d - k) := by
      simp
    have hb0 : b 0 ≤ d - (d - k) := by
      omega
    have hlast : d - (d - k) ≤ k := by omega
    exact le_trans hb0 hlast
  · intro i
    have hle : (b + Finsupp.single (0 : Fin (n + 1)) (d - k)) i.succ ≤ d := by
      have h := hcs_coord_le_degree (t := Fin (n + 1))
        (b + Finsupp.single (0 : Fin (n + 1)) (d - k)) i.succ
      rwa [had] at h
    simpa [Finsupp.add_apply] using hle

/-- Support of `P4` is `y`-free and coordinate-wise bounded by `d`. -/
lemma hcs_P4_mem_support_bound (n k d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hd : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d) {c : Fin (n + 1) →₀ ℕ}
    (hc : c ∈ support (hcs_P4 n k d p)) : c 0 ≤ 0 ∧ ∀ i : Fin n, c i.succ ≤ d := by
  classical
  have hmem : c + Finsupp.single (0 : Fin (n + 1)) k ∈ support (hcs_P3 n k d p) :=
    hcs_pderiv_iterate_mem_support (m := n + 1) (0 : Fin (n + 1)) k (hcs_P3 n k d p) c
      (by simpa [hcs_P4] using hc)
  have hle : ∀ i : Fin (n + 1),
      (c + Finsupp.single (0 : Fin (n + 1)) k) i ≤ yxExpo n k d i :=
    hcs_recip_mem_support_le (hcs_P2 n k d p) (yxExpo n k d)
      (c + Finsupp.single (0 : Fin (n + 1)) k) (by simpa [hcs_P3] using hmem)
  constructor
  · have h0 : (c + Finsupp.single (0 : Fin (n + 1)) k) 0 ≤ k := by
      simpa [yxExpo] using hle 0
    have h' : c 0 + k ≤ k := by
      simpa [Finsupp.add_apply] using h0
    omega
  · intro i
    have hi := hle i.succ
    have h2 : c i.succ ≤ yxExpo n k d i.succ := by
      simpa [Finsupp.add_apply] using hi
    simpa [yxExpo] using h2

/-- `P2` exponents satisfy the pointwise bound required for `recip`. -/
lemma hcs_P2_hdeg (n k d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hd : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d) :
    ∀ b : Fin (n + 1) →₀ ℕ, b ∈ support (hcs_P2 n k d p) →
      ∀ i : Fin (n + 1), b i ≤ yxExpo n k d i := by
  intro b hb i
  cases i using Fin.cases with
  | zero =>
      have hb0 := (hcs_P2_mem_support_bound n k d p hd hb).1
      simpa [yxExpo] using hb0
  | succ i =>
      have hbi := (hcs_P2_mem_support_bound n k d p hd hb).2 i
      simpa [yxExpo] using hbi

/-- `P4` exponents satisfy the pointwise bound required for `recip`. -/
lemma hcs_P4_hdeg (n k d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hd : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d) :
    ∀ c : Fin (n + 1) →₀ ℕ, c ∈ support (hcs_P4 n k d p) →
      ∀ i : Fin (n + 1), c i ≤ yxExpo n 0 d i := by
  intro c hc i
  cases i using Fin.cases with
  | zero =>
      have hc0 := (hcs_P4_mem_support_bound n k d p hd hc).1
      simpa [yxExpo] using hc0
  | succ i =>
      have hci := (hcs_P4_mem_support_bound n k d p hd hc).2 i
      simpa [yxExpo] using hci

/-- The chain polynomial `P5` is stable or zero. -/
lemma hcs_P5_stable_or_zero (n k d : ℕ) (p : MvPolynomial (Fin n) ℝ)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m)
    (hd : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d)
    (hstab : p = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) p ≠ 0) :
    hcs_P5 n k d p = 0 ∨ ∀ w : Fin (n + 1) → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin (n + 1) => ((w i : UpperHalfPlane) : ℂ))
          (hcs_P5 n k d p) ≠ 0 := by
  classical
  have hF : homogenization d p = 0 ∨ ∀ w : Fin (n + 1) → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin (n + 1) => ((w i : UpperHalfPlane) : ℂ))
        (homogenization d p) ≠ 0 := by
    simpa [homogenization] using homogenization_stable_of_stable_nonneg n d p hnn hd hstab
  have hP2 : hcs_P2 n k d p = 0 ∨ ∀ w : Fin (n + 1) → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin (n + 1) => ((w i : UpperHalfPlane) : ℂ))
        (hcs_P2 n k d p) ≠ 0 := by
    unfold hcs_P2
    exact hcs_pderiv_iterate_stable (homogenization d p) (0 : Fin (n + 1)) (d - k) hF
  have hP3 : hcs_P3 n k d p = 0 ∨ ∀ w : Fin (n + 1) → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin (n + 1) => ((w i : UpperHalfPlane) : ℂ))
        (hcs_P3 n k d p) ≠ 0 := by
    unfold hcs_P3
    exact hcs_stable_recip (hcs_P2 n k d p) (yxExpo n k d) (hcs_P2_hdeg n k d p hd) hP2
  have hP4 : hcs_P4 n k d p = 0 ∨ ∀ w : Fin (n + 1) → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin (n + 1) => ((w i : UpperHalfPlane) : ℂ))
        (hcs_P4 n k d p) ≠ 0 := by
    unfold hcs_P4
    exact hcs_pderiv_iterate_stable (hcs_P3 n k d p) (0 : Fin (n + 1)) k hP3
  unfold hcs_P5
  exact hcs_stable_recip (hcs_P4 n k d p) (yxExpo n 0 d) (hcs_P4_hdeg n k d p hd) hP4

/-- `κ = (d-k)! · k!` is non-zero. -/
lemma hcs_kappa_ne_zero (a b : ℕ) : (hcs_kappa a b : ℝ) ≠ 0 := by
  have hprod : 0 < ((hcs_fallFact a a * hcs_fallFact b b : ℕ) : ℝ) := by
    exact_mod_cast (mul_pos (hcs_fallFact_self_pos a) (hcs_fallFact_self_pos b))
  exact ne_of_gt hprod

/-- `rename succ` is injective away from zero. -/
lemma hcs_rename_succ_ne_zero {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (hp : p ≠ 0) :
    MvPolynomial.rename (fun i : Fin n => i.succ) p ≠ 0 := by
  intro hz
  apply hp
  exact (MvPolynomial.rename_injective (fun i : Fin n => i.succ) (Fin.succ_injective n))
    (by simpa using hz)

/-- Multiplying a non-zero polynomial by a non-zero real scalar keeps it non-zero. -/
lemma hcs_smul_ne_zero {σ : Type*} (κ : ℝ) (q : MvPolynomial σ ℝ) (hκ : κ ≠ 0) (hq : q ≠ 0) :
    κ • q ≠ 0 := by
  classical
  intro hz
  rcases MvPolynomial.exists_coeff_ne_zero hq with ⟨m, hm⟩
  have h := congr_arg (fun r : MvPolynomial σ ℝ => MvPolynomial.coeff m r) hz
  rw [MvPolynomial.coeff_smul] at h
  rw [smul_eq_mul] at h
  exact (mul_ne_zero hκ hm) h

/-- Theorem (Borcea--Br\"and\'en--Liggett, Lemma 4.16, special case `p = q = k`):
every homogeneous component of a real stable polynomial with nonnegative coefficients
is stable (or zero). -/
theorem homogeneousComponent_stable_of_stable_nonneg_full (n k : ℕ)
    (p : MvPolynomial (Fin n) ℝ)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m)
    (hstab : p = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) p ≠ 0) :
    MvPolynomial.homogeneousComponent k p = 0 ∨
      ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ))
          (MvPolynomial.homogeneousComponent k p) ≠ 0 := by
  classical
  by_cases hp0 : p = 0
  · left
    subst p
    simp
  · let d : ℕ := p.totalDegree
    let Ek : MvPolynomial (Fin n) ℝ := MvPolynomial.homogeneousComponent k p
    by_cases hEk : Ek = 0
    · left
      exact hEk
    · right
      have hkd : k ≤ d := by
        by_contra h
        have hlt : d < k := Nat.lt_of_not_ge h
        have hz : MvPolynomial.homogeneousComponent k p = 0 :=
          MvPolynomial.homogeneousComponent_eq_zero k p hlt
        exact hEk hz
      have hd : ∀ m : Fin n →₀ ℕ, m ∈ p.support → m.degree ≤ d := by
        intro m hm
        dsimp [d]
        exact MvPolynomial.le_totalDegree (p := p) (s := m) hm
      let κR : ℝ := (hcs_kappa (d - k) k : ℝ)
      have hκ : κR ≠ 0 := by
        dsimp [κR]
        exact hcs_kappa_ne_zero (d - k) k
      have hP5nz : hcs_P5 n k d p ≠ 0 := by
        intro hz
        have hid := hcs_P5_eq_homogeneousComponent n k p d hd hkd
        rw [hid] at hz
        have hren : MvPolynomial.rename (fun i : Fin n => i.succ)
            (MvPolynomial.homogeneousComponent k p) ≠ 0 := by
          exact hcs_rename_succ_ne_zero (MvPolynomial.homogeneousComponent k p) hEk
        exact hcs_smul_ne_zero κR (MvPolynomial.rename (fun i : Fin n => i.succ)
          (MvPolynomial.homogeneousComponent k p)) hκ hren hz
      have hP5nv : ∀ w : Fin (n + 1) → UpperHalfPlane,
          MvPolynomial.aeval (R := ℝ) (fun i : Fin (n + 1) => ((w i : UpperHalfPlane) : ℂ))
            (hcs_P5 n k d p) ≠ 0 :=
        (hcs_P5_stable_or_zero n k d p hnn hd hstab).resolve_left hP5nz
      intro z
      let w : Fin (n + 1) → UpperHalfPlane := Fin.cons UpperHalfPlane.I z
      have hw : MvPolynomial.aeval (R := ℝ)
          (fun i : Fin (n + 1) => ((w i : UpperHalfPlane) : ℂ)) (hcs_P5 n k d p) ≠ 0 := hP5nv w
      have hmain : MvPolynomial.aeval (R := ℝ)
          (fun i : Fin (n + 1) => ((w i : UpperHalfPlane) : ℂ)) (hcs_P5 n k d p)
          = κR • MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) Ek := by
        calc
          MvPolynomial.aeval (R := ℝ) (fun i : Fin (n + 1) => ((w i : UpperHalfPlane) : ℂ))
              (hcs_P5 n k d p)
              = MvPolynomial.aeval (R := ℝ) (fun i : Fin (n + 1) => ((w i : UpperHalfPlane) : ℂ))
                  (κR • MvPolynomial.rename (fun i : Fin n => i.succ) Ek) := by
                  rw [hcs_P5_eq_homogeneousComponent n k p d hd hkd]
          _ = κR • MvPolynomial.aeval (R := ℝ) (fun i : Fin (n + 1) => ((w i : UpperHalfPlane) : ℂ))
                  (MvPolynomial.rename (fun i : Fin n => i.succ) Ek) := by
                  rw [map_smul]
          _ = κR • MvPolynomial.aeval (R := ℝ)
                  (fun i : Fin n => ((w (i.succ) : UpperHalfPlane) : ℂ)) Ek := by
                  rw [MvPolynomial.aeval_rename]
                  rfl
          _ = κR • MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) Ek := by
                  rfl
      intro hz0
      have hz0' : MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) Ek = 0 := by
        simpa [Ek] using hz0
      have hbad : MvPolynomial.aeval (R := ℝ)
          (fun i : Fin (n + 1) => ((w i : UpperHalfPlane) : ℂ)) (hcs_P5 n k d p) = 0 := by
        rw [hmain]
        simp [hz0']
      exact hw hbad
