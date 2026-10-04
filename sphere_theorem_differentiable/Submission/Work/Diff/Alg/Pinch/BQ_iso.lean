import Mathlib
import Submission.Work.Diff.Alg.Pinch.BQDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The polarization `BQ R (Iso n) = Ric(R) ∧ id`

For an algebraic curvature tensor `R` the polarization of Hamilton's quadratic term against the
round-sphere tensor `Iso n` (the identity of `Λ²`, `Iso n i j k l = δᵢₖ δⱼₗ − δᵢₗ δⱼₖ`) is the
Kulkarni–Nomizu product of the Ricci tensor with the metric:

`BQ R (Iso n) = knProd (ric R) (id2 n)`, componentwise
`(BQ R Iso)ᵢⱼₖₗ = Ricᵢₖ δⱼₗ − Ricᵢₗ δⱼₖ − Ricⱼₖ δᵢₗ + Ricⱼₗ δᵢₖ`.

This is the first-order term in the linearization of Hamilton's ODE `R' = Q(R)` about the round
sphere: `Q (R + t • Iso n) = Q R + 2 t • BQ R Iso + t² Q Iso`, and it identifies the (Ricci) part
of `R` that survives the linearization. It is used in the pinching-set construction to see that
the linearized flow is the Ricci flow of the `(0,2)`-tensor.

The proof is a purely algebraic index computation.  Expanding `BQ` gives the six double sums

* `∑_{p q} Rᵢⱼₚq (Iso n)ₖₗₚq = 2 Rᵢⱼₖₗ`, `∑_{p q} (Iso n)ᵢⱼₚq Rₖₗₚq = 2 Rᵢⱼₖₗ` (the pair contractions),
* `∑_{p q} Rᵢₚₖq (Iso n)ⱼₚₗq = δⱼₗ (∑ₚ Rᵢₚₖₚ) − Rᵢₗₖⱼ` and its three siblings (the mixed
  contractions),

and the whole identity reduces to two facts valid for algebraic curvature tensors: the "diagonal"
identity `∑ₚ Rᵢₚₖₚ = Ricᵢₖ` (a consequence of the Bianchi identity) and the index identity
`2 Rᵢⱼₖₗ − Rᵢₗₖⱼ − Rⱼₖₗᵢ + Rᵢₖₗⱼ + Rⱼₗₖᵢ = 0` (Bianchi together with the pair symmetries).
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-! ## Kronecker-delta contractions against `Iso` -/

/-- Contraction of `Iso` against an arbitrary array `X` in the last two slots:
`∑_{p q} X p q · (Iso n) a b p q = X a b − X b a`. -/
lemma Iso_contract_pair (X : Fin n → Fin n → ℝ) (a b : Fin n) :
    (∑ p, ∑ q, X p q * Iso n a b p q) = X a b - X b a := by
  have hpt : ∀ p q, X p q * Iso n a b p q
      = X p q * (if a = p then (1:ℝ) else 0) * (if b = q then (1:ℝ) else 0)
        - X p q * (if a = q then (1:ℝ) else 0) * (if b = p then (1:ℝ) else 0) := by
    intro p q; simp only [Iso]; ring
  simp only [hpt, Finset.sum_sub_distrib]
  congr 1
  · have h1 : ∀ p, (∑ q, X p q * (if a = p then (1:ℝ) else 0) * (if b = q then (1:ℝ) else 0))
        = (if a = p then (1:ℝ) else 0) * X p b := by
      intro p
      rw [show (∑ q, X p q * (if a = p then (1:ℝ) else 0) * (if b = q then (1:ℝ) else 0))
          = (if a = p then (1:ℝ) else 0) * (∑ q, X p q * (if b = q then (1:ℝ) else 0)) from by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
      rw [show (∑ q, X p q * (if b = q then (1:ℝ) else 0)) = X p b from by
        rw [Finset.sum_eq_single b]
        · simp
        · intro q _ hq; rw [ite_eq_right (show ¬ (b = q) from fun h => hq h.symm), mul_zero]
        · intro hb; exact absurd (Finset.mem_univ b) hb]
    simp only [h1]
    rw [show (∑ p, (if a = p then (1:ℝ) else 0) * X p b) = X a b from by
      rw [Finset.sum_eq_single a]
      · simp
      · intro p _ hp; rw [ite_eq_right (show ¬ (a = p) from Ne.symm hp), zero_mul]
      · intro ha; exact absurd (Finset.mem_univ a) ha]
  · have h1 : ∀ p, (∑ q, X p q * (if a = q then (1:ℝ) else 0) * (if b = p then (1:ℝ) else 0))
        = (if b = p then (1:ℝ) else 0) * X p a := by
      intro p
      rw [show (∑ q, X p q * (if a = q then (1:ℝ) else 0) * (if b = p then (1:ℝ) else 0))
          = (if b = p then (1:ℝ) else 0) * (∑ q, X p q * (if a = q then (1:ℝ) else 0)) from by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
      rw [show (∑ q, X p q * (if a = q then (1:ℝ) else 0)) = X p a from by
        rw [Finset.sum_eq_single a]
        · simp
        · intro q _ hq; rw [ite_eq_right (show ¬ (a = q) from Ne.symm hq), mul_zero]
        · intro ha; exact absurd (Finset.mem_univ a) ha]
    simp only [h1]
    rw [show (∑ p, (if b = p then (1:ℝ) else 0) * X p a) = X b a from by
      rw [Finset.sum_eq_single b]
      · simp
      · intro p _ hp; rw [ite_eq_right (show ¬ (b = p) from Ne.symm hp), zero_mul]
      · intro hb; exact absurd (Finset.mem_univ b) hb]

/-- Contraction of `Iso` against an arbitrary array `X`, with the factors swapped. -/
lemma Iso_contract_pair' (X : Fin n → Fin n → ℝ) (a b : Fin n) :
    (∑ p, ∑ q, Iso n a b p q * X p q) = X a b - X b a := by
  rw [show (∑ p, ∑ q, Iso n a b p q * X p q) = ∑ p, ∑ q, X p q * Iso n a b p q from
    Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => mul_comm _ _))]
  exact Iso_contract_pair X a b

/-- Mixed contraction of `Iso` against an arbitrary array `X` (the adjacency pattern
`(Iso n) a p b q`): `∑_{p q} X p q · (Iso n) a p b q = δ_{ab} (∑ₚ X p p) − X b a`. -/
lemma Iso_contract_mixed (X : Fin n → Fin n → ℝ) (a b : Fin n) :
    (∑ p, ∑ q, X p q * Iso n a p b q) = id2 n a b * (∑ p, X p p) - X b a := by
  have hpt : ∀ p q, X p q * Iso n a p b q
      = id2 n a b * (X p q * (if p = q then (1:ℝ) else 0))
        - X p q * (if a = q then (1:ℝ) else 0) * (if p = b then (1:ℝ) else 0) := by
    intro p q; simp only [Iso, id2]; ring
  have hdiag : ∀ p, (∑ q, X p q * (if p = q then (1:ℝ) else 0)) = X p p := by
    intro p
    rw [Finset.sum_eq_single p]
    · simp
    · intro q _ hq; rw [ite_eq_right (show ¬(p=q) from Ne.symm hq), mul_zero]
    · intro hp; exact absurd (Finset.mem_univ p) hp
  simp only [hpt, Finset.sum_sub_distrib]
  congr 1
  · rw [show (∑ p, ∑ q, id2 n a b * (X p q * (if p = q then (1:ℝ) else 0)))
        = id2 n a b * (∑ p, ∑ q, X p q * (if p = q then (1:ℝ) else 0)) from by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro p _
      rw [Finset.mul_sum]]
    simp only [hdiag]
  · have h1 : ∀ p, (∑ q, X p q * (if a = q then (1:ℝ) else 0) * (if p = b then (1:ℝ) else 0))
        = (if p = b then (1:ℝ) else 0) * X p a := by
      intro p
      rw [show (∑ q, X p q * (if a = q then (1:ℝ) else 0) * (if p = b then (1:ℝ) else 0))
          = (if p = b then (1:ℝ) else 0) * (∑ q, X p q * (if a = q then (1:ℝ) else 0)) from by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro q _; ring]
      rw [show (∑ q, X p q * (if a = q then (1:ℝ) else 0)) = X p a from by
        rw [Finset.sum_eq_single a]
        · simp
        · intro q _ hq; rw [ite_eq_right (show ¬ (a = q) from Ne.symm hq), mul_zero]
        · intro ha; exact absurd (Finset.mem_univ a) ha]
    simp only [h1]
    rw [show (∑ p, (if p = b then (1:ℝ) else 0) * X p a) = X b a from by
      rw [Finset.sum_eq_single b]
      · simp
      · intro p _ hp; rw [ite_eq_right (show ¬ (p = b) from hp), zero_mul]
      · intro hb; exact absurd (Finset.mem_univ b) hb]

/-- Mixed contraction of `Iso`, with the factors swapped. -/
lemma Iso_contract_mixed' (X : Fin n → Fin n → ℝ) (a b : Fin n) :
    (∑ p, ∑ q, Iso n a p b q * X p q) = id2 n a b * (∑ p, X p p) - X b a := by
  rw [show (∑ p, ∑ q, Iso n a p b q * X p q) = ∑ p, ∑ q, X p q * Iso n a p b q from
    Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => mul_comm _ _))]
  exact Iso_contract_mixed X a b

/-- The diagonal contraction of `Iso` against `Iso`. -/
lemma sum6_diag {A B C D E F : Fin n → Fin n → ℝ} :
    (∑ p, ∑ q, (A p q + B p q + 2 * C p q + 2 * D p q - 2 * E p q - 2 * F p q))
      = (∑ p, ∑ q, A p q) + (∑ p, ∑ q, B p q) + 2 * (∑ p, ∑ q, C p q)
        + 2 * (∑ p, ∑ q, D p q) - 2 * (∑ p, ∑ q, E p q) - 2 * (∑ p, ∑ q, F p q) := by
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-! ## The Ricci diagonal of an algebraic curvature tensor -/

/-- For an algebraic curvature tensor `R`, `∑ₚ R a p b p = Ric a b`. -/
lemma sum_self_eq_ric {R : Curv4 n} (hR : IsAlgCurv R) (a b : Fin n) :
    (∑ p, R a p b p) = ric R a b := by
  obtain ⟨hanti, hpair, hbian⟩ := hR
  have hanti2 : ∀ i j k l : Fin n, R i j k l = - R i j l k := by
    intro i j k l
    have h1 : R i j k l = R k l i j := (hpair i j k l).symm
    have h2 : R i j l k = R l k i j := (hpair i j l k).symm
    have h3 : R l k i j = - R k l i j := hanti k l i j
    linarith
  have hpt : ∀ p, R a p b p = R p a p b := by
    intro p
    have h1 := hbian p a p b
    have h2 : R a p p b = - R a p b p := hanti2 a p p b
    have h3 : R p p a b = 0 := by have := hanti p p a b; linarith
    linarith
  rw [show (∑ p, R a p b p) = ∑ p, R p a p b from Finset.sum_congr rfl (fun p _ => hpt p)]
  rfl

/-! ## The main identity -/

theorem BQ_iso (n : ℕ) {R : Submission.Diff.Alg.Curv4 n} (hR : Submission.Diff.Alg.IsAlgCurv R) :
    Work.Diff.Alg.Pinch.BQ R (Submission.Diff.Alg.Iso n)
      = Work.Diff.Alg.Pinch.knProd (Work.Diff.Alg.Pinch.ric R) (Work.Diff.Alg.Pinch.id2 n) := by
  obtain ⟨hanti, hpair, hbian⟩ := hR
  have hanti2 : ∀ a b c d : Fin n, R a b c d = - R a b d c := by
    intro a b c d
    have h1 : R a b c d = R c d a b := (hpair a b c d).symm
    have h2 : R a b d c = R d c a b := (hpair a b d c).symm
    have h3 : R d c a b = - R c d a b := hanti c d a b
    linarith
  have hself : ∀ a b : Fin n, (∑ p, R a p b p) = ric R a b :=
    fun a b => sum_self_eq_ric ⟨hanti, hpair, hbian⟩ a b
  funext i j k l
  rw [BQ_apply]
  have hA := Iso_contract_pair (n := n) (X := fun p q => R i j p q) (a := k) (b := l)
  have hB := Iso_contract_pair' (n := n) (X := fun p q => R k l p q) (a := i) (b := j)
  have hC := Iso_contract_mixed (n := n) (X := fun p q => R i p k q) (a := j) (b := l)
  have hD := Iso_contract_mixed' (n := n) (X := fun p q => R j p l q) (a := i) (b := k)
  have hE := Iso_contract_mixed (n := n) (X := fun p q => R i p l q) (a := j) (b := k)
  have hF := Iso_contract_mixed' (n := n) (X := fun p q => R j p k q) (a := i) (b := l)
  have hA2 : (∑ p, ∑ q, R i j p q * Iso n k l p q) = 2 * R i j k l := by
    rw [hA]; linarith [hanti2 i j k l]
  have hB2 : (∑ p, ∑ q, Iso n i j p q * R k l p q) = 2 * R i j k l := by
    rw [hB]; linarith [hpair i j k l, hanti2 k l i j, hanti2 k l j i]
  have hC2 : (∑ p, ∑ q, R i p k q * Iso n j p l q) = id2 n j l * ric R i k - R i l k j := by
    rw [hC, hself i k]
  have hD2 : (∑ p, ∑ q, Iso n i p k q * R j p l q) = id2 n i k * ric R j l - R j k l i := by
    rw [hD, hself j l]
  have hE2 : (∑ p, ∑ q, R i p l q * Iso n j p k q) = id2 n j k * ric R i l - R i k l j := by
    rw [hE, hself i l]
  have hF2 : (∑ p, ∑ q, Iso n i p l q * R j p k q) = id2 n i l * ric R j k - R j l k i := by
    rw [hF, hself j k]
  have hcancel : 2 * R i j k l - R i l k j - R j k l i + R i k l j + R j l k i = 0 := by
    have e1 : R i l k j = R j k l i := by
      have b1 := hbian i l k j
      have b2 := hbian j k l i
      have a1 : R k l i j = R i j k l := hpair i j k l
      have a2 : R l k i j = - R i j k l := by rw [hanti k l i j, hpair i j k l]
      have a3 : R k l j i = - R i j k l := by rw [hanti2 k l j i, hpair i j k l]
      have a4 : R l j k i = R k i l j := (hpair l j k i).symm
      linarith
    have e2 : R i k l j = R j l k i := by
      have b1 := hbian i k l j
      have b2 := hbian j l k i
      have a1 : R k l i j = R i j k l := hpair i j k l
      have a2 : R l k j i = R i j k l := by
        rw [hanti k l j i, hanti2 k l j i, hpair i j k l]; ring
      have a3 : R l i k j = R k j l i := (hpair l i k j).symm
      linarith
    have e3 : R i k l j = R j k l i - R i j k l := by
      have b1 := hbian i k l j
      have a1 : R k l i j = R i j k l := hpair i j k l
      have a2 : R l i k j = - R j k l i := by rw [hanti i l k j, e1]
      linarith
    linarith
  have key : 2 * (∑ p, ∑ q, ( (R i j p q * Iso n k l p q + Iso n i j p q * R k l p q) / 2
        + (R i p k q * Iso n j p l q + Iso n i p k q * R j p l q)
        - (R i p l q * Iso n j p k q + Iso n i p l q * R j p k q) ))
      = 2 * knProd (ric R) (id2 n) i j k l := by
    rw [show 2 * (∑ p, ∑ q, ( (R i j p q * Iso n k l p q + Iso n i j p q * R k l p q) / 2
          + (R i p k q * Iso n j p l q + Iso n i p k q * R j p l q)
          - (R i p l q * Iso n j p k q + Iso n i p l q * R j p k q) ))
        = ∑ p, ∑ q, 2 * ( (R i j p q * Iso n k l p q + Iso n i j p q * R k l p q) / 2
          + (R i p k q * Iso n j p l q + Iso n i p k q * R j p l q)
          - (R i p l q * Iso n j p k q + Iso n i p l q * R j p k q) ) from by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro p _
        rw [Finset.mul_sum]]
    rw [show (∑ p, ∑ q, 2 * ( (R i j p q * Iso n k l p q + Iso n i j p q * R k l p q) / 2
          + (R i p k q * Iso n j p l q + Iso n i p k q * R j p l q)
          - (R i p l q * Iso n j p k q + Iso n i p l q * R j p k q) ))
        = ∑ p, ∑ q, (R i j p q * Iso n k l p q + Iso n i j p q * R k l p q
          + 2 * (R i p k q * Iso n j p l q) + 2 * (Iso n i p k q * R j p l q)
          - 2 * (R i p l q * Iso n j p k q) - 2 * (Iso n i p l q * R j p k q)) from
      Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => by ring))]
    rw [sum6_diag (A := fun p q => R i j p q * Iso n k l p q)
             (B := fun p q => Iso n i j p q * R k l p q)
             (C := fun p q => R i p k q * Iso n j p l q)
             (D := fun p q => Iso n i p k q * R j p l q)
             (E := fun p q => R i p l q * Iso n j p k q)
             (F := fun p q => Iso n i p l q * R j p k q)]
    rw [hA2, hB2, hC2, hD2, hE2, hF2, knProd]
    linarith
  linarith

end Work.Diff.Alg.Pinch
