import Mathlib
import Submission.Work.Diff.Alg.Pinch.RicFormDefs
import Submission.Work.Diff.Alg.Pinch.bmat_knProd_id2
import Submission.Work.Diff.Alg.Pinch.bmat_knProd_id2_id2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Expansion of the `Ric`–`bmat` pairing of `ℓ_{a,1/2}(S)`

For an algebraic curvature tensor `S`, a vector `v` and the Böhm–Wilking transform at `b = 1/2`,

`Y = ℓ_{a,1/2}(S) = S + (1/2)·(Ric₀ S ∧ id) + (a/n·scal S)·(id ∧ id)`,

this file computes the pairing

`W(Y) = ∑ᵢⱼ ric(Y)ᵢⱼ · bmat(v,Y)ᵢⱼ`

in terms of the corresponding data of `S`.  Here `bmat v R p q = ∑ᵢⱼ vᵢvⱼR i p j q`
(`Work.Diff.Alg.Pinch.bmat`) is the `(v,v)`-contraction of `R`, and the identity used
throughout is

`bmat v (A ∧ id) p q = (∑ᵢⱼ vᵢAᵢⱼvⱼ)·δₚq − v_p·(∑ⱼ A_qj v_j) − v_q·(∑ⱼ A_pj v_j) + |v|²·A_pq`

(`Work.Diff.Alg.Pinch.bmat_knProd_id2`) together with its `id ∧ id` analogue
(`Work.Diff.Alg.Pinch.bmat_knProd_id2_id2`).  Because both `ric(Y)` and `bmat(v,Y)` are affine in
`S` (linear plus a multiple of the identity), the whole pairing expands into six Frobenius pairings
of `(0,2)`-tensors, each of which is evaluated by an elementary double-sum computation using the
symmetry and trace-freeness of `Ric₀ S`.

The result is the algebraic identity needed for the Böhm–Wilking one-step estimate: with
`Λ = scal S / n`, `σ = |Ric₀ S|²/n`, `q = |v|²`, `τ = tr(bmat v S)` and `U = ∑ᵢ vᵢ(Ric₀ S · v)ᵢ`,

`W(ℓ_{a,1/2} S) = (1 + (n-2)/2)·(W₀ − |Ric₀ S·v|² + (n/2)·q·σ − 2aΛ·U)
                + Λ(1 + 2(n-1)a)·(τ + (n-2)/2·U + 2a(n-1)Λ·q)`,

where `W₀ = ∑ᵢⱼ (Ric₀ S)ᵢⱼ · bmat(v,S)ᵢⱼ`.
-/

namespace Work.Diff.Alg.Pinch

open Finset Submission.Diff.Alg

variable {n : ℕ}

/-- The Frobenius pairing `∑ᵢⱼ Mᵢⱼ Nᵢⱼ` of two `(0,2)`-tensors. -/
noncomputable def frobPair (M N : Fin n → Fin n → ℝ) : ℝ := ∑ i, ∑ j, M i j * N i j

private lemma frobPair_add_left (M M' N : Fin n → Fin n → ℝ) :
    frobPair (M + M') N = frobPair M N + frobPair M' N := by
  simp only [frobPair, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma frobPair_add_right (M N N' : Fin n → Fin n → ℝ) :
    frobPair M (N + N') = frobPair M N + frobPair M N' := by
  simp only [frobPair, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private lemma frobPair_smul_left (c : ℝ) (M N : Fin n → Fin n → ℝ) :
    frobPair (c • M) N = c * frobPair M N := by
  simp only [frobPair, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  ring

private lemma frobPair_smul_right (c : ℝ) (M N : Fin n → Fin n → ℝ) :
    frobPair M (c • N) = c * frobPair M N := by
  simp only [frobPair, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  ring

/-- Pairing against the Kronecker delta picks out the diagonal. -/
private lemma frobPair_delta_left (B : Fin n → Fin n → ℝ) :
    frobPair (fun i j : Fin n => (if i = j then (1:ℝ) else 0)) B = ∑ p, B p p := by
  simp only [frobPair]
  apply Finset.sum_congr rfl; intro p _
  rw [Finset.sum_eq_single p]
  · simp
  · intro q _ hq; rw [if_neg (fun h : p = q => hq h.symm)]; ring
  · intro h; exact absurd (Finset.mem_univ p) h

/-! ## Elementary double-sum manipulations -/

/-- `∑ᵢⱼ vᵢAᵢⱼvⱼ = ∑ᵢ vᵢ(∑ⱼ Aᵢⱼvⱼ)`. -/
private lemma sum_vA_v (A : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    (∑ i, ∑ j, v i * A i j * v j) = ∑ i, v i * (∑ j, A i j * v j) := by
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  ring

/-- `∑ₚ∑q Aₚq vₚ(∑ⱼA_qjvⱼ) = ∑ₚ (Av)ₚ²` for symmetric `A`. -/
private lemma sum_symm_vec_quad {A : Fin n → Fin n → ℝ} (hA : ∀ i j, A i j = A j i)
    (v : Fin n → ℝ) :
    (∑ p, ∑ q, A p q * (v p * (∑ j, A q j * v j)))
      = ∑ p, (∑ j, A p j * v j) * (∑ j, A p j * v j) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro q _
  have h1 : (∑ p : Fin n, A p q * (v p * (∑ j, A q j * v j)))
      = (∑ p, A p q * v p) * (∑ j, A q j * v j) := by
    rw [Finset.sum_congr rfl (fun p _ => by ring : ∀ p ∈ (Finset.univ : Finset (Fin n)),
      A p q * (v p * (∑ j, A q j * v j)) = (A p q * v p) * (∑ j, A q j * v j))]
    exact (Finset.sum_mul Finset.univ (fun p => A p q * v p) _).symm
  rw [h1]
  have h2 : (∑ p, A p q * v p) = ∑ j, A q j * v j := by
    apply Finset.sum_congr rfl; intro p _
    rw [hA p q]
  rw [h2]

/-- `∑ₚ∑q Aₚq vₚv_q = ∑ₚ vₚ(∑ⱼAₚⱼvⱼ)`. -/
private lemma sum_symm_vv (A : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    (∑ p, ∑ q, A p q * (v p * v q)) = ∑ p, v p * (∑ j, A p j * v j) := by
  apply Finset.sum_congr rfl; intro p _
  have h1 : (∑ q, A p q * (v p * v q)) = v p * (∑ q, A p q * v q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _; ring
  rw [h1]

/-! ## Pairing against `bmat v (A ∧ id)` and `bmat v (id ∧ id)` -/

/-- Frobenius pairing of an arbitrary `(0,2)`-tensor `M` against `bmat v (A ∧ id)`:
`(vAv)·tr M − 2 ∑ₚ∑q Mₚq vₚ(Av)_q + |v|²·⟨M,A⟩` for symmetric `A` and `M`. -/
private lemma sum_bmat_knProd_id2 (n : ℕ) {A M : Fin n → Fin n → ℝ}
    (hA : ∀ i j, A i j = A j i) (hM : ∀ i j, M i j = M j i) (v : Fin n → ℝ) :
    (∑ p, ∑ q, M p q * bmat v (knProd A (id2 n)) p q)
      = (∑ i, ∑ j, v i * A i j * v j) * (∑ p, M p p)
        - 2 * (∑ p, ∑ q, M p q * (v p * (∑ j, A q j * v j)))
        + (∑ i, v i * v i) * (∑ p, ∑ q, M p q * A p q) := by
  have hpt : ∀ p q, M p q * bmat v (knProd A (id2 n)) p q
      = M p q * ((∑ i, ∑ j, v i * A i j * v j) * (if p = q then (1:ℝ) else 0))
        - M p q * (v p * (∑ j, A q j * v j))
        - M p q * (v q * (∑ j, A p j * v j))
        + M p q * ((∑ i, v i * v i) * A p q) := by
    intro p q
    rw [bmat_knProd_id2 n hA v p q]
    ring
  have hS1 : (∑ p, ∑ q, M p q * ((∑ i, ∑ j, v i * A i j * v j) * (if p = q then (1:ℝ) else 0)))
      = (∑ p, M p p) * (∑ i, ∑ j, v i * A i j * v j) := by
    have hinner : ∀ p, (∑ q, M p q * ((∑ i, ∑ j, v i * A i j * v j) * (if p = q then (1:ℝ) else 0)))
        = M p p * (∑ i, ∑ j, v i * A i j * v j) := by
      intro p
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hq; rw [if_neg (fun h : p = q => hq h.symm)]; ring
      · intro h; exact absurd (Finset.mem_univ p) h
    rw [Finset.sum_congr rfl (fun p _ => hinner p)]
    exact (Finset.sum_mul Finset.univ (fun p => M p p) _).symm
  have hS3 : (∑ p, ∑ q, M p q * (v q * (∑ j, A p j * v j)))
      = (∑ p, ∑ q, M p q * (v p * (∑ j, A q j * v j))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro a _
    apply Finset.sum_congr rfl; intro b _
    rw [hM b a]
  have hS4 : (∑ p, ∑ q, M p q * ((∑ i, v i * v i) * A p q))
      = (∑ i, v i * v i) * (∑ p, ∑ q, M p q * A p q) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _
    ring
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hpt p q))]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hS1, hS3, hS4]
  ring

/-- Frobenius pairing of an arbitrary `(0,2)`-tensor `M` against `bmat v (id ∧ id)`. -/
private lemma sum_bmat_knProd_id2_id2 (n : ℕ) (M : Fin n → Fin n → ℝ) (v : Fin n → ℝ) :
    (∑ p, ∑ q, M p q * bmat v (knProd (id2 n) (id2 n)) p q)
      = 2 * (∑ i, v i * v i) * (∑ p, M p p) - 2 * (∑ p, ∑ q, M p q * (v p * v q)) := by
  have hpt : ∀ p q, M p q * bmat v (knProd (id2 n) (id2 n)) p q
      = M p q * (2 * (∑ i, v i * v i) * (if p = q then (1:ℝ) else 0))
        - M p q * (2 * (v p * v q)) := by
    intro p q
    rw [bmat_knProd_id2_id2 n v p q]
    ring
  have hS1 : (∑ p, ∑ q, M p q * (2 * (∑ i, v i * v i) * (if p = q then (1:ℝ) else 0)))
      = 2 * (∑ i, v i * v i) * (∑ p, M p p) := by
    have hinner : ∀ p, (∑ q, M p q * (2 * (∑ i, v i * v i) * (if p = q then (1:ℝ) else 0)))
        = M p p * (2 * (∑ i, v i * v i)) := by
      intro p
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _ hq; rw [if_neg (fun h : p = q => hq h.symm)]; ring
      · intro h; exact absurd (Finset.mem_univ p) h
    rw [Finset.sum_congr rfl (fun p _ => hinner p)]
    rw [show (∑ p, M p p * (2 * (∑ i, v i * v i))) = (∑ p, M p p) * (2 * (∑ i, v i * v i)) from
      (Finset.sum_mul Finset.univ (fun p => M p p) _).symm]
    ring
  have hS2 : (∑ p, ∑ q, M p q * (2 * (v p * v q))) = 2 * (∑ p, ∑ q, M p q * (v p * v q)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro p _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro q _
    ring
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hpt p q))]
  simp only [Finset.sum_sub_distrib, hS1, hS2]

/-- Diagonal value of `bmat v (A ∧ id)` for a trace-free symmetric `A`. -/
private lemma sum_diag_bmat_knProd_id2 (n : ℕ) {A : Fin n → Fin n → ℝ}
    (hA : ∀ i j, A i j = A j i) (htr : (∑ p, A p p) = 0) (v : Fin n → ℝ) :
    (∑ p, bmat v (knProd A (id2 n)) p p)
      = ((n : ℝ) - 2) * (∑ p, v p * (∑ j, A p j * v j)) := by
  have hpt : ∀ p, bmat v (knProd A (id2 n)) p p
      = (∑ i, ∑ j, v i * A i j * v j) * 1 - 2 * (v p * (∑ j, A p j * v j))
        + (∑ i, v i * v i) * A p p := by
    intro p
    rw [bmat_knProd_id2 n hA v p p]
    simp only [ite_true]
    ring
  rw [Finset.sum_congr rfl (fun p _ => hpt p)]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [show (∑ p : Fin n, (∑ i, ∑ j, v i * A i j * v j) * 1)
      = (n : ℝ) * (∑ i, ∑ j, v i * A i j * v j) from by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
  rw [show (∑ p : Fin n, 2 * (v p * (∑ j, A p j * v j)))
      = 2 * (∑ p, v p * (∑ j, A p j * v j)) from by
    rw [Finset.mul_sum]]
  rw [show (∑ p : Fin n, (∑ i, v i * v i) * A p p) = (∑ i, v i * v i) * (∑ p, A p p) from by
    rw [Finset.mul_sum]]
  rw [htr, mul_zero, sum_vA_v]
  ring

/-- Diagonal value of `bmat v (id ∧ id)`. -/
private lemma sum_diag_bmat_knProd_id2_id2 (n : ℕ) (v : Fin n → ℝ) :
    (∑ p, bmat v (knProd (id2 n) (id2 n)) p p) = 2 * ((n : ℝ) - 1) * (∑ i, v i * v i) := by
  have hpt : ∀ p, bmat v (knProd (id2 n) (id2 n)) p p
      = 2 * (∑ i, v i * v i) - 2 * (v p * v p) := by
    intro p
    rw [bmat_knProd_id2_id2 n v p p]
    simp only [ite_true]
    ring
  rw [Finset.sum_congr rfl (fun p _ => hpt p)]
  simp only [Finset.sum_sub_distrib]
  rw [show (∑ p : Fin n, 2 * (∑ i, v i * v i)) = (n : ℝ) * (2 * (∑ i, v i * v i)) from by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
  rw [show (∑ p : Fin n, 2 * (v p * v p)) = 2 * (∑ i, v i * v i) from
    (Finset.mul_sum Finset.univ (fun i => v i * v i) 2).symm]
  ring

/-! ## The six pairings for `S` -/

/-- `⟨Ric₀ S, bmat v (Ric₀ S ∧ id)⟩ = −2|Ric₀S·v|² + |v|²|Ric₀S|²`. -/
private lemma eval_ric0_bd (n : ℕ) {S : Curv4 n} (hS : IsAlgCurv S) (v : Fin n → ℝ) :
    frobPair (ric0 S) (bmat v (knProd (ric0 S) (id2 n)))
      = -2 * (∑ i, (∑ j, ric0 S i j * v j) * (∑ j, ric0 S i j * v j))
        + (∑ i, v i * v i) * ric0Frob2 S := by
  change (∑ p, ∑ q, ric0 S p q * bmat v (knProd (ric0 S) (id2 n)) p q) = _
  rw [sum_bmat_knProd_id2 n (ric0_symm hS) (ric0_symm hS) v]
  rw [ric0_trace_zero S hS, mul_zero, zero_sub]
  rw [sum_symm_vec_quad (ric0_symm hS) v]
  simp only [ric0Frob2]
  ring

/-- `⟨δ, bmat v S⟩ = tr(bmat v S)`. -/
private lemma eval_delta_bmat {S : Curv4 n} (v : Fin n → ℝ) {trB : ℝ}
    (htrB : trB = ∑ i, bmat v S i i) :
    frobPair (fun i j : Fin n => (if i = j then (1:ℝ) else 0)) (bmat v S) = trB := by
  rw [frobPair_delta_left]
  exact htrB.symm

/-- `⟨δ, bmat v (Ric₀ S ∧ id)⟩ = (n−2)·vᵀRic₀S·v`. -/
private lemma eval_delta_bd (n : ℕ) {S : Curv4 n} (hS : IsAlgCurv S) (v : Fin n → ℝ) :
    frobPair (fun i j : Fin n => (if i = j then (1:ℝ) else 0)) (bmat v (knProd (ric0 S) (id2 n)))
      = ((n : ℝ) - 2) * (∑ p, v p * (∑ j, ric0 S p j * v j)) := by
  rw [frobPair_delta_left]
  exact sum_diag_bmat_knProd_id2 n (ric0_symm hS) (ric0_trace_zero S hS) v

/-- `⟨Ric₀ S, bmat v (id ∧ id)⟩ = −2·vᵀRic₀S·v`. -/
private lemma eval_ric0_bi (n : ℕ) {S : Curv4 n} (hS : IsAlgCurv S) (v : Fin n → ℝ) :
    frobPair (ric0 S) (bmat v (knProd (id2 n) (id2 n)))
      = -2 * (∑ p, v p * (∑ j, ric0 S p j * v j)) := by
  change (∑ p, ∑ q, ric0 S p q * bmat v (knProd (id2 n) (id2 n)) p q) = _
  rw [sum_bmat_knProd_id2_id2 n (ric0 S) v]
  rw [ric0_trace_zero S hS, mul_zero]
  rw [sum_symm_vv (ric0 S) v]
  ring

/-- `⟨δ, bmat v (id ∧ id)⟩ = 2(n−1)|v|²`. -/
private lemma eval_delta_bi (n : ℕ) (v : Fin n → ℝ) :
    frobPair (fun i j : Fin n => (if i = j then (1:ℝ) else 0)) (bmat v (knProd (id2 n) (id2 n)))
      = 2 * ((n : ℝ) - 1) * (∑ i, v i * v i) := by
  rw [frobPair_delta_left]
  exact sum_diag_bmat_knProd_id2_id2 n v

/-! ## The expansion theorem -/

theorem W_expansion (n : ℕ) (hn : (n : ℝ) ≠ 0) {a : ℝ} {S : Submission.Diff.Alg.Curv4 n}
    (hS : Submission.Diff.Alg.IsAlgCurv S) {v : Fin n → ℝ} {Lam sg vv trB : ℝ}
    (hLam : Lam = Submission.Diff.Alg.scalAlg S / (n : ℝ))
    (hsg : sg = Work.Diff.Alg.Pinch.ric0Frob2 S / (n : ℝ))
    (hvv : vv = ∑ i, v i * v i)
    (htrB : trB = ∑ i, Work.Diff.Alg.Pinch.bmat v S i i) :
    (∑ i, ∑ j, Work.Diff.Alg.Pinch.ric (Work.Diff.Alg.Pinch.ell a (1 / 2) S) i j
        * Work.Diff.Alg.Pinch.bmat v (Work.Diff.Alg.Pinch.ell a (1 / 2) S) i j)
      = (1 + ((n : ℝ) - 2) * (1 / 2))
          * ((∑ i, ∑ j, Work.Diff.Alg.Pinch.ric0 S i j * Work.Diff.Alg.Pinch.bmat v S i j)
             - (∑ i, (∑ j, Work.Diff.Alg.Pinch.ric0 S i j * v j)
                 * (∑ j, Work.Diff.Alg.Pinch.ric0 S i j * v j))
             + ((n : ℝ) / 2) * vv * sg
             - 2 * a * Lam * (∑ i, v i * (∑ j, Work.Diff.Alg.Pinch.ric0 S i j * v j)))
        + (Lam * (1 + 2 * ((n : ℝ) - 1) * a))
          * (trB + ((n : ℝ) - 2) / 2 * (∑ i, v i * (∑ j, Work.Diff.Alg.Pinch.ric0 S i j * v j))
             + 2 * a * ((n : ℝ) - 1) * Lam * vv) := by
  have hr : ric (ell a (1/2) S)
      = (1 + ((n : ℝ) - 2) * (1/2)) • ric0 S
        + (scalAlg S * (1 + 2 * ((n : ℝ) - 1) * a) / (n : ℝ))
            • (fun i j : Fin n => (if i = j then (1:ℝ) else 0)) := by
    funext i j
    rw [ric_ell_aux a (1/2) hn hS i j]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hb : bmat v (ell a (1/2) S)
      = bmat v S + ((1:ℝ)/2) • bmat v (knProd (ric0 S) (id2 n))
        + (a / (n : ℝ) * scalAlg S) • bmat v (knProd (id2 n) (id2 n)) := by
    simp only [ell, bmat_add, bmat_smul]
  change frobPair (ric (ell a (1/2) S)) (bmat v (ell a (1/2) S)) = _
  rw [hr, hb]
  simp only [frobPair_add_left, frobPair_add_right, frobPair_smul_left, frobPair_smul_right]
  rw [eval_ric0_bd n hS v, eval_delta_bmat (v := v) htrB, eval_delta_bd n hS v,
      eval_ric0_bi n hS v, eval_delta_bi n v]
  rw [show frobPair (ric0 S) (bmat v S) = ∑ i, ∑ j, ric0 S i j * bmat v S i j from rfl]
  rw [hLam, hsg, hvv]
  field_simp
  ring

end Work.Diff.Alg.Pinch
