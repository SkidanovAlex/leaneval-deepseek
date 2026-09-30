import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.homog_basic
import Submission.Work.BW.derH_comm
import Submission.Work.BW.derH_transl
import Submission.Work.BW.foldr_two
import Submission.Work.BW.chainIdeal_le_ptIdeal_gone

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW multiplicity block B: the split of zero_estimate_stepwise, requests/bw3). Your node is `derH_basic`. Its doc comment gives the proof idea, size and dependencies; the design is below. Definitions: Submission.Work.BW.DefsB (imports DefsMult; lead-placed, do not edit). All 18 B-nodes are dispatched in parallel as Submission.Work.BW.<name>. Block-A nodes (rayHilb_poly, refined_bezout, subgroup_rayDeg, multiHom_assPrime, rayDeg_*) are live or proved. IMPORT siblings; never reprove them or restate them under another name. zero_estimate_stepwise (owner H32) is now the ASSEMBLY of these. If you believe your statement is false, give a concrete counterexample.

===== DESIGN_B.md (excerpt) =====
| **B3** `derH_basic` | derH_basic, subIdeal_isPrime | 2.5–4k |
`derH_basic` (Philippon 4.6–4.7, Wüstholz). If `I(G')` is a minimal prime of `J` and
`δ^t J ⊆ I(G')` for all `|t| ≤ T`, then the primary component of `J` at `I(G')` has length
`≥ C(T + ℓ, ℓ)`, `ℓ = dim W − dim (W ∩ Lie G')`. Proof: pick `u_j ∈ I(G')` (homogenised
`χ^{M_j} − 1`, and `X₀₁` if `ε = false`) and `ℓ` derivations in `W` with `δ_i u_j ≡ δ_{ij}`
mod `I(G')` (4.6: the matrix `(δ_{w_k} u_j)` is constant on `G'` of rank `ℓ`); for each `τ ≤ T`
the monomials `u^α`, `|α| = τ`, are independent over the residue field modulo
`J + I(G')^{τ+1}` (apply `δ^{α}`); sum the graded pieces of `(R/J)_{I(G')}`.
-/

namespace Work.BW

open MvPolynomial


private lemma weight_single_add_sub_single {N : ℕ} {u v : Fin (N+1) × Fin 2}
    (huv : mdeg N u = mdeg N v) (m : (Fin (N+1) × Fin 2) →₀ ℕ) (hmv : m v ≠ 0) :
    Finsupp.weight (mdeg N) (Finsupp.single u 1 + (m - Finsupp.single v 1))
      = Finsupp.weight (mdeg N) m := by
  have h1 := Finsupp.weight_sub_single_add (w := mdeg N) hmv
  calc Finsupp.weight (mdeg N) (Finsupp.single u 1 + (m - Finsupp.single v 1))
      = Finsupp.weight (mdeg N) (Finsupp.single u 1) + Finsupp.weight (mdeg N) (m - Finsupp.single v 1) := map_add _ _ _
    _ = mdeg N u + Finsupp.weight (mdeg N) (m - Finsupp.single v 1) := by rw [Finsupp.weight_single, one_smul]
    _ = mdeg N v + Finsupp.weight (mdeg N) (m - Finsupp.single v 1) := by rw [huv]
    _ = Finsupp.weight (mdeg N) (m - Finsupp.single v 1) + mdeg N v := add_comm _ _
    _ = Finsupp.weight (mdeg N) m := h1

private lemma X_mul_pderiv_monomial {N : ℕ} (u v : Fin (N+1) × Fin 2)
    (m : (Fin (N+1) × Fin 2) →₀ ℕ) (a : ℂ) :
    (MvPolynomial.X u : MR N) * MvPolynomial.pderiv v (MvPolynomial.monomial m a) =
      MvPolynomial.monomial (Finsupp.single u 1 + (m - Finsupp.single v 1)) (a * (m v : ℂ)) := by
  rw [MvPolynomial.pderiv_monomial, ← pow_one (MvPolynomial.X u), MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul_monomial]
  simp

private lemma X_mul_pderiv_mem {N : ℕ} {u v : Fin (N+1) × Fin 2} (huv : mdeg N u = mdeg N v)
    {d : Fin (N+1) →₀ ℕ} {F : MR N} (hF : F ∈ homPiece N d) :
    MvPolynomial.X u * MvPolynomial.pderiv v F ∈ homPiece N d := by
  have hF' : F ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N) d := hF
  show MvPolynomial.X u * MvPolynomial.pderiv v F ∈
    MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N) d
  rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported,
      AddMonoidAlgebra.supported_eq_span_single] at hF'
  refine Submodule.span_induction (p := fun x _ => MvPolynomial.X u * MvPolynomial.pderiv v x ∈
      MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N) d) ?_ ?_ ?_ ?_ hF'
  · rintro x ⟨m, hm, rfl⟩
    change MvPolynomial.X u * MvPolynomial.pderiv v (MvPolynomial.monomial m 1) ∈
      MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N) d
    rw [X_mul_pderiv_monomial]
    by_cases h : m v = 0
    · rw [h]; simp
    · rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
      refine MvPolynomial.isWeightedHomogeneous_monomial (mdeg N) _ _ ?_
      rw [weight_single_add_sub_single huv m h, hm]
  · simp
  · intro x y hx hy hp hq
    rw [map_add, mul_add]
    exact add_mem hp hq
  · intro a x hx hp
    rw [Derivation.map_smul, mul_smul_comm]
    exact Submodule.smul_mem _ _ hp

private lemma C_mul_mem_homPiece {N : ℕ} {c : ℂ} {d : Fin (N+1) →₀ ℕ} {G : MR N}
    (hG : G ∈ homPiece N d) : MvPolynomial.C c * G ∈ homPiece N d := by
  rw [MvPolynomial.C_mul']
  exact Submodule.smul_mem _ _ hG

private lemma derH_mem_homPiece {N : ℕ} (w : Fin (N+1) → ℂ) {d : Fin (N+1) →₀ ℕ} {F : MR N}
    (hF : F ∈ homPiece N d) : derH w F ∈ homPiece N d := by
  rw [derH]
  refine add_mem ?_ ?_
  · rw [mul_assoc]
    exact C_mul_mem_homPiece (X_mul_pderiv_mem (by rfl : mdeg N (0,0) = mdeg N (0,1)) hF)
  · refine Submodule.sum_mem _ fun i _ => ?_
    rw [mul_assoc]
    exact C_mul_mem_homPiece (X_mul_pderiv_mem (by rfl : mdeg N (i.succ,1) = mdeg N (i.succ,1)) hF)

private lemma iterate_mem {α : Type*} {S : Set α} {f : α → α} (hf : ∀ x ∈ S, f x ∈ S) :
    ∀ (n : ℕ) (x : α), x ∈ S → (f^[n]) x ∈ S := by
  intro n
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih => intro x hx; rw [Function.iterate_succ_apply']; exact hf _ (ih x hx)

private lemma foldr_mem {ι α : Type*} (L : List ι) (f : ι → α → α) (S : Set α)
    (hf : ∀ i ∈ L, ∀ x ∈ S, f i x ∈ S) (x : α) (hx : x ∈ S) :
    L.foldr (fun i Q => f i Q) x ∈ S := by
  induction L with
  | nil => simpa using hx
  | cons a L ih =>
    simp only [List.foldr_cons]
    exact hf a List.mem_cons_self _ (ih (fun i hi => hf i (List.mem_cons_of_mem a hi)))

private lemma applyH_mem {N q : ℕ} (w : Fin q → Fin (N+1) → ℂ) (t : Fin q → ℕ)
    {d : Fin (N+1) →₀ ℕ} {F : MR N} (hF : F ∈ homPiece N d) :
    applyH w t F ∈ homPiece N d := by
  rw [applyH]
  refine foldr_mem (List.finRange q) (fun m Q => (derH (w m))^[t m] Q) (homPiece N d) ?_ F hF
  intro m _ x hx
  exact iterate_mem (f := derH (w m)) (fun y hy => derH_mem_homPiece (w m) hy) (t m) x hx

private lemma iterate_transl {N : ℕ} (g w : Fin (N+1) → ℂ) (n : ℕ) (F : MR N) :
    transl g (((derH w)^[n]) F) = ((derH w)^[n]) (transl g F) := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', derH_transl, ih]

private lemma foldr_transl {N : ℕ} {ι : Type*} (L : List ι) (f : ι → MR N → MR N)
    (g : Fin (N+1) → ℂ)
    (hf : ∀ i ∈ L, ∀ Q, transl g (f i Q) = f i (transl g Q)) (F : MR N) :
    transl g (L.foldr (fun i Q => f i Q) F) = L.foldr (fun i Q => f i Q) (transl g F) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.foldr_cons]
    rw [hf a List.mem_cons_self]
    rw [ih (fun i hi => hf i (List.mem_cons_of_mem a hi))]

private lemma applyH_transl {N q : ℕ} (w : Fin q → Fin (N+1) → ℂ) (g : Fin (N+1) → ℂ)
    (t : Fin q → ℕ) (F : MR N) :
    transl g (applyH w t F) = applyH w t (transl g F) := by
  rw [applyH, applyH]
  exact foldr_transl (List.finRange q) (fun m Q => (derH (w m))^[t m] Q) g
    (fun m _ Q => iterate_transl g (w m) (t m) Q) F

private lemma iterate_comm_right {α : Type*} {f g : α → α} (h : ∀ x, f (g x) = g (f x)) :
    ∀ (n : ℕ) (x : α), f ((g^[n]) x) = (g^[n]) (f x) := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    rw [Function.iterate_succ_apply', h, ih, Function.iterate_succ_apply']

private lemma iterate_comm {α : Type*} {f g : α → α} (h : ∀ x, f (g x) = g (f x)) (m n : ℕ) (x : α) :
    (f^[m]) ((g^[n]) x) = (g^[n]) ((f^[m]) x) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih, iterate_comm_right h n]

private lemma applyH_add {N q : ℕ} (w : Fin q → Fin (N+1) → ℂ) (t t' : Fin q → ℕ) (F : MR N) :
    applyH w t (applyH w t' F) = applyH w (t + t') F := by
  rw [applyH, applyH, applyH]
  exact foldr_two (List.finRange q) (fun i n => (derH (w i))^[n])
    (fun i n n' => Function.iterate_add (derH (w i)) n n')
    (fun i j n n' x => iterate_comm (fun y => derH_comm (w i) (w j) y) n n' x)
    t t' F

/-- B1b (Philippon 4.1–4.3 for `G_a × G_m^N`). The homogeneous invariant derivations preserve
multidegree, commute (so `δ^t δ^{t'} = δ^{t+t'}`) and commute with translations; homogenisation
to multidegree `D` intertwines `derH` with the affine `derC`, so `δ^t P^h` dehomogenises to
`applyW w t P`. Proof: `derH w (homog D Q) = homog D (derC w Q)` on the monomial basis, then
induction along `List.finRange`. Size 1.5–2.5k. -/
theorem derH_basic {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) :
    (∀ (t : Fin q → ℕ) (d : Fin (N + 1) →₀ ℕ) (F : MR N),
      F ∈ homPiece N d → applyH w t F ∈ homPiece N d) ∧
    (∀ (t t' : Fin q → ℕ) (F : MR N), applyH w t (applyH w t' F) = applyH w (t + t') F) ∧
    (∀ (g : Fin (N + 1) → ℂ) (t : Fin q → ℕ) (F : MR N),
      transl g (applyH w t F) = applyH w t (transl g F)) ∧
    (∀ (D : Fin (N + 1) → ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ), (∀ i, P.degreeOf i ≤ D i) →
      homog D P ∈ homPiece N (fsD D) ∧ (P ≠ 0 → homog D P ≠ 0) ∧
      ∀ (t : Fin q → ℕ) (y : Fin (N + 1) → ℂ),
        MvPolynomial.eval (conePt N y) (applyH w t (homog D P)) =
          MvPolynomial.eval y (applyW w t P)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t d F hF
    exact applyH_mem w t hF
  · intro t t' F
    exact applyH_add w t t' F
  · intro g t F
    exact applyH_transl w g t F
  · intro D P h
    refine ⟨(homog_basic D P h).1, (homog_basic D P h).2.1, ?_⟩
    intro t y
    rw [eval_dehom, dehom_applyH, dehom_homog]

end Work.BW
