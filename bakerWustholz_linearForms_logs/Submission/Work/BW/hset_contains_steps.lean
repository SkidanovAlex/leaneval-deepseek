import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.transl_basic
import Submission.Work.BW.vanish_span
import Submission.Work.BW.derH_comm
import Submission.Work.BW.derH_transl
import Submission.Work.BW.foldr_two

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW multiplicity block B: the split of zero_estimate_stepwise, requests/bw3). Your node is `hset_contains_steps`. Its doc comment gives the proof idea, size and dependencies; the design is below. Definitions: Submission.Work.BW.DefsB (imports DefsMult; lead-placed, do not edit). All 18 B-nodes are dispatched in parallel as Submission.Work.BW.<name>. Block-A nodes (rayHilb_poly, refined_bezout, subgroup_rayDeg, multiHom_assPrime, rayDeg_*) are live or proved. IMPORT siblings; never reprove them or restate them under another name. zero_estimate_stepwise (owner H32) is now the ASSEMBLY of these. If you believe your statement is false, give a concrete counterexample.

===== DESIGN_B.md =====
# How `zero_estimate_stepwise` is split into nodes (phase 3, 2026-09-27)

**The statement of `zero_estimate_stepwise` does not change.** It matches the workspace text
byte for byte, and only its proof becomes an assembly.

## Files

* **Definitions.** New definitions are in `DefsB.lean` (no `sorry`). Install it as
  `Submission/Work/BW/DefsB.lean`, importing `Submission.Work.BW.DefsMult`, in `namespace Work.BW`.
* **Nodes.** There are 19 statement files. Each ends in `:= by sorry` and has no import or
  namespace lines.
* **What each node file holds.** Its doc comment gives the proof idea, the size in k lines, and
  the dependencies.

## Elaboration check

I ran one check on 3.144 with
`systemd-run --user --scope -q -p MemoryMax=12G ~/.elan/bin/lake env lean /tmp/bwmult/TestB.lean`.
* **Imports.** The file imported Mathlib, `DefsMult`, `subgroup_rayDeg`, `multiHom_assPrime`,
  `rayDeg_bot`, `rayHilb_poly`, `zeroest_defs` and `rayDeg_mono`.
* **Contents.** `DefsB`, then all 19 statements.
* **Result.** 19 `sorry` warnings, no errors, and no name clashes with those modules.
* **Not imported.** `refined_bezout` has no olean yet, and `rayDim_lt_of_lt`'s olean is stale.
  The statements here only name those two nodes in doc comments, so importing them is not needed.

## Key simplification

Philippon's operators `δ^x_g` (4.1–4.2) are defined here as polynomial maps. There are no
analytic functions and no "components meeting G" quotients.
* **`transl g`.** A graded `aeval` substitution:
  * `X₀₁ ↦ X₀₁ + g₀X₀₀`;
  * `X_{i1} ↦ gᵢX_{i1}`.
* **`derH w`.** A multidegree-preserving invariant derivation:
  * `w₀X₀₀∂_{X₀₁} + ∑ wᵢX_{i1}∂_{X_{i1}}`.
* **Consequences.**
  * Prop 4.3 becomes an exact identity: `δ^tδ^{t'} = δ^{t+t'}`, and `τ` commutes with `δ`.
  * Prop 4.4 is true by definition, since `Hset` is phrased as ideal membership in `𝔓`.
* **Point sets.** The step point sets are `{sγ : s ≤ S}`, so the chain ideals are explicit
  (`chainIdeal A B`).

## DAG and sizes (k lines, DeepSeek)

| node | deps | size |
|---|---|---|
| **B1** `transl_basic` | — | 0.6–1 |
| **B1** `derH_basic` | — | 1.5–2.5 |
| **B1** `vanish_span` | derH_basic | 0.8–1.5 |
| **B1** `rayHilb_transl` | transl_basic | 0.4–0.8 |
| **B1** `mem_of_vanish_ZG` | transl_basic | 0.8–1.5 |
| **B1** `rayPoly_ne_zero_of_meetsG` | rayHilb_poly | 0.3–0.6 |
| **B2** `closedSub_jordan` | (expPoly_zeros-style independence) | 1.5–2.5 |
| **B2** `closedSub_torus` | Mathlib `linearIndependent_monoidHom` | 0.8–1.5 |
| **B2** `closedSub_structure` | B2a, B2b, ratSpan_saturation | 1.5–2.5 |
| **B2** `stab_closedSub` | transl_basic | 1–2 |
| **B3** `subIdeal_isPrime` | multiHom_subIdeal | 1–1.5 |
| **B3** `wuestholz_length` | derH_basic, subIdeal_isPrime | 2.5–4 |
| **§5.1** `chain_first_stable` | B1, multiHom_assPrime, rayDim_lt_of_lt, rayDeg_bot | 1–2 |
| **§5.1** `hset_contains_steps` | B1 | 0.4–0.8 |
| **§5.1** `hset_zero_cosets` | rayHilb_transl, rayDim_lt_of_lt, rayPoly_ne_zero_of_meetsG, multiHom_assPrime | 1–1.5 |
| **§5.1** `coset_minimalPrime` | mem_of_vanish_ZG, subIdeal_isPrime, B1 | 1.5–2.5 |
| **§5.1** `coset_length` | wuestholz_length, vanish_span, transl_basic | 0.6–1 |
| **§5.1** `stab_step` | all of the above in this table, refined_bezout, rayDeg_bot | 1.5–2.5 |
| **assembly** `zero_estimate_stepwise` | chain_first_stable, stab_step, subgroup_rayDeg | 0.6–1 |
| **total** | | **≈19–34k (central ≈25k)** |

**This is larger than the phase-2 estimate of 9–16k.** That estimate did not count the subgroup
classification B2, the cone Nullstellensatz step, or the §5.1 bookkeeping.

**Parallelism.**
* **Wave 1, can start now:** all of B1, B2 and B3, plus `hset_contains_steps`.
* **Wave 2:** `chain_first_stable`, `hset_zero_cosets`, `coset_minimalPrime` and `coset_length`.
* **Wave 3:** `stab_step`.
* **Wave 4:** the assembly.

## Notes for the owner (H32)

* **`pointwise_zero_dichotomy` / `expPoly_zeros` are not on this route.** `expPoly_zeros` (or its
  proof idea) is reusable in `closedSub_jordan`.
* **`B2` is split** into `closedSub_jordan`, `closedSub_torus` and `closedSub_structure`, with
  `stab_closedSub` separate. Each is ≤ 2.5k.
* **`hmax` hypotheses.** `stab_step` and `hset_zero_cosets` need "𝔓 is of maximal dimension among
  the minimal primes through `G`". `chain_first_stable` supplies it.
-/

namespace Work.BW

/-! ### The two `applyH` laws used by this node

`derH_basic` bundles four facts; this node needs only the last two of them, namely that
`transl g` commutes with `applyH` (`applyH_transl`) and that `applyH` composes additively in the
budget (`applyH_add`).  Those two facts rest only on `derH_transl` (commutation of `derH` with
`transl`), on `derH_comm` (commutation of two `derH`'s) and on the generic list lemma `foldr_two`;
we derive them here directly from those three proved modules, so that this node does not depend
on the (independently owned) `derH_basic` constant. -/

private lemma iterate_transl_aux {N : ℕ} (g w : Fin (N + 1) → ℂ) (n : ℕ) (F : MR N) :
    transl g (((derH w)^[n]) F) = ((derH w)^[n]) (transl g F) := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', derH_transl, ih]

private lemma foldr_transl_aux {N : ℕ} {ι : Type*} (L : List ι) (f : ι → MR N → MR N)
    (g : Fin (N + 1) → ℂ)
    (hf : ∀ i ∈ L, ∀ Q, transl g (f i Q) = f i (transl g Q)) (F : MR N) :
    transl g (L.foldr (fun i Q => f i Q) F) = L.foldr (fun i Q => f i Q) (transl g F) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.foldr_cons]
    rw [hf a List.mem_cons_self]
    rw [ih (fun i hi => hf i (List.mem_cons_of_mem a hi))]

private lemma applyH_transl_aux {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (g : Fin (N + 1) → ℂ)
    (t : Fin q → ℕ) (F : MR N) :
    transl g (applyH w t F) = applyH w t (transl g F) := by
  rw [applyH, applyH]
  exact foldr_transl_aux (List.finRange q) (fun m Q => (derH (w m))^[t m] Q) g
    (fun m _ Q => iterate_transl_aux g (w m) (t m) Q) F

private lemma iterate_comm_right_aux {α : Type*} {f g : α → α} (h : ∀ x, f (g x) = g (f x)) :
    ∀ (n : ℕ) (x : α), f ((g^[n]) x) = (g^[n]) (f x) := by
  intro n
  induction n with
  | zero => intro x; rfl
  | succ n ih =>
    intro x
    rw [Function.iterate_succ_apply', h, ih, Function.iterate_succ_apply']

private lemma iterate_comm_aux {α : Type*} {f g : α → α} (h : ∀ x, f (g x) = g (f x))
    (m n : ℕ) (x : α) : (f^[m]) ((g^[n]) x) = (g^[n]) ((f^[m]) x) := by
  induction m generalizing x with
  | zero => rfl
  | succ m ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih, iterate_comm_right_aux h n]

private lemma applyH_add_aux {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (t t' : Fin q → ℕ)
    (F : MR N) : applyH w t (applyH w t' F) = applyH w (t + t') F := by
  rw [applyH, applyH, applyH]
  exact foldr_two (List.finRange q) (fun i n => (derH (w i))^[n])
    (fun i n n' => Function.iterate_add (derH (w i)) n n')
    (fun i j n n' x => iterate_comm_aux (fun y => derH_comm (w i) (w j) y) n n' x)
    t t' F

/-- The group law of `G` sends `sγ` and `s'γ` to `(s+s')γ`: `gmul` of two step points is the
step point of the sum of the indices. -/
theorem gmul_ptTheta {N : ℕ} (θ : Fin N → ℂ) (s s' : ℕ) :
    gmul (ptTheta θ s) (ptTheta θ s') = ptTheta θ (s + s') := by
  funext j
  refine Fin.cases ?_ ?_ j <;>
    simp [gmul, ptTheta, Fin.cons_zero, Fin.cons_succ, Nat.cast_add, pow_add]

/-- §5.1(c), where the step data enter. If `I_{r+1} ≤ 𝔓` (budgets `A + S`, `B + T`), then every
step point `sγ`, `s ≤ S`, lies in `H_V(T)` for `I_r` (budgets `A`, `B`): on generators,
`τ_{sγ} δ^{t'} τ_{s''γ} δ^{t''} P^h = τ_{(s+s'')γ} δ^{t'+t''} P^h ∈ chainGen (A+S) (B+T)`
(`derH_basic`, `transl_basic`, `gmul` of `ptTheta`), then `vanish_span`. Size 0.4–0.8k. -/
theorem hset_contains_steps {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (θ : Fin N → ℂ)
    (hθ : ∀ i, θ i ≠ 0) (D : Fin (N + 1) → ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ)
    (A B S T : ℕ) (𝔓 : Ideal (MR N)) (h2 : chainIdeal w θ D P (A + S) (B + T) ≤ 𝔓) :
    ∀ s, s ≤ S → ptTheta θ s ∈ Hset w 𝔓 (chainIdeal w θ D P A B) T := by
  intro s hs
  refine ⟨?_, ?_⟩
  · intro i
    show ptTheta θ s i.succ ≠ 0
    rw [ptTheta, Fin.cons_succ]
    exact pow_ne_zero s (hθ i)
  · intro F hF t ht
    refine vanish_span w (ptTheta θ s) T 𝔓 (chainGen w θ D P A B) ?_ F hF t ht
    intro F₀ hF₀ t₀ ht₀
    obtain ⟨s'', t'', hs'', ht'', rfl⟩ := hF₀
    have key :
        transl (ptTheta θ s) (applyH w t₀ (transl (ptTheta θ s'') (applyH w t'' (homog D P))))
          = transl (ptTheta θ (s + s'')) (applyH w (t₀ + t'') (homog D P)) := by
      rw [← applyH_transl_aux w (ptTheta θ s'') t₀ (applyH w t'' (homog D P))]
      rw [(transl_basic (ptTheta θ s) (ptTheta θ s'')).2.2.1
            (applyH w t₀ (applyH w t'' (homog D P)))]
      rw [gmul_ptTheta]
      rw [applyH_add_aux w t₀ t'' (homog D P)]
    rw [key]
    apply h2
    apply Ideal.subset_span
    refine ⟨s + s'', t₀ + t'', ?_, ?_, rfl⟩
    · omega
    · have hsum : ∑ k, (t₀ + t'') k = (∑ k, t₀ k) + (∑ k, t'' k) := by
        simp only [Pi.add_apply]
        exact Finset.sum_add_distrib
      omega

end Work.BW
