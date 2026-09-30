import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.rayPoly_eq
import Submission.Work.BW.rayHilb_finite
import Submission.Work.BW.rayHilb_poly

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
/-! Guidance from the project lead (the requester):

LEAD NOTES (BW multiplicity block B: the split of zero_estimate_stepwise, requests/bw3). Your node is `rayPoly_ne_zero_of_meetsG`. Its doc comment gives the proof idea, size and dependencies; the design is below. Definitions: Submission.Work.BW.DefsB (imports DefsMult; lead-placed, do not edit). All 18 B-nodes are dispatched in parallel as Submission.Work.BW.<name>. Block-A nodes (rayHilb_poly, refined_bezout, subgroup_rayDeg, multiHom_assPrime, rayDeg_*) are live or proved. IMPORT siblings; never reprove them or restate them under another name. zero_estimate_stepwise (owner H32) is now the ASSEMBLY of these. If you believe your statement is false, give a concrete counterexample.

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

/-- The monomial `∏ᵢ X_{i0}^{dᵢ}` has multidegree `d`: it lies in the piece `homPiece N d`. -/
private lemma prod_X_mem_homPiece {N : ℕ} (d : Fin (N + 1) →₀ ℕ) :
    (∏ i : Fin (N + 1), MvPolynomial.X (i, 0) ^ (d i)) ∈ homPiece N d := by
  rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule]
  have hprod : MvPolynomial.IsWeightedHomogeneous (mdeg N)
      ((∏ i : Fin (N + 1), MvPolynomial.X (i, 0) ^ (d i)) : MR N)
      (∑ i : Fin (N + 1), (d i) • mdeg N (i, 0)) := by
    apply MvPolynomial.IsWeightedHomogeneous.prod (R := ℂ) (σ := Fin (N + 1) × Fin 2)
      (ι := Fin (N + 1)) Finset.univ (fun i => MvPolynomial.X (i, 0) ^ (d i))
      (fun i => (d i) • mdeg N (i, 0))
    intro i _
    exact (MvPolynomial.isWeightedHomogeneous_X (R := ℂ) (mdeg N) (i, 0)).pow (d i)
  convert hprod using 2
  ext j
  simp [mdeg, Finsupp.smul_single]

/-- On a point where `X_{i0} ≠ 0` for every `i`, the monomial `∏ᵢ X_{i0}^{aᵢ}` does not vanish. -/
private lemma eval_prod_X_ne_zero {N : ℕ} (x : Fin (N + 1) × Fin 2 → ℂ)
    (hx : ∀ i : Fin (N + 1), x (i, 0) ≠ 0) (a : Fin (N + 1) → ℕ) :
    MvPolynomial.eval x ((∏ i : Fin (N + 1), MvPolynomial.X (i, 0) ^ (a i)) : MR N) ≠ 0 := by
  rw [map_prod]
  simp only [MvPolynomial.eval_X, MvPolynomial.eval_pow]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hx i))

/-- An ideal meeting `G` has `rayHilb ≥ 1` in every degree `tD`: the monomial `∏ᵢ X_{i0}^{tDᵢ}`
lies in the piece `(R)_{tD}`, is nonzero at any point of `Z(I) ∩ G`, and therefore survives in
`(R/I)_{tD}`. -/
private lemma rayHilb_pos_of_meetsG {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (I : Ideal (MR N))
    (hG : MeetsG N I) (t : ℕ) : 1 ≤ rayHilb N D I t := by
  obtain ⟨x, hx, hIx⟩ := hG
  have hx0 : ∀ i : Fin (N + 1), x (i, 0) ≠ 0 := by
    intro i
    induction i using Fin.cases with
    | zero => exact hx.1
    | succ j => exact (hx.2 j).1
  set m : MR N := ∏ i : Fin (N + 1), MvPolynomial.X (i, 0) ^ ((t • D) i) with hm
  have hmmem : m ∈ homPiece N (t • D) := by
    rw [hm]; exact prod_X_mem_homPiece (t • D)
  have hmnot : m ∉ I := by
    intro hmem
    have hze : MvPolynomial.eval x m = 0 := by
      have h1 : m ∈ ptIdeal N x := hIx hmem
      rw [ptIdeal, RingHom.mem_ker] at h1
      exact h1
    have hne : MvPolynomial.eval x m ≠ 0 := by
      rw [hm]; exact eval_prod_X_ne_zero x hx0 (fun i => (t • D) i)
    exact hne hze
  have hfin : Module.Finite ℂ ↥(homPiece N (t • D)) := rayHilb_finite N (t • D)
  have hneq : (Submodule.Quotient.mk (p := Submodule.comap (homPiece N (t • D)).subtype
        (I.restrictScalars ℂ)) ⟨m, hmmem⟩ : ↥(homPiece N (t • D)) ⧸
        Submodule.comap (homPiece N (t • D)).subtype (I.restrictScalars ℂ)) ≠ 0 := by
    intro hzero
    rw [Submodule.Quotient.mk_eq_zero] at hzero
    exact hmnot (by simpa [Submodule.mem_comap] using hzero)
  have hnt : Nontrivial (↥(homPiece N (t • D)) ⧸
      Submodule.comap (homPiece N (t • D)).subtype (I.restrictScalars ℂ)) :=
    nontrivial_of_ne _ _ hneq
  have hpos : 0 < rayHilb N D I t := by
    rw [rayHilb]
    exact Module.finrank_pos
  omega



/-- B1f. An ideal through a point of `G` is relevant: `∏ X_{i0}^{tDᵢ} ∉ I`, so its ray Hilbert
function is `≥ 1` and its ray Hilbert polynomial (A2) is nonzero. Size 0.3–0.6k. -/
theorem rayPoly_ne_zero_of_meetsG {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (I : Ideal (MR N)) (hI : MultiHom N I) (hG : MeetsG N I) : rayPoly N D I ≠ 0 := by
  obtain ⟨q, hq, _⟩ := rayHilb_poly D hD I hI
  rw [rayPoly_eq hq]
  intro hq0
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hq
  have h1 : ((rayHilb N D I (max a 1) : ℕ) : ℚ) = q.eval ((max a 1 : ℕ) : ℚ) :=
    ha _ (le_max_left _ _)
  rw [hq0] at h1
  simp at h1
  have h2 : 1 ≤ rayHilb N D I (max a 1) := rayHilb_pos_of_meetsG D I hG _
  have h3 : (1 : ℚ) ≤ ((rayHilb N D I (max a 1) : ℕ) : ℚ) := by exact_mod_cast h2
  linarith

end Work.BW
