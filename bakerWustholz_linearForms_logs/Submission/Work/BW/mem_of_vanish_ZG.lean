import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.eval_scale_homPiece
import Submission.Work.BW.ptIdeal_conePt_of_mem_zeroLocus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW multiplicity block B: the split of zero_estimate_stepwise, requests/bw3). Your node is `mem_of_vanish_ZG`. Its doc comment gives the proof idea, size and dependencies; the design is below. Definitions: Submission.Work.BW.DefsB (imports DefsMult; lead-placed, do not edit). All 18 B-nodes are dispatched in parallel as Submission.Work.BW.<name>. Block-A nodes (rayHilb_poly, refined_bezout, subgroup_rayDeg, multiHom_assPrime, rayDeg_*) are live or proved. IMPORT siblings; never reprove them or restate them under another name. zero_estimate_stepwise (owner H32) is now the ASSEMBLY of these. If you believe your statement is false, give a concrete counterexample.

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

open MvPolynomial

variable {N : ℕ}

/-- The product `X₀₀ · ∏_{i : Fin N} X_{i+1,0} X_{i+1,1}` of the cone coordinates that are
nonzero on the cone over `G = G_a × G_m^N` (the `X_{0,1}` coordinate is not part of it, since
`G_a` has no `X_{0,1} ≠ 0` condition).  It is multihomogeneous of multidegree `∑ᵢ eᵢ`, and it
vanishes exactly on the complement of the cone over `G`. -/
noncomputable def conePi (N : ℕ) : MR N :=
  MvPolynomial.X ((0 : Fin (N + 1)), (0 : Fin 2)) *
    ∏ i : Fin N,
      (MvPolynomial.X (i.succ, (0 : Fin 2)) * MvPolynomial.X (i.succ, (1 : Fin 2)))

/-- Evaluation of `conePi` at a cone point. -/
lemma eval_conePi (x : Fin (N + 1) × Fin 2 → ℂ) :
    MvPolynomial.eval x (conePi N) =
      x (0, 0) * ∏ i : Fin N, (x (i.succ, 0) * x (i.succ, 1)) := by
  rw [conePi, map_mul, map_prod]
  congr 1
  · rw [MvPolynomial.eval_X]
  · exact Finset.prod_congr rfl fun i _ => by
      rw [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X]

/-- `conePi` does not vanish at a cone point over `G`. -/
lemma eval_conePi_ne_zero {x : Fin (N + 1) × Fin 2 → ℂ} (hx : OnG N x) :
    MvPolynomial.eval x (conePi N) ≠ 0 := by
  rw [eval_conePi]
  exact mul_ne_zero hx.1
    (Finset.prod_ne_zero_iff.mpr fun i _ => mul_ne_zero (hx.2 i).1 (hx.2 i).2)

/-- B1e (Nullstellensatz on the cone, relative to `G`). A multihomogeneous prime `𝔓` through a
point of `G` contains every multihomogeneous `F` vanishing at the cone points over `ZG 𝔓`.
Proof: rescale each factor to reach every cone point of `Z(𝔓)` over `G`; then `F · Π` vanishes on
`Z(𝔓)` with `Π = X₀₀ ∏ X_{i0}X_{i1}`, so `F Π ∈ √𝔓 = 𝔓` (Mathlib `MvPolynomial` Nullstellensatz)
and `Π ∉ 𝔓`. Size 0.8–1.5k. -/
theorem mem_of_vanish_ZG {N : ℕ} (𝔓 : Ideal (MR N)) (h𝔓 : 𝔓.IsPrime) (hH : MultiHom N 𝔓)
    (hG : MeetsG N 𝔓) (F : MR N) (hFh : ∃ d, F ∈ homPiece N d)
    (hF : ∀ v ∈ ZG 𝔓, MvPolynomial.eval (conePt N v) F = 0) : F ∈ 𝔓 := by
  classical
  -- `𝔓` passes through a cone point `x₀` over `G`, so `Π = conePi N` is nonzero there.
  obtain ⟨x₀, hx₀G, hx₀𝔓⟩ := hG
  have hPiNot : conePi N ∉ 𝔓 := fun hmem =>
    eval_conePi_ne_zero hx₀G (by simpa [ptIdeal] using hx₀𝔓 hmem)
  -- `F · Π` vanishes on all of `Z(𝔓)`: at the cone points over `G` after rescaling the factors
  -- (`F` vanishes there by hypothesis), and elsewhere because `Π` does.
  have hmem : F * conePi N ∈ 𝔓 := by
    have h1 : F * conePi N ∈ MvPolynomial.vanishingIdeal ℂ (MvPolynomial.zeroLocus ℂ 𝔓) := by
      rw [MvPolynomial.mem_vanishingIdeal_iff]
      intro x hx
      rw [MvPolynomial.aeval_eq_eval]
      by_cases hPiX : MvPolynomial.eval x (conePi N) = 0
      · rw [map_mul, hPiX, mul_zero]
      · -- `x` has every coordinate of `Π` nonzero: rescale each `P¹` factor to the chart `X_{i0}=1`
        rw [eval_conePi] at hPiX
        obtain ⟨hx00, hxprod⟩ := mul_ne_zero_iff.mp hPiX
        have hxi : ∀ i : Fin N, x (i.succ, 0) ≠ 0 ∧ x (i.succ, 1) ≠ 0 := fun i =>
          mul_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp hxprod i (Finset.mem_univ i))
        have hx0 : ∀ i : Fin (N + 1), x (i, 0) ≠ 0 := fun i =>
          Fin.cases hx00 (fun i => (hxi i).1) i
        have hx' : ∀ p ∈ 𝔓, MvPolynomial.eval x p = 0 := fun p hp => by
          have h := hx p hp
          rwa [MvPolynomial.aeval_eq_eval] at h
        set lam : Fin (N + 1) → ℂ := fun i => x (i, 0) with hlam
        set vv : Fin (N + 1) → ℂ := fun i => x (i, 1) * (x (i, 0))⁻¹ with hvv
        -- the rescaled point is again a zero of the multihomogeneous ideal `𝔓`
        have hsub : 𝔓 ≤ ptIdeal N (conePt N vv) := by
          rw [hvv]
          exact ptIdeal_conePt_of_mem_zeroLocus 𝔓 hH x hx0 hx'
        have hvInG : InG vv := by
          rw [hvv]
          intro i
          exact mul_ne_zero (hxi i).2 (inv_ne_zero (hxi i).1)
        -- `x` is the rescaling of the cone point `conePt N vv` by `lam`
        have hscale : (fun v : Fin (N + 1) × Fin 2 => lam v.1 * conePt N vv v) = x := by
          funext v
          obtain ⟨i, j⟩ := v
          fin_cases j <;> simp [hlam, hvv, conePt, mul_comm (x (i, 1)) ((x (i, 0))⁻¹),
            mul_inv_cancel_left₀ (hx0 i) (x (i, 1))]
        have hFx : MvPolynomial.eval x F = 0 := by
          obtain ⟨d, hd⟩ := hFh
          have hkey := eval_scale_homPiece d F hd lam (conePt N vv)
          rw [hscale, hF vv ⟨hvInG, fun H hH' => hsub hH'⟩, mul_zero] at hkey
          exact hkey
        rw [map_mul, hFx, zero_mul]
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical, h𝔓.radical] at h1
    exact h1
  -- `𝔓` is prime, `Π ∉ 𝔓`, so `F ∈ 𝔓`.
  rcases h𝔓.mem_or_mem hmem with h | h
  · exact h
  · exact absurd h hPiNot

end Work.BW
