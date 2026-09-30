import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.subIdealDefs
import Submission.Work.BW.EV_psiMap
import Submission.Work.BW.kerZ_param
import Submission.Work.BW.EV_sep
import Submission.Work.BW.isPrime_of_multiHom

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW multiplicity block B: the split of zero_estimate_stepwise, requests/bw3). Your node is `subIdeal_isPrime`. Its doc comment gives the proof idea, size and dependencies; the design is below. Definitions: Submission.Work.BW.DefsB (imports DefsMult; lead-placed, do not edit). All 18 B-nodes are dispatched in parallel as Submission.Work.BW.<name>. Block-A nodes (rayHilb_poly, refined_bezout, subgroup_rayDeg, multiHom_assPrime, rayDeg_*) are live or proved. IMPORT siblings; never reprove them or restate them under another name. zero_estimate_stepwise (owner H32) is now the ASSEMBLY of these. If you believe your statement is false, give a concrete counterexample.

===== DESIGN_B.md =====
# How `zero_estimate_stepwise` is split into nodes (phase 3, 2026-09-27)

**The statement of `zero_estimate_stepwise` does not change.** It matches the workspace text
byte for byte, and only its proof becomes an assembly.

## Files

* **Definitions.** New definitions are in `DefsB.lean` (no `placeholder`). Install it as
  `Submission/Work/BW/DefsB.lean`, importing `Submission.Work.BW.DefsMult`, in `namespace Work.BW`.
* **Nodes.** There are 19 statement files. Each ends in `:= by placeholder` and has no import or
  namespace lines.
* **What each node file holds.** Its doc comment gives the proof idea, the size in k lines, and
  the dependencies.

## Elaboration check

I ran one check on 3.144 with
`systemd-run --user --scope -q -p MemoryMax=12G ~/.elan/bin/lake env lean /tmp/bwmult/TestB.lean`.
* **Imports.** The file imported Mathlib, `DefsMult`, `subgroup_rayDeg`, `multiHom_assPrime`,
  `rayDeg_bot`, `rayHilb_poly`, `zeroest_defs` and `rayDeg_mono`.
* **Contents.** `DefsB`, then all 19 statements.
* **Result.** 19 `placeholder` warnings, no errors, and no name clashes with those modules.
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

noncomputable section

set_option maxHeartbeats 1000000

set_option linter.unusedVariables false


/-- `subIdeal` is a multihomogeneous ideal.  (This is `Work.BW.multiHom_subIdeal`; it is proved
here because the module `Submission.Work.BW.subgroup_rayDeg` that carries it does not currently
build.) -/
lemma subIdeal_multiHom (N ρ : ℕ) (ε : Bool) (M : Fin ρ → Fin N → ℤ) :
    MultiHom N (subIdeal N ρ ε M) := by
  letI : GradedAlgebra (MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N)) :=
    MvPolynomial.weightedGradedAlgebra ℂ (mdeg N)
  have hgen : ∀ x ∈ {F : MR N | (∃ d, F ∈ homPiece N d) ∧
      ∀ y, InSub N ρ ε M y → MvPolynomial.eval (conePt N y) F = 0},
      SetLike.IsHomogeneousElem (MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N)) x := by
    rintro x ⟨⟨d, hd⟩, -⟩
    exact ⟨d, hd⟩
  have hI : (subIdeal N ρ ε M).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N)) :=
    Ideal.homogeneous_span (MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N)) _ hgen
  intro p hp d
  exact (MvPolynomial.mem_iff_weightedHomogeneousComponent_mem ℂ (mdeg N) hI p).mp hp d

/-- Elements of `subIdeal` vanish at every point of `G'`. -/
lemma subIdeal_vanish {N ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ) {y : Fin (N + 1) → ℂ}
    (hy : InSub N ρ ε M y) {F : MR N} (hF : F ∈ subIdeal N ρ ε M) :
    MvPolynomial.eval (conePt N y) F = 0 := by
  have hle : Ideal.span {G : MR N | (∃ d, G ∈ homPiece N d) ∧
      ∀ z, InSub N ρ ε M z → MvPolynomial.eval (conePt N z) G = 0} ≤
      RingHom.ker (MvPolynomial.eval (conePt N y)) := by
    rw [Ideal.span_le]
    rintro G ⟨-, hGy⟩
    exact hGy y hy
  exact hle hF

/-- `subIdeal` is a proper ideal (`1` does not vanish at the point `(0,1,…,1)` of `G'`). -/
lemma subIdeal_ne_top {N ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ) :
    subIdeal N ρ ε M ≠ ⊤ := by
  intro htop
  have hgone : InSub N ρ ε M (Fin.cons 0 (fun _ : Fin N => 1)) := by
    refine ⟨fun _ => ?_, fun i => ?_, fun j => ?_⟩
    · rw [Fin.cons_zero]
    · rw [Fin.cons_succ]; exact one_ne_zero
    · refine Finset.prod_eq_one (fun i _ => ?_)
      rw [Fin.cons_succ, one_zpow]
  have h1 : (1 : MR N) ∈ subIdeal N ρ ε M := htop ▸ Submodule.mem_top
  have := subIdeal_vanish ε M hgone h1
  rw [map_one] at this
  exact one_ne_zero this

/-- For a multihomogeneous `F`, membership in `subIdeal` is exactly vanishing on `G'`. -/
lemma subIdeal_mem_iff {N ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ) {d : Fin (N + 1) →₀ ℕ}
    {F : MR N} (hF : F ∈ homPiece N d) :
    F ∈ subIdeal N ρ ε M ↔ ∀ y, InSub N ρ ε M y → MvPolynomial.eval (conePt N y) F = 0 :=
  ⟨fun h y hy => subIdeal_vanish ε M hy h, fun h => Ideal.subset_span ⟨⟨d, hF⟩, h⟩⟩


/-- B3a. The ideal of the closure of a connected `G' = G_a^ε × ker 𝒵` (`𝒵` saturated) is prime.
Proof: test on multihomogeneous elements (graded prime criterion); parametrise `ker 𝒵 ≅ (ℂ^×)^{N-ρ}`
through a complement of the saturated `𝒵`, so restrictions to `G'` become Laurent polynomials in
an integral domain. Size 1–1.5k. -/
theorem subIdeal_isPrime {N ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ) (hM : PrimSys M) :
    (subIdeal N ρ ε M).IsPrime := by
  classical
  obtain ⟨c, hc_in, hc_surj⟩ := kerZ_param M hM
  refine isPrime_of_multiHom (subIdeal N ρ ε M) (subIdeal_ne_top ε M)
    (subIdeal_multiHom N ρ ε M) ?_
  -- (H): psi vanishes on all of subIdeal
  have hH : ∀ {F : MR N}, F ∈ subIdeal N ρ ε M → psiMap ε c F = 0 := by
    intro F hmem
    refine EV_sep _ (fun a x => ?_)
    rw [EV_psiMap]
    refine subIdeal_vanish ε M ?_ hmem
    refine ⟨fun hε => ?_, fun i => ?_, fun j => ?_⟩
    · rw [gammaPt, Fin.cons_zero]; simp [hε]
    · rw [gammaPt, Fin.cons_succ]
      exact Finset.prod_ne_zero_iff.mpr
        (fun j _ => zpow_ne_zero _ (by exact_mod_cast Units.ne_zero (x j)))
    · rw [gammaPt]
      have hx := hc_in (fun k => ((x k : ℂˣ) : ℂ))
        (fun k => by exact_mod_cast Units.ne_zero (x k)) j
      simpa only [Fin.cons_succ] using hx
  -- (E): for multihomogeneous F, psi F = 0 forces F into subIdeal
  have hE : ∀ {d : Fin (N + 1) →₀ ℕ} {F : MR N}, F ∈ homPiece N d → psiMap ε c F = 0 →
      F ∈ subIdeal N ρ ε M := by
    intro d F hF hpsi
    refine (subIdeal_mem_iff ε M hF).mpr ?_
    intro y hy
    obtain ⟨T, hTne, hTy⟩ :=
      hc_surj (fun i => y i.succ) (fun i => hy.2.1 i) (fun j => hy.2.2 j)
    set x : Fin (N - ρ) → ℂˣ := fun j => Units.mk0 (T j) (hTne j) with hxdef
    have hval : ∀ j, ((x j : ℂˣ) : ℂ) = T j := fun j => Units.val_mk0 _
    have hpoint : gammaPt ε c (y 0) (fun j => ((x j : ℂˣ) : ℂ)) = y := by
      funext i
      refine Fin.cases ?_ ?_ i
      · rw [gammaPt, Fin.cons_zero]
        cases ε with
        | true => simp
        | false => exact (hy.1 rfl).symm
      · intro k
        rw [gammaPt, Fin.cons_succ]
        rw [show (∏ j : Fin (N - ρ), ((x j : ℂˣ) : ℂ) ^ (c k j))
              = ∏ j : Fin (N - ρ), (T j) ^ (c k j) from
            Finset.prod_congr rfl (fun j _ => by rw [hval j])]
        exact (hTy k).symm
    rw [← hpoint, ← EV_psiMap ε c (y 0) x, hpsi, map_zero]
  -- multihomogeneous product condition
  intro x y hx hy hxy
  obtain ⟨dx, hx⟩ := hx
  obtain ⟨dy, hy⟩ := hy
  have hmul : x * y ∈ homPiece N (dx + dy) := by
    rw [homPiece] at hx hy ⊢
    rw [MvPolynomial.mem_weightedHomogeneousSubmodule] at hx hy ⊢
    exact hx.mul hy
  have hprod : psiMap ε c (x * y) = 0 := hH hxy
  rw [map_mul] at hprod
  rcases mul_eq_zero.mp hprod with h | h
  · exact Or.inl (hE hx h)
  · exact Or.inr (hE hy h)


end

end Work.BW
