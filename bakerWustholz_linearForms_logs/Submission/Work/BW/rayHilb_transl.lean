import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.rayPoly_eq
import Submission.Work.BW.transl_basic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW multiplicity block B: the split of zero_estimate_stepwise, requests/bw3). Your node is `rayHilb_transl`. Its doc comment gives the proof idea, size and dependencies; the design is below. Definitions: Submission.Work.BW.DefsB (imports DefsMult; lead-placed, do not edit). All 18 B-nodes are dispatched in parallel as Submission.Work.BW.<name>. Block-A nodes (rayHilb_poly, refined_bezout, subgroup_rayDeg, multiHom_assPrime, rayDeg_*) are live or proved. IMPORT siblings; never reprove them or restate them under another name. zero_estimate_stepwise (owner H32) is now the ASSEMBLY of these. If you believe your statement is false, give a concrete counterexample.

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

private lemma transl_gone_aux {N : ℕ} (F : MR N) : transl (gone N) F = F := by
  have hφ : (fun v : Fin (N + 1) × Fin 2 =>
        if v.2 = 0 then X v
        else if v.1 = 0 then X v + C ((gone N) 0) * X (0, 0)
        else C ((gone N) v.1) * X v) = (fun v => X v) := by
    funext v
    obtain ⟨i, j⟩ := v
    fin_cases j
    · simp
    · rcases Fin.eq_zero_or_eq_succ i with h | ⟨k, rfl⟩
      · simp [h, gone]
      · simp [gone]
  rw [transl, hφ, MvPolynomial.aeval_X_left_apply]

private lemma gmul_ginv_aux {N : ℕ} (g : Fin (N + 1) → ℂ) (hg : InG g) :
    gmul g (ginv g) = gone N := by
  ext i
  induction i using Fin.cases with
  | zero => simp [gmul, ginv, gone]
  | succ j => simp [gmul, ginv, gone, hg j]

private lemma rayHilb_eq_of_algEquiv_aux {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (I : Ideal (MR N))
    (φ ψ : MR N →ₐ[ℂ] MR N)
    (hpres : ∀ d F, F ∈ homPiece N d → φ F ∈ homPiece N d)
    (hpres' : ∀ d F, F ∈ homPiece N d → ψ F ∈ homPiece N d)
    (hφψ : ∀ F, ψ (φ F) = F) (hψφ : ∀ F, φ (ψ F) = F) (t : ℕ) :
    rayHilb N D (Ideal.map φ I) t = rayHilb N D I t := by
  have hsurj : Function.Surjective φ := fun y => ⟨ψ y, hψφ y⟩
  unfold rayHilb
  set M : Submodule ℂ (MR N) := homPiece N (t • D) with hM
  set P : Submodule ℂ ↥M := Submodule.comap M.subtype (I.restrictScalars ℂ) with hP
  set Q : Submodule ℂ ↥M :=
    Submodule.comap M.subtype ((Ideal.map φ I).restrictScalars ℂ) with hQ
  let eM : ↥M ≃ₗ[ℂ] ↥M :=
    { toFun := fun x => ⟨φ x.1, hpres (t • D) x.1 x.2⟩
      invFun := fun x => ⟨ψ x.1, hpres' (t • D) x.1 x.2⟩
      map_add' := by intro x y; ext; simp
      map_smul' := by intro c x; ext; simp
      left_inv := by intro x; apply Subtype.ext; show ψ (φ x.1) = x.1; exact hφψ x.1
      right_inv := by intro x; apply Subtype.ext; show φ (ψ x.1) = x.1; exact hψφ x.1 }
  have heMval : ∀ x : ↥M, ((eM : ↥M →ₗ[ℂ] ↥M) x : MR N) = φ x.1 := fun x => rfl
  have hmap : Submodule.map (eM : ↥M →ₗ[ℂ] ↥M) P = Q := by
    ext x
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨y, hyP, hyx⟩
      have hyI : (y : MR N) ∈ I := Submodule.mem_comap.mp hyP
      have hxval : (x : MR N) = φ (y : MR N) := by
        have h1 : ((eM : ↥M →ₗ[ℂ] ↥M) y : MR N) = (x : MR N) := congrArg Subtype.val hyx
        rw [heMval y] at h1
        exact h1.symm
      have hmem : (x : MR N) ∈ Ideal.map φ I := by
        rw [hxval]
        exact Ideal.mem_map_of_mem φ hyI
      exact Submodule.mem_comap.mpr hmem
    · intro hx
      have hx' : (x : MR N) ∈ Ideal.map φ I := Submodule.mem_comap.mp hx
      obtain ⟨y, hyI, hyeq⟩ := (Ideal.mem_map_iff_of_surjective φ hsurj).mp hx'
      have hyM : y ∈ M := by
        have hy_eq : y = ψ (x : MR N) := by rw [← hφψ y, hyeq]
        rw [hy_eq]
        exact hpres' (t • D) x.1 x.2
      refine ⟨⟨y, hyM⟩, ?_, ?_⟩
      · exact hyI
      · apply Subtype.ext
        rw [heMval]
        exact hyeq
  exact LinearEquiv.finrank_eq (Submodule.Quotient.equiv P Q eM hmap).symm

private lemma rayPoly_congr_aux {N : ℕ} {D : Fin (N + 1) →₀ ℕ} {I I' : Ideal (MR N)}
    (h : ∀ t, rayHilb N D I' t = rayHilb N D I t) : rayPoly N D I' = rayPoly N D I := by
  have hiff : ∀ q, IsRayPoly N D I' q ↔ IsRayPoly N D I q := by
    intro q
    simp only [IsRayPoly]
    constructor
    · intro hq
      filter_upwards [hq] with t ht
      rwa [← h t]
    · intro hq
      filter_upwards [hq] with t ht
      rwa [h t]
  by_cases hex : ∃ q, IsRayPoly N D I q
  · have hq : IsRayPoly N D I (Classical.choose hex) := Classical.choose_spec hex
    have hI : rayPoly N D I = Classical.choose hex := rayPoly_eq hq
    have hq' : IsRayPoly N D I' (Classical.choose hex) := (hiff _).mpr hq
    have hI' : rayPoly N D I' = Classical.choose hex := rayPoly_eq hq'
    rw [hI, hI']
  · have hI : rayPoly N D I = 0 := by
      unfold rayPoly
      rw [dite_eq_right (show ¬ (∃ q, IsRayPoly N D I q) from hex)]
    have hex' : ¬ ∃ q, IsRayPoly N D I' q := by
      rintro ⟨q, hq⟩
      exact hex ⟨q, (hiff q).mp hq⟩
    have hI' : rayPoly N D I' = 0 := by
      unfold rayPoly
      rw [dite_eq_right (show ¬ (∃ q, IsRayPoly N D I' q) from hex')]
    rw [hI, hI']

/-- B1d (Philippon 4.5 with `c_i = 1`). Translation by `g ∈ G` is a graded automorphism, so it
preserves ray Hilbert functions, hence `rayDim` and `rayDeg`. Size 0.4–0.8k. -/
theorem rayHilb_transl {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (g : Fin (N + 1) → ℂ) (hg : InG g)
    (I : Ideal (MR N)) :
    (∀ t, rayHilb N D (Ideal.map (transl g) I) t = rayHilb N D I t) ∧
      rayDim N D (Ideal.map (transl g) I) = rayDim N D I ∧
      rayDeg N D (Ideal.map (transl g) I) = rayDeg N D I := by
  have htb1 := transl_basic g (ginv g)
  have htb2 := transl_basic (ginv g) g
  have hpres_g : ∀ d F, F ∈ homPiece N d → transl g F ∈ homPiece N d := htb1.2.2.2.1
  have hpres_i : ∀ d F, F ∈ homPiece N d → transl (ginv g) F ∈ homPiece N d := htb2.2.2.2.1
  have hcomp1 : ∀ F, transl g (transl (ginv g) F) = transl (gmul g (ginv g)) F := htb1.2.2.1
  have hinv : ∀ F, transl (ginv g) (transl g F) = F := htb1.2.2.2.2 hg
  have hgmul : gmul g (ginv g) = gone N := gmul_ginv_aux g hg
  have hcomp2 : ∀ F, transl g (transl (ginv g) F) = F := by
    intro F
    rw [hcomp1 F, hgmul]
    exact transl_gone_aux F
  have hfin : ∀ t, rayHilb N D (Ideal.map (transl g) I) t = rayHilb N D I t :=
    fun t => rayHilb_eq_of_algEquiv_aux D I (transl g) (transl (ginv g)) hpres_g hpres_i
      hinv hcomp2 t
  have hpoly : rayPoly N D (Ideal.map (transl g) I) = rayPoly N D I := rayPoly_congr_aux hfin
  exact ⟨hfin, by rw [rayDim, rayDim, hpoly], by rw [rayDeg, rayDeg, hpoly]⟩


end Work.BW
