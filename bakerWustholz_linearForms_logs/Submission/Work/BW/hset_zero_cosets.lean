import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.hset_zero_cosets_aux
import Submission.Work.BW.transl_basic
import Submission.Work.BW.rayHilb_transl
import Submission.Work.BW.rayDim_lt_of_lt
import Submission.Work.BW.multiHom_assPrime

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW multiplicity block B: the split of zero_estimate_stepwise, requests/bw3). Your node is `hset_zero_cosets`. Its doc comment gives the proof idea, size and dependencies; the design is below. Definitions: Submission.Work.BW.DefsB (imports DefsMult; lead-placed, do not edit). All 18 B-nodes are dispatched in parallel as Submission.Work.BW.<name>. Block-A nodes (rayHilb_poly, refined_bezout, subgroup_rayDeg, multiHom_assPrime, rayDeg_*) are live or proved. IMPORT siblings; never reprove them or restate them under another name. zero_estimate_stepwise (owner H32) is now the ASSEMBLY of these. If you believe your statement is false, give a concrete counterexample.

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

/-- §5.1(c), finiteness. If `𝔓` is a minimal prime of `I` through `G` of maximal dimension among
those, `H_V(0)` is covered by finitely many cosets of the stabiliser: for `g ∈ H_V(0)`,
`I ≤ τ_{g⁻¹} 𝔓`, which is a prime through `G` of the same `rayDim` (`rayHilb_transl`), hence a
minimal prime of `I` (`rayDim_lt_of_lt`, `rayPoly_ne_zero_of_meetsG`); minimal primes are finite
and `g, g'` giving the same prime differ by `stabG 𝔓`. Size 1–1.5k. -/
theorem hset_zero_cosets {N q : ℕ} (D : Fin (N + 1) → ℕ) (hD : ∀ i, 1 ≤ D i)
    (w : Fin q → Fin (N + 1) → ℂ) (I 𝔓 : Ideal (MR N)) (hI : MultiHom N I)
    (h𝔓 : 𝔓.IsPrime) (hmin : 𝔓 ∈ I.minimalPrimes) (hG : MeetsG N 𝔓)
    (hmax : ∀ p ∈ I.minimalPrimes, MeetsG N p → rayDim N (fsD D) p ≤ rayDim N (fsD D) 𝔓) :
    ∃ F : Finset (Fin (N + 1) → ℂ), Hset w 𝔓 I 0 ⊆ ⋃ f ∈ F, gmul f '' stabG 𝔓 := by
  classical
  have hD' : ∀ i, 1 ≤ fsD D i := fun i => by simpa [fsD] using hD i
  set Φ : (Fin (N + 1) → ℂ) → Ideal (MR N) := fun g => Ideal.map (transl (ginv g)) 𝔓 with hΦdef
  -- Step A: for `g ∈ H_V(0)`, `Φ g` is a minimal prime of `I` of maximal dimension.
  have hkey : ∀ g ∈ Hset w 𝔓 I 0, Φ g ∈ I.minimalPrimes := by
    intro g hg
    have hgG : InG g := hg.1
    have hginvG : InG (ginv g) := hsc_inG_ginv hgG
    have hle : I ≤ Φ g := by
      intro F hF
      have h1 : transl g F ∈ 𝔓 := hsc_Hset_transl_mem hg hF
      rw [← hsc_transl_inv hgG F]
      exact Ideal.mem_map_of_mem (transl (ginv g)) h1
    have hprime : (Φ g).IsPrime := hsc_map_ginv_isPrime hgG h𝔓
    have hmeets : MeetsG N (Φ g) := hsc_meetsG_map_ginv hgG hG
    have hhom : MultiHom N (Φ g) :=
      hsc_MultiHom_map_transl (hsc_multiHom_minimalPrimes hI hmin) hginvG
    have hdim : rayDim N (fsD D) (Φ g) = rayDim N (fsD D) 𝔓 :=
      (rayHilb_transl (fsD D) (ginv g) hginvG 𝔓).2.1
    refine ⟨⟨hprime, hle⟩, ?_⟩
    intro r hr hrle
    by_contra hnot
    haveI : r.IsPrime := hr.1
    obtain ⟨q, hqmem, hqle⟩ := Ideal.exists_minimalPrimes_le (I := I) (J := r) hr.2
    have hqr : q ≤ Φ g := le_trans hqle hrle
    have hqlt : q < Φ g :=
      lt_of_le_of_ne hqr fun hcontra => hnot (hcontra ▸ hqle)
    have hqprime : q.IsPrime := hqmem.1.1
    have hqhom : MultiHom N q := hsc_multiHom_minimalPrimes hI hqmem
    have hqmeets : MeetsG N q := hsc_meetsG_mono hqr hmeets
    -- `Φ g` meets `G`, so its ray Hilbert function is `≥ 1` for all `t`, and its ray Hilbert
    -- polynomial (which exists by multigraded Hilbert–Samuel, `hsc_isRayPoly_of_multiHom`) is
    -- therefore not the zero polynomial.
    have hrayΦ : rayPoly N (fsD D) (Φ g) ≠ 0 := by
      obtain ⟨P, hP⟩ := hsc_isRayPoly_of_multiHom (fsD D) hD' (Φ g) hhom
      rw [rayPoly_eq hP]
      intro hP0
      obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hP
      have h1 : ((rayHilb N (fsD D) (Φ g) (max a 1) : ℕ) : ℚ) =
          P.eval ((max a 1 : ℕ) : ℚ) := ha _ (le_max_left _ _)
      rw [hP0] at h1
      simp at h1
      have h2 : 1 ≤ rayHilb N (fsD D) (Φ g) (max a 1) :=
        hsc_rayHilb_pos_of_meetsG (fsD D) (Φ g) hmeets _
      have h3 : (1 : ℚ) ≤ ((rayHilb N (fsD D) (Φ g) (max a 1) : ℕ) : ℚ) := by
        exact_mod_cast h2
      linarith
    have hlt := rayDim_lt_of_lt (fsD D) hD' q (Φ g) hqprime hprime hqhom hhom hqlt hrayΦ
    have hmaxq := hmax q hqmem hqmeets
    rw [hdim] at hlt
    omega
  -- Step B: finitely many representatives.
  have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing (MR N) I
  let rep : Ideal (MR N) → (Fin (N + 1) → ℂ) := fun p =>
    if h : ∃ g : Fin (N + 1) → ℂ, g ∈ Hset w 𝔓 I 0 ∧ Φ g = p then
      Classical.choose h else gone N
  have hrep : ∀ p (h : ∃ g : Fin (N + 1) → ℂ, g ∈ Hset w 𝔓 I 0 ∧ Φ g = p),
      rep p ∈ Hset w 𝔓 I 0 ∧ Φ (rep p) = p := by
    intro p h
    have hch : rep p = Classical.choose h := by
      show (if h' : ∃ g : Fin (N + 1) → ℂ, g ∈ Hset w 𝔓 I 0 ∧ Φ g = p then
          Classical.choose h' else gone N) = Classical.choose h
      rw [dif_pos h]
    rw [hch]
    exact Classical.choose_spec h
  refine ⟨hfin.toFinset.image rep, ?_⟩
  intro g hg
  have hgmin : Φ g ∈ I.minimalPrimes := hkey g hg
  have hex : ∃ g' : Fin (N + 1) → ℂ, g' ∈ Hset w 𝔓 I 0 ∧ Φ g' = Φ g := ⟨g, hg, rfl⟩
  have hspec := hrep (Φ g) hex
  refine Set.mem_iUnion.mpr ⟨rep (Φ g), Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
  · exact Finset.mem_image.mpr ⟨Φ g, hfin.mem_toFinset.mpr hgmin, rfl⟩
  · exact hsc_mem_coset hspec.1.1 hg.1 hspec.2


end Work.BW
