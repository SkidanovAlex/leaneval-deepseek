import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.stabAux
import Submission.Work.BW.transl_basic
import Submission.Work.BW.cruxPolyEval
import Submission.Work.BW.invSubEval

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! LEAD NOTES (BW multiplicity block B: the split of zero_estimate_stepwise, requests/bw3). Your node is `stab_closedSub`. Its doc comment gives the proof idea, size and dependencies; the design is below. Definitions: Submission.Work.BW.DefsB (imports DefsMult; lead-placed, do not edit). All 18 B-nodes are dispatched in parallel as Submission.Work.BW.<name>. Block-A nodes (rayHilb_poly, refined_bezout, subgroup_rayDeg, multiHom_assPrime, rayDeg_*) are live or proved. IMPORT siblings; never reprove them or restate them under another name. zero_estimate_stepwise (owner H32) is now the ASSEMBLY of these. If you believe your statement is false, give a concrete counterexample.

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
  the minimal primes through `G`". `chain_first_stable` supplies it.-/

namespace Work.BW

/-! ### Basic facts about `transl` and the group law -/

/-- `transl (gone N)` fixes every coordinate variable. -/
lemma stabG_transl_gone_X {N : ℕ} (v : Fin (N + 1) × Fin 2) :
    transl (gone N) (MvPolynomial.X v) = MvPolynomial.X v := by
  obtain ⟨a, b⟩ := v
  by_cases h2 : b = 0
  · simp [transl, h2]
  · by_cases h1 : a = 0
    · simp [transl, h2, h1, gone]
    · obtain ⟨j, hj⟩ := (Fin.eq_zero_or_eq_succ a).resolve_left h1
      subst hj
      simp [transl, h2, Fin.succ_ne_zero, gone]

/-- `transl (gone N)` is the identity. -/
lemma stabG_transl_gone {N : ℕ} : (transl (gone N) : MR N →+* MR N) = RingHom.id (MR N) := by
  refine RingHom.ext (fun F => ?_)
  have h : transl (gone N : Fin (N + 1) → ℂ) = AlgHom.id ℂ (MR N) := by
    apply MvPolynomial.algHom_ext
    intro v
    exact stabG_transl_gone_X v
  simpa using congrArg (fun f : MR N →ₐ[ℂ] MR N => f F) h

/-- `transl` respects the group law. -/
lemma stabG_transl_comp {N : ℕ} (g h : Fin (N + 1) → ℂ) :
    (transl g : MR N →+* MR N).comp (transl h : MR N →+* MR N) =
      (transl (gmul g h) : MR N →+* MR N) :=
  RingHom.ext (fun F => (transl_basic g h).2.2.1 F)

/-- Bridge: `Ideal.map` only sees the underlying function, not the coercion of `transl`. -/
lemma stabG_map_coe {N : ℕ} (g : Fin (N + 1) → ℂ) (I : Ideal (MR N)) :
    Ideal.map (transl g) I = Ideal.map (transl g : MR N →+* MR N) I := rfl

/-- `Ideal.map` of a composed ring homomorphism. -/
lemma stabG_map_comp {N : ℕ} (f g : MR N →+* MR N) (I : Ideal (MR N)) :
    Ideal.map (g.comp f) I = Ideal.map g (Ideal.map f I) :=
  (Ideal.map_map f g).symm

/-- `(transl g⁻¹) ∘ (transl g) = id` on `G`. -/
lemma stabG_transl_ginv_left {N : ℕ} (g : Fin (N + 1) → ℂ) (hg : InG g) :
    (transl (ginv g) : MR N →+* MR N).comp (transl g : MR N →+* MR N) = RingHom.id (MR N) :=
  RingHom.ext (fun F => (transl_basic g g).2.2.2.2 hg F)

lemma stabG_ginv_ginv {N : ℕ} (g : Fin (N + 1) → ℂ) : ginv (ginv g) = g := by
  funext i
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, rfl⟩
  · rw [h, ginv, Fin.cons_zero, ginv, Fin.cons_zero, neg_neg]
  · rw [ginv, Fin.cons_succ, ginv, Fin.cons_succ, inv_inv]

lemma stabG_inG_ginv {N : ℕ} {g : Fin (N + 1) → ℂ} (hg : InG g) : InG (ginv g) :=
  fun i => by
    have : ginv g i.succ = (g i.succ)⁻¹ := by rw [ginv, Fin.cons_succ]
    rw [this]
    exact inv_ne_zero (hg i)

lemma stabG_inG_gmul {N : ℕ} {a b : Fin (N + 1) → ℂ} (ha : InG a) (hb : InG b) :
    InG (gmul a b) :=
  fun i => by
    have : gmul a b i.succ = a i.succ * b i.succ := by rw [gmul, Fin.cons_succ]
    rw [this]
    exact mul_ne_zero (ha i) (hb i)

/-- `(transl g) ∘ (transl g⁻¹) = id` on `G`. -/
lemma stabG_transl_ginv_right {N : ℕ} (g : Fin (N + 1) → ℂ) (hg : InG g) :
    (transl g : MR N →+* MR N).comp (transl (ginv g) : MR N →+* MR N) = RingHom.id (MR N) := by
  have h := stabG_transl_ginv_left (ginv g) (stabG_inG_ginv hg)
  rwa [stabG_ginv_ginv] at h

/-- One-sided stability at `y` upgrades to one-sided stability at `y⁻¹`. -/
lemma stabG_map_ginv {N : ℕ} (𝔓 : Ideal (MR N)) {y : Fin (N + 1) → ℂ} (hy : InG y)
    (h : Ideal.map (transl y) 𝔓 = 𝔓) : Ideal.map (transl (ginv y)) 𝔓 = 𝔓 := by
  have h' : Ideal.map (transl y : MR N →+* MR N) 𝔓 = 𝔓 := by
    simpa only [stabG_map_coe] using h
  have key := congrArg (Ideal.map (transl (ginv y) : MR N →+* MR N)) h'
  rw [← stabG_map_comp (transl y : MR N →+* MR N) (transl (ginv y) : MR N →+* MR N),
    stabG_transl_ginv_left y hy, Ideal.map_id] at key
  simpa only [stabG_map_coe] using key.symm

lemma stabG_mem_of_forall_dual {N : ℕ} (𝔓 : Ideal (MR N)) {v : MR N}
    (h : ∀ φ : MR N →ₗ[ℂ] ℂ, (∀ z ∈ 𝔓, φ z = 0) → φ v = 0) : v ∈ 𝔓 := by
  have key : (∀ φ ∈ Submodule.dualAnnihilator (Submodule.restrictScalars ℂ 𝔓), φ v = 0) ↔
      v ∈ Submodule.restrictScalars ℂ 𝔓 :=
    Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff _ v
  exact key.mp (fun φ hφ => h φ (fun z hz => (Submodule.mem_dualAnnihilator φ).mp hφ z hz))

/-! ### The equations cutting out the stabiliser -/

/-- Degree bound clearing the powers `gᵢ⁻¹` occurring in `eval (ginv ·) q`. -/
noncomputable def stabG_boundK {N : ℕ} (q : MvPolynomial (Fin (N + 1)) ℂ) : ℕ :=
  ∑ s ∈ q.support, ∑ i : Fin N, s i.succ

lemma stabG_boundK_spec {N : ℕ} (q : MvPolynomial (Fin (N + 1)) ℂ) :
    ∀ s ∈ q.support, ∀ i : Fin N, s i.succ ≤ stabG_boundK q := by
  intro s hs i
  have h1 : s i.succ ≤ ∑ j : Fin N, s j.succ :=
    Finset.single_le_sum (f := fun j : Fin N => s j.succ) (s := Finset.univ)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have h2 : (∑ j : Fin N, s j.succ) ≤ stabG_boundK q :=
    Finset.single_le_sum (f := fun s' : Fin (N + 1) →₀ ℕ => ∑ j : Fin N, s' j.succ)
      (s := q.support) (fun s' _ => Nat.zero_le _) hs
  exact le_trans h1 h2

/-- The equations cutting out `stabG 𝔓` in `G`. -/
noncomputable def stabG_eqns {N : ℕ} (𝔓 : Ideal (MR N)) : Set (MvPolynomial (Fin (N + 1)) ℂ) :=
  {q | ∃ (F : MR N) (_ : F ∈ 𝔓) (μ : MR N →ₗ[ℂ] ℂ), (∀ y ∈ 𝔓, μ y = 0) ∧ q = cruxPoly F μ} ∪
  {p | ∃ (F : MR N) (_ : F ∈ 𝔓) (μ : MR N →ₗ[ℂ] ℂ), (∀ y ∈ 𝔓, μ y = 0) ∧
        p = invSub (stabG_boundK (cruxPoly F μ)) (cruxPoly F μ)}

/-! ### Main theorem -/

/-- B2d. The stabiliser of a multihomogeneous ideal is a closed subgroup of `G`. Proof:
`g ∈ stabG 𝔓 ⇔ τ_g 𝔓 ≤ 𝔓 ∧ τ_{g⁻¹} 𝔓 ≤ 𝔓`; for each homogeneous generator `F` of degree `d`,
`τ_g F ∈ 𝔓 ∩ R_d` is a set of linear conditions on coefficients polynomial in `g` (in `g⁻¹` for
the second, cleared by powers of the `gᵢ`). Size 1–2k. -/
theorem stab_closedSub {N : ℕ} (𝔓 : Ideal (MR N)) (hH : MultiHom N 𝔓) :
    IsClosedSubG (stabG 𝔓) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro y hy; exact hy.1
  · refine ⟨fun i => by simp [gone], ?_⟩
    simp only [stabG_map_coe, stabG_transl_gone, Ideal.map_id]
  · rintro a ⟨haG, haP⟩ b ⟨hbG, hbP⟩
    have haP' : Ideal.map (transl a : MR N →+* MR N) 𝔓 = 𝔓 := by
      simpa only [stabG_map_coe] using haP
    have hbP' : Ideal.map (transl b : MR N →+* MR N) 𝔓 = 𝔓 := by
      simpa only [stabG_map_coe] using hbP
    refine ⟨stabG_inG_gmul haG hbG, ?_⟩
    simp only [stabG_map_coe]
    rw [← stabG_transl_comp a b,
      stabG_map_comp (transl b : MR N →+* MR N) (transl a : MR N →+* MR N), hbP', haP']
  · rintro a ⟨haG, haP⟩
    exact ⟨stabG_inG_ginv haG, stabG_map_ginv 𝔓 haG haP⟩
  · refine ⟨stabG_eqns 𝔓, ?_⟩
    ext y
    constructor
    · rintro ⟨hyG, hyP⟩
      refine ⟨hyG, fun f hf => ?_⟩
      rcases hf with ⟨F, hF, μ, hμ, rfl⟩ | ⟨F, hF, μ, hμ, rfl⟩
      · rw [cruxPolyEval]
        exact hμ _ (hyP ▸ Ideal.mem_map_of_mem (transl y) hF)
      · have hmem : transl (ginv y) F ∈ 𝔓 :=
          (stabG_map_ginv 𝔓 hyG hyP) ▸ Ideal.mem_map_of_mem (transl (ginv y)) hF
        rw [invSubEval (q := cruxPoly F μ) (K := stabG_boundK (cruxPoly F μ))
          (hK := stabG_boundK_spec _) (g := y) (hg := hyG), cruxPolyEval, hμ _ hmem, mul_zero]
    · rintro ⟨hyG, hz⟩
      have hle : Ideal.map (transl y) 𝔓 ≤ 𝔓 := by
        rw [Ideal.map_le_iff_le_comap]
        intro F hF
        rw [Ideal.mem_comap]
        refine stabG_mem_of_forall_dual 𝔓 (fun φ hφ0 => ?_)
        rw [← cruxPolyEval F φ y]
        exact hz _ (Or.inl ⟨F, hF, φ, hφ0, rfl⟩)
      have hle' : Ideal.map (transl (ginv y)) 𝔓 ≤ 𝔓 := by
        rw [Ideal.map_le_iff_le_comap]
        intro F hF
        rw [Ideal.mem_comap]
        refine stabG_mem_of_forall_dual 𝔓 (fun φ hφ0 => ?_)
        have hq : (∏ i : Fin N, (y i.succ) ^ (stabG_boundK (cruxPoly F φ))) *
            φ (transl (ginv y) F) = 0 := by
          rw [← cruxPolyEval F φ (ginv y), ← invSubEval (q := cruxPoly F φ)
            (K := stabG_boundK (cruxPoly F φ)) (hK := stabG_boundK_spec _) (g := y) (hg := hyG)]
          exact hz _ (Or.inr ⟨F, hF, φ, hφ0, rfl⟩)
        exact (mul_eq_zero.mp hq).resolve_left
          (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hyG i)))
      have hle'' : Ideal.map (transl (ginv y) : MR N →+* MR N) 𝔓 ≤ 𝔓 := by
        simpa only [stabG_map_coe] using hle'
      refine ⟨hyG, le_antisymm (by simpa only [stabG_map_coe] using hle) ?_⟩
      have hge : 𝔓 ≤ Ideal.map (transl y : MR N →+* MR N) 𝔓 := by
        calc 𝔓 = Ideal.map ((transl y : MR N →+* MR N).comp (transl (ginv y))) 𝔓 := by
                rw [stabG_transl_ginv_right y hyG, Ideal.map_id]
          _ = Ideal.map (transl y : MR N →+* MR N)
                (Ideal.map (transl (ginv y) : MR N →+* MR N) 𝔓) :=
                stabG_map_comp (transl (ginv y) : MR N →+* MR N) (transl y : MR N →+* MR N) 𝔓
          _ ≤ Ideal.map (transl y : MR N →+* MR N) 𝔓 := Ideal.map_mono hle''
      simpa only [stabG_map_coe] using hge

end Work.BW
