import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.subgroup_rayDegAux
import Submission.Work.BW.charPoly_spec
import Submission.Work.BW.eval_scale_of_isWeightedHomogeneous
import Submission.Work.BW.sum_minimalPrimes_le
import Submission.Work.BW.primLen_ne_top
import Submission.Work.BW.derH_basic
import Submission.Work.BW.derH_comm
import Submission.Work.BW.derH_transl
import Submission.Work.BW.homog_basic
import Submission.Work.BW.foldr_two
import Submission.Work.BW.transl_basic
import Submission.Work.BW.vanish_span
import Submission.Work.BW.rayHilb_transl
import Submission.Work.BW.hset_contains_steps
import Submission.Work.BW.mem_of_vanish_ZG
import Submission.Work.BW.rayPoly_ne_zero_of_meetsG
import Submission.Work.BW.stab_closedSub
import Submission.Work.BW.closedSub_structure
import Submission.Work.BW.subIdeal_isPrime

-- (not needed at this node: `rayDeg_nonneg_aux` gives the nonnegativity of `rayDeg`)
-- (not needed at this node: `hmax` is a hypothesis of `stab_step`)
import Submission.Work.BW.coset_minimalPrime
import Submission.Work.BW.coset_length
import Submission.Work.BW.hset_zero_cosets
import Submission.Work.BW.rayDeg_bot
import Submission.Work.BW.rayDim_lt_of_lt
import Submission.Work.BW.multiHom_assPrime
-- import Submission.Work.BW.rayDeg_mono
-- (not needed: `rayPoly_ne_zero_of_meetsG` imports it itself)
import Submission.Work.BW.zeroest_defs

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW multiplicity block B: the split of zero_estimate_stepwise, requests/bw3). Your node is `stab_step`. Its doc comment gives the proof idea, size and dependencies; the design is below. Definitions: Submission.Work.BW.DefsB (imports DefsMult; lead-placed, do not edit). All 18 B-nodes are dispatched in parallel as Submission.Work.BW.<name>. Block-A nodes (rayHilb_poly, refined_bezout, subgroup_rayDeg, multiHom_assPrime, rayDeg_*) are live or proved. IMPORT siblings; never reprove them or restate them under another name. zero_estimate_stepwise (owner H32) is now the ASSEMBLY of these. If you believe your statement is false, give a concrete counterexample.

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

set_option maxHeartbeats 1000000




/-! ## Structural preliminaries for `stab_step`

These are the pieces of the §5.1 bookkeeping that are not already provided by the block-B
sibling nodes: the group law on `G = G_a × G_m^N`, the fact that `transl` by the neutral
element is the identity, monotonicity of the chain ideals and of the sets `H_V(t)`, and the
identification `Z(I(G')) ∩ G = G'` for the connected subgroup `G' = G_a^ε × ker 𝒵`.
-/

section GroupLaw

variable {N : ℕ}

theorem gmul_comm (a b : Fin (N + 1) → ℂ) : gmul a b = gmul b a := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp only [gmul, Fin.cons_zero]
    ring
  · intro i
    simp only [gmul, Fin.cons_succ]
    ring

theorem gmul_assoc (a b c : Fin (N + 1) → ℂ) :
    gmul (gmul a b) c = gmul a (gmul b c) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp only [gmul, Fin.cons_zero]
    ring
  · intro i
    simp only [gmul, Fin.cons_succ]
    ring

theorem gmul_gone_left (g : Fin (N + 1) → ℂ) : gmul (gone N) g = g := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp [gmul, gone]
  · intro i
    simp [gmul, gone]

theorem gmul_gone_right (g : Fin (N + 1) → ℂ) : gmul g (gone N) = g := by
  rw [gmul_comm, gmul_gone_left]

theorem ginv_gone : ginv (gone N) = gone N := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp [ginv, gone]
  · intro i
    simp [ginv, gone]

theorem gone_mem_InG : InG (gone N) := by
  intro i
  have h : gone N i.succ = (1 : ℂ) := by
    simpa [gone] using (Fin.cons_succ (0 : ℂ) (fun _ : Fin N => (1 : ℂ)) i)
  rw [h]
  exact one_ne_zero

theorem gone_mem_InSub (ρ : ℕ) (ε : Bool) (M : Fin ρ → Fin N → ℤ) :
    InSub N ρ ε M (gone N) := by
  refine ⟨?_, ?_, ?_⟩
  · intro _
    exact rfl
  · intro i
    exact one_ne_zero
  · intro j
    exact Finset.prod_eq_one fun i _ => by simp [gone]

end GroupLaw

section TranslGone

variable {N : ℕ}

theorem transl_gone_apply (F : MR N) : transl (gone N) F = F := by
  have hX : ∀ v : Fin (N + 1) × Fin 2,
      transl (gone N) (MvPolynomial.X v) = MvPolynomial.X v := by
    intro v
    obtain ⟨i, j⟩ := v
    rw [transl, MvPolynomial.aeval_X]
    fin_cases j
    · simp
    · refine Fin.cases ?_ ?_ i
      · simp [gone]
      · intro k
        simp [gone]
  have h : transl (gone N) = AlgHom.id ℂ (MR N) :=
    MvPolynomial.algHom_ext fun v => by simpa [AlgHom.id_apply] using hX v
  rw [h]
  rfl

end TranslGone

section Mono

variable {N q : ℕ}

theorem chainGen_mono (w : Fin q → Fin (N + 1) → ℂ) (θ : Fin N → ℂ)
    (D : Fin (N + 1) → ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) {A B A' B' : ℕ}
    (hA : A ≤ A') (hB : B ≤ B') :
    chainGen w θ D P A B ⊆ chainGen w θ D P A' B' := by
  rintro F ⟨s, t, hs, ht, rfl⟩
  exact ⟨s, t, le_trans hs hA, le_trans ht hB, rfl⟩

theorem chainIdeal_mono (w : Fin q → Fin (N + 1) → ℂ) (θ : Fin N → ℂ)
    (D : Fin (N + 1) → ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) {A B A' B' : ℕ}
    (hA : A ≤ A') (hB : B ≤ B') :
    chainIdeal w θ D P A B ≤ chainIdeal w θ D P A' B' :=
  Ideal.span_le.mpr fun F hF => Ideal.subset_span (chainGen_mono w θ D P hA hB hF)

theorem Hset_mono (w : Fin q → Fin (N + 1) → ℂ) (𝔓 I : Ideal (MR N)) {t t' : ℕ}
    (h : t' ≤ t) : Hset w 𝔓 I t ⊆ Hset w 𝔓 I t' := by
  rintro g ⟨hg, hcond⟩
  exact ⟨hg, fun F hF t'' ht'' => hcond F hF t'' (le_trans ht'' h)⟩

end Mono



section HsetFacts

variable {N q : ℕ}

theorem gone_mem_hset (w : Fin q → Fin (N + 1) → ℂ) (θ : Fin N → ℂ)
    (D : Fin (N + 1) → ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) (A B S T : ℕ)
    (𝔓 : Ideal (MR N)) (h2 : chainIdeal w θ D P (A + S) (B + T) ≤ 𝔓) :
    gone N ∈ Hset w 𝔓 (chainIdeal w θ D P A B) T := by
  refine ⟨gone_mem_InG, ?_⟩
  intro F hF t ht
  have hv : transl (gone N) (applyH w t F) ∈ 𝔓 :=
    vanish_span w (gone N) T 𝔓 (chainGen w θ D P A B) ?_ F hF t ht
  · simpa [transl_gone_apply] using hv
  intro F₀ hF₀ t₀ ht₀
  obtain ⟨s'', t'', hs'', ht'', rfl⟩ := hF₀
  rw [transl_gone_apply]
  rw [← (derH_basic w).2.2.1 (ptTheta θ s'') t₀ (applyH w t'' (homog D P))]
  rw [(derH_basic w).2.1 t₀ t'' (homog D P)]
  refine h2 (Ideal.subset_span ⟨s'', t₀ + t'', by omega, ?_, rfl⟩)
  have hsum : (∑ k, (t₀ + t'') k) = (∑ k, t₀ k) + (∑ k, t'' k) := Finset.sum_add_distrib
  omega

theorem ptTheta_mem_hset_zero (w : Fin q → Fin (N + 1) → ℂ) (θ : Fin N → ℂ)
    (hθ : ∀ i, θ i ≠ 0) (D : Fin (N + 1) → ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ)
    (A B S T : ℕ) (𝔓 : Ideal (MR N))
    (h2 : chainIdeal w θ D P (A + S) (B + T) ≤ 𝔓) :
    ∀ s, s ≤ S → ptTheta θ s ∈ Hset w 𝔓 (chainIdeal w θ D P A B) 0 :=
  fun s hs => Hset_mono w 𝔓 _ (Nat.zero_le T)
    (hset_contains_steps w θ hθ D P A B S T 𝔓 h2 s hs)

theorem ptTheta_mem_InG {N : ℕ} (θ : Fin N → ℂ) (hθ : ∀ i, θ i ≠ 0) (s : ℕ) :
    InG (ptTheta θ s) := by
  intro i
  rw [ptTheta, Fin.cons_succ]
  exact pow_ne_zero _ (hθ i)

end HsetFacts

section MultiHomFacts

variable {N q : ℕ}

theorem multiHom_chainIdeal (w : Fin q → Fin (N + 1) → ℂ) (θ : Fin N → ℂ)
    (D : Fin (N + 1) → ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) (A B : ℕ)
    (hdeg : ∀ i, P.degreeOf i ≤ D i) :
    MultiHom N (chainIdeal w θ D P A B) := by
  letI : GradedAlgebra (MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N)) :=
    MvPolynomial.weightedGradedAlgebra ℂ (mdeg N)
  have hgen : ∀ x ∈ chainGen w θ D P A B,
      SetLike.IsHomogeneousElem (MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N)) x := by
    rintro x ⟨s, t, hs, ht, rfl⟩
    exact ⟨fsD D, (transl_basic (ptTheta θ s) (gone N)).2.2.2.1 (fsD D) _
      ((derH_basic w).1 t (fsD D) (homog D P) (homog_basic D P hdeg).1)⟩
  have hI : (chainIdeal w θ D P A B).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N)) :=
    Ideal.homogeneous_span (MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N)) _ hgen
  intro p hp d
  exact (MvPolynomial.mem_iff_weightedHomogeneousComponent_mem ℂ (mdeg N) hI p).mp hp d

theorem multiHom_minimalPrimes {N : ℕ} {I : Ideal (MR N)} (hI : MultiHom N I)
    {p : Ideal (MR N)} (hp : p ∈ I.minimalPrimes) : MultiHom N p := by
  have hann : Module.annihilator (MR N) ((MR N) ⧸ I) = I := Ideal.annihilator_quotient
  have hassoc : p ∈ associatedPrimes (MR N) ((MR N) ⧸ I) := by
    have h := Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes
      (MR N) ((MR N) ⧸ I)
    rw [hann] at h
    exact h hp
  exact multiHom_assPrime I hI p hassoc

end MultiHomFacts


section BasicGroupLemmas

variable {N : ℕ}

theorem ginv_InG {g : Fin (N + 1) → ℂ} (hg : InG g) : InG (ginv g) := by
  intro i
  rw [ginv, Fin.cons_succ]
  exact inv_ne_zero (hg i)

theorem gmul_ginv_self {g : Fin (N + 1) → ℂ} (hg : InG g) : gmul (ginv g) g = gone N := by
  funext j
  refine Fin.cases ?_ ?_ j
  · simp [gmul, ginv, gone]
  · intro i
    have h := hg i
    simp [gmul, ginv, gone, h]

theorem gmul_mem_InG {a b : Fin (N + 1) → ℂ} (ha : InG a) (hb : InG b) : InG (gmul a b) := by
  intro i
  rw [gmul, Fin.cons_succ]
  exact mul_ne_zero (ha i) (hb i)

end BasicGroupLemmas

section CoverCombine

variable {N : ℕ}

/-- Two consecutive coset coverings compose. -/
theorem cover_combine (A B C : Set (Fin (N + 1) → ℂ))
    (F₁ F₂ : Finset (Fin (N + 1) → ℂ))
    (h₁ : A ⊆ ⋃ f ∈ F₁, gmul f '' B) (h₂ : B ⊆ ⋃ f ∈ F₂, gmul f '' C) :
    A ⊆ ⋃ f ∈ F₁.product F₂, gmul (gmul f.1 f.2) '' C := by
  intro a ha
  rcases Set.mem_iUnion.mp (h₁ ha) with ⟨f₁, hf₁mem⟩
  rcases Set.mem_iUnion.mp hf₁mem with ⟨hf₁, haB⟩
  rcases haB with ⟨b, hb, hfb⟩
  rcases Set.mem_iUnion.mp (h₂ hb) with ⟨f₂, hf₂mem⟩
  rcases Set.mem_iUnion.mp hf₂mem with ⟨hf₂, hbC⟩
  rcases hbC with ⟨c, hc, hfc⟩
  refine Set.mem_iUnion.mpr ⟨(f₁, f₂), Set.mem_iUnion.mpr ⟨Finset.mem_product.mpr ⟨hf₁, hf₂⟩, ?_⟩⟩
  exact ⟨c, hc, by rw [gmul_assoc, hfc, hfb]⟩

end CoverCombine

section CosetIdealFacts

variable {N : ℕ}

theorem subIdeal_le_ptIdeal_gone (ρ : ℕ) (ε : Bool) (M : Fin ρ → Fin N → ℤ) :
    subIdeal N ρ ε M ≤ ptIdeal N (conePt N (gone N)) := by
  rw [subIdeal, Ideal.span_le]
  rintro F ⟨⟨d, hd⟩, hvan⟩
  have h := hvan (gone N) (gone_mem_InSub ρ ε M)
  simpa [ptIdeal] using h

theorem rayDim_cosetIdeal (D : Fin (N + 1) →₀ ℕ) (σ : Fin (N + 1) → ℂ) (hσ : InG σ)
    (ρ : ℕ) (ε : Bool) (M : Fin ρ → Fin N → ℤ) :
    rayDim N D (cosetIdeal σ ε M) = rayDim N D (subIdeal N ρ ε M) :=
  (rayHilb_transl D (ginv σ) (ginv_InG hσ) _).2.1

theorem rayDeg_cosetIdeal (D : Fin (N + 1) →₀ ℕ) (σ : Fin (N + 1) → ℂ) (hσ : InG σ)
    (ρ : ℕ) (ε : Bool) (M : Fin ρ → Fin N → ℤ) :
    rayDeg N D (cosetIdeal σ ε M) = rayDeg N D (subIdeal N ρ ε M) :=
  (rayHilb_transl D (ginv σ) (ginv_InG hσ) _).2.2

/-- Every coset ideal is a prime through the cone over `G`. -/
theorem meetsG_cosetIdeal (ρ : ℕ) (ε : Bool) (M : Fin ρ → Fin N → ℤ)
    (σ : Fin (N + 1) → ℂ) (hσ : InG σ) : MeetsG N (cosetIdeal σ ε M) := by
  refine ⟨conePt N σ, ⟨?_, ?_⟩, ?_⟩
  · simp [conePt]
  · intro i
    simpa [conePt] using hσ i
  · rw [cosetIdeal, Ideal.map_le_iff_le_comap]
    intro G hG
    have hG' : MvPolynomial.eval (conePt N (gone N)) G = 0 := by
      have h := subIdeal_le_ptIdeal_gone (N := N) ρ ε M hG
      simpa [ptIdeal] using h
    rw [Ideal.mem_comap]
    simp only [ptIdeal, RingHom.mem_ker]
    rw [(transl_basic (ginv σ) (gone N)).1 (conePt N σ) G,
      (transl_basic (ginv σ) (gone N)).2.1 σ, gmul_ginv_self hσ]
    exact hG'

end CosetIdealFacts


section ZGSubIdeal

variable {N : ℕ}

/-- The `G`-points of `Z(G')` are exactly the points of the closed subgroup `G'`. -/
theorem ZG_subIdeal_eq_InSub (N ρ : ℕ) (ε : Bool) (M : Fin ρ → Fin N → ℤ) :
    ZG (subIdeal N ρ ε M) = InSub N ρ ε M := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvG, hvanish⟩ := hv
    refine ⟨?_, hvG, ?_⟩
    · intro hε
      have hX : MvPolynomial.X (((0 : Fin (N + 1)), (1 : Fin 2))) ∈ subIdeal N ρ ε M := by
        refine Ideal.subset_span ⟨⟨Finsupp.single (0 : Fin (N + 1)) 1, ?_⟩, ?_⟩
        · rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule]
          exact MvPolynomial.isWeightedHomogeneous_X ℂ (mdeg N) ((0 : Fin (N + 1)), (1 : Fin 2))
        · intro y hy
          have h := hy.1 hε
          simpa [conePt] using h
      have h0 := hvanish _ hX
      simpa [conePt] using h0
    · intro j
      obtain ⟨F, hFmem, hFval⟩ := charPoly_spec (N := N) ε M j
      have h0 := hvanish F hFmem
      rw [hFval v hvG] at h0
      have hne : (∏ i : Fin N, (v i.succ) ^ ((M j i).natAbs)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hvG i)
      have h1 : (∏ i : Fin N, (v i.succ) ^ (M j i)) - 1 = 0 := by
        rcases mul_eq_zero.mp h0 with h | h
        · exact absurd h hne
        · exact h
      exact sub_eq_zero.mp h1
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h2, ?_⟩
    intro F hF
    have hle : subIdeal N ρ ε M ≤ ptIdeal N (conePt N v) := by
      rw [subIdeal, Ideal.span_le]
      rintro F ⟨⟨d, hd⟩, hvan⟩
      have := hvan v ⟨h1, h2, h3⟩
      simpa [ptIdeal] using this
    have := hle hF
    simpa [ptIdeal] using this

theorem meetsG_subIdeal (ρ : ℕ) (ε : Bool) (M : Fin ρ → Fin N → ℤ) :
    MeetsG N (subIdeal N ρ ε M) :=
  ⟨conePt N (gone N), ⟨by simp [conePt], fun i => ⟨by simp [conePt], gone_mem_InG i⟩⟩,
    subIdeal_le_ptIdeal_gone ρ ε M⟩

/-- The stabiliser of `𝔓` acts on its `G`-points. -/
theorem mem_ZG_of_stab {𝔓 : Ideal (MR N)} {v : Fin (N + 1) → ℂ} (hv : v ∈ ZG 𝔓)
    {g : Fin (N + 1) → ℂ} (hg : g ∈ stabG 𝔓) : gmul v g ∈ ZG 𝔓 := by
  obtain ⟨hvG, hvanish⟩ := hv
  obtain ⟨hgG, hgmap⟩ := hg
  refine ⟨gmul_mem_InG hvG hgG, ?_⟩
  intro F hF
  rw [gmul_comm v g, ← (transl_basic g (gone N)).2.1 v]
  rw [← (transl_basic g (gone N)).1 (conePt N v) F]
  refine hvanish _ ?_
  rw [← hgmap]
  exact Ideal.mem_map_of_mem (transl g) hF

/-- `MeetsG 𝔓` supplies a point of `ZG 𝔓`: normalising the cone point by the torus scaling. -/
theorem exists_mem_ZG_of_meetsG {𝔓 : Ideal (MR N)} (hH : MultiHom N 𝔓)
    (hG : MeetsG N 𝔓) : ∃ v, v ∈ ZG 𝔓 := by
  obtain ⟨x, hxG, hxle⟩ := hG
  have hlam : ∀ i : Fin (N + 1), x (i, (0 : Fin 2)) ≠ 0 := by
    intro i
    refine Fin.cases ?_ ?_ i
    · simpa using hxG.1
    · intro k
      exact (hxG.2 k).1
  set v : Fin (N + 1) → ℂ := fun i => x (i, (1 : Fin 2)) / x (i, (0 : Fin 2)) with hvdef
  have hvG : InG v := by
    intro i
    rw [hvdef]
    exact div_ne_zero (hxG.2 i).2 (hxG.2 i).1
  refine ⟨v, hvG, ?_⟩
  intro F hF
  have hfin := MvPolynomial.weightedHomogeneousComponent_finsupp (w := mdeg N) F
  have hsum := MvPolynomial.sum_weightedHomogeneousComponent (mdeg N) F
  rw [finsum_eq_sum _ hfin] at hsum
  rw [← hsum, map_sum]
  refine Finset.sum_eq_zero fun d hd => ?_
  have hFd : (MvPolynomial.weightedHomogeneousComponent (mdeg N) d F) ∈ 𝔓 := hH F hF d
  have hx0 : MvPolynomial.eval x (MvPolynomial.weightedHomogeneousComponent (mdeg N) d F) = 0 := by
    simpa [ptIdeal] using hxle hFd
  have hhom : MvPolynomial.IsWeightedHomogeneous (mdeg N)
      (MvPolynomial.weightedHomogeneousComponent (mdeg N) d F) d :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous d F
  have hpt : (fun w : Fin (N + 1) × Fin 2 => x (w.1, (0 : Fin 2)) * conePt N v w) = x := by
    funext w
    obtain ⟨i, j⟩ := w
    refine Fin.cases ?_ ?_ j
    · simp [conePt]
    · intro e
      simp only [conePt, hvdef]
      rw [if_neg (by simp), ← mul_div_assoc, mul_div_cancel_left₀ _ (hlam i)]
      refine congrArg x ?_
      ext <;> simp
  have hscale := eval_scale_of_isWeightedHomogeneous hhom (fun i => x (i, (0 : Fin 2))) (conePt N v)
  rw [hpt] at hscale
  have hne : (∏ i : Fin (N + 1), x (i, (0 : Fin 2)) ^ (d i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hlam i)
  have hzero := hx0
  rw [hscale] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · exact absurd h hne
  · exact h

end ZGSubIdeal


section InSubGroup

variable {N : ℕ}

/-- The points of `G'` lie on the cone over `G`. -/
theorem InSub_imp_InG {ρ : ℕ} {ε : Bool} {M : Fin ρ → Fin N → ℤ} {y : Fin (N + 1) → ℂ}
    (h : InSub N ρ ε M y) : InG y := h.2.1

theorem inv_zpow_mul_zpow (a : ℂ) (ha : a ≠ 0) (n : ℤ) : (a⁻¹ : ℂ) ^ n * a ^ n = 1 := by
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    rw [zpow_natCast, zpow_natCast, ← mul_pow, inv_mul_cancel₀ ha, one_pow]
  · obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero hn
    rw [zpow_negSucc, zpow_negSucc, inv_pow, inv_inv, mul_inv_cancel₀ (pow_ne_zero _ ha)]

theorem InSub_gmul {ρ : ℕ} {ε : Bool} {M : Fin ρ → Fin N → ℤ}
    {a b : Fin (N + 1) → ℂ} (ha : InSub N ρ ε M a) (hb : InSub N ρ ε M b) :
    InSub N ρ ε M (gmul a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hε
    rw [gmul, Fin.cons_zero, ha.1 hε, hb.1 hε, add_zero]
  · intro i
    rw [gmul, Fin.cons_succ]
    exact mul_ne_zero (ha.2.1 i) (hb.2.1 i)
  · intro j
    rw [show (∏ i : Fin N, (gmul a b i.succ) ^ (M j i))
        = ∏ i : Fin N, (a i.succ) ^ (M j i) * (b i.succ) ^ (M j i) from
      Finset.prod_congr rfl fun i _ => by rw [gmul, Fin.cons_succ, mul_zpow]]
    rw [Finset.prod_mul_distrib, ha.2.2 j, hb.2.2 j, one_mul]

theorem InSub_ginv {ρ : ℕ} {ε : Bool} {M : Fin ρ → Fin N → ℤ} {a : Fin (N + 1) → ℂ}
    (ha : InSub N ρ ε M a) : InSub N ρ ε M (ginv a) := by
  refine ⟨?_, ?_, ?_⟩
  · intro hε
    rw [ginv, Fin.cons_zero, ha.1 hε, neg_zero]
  · intro i
    rw [ginv, Fin.cons_succ]
    exact inv_ne_zero (ha.2.1 i)
  · intro j
    have hne : ∀ i : Fin N, a i.succ ≠ 0 := fun i => ha.2.1 i
    rw [show (∏ i : Fin N, (ginv a i.succ) ^ (M j i))
        = ∏ i : Fin N, ((a i.succ)⁻¹) ^ (M j i) from
      Finset.prod_congr rfl fun i _ => by rw [ginv, Fin.cons_succ]]
    have h1 : (∏ i : Fin N, ((a i.succ)⁻¹) ^ (M j i)) *
        (∏ i : Fin N, (a i.succ) ^ (M j i)) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun i _ => inv_zpow_mul_zpow _ (hne i) _
    rwa [ha.2.2 j, mul_one] at h1

theorem InSub_gone {N ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ) :
    InSub N ρ ε M (gone N) := gone_mem_InSub ρ ε M

end InSubGroup


section ZpowHelpers

theorem zpow_mul_of_ne_zero {x : ℂ} (hx : x ≠ 0) (m n : ℤ) : x ^ (m * n) = (x ^ m) ^ n := by
  have key := congrArg (fun z : ℂˣ => (z : ℂ)) (zpow_mul (Units.mk0 x hx) m n)
  simpa only [Units.val_zpow_eq_zpow_val, Units.val_mk0] using key

theorem mul_zpow_of_ne_zero {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) (n : ℤ) :
    (x * y) ^ n = x ^ n * y ^ n := by
  have key := congrArg (fun z : ℂˣ => (z : ℂ)) (mul_zpow (Units.mk0 x hx) (Units.mk0 y hy) n)
  simpa only [Units.val_zpow_eq_zpow_val, Units.val_mk0, Units.val_mul] using key

theorem inv_zpow_of_ne_zero {x : ℂ} (hx : x ≠ 0) (n : ℤ) : (x⁻¹) ^ n = (x ^ n)⁻¹ := by
  have h1 : (x⁻¹) ^ n = x ^ (-n) := by
    rw [← zpow_neg_one (x := x), ← zpow_mul_of_ne_zero hx (-1 : ℤ) n, neg_one_mul]
  have h2 : (x ^ n)⁻¹ = x ^ (-n) := by
    rw [← zpow_neg_one (x := x ^ n), ← zpow_mul_of_ne_zero hx n (-1 : ℤ), mul_neg_one]
  rw [h1, h2]

end ZpowHelpers

section StepClasses

variable {N : ℕ}

/-- The class of the step point `sγ` modulo `G'`, in the coordinates of `cardMod`. -/
noncomputable def stepClass {ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ) (θ : Fin N → ℂ)
    (s : ℕ) : ℂ × (Fin ρ → ℂ) :=
  ((if ε then 0 else (s : ℂ)), fun j => ∏ i : Fin N, θ i ^ ((s : ℤ) * M j i))

theorem ptTheta_succ_ne_zero {N : ℕ} (θ : Fin N → ℂ) (hθ : ∀ i, θ i ≠ 0) (s : ℕ) (i : Fin N) :
    ptTheta θ s i.succ ≠ 0 := by
  rw [ptTheta, Fin.cons_succ]
  exact pow_ne_zero _ (hθ i)

theorem stepClass_chi {ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ) (θ : Fin N → ℂ)
    (hθ : ∀ i, θ i ≠ 0) (s : ℕ) (j : Fin ρ) :
    (stepClass ε M θ s).2 j = ∏ i : Fin N, (ptTheta θ s i.succ) ^ (M j i) := by
  simp only [stepClass]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [ptTheta, Fin.cons_succ]
  exact (zpow_mul_of_ne_zero (hθ i) (s : ℤ) (M j i)).trans (by rw [zpow_natCast])

theorem ptTheta_succ_inv {N : ℕ} (θ : Fin N → ℂ) (hθ : ∀ i, θ i ≠ 0) (s : ℕ) (i : Fin N) :
    (ginv (ptTheta θ s)) i.succ = ((ptTheta θ s) i.succ)⁻¹ := by
  rw [ginv, Fin.cons_succ]

theorem stepClass_eq_iff {ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ) (θ : Fin N → ℂ)
    (hθ : ∀ i, θ i ≠ 0) (s s' : ℕ) :
    stepClass ε M θ s = stepClass ε M θ s' ↔
      InSub N ρ ε M (gmul (ptTheta θ s) (ginv (ptTheta θ s'))) := by
  have hchi : ∀ j : Fin ρ,
      (∏ i : Fin N, ((ptTheta θ s) i.succ * ((ptTheta θ s') i.succ)⁻¹) ^ (M j i)) =
        (∏ i : Fin N, ((ptTheta θ s) i.succ) ^ (M j i)) *
          (∏ i : Fin N, ((ptTheta θ s') i.succ) ^ (M j i))⁻¹ := by
    intro j
    have hpt : ∀ i : Fin N,
        ((ptTheta θ s) i.succ * ((ptTheta θ s') i.succ)⁻¹) ^ (M j i)
          = ((ptTheta θ s) i.succ) ^ (M j i) *
              (((ptTheta θ s') i.succ) ^ (M j i))⁻¹ := by
      intro i
      rw [mul_zpow_of_ne_zero (ptTheta_succ_ne_zero θ hθ s i)
            (inv_ne_zero (ptTheta_succ_ne_zero θ hθ s' i)) (M j i),
          inv_zpow_of_ne_zero (ptTheta_succ_ne_zero θ hθ s' i) (M j i)]
    rw [Finset.prod_congr rfl (fun i _ => hpt i), Finset.prod_mul_distrib,
      Finset.prod_inv_distrib]
  have hgm : ∀ i : Fin N,
      (gmul (ptTheta θ s) (ginv (ptTheta θ s'))) i.succ =
        (ptTheta θ s) i.succ * ((ptTheta θ s') i.succ)⁻¹ := by
    intro i
    rw [gmul, Fin.cons_succ, ptTheta_succ_inv θ hθ s' i]
  have hzero : (gmul (ptTheta θ s) (ginv (ptTheta θ s'))) 0 = (s : ℂ) - (s' : ℂ) := by
    simp [gmul, ginv, ptTheta, sub_eq_add_neg]
  constructor
  · intro h
    have h1 : (if ε then (0 : ℂ) else (s : ℂ)) = (if ε then (0 : ℂ) else (s' : ℂ)) :=
      congrArg Prod.fst h
    have h2 : ∀ j : Fin ρ, (∏ i : Fin N, (ptTheta θ s) i.succ ^ (M j i)) =
        ∏ i : Fin N, (ptTheta θ s') i.succ ^ (M j i) := by
      intro j
      have hj := congrFun (congrArg Prod.snd h) j
      rw [stepClass_chi ε M θ hθ s j, stepClass_chi ε M θ hθ s' j] at hj
      exact hj
    refine ⟨?_, ?_, ?_⟩
    · intro hε
      have hs : (s : ℂ) = (s' : ℂ) := by simpa [hε] using h1
      rw [hzero, hs, sub_self]
    · intro i
      rw [hgm i]
      exact mul_ne_zero (ptTheta_succ_ne_zero θ hθ s i)
        (inv_ne_zero (ptTheta_succ_ne_zero θ hθ s' i))
    · intro j
      have hpt : ∀ i : Fin N,
          ((gmul (ptTheta θ s) (ginv (ptTheta θ s'))) i.succ) ^ (M j i)
            = ((ptTheta θ s) i.succ * ((ptTheta θ s') i.succ)⁻¹) ^ (M j i) :=
        fun i => by rw [hgm i]
      rw [Finset.prod_congr rfl (fun i _ => hpt i), hchi j]
      have hne : (∏ i : Fin N, (ptTheta θ s') i.succ ^ (M j i)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun i _ =>
          zpow_ne_zero (M j i) (ptTheta_succ_ne_zero θ hθ s' i)
      rw [h2 j, mul_inv_cancel₀ hne]
  · intro h
    have h1 : (if ε then (0 : ℂ) else (s : ℂ)) = (if ε then (0 : ℂ) else (s' : ℂ)) := by
      by_cases hε : ε = true
      · simp [hε]
      · have hε' : ε = false := by cases ε <;> simp_all
        have h0 := h.1 hε'
        have hs : (s : ℂ) = (s' : ℂ) := by
          rw [hzero, sub_eq_zero] at h0
          exact h0
        simp [hε', hs]
    have h2 : ∀ j : Fin ρ, (∏ i : Fin N, (ptTheta θ s) i.succ ^ (M j i)) =
        ∏ i : Fin N, (ptTheta θ s') i.succ ^ (M j i) := by
      intro j
      rw [← stepClass_chi ε M θ hθ s j, ← stepClass_chi ε M θ hθ s' j]
      have hj := h.2.2 j
      have hpt : ∀ i : Fin N,
          ((gmul (ptTheta θ s) (ginv (ptTheta θ s'))) i.succ) ^ (M j i)
            = ((ptTheta θ s) i.succ * ((ptTheta θ s') i.succ)⁻¹) ^ (M j i) :=
        fun i => by rw [hgm i]
      rw [Finset.prod_congr rfl (fun i _ => hpt i)] at hj
      rw [hchi j] at hj
      rw [← stepClass_chi ε M θ hθ s j, ← stepClass_chi ε M θ hθ s' j] at hj
      have hne : (stepClass ε M θ s').2 j ≠ 0 := by
        rw [stepClass_chi ε M θ hθ s' j]
        exact Finset.prod_ne_zero_iff.mpr fun i _ =>
          zpow_ne_zero (M j i) (ptTheta_succ_ne_zero θ hθ s' i)
      exact (mul_inv_eq_one₀ hne).mp hj
    refine Prod.ext ?_ ?_
    · simpa only [stepClass] using h1
    · funext j
      rw [stepClass_chi ε M θ hθ s j, stepClass_chi ε M θ hθ s' j]
      exact h2 j

end StepClasses

section CosetDictionary

variable {N : ℕ}

theorem transl_gone_eq_id : transl (gone N) = AlgHom.id ℂ (MR N) :=
  AlgHom.ext fun _ => transl_gone_apply _

theorem map_transl_gone (I : Ideal (MR N)) : Ideal.map (transl (gone N)) I = I := by
  rw [transl_gone_eq_id]
  simpa using Ideal.map_id (R := MR N) I

/-- `map (transl a) ∘ map (transl b) = map (transl (a·b))` on ideals. -/
theorem map_transl_transl (a b : Fin (N + 1) → ℂ) (I : Ideal (MR N)) :
    (I.map (transl b)).map (transl a) = I.map (transl (gmul a b)) := by
  have hcomp : (transl a).comp (transl b) = transl (gmul a b) :=
    AlgHom.ext fun F => (transl_basic a b).2.2.1 F
  rw [Ideal.map_mapₐ (transl b) (transl a), hcomp]

/-- A multihomogeneous polynomial lies in `subIdeal` iff it vanishes on `G'`. -/
theorem mem_subIdeal_iff {ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ) (hM : PrimSys M)
    {F : MR N} (hF : ∃ d, F ∈ homPiece N d) :
    F ∈ subIdeal N ρ ε M ↔ ∀ y, InSub N ρ ε M y →
      MvPolynomial.eval (conePt N y) F = 0 := by
  refine ⟨fun hFmem y hy => ?_, fun hvan => ?_⟩
  · have hle : subIdeal N ρ ε M ≤ ptIdeal N (conePt N y) := by
      rw [subIdeal, Ideal.span_le]
      rintro G ⟨⟨d, hd⟩, hGvan⟩
      have := hGvan y hy
      simpa [ptIdeal] using this
    have := hle hFmem
    simpa [ptIdeal] using this
  · refine mem_of_vanish_ZG (subIdeal N ρ ε M) (subIdeal_isPrime ε M hM)
      (multiHom_subIdeal N ρ ε M) (meetsG_subIdeal ρ ε M) F hF ?_
    intro v hv
    rw [ZG_subIdeal_eq_InSub] at hv
    exact hvan v hv

theorem map_transl_subIdeal_le {ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ) (hM : PrimSys M)
    {g : Fin (N + 1) → ℂ} (hg : InSub N ρ ε M g) :
    Ideal.map (transl g) (subIdeal N ρ ε M) ≤ subIdeal N ρ ε M := by
  rw [Ideal.map_le_iff_le_comap]
  intro F hF
  rw [Ideal.mem_comap]
  have hfin := MvPolynomial.weightedHomogeneousComponent_finsupp (w := mdeg N) F
  have hsum := MvPolynomial.sum_weightedHomogeneousComponent (mdeg N) F
  rw [finsum_eq_sum _ hfin] at hsum
  rw [← hsum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hFd : MvPolynomial.weightedHomogeneousComponent (mdeg N) d F ∈ subIdeal N ρ ε M :=
    (multiHom_subIdeal N ρ ε M) F hF d
  have hhom : MvPolynomial.IsWeightedHomogeneous (mdeg N)
      (MvPolynomial.weightedHomogeneousComponent (mdeg N) d F) d :=
    MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous d F
  refine (mem_subIdeal_iff ε M hM ⟨d, by
    rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule]
    exact (transl_basic g (gone N)).2.2.2.1 d _ (by
      rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule]; exact hhom)⟩).mpr ?_
  intro y hy
  rw [(transl_basic g (gone N)).1 (conePt N y) _]
  rw [(transl_basic g (gone N)).2.1 y]
  exact (mem_subIdeal_iff ε M hM ⟨d, by
    rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule]; exact hhom⟩).mp hFd
    (gmul g y) (InSub_gmul hg hy)

theorem map_transl_subIdeal_of_mem {ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ) (hM : PrimSys M)
    {g : Fin (N + 1) → ℂ} (hg : InSub N ρ ε M g) :
    Ideal.map (transl g) (subIdeal N ρ ε M) = subIdeal N ρ ε M := by
  refine le_antisymm (map_transl_subIdeal_le ε M hM hg) ?_
  have h := map_transl_subIdeal_le ε M hM (InSub_ginv hg)
  have hgg : gmul g (ginv g) = gone N := by
    rw [gmul_comm]; exact gmul_ginv_self (InSub_imp_InG hg)
  calc subIdeal N ρ ε M
      = Ideal.map (transl (gone N)) (subIdeal N ρ ε M) := (map_transl_gone _).symm
    _ = Ideal.map (transl (gmul g (ginv g))) (subIdeal N ρ ε M) := by rw [hgg]
    _ = Ideal.map (transl g) (Ideal.map (transl (ginv g)) (subIdeal N ρ ε M)) :=
        (map_transl_transl g (ginv g) _).symm
    _ ≤ Ideal.map (transl g) (subIdeal N ρ ε M) := Ideal.map_mono h

theorem isPrime_cosetIdeal {ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ) (hM : PrimSys M)
    (v : Fin (N + 1) → ℂ) (hv : InG v) : (cosetIdeal v ε M).IsPrime := by
  have hEq : cosetIdeal v ε M = Ideal.comap (transl v) (subIdeal N ρ ε M) := by
    ext F
    rw [Ideal.mem_comap]
    rw [cosetIdeal]
    constructor
    · intro hF
      have h1 : transl v F ∈ Ideal.map (transl v) (Ideal.map (transl (ginv v)) (subIdeal N ρ ε M)) :=
        Ideal.mem_map_of_mem (transl v) hF
      rwa [map_transl_transl, show gmul v (ginv v) = gone N from by
            rw [gmul_comm]; exact gmul_ginv_self hv, map_transl_gone] at h1
    · intro hF
      have h1 : transl (ginv v) (transl v F) ∈
          Ideal.map (transl (ginv v)) (subIdeal N ρ ε M) :=
        Ideal.mem_map_of_mem (transl (ginv v)) hF
      rwa [(transl_basic v (ginv v)).2.2.2.2 hv F] at h1
  rw [hEq]
  haveI := subIdeal_isPrime ε M hM
  exact inferInstance

theorem multiHom_cosetIdeal {ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ)
    (g : Fin (N + 1) → ℂ) : MultiHom N (cosetIdeal g ε M) := by
  letI : GradedAlgebra (MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N)) :=
    MvPolynomial.weightedGradedAlgebra ℂ (mdeg N)
  have hgen : ∀ x ∈ ({F : MR N | (∃ d, F ∈ homPiece N d) ∧
      ∀ y, InSub N ρ ε M y → MvPolynomial.eval (conePt N y) F = 0} : Set (MR N)),
      SetLike.IsHomogeneousElem (MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N))
        (transl (ginv g) x) := by
    rintro x ⟨⟨d, hd⟩, -⟩
    exact ⟨d, (transl_basic (ginv g) (gone N)).2.2.2.1 d x hd⟩
  have hspan : cosetIdeal g ε M = Ideal.span ((transl (ginv g)) ''
      {F : MR N | (∃ d, F ∈ homPiece N d) ∧
        ∀ y, InSub N ρ ε M y → MvPolynomial.eval (conePt N y) F = 0}) := by
    rw [cosetIdeal, subIdeal, Ideal.map_span]
  have hI : (cosetIdeal g ε M).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N)) := by
    rw [hspan]
    exact Ideal.homogeneous_span _ _ (by rintro x ⟨y, hy, rfl⟩; exact hgen y hy)
  intro p hp d
  exact (MvPolynomial.mem_iff_weightedHomogeneousComponent_mem ℂ (mdeg N) hI p).mp hp d

/-- The `G`-points of `Z(cosetIdeal σ)` are the coset `σ·G'`. -/
theorem ZG_cosetIdeal {ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ) (hM : PrimSys M)
    (σ : Fin (N + 1) → ℂ) (hσ : InG σ) :
    {y | InG y ∧ ∀ F ∈ cosetIdeal σ ε M, MvPolynomial.eval (conePt N y) F = 0}
      = {y | InG y ∧ InSub N ρ ε M (gmul (ginv σ) y)} := by
  ext y
  constructor
  · rintro ⟨hyG, hyv⟩
    refine ⟨hyG, ?_⟩
    rw [← ZG_subIdeal_eq_InSub]
    refine ⟨gmul_mem_InG (ginv_InG hσ) hyG, ?_⟩
    intro F' hF'
    have h := hyv _ (Ideal.mem_map_of_mem (transl (ginv σ)) hF')
    rw [(transl_basic (ginv σ) (gone N)).1, (transl_basic (ginv σ) (gone N)).2.1] at h
    exact h
  · rintro ⟨hyG, hy⟩
    refine ⟨hyG, ?_⟩
    intro F hF
    have hle : cosetIdeal σ ε M ≤ ptIdeal N (conePt N y) := by
      rw [cosetIdeal, Ideal.map_le_iff_le_comap]
      intro F' hF'
      rw [Ideal.mem_comap, ptIdeal, RingHom.mem_ker]
      have hfin := MvPolynomial.weightedHomogeneousComponent_finsupp (w := mdeg N) F'
      have hsum := MvPolynomial.sum_weightedHomogeneousComponent (mdeg N) F'
      rw [finsum_eq_sum _ hfin] at hsum
      conv_lhs => rw [← hsum]
      rw [map_sum, map_sum]
      refine Finset.sum_eq_zero fun d hd => ?_
      have hFd : MvPolynomial.weightedHomogeneousComponent (mdeg N) d F' ∈ subIdeal N ρ ε M :=
        (multiHom_subIdeal N ρ ε M) F' hF' d
      have hhom : MvPolynomial.IsWeightedHomogeneous (mdeg N)
          (MvPolynomial.weightedHomogeneousComponent (mdeg N) d F') d :=
        MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous d F'
      have hvan := (mem_subIdeal_iff ε M hM ⟨d, by
        rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule]; exact hhom⟩).mp hFd
      have hpt := hvan (gmul (ginv σ) y) hy
      rw [(transl_basic (ginv σ) (gone N)).1 (conePt N y) _,
        (transl_basic (ginv σ) (gone N)).2.1 y]
      exact hpt
    have := hle hF
    simpa [ptIdeal] using this

end CosetDictionary

section CosetPrimeGap

variable {N : ℕ}

theorem cosetIdeal_eq_iff {ρ : ℕ} (ε : Bool) (M : Fin ρ → Fin N → ℤ) (hM : PrimSys M)
    (σ σ' : Fin (N + 1) → ℂ) (hσ : InG σ) (hσ' : InG σ') :
    cosetIdeal σ ε M = cosetIdeal σ' ε M ↔ InSub N ρ ε M (gmul σ (ginv σ')) := by
  constructor
  · intro h
    have hmemσ : σ ∈ {y | InG y ∧ ∀ F ∈ cosetIdeal σ ε M, MvPolynomial.eval (conePt N y) F = 0} := by
      rw [ZG_cosetIdeal ε M hM σ hσ]
      exact ⟨hσ, by rw [gmul_ginv_self hσ]; exact InSub_gone ε M⟩
    have hmem' : InSub N ρ ε M (gmul (ginv σ') σ) := by
      have h2 := hmemσ
      rw [h] at h2
      rw [ZG_cosetIdeal ε M hM σ' hσ'] at h2
      exact h2.2
    rwa [gmul_comm] at hmem'
  · intro h
    have hgrp : gmul (ginv σ) (gmul σ (ginv σ')) = ginv σ' := by
      rw [← gmul_assoc, gmul_ginv_self hσ, gmul_gone_left]
    rw [cosetIdeal, cosetIdeal]
    calc (subIdeal N ρ ε M).map (transl (ginv σ))
        = ((subIdeal N ρ ε M).map (transl (gmul σ (ginv σ')))).map (transl (ginv σ)) := by
          rw [map_transl_subIdeal_of_mem ε M hM h]
      _ = (subIdeal N ρ ε M).map (transl (gmul (ginv σ) (gmul σ (ginv σ')))) :=
          map_transl_transl (ginv σ) (gmul σ (ginv σ')) (subIdeal N ρ ε M)
      _ = (subIdeal N ρ ε M).map (transl (ginv σ')) := by rw [hgrp]

end CosetPrimeGap

section DimGap

variable {N : ℕ}

/-- `dim G' ≤ dim Z(𝔓)`. -/
theorem rayDim_subIdeal_le (D : Fin (N + 1) → ℕ) (hD : ∀ i, 1 ≤ D i)
    (𝔓 : Ideal (MR N)) (h𝔓 : 𝔓.IsPrime) (hH : MultiHom N 𝔓) (hG : MeetsG N 𝔓)
    (ρ : ℕ) (ε : Bool) (M : Fin ρ → Fin N → ℤ) (hM : PrimSys M)
    (hsub : subSet N ρ ε M ⊆ stabG 𝔓) :
    rayDim N (fsD D) (subIdeal N ρ ε M) ≤ rayDim N (fsD D) 𝔓 := by
  obtain ⟨v, hv⟩ := exists_mem_ZG_of_meetsG hH hG
  have hvG : InG v := hv.1
  -- `𝔓 ≤ cosetIdeal v ε M`
  have hle : 𝔓 ≤ cosetIdeal v ε M := by
    intro F hF
    rw [cosetIdeal]
    have hfin := MvPolynomial.weightedHomogeneousComponent_finsupp (w := mdeg N) F
    have hsum := MvPolynomial.sum_weightedHomogeneousComponent (mdeg N) F
    rw [finsum_eq_sum _ hfin] at hsum
    rw [← hsum]
    refine Submodule.sum_mem _ fun d hd => ?_
    have hFd : MvPolynomial.weightedHomogeneousComponent (mdeg N) d F ∈ 𝔓 := hH F hF d
    have hhom : MvPolynomial.IsWeightedHomogeneous (mdeg N)
        (MvPolynomial.weightedHomogeneousComponent (mdeg N) d F) d :=
      MvPolynomial.weightedHomogeneousComponent_isWeightedHomogeneous d F
    have hsubd : transl v (MvPolynomial.weightedHomogeneousComponent (mdeg N) d F) ∈
        subIdeal N ρ ε M := by
      refine (mem_subIdeal_iff ε M hM ⟨d, by
        rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule]
        exact (transl_basic v (gone N)).2.2.2.1 d _ (by
          rw [homPiece, MvPolynomial.mem_weightedHomogeneousSubmodule]; exact hhom)⟩).mpr ?_
      intro z hz
      rw [(transl_basic v (gone N)).1 (conePt N z) _]
      rw [(transl_basic v (gone N)).2.1 z]
      exact (mem_ZG_of_stab hv (hsub hz)).2 _ hFd
    rw [← (transl_basic v (ginv v)).2.2.2.2 hvG
      (MvPolynomial.weightedHomogeneousComponent (mdeg N) d F)]
    exact Ideal.mem_map_of_mem (transl (ginv v)) hsubd
  have hq : (cosetIdeal v ε M).IsPrime := isPrime_cosetIdeal ε M hM v hvG
  have hqH : MultiHom N (cosetIdeal v ε M) := multiHom_cosetIdeal ε M v
  have hq0 : rayPoly N (fsD D) (cosetIdeal v ε M) ≠ 0 :=
    rayPoly_ne_zero_of_meetsG (fsD D) (by intro i; simpa [fsD] using hD i) _
      hqH (meetsG_cosetIdeal ρ ε M v hvG)
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hlt' := rayDim_lt_of_lt (fsD D) (by intro i; simpa [fsD] using hD i) 𝔓
      (cosetIdeal v ε M) h𝔓 hq hH hqH hlt hq0
    rw [rayDim_cosetIdeal (fsD D) v hvG ρ ε M] at hlt'
    exact le_of_lt hlt'
  · rw [heq, rayDim_cosetIdeal (fsD D) v hvG ρ ε M]

end DimGap



theorem stab_step {N q : ℕ} (P : MvPolynomial (Fin (N + 1)) ℂ) (hP : P ≠ 0)
    (D : Fin (N + 1) → ℕ) (hD : ∀ i, 1 ≤ D i) (hdeg : ∀ i, P.degreeOf i ≤ D i)
    (w : Fin q → Fin (N + 1) → ℂ) (θ : Fin N → ℂ) (hθ : ∀ i, θ i ≠ 0) (A B S T : ℕ)
    (𝔓 : Ideal (MR N)) (h𝔓 : 𝔓.IsPrime) (hG : MeetsG N 𝔓)
    (h1 : 𝔓 ∈ (chainIdeal w θ D P A B).minimalPrimes)
    (h2 : chainIdeal w θ D P (A + S) (B + T) ≤ 𝔓)
    (hmax : ∀ p ∈ (chainIdeal w θ D P A B).minimalPrimes, MeetsG N p →
      rayDim N (fsD D) p ≤ rayDim N (fsD D) 𝔓) :
    ∃ (ε : Bool) (ρ : ℕ) (M : Fin ρ → Fin N → ℤ), ρ ≤ N ∧ PrimSys M ∧
      rayDim N (fsD D) (subIdeal N ρ ε M) ≤ rayDim N (fsD D) 𝔓 ∧
      (((T + ellW w ε M).choose (ellW w ε M) : ℕ) : ℚ) * (cardMod ε M θ S : ℚ) *
          rayDeg N (fsD D) (subIdeal N ρ ε M) ≤
        ((N + 1).factorial : ℚ) * ∏ i, (D i : ℚ) := by
  classical
  -- ### 0. multihomogeneity of the chain ideal and of `𝔓`
  have hHsol : MultiHom N (chainIdeal w θ D P A B) := multiHom_chainIdeal w θ D P A B hdeg
  have hH𝔓 : MultiHom N 𝔓 := multiHom_minimalPrimes hHsol h1
  set I : Ideal (MR N) := chainIdeal w θ D P A B with hIdef
  -- ### 1. the connected subgroup `G' = subSet N ρ ε M` of `stabG 𝔓`
  obtain ⟨ε, ρ, M, hρN, hM, hsub, F₂, -, hF₂cov⟩ :=
    closedSub_structure (stabG 𝔓) (stab_closedSub 𝔓 hH𝔓)
  refine ⟨ε, ρ, M, hρN, hM, ?_, ?_⟩
  · -- `dim G' ≤ dim Z(𝔓)`
    exact rayDim_subIdeal_le D hD 𝔓 h𝔓 hH𝔓 hG ρ ε M hM hsub
  · -- ### 2. the multiplicity bound
    set J : Ideal (MR N) := Ideal.span (bigGen w θ D P A B 𝔓) with hJdef
    -- the covering of `Hset 0` by `G'`-cosets
    obtain ⟨F₁, hF₁⟩ :=
      hset_zero_cosets (fsD D) hD w I 𝔓 hHsol h𝔓 h1 hG hmax
    have hcov : Hset w 𝔓 I 0 ⊆
        ⋃ f ∈ F₁.product F₂, gmul (gmul f.1 f.2) '' subSet N ρ ε M :=
      cover_combine _ _ _ _ _ hF₁ hF₂cov
    -- the same cover, indexed by single elements of `G` instead of pairs
    set Fcov : Finset (Fin (N + 1) → ℂ) := (F₁.product F₂).image (fun p => gmul p.1 p.2)
      with hFcovdef
    have hcov' : Hset w 𝔓 I 0 ⊆ ⋃ f ∈ Fcov, gmul f '' subSet N ρ ε M := by
      intro x hx
      rcases Set.mem_iUnion.mp (hcov hx) with ⟨p, hp⟩
      rcases Set.mem_iUnion.mp hp with ⟨hpF, hxp⟩
      refine Set.mem_iUnion.mpr ⟨gmul p.1 p.2, Set.mem_iUnion.mpr ⟨?_, hxp⟩⟩
      rw [hFcovdef]
      exact Finset.mem_image.mpr ⟨p, hpF, rfl⟩
    -- the classes of the step points modulo `G'`
    set classes : Finset (ℂ × (Fin ρ → ℂ)) :=
      (Finset.range (S + 1)).image (stepClass ε M θ) with hclasses
    -- representatives
    set rep : ℂ × (Fin ρ → ℂ) → ℕ := fun c =>
      if h : ∃ s ∈ Finset.range (S + 1), stepClass ε M θ s = c then Classical.choose h else 0
      with hrepdef
    have hrep (c : ℂ × (Fin ρ → ℂ)) (hc : c ∈ classes) :
        rep c ∈ Finset.range (S + 1) ∧ stepClass ε M θ (rep c) = c := by
      have hex : ∃ s ∈ Finset.range (S + 1), stepClass ε M θ s = c := by
        rw [hclasses, Finset.mem_image] at hc
        obtain ⟨s, hs, hsc⟩ := hc
        exact ⟨s, hs, hsc⟩
      have : rep c = Classical.choose hex := by
        simp only [hrepdef]
        rw [dif_pos hex]
      rw [this]
      exact Classical.choose_spec hex
    set prime : ℂ × (Fin ρ → ℂ) → Ideal (MR N) :=
      fun c => cosetIdeal (ptTheta θ (rep c)) ε M with hprimedef
    have hprime_mem (c : ℂ × (Fin ρ → ℂ)) (hc : c ∈ classes) : prime c ∈ J.minimalPrimes := by
      have hmem := (hrep c hc).1
      have hs : rep c ≤ S := Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem)
      exact coset_minimalPrime w θ D P hdeg A B 𝔓 h𝔓 hH𝔓 hG ε M hM hsub
        Fcov (by simpa [hIdef] using hcov') (ptTheta θ (rep c))
        (by simpa [hIdef] using ptTheta_mem_hset_zero w θ hθ D P A B S T 𝔓 h2 (rep c) hs)
    have hprime_len (c : ℂ × (Fin ρ → ℂ)) (hc : c ∈ classes) :
        (((T + ellW w ε M).choose (ellW w ε M) : ℕ) : ℕ∞) ≤ primLen J (prime c) := by
      have hmem := (hrep c hc).1
      have hs : rep c ≤ S := Nat.lt_succ_iff.mp (Finset.mem_range.mp hmem)
      exact coset_length w θ D P hdeg A B T 𝔓 h𝔓 hH𝔓 hG ε M hM hsub (ptTheta θ (rep c))
        (hset_contains_steps w θ hθ D P A B S T 𝔓 h2 (rep c) hs)
        (by simpa [hJdef, hprimedef] using hprime_mem c hc)
    have hprime_InG (c : ℂ × (Fin ρ → ℂ)) : InG (ptTheta θ (rep c)) :=
      ptTheta_mem_InG θ hθ _
    have hprime_inj (c c' : ℂ × (Fin ρ → ℂ)) (hc : c ∈ classes) (hc' : c' ∈ classes)
        (heq : prime c = prime c') : c = c' := by
      have hclass := (cosetIdeal_eq_iff ε M hM _ _ (hprime_InG c) (hprime_InG c')).mp heq
      have hclass' : stepClass ε M θ (rep c) = stepClass ε M θ (rep c') :=
        (stepClass_eq_iff ε M θ hθ (rep c) (rep c')).mpr hclass
      rw [← (hrep c hc).2, ← (hrep c' hc').2]
      exact hclass'
    -- nonnegativity of `rayDeg (subIdeal ...)`
    have hdeg_nonneg : (0 : ℚ) ≤ rayDeg N (fsD D) (subIdeal N ρ ε M) :=
      rayDeg_nonneg_aux (fsD D) (subIdeal N ρ ε M)
    -- the sum over the classes is bounded by the partial sum over the primes
    have hsum_le : (∑ c ∈ classes,
          (((T + ellW w ε M).choose (ellW w ε M) : ℕ) : ℚ) * rayDeg N (fsD D) (subIdeal N ρ ε M))
        ≤ ∑ c ∈ classes, ((primLen J (prime c)).toNat : ℚ) * rayDeg N (fsD D) (prime c) := by
      refine Finset.sum_le_sum fun c hc => ?_
      rw [rayDeg_cosetIdeal (fsD D) (ptTheta θ (rep c)) (hprime_InG c) ρ ε M]
      have hC : (((T + ellW w ε M).choose (ellW w ε M) : ℕ) : ℚ) ≤
          ((primLen J (prime c)).toNat : ℚ) := by
        have h2' := hprime_len c hc
        rw [← ENat.natCast_toNat (primLen_ne_top J (prime c) (hprime_mem c hc))] at h2'
        exact_mod_cast h2'
      nlinarith [hdeg_nonneg]
    -- the sum over the primes is bounded by the Bezout bound
    have hsum_bound : (∑ c ∈ classes, ((primLen J (prime c)).toNat : ℚ) * rayDeg N (fsD D) (prime c))
        ≤ rayDeg N (fsD D) ⊥ := by
      have hinj : Set.InjOn prime (↑classes : Set (ℂ × (Fin ρ → ℂ))) :=
        fun a ha b hb h => hprime_inj a b ha hb h
      have himg : (∑ p ∈ classes.image prime, ((primLen J p).toNat : ℚ) * rayDeg N (fsD D) p)
          = ∑ c ∈ classes, ((primLen J (prime c)).toNat : ℚ) * rayDeg N (fsD D) (prime c) :=
        Finset.sum_image hinj
      rw [← himg]
      refine sum_minimalPrimes_le (fsD D) hD (bigGen w θ D P A B 𝔓) ?_ (classes.image prime) ?_
      · intro Q hQ
        obtain ⟨v, hv, Q₀, hQ₀, rfl⟩ := hQ
        obtain ⟨s, t, hs, ht, rfl⟩ := hQ₀
        exact (transl_basic v (gone N)).2.2.2.1 (fsD D) _
          ((transl_basic (ptTheta θ s) (gone N)).2.2.2.1 (fsD D) _
            ((derH_basic w).1 t (fsD D) (homog D P) (homog_basic D P hdeg).1))
      · intro p hp
        rw [Finset.mem_image] at hp
        obtain ⟨c, hc, rfl⟩ := hp
        exact ⟨hprime_mem c hc, meetsG_cosetIdeal ρ ε M (ptTheta θ (rep c)) (hprime_InG c)⟩
    -- the explicit value of the left-hand side
    have hcard : classes.card = cardMod ε M θ S := by
      rw [hclasses, cardMod]
      rfl
    have hLHS : (∑ c ∈ classes,
          (((T + ellW w ε M).choose (ellW w ε M) : ℕ) : ℚ) * rayDeg N (fsD D) (subIdeal N ρ ε M))
        = (((T + ellW w ε M).choose (ellW w ε M) : ℕ) : ℚ) * (cardMod ε M θ S : ℚ) *
            rayDeg N (fsD D) (subIdeal N ρ ε M) := by
      rw [Finset.sum_const, hcard, nsmul_eq_mul]
      ring
    have hbot : rayDeg N (fsD D) ⊥ = ((N + 1).factorial : ℚ) * ∏ i, (D i : ℚ) := by
      rw [(rayDeg_bot (fsD D) (by intro i; simpa [fsD] using hD i)).2.2]
      congr 1
    rw [← hLHS]
    refine le_trans hsum_le (le_trans hsum_bound ?_)
    rw [hbot]

end Work.BW

/-! ## Status of this node (for the project lead)

The proof below is complete: it uses only sibling nodes of this workspace (no local stand-ins, no
`sorry`).  At the time of writing, `#print axioms Work.BW.stab_step` reports exactly
`[propext, sorryAx, Classical.choice, Quot.sound]`, where the single `sorryAx` is inherited from
two *other* nodes that are still unfinished:

* `Submission/Work/BW/RB/A4.lean:179` (`Srel_cut`, the hypersurface-cutting step of the refined
  Bézout theorem) -- reached through `sum_minimalPrimes_le` / `refined_bezout`;
* `Submission/Work/BW/wuestholz_length.lean` (Wüstholz's multiplicity estimate) -- reached through
  `coset_length`.

As soon as those two are sorry-free and their `.olean`s rebuilt, this node becomes axiom-clean and
`declare_proven` applies (nothing here needs changing). -/
