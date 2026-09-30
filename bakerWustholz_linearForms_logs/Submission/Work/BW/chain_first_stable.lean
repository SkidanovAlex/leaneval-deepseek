import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.derH_basic
import Submission.Work.BW.transl_basic
import Submission.Work.BW.hset_zero_cosets_aux
import Submission.Work.BW.rayPoly_eq
import Submission.Work.BW.rayDim_lt_of_lt
import Submission.Work.BW.rayDeg_bot
import Submission.Work.BW.chainIdeal_le_ptIdeal_gone

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW multiplicity block B: the split of zero_estimate_stepwise, requests/bw3). Your node is `chain_first_stable`. Its doc comment gives the proof idea, size and dependencies; the design is below. Definitions: Submission.Work.BW.DefsB (imports DefsMult; lead-placed, do not edit). All 18 B-nodes are dispatched in parallel as Submission.Work.BW.<name>. Block-A nodes (rayHilb_poly, refined_bezout, subgroup_rayDeg, multiHom_assPrime, rayDeg_*) are live or proved. IMPORT siblings; never reprove them or restate them under another name. zero_estimate_stepwise (owner H32) is now the ASSEMBLY of these. If you believe your statement is false, give a concrete counterexample.

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

/-- The zero ideal is multihomogeneous. -/
private lemma multiHom_bot {N : ℕ} : MultiHom N (⊥ : Ideal (MR N)) := by
  intro p hp d
  rw [Submodule.mem_bot] at hp
  subst hp
  simp

/-- All generators of `chainIdeal` lie in the single piece `homPiece N (fsD D)`, so the chain
ideal is multihomogeneous. -/
private lemma chainIdeal_multiHom_aux {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (θ : Fin N → ℂ)
    (D : Fin (N + 1) → ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) (A B : ℕ)
    (hdeg : ∀ i, P.degreeOf i ≤ D i) : MultiHom N (chainIdeal w θ D P A B) := by
  letI : GradedAlgebra (MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N)) :=
    MvPolynomial.weightedGradedAlgebra ℂ (mdeg N)
  have hgen : ∀ x ∈ chainGen w θ D P A B,
      SetLike.IsHomogeneousElem (MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N)) x := by
    rintro x ⟨s, t, hs, ht, rfl⟩
    exact ⟨fsD D, (transl_basic (ptTheta θ s) (gone N)).2.2.2.1 (fsD D) _
      ((derH_basic w).1 t (fsD D) (homog D P) ((derH_basic w).2.2.2 D P hdeg).1)⟩
  have hI : (chainIdeal w θ D P A B).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N)) :=
    Ideal.homogeneous_span (MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N)) _ hgen
  intro p hp d
  exact (MvPolynomial.mem_iff_weightedHomogeneousComponent_mem ℂ (mdeg N) hI p).mp hp d

/-- A partial sum over `range (r-1)` is bounded by the partial sum over `range r`. -/
private lemma sum_range_sub {u : ℕ → ℕ} {r : ℕ} :
    (∑ m ∈ Finset.range (r - 1), u m) ≤ ∑ m ∈ Finset.range r, u m :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (Nat.sub_le r 1))
    (fun _ _ _ => Nat.zero_le _)

/-- `chainIdeal` is monotone in its two budgets. -/
private lemma chainIdeal_mono_aux {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (θ : Fin N → ℂ)
    (D : Fin (N + 1) → ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) {A B A' B' : ℕ}
    (hA : A ≤ A') (hB : B ≤ B') :
    chainIdeal w θ D P A B ≤ chainIdeal w θ D P A' B' := by
  refine Ideal.span_le.mpr ?_
  rintro F ⟨s, t, hs, ht, rfl⟩
  exact Ideal.subset_span ⟨s, t, le_trans hs hA, le_trans ht hB, rfl⟩

/-- An ideal meeting `G` has nonzero ray Hilbert polynomial: the ray Hilbert function is `≥ 1`
at every `t` (`hsc_rayHilb_pos_of_meetsG`), while a ray Hilbert polynomial exists by
`hsc_isRayPoly_of_multiHom`. -/
private lemma rayPoly_ne_zero_of_meetsG_aux {N : ℕ} (D : Fin (N + 1) →₀ ℕ)
    (hD : ∀ i, 1 ≤ D i) (I : Ideal (MR N)) (hI : MultiHom N I) (hG : MeetsG N I) :
    rayPoly N D I ≠ 0 := by
  obtain ⟨P, hP⟩ := hsc_isRayPoly_of_multiHom D hD I hI
  have hspec : IsRayPoly N D I (rayPoly N D I) := by
    rw [rayPoly, dif_pos (show ∃ q, IsRayPoly N D I q from ⟨P, hP⟩)]
    exact Classical.choose_spec _
  intro h0
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hspec
  have h1 : ((rayHilb N D I a : ℕ) : ℚ) = 0 := by
    rw [ha a le_rfl, h0]
    simp
  have h2 : (1 : ℚ) ≤ ((rayHilb N D I a : ℕ) : ℚ) := by
    exact_mod_cast hsc_rayHilb_pos_of_meetsG D I hG a
  linarith

/-- §5.1(b) (dimension pigeonhole). Put `I_r = chainIdeal` with budgets `∑_{m<r-1} Sq m`,
`∑_{m<r-1} Tq m`, and `d_r` = the largest `rayDim` of a minimal prime of `I_r` through `G`. The
hypothesis puts the neutral point in `Z(I_{N+2})`, so every `I_r` (`r ≤ N+2`) has such primes;
`d_1 ≤ N` (a nonzero `P^h` lies in each), `d_{r+1} ≤ d_r` (`rayDim_lt_of_lt`), so a first `r ≤ N+1`
with `d_r = d_{r+1}` exists and `d_r ≤ N + 1 − r`. A minimal prime of `I_{r+1}` through `G` of
dimension `d_{r+1}` contains a minimal prime of `I_r` through `G`, which must equal it.
Deps: `derH_basic`, `transl_basic`, `multiHom_assPrime`, `rayDim_lt_of_lt`, `rayDeg_bot`,
`rayPoly_ne_zero_of_meetsG`. Size 1–2k. -/
theorem chain_first_stable {N q : ℕ} (P : MvPolynomial (Fin (N + 1)) ℂ) (hP : P ≠ 0)
    (D : Fin (N + 1) → ℕ) (hD : ∀ i, 1 ≤ D i) (hdeg : ∀ i, P.degreeOf i ≤ D i)
    (w : Fin q → Fin (N + 1) → ℂ) (θ : Fin N → ℂ) (hθ : ∀ i, θ i ≠ 0) (Sq Tq : ℕ → ℕ)
    (hvan : ∀ s, s ≤ ∑ m ∈ Finset.range (N + 1), Sq m → ∀ t : Fin q → ℕ,
      ∑ k, t k ≤ ∑ m ∈ Finset.range (N + 1), Tq m →
      MvPolynomial.eval (ptTheta θ s) (applyW w t P) = 0) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ N + 1 ∧ ∃ 𝔓 : Ideal (MR N), 𝔓.IsPrime ∧ MeetsG N 𝔓 ∧
      𝔓 ∈ (chainIdeal w θ D P (∑ m ∈ Finset.range (r - 1), Sq m)
        (∑ m ∈ Finset.range (r - 1), Tq m)).minimalPrimes ∧
      chainIdeal w θ D P (∑ m ∈ Finset.range r, Sq m) (∑ m ∈ Finset.range r, Tq m) ≤ 𝔓 ∧
      (∀ p ∈ (chainIdeal w θ D P (∑ m ∈ Finset.range (r - 1), Sq m)
          (∑ m ∈ Finset.range (r - 1), Tq m)).minimalPrimes,
        MeetsG N p → rayDim N (fsD D) p ≤ rayDim N (fsD D) 𝔓) ∧
      rayDim N (fsD D) 𝔓 + r ≤ N + 1 := by
  classical
  have hDf : ∀ i, 1 ≤ fsD D i := fun i => by simpa [fsD] using hD i
  let A : ℕ → ℕ := fun r => ∑ m ∈ Finset.range (r - 1), Sq m
  let B : ℕ → ℕ := fun r => ∑ m ∈ Finset.range (r - 1), Tq m
  let I : ℕ → Ideal (MR N) := fun r => chainIdeal w θ D P (A r) (B r)
  have hIm : ∀ r, I r ≤ I (r + 1) :=
    fun r => chainIdeal_mono_aux w θ D P (sum_range_sub) (sum_range_sub)
  have hIh : ∀ r, MultiHom N (I r) :=
    fun r => chainIdeal_multiHom_aux w θ D P (A r) (B r) hdeg
  have hOnG : OnG N (conePt N (gone N)) := by
    refine ⟨?_, fun i => ⟨?_, ?_⟩⟩
    · simp [conePt]
    · simp [conePt]
    · simp [conePt, gone]
  have hbot : ∀ r, r ≤ N + 2 → I r ≤ ptIdeal N (conePt N (gone N)) :=
    fun r hr => chainIdeal_le_ptIdeal_gone P D hdeg w θ Sq Tq r hr hvan
  haveI hpt : (ptIdeal N (conePt N (gone N))).IsPrime := by
    rw [ptIdeal]; exact RingHom.ker_isPrime _
  have hMP : ∀ r, r ≤ N + 2 → ∃ p, p ∈ (I r).minimalPrimes ∧ MeetsG N p := by
    intro r hr
    obtain ⟨p, hpmin, hple⟩ := Ideal.exists_minimalPrimes_le (hbot r hr)
    exact ⟨p, hpmin, ⟨conePt N (gone N), hOnG, hple⟩⟩
  have hMH : ∀ r, ∀ p ∈ (I r).minimalPrimes, MultiHom N p :=
    fun r p hp => hsc_multiHom_minimalPrimes (hIh r) hp
  have hRP : ∀ r, ∀ p ∈ (I r).minimalPrimes, MeetsG N p → rayPoly N (fsD D) p ≠ 0 :=
    fun r p hp hG => rayPoly_ne_zero_of_meetsG_aux (fsD D) hDf p (hMH r p hp) hG
  have hray_mono : ∀ p q : Ideal (MR N), p.IsPrime → q.IsPrime → p ≤ q → MultiHom N p →
      MultiHom N q → rayPoly N (fsD D) q ≠ 0 → rayDim N (fsD D) q ≤ rayDim N (fsD D) p := by
    intro p q hpp hqp hpq hpm hqm hq0
    rcases eq_or_lt_of_le hpq with h | h
    · rw [← h]
    · exact le_of_lt (rayDim_lt_of_lt (fsD D) hDf p q hpp hqp hpm hqm h hq0)
  let finMin : ℕ → Finset (Ideal (MR N)) := fun r =>
    (Ideal.finite_minimalPrimes_of_isNoetherianRing (MR N) (I r)).toFinset
  have hfinMin : ∀ r p, p ∈ finMin r ↔ p ∈ (I r).minimalPrimes :=
    fun r p => Set.Finite.mem_toFinset (Ideal.finite_minimalPrimes_of_isNoetherianRing (MR N) (I r))
  let fDD : Ideal (MR N) → ℕ := fun p => if MeetsG N p then rayDim N (fsD D) p else 0
  let DD : ℕ → ℕ := fun r => (finMin r).sup fDD
  have hDD_le : ∀ r p, p ∈ (I r).minimalPrimes → MeetsG N p → rayDim N (fsD D) p ≤ DD r := by
    intro r p hp hG
    have hmem : p ∈ finMin r := (hfinMin r p).mpr hp
    have hle := Finset.le_sup (s := finMin r) (f := fDD) hmem
    simp only [DD, fDD, if_pos hG] at hle
    exact hle
  have hDD_spec : ∀ r, r ≤ N + 2 → ∃ p, p ∈ (I r).minimalPrimes ∧ MeetsG N p ∧
      rayDim N (fsD D) p = DD r := by
    intro r hr
    obtain ⟨p0, hp0min, hp0G⟩ := hMP r hr
    have hne : (finMin r).Nonempty := ⟨p0, (hfinMin r p0).mpr hp0min⟩
    obtain ⟨p, hpmem, hpsup⟩ := Finset.exists_mem_eq_sup (finMin r) hne fDD
    have hpm : p ∈ (I r).minimalPrimes := (hfinMin r p).mp hpmem
    by_cases hG : MeetsG N p
    · refine ⟨p, hpm, hG, ?_⟩
      show rayDim N (fsD D) p = (finMin r).sup fDD
      rw [hpsup]
      simp [fDD, hG]
    · have hzero : DD r = 0 := by
        show (finMin r).sup fDD = 0
        rw [hpsup]
        simp [fDD, hG]
      refine ⟨p0, hp0min, hp0G, ?_⟩
      have hle := hDD_le r p0 hp0min hp0G
      omega
  have hDD_mono : ∀ r, r ≤ N + 1 → DD (r + 1) ≤ DD r := by
    intro r hr
    obtain ⟨q, hqmin, hqG, hqdim⟩ := hDD_spec (r + 1) (by omega)
    have hqprime : q.IsPrime := hqmin.isPrime
    haveI : q.IsPrime := hqprime
    have hpq_le : I r ≤ q := le_trans (hIm r) hqmin.le
    obtain ⟨p, hpmin, hpq⟩ := Ideal.exists_minimalPrimes_le hpq_le
    have hpprime : p.IsPrime := hpmin.isPrime
    have hpG : MeetsG N p := hsc_meetsG_mono hpq hqG
    have hle : rayDim N (fsD D) q ≤ rayDim N (fsD D) p :=
      hray_mono p q hpprime hqprime hpq (hMH r p hpmin) (hMH (r + 1) q hqmin)
        (hRP (r + 1) q hqmin hqG)
    have h2 : rayDim N (fsD D) p ≤ DD r := hDD_le r p hpmin hpG
    omega
  have hDD_one : DD 1 ≤ N := by
    obtain ⟨p, hpmin, hpG, hpdim⟩ := hDD_spec 1 (by omega)
    have hpprime : p.IsPrime := hpmin.isPrime
    have hp0 : rayPoly N (fsD D) p ≠ 0 := hRP 1 p hpmin hpG
    have hpne : p ≠ ⊥ := by
      have hpth : ptTheta θ 0 = gone N := by funext i; simp [ptTheta, gone]
      have hapH : applyH w (0 : Fin q → ℕ) (homog D P) = homog D P := by simp [applyH]
      have hgen : homog D P ∈ chainGen w θ D P (A 1) (B 1) := by
        refine ⟨0, 0, Nat.zero_le _, by simp, ?_⟩
        rw [hpth, hapH, hsc_transl_gone]
      have hne : homog D P ≠ 0 := ((derH_basic w).2.2.2 D P hdeg).2.1 hP
      intro hpbot
      have hmem := hpmin.le (Ideal.subset_span hgen)
      rw [hpbot, Submodule.mem_bot] at hmem
      exact hne hmem
    have hlt := rayDim_lt_of_lt (fsD D) hDf ⊥ p Ideal.isPrime_bot hpprime multiHom_bot (hMH 1 p hpmin)
      (bot_lt_iff_ne_bot.mpr hpne) hp0
    have hbd : rayDim N (fsD D) ⊥ = N + 1 := (rayDeg_bot (fsD D) hDf).2.1
    rw [hbd] at hlt
    omega
  have hex : ∃ r, 1 ≤ r ∧ r ≤ N + 1 ∧ DD r = DD (r + 1) := by
    by_contra hcon
    push_neg at hcon
    have hdec : ∀ r, 1 ≤ r → r ≤ N + 1 → DD (r + 1) < DD r := by
      intro r h1 h2
      exact lt_of_le_of_ne (hDD_mono r h2) (Ne.symm (hcon r h1 h2))
    have hchain : ∀ k, k ≤ N + 1 → DD (k + 1) + k ≤ DD 1 := by
      intro k hk
      induction k with
      | zero => simp
      | succ k ih =>
        have ihk := ih (by omega)
        have hstep := hdec (k + 1) (by omega) (by omega)
        omega
    have hfin := hchain (N + 1) le_rfl
    omega
  let r0 : ℕ := Nat.find hex
  have hr0 : 1 ≤ r0 ∧ r0 ≤ N + 1 ∧ DD r0 = DD (r0 + 1) := Nat.find_spec hex
  have hr0min : ∀ j, 1 ≤ j → j ≤ N + 1 → DD j = DD (j + 1) → r0 ≤ j :=
    fun j h1 h2 h3 => Nat.find_min' hex ⟨h1, h2, h3⟩
  have hdec' : ∀ j, 1 ≤ j → j < r0 → DD (j + 1) < DD j := by
    intro j hj1 hjlt
    have hne : DD j ≠ DD (j + 1) := by
      intro heq
      have := hr0min j hj1 (by omega) heq
      omega
    exact lt_of_le_of_ne (hDD_mono j (by omega)) (Ne.symm hne)
  have hchain2 : ∀ k, k + 1 ≤ r0 → DD (k + 1) + k ≤ DD 1 := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have ihk := ih (by omega)
      have hstep := hdec' (k + 1) (by omega) (by omega)
      omega
  have hfin2 : DD r0 + r0 ≤ N + 1 := by
    have hc := hchain2 (r0 - 1) (by omega)
    rw [Nat.sub_add_cancel hr0.1] at hc
    have h1 := hDD_one
    omega
  obtain ⟨q, hqmin, hqG, hqdim⟩ := hDD_spec (r0 + 1) (by omega)
  have hqprime : q.IsPrime := hqmin.isPrime
  haveI : q.IsPrime := hqprime
  have hpq_le : I r0 ≤ q := le_trans (hIm r0) hqmin.le
  obtain ⟨p, hpmin, hpq⟩ := Ideal.exists_minimalPrimes_le hpq_le
  have hpprime : p.IsPrime := hpmin.isPrime
  have hpG : MeetsG N p := hsc_meetsG_mono hpq hqG
  have hdimle : rayDim N (fsD D) q ≤ rayDim N (fsD D) p :=
    hray_mono p q hpprime hqprime hpq (hMH r0 p hpmin) (hMH (r0 + 1) q hqmin)
      (hRP (r0 + 1) q hqmin hqG)
  have hpdim_le : rayDim N (fsD D) p ≤ DD r0 := hDD_le r0 p hpmin hpG
  have hpdim : rayDim N (fsD D) p = DD r0 := by
    refine le_antisymm hpdim_le ?_
    rw [hr0.2.2, ← hqdim]
    exact hdimle
  have hpqeq : p = q := by
    by_contra hne
    have hlt : p < q := lt_of_le_of_ne hpq hne
    have hcontra := rayDim_lt_of_lt (fsD D) hDf p q hpprime hqprime (hMH r0 p hpmin)
      (hMH (r0 + 1) q hqmin) hlt (hRP (r0 + 1) q hqmin hqG)
    rw [hpdim] at hcontra
    rw [hr0.2.2, ← hqdim] at hcontra
    exact absurd hcontra (lt_irrefl _)
  refine ⟨r0, hr0.1, hr0.2.1, p, hpprime, hpG, hpmin, ?_, ?_, ?_⟩
  · rw [hpqeq]; exact hqmin.le
  · intro p' hp' hp'G
    have := hDD_le r0 p' hp' hp'G
    rw [hpdim]
    exact this
  · rw [hpdim]; exact hfin2

end Work.BW
