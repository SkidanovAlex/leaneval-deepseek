import Mathlib
import Submission.Work.BW.DefsB

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW multiplicity block B: the split of zero_estimate_stepwise, requests/bw3). Your node is `vanish_span`. Its doc comment gives the proof idea, size and dependencies; the design is below. Definitions: Submission.Work.BW.DefsB (imports DefsMult; lead-placed, do not edit). All 18 B-nodes are dispatched in parallel as Submission.Work.BW.<name>. Block-A nodes (rayHilb_poly, refined_bezout, subgroup_rayDeg, multiHom_assPrime, rayDeg_*) are live or proved. IMPORT siblings; never reprove them or restate them under another name. zero_estimate_stepwise (owner H32) is now the ASSEMBLY of these. If you believe your statement is false, give a concrete counterexample.

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

open MvPolynomial (C X pderiv)

/-! ### Helper lemmas for `vanish_span`

The proof is self-contained (it only imports `DefsB`): we show that the set of `F` whose
translated `δ`-formal derivatives of order `≤ T` all lie in `𝔓` is an ideal, using the Leibniz
rule for the invariant derivation `derH` and the multiplicativity of the commuting family
`applyH w t` (Philippon 4.2–4.4). -/

/-- The variable by which `derH v` multiplies in the direction `(j,1)`: `X_{00}` for `j = 0`
(a translation along the `G_a` factor) and `X_{j1}` otherwise. -/
private def mulV {N : ℕ} (j : Fin (N + 1)) : Fin (N + 1) × Fin 2 :=
  if j = 0 then (0, 0) else (j, 1)

/-- `derH v` written as a single sum over `Fin (N+1)`. -/
private lemma derH_eq_sum {N : ℕ} (v : Fin (N + 1) → ℂ) (F : MR N) :
    derH v F = ∑ j : Fin (N + 1), C (v j) * X (mulV j) * pderiv (j, 1) F := by
  rw [derH, Fin.sum_univ_succ]
  simp only [mulV, ite_true, Fin.succ_ne_zero]
  simp

/-- Value of `derH v` on a coordinate variable. -/
private lemma derH_X {N : ℕ} (v : Fin (N + 1) → ℂ) (u : Fin (N + 1) × Fin 2) :
    derH v (X u) = if u.2 = 1 then C (v u.1) * X (mulV u.1) else 0 := by
  obtain ⟨j0, b⟩ := u
  rw [derH_eq_sum]
  simp only [MvPolynomial.pderiv_X]
  by_cases hb : b = 1
  · subst hb
    rw [Finset.sum_eq_single j0]
    · rw [Pi.single_eq_same]; simp
    · intro x _ hx
      rw [Pi.single_eq_of_ne (by intro h; exact hx (Prod.ext_iff.mp h).1.symm)]; simp
    · intro h; exact absurd (Finset.mem_univ j0) h
  · rw [Finset.sum_eq_zero]
    · simp [hb]
    · intro x _
      rw [Pi.single_eq_of_ne (by intro h; exact hb (congrArg Prod.snd h))]; simp

private lemma derH_X_mulV {N : ℕ} (v : Fin (N + 1) → ℂ) (j : Fin (N + 1)) :
    derH v (X (mulV j)) = if j = 0 then 0 else C (v j) * X (mulV j) := by
  rw [derH_X]
  by_cases hj : j = 0
  · subst hj; simp [mulV]
  · simp [mulV, hj]

private lemma derH_zero {N : ℕ} (v : Fin (N + 1) → ℂ) : derH v 0 = 0 := by simp [derH]

private lemma derH_C_mul {N : ℕ} (v : Fin (N + 1) → ℂ) (c : ℂ) (F : MR N) :
    derH v (C c * F) = C c * derH v F := by
  simp only [derH, MvPolynomial.pderiv_C_mul]
  rw [mul_add, Finset.mul_sum]
  ring_nf

/-- `derH v` as a genuine derivation. -/
private noncomputable def derHd {N : ℕ} (v : Fin (N + 1) → ℂ) :
    Derivation ℂ (MR N) (MR N) :=
  ∑ j : Fin (N + 1), (C (v j) * X (mulV j)) • pderiv (j, 1)

private lemma sum_deriv_apply {N : ℕ} (s : Finset (Fin (N + 1)))
    (D : Fin (N + 1) → Derivation ℂ (MR N) (MR N)) (F : MR N) :
    (∑ i ∈ s, D i) F = ∑ i ∈ s, D i F := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

private lemma derHd_apply {N : ℕ} (v : Fin (N + 1) → ℂ) (F : MR N) :
    derHd v F = derH v F := by
  rw [derH_eq_sum, derHd, sum_deriv_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [Derivation.smul_apply, smul_eq_mul]

private lemma derH_leibniz {N : ℕ} (v : Fin (N + 1) → ℂ) (a b : MR N) :
    derH v (a * b) = derH v a * b + a * derH v b := by
  rw [← derHd_apply, ← derHd_apply, ← derHd_apply, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
  ring

private lemma derH_add {N : ℕ} (v : Fin (N + 1) → ℂ) (F G : MR N) :
    derH v (F + G) = derH v F + derH v G := by
  rw [← derHd_apply, ← derHd_apply, ← derHd_apply, Derivation.map_add]

private lemma derH_comm {N : ℕ} (v v' : Fin (N + 1) → ℂ) (F : MR N) :
    derH v (derH v' F) = derH v' (derH v F) := by
  have h : ⁅derHd v, derHd v'⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro u
    simp only [Derivation.commutator_apply, derHd_apply, Derivation.zero_apply]
    by_cases h2 : u.2 = 1
    · by_cases h1 : u.1 = 0
      · rw [derH_X v' u, derH_X v u, ite_eq_left h2, ite_eq_left h2, derH_C_mul, derH_C_mul,
          derH_X_mulV, derH_X_mulV, ite_eq_left h1, ite_eq_left h1]
        simp
      · rw [derH_X v' u, derH_X v u, ite_eq_left h2, ite_eq_left h2, derH_C_mul, derH_C_mul,
          derH_X_mulV, derH_X_mulV, ite_eq_right h1, ite_eq_right h1]
        ring
    · rw [derH_X v' u, derH_X v u, ite_eq_right h2, ite_eq_right h2, derH_zero, derH_zero]
      ring
  have h2 : derH v (derH v' F) - derH v' (derH v F) = 0 := by
    have hh := Derivation.commutator_apply (D1 := derHd v) (D2 := derHd v') F
    rw [h, Derivation.zero_apply, derHd_apply, derHd_apply, derHd_apply, derHd_apply] at hh
    exact hh.symm
  exact sub_eq_zero.mp h2

private lemma derH_iterate_add {N : ℕ} (v : Fin (N + 1) → ℂ) (k : ℕ) (F G : MR N) :
    (derH v)^[k] (F + G) = (derH v)^[k] F + (derH v)^[k] G := by
  induction k with
  | zero => simp
  | succ k ih => simp only [Function.iterate_succ_apply']; rw [ih, derH_add]

private lemma derH_pow_comm {N : ℕ} (v v' : Fin (N + 1) → ℂ)
    (hcomm : ∀ F, derH v (derH v' F) = derH v' (derH v F)) (k : ℕ) (F : MR N) :
    derH v ((derH v')^[k] F) = (derH v')^[k] (derH v F) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hcomm, ih]

/-- The composition of the derivations `derH (w m)` with multiplicities `t m`, over a list
`l` (the definitional unfolding of `applyH` for `l = List.finRange q`). -/
private noncomputable def apFold {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (l : List (Fin q))
    (t : Fin q → ℕ) (F : MR N) : MR N :=
  l.foldr (fun m Q => (derH (w m))^[t m] Q) F

private lemma applyH_eq_apFold {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (t : Fin q → ℕ)
    (F : MR N) : applyH w t F = apFold w (List.finRange q) t F := rfl

private lemma apFold_cons {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (m : Fin q)
    (l : List (Fin q)) (t : Fin q → ℕ) (F : MR N) :
    apFold w (m :: l) t F = (derH (w m))^[t m] (apFold w l t F) := rfl

private lemma apFold_congr {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (l : List (Fin q))
    {u v : Fin q → ℕ} (h : ∀ m ∈ l, u m = v m) (F : MR N) :
    apFold w l u F = apFold w l v F := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    simp only [apFold_cons]
    rw [h m (by simp), ih (fun j hj => h j (by simp [hj]))]

private lemma apFold_eq_self {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (l : List (Fin q))
    (t : Fin q → ℕ) (F : MR N) (h : ∀ m ∈ l, t m = 0) : apFold w l t F = F := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    simp only [apFold_cons]
    rw [h m (by simp), ih (fun j hj => h j (by simp [hj]))]
    simp

private lemma apFold_add {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (l : List (Fin q))
    (t : Fin q → ℕ) (F G : MR N) :
    apFold w l t (F + G) = apFold w l t F + apFold w l t G := by
  induction l with
  | nil => rfl
  | cons m l ih => simp only [apFold_cons, ih, derH_iterate_add]

private lemma apFold_derH_comm {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (l : List (Fin q))
    {m : Fin q} (hm : m ∉ l) (t : Fin q → ℕ) (F : MR N) :
    derH (w m) (apFold w l t F) = apFold w l t (derH (w m) F) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have hm' : m ∉ l := fun h => hm (List.mem_cons_of_mem j h)
    have hmj : m ≠ j := fun h => hm (h ▸ List.mem_cons_self)
    simp only [apFold_cons]
    rw [derH_pow_comm (w m) (w j) (fun F => derH_comm _ _ F) (t j) (apFold w l t F), ih hm']

private lemma apFold_derH_iterate_comm {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ)
    (l : List (Fin q)) {m : Fin q} (hm : m ∉ l) (t : Fin q → ℕ) (k : ℕ) (F : MR N) :
    (derH (w m))^[k] (apFold w l t F) = apFold w l t ((derH (w m))^[k] F) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ_apply']
    rw [ih, apFold_derH_comm w l hm]

private lemma apFold_comp {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (l : List (Fin q))
    (hl : l.Nodup) (t t' : Fin q → ℕ) (F : MR N) :
    apFold w l t (apFold w l t' F) = apFold w l (t + t') F := by
  induction l with
  | nil => rfl
  | cons m l ih =>
    have hml : m ∉ l := (List.nodup_cons.mp hl).1
    have hl' : l.Nodup := (List.nodup_cons.mp hl).2
    simp only [apFold_cons, Pi.add_apply]
    rw [← apFold_derH_iterate_comm w l hml t (t' m), ← Function.iterate_add_apply, ih hl']

private lemma apFold_single {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (l : List (Fin q))
    (hl : l.Nodup) {m : Fin q} (hm : m ∈ l) (F : MR N) :
    apFold w l (Pi.single m 1) F = derH (w m) F := by
  induction l with
  | nil => simp at hm
  | cons j l ih =>
    have hj : j ∉ l := (List.nodup_cons.mp hl).1
    have hl' : l.Nodup := (List.nodup_cons.mp hl).2
    simp only [apFold_cons]
    by_cases hjm : j = m
    · subst hjm
      rw [Pi.single_eq_same]
      rw [apFold_eq_self w l (Pi.single j 1) F (fun k hk => by
        rw [Pi.single_eq_of_ne (by intro h; exact hj (h ▸ hk))])]
      simp
    · rw [Pi.single_eq_of_ne (by intro h; exact hjm h)]
      simp only [Function.iterate_zero_apply]
      exact ih hl' (by rcases List.mem_cons.mp hm with h | h
                       · exact absurd h.symm hjm
                       · exact h)

/-- `applyH w t` is additive. -/
private lemma applyH_add {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (t : Fin q → ℕ)
    (F G : MR N) : applyH w t (F + G) = applyH w t F + applyH w t G := by
  rw [applyH_eq_apFold, applyH_eq_apFold, applyH_eq_apFold, apFold_add]

/-- `applyH w 0` is the identity. -/
private lemma applyH_zero {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (F : MR N) :
    applyH w 0 F = F := by
  rw [applyH_eq_apFold]
  exact apFold_eq_self w (List.finRange q) 0 F (fun m _ => rfl)

private lemma derH_iterate_zero {N : ℕ} (v : Fin (N + 1) → ℂ) (k : ℕ) :
    (derH v)^[k] (0 : MR N) = 0 := by
  induction k with
  | zero => simp
  | succ k ih => simp only [Function.iterate_succ_apply']; rw [ih, derH_zero]

private lemma apFold_zero {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (l : List (Fin q))
    (t : Fin q → ℕ) : apFold w l t (0 : MR N) = 0 := by
  induction l with
  | nil => rfl
  | cons m l ih => simp only [apFold_cons, ih, derH_iterate_zero]

/-- `applyH w t` kills `0`. -/
private lemma applyH_zero_el {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (t : Fin q → ℕ) :
    applyH w t (0 : MR N) = 0 := by
  rw [applyH_eq_apFold]
  exact apFold_zero w (List.finRange q) t

/-- The formal derivatives compose: `applyH w t ∘ applyH w t' = applyH w (t + t')`. -/
private lemma applyH_compose {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (t t' : Fin q → ℕ)
    (F : MR N) : applyH w t (applyH w t' F) = applyH w (t + t') F := by
  rw [applyH_eq_apFold, applyH_eq_apFold, applyH_eq_apFold,
    apFold_comp w (List.finRange q) (List.nodup_finRange q)]

private lemma applyH_single {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (m : Fin q) (F : MR N) :
    applyH w (Pi.single m 1) F = derH (w m) F := by
  rw [applyH_eq_apFold]
  exact apFold_single w (List.finRange q) (List.nodup_finRange q) (List.mem_finRange m) F

private lemma sum_single {q : ℕ} (m : Fin q) : (∑ i : Fin q, (Pi.single m (1 : ℕ)) i) = 1 := by
  rw [Finset.sum_eq_single m]
  · simp
  · intro i _ hi
    rw [Pi.single_eq_of_ne (i := m) (i' := i) (by intro h; exact hi h)]
  · intro h; exact absurd (Finset.mem_univ m) h

/-- Closure of the vanishing condition under multiplication by an arbitrary polynomial. -/
private lemma smul_vanish {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (g : Fin (N + 1) → ℂ)
    (_T : ℕ) (𝔓 : Ideal (MR N)) :
    ∀ (k : ℕ) (a F : MR N),
      (∀ t' : Fin q → ℕ, (∑ i, t' i) ≤ k → transl g (applyH w t' F) ∈ 𝔓) →
      ∀ t : Fin q → ℕ, (∑ i, t i) ≤ k → transl g (applyH w t (a * F)) ∈ 𝔓 := by
  intro k
  induction k with
  | zero =>
    intro a F hF t ht
    have ht0 : t = 0 := funext fun i =>
      Nat.eq_zero_of_le_zero
        (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)) ht)
    rw [ht0, applyH_zero, map_mul]
    refine Ideal.mul_mem_left 𝔓 (transl g a) ?_
    simpa [applyH_zero] using hF 0 (by simp)
  | succ k ih =>
    intro a F hF t ht
    by_cases ht0 : (∑ i, t i) = 0
    · have ht_zero : t = 0 := funext fun i =>
        Nat.eq_zero_of_le_zero
          (le_trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
            (le_of_eq ht0))
      rw [ht_zero, applyH_zero, map_mul]
      refine Ideal.mul_mem_left 𝔓 (transl g a) ?_
      simpa [applyH_zero] using hF 0 (by simp)
    · obtain ⟨m, -, hm⟩ := Finset.exists_ne_zero_of_sum_ne_zero ht0
      have ht_eq : Function.update t m (t m - 1) + Pi.single m 1 = t := by
        funext i
        rw [Pi.add_apply, Function.update_apply]
        by_cases hi : i = m
        · subst hi
          rw [ite_eq_left rfl, Pi.single_eq_same]
          exact Nat.sub_add_cancel (Nat.pos_of_ne_zero hm)
        · rw [ite_eq_right (by intro h; exact hi h),
              Pi.single_eq_of_ne (i := m) (i' := i) (by intro h; exact hi h)]
          simp
      have hsum : (∑ i, Function.update t m (t m - 1) i) + 1 = ∑ i, t i := by
        have h := congrArg (fun s : Fin q → ℕ => ∑ i, s i) ht_eq
        simp only [Pi.add_apply, Finset.sum_add_distrib, sum_single] at h
        exact h
      have ht'le : (∑ i, Function.update t m (t m - 1) i) ≤ k := by omega
      rw [← ht_eq, ← applyH_compose, applyH_single, derH_leibniz, applyH_add, map_add]
      refine 𝔓.add_mem ?_ ?_
      · exact ih (derH (w m) a) F (fun s hs => hF s (le_trans hs (Nat.le_succ k)))
          (Function.update t m (t m - 1)) ht'le
      · refine ih a (derH (w m) F) (fun u hu => ?_) (Function.update t m (t m - 1)) ht'le
        rw [← applyH_single, applyH_compose]
        refine hF (u + Pi.single m 1) ?_
        have hu' : (∑ i, (u i + (Pi.single m (1 : ℕ) : Fin q → ℕ) i)) = (∑ i, u i) + 1 := by
          rw [Finset.sum_add_distrib, sum_single]
        have hb : (∑ i, ((u + Pi.single m 1) : Fin q → ℕ) i) = (∑ i, u i) + 1 := hu'
        rw [hb]
        omega

/-- B1c (Philippon 4.2–4.4, the part used). Vanishing to order `> T` along `W` after translation
by `g` passes from a generating set to the ideal it spans (Leibniz rule for the commuting
`derH`, and `transl g` is a ring map). Size 0.8–1.5k. -/
theorem vanish_span {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (g : Fin (N + 1) → ℂ) (T : ℕ)
    (𝔓 : Ideal (MR N)) (S : Set (MR N))
    (hS : ∀ F ∈ S, ∀ t : Fin q → ℕ, ∑ k, t k ≤ T → transl g (applyH w t F) ∈ 𝔓) :
    ∀ F ∈ Ideal.span S, ∀ t : Fin q → ℕ, ∑ k, t k ≤ T → transl g (applyH w t F) ∈ 𝔓 := by
  let V : Ideal (MR N) :=
    { carrier := {F | ∀ t : Fin q → ℕ, (∑ k, t k) ≤ T → transl g (applyH w t F) ∈ 𝔓}
      add_mem' := by
        intro F G hF hG t ht
        rw [applyH_add, map_add]
        exact 𝔓.add_mem (hF t ht) (hG t ht)
      zero_mem' := by
        intro t _
        rw [applyH_zero_el, map_zero]
        exact 𝔓.zero_mem
      smul_mem' := by
        intro a F hF t ht
        rw [smul_eq_mul]
        exact smul_vanish w g T 𝔓 T a F hF t ht }
  intro F hF t ht
  have hVS : S ⊆ (V : Set (MR N)) := fun x hx => hS x hx
  have hspan : F ∈ V := Ideal.span_le.mpr hVS hF
  exact hspan t ht

end Work.BW
