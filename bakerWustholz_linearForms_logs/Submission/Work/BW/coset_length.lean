import Mathlib
import Submission.Work.BW.DefsB
import Submission.Work.BW.transl_basic
import Submission.Work.BW.hset_zero_cosets_aux
import Submission.Work.BW.gmul_mem_ZG_of_stab
import Submission.Work.BW.derH_transl
import Submission.Work.BW.homog_basic
import Submission.Work.BW.vanish_span
import Submission.Work.BW.wuestholz_length
import Submission.Work.BW.primLen_map_ringEquiv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW block B, phase-4 fix). Your node is `coset_length`. Definitions: Submission.Work.BW.DefsB. PHASE4_FIXES.md below gives the verdicts and the proof routes (the coset_minimalPrime full proof via mem_of_vanish_ZG plus the helpers; coset_length = wuestholz_length transported by τ_σ, applied directly with no ρ case split). Import siblings; do not reprove them. If a previous owner's partial file exists at ~/snapshots/bw-coset-0927/<name>.lean, you may reuse it (its statement lacked hdeg).

===== PHASE4_FIXES.md =====
# Phase 4: verdicts on the owners' bw3 defect reports (2026-09-27)

**Summary.** None of the four reports shows a false statement. They do expose one real gap of
mine: `coset_minimalPrime` and `coset_length` lack `hdeg`. That fix only adds a hypothesis. I also
add 5 helper nodes that fill routing gaps in `stab_step`, `coset_minimalPrime` and `coset_length`.

**Sources.**
* The live statements in 3.144 `Submission/Work/BW/*.lean`.
* The probes in `probes/0927-1905/`.

**Owners** (from `enqueue.py --status`):

| probe | node |
|---|---|
| H183 | `coset_length` |
| H185 | `coset_minimalPrime` |
| H186 | `mem_of_vanish_ZG` |
| H187 | `stab_step` |

**Elaboration check.** `bw3/fix/*.lean` was tested on 3.144 against `import Submission.Work.BW.DefsB`,
with `systemd-run --user --scope -q -p MemoryMax=12G lake env lean`. Result: 7 `sorry` warnings, no
errors, and no name clashes with the workspace.

## Verdicts

### H187 on `hset_zero_cosets`: "covers H_V(0) by stabG, not by a finite-index G′"

**As designed, not a defect.**
* The statement and its doc comment agree: both say "cosets of the stabiliser".
* The finite-index `G'` enters through `closedSub_structure`. The design already had `stab_step`
  combine the two covers.
* The live file is being proved along exactly that line (`hsc_*` aux, the `Φ g` minimal-prime
  argument).

**To make it explicit** I added **`hset_zero_subcosets`**, which composes the two covers
(0.2–0.4k).

### H187 on `coset_length`: "states `primLen J (cosetIdeal σ)` but `wuestholz_length` is about `primLen J (subIdeal)`"

**As designed, not a defect.**
* `coset_length` is the translate of `wuestholz_length` by the ring automorphism `τ_σ`. H183's child
  `primLen_ringEquiv` is exactly that transport step.
* `τ_σ` carries `cosetIdeal σ = τ_{σ⁻¹}(I(G'))` to `I(G')` and `J'` to `τ_σ J'`. It preserves
  `primLen` and minimal primes, and it commutes with `applyH`.

### H187 on `refined_bezout`: "`primLen.toNat` vs `ℕ`"

**A real gap for `stab_step`, but not a false statement.**
* `stab_step` needs `C ≤ primLen` in `ℕ∞` to give `C ≤ primLen.toNat`. That requires
  `primLen ≠ ⊤` at minimal primes. It is true: the localisation at a minimal prime is Artinian.
* **Fix: new node `primLen_ne_top`** (0.4–0.8k).

### H187: "MeetsG / MultiHom hypotheses unused, an unmotivated inequality"

**Not a defect.** Every such hypothesis is used:
* `hset_zero_cosets`:
  * `MeetsG 𝔓` makes each translate `τ_{g⁻¹}𝔓` pass through `G`, so that `rayDim_lt_of_lt` and
    `hmax` apply;
  * `MultiHom I` makes the minimal primes multihomogeneous.
* `coset_*`: `MultiHom 𝔓` and `MeetsG 𝔓` are exactly the hypotheses of `mem_of_vanish_ZG`.

`stab_step` has no `MultiHom` hypothesis. Its `MeetsG` feeds `hset_zero_cosets` and the
`dim G' ≤ dim 𝔓` step: pick `v ∈ ZG 𝔓`, then `v ⋆ G' ⊆ V`.

### H186 on `mem_of_vanish_ZG`: "a cone point of Z(𝔓) scaled by arbitrary λ lands back in ZG 𝔓"

**The statement is true (the owner agrees). The route claim is false only in its literal
"arbitrary λ" form.**
* **What is true and needed.** Take `𝔓` multihomogeneous and a cone point `x ∈ Z(𝔓)` with `OnG x`.
  Scale **factor by factor** by the **nonzero** `λ_i = x(i,0)⁻¹`. Each multihomogeneous component
  `G_d` of an element of `𝔓` satisfies `G_d(λx) = λ^d G_d(x) = 0`. So `λx = conePt y` with
  `y_i = x(i,1)/x(i,0) ≠ 0`, and `y ∈ ZG 𝔓`.
* **What is false.** With `λ_i = 0` the scaled point leaves `G`. With different scalars on the two
  coordinates of one `P¹` factor, the claim fails: take `𝔓 = (X₀₁ − X₀₀)` and scale only `X₀₁`.
* Points with `¬OnG x` are killed by `Π = X₀₀∏X_{i0}X_{i1}`.

**No statement change.** Advice: scale by the specific `x(i,0)⁻¹` per factor.

### H185 on `coset_minimalPrime`: "the isolation claim is false; Zariski density of ZG 𝔓 in Z(𝔓) is needed"

**The isolation claim is true. The density it needs is exactly `mem_of_vanish_ZG`**
(`𝔓 = I(ZG 𝔓)` for a multihomogeneous prime through `G`).

Proof. Take a prime `q` with `J' ≤ q ≤ cosetIdeal σ`.
1. Choose a minimal prime `p` of `J'` with `p ≤ q`. It is multihomogeneous and passes through `G`.
2. `ZG p ⊆ Z_G(J') ⊆ H_V(0)`, by **`ZG_bigGen_sub_Hset`** (new; this is where `mem_of_vanish_ZG`
   enters). `H_V(0)` lies in `⋃_k f_k G'` by `hcov`.
3. Suppose `p` contains no `cosetIdeal f_k`. Pick multihomogeneous `F_k ∈ cosetIdeal f_k \ p`. Then
   `∏F_k` vanishes on the cone points over `ZG p`, so `∏F_k ∈ p` by `mem_of_vanish_ZG`. This
   contradicts primality.
4. Hence `cosetIdeal f_k ≤ p ≤ cosetIdeal σ` for some `k`. So `σG'` lies in the zero set in `G` of
   `cosetIdeal f_k`, which is `f_k G'` by **`InSub_of_subIdeal`** (new: cosets are closed in `G`).
   So `σG' = f_kG'`, and `p = q = cosetIdeal σ`.
5. `J' ≤ cosetIdeal σ` uses **`gmul_mem_ZG_of_stab`** (new: `V ⋆ G_V = V`) and `σ ∈ H_V(0)`.

**The real defect found here is mine.** The route applies `mem_of_vanish_ZG` to `τ_y Q`, which
must be multihomogeneous. `homog D P` is multihomogeneous only when `degreeOf i P ≤ D i`, and
`coset_minimalPrime` did not assume that. **Fix: add `hdeg`.**
* This only adds a hypothesis, so any partial proof stays valid.
* `stab_step` has `hdeg` and passes it on.
* I found no counterexample to the old statement. The fix is needed for the route, not for truth.

### H183 on `coset_length`: "the general 0<ρ<N case needs `wuestholz_length` to fire, which needs cosetIdeal minimal over J′"

**Not a defect.** Minimality is the hypothesis `hmin` of `coset_length`, which `coset_minimalPrime`
supplies in `stab_step`. No case split on `ρ` is needed. Transport by `τ_σ` and apply
`wuestholz_length` directly:
* `hJ`: the automorphism `τ_σ` maps `minimalPrimes J'` to `minimalPrimes (τ_σ J')`, and
  `τ_σ(cosetIdeal σ) = subIdeal`.
* `hT`:
  1. On a generator, `applyH t (τ_σ τ_v Q) = τ_{σv}(δ^t Q)`. It vanishes at `conePt u` for
     `u ∈ G'`, because `v u ∈ ZG 𝔓` (`gmul_mem_ZG_of_stab`) and `σ ∈ H_V(T)`. Being
     multihomogeneous (**needs `hdeg`**), it lies in `subIdeal`.
  2. Pass to the span with `vanish_span` (`g = gone`, `𝔓 := subIdeal`).

**Fix: add `hdeg`** (same reason and same remarks as for `coset_minimalPrime`).

## Does §5.1 still assemble `zero_estimate_stepwise`?

**Yes.** The statement of `zero_estimate_stepwise` and those of `stab_step`, `chain_first_stable`,
`hset_contains_steps`, `hset_zero_cosets`, `wuestholz_length` and `mem_of_vanish_ZG` are unchanged.
In `stab_step`:
1. **`G'`:** `stab_closedSub` and `closedSub_structure` give `G'` and the cover `Fg`.
2. **Covering `H_V(0)`:** `hset_zero_cosets` gives the cover `Fs`; `hset_zero_subcosets` composes
   the two into the `hcov` input.
3. **Step points:** `hset_contains_steps` puts `ptTheta θ s ∈ H_V(T) ⊆ H_V(0)` for `s ≤ S`.
4. **Per coset class** (with `hdeg`):
   * `coset_minimalPrime` shows `cosetIdeal σ` is a minimal prime of `J'`;
   * `coset_length` gives length `≥ C(T+ℓ,ℓ)`;
   * `primLen_ne_top` converts that to `toNat`;
   * `rayHilb_transl` gives `rayDeg = rayDeg(subIdeal)`.
5. **Distinctness:** distinct classes of `{0..S}γ` mod `G'` give distinct coset ideals (by
   `InSub_of_subIdeal`), `cardMod` of them in all.
6. **Bound:** `refined_bezout` on `bigGen` (in `homPiece (fsD D)` by `derH_basic`/`transl_basic`),
   restricted to this subfamily, plus `rayDeg_bot`.
7. **Dimension:** `dim G' ≤ dim 𝔓` from `v ⋆ G' ⊆ V`, `rayHilb` monotonicity and `rayHilb_transl`.

## Node actions for the lead

**Re-dispatch** (add the hypothesis in place; existing partial proofs stay valid):
* `coset_minimalPrime`: adds `(hdeg : ∀ i, P.degreeOf i ≤ D i)` after `P`.
* `coset_length`: adds the same.

**New nodes** (dispatch; each is small):

| node | size (k lines) | serves |
|---|---|---|
| `primLen_ne_top` | 0.4–0.8 | `stab_step` |
| `hset_zero_subcosets` | 0.2–0.4 | `stab_step` |
| `InSub_of_subIdeal` | 0.5–1 | `coset_minimalPrime`, `stab_step` |
| `gmul_mem_ZG_of_stab` | 0.2–0.4 | `coset_minimalPrime`, `coset_length` |
| `ZG_bigGen_sub_Hset` | 0.5–0.8 | `coset_minimalPrime` |

**Unchanged:** `hset_zero_cosets`, `mem_of_vanish_ZG`, `stab_step`, `wuestholz_length`,
`refined_bezout`, `zero_estimate_stepwise`.
-/

namespace Work.BW


open MvPolynomial (C X)

variable {N : ℕ}

/-- `transl σ` is a ring automorphism of the homogeneous coordinate ring when `σ ∈ G`
(it has the two-sided inverse `transl (σ⁻¹)`). -/
noncomputable def tauEquiv (σ : Fin (N + 1) → ℂ) (hσ : InG σ) : MR N ≃+* MR N :=
  RingEquiv.ofBijective (transl σ : MR N →+* MR N)
    ⟨Function.LeftInverse.injective (fun F => hsc_transl_inv hσ F), hsc_transl_surj hσ⟩

lemma tauEquiv_apply (σ : Fin (N + 1) → ℂ) (hσ : InG σ) (F : MR N) :
    tauEquiv σ hσ F = transl σ F := rfl

lemma map_tauEquiv (σ : Fin (N + 1) → ℂ) (hσ : InG σ) (I : Ideal (MR N)) :
    Ideal.map ((tauEquiv σ hσ : MR N ≃+* MR N) : MR N →+* MR N) I = Ideal.map (transl σ) I := by
  congr 1


/-! ### The pieces of `derH_basic` used here

`derH_basic` (owned by a sibling node) collects the multidegree calculus of `applyH`.  Until that
module is available the three facts needed below are reproduced here privately: `applyH` preserves
every multidegree piece, `transl` commutes with `applyH`, and (from the sibling modules
`derH_transl` and `homog_basic`, which are imported) `derH` commutes with `transl` and `homog` lands
in the expected piece. -/

section DerHPieces

variable {N : ℕ}

private lemma weight_single_add_sub_single {u v : Fin (N + 1) × Fin 2}
    (huv : mdeg N u = mdeg N v) (m : (Fin (N + 1) × Fin 2) →₀ ℕ) (hmv : m v ≠ 0) :
    Finsupp.weight (mdeg N) (Finsupp.single u 1 + (m - Finsupp.single v 1)) =
      Finsupp.weight (mdeg N) m := by
  have h1 := Finsupp.weight_sub_single_add (w := mdeg N) hmv
  calc Finsupp.weight (mdeg N) (Finsupp.single u 1 + (m - Finsupp.single v 1))
      = Finsupp.weight (mdeg N) (Finsupp.single u 1) +
          Finsupp.weight (mdeg N) (m - Finsupp.single v 1) := map_add _ _ _
    _ = mdeg N u + Finsupp.weight (mdeg N) (m - Finsupp.single v 1) := by
        rw [Finsupp.weight_single, one_smul]
    _ = mdeg N v + Finsupp.weight (mdeg N) (m - Finsupp.single v 1) := by rw [huv]
    _ = Finsupp.weight (mdeg N) (m - Finsupp.single v 1) + mdeg N v := add_comm _ _
    _ = Finsupp.weight (mdeg N) m := h1

private lemma X_mul_pderiv_monomial (u v : Fin (N + 1) × Fin 2)
    (m : (Fin (N + 1) × Fin 2) →₀ ℕ) (a : ℂ) :
    (MvPolynomial.X u : MR N) * MvPolynomial.pderiv v (MvPolynomial.monomial m a) =
      MvPolynomial.monomial (Finsupp.single u 1 + (m - Finsupp.single v 1)) (a * (m v : ℂ)) := by
  rw [MvPolynomial.pderiv_monomial, ← pow_one (MvPolynomial.X u), MvPolynomial.X_pow_eq_monomial,
    MvPolynomial.monomial_mul_monomial]
  simp

private lemma X_mul_pderiv_mem {u v : Fin (N + 1) × Fin 2} (huv : mdeg N u = mdeg N v)
    {d : Fin (N + 1) →₀ ℕ} {F : MR N} (hF : F ∈ homPiece N d) :
    MvPolynomial.X u * MvPolynomial.pderiv v F ∈ homPiece N d := by
  have hF' : F ∈ MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N) d := hF
  show MvPolynomial.X u * MvPolynomial.pderiv v F ∈
    MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N) d
  rw [MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported,
      AddMonoidAlgebra.supported_eq_span_single] at hF'
  refine Submodule.span_induction (p := fun x _ =>
    MvPolynomial.X u * MvPolynomial.pderiv v x ∈
      MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N) d) ?_ ?_ ?_ ?_ hF'
  · rintro x ⟨m, hm, rfl⟩
    change MvPolynomial.X u * MvPolynomial.pderiv v (MvPolynomial.monomial m 1) ∈
      MvPolynomial.weightedHomogeneousSubmodule ℂ (mdeg N) d
    rw [X_mul_pderiv_monomial]
    by_cases h : m v = 0
    · rw [h]; simp
    · rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
      refine MvPolynomial.isWeightedHomogeneous_monomial (mdeg N) _ _ ?_
      rw [weight_single_add_sub_single huv m h, hm]
  · simp
  · intro x y _ _ hp hq
    rw [map_add, mul_add]
    exact add_mem hp hq
  · intro a x _ hp
    rw [Derivation.map_smul, mul_smul_comm]
    exact Submodule.smul_mem _ _ hp

private lemma C_mul_mem_homPiece {c : ℂ} {d : Fin (N + 1) →₀ ℕ} {G : MR N}
    (hG : G ∈ homPiece N d) : MvPolynomial.C c * G ∈ homPiece N d := by
  rw [MvPolynomial.C_mul']
  exact Submodule.smul_mem _ _ hG

private lemma derH_mem_homPiece (w : Fin (N + 1) → ℂ) {d : Fin (N + 1) →₀ ℕ} {F : MR N}
    (hF : F ∈ homPiece N d) : derH w F ∈ homPiece N d := by
  rw [derH]
  refine add_mem ?_ ?_
  · rw [mul_assoc]
    exact C_mul_mem_homPiece (X_mul_pderiv_mem (by rfl : mdeg N (0, 0) = mdeg N (0, 1)) hF)
  · refine Submodule.sum_mem _ fun i _ => ?_
    rw [mul_assoc]
    exact C_mul_mem_homPiece
      (X_mul_pderiv_mem (by rfl : mdeg N (i.succ, 1) = mdeg N (i.succ, 1)) hF)

private lemma iterate_mem {α : Type*} {S : Set α} {f : α → α} (hf : ∀ x ∈ S, f x ∈ S) :
    ∀ (n : ℕ) (x : α), x ∈ S → (f^[n]) x ∈ S := by
  intro n
  induction n with
  | zero => intro x hx; simpa using hx
  | succ n ih => intro x hx; rw [Function.iterate_succ_apply']; exact hf _ (ih x hx)

private lemma foldr_mem {ι α : Type*} (L : List ι) (f : ι → α → α) (S : Set α)
    (hf : ∀ i ∈ L, ∀ x ∈ S, f i x ∈ S) (x : α) (hx : x ∈ S) :
    L.foldr (fun i Q => f i Q) x ∈ S := by
  induction L with
  | nil => simpa using hx
  | cons a L ih =>
    simp only [List.foldr_cons]
    exact hf a List.mem_cons_self _ (ih (fun i hi => hf i (List.mem_cons_of_mem a hi)))

/-- `applyH w t` preserves every multidegree piece. -/
private lemma applyH_mem {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (t : Fin q → ℕ)
    {d : Fin (N + 1) →₀ ℕ} {F : MR N} (hF : F ∈ homPiece N d) :
    applyH w t F ∈ homPiece N d := by
  rw [applyH]
  refine foldr_mem (List.finRange q) (fun m Q => (derH (w m))^[t m] Q) (homPiece N d) ?_ F hF
  intro m _ x hx
  exact iterate_mem (f := derH (w m)) (fun y hy => derH_mem_homPiece (w m) hy) (t m) x hx

private lemma iterate_transl (g w : Fin (N + 1) → ℂ) (n : ℕ) (F : MR N) :
    transl g (((derH w)^[n]) F) = ((derH w)^[n]) (transl g F) := by
  induction n generalizing F with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', derH_transl, ih]

private lemma foldr_transl {ι : Type*} (L : List ι) (f : ι → MR N → MR N)
    (g : Fin (N + 1) → ℂ)
    (hf : ∀ i ∈ L, ∀ Q, transl g (f i Q) = f i (transl g Q)) (F : MR N) :
    transl g (L.foldr (fun i Q => f i Q) F) = L.foldr (fun i Q => f i Q) (transl g F) := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    simp only [List.foldr_cons]
    rw [hf a List.mem_cons_self]
    rw [ih (fun i hi => hf i (List.mem_cons_of_mem a hi))]

/-- `transl g` commutes with `applyH w t`. -/
private lemma applyH_transl {N q : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (g : Fin (N + 1) → ℂ)
    (t : Fin q → ℕ) (F : MR N) :
    transl g (applyH w t F) = applyH w t (transl g F) := by
  rw [applyH, applyH]
  exact foldr_transl (List.finRange q) (fun m Q => (derH (w m))^[t m] Q) g
    (fun m _ Q => iterate_transl g (w m) (t m) Q) F

end DerHPieces

/-- `transl σ` maps a prime ideal to a prime ideal (its kernel is trivial). -/
lemma isPrime_map_transl (σ : Fin (N + 1) → ℂ) (hσ : InG σ) {p : Ideal (MR N)}
    (hp : p.IsPrime) : (Ideal.map (transl σ) p).IsPrime := by
  haveI := hp
  refine Ideal.map_isPrime_of_surjective (f := (transl σ : MR N →+* MR N))
    (hsc_transl_surj hσ) ?_
  intro x hx
  have hx' : transl σ x = 0 := by
    rw [← RingHom.coe_coe (transl σ)]
    exact RingHom.mem_ker.mp hx
  have h0 : x = 0 := by rw [← hsc_transl_inv hσ x, hx', map_zero]
  rw [h0]
  exact p.zero_mem

/-- `transl σ` carries the coset ideal `τ_{σ⁻¹}I(G')` back to `I(G')`. -/
lemma transl_map_cosetIdeal {N ρ : ℕ} (σ : Fin (N + 1) → ℂ) (hσ : InG σ) (ε : Bool)
    (M : Fin ρ → Fin N → ℤ) :
    Ideal.map (transl σ) (cosetIdeal σ ε M) = subIdeal N ρ ε M := by
  rw [cosetIdeal]
  exact hsc_map_transl_map_ginv hσ (subIdeal N ρ ε M)



/-- One generator step of `coset_length`: for `v ∈ ZG 𝔓` and `sγ`-translate of `δ^{t'}P^h`, the
translated derivative `δ^t (τ_σ τ_v τ_{sγ} δ^{t'}P^h)`, `|t| ≤ T`, is multihomogeneous of
multidegree `D` and vanishes on `G'`, hence lies in `I(G') = subIdeal`. -/
private lemma step_gen {N q ρ : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (θ : Fin N → ℂ)
    (D : Fin (N + 1) → ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) (hdeg : ∀ i, P.degreeOf i ≤ D i)
    (A B T : ℕ) (𝔓 : Ideal (MR N)) (ε : Bool) (M : Fin ρ → Fin N → ℤ)
    (hsub : subSet N ρ ε M ⊆ stabG 𝔓) (σ : Fin (N + 1) → ℂ) (hσG : InG σ)
    (hσH : ∀ F ∈ chainIdeal w θ D P A B, ∀ t : Fin q → ℕ, ∑ k, t k ≤ T →
      transl σ (applyH w t F) ∈ 𝔓)
    (s : ℕ) (hs : s ≤ A) (t' : Fin q → ℕ) (ht' : ∑ k, t' k ≤ B)
    (v : Fin (N + 1) → ℂ) (hv : v ∈ ZG 𝔓) (t : Fin q → ℕ) (ht : ∑ k, t k ≤ T) :
    transl σ (applyH w t (transl v (transl (ptTheta θ s) (applyH w t' (homog D P))))) ∈
      subIdeal N ρ ε M := by
  set Q₀ : MR N := transl (ptTheta θ s) (applyH w t' (homog D P)) with hQ₀def
  have hQ₀mem : Q₀ ∈ homPiece N (fsD D) := by
    rw [hQ₀def]
    exact hsc_transl_homPiece (ptTheta θ s) (fsD D)
      (applyH_mem w t' (homog_basic D P hdeg).1)
  have hQ₀I : Q₀ ∈ chainIdeal w θ D P A B := by
    rw [hQ₀def, chainIdeal]
    exact Ideal.subset_span ⟨s, t', hs, ht', rfl⟩
  have hH : transl σ (applyH w t Q₀) ∈ 𝔓 := hσH Q₀ hQ₀I t ht
  have hgoal : transl σ (applyH w t (transl v Q₀)) = transl v (transl σ (applyH w t Q₀)) := by
    calc transl σ (applyH w t (transl v Q₀))
        = applyH w t (transl σ (transl v Q₀)) := applyH_transl w σ t (transl v Q₀)
      _ = applyH w t (transl (gmul σ v) Q₀) := by rw [hsc_transl_transl σ v Q₀]
      _ = transl (gmul σ v) (applyH w t Q₀) := (applyH_transl w (gmul σ v) t Q₀).symm
      _ = transl (gmul v σ) (applyH w t Q₀) := by rw [hsc_gmul_comm σ v]
      _ = transl v (transl σ (applyH w t Q₀)) := (hsc_transl_transl v σ (applyH w t Q₀)).symm
  rw [hgoal, subIdeal]
  refine Ideal.subset_span ⟨⟨fsD D, ?_⟩, ?_⟩
  · exact hsc_transl_homPiece v (fsD D)
      (hsc_transl_homPiece σ (fsD D) (applyH_mem w t hQ₀mem))
  · intro y hy
    rw [hsc_eval_transl v (conePt N y) (transl σ (applyH w t Q₀)), hsc_coneAct_conePt v y]
    exact (gmul_mem_ZG_of_stab 𝔓 v y hv (hsub hy)).2 (transl σ (applyH w t Q₀)) hH

/-- Transport of `primLen` along `transl σ` (instance of `primLen_map_ringEquiv`). -/
private lemma primLen_map_transl {N : ℕ} (σ : Fin (N + 1) → ℂ) (hσ : InG σ) (I p : Ideal (MR N)) :
    primLen (Ideal.map (transl σ) I) (Ideal.map (transl σ) p) = primLen I p := by
  have h := primLen_map_ringEquiv (tauEquiv σ hσ) I p
  rw [map_tauEquiv σ hσ I, map_tauEquiv σ hσ p] at h
  exact h

/-- §5.1(c), multiplicity. For `σ ∈ H_V(T)`, `J'` has length `≥ C(T + ℓ, ℓ)` at `cosetIdeal σ`:
translate by `τ_σ` (a ring automorphism commuting with `δ^t`, preserving `primLen`), check
`δ^t (τ_σ J') ⊆ I(G')` for `|t| ≤ T` on generators (`V ⋆ G' = V`, `σ ∈ H_V(T)`) and spans
(`vanish_span`), then `wuestholz_length`. Size 0.6–1k.  Phase 4: `hdeg` added (the
generators `τ_v τ_{sγ} δ^t P^h` must be multihomogeneous for `mem_of_vanish_ZG` and for membership
in `subIdeal`/`cosetIdeal`); it is free at the only call site `stab_step`. -/
theorem coset_length {N q ρ : ℕ} (w : Fin q → Fin (N + 1) → ℂ) (θ : Fin N → ℂ)
    (D : Fin (N + 1) → ℕ) (P : MvPolynomial (Fin (N + 1)) ℂ) (hdeg : ∀ i, P.degreeOf i ≤ D i) (A B T : ℕ) (𝔓 : Ideal (MR N))
    (h𝔓 : 𝔓.IsPrime) (hH : MultiHom N 𝔓) (hG : MeetsG N 𝔓) (ε : Bool)
    (M : Fin ρ → Fin N → ℤ) (hM : PrimSys M) (hsub : subSet N ρ ε M ⊆ stabG 𝔓)
    (σ : Fin (N + 1) → ℂ) (hσ : σ ∈ Hset w 𝔓 (chainIdeal w θ D P A B) T)
    (hmin : cosetIdeal σ ε M ∈ (Ideal.span (bigGen w θ D P A B 𝔓)).minimalPrimes) :
    (((T + ellW w ε M).choose (ellW w ε M) : ℕ) : ℕ∞) ≤
      primLen (Ideal.span (bigGen w θ D P A B 𝔓)) (cosetIdeal σ ε M) :=
  by
  obtain ⟨hσG, hσH⟩ := hσ
  have hmap_coset : Ideal.map (transl σ) (cosetIdeal σ ε M) = subIdeal N ρ ε M :=
    transl_map_cosetIdeal σ hσG ε M
  have hgen : ∀ Q ∈ bigGen w θ D P A B 𝔓, ∀ t : Fin q → ℕ, (∑ k, t k) ≤ T →
      transl σ (applyH w t Q) ∈ subIdeal N ρ ε M := by
    rintro Q ⟨v, hv, Q₀, hQ₀, rfl⟩ t ht
    obtain ⟨s, t', hs, ht', rfl⟩ := hQ₀
    exact step_gen w θ D P hdeg A B T 𝔓 ε M hsub σ hσG hσH s hs t' ht' v hv t ht
  have hvanish : ∀ F ∈ Ideal.span (bigGen w θ D P A B 𝔓), ∀ t : Fin q → ℕ, (∑ k, t k) ≤ T →
      transl σ (applyH w t F) ∈ subIdeal N ρ ε M :=
    vanish_span w σ T (subIdeal N ρ ε M) (bigGen w θ D P A B 𝔓) hgen
  have hT : ∀ F ∈ Ideal.map (transl σ) (Ideal.span (bigGen w θ D P A B 𝔓)), ∀ t : Fin q → ℕ,
      (∑ k, t k) ≤ T → applyH w t F ∈ subIdeal N ρ ε M := by
    intro F hF t ht
    obtain ⟨Q, hQ, rfl⟩ :=
      (Ideal.mem_map_iff_of_surjective (transl σ) (hsc_transl_surj hσG)).mp hF
    rw [← applyH_transl w σ t Q]
    exact hvanish Q hQ t ht
  have hmin' : (Ideal.span (bigGen w θ D P A B 𝔓)).IsMinimalPrime (cosetIdeal σ ε M) := hmin
  have hJ : subIdeal N ρ ε M ∈
      (Ideal.map (transl σ) (Ideal.span (bigGen w θ D P A B 𝔓))).minimalPrimes := by
    rw [← hmap_coset]
    refine ⟨⟨isPrime_map_transl σ hσG hmin'.isPrime, Ideal.map_mono hmin'.le⟩, ?_⟩
    intro r hr hrle
    have hrc : (Ideal.comap (transl σ) r).IsPrime := by
      haveI := hr.1
      exact Ideal.IsPrime.comap (transl σ)
    have hJle : Ideal.span (bigGen w θ D P A B 𝔓) ≤ Ideal.comap (transl σ) r := by
      intro x hx
      exact hr.2 (Ideal.mem_map_of_mem (transl σ) hx)
    have hle : Ideal.comap (transl σ) r ≤ cosetIdeal σ ε M := by
      intro x hx
      have hx' : transl σ x ∈ r := hx
      have hx'' : transl σ x ∈ Ideal.map (transl σ) (cosetIdeal σ ε M) := hrle hx'
      rw [Ideal.mem_map_iff_of_surjective (transl σ) (hsc_transl_surj hσG)] at hx''
      obtain ⟨y, hy, hyx⟩ := hx''
      have hxy : x = y := by
        have h1 : transl (ginv σ) (transl σ x) = transl (ginv σ) (transl σ y) := by rw [hyx]
        rw [hsc_transl_inv hσG x, hsc_transl_inv hσG y] at h1
        exact h1
      rw [hxy]
      exact hy
    have hfin : cosetIdeal σ ε M ≤ Ideal.comap (transl σ) r := hmin'.le_of_le ⟨hrc, hJle⟩ hle
    calc Ideal.map (transl σ) (cosetIdeal σ ε M)
        ≤ Ideal.map (transl σ) (Ideal.comap (transl σ) r) := Ideal.map_mono hfin
      _ ≤ r := Ideal.map_comap_le
  have hwl := wuestholz_length w ε M hM
    (Ideal.map (transl σ) (Ideal.span (bigGen w θ D P A B 𝔓))) hJ T hT
  rw [← hmap_coset] at hwl
  rw [← primLen_map_transl σ hσG (Ideal.span (bigGen w θ D P A B 𝔓)) (cosetIdeal σ ε M)]
  exact hwl

end Work.BW
