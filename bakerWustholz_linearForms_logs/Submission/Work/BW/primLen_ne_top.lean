import Mathlib
import Submission.Work.BW.DefsB

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

/-! Guidance from the project lead (the requester):

LEAD NOTES (BW block B, phase-4 fix). Your node is `primLen_ne_top`. Definitions: Submission.Work.BW.DefsB. PHASE4_FIXES.md below gives the verdicts and the proof routes (the coset_minimalPrime full proof via mem_of_vanish_ZG plus the helpers; coset_length = wuestholz_length transported by τ_σ, applied directly with no ρ case split). Import siblings; do not reprove them. If a previous owner's partial file exists at ~/snapshots/bw-coset-0927/<name>.lean, you may reuse it (its statement lacked hdeg).

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

/-- General form of the phase-4 helper, over an arbitrary commutative Noetherian ring: if `p` is a
minimal prime of `J` then the localised quotient `(R/J)_p` has finite length over the localisation
`R_p`. Indeed `R_p` is local with maximal ideal `p·R_p`, and `radical(J·R_p) = p·R_p`
(`IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes`), so the maximal ideal is a minimal prime
over `J·R_p` and `R_p ⧸ J·R_p` is Artinian
(`IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing`); it is Noetherian because `R`
is, so its length is finite, and length is unchanged when passing from the quotient ring back to
`R_p` (`Module.length_eq_of_surjective`). -/
lemma primLen_ne_top_aux {R : Type*} [CommRing R] [IsNoetherianRing R]
    (J p : Ideal R) [p.IsPrime] (hp : p ∈ J.minimalPrimes) :
    Module.length (Localization.AtPrime p)
      (Localization.AtPrime p ⧸ J.map (algebraMap R (Localization.AtPrime p))) ≠ ⊤ := by
  let S := Localization.AtPrime p
  let JL : Ideal S := J.map (algebraMap R S)
  -- The localisation of `J` has radical the maximal ideal of the local ring `R_p`.
  have hrad : JL.radical = IsLocalRing.maximalIdeal S := by
    rw [IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (A := S) p J hp,
        IsLocalization.AtPrime.map_eq_maximalIdeal p S]
  -- So the maximal ideal is a minimal prime over `J·R_p`.
  have hmem : IsLocalRing.maximalIdeal S ∈ JL.minimalPrimes := by
    refine ⟨⟨(IsLocalRing.maximalIdeal.isMaximal S).isPrime, hrad ▸ Ideal.le_radical⟩, ?_⟩
    intro Q hQ _
    have h1 : JL.radical ≤ Q := hQ.1.radical_le_iff.mpr hQ.2
    rw [hrad] at h1
    exact h1
  -- Hence `R_p ⧸ J·R_p` is an Artinian (and Noetherian) ring, so of finite length over itself.
  haveI : IsArtinianRing (S ⧸ JL) :=
    IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing JL hmem
  have hlen : Module.length (S ⧸ JL) (S ⧸ JL) ≠ ⊤ := Module.length_ne_top
  -- Length over `R_p` agrees with length over the quotient ring.
  rw [Module.length_eq_of_surjective (R := S ⧸ JL) (M := S ⧸ JL) (S := S)
      Ideal.Quotient.mk_surjective]
  exact hlen

/-- Phase 4 helper for `stab_step`. At a minimal prime `p` of `J` the localisation `(R/J)_p` is
Artinian and finitely generated, so `primLen J p` is finite; this justifies passing from the
`ℕ∞` bound of `coset_length` to the `toNat` in `refined_bezout`. Mathlib: the localisation at a
minimal prime has Krull dimension `0`, `IsArtinianRing`, finite length. Size 0.4–0.8k. -/
theorem primLen_ne_top {N : ℕ} (J p : Ideal (MR N)) (hp : p ∈ J.minimalPrimes) :
    primLen J p ≠ ⊤ := by
  have hp' : p.IsPrime := hp.1.1
  letI := hp'
  rw [primLen, dite_eq_left hp']
  exact primLen_ne_top_aux J p hp

end Work.BW
