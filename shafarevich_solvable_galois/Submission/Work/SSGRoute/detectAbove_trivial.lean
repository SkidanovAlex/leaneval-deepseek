import Mathlib
import Submission.Work.SSGRoute.E7bDefs
import Submission.Work.SSGRoute.local_duality_ext
import Submission.Work.SSGRoute.exists_level_normGroup_not_mem_of_not_pthPower
import Submission.Work.SSGRoute.exists_level_local_embedding_fix
import Submission.Work.SSGRoute.norm_fail_of_local_embedding
import Submission.Work.SSGRoute.localUnitsEquiv_fixed_iff_ringEquiv_fixed
import Submission.Work.SSGRoute.localAlgebraMapUnits_self
import Submission.Work.SSGRoute.phi1_level_naturality
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localFixed_all
import Submission.NK.NUV2.LC.RouteB.locUnits_tower_eq_zero
import Submission.Work.SSGRoute.arch_quotientNorm_avoids
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

LEAD NOTES (SSG E7b redesign, requests/ssg6). Your node is `detectAbove_trivial`; find it in the design below (its tag, content, dependencies and size). Definitions: Submission.Work.SSGRoute.E7bDefs (lead-placed; do not edit). All 19 E7b nodes are dispatched in parallel as Submission.Work.SSGRoute.<name>. If you need a sibling, IMPORT its module; never reprove it or restate it under another name. Key idea: restrict to a Sylow p-subgroup of D_w first, so every simple module is 𝔽_p. Do NOT use the Sylow-free dévissage (local_duality_detect_step/base) or the degree-0/2/Euler lane. Do NOT delete or rewrite local_duality_ext.lean: it carries shared helper lemmas. If you believe your statement is false, give a concrete counterexample.

===== DESIGN_E7B.md =====
# ssg6: a fleet route for E7b `Work.SSGRoute.local_duality_ext_in`

Designer's note, 2026-09-27.

- **Workspace:** 3.144 `shafarevich_solvable_galois`, read-only.
- **Checks:** everything was elaborated on the box under `/tmp/e7bd/` with `lake env lean` under a
  12G MemoryMax scope. No workspace file was touched, nothing was built, and nothing was
  dispatched.

## 0. Status of what exists (checked with `#print axioms` on the built oleans)

**The target is already split.**

```
local_duality_ext_in = ⟨local_duality_ext_detect_levels,
                        local_duality_ext_realization_of_detection + local_duality_ext_detect_h⟩
```

| Declaration | Status |
|---|---|
| `local_duality_ext_realization_of_detection` (clause (ii) from right detection, by finite duality) | **clean** |
| `local_duality_ext_extH_finite` | **clean** |
| `local_pTorsion_card`: `|H²(D_{w'},L_{w'}ˣ)[p]| = p` when `p ∣ |D_{w'}|`, all places | **clean** |
| `local_duality_ext_detect_h` (right detection, all `M`) | `sorryAx` |
| `local_duality_ext_detect_levels` (clause (i)) | `sorry` (no build of its olean needed to see it) |

Also **clean** (usable as they stand):
- **Pairing calculus:** `levelPair_coeff_naturality`, `levelPair_extHMap`, `levelPair_add*`.
- **Base-case algebra:**
  - `local_duality_ext_base_source_uncond` (`Ext¹_{D_w}(𝔽_p,K_wˣ) ≅ H⁰/p`);
  - `hilbert90_localUnits_extH`;
  - `hilbert90_localUnitsRep`, which covers every subgroup;
  - `normCriterion_quotient`;
  - `levelPair_trivial_eq_zero_iff_norm(B)`;
  - `detect_trivial_cyclic_of_norm_notMem`.
- **Clause (i) at `𝔽_p`:** `clause_i_trivial` and `clause_i_trivial_of_arithmetic`, both modulo the
  hypothesis `hAI`.
- **Level data:** `decompK_restrict_exists`, `localUnitsMap_exists`.
- **Local class field theory:** `exists_level_normGroup_not_mem_of_not_pthPower`.
- **Global levels:** `exists_level_pthRoot`.
- **Corestriction:**
  - `ext_corestriction` / `extCor` (`cor ∘ res = index`);
  - `extRes_injective_of_index`;
  - `SylowDesc.extRes_eq_zero_of_pTorsion`;
  - `E6Calc.extCor_levelPair` (projection formula).

The sorry'd arithmetic input is `exists_level_quotientNorm_avoids` (`hAI`).

## 1. The 8-vs-16 claim: FALSE. The correct count is 8 → 4, and it is fine

**The example.** Reviewer 2 of `H968-L1022` took `k = K = ℚ`, `p = 2`, `M = 𝔽₂`, `w ∣ 2`,
`L = ℚ(ζ₈)`. The count below uses the actual Lean objects.

**Source: 8 elements.**
- `decompK w` is the stabiliser in `Gal(ℚ/ℚ) = 1`.
- So the source is `Abelian.Ext (res 𝔽₂) (localUnitsK w) 1 ≅ ℚ₂ˣ/ℚ₂ˣ²` (`ext_zmod_prime_iso_corrected`
  plus Hilbert 90).
- It has 8 elements.

**Target of `h`: 4 elements.**
- 2 is totally ramified in `ℚ(ζ₈)`, so `D_{w'} = Gal = (ℤ/2)²`.
- `extH (res_f 𝔽₂) 1 = Hom((ℤ/2)², ℤ/2)` has 4 elements.

**Where the reviewer went wrong.**
- The value group is `T = extH (localUnitsRep ℚ L w') 2 = Br(ℚ₂(ζ₈)/ℚ₂) ≅ ℤ/4`. It is **cyclic**.
- The reviewer wrote `H² = Ĥ⁰ ≅ D' = (ℤ/2)²`. That uses periodicity `Ĥ⁰ ≅ Ĥ²`, which holds only for
  cyclic groups; `Ĥ⁰ ≅ D'^{ab}` is local reciprocity, not `H²`.
- In Lean this is settled by the proved `local_pTorsion_card`: `|T[2]| = 2`.

**The corrected count.**
- The 2-torsion functionals are `Hom((ℤ/2)², T[2])`, which has 4 elements, not 16.
- The pairing `ℚ₂ˣ/2 → Hom(D', T[2])` sends `a ↦ (χ ↦ a ∪ δχ)`.
- Its kernel is `N(ℚ₂(ζ₈)ˣ)·ℚ₂ˣ²/ℚ₂ˣ²`, of order 2, because the norm group has index 4.
- So the map `8 → 4` is onto, and clause (ii) holds here.

**The other "counterexamples" do not concern E7b.**
- H379's `|H¹(D,E)| = 8 ≠ 2`, and `localTatePairing_deg02`'s "dim 1 vs 3", refute **different**
  statements: a finite-level `H¹ × H¹` duality, and an `Ext⁰`/`H²` realisation.
- E7b is `Ext¹_{D_w}(M,K_wˣ) × H¹(D_{w'},M)`, with `y` at level `K`. Both clauses are true as
  formalised (§2).

## 2. What is needed at finite level, and why the owner's "no plan" is wrong

**Notation.**
- `D = D_w = Gal(K_w/k_v)`, `A = K_wˣ`.
- A level `λ` is `(L, w', f, ι)`, with `G_λ = D_{w'}`, `f : G_λ ↠ D` and `B_λ = L_{w'}ˣ`.
- `V(M) = Ext¹_D(M,A)` and `W_λ(M) = H¹(G_λ,M)`.
- `T_λ = H²(G_λ,B_λ)[p]`, of order `p` when `p ∣ |G_λ|`.

**Both clauses are true.**
- By Hilbert 90 and `Ext_ℤ(M, k̄ˣ)` divisibility, `V(M) = Ext¹_{G_{k_v}}(M, k̄_vˣ) = H¹(k_v, M^∨(1))`.
- `W_λ(M) ↪ H¹(k_v, M)` by inflation.
- `T_λ = Br(k_v)[p]` when `p ∣ |G_λ|`.
- So (ii) is the extension of functionals from a subspace under perfect local duality, and (i) is
  perfectness.
- Archimedean places are covered: `p ∣ |D_{w'}|` forces `p = 2` and `D_{w'} = Gal(ℂ/ℝ)`, where
  `Br(ℂ/ℝ) = ℤ/2 = Br(ℝ)`.

**The lead's diagnosis is right for (i), and for the degree-1 dévissage of (ii) too.**

What rescues both:

**(1) Sylow first.** The owner's "irreducible `M` of dimension ≥ 2 is inert" objection disappears
after restriction to a Sylow `S ≤ D_w`: every simple `𝔽_p[S]`-module is `𝔽_p`.
- For (i), restriction is injective on `p`-torsion `Ext¹`. The level values transfer by the proved
  projection formula `E6Calc.extCor_levelPair`, plus injectivity of `cor` on `T` (the orders are
  equal).
- For (ii), one needs `y = cor z`, hence a Mackey formula for `cor` under the surjection `f`.
- `μ_p ⊆ k_v` comes free, since a `p`-group fixes `ζ`. Twisted `𝔽_p(χ)` base cases are never needed.

**(2) Clause (ii): the quotient orientation `0 → M₁ → M → 𝔽_p → 0` needs only `|Ext²_D(𝔽_p,A)| ≤ p`.**

This bound is `H²(D,A)[p]`, via Hilbert 90. The argument, for `h ∈ W_λ(M)` nonzero:
1. If `π_*h ≠ 0`, the base case detects `π_*h`, and the pullback detects `h`.
2. Otherwise `h = i_*h₁` with `h₁ ∉ span(e)`, where `e = δ(1)` is the extension class.
3. Choose `ℓ` on `W_λ(M₁)` with `ℓ(h₁) ≠ 0` and `ℓ(e) = 0`. Realise `ℓ = ⟨y₁,·⟩` (induction plus the
   proved finite duality).
4. Then `⟨y₁,e⟩ = J(∂y₁)`, where `J(u) = ⟨u, 1⟩` on `Ext²_D(𝔽_p, A)`, a group of order at most `p`.
5. Hence `∂y₁ = 0`:
   - If `e ≠ 0`, `J` is nonzero on the image of `∂`, so it is injective there.
   - If `e = 0`, then `1` lifts to `M^{G_λ} = M^D` (`f` is onto), the sequence splits, and `∂ = 0`.
6. So `y₁ = i^*y` and `⟨y,h⟩ = ℓ(h₁) ≠ 0`.

No Kummer theory, no degree-2 injectivity, and no new levels are needed. **(ii) is a single-level
statement.**

**(3) Clause (i): the sub orientation `0 → 𝔽_p → M → Q → 0` needs the degree-0/2 input, but only for
`𝔽_p`.**

The input is `H²(k_v, μ_p) ↪ Br(k_v)[p] ≅ ℤ/p`: a class of `H²(D_λ, 𝔽_p)` that dies in the Brauer
group dies at a higher level (local Kummer), and `|T_λ| ≤ p`.

The step (E5s-type):
1. `i^*y = 0` by the base case, so `y = π^*y''`.
2. At each level, `⟨y'',·⟩` factors through `δ` into `H²(D_λ, 𝔽_p)` and kills `ker(ζ_*) ∩ im δ`
   (Kummer dies, plus injective inflation of `H²(·, L_{w'}ˣ)`).
3. So `⟨y'',·⟩ = a_λ · ζ_* ∘ δ`.
4. Once some level `λ₁` has `ζ_* ∘ δ ≠ 0`, the scalar `a` is the same at every level above `λ₁`
   (inflation is injective).
5. Then `y'' − a·(extClass ∘ ζ)` vanishes above `λ₁`, and `y = π^*(…) = 0`.

**Cone form.** The step needs the induction hypothesis on cones above an arbitrary level. This is why
clause (i) is carried in the form `DetectAbove` (E7bDefs). It needs no directedness and no composita.

## 3. Route choice

- **(a) Full degree-0/1/2 five-lemma.** Not needed. Degrees 0 and 2 enter only for the trivial module
  and only as a bound, `|T| ≤ p` (plus Kummer in (i)).
- **(b) Induced modules plus Shapiro (Milne I.1.8 / I.2.1).** Rejected. Shapiro for the pairing needs
  the same corestriction and Mackey machinery as (1) and adds the induced-module Ext
  identifications. I.1.8's finite-level form is false for torsion `M`, since it needs
  `Tor(M,C) = 0`.
- **(c) Counting through the local Euler characteristic.** Rejected.
  - `local_tate_duality_euler` is a restored **unproved** statement in the continuous-cochain model.
  - Counting from (ii) alone needs `|V(M)| ≤ |W_λ(M)|` at a level. That is the Euler-characteristic
    or `Ext`-versus-`H¹(Hom)` comparison, which is heavier than Kummer.
- **(d) Go through Ω.** Adopted in part, as a statement about the consumers:
  - E7cΩ (`local_phi_realization_in`, (C)) needs **only (ii)**, plus finiteness of `V(M)` (F1), plus
    directedness of Ω-levels.
  - The realising sets `R_λ = {y : ⟨y,·⟩_λ = ℓ_λ}` are nonempty by (ii), finite by F1, and
    decreasing along levels (injective inflation, which E7cΩ already has for `C_L`). A level with
    minimal `|R_λ|` realises every level.
  - So **Phase 1 = (ii) + F1** unblocks E7cΩ/E9.
  - Clause (i) is Phase 2, needed only by `Ext ≅ H¹` consumers (E7a, G1).

**Chosen:** the Sylow reduction, then single-level quotient dévissage for (ii) and cone sub-dévissage
with local Kummer for (i).
- All group-cohomology steps are abstract lemmas about a surjection `f : G ↠ D`.
- The arithmetic sits in a few base lemmas stated at the **full** decomposition group over an
  arbitrary base.
- The Sylow subgroup is reached by base change to `k' = K^S` (Y3). Every base lemma is then used
  verbatim at `k'`, including the fleet's existing `𝔽_p` work and `local_pTorsion_card`.

## 4. The nodes (all statements in this directory; each elaborates with only `declaration uses sorry`)

**Setup.**
- `E7bDefs.lean` is lead-placed, like PTDefs, as `Submission/Work/SSGRoute/E7bDefs.lean`. It defines:
  - `RightDetect f ι M`;
  - `PTorsLE p X`;
  - `VanishesAbove`;
  - `DetectAbove k K w N` (clause (i) in cone form, with the level data at `L ⊇ L₀` written as
    `(f₀ ∘ g, res_g ι₀ ≫ ι₁)`).
- It compiles with no output.
- The exact `--imports` are in `IMPORTS.txt`.
- The harness inlined E7bDefs.

Sizes are in k lines for DeepSeek (1.5–2× verbose).

### Phase 1: clause (ii) (priority; with F1 it unblocks E7cΩ)

**X1 `rightDetect_quotient_step` (abstract): the quotient step of §2(2).**
- Uses Mathlib `Ext.covariant/contravariant_sequence_exact₁₂₃`, `mapExactFunctor_extClass`,
  `comp_extClass`.
- Uses `levelPair_coeff_naturality` and `realization_of_detection_pairing`.
- Size 0.8–1.3.

**X2 `rightDetect_pgroup` (abstract): strong induction on `|M|` for `D` a `p`-group.**
- A nonzero `M` maps onto `𝔽_p`, because `D` fixes a nonzero vector of `Hom(M,𝔽_p)`
  (`IsPGroup.card_modEq_card_fixedPoints`).
- Deps: X1. Size 0.5–0.9.

**X3 `ext_two_trivial_ptors` (abstract): `H¹(D,A) = 0` and `PTorsLE p H²(D,A)` give `|Ext²_D(𝔽_p,A)| ≤ p`.**
- Uses the contravariant sequence of `Phi1.coeffSES` and `ext_nsmul_p_torsion_left`.
- Size 0.3–0.6.

**X4 `levelPair_extCor_comap` (abstract, RISK): `⟨cor_S^D z, h⟩_G = cor_{S'}^G ⟨z, res_{S'} h⟩`, with `S' = f⁻¹S`.**
- Built from:
  - the natural isomorphism `res_f ∘ Coind_S ≅ Coind_{S'} ∘ res_{f|}`, compatible with the units and
    `coindTrace`;
  - a natural-transformation version of `ext_mapExactFunctor_naturality_aux`;
  - `ext_mapExactFunctor_comp_functor_aux`;
  - the mirror projection formula `x ∘ cor y = cor(res x ∘ y)`.
- Size 1.0–1.8.

**X6 `extCor_two_injective_pTorsion` (abstract): `cor` is injective on `H²(S,B)[p]` when both `p`-torsions have `p` elements.**
- Uses `ext_corestriction`.
- Size 0.2–0.4.

**X5 `rightDetect_of_sylow` (abstract): right detection on `S' ↠ S` gives right detection on `G ↠ D`.**
- Uses `extRes_eq_zero_of_pTorsion` and `Subgroup.index_comap_of_surjective`.
- Deps: X4, X6. Size 0.3–0.6.

**Y1 `detect_h_trivial`: the `𝔽_p` base at any level with `p ∣ |D_{w'}|`.**
- This is the E7b lane's current work: `levelPair_trivial_eq_zero_iff_normB`, the norm index at the
  level, `-1` at archimedean places.
- Size 0.6–1.2 (partly done).

**Y2 `decompK_restrict_surjective`: `f : D_{w'} → D_w` is onto.**
- Uses NK `exists_liesOver_conjugate`.
- Size 0.2–0.5.

**Y3 `levelPair_baseChange` (RISK): base change `k ⊆ k' ⊆ K`.**
- `D_w(K/k') ≃* S`.
- One level-independent `eE`, together with, at each `k`-level:
  - `|D_{w'}(L/k')| = |S'|`;
  - equal `p`-torsion cardinalities;
  - `eH`, `eB` intertwining the pairings.
- Modelled on `SylowDesc.classesK_baseChangeIso`, `ext_res_mulEquiv`, `extH_congr`.
- Size 1.0–1.8.

**Y4 `local_detect_h_pgroup`: `RightDetect` at every level when `D_w` is a `p`-group.**
- The instance of X2 with `hT = local_pTorsion_card`.
- `hE2` is X3 plus `hilbert90_localUnits_extH` plus `local_pTorsion_card`, or `extRes` to `⊥` when
  `p ∤ |D_w|`.
- `hbase = Y1`, `hf = Y2`.
- Deps: X2, X3, Y1, Y2. Size 0.3–0.5.

**Y5 `local_duality_ext_detect_h` (existing statement): the assembly.**
1. Take `S ∈ Sylow p D_w` and `k' := fixedField S`. Y3's `S` is this Sylow, by
   `fixingSubgroup_fixedField`.
2. Y4 at `k'`; `hp` via Y3 and the index being prime to `p`.
3. Transport by Y3.
4. X5 with `hTS` from Y3 plus `local_pTorsion_card` at `k'`.
- **E7b(ii) is then closed** by the proved `realization_of_detection`.
- Deps: Y3, Y4, X5. Size 0.4–0.8.

**F1 `ext_localUnits_finite` (for E7cΩ): `V(N)` is finite.**
- Sylow restriction is injective.
- `Ext¹_S(𝔽_p,A) = A^S/p` injects into `A/p × H¹(S, μ_p)`.
- Size 0.6–1.2.

**Phase 1 total: 5.6–10.4k (Y1 partly done), plus F1 0.6–1.2k.**

### Phase 2: clause (i) (only if E7a/G1 need it)

**Z1 `levelPair_comp_extHMap` (abstract): the pairing at the upper level of an inflated class is the inflation of the pairing.**
- Uses `ext_mapExactFunctor_comp_functor_aux`.
- Size 0.2–0.4.

**Z2 `localUnits_infl_injective`: `H²(D_w,K_wˣ) → H²(D_{w'},L_{w'}ˣ)` is injective.**
- Hilbert 90 on `ker f`.
- Galois descent `(L_{w'}ˣ)^{ker f} = ι(K_wˣ)`, via `NK.GlobalCFTdeep.decompositionSubgroupIsoLocalGalois`
  and `localUnitsRep_eq_res`.
- Commons `H2_inflation_injective_of_subsingleton_H1_general` through E0b, as in
  `E4R3.inflC_injective`.
- Deps: Y2. Size 0.8–1.5.

**Z3 `exists_level_localPthPower`: for any `b ∈ K_wˣ`, a level where `b` becomes a `p`-th power.**
- Weak approximation, `principalUnits_deep_mem_pow`, `exists_level_pthRoot`-style Galois closure,
  `exists_place_liesOver`.
- Size 0.6–1.2.

**Z4 `local_kummer_dies`: `z ≠ 0` and `z_* x = 0` imply `x` inflates to 0 at some level.**
- A local copy of `E4R3.kummer_dies_at_higher_level_clean`.
- Deps: Z3. Size 0.8–1.5.

**Z5a `exists_level_above_quotientNorm_avoids` (RISK): `hAI` above an arbitrary level `L₀`.**
- **It supersedes `exists_level_quotientNorm_avoids`**, which is its case `L₀ = K`.
- H390's plan: local CFT, a Kummer generator, weak approximation.
- Size 1.0–2.0.

**Z5 `detectAbove_trivial`: the cone base `𝔽_p`.**
- Built like the proved `clause_i_trivial_of_arithmetic`.
- Deps: Z5a. Size 0.4–0.8.

**Z6 `detectAbove_sub_step`: the step of §2(3).**
- Uses Mathlib Ext exact sequences, `local_pTorsion_card`, `localAlgebraMapUnits` transitivity and
  `galRes_trans`.
- Deps: Z1, Z2, Z4. Size 1.0–1.6.

**Z7 `detectAbove_pgroup`: induction by fixed vectors.**
- Deps: Z5, Z6. Size 0.3–0.6.

**Z8 `local_duality_ext_detect_levels` (existing statement): the assembly.**
1. `k' = K^S`, and `z : 𝔽_p → K_wˣ` from `ζ`: a `p`-group fixes `ζ` since `[k(ζ):k] ∣ p−1`.
2. For `y ⊥` all `k`-levels, `eE(res_S y)` vanishes above the base level over `k'`. For a
   `k'`-level `L`, pass to its Galois closure `L̃/k` (Z1 and Z2 at `k'`). At `L̃`, apply Y3 and
   `E6Calc.extCor_levelPair` with X6.
3. Z7 gives `eE(res y) = 0`.
4. `extRes_injective_of_index` gives `y = 0`.
- Base level: `f₀ = id`, `ι₀ = 𝟙` (`localAlgebraMapUnits_self`).
- Deps: Z7, Y3, X6. Size 0.8–1.5.

**Phase 2 total: 5.9–11.1k.**

**Whole E7b: 19 new statement files (+ E7bDefs) and 2 assemblies of existing statements (Y5, Z8), about 12–22k lines.** This far exceeds the ssg4 estimate of 2–3.5k, which
assumed a Sylow-free dévissage.

## 5. Order, cancellations, consumers

**Waves.**
1. X1, X3, X4, X6, Y2, Y3, F1, and Y1 (continuing). For Phase 2, also Z1, Z2, Z3, Z5a.
2. X2, X5, Y4. For Phase 2, also Z4 and Z5.
3. Y5 (**E7b(ii) done**). For Phase 2, also Z6.
4. Z7, then Z8 (**E7b(i) done**).

**Do NOT build or keep:**
- `local_duality_detect_step` and the `detect_of_base_and_step` framing: Sylow-free subquotient
  dévissage, rightly declared insufficient.
- `local_duality_detect_base`: twisted `𝔽_p(χ)` bases, unnecessary after Sylow.
- `exists_level_quotientNorm_avoids`: retarget its owner to Z5a.
- The deg02/Euler/continuous-cochain lane (`local_tate_duality_02/euler/mup_dim`,
  `PT/localTatePairing_deg02`): not needed.
- `tate_duality_finiteLevel` (H379): false.
- Any "degree-2 injectivity at a level" (X1 needs only a bound).
- Composita and directedness of levels (cone form).

**The on-disk duplicate.** `local_duality_ext` (the E7b statement, still `sorry`) is superseded by
`local_duality_ext_in`. It cannot be closed from it, because `_in` imports it; retire it.

**Consumer note for E7cΩ (H968).** Its input (C) should be derived from (ii) + F1 + minimal
`|R_λ|` over Ω-levels (§3(d)), not from (i).

## 6. Risks

**X4 and Y3.** Both are formal (Rep/coinduction and base-change transport, with the known
`ULift.module`/`hV2` instance diamonds). They are bounded, but they are the most likely places to
stall.

**Z5a.** A Grunwald-style realisation of a local cyclic extension above an arbitrary level. It is
the single genuine arithmetic risk, and it is the same risk the base case already carries.

**Mathematics.** No step depends on an unproved conjecture. Every statement was checked true
(including archimedean places):
- X1's two sub-cases;
- Z6's Case 1 and Case 2;
- Mackey for a surjection `f` (a single double coset).
-/

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module
attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass
attribute [local instance 1] ULift.distribSMul ULift.distribMulAction ULift.smulWithZero
attribute [local instance 1] ULift.mulActionWithZero


/-! ## The arithmetic input, finite-place case

The sibling module `Submission.Work.SSGRoute.exists_level_above_quotientNorm_avoids` (node Z5a of the
ssg6 E7b redesign) states the arithmetic input needed by `detectAbove_trivial` but does not currently
elaborate (it calls the undefined `exists_level_above_quotientNorm_avoids_infinite`), so the pieces
used here are assembled locally from the *proved* modules of the workspace:

* `exists_level_normGroup_not_mem_of_not_pthPower` — local CFT: a unit which is not a `p`-th power is
  not a norm from some degree-`p` local Galois extension;
* `exists_level_local_embedding_fix` — Krasner: that local extension is realised as a completion of a
  global level over a prescribed number field;
* `norm_fail_of_local_embedding` — the Rep-theoretic bridge: the local embedding produces `N ⊴ D_{w'}`
  with cyclic quotient of order `p` for which the image of the local unit is not an `N`-norm.

The archimedean case is delegated (node `Work.SSGRoute.arch_quotientNorm_avoids`). -/

section FiniteCase

/-- **Local fixed units are the units of the base local field.**  A unit `a` of `K_wˣ` fixed by the
whole decomposition group `D_w = decompK w` is the image of a unit of `k_vˣ` under the canonical
local map.  (Copy of the corresponding helper of node Z5a, kept here so that this file is
independent of the currently non-building sibling module.) -/
theorem detectAbove_localFixedUnits_eq_localAlgebraMapUnits
    (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (v : NK.GlobalCFT.Place k) (hv : NK.GlobalCFT.Place.LiesOver w v)
    (a : (NK.GlobalCFT.Place.localField K w)ˣ)
    (hafix : ∀ σ : decompK (k := k) w,
      NK.HassePrinciple.localUnitsEquiv (K := k) w σ a = a) :
    ∃ a₀ : (NK.GlobalCFT.Place.localField k v)ˣ,
      NK.GlobalCFT.Place.localAlgebraMapUnits w v hv a₀ = a :=
  NK.GlobalCFT.Inclusion.globalCFT_localFixed_mem_range (K := k) (L := K) hv a
    ((localUnitsEquiv_fixed_iff_ringEquiv_fixed_general (k := k) (K := K) w a).mp hafix)

/-- The image of `k_vˣ` in `K_wˣ` is fixed by the decomposition group. -/
theorem detectAbove_localUnitsEquiv_localAlgebraMapUnits_eq_self
    (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
    [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (v : NK.GlobalCFT.Place k) (hv : NK.GlobalCFT.Place.LiesOver w v)
    (u : (NK.GlobalCFT.Place.localField k v)ˣ) (σ : decompK (k := k) w) :
    NK.HassePrinciple.localUnitsEquiv (K := k) w σ
        (NK.GlobalCFT.Place.localAlgebraMapUnits w v hv u)
      = NK.GlobalCFT.Place.localAlgebraMapUnits w v hv u := by
  have h := NK.NUV2.LC.RouteB.localUnitsEquiv_localAlgebraMapUnits_tower
    (F := k) (L := k) (M := K) hv σ u
  rw [← h]
  congr 1
  have hτ : (NK.NUV2.LC.RouteB.localStabilizerMapTower (F := k) (L := k) (M := K) hv σ) = 1 :=
    Subsingleton.elim _ _
  rw [hτ, NK.HassePrinciple.localUnitsEquiv_one]
  rfl

/-- **The finite-place case of the Z5a arithmetic input.**  For a finite place `qw` of `K`, a unit
`a ∈ K_{qw}ˣ` fixed by the decomposition group and not a `p`-th power of a fixed unit, and an
arbitrary level `L₀ ⊇ K` with a place `w₀ ∣ qw`, there are a level `L ⊇ L₀` (finite Galois over `k`),
a place `w' ∣ w₀` and `N ⊴ D_{w'}` with `D_{w'}/N` cyclic of order `p` for which the image of `a` in
`L_{w'}ˣ` is not an `N`-relative norm. -/
theorem detectAbove_finite_quotientNorm_avoids
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (qw : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (a : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite qw))ˣ)
    (hafix : ∀ σ : decompK (k := k) (NK.GlobalCFT.Place.ofFinite qw),
      NK.HassePrinciple.localUnitsEquiv (K := k) (NK.GlobalCFT.Place.ofFinite qw) σ a = a)
    (ha : ¬ ∃ b : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite qw))ˣ,
      (∀ σ : decompK (k := k) (NK.GlobalCFT.Place.ofFinite qw),
        NK.HassePrinciple.localUnitsEquiv (K := k) (NK.GlobalCFT.Place.ofFinite qw) σ b = b) ∧
        b ^ p = a)
    (L₀ : Type) [Field L₀] [NumberField L₀] [Algebra k L₀] [Algebra K L₀] [IsScalarTower k K L₀]
    [FiniteDimensional k L₀] [IsGalois k L₀]
    (w₀ : NK.GlobalCFT.Place L₀)
    (hw₀ : NK.GlobalCFT.Place.LiesOver w₀ (NK.GlobalCFT.Place.ofFinite qw)) :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra k L) (_ : Algebra L₀ L)
      (_ : IsScalarTower k L₀ L) (_ : FiniteDimensional k L) (_ : IsGalois k L)
      (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w₀)
      (N : Subgroup (MulAction.stabilizer (L ≃ₐ[k] L) w')) (_ : N.Normal)
      (_ : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N)),
      IsCyclic (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) ∧
      Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) = p ∧
      ¬ (∃ bb : NK.HassePrinciple.localUnitsRep k L w',
        (∀ n : N, (NK.HassePrinciple.localUnitsRep k L w').ρ
          (n : MulAction.stabilizer (L ≃ₐ[k] L) w') bb = bb) ∧
        (∑ x : MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N,
          (NK.HassePrinciple.localUnitsRep k L w').ρ (Quotient.out x) bb) =
          Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w₀ hw'
            (NK.GlobalCFT.Place.localAlgebraMapUnits w₀ (NK.GlobalCFT.Place.ofFinite qw) hw₀ a))) := by
  classical
  rcases w₀ with w₀K | q₀
  · exact absurd ((NK.GlobalCFT.Place.isFinite_of_liesOver hw₀).mpr
      (NK.GlobalCFT.Place.isFinite_ofFinite qw)) (by simp)
  · -- the base place of `k` below `q₀`
    let Qk : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) :=
      ⟨q₀.asIdeal.under (NumberField.RingOfIntegers k), inferInstance, Ideal.under_ne_bot _ q₀.ne_bot⟩
    have hq₀Q : q₀.asIdeal.LiesOver Qk.asIdeal := Ideal.over_under q₀.asIdeal
    have hq₀qw : q₀.asIdeal.LiesOver qw.asIdeal := by
      rcases (NK.GlobalCFT.Place.liesOver_iff _ _).mp hw₀ with h | ⟨q', Q', e1, e2, hL⟩
      · obtain ⟨w', v', e1, e2, hL⟩ := h
        exact absurd e1 (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w' q₀).symm
      · rw [NK.GlobalCFT.Place.ofFinite_inj] at e1 e2
        rw [← e1, ← e2] at hL; exact hL
    have hqwQ : qw.asIdeal.LiesOver Qk.asIdeal := by
      haveI := hq₀qw
      have hQeq : Qk.asIdeal = qw.asIdeal.under (NumberField.RingOfIntegers k) := by
        change q₀.asIdeal.under (NumberField.RingOfIntegers k) = _
        rw [Ideal.LiesOver.over (A := NumberField.RingOfIntegers K) (P := q₀.asIdeal)
              (p := qw.asIdeal),
          Ideal.under_under (A := NumberField.RingOfIntegers k) q₀.asIdeal]
      rw [hQeq]
      exact Ideal.over_under qw.asIdeal
    obtain ⟨a₀, ha₀⟩ := detectAbove_localFixedUnits_eq_localAlgebraMapUnits k K
      (NK.GlobalCFT.Place.ofFinite qw) (NK.GlobalCFT.Place.ofFinite Qk)
      (NK.GlobalCFT.Place.liesOver_ofFinite hqwQ) a hafix
    have hnotpow : ∀ b : (Qk.adicCompletion k)ˣ, b ^ p ≠ a₀ := by
      intro b hb
      apply ha
      refine ⟨NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite qw)
          (NK.GlobalCFT.Place.ofFinite Qk) (NK.GlobalCFT.Place.liesOver_ofFinite hqwQ) b, ?_, ?_⟩
      · intro σ
        exact detectAbove_localUnitsEquiv_localAlgebraMapUnits_eq_self k K
          (NK.GlobalCFT.Place.ofFinite qw) (NK.GlobalCFT.Place.ofFinite Qk)
          (NK.GlobalCFT.Place.liesOver_ofFinite hqwQ) b σ
      · rw [← map_pow, hb, ha₀]
    obtain ⟨E, hEf, hEA, hEfd, hEgal, hEcard, hEnorm⟩ :=
      exists_level_normGroup_not_mem_of_not_pthPower Qk p a₀ hnotpow
    obtain ⟨L, hLf, hLn, hLk, hLL₀, hST, hLfd, hLgal, q', hq', hq'Q, hne⟩ :=
      exists_level_local_embedding_fix k L₀ q₀ Qk hq₀Q E
    letI : Field L := hLf
    letI : NumberField L := hLn
    letI : Algebra k L := hLk
    letI : Algebra L₀ L := hLL₀
    letI : IsScalarTower k L₀ L := hST
    letI : FiniteDimensional k L := hLfd
    letI : IsGalois k L := hLgal
    obtain ⟨N, hNnorm, hNfin, hcyc, hcard, hfail⟩ :=
      norm_fail_of_local_embedding p k L Qk q' hq'Q E hEcard hne a₀ hEnorm
    letI : N.Normal := hNnorm
    letI : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q') ⧸ N) := hNfin
    have hstep1 : (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q₀)
          (NK.GlobalCFT.Place.ofFinite qw) hw₀)
          (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite qw)
            (NK.GlobalCFT.Place.ofFinite Qk) (NK.GlobalCFT.Place.liesOver_ofFinite hqwQ) a₀)
        = NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q₀)
          (NK.GlobalCFT.Place.ofFinite Qk) (NK.GlobalCFT.Place.liesOver_ofFinite hq₀Q) a₀ := by
      rw [← MonoidHom.comp_apply, localAlgebraMapUnits_comp (K := k) (L := K) (M := L₀)
          hw₀ (NK.GlobalCFT.Place.liesOver_ofFinite hqwQ)
          (NK.GlobalCFT.Place.liesOver_ofFinite hq₀Q)]
    have hstep2 : (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q')
          (NK.GlobalCFT.Place.ofFinite q₀) (NK.GlobalCFT.Place.liesOver_ofFinite hq'))
          (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q₀)
            (NK.GlobalCFT.Place.ofFinite Qk) (NK.GlobalCFT.Place.liesOver_ofFinite hq₀Q) a₀)
        = NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q')
          (NK.GlobalCFT.Place.ofFinite Qk) (NK.GlobalCFT.Place.liesOver_ofFinite hq'Q) a₀ := by
      rw [← MonoidHom.comp_apply, localAlgebraMapUnits_comp (K := k) (L := L₀) (M := L)
          (NK.GlobalCFT.Place.liesOver_ofFinite hq')
          (NK.GlobalCFT.Place.liesOver_ofFinite hq₀Q)
          (NK.GlobalCFT.Place.liesOver_ofFinite hq'Q)]
    have hkey : NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q')
          (NK.GlobalCFT.Place.ofFinite q₀) (NK.GlobalCFT.Place.liesOver_ofFinite hq')
          (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q₀)
            (NK.GlobalCFT.Place.ofFinite qw) hw₀ a)
        = NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q')
          (NK.GlobalCFT.Place.ofFinite Qk) (NK.GlobalCFT.Place.liesOver_ofFinite hq'Q) a₀ := by
      rw [← ha₀, hstep1, hstep2]
    exact ⟨L, hLf, hLn, hLk, hLL₀, hST, hLfd, hLgal, NK.GlobalCFT.Place.ofFinite q',
      NK.GlobalCFT.Place.liesOver_ofFinite hq', N, hNnorm, hNfin, hcyc, hcard, by
        rw [hkey]
        exact hfail⟩

end FiniteCase

/-- **Z5 (clause (i), cone form, `M = 𝔽_p`).**  Same assembly as the proved
`Work.SSGRoute.clause_i_trivial_of_arithmetic` / `clause_i_trivial`, with the arithmetic input
(the cone form of `Work.SSGRoute.exists_level_quotientNorm_avoids`, node Z5a of the ssg6 design) in
place of `hAI` and the level data `(f₀ ∘ g, res_g ι₀ ≫ ι₁)`: `y = pushClass a`
(`Work.SSGRoute.localUnits_pushClass_surjective`), `y ≠ 0` forces `a` not a `p`-th power of a fixed
unit (`Work.SSGRoute.not_pow_of_pushClass_lde_ne_zero_local`), then
`Work.SSGRoute.levelPair_trivial_eq_zero_iff_normB` at the level produced by the arithmetic input.

The arithmetic input is split by the place `w` of `K` (the archimedean case is the delegated node
`Work.SSGRoute.arch_quotientNorm_avoids`, the finite case is
`Work.SSGRoute.detectAbove_finite_quotientNorm_avoids` above). -/
theorem detectAbove_trivial (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) :
    DetectAbove k K w (Rep.trivial Coeff (decompK (k := k) w) (ZMod p)) := by
  classical
  unfold DetectAbove
  intro L₀ hL₀f hL₀n hkL₀ hKL₀ hST₀ hfd₀ hgal₀ w₀ hw₀ f₀ hf₀ ι₀ hι₀ y hy
  by_contra hyne
  obtain ⟨φ, hφ⟩ := localUnits_pushClass_surjective p k K w y
  rw [hφ] at hyne
  let av : Additive (NK.GlobalCFT.Place.localField K w)ˣ := Rep.Hom.hom φ (1 : Coeff)
  let a : (NK.GlobalCFT.Place.localField K w)ˣ := Additive.toMul av
  have hof : (Rep.Hom.hom φ (1 : Coeff) : localUnitsK (k := k) w) = Additive.ofMul a := rfl
  have hafix : ∀ σ : decompK (k := k) w,
      NK.HassePrinciple.localUnitsEquiv (K := k) w σ a = a := by
    intro σ
    have h2 : Additive.ofMul (NK.HassePrinciple.localUnitsEquiv (K := k) w σ a) =
        Additive.ofMul a := rep_hom_apply_one_fixed φ σ
    exact Additive.ofMul.injective h2
  have ha : ¬ ∃ bb : (NK.GlobalCFT.Place.localField K w)ˣ,
      (∀ σ : decompK (k := k) w,
        NK.HassePrinciple.localUnitsEquiv (K := k) w σ bb = bb) ∧ bb ^ p = a := by
    rintro ⟨bb, hbb, hbbp⟩
    refine not_pow_of_pushClass_lde_ne_zero_local p k K w φ hyne ⟨bb, hbb, ?_⟩
    rw [hbbp]
    exact hof
  obtain ⟨L, hLf, hLn, hAL, hAL₀, hSTL, hfdL, hgalL, w', hw', N, hN, hF, hcyc, hcard, hfail⟩ :=
    (show ∃ (L : Type 0) (_ : Field L) (_ : NumberField L) (_ : Algebra k L)
        (_ : Algebra L₀ L) (_ : IsScalarTower k L₀ L) (_ : FiniteDimensional k L)
        (_ : IsGalois k L) (w' : NK.GlobalCFT.Place L)
        (hw' : NK.GlobalCFT.Place.LiesOver w' w₀)
        (N : Subgroup (MulAction.stabilizer (L ≃ₐ[k] L) w')) (_ : N.Normal)
        (_ : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N)),
        IsCyclic (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) ∧
        Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) = p ∧
        ¬ (∃ bb : NK.HassePrinciple.localUnitsRep k L w',
          (∀ n : N, (NK.HassePrinciple.localUnitsRep k L w').ρ
            (n : MulAction.stabilizer (L ≃ₐ[k] L) w') bb = bb) ∧
          (∑ x : MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N,
            (NK.HassePrinciple.localUnitsRep k L w').ρ (Quotient.out x) bb) =
            Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w₀ hw'
              (NK.GlobalCFT.Place.localAlgebraMapUnits w₀ w hw₀ a))) from by
      rcases w with u | qw
      · exact arch_quotientNorm_avoids p k K u a hafix ha L₀ w₀ hw₀
      · exact detectAbove_finite_quotientNorm_avoids p k K qw a hafix ha L₀ w₀ hw₀)
  letI : Field L := hLf
  letI : NumberField L := hLn
  letI : Algebra k L := hAL
  letI : Algebra L₀ L := hAL₀
  letI : IsScalarTower k L₀ L := hSTL
  letI : FiniteDimensional k L := hfdL
  letI : IsGalois k L := hgalL
  letI : N.Normal := hN
  letI : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) := hF
  letI : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w') := Fintype.ofFinite _
  obtain ⟨g, hg⟩ := decompK_restrict_exists k L₀ L w₀ w' hw'
  obtain ⟨ι₁, hι₁⟩ := localUnitsMap_exists k L₀ L w₀ w' hw' g hg
  obtain ⟨χ₀, hχ₀ne, hχ₀infl⟩ := exists_H1_inflated_ne_zero N p hcyc hcard
  obtain ⟨b⟩ := nonempty_extGroupCohomologyBridge
  set hb : groupCohomology
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p)) 1 :=
    (groupCohomology.map (QuotientGroup.mk' N)
      (trivResInv (QuotientGroup.mk' N) (ZMod p)) 1).hom χ₀ with hbdef
  set h : extH (Rep.res (f₀.comp g) (Rep.trivial Coeff (decompK (k := k) w) (ZMod p))) 1 :=
    (b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))) hb with hh
  have hne : h ≠ 0 := by
    rw [hh]
    intro h0
    exact hχ₀infl ((b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).injective
      (by rw [h0]; exact (map_zero _).symm))
  have hlift : ∃ hb' : groupCohomology
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) (ZMod p)) 1,
      (groupCohomology.map (QuotientGroup.mk' N)
        (trivResInv (QuotientGroup.mk' N) (ZMod p)) 1).hom hb' =
        (b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
          (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).symm h := by
    refine ⟨χ₀, ?_⟩
    rw [hh, hbdef]
    exact ((b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).symm_apply_apply
      ((groupCohomology.map (QuotientGroup.mk' N)
        (trivResInv (QuotientGroup.mk' N) (ZMod p)) 1).hom χ₀)).symm
  -- The value of the level coefficient map on `1` is the image of `a` in `L_{w'}ˣ`.
  let u : (Rep.res g (Rep.res f₀ (localUnitsK (k := k) w))).V := Additive.ofMul a
  have h₁ : Rep.Hom.hom (Rep.resMap g ι₀) u
      = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w₀ w hw₀ a) :=
    hι₀ a
  have h₂ : Rep.Hom.hom (Rep.resMap g ι₀ ≫ ι₁) u
      = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w₀ hw'
          (NK.GlobalCFT.Place.localAlgebraMapUnits w₀ w hw₀ a)) := by
    rw [Rep.hom_comp]
    simp only [Representation.IntertwiningMap.comp_apply]
    rw [h₁]
    exact hι₁ (NK.GlobalCFT.Place.localAlgebraMapUnits w₀ w hw₀ a)
  have hcomp : Rep.Hom.hom (((Rep.resFunctor (f₀.comp g)).map φ) ≫ (Rep.resMap g ι₀ ≫ ι₁))
      (1 : Coeff)
      = Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w' w₀ hw'
          (NK.GlobalCFT.Place.localAlgebraMapUnits w₀ w hw₀ a)) := by
    rw [Rep.hom_comp]
    simp only [Representation.IntertwiningMap.comp_apply]
    exact h₂
  -- `y` vanishes at the level `(L, w')` with the level data `(g, ι₁)`.
  have hzero : levelPair (f₀.comp g) (Rep.resMap g ι₀ ≫ ι₁)
      (pushClass_lde p (localUnitsK (k := k) w) φ) h = 0 := by
    rw [← hφ]
    exact hy L w' hw' g hg ι₁ hι₁ h
  -- the group-cohomology class corresponding to `h` at the level `(L, w')`
  set χ : groupCohomology
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p)) 1 :=
    (b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
      (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).symm h with hχ
  have hχne : χ ≠ 0 := by
    rw [hχ]
    intro h0
    have h1 : (b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
        (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p)))
        ((b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
          (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).symm h) = h :=
      (b.e 1 (MulAction.stabilizer (L ≃ₐ[k] L) w')
        (Rep.trivial Coeff (MulAction.stabilizer (L ≃ₐ[k] L) w') (ZMod p))).apply_symm_apply h
    rw [h0, map_zero] at h1
    exact hne h1.symm
  have hbridge : groupCohomology.map (MonoidHom.id (MulAction.stabilizer (L ≃ₐ[k] L) w'))
      (((Rep.resFunctor (f₀.comp g)).map φ) ≫ (Rep.resMap g ι₀ ≫ ι₁)) 2
      ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact
        (MulAction.stabilizer (L ≃ₐ[k] L) w') p) 1 2 rfl).hom χ) = 0 :=
    (levelPair_pushClass_bridge b p (f₀.comp g) (Rep.resMap g ι₀ ≫ ι₁) φ h).mp hzero
  have hcrit := (normCriterion_quotient_apply_one'
      (((Rep.resFunctor (f₀.comp g)).map φ) ≫ (Rep.resMap g ι₀ ≫ ι₁))
      (fun σ => rep_hom_apply_one_fixed _ σ) N p hcyc hcard
      (hilbert90_localUnitsRep (k := k) (L := L) w' N) χ hlift hχne).mp hbridge
  rw [hcomp] at hcrit
  exact hfail hcrit


end Work.SSGRoute
