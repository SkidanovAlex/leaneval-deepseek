import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Submission.Work.SSGRoute.local_duality_ext
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

LEAD NOTES (SSG E7b redesign, requests/ssg6). Your node is `rightDetect_quotient_step`; find it in the design below (its tag, content, dependencies and size). Definitions: Submission.Work.SSGRoute.E7bDefs (lead-placed; do not edit). All 19 E7b nodes are dispatched in parallel as Submission.Work.SSGRoute.<name>. If you need a sibling, IMPORT its module; never reprove it or restate it under another name. Key idea: restrict to a Sylow p-subgroup of D_w first, so every simple module is 𝔽_p. Do NOT use the Sylow-free dévissage (local_duality_detect_step/base) or the degree-0/2/Euler lane. Do NOT delete or rewrite local_duality_ext.lean: it carries shared helper lemmas. If you believe your statement is false, give a concrete counterexample.

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

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

-- Instance house-keeping for `Coeff = ULift ℤ` (as in `powHomRepDefs`), needed by `powHomRep`.
attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module
attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass
attribute [local instance 1] ULift.distribSMul ULift.distribMulAction ULift.smulWithZero
attribute [local instance 1] ULift.mulActionWithZero

section Helpers

/-- Composing with `mk₀` of an isomorphism is injective: `u ≫ mk₀ θ = 0` forces `u = 0`. -/
lemma ext_eq_zero_of_comp_mk₀_iso {G : Type} [Group G] {M M' X : Rep.{0} Coeff G} {n : ℕ}
    (θ : M ≅ M') (u : Abelian.Ext.{0} X M n)
    (h : u.comp (Abelian.Ext.mk₀ θ.hom) (add_zero n) = 0) : u = 0 := by
  have h2 : (u.comp (Abelian.Ext.mk₀ θ.hom) (add_zero n)).comp (Abelian.Ext.mk₀ θ.inv)
      (add_zero n) = 0 := by rw [h]; simp
  simpa only [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀, θ.hom_inv_id,
    Abelian.Ext.comp_mk₀_id] using h2

/-- **The connecting maps are adjoint for the level pairing.**  For `z ∈ Ext¹_D(S.X₁, A)` and
`x₃ ∈ Hⁿ(G, res S.X₃)`, the pairing of `z` with the image of `x₃` under the connecting map of the
restricted sequence equals the pairing of the image of `z` under the connecting map of `S` with
`x₃`. -/
lemma levelPair_extClass_comp {G D : Type} [Group G] [Group D] (f : G →* D)
    {A : Rep.{0} Coeff D} {B : Rep.{0} Coeff G} (ι : Rep.res f A ⟶ B)
    (S : ShortComplex (Rep.{0} Coeff D)) (hS : S.ShortExact) {n : ℕ}
    (z : Abelian.Ext.{0} S.X₁ A 1) (x₃ : extH (Rep.res f S.X₃) n) :
    levelPair f ι z (x₃.comp (hS.map_of_exact (Rep.resFunctor f)).extClass rfl) =
      levelPair f ι (hS.extClass.comp z rfl) x₃ := by
  have hβ : (hS.map_of_exact (Rep.resFunctor f)).extClass
      = (hS.extClass).mapExactFunctor (Rep.resFunctor f) :=
    (Abelian.Ext.mapExactFunctor_extClass (Rep.resFunctor f) hS).symm
  have hcomp : (hS.extClass.comp z rfl).mapExactFunctor (Rep.resFunctor f)
      = ((hS.extClass).mapExactFunctor (Rep.resFunctor f)).comp
        (z.mapExactFunctor (Rep.resFunctor f)) rfl :=
    Abelian.Ext.mapExactFunctor_comp (F := Rep.resFunctor f) (α := hS.extClass) (β := z)
      (h := rfl)
  simp only [levelPair, extRes]
  rw [hβ, hcomp]
  have hstep1 : (x₃.comp ((hS.extClass).mapExactFunctor (Rep.resFunctor f)) rfl).comp
        ((z.mapExactFunctor (Rep.resFunctor f)).comp (Abelian.Ext.mk₀ ι) (add_zero 1)) rfl
      = x₃.comp (((hS.extClass).mapExactFunctor (Rep.resFunctor f)).comp
          ((z.mapExactFunctor (Rep.resFunctor f)).comp (Abelian.Ext.mk₀ ι) (add_zero 1)) rfl)
        rfl :=
    Abelian.Ext.comp_assoc x₃ ((hS.extClass).mapExactFunctor (Rep.resFunctor f))
      ((z.mapExactFunctor (Rep.resFunctor f)).comp (Abelian.Ext.mk₀ ι) (add_zero 1))
      rfl rfl rfl
  have hstep2 : (((hS.extClass).mapExactFunctor (Rep.resFunctor f)).comp
        (z.mapExactFunctor (Rep.resFunctor f)) rfl).comp (Abelian.Ext.mk₀ ι) (add_zero 2)
      = ((hS.extClass).mapExactFunctor (Rep.resFunctor f)).comp
          ((z.mapExactFunctor (Rep.resFunctor f)).comp (Abelian.Ext.mk₀ ι) (add_zero 1)) rfl :=
    Abelian.Ext.comp_assoc ((hS.extClass).mapExactFunctor (Rep.resFunctor f))
      (z.mapExactFunctor (Rep.resFunctor f)) (Abelian.Ext.mk₀ ι) rfl (add_zero 1) rfl
  rw [hstep1, hstep2]

end Helpers

/-- Variant of `Work.SSGRoute.levelPair_coeff_naturality` in which the restriction map is written as
`(Rep.resFunctor f).map π` rather than `Rep.resMap f π`.  The two are definitionally equal, but the
rewriter is sensitive to the spelling.  This file cannot import the module holding the sibling lemma
(a dependency cycle through `rightDetect_pgroup`), so the (three-line) proof is reproduced here. -/
lemma levelPair_coeff_naturality_map {H G : Type} [Group H] [Group G] (f : H →* G)
    {M M' : Rep.{0} Coeff G} (π : M ⟶ M') {A : Rep.{0} Coeff G} {B : Rep.{0} Coeff H}
    (ι : Rep.res f A ⟶ B) {r s : ℕ} (y : Abelian.Ext.{0} M' A r)
    (h : extH (Rep.res f M) s) :
    levelPair f ι ((Abelian.Ext.mk₀ π).comp y (zero_add r)) h =
      levelPair f ι y (h.comp (Abelian.Ext.mk₀ ((Rep.resFunctor f).map π)) (add_zero s)) := by
  simp only [levelPair, extRes, Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.comp_assoc_of_third_deg_zero]

/-- **X1 (E7b(ii), p-group step, abstract).**  Let `f : G ↠ D` be a surjection of finite groups,
`ι : res_f A ⟶ B`, and `0 → S.X₁ → S.X₂ → S.X₃ → 0` a short exact sequence of `D`-modules with
`S.X₃ ≅ 𝔽_p` trivial and `S.X₂` killed by `p`.  If the `p`-torsion of `H²(G,B)` has `p` elements
and `Ext²_D(𝔽_p, A)` has at most `p` elements, then right detection for `S.X₁` and for `𝔽_p`
gives right detection for `S.X₂`. -/
theorem rightDetect_quotient_step (p : ℕ) [Fact p.Prime] {G D : Type} [Group G] [Group D]
    [Finite G] [Finite D] (f : G →* D) (hf : Function.Surjective f)
    {A : Rep Coeff D} {B : Rep Coeff G} (ι : Rep.res f A ⟶ B)
    (hT : Nat.card {x : extH B 2 // p • x = 0} = p)
    (hE2 : Finite (Abelian.Ext (Rep.trivial Coeff D (ZMod p)) A 2))
    (hE2card : Nat.card (Abelian.Ext (Rep.trivial Coeff D (ZMod p)) A 2) ≤ p)
    (S : ShortComplex (Rep Coeff D)) (hS : S.ShortExact)
    (e : S.X₃ ≅ Rep.trivial Coeff D (ZMod p))
    [Finite S.X₁] (hp₁ : ∀ m : S.X₁, p • m = 0) (hp₂ : ∀ m : S.X₂, p • m = 0)
    (h₁ : RightDetect f ι S.X₁) (h₃ : RightDetect f ι (Rep.trivial Coeff D (ZMod p))) :
    RightDetect f ι S.X₂ := by
  classical
  intro h hne
  -- `S.X₃` is `p`-torsion: it is a quotient of `S.X₂`
  have hp₃ : ∀ m : S.X₃, p • m = 0 := by
    intro m
    obtain ⟨x, hx⟩ := (Rep.epi_iff_surjective S.g).mp hS.epi_g m
    rw [← hx]
    have h1 : S.g (p • x) = p • S.g x := map_nsmul (Rep.Hom.hom S.g).toLinearMap p x
    rw [← h1, hp₂ x, map_zero]
  -- the target `Ext²_D(S.X₃, A)` of the connecting map
  have hpE : ∀ x : Abelian.Ext S.X₃ A 2, p • x = 0 := fun x => ext_nsmul_p_torsion_left p hp₃ x
  have hcancel : ∀ x : Abelian.Ext S.X₃ A 2,
      (Abelian.Ext.mk₀ e.hom).comp ((Abelian.Ext.mk₀ e.inv).comp x (zero_add 2)) (zero_add 2)
        = x := by
    intro x
    rw [Abelian.Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Abelian.Ext.mk₀_id_comp]
  have hinj : Function.Injective
      (fun u : Abelian.Ext S.X₃ A 2 => (Abelian.Ext.mk₀ e.inv).comp u (zero_add 2)) := by
    intro u v huv
    have huv' : (Abelian.Ext.mk₀ e.inv).comp u (zero_add 2)
        = (Abelian.Ext.mk₀ e.inv).comp v (zero_add 2) := huv
    calc u = (Abelian.Ext.mk₀ e.hom).comp ((Abelian.Ext.mk₀ e.inv).comp u (zero_add 2))
          (zero_add 2) := (hcancel u).symm
      _ = (Abelian.Ext.mk₀ e.hom).comp ((Abelian.Ext.mk₀ e.inv).comp v (zero_add 2))
          (zero_add 2) := congrArg
            (fun x => (Abelian.Ext.mk₀ e.hom).comp x (zero_add 2)) huv'
      _ = v := hcancel v
  haveI hEfin : Finite (Abelian.Ext S.X₃ A 2) := Finite.of_injective _ hinj
  have hEcard : Nat.card (Abelian.Ext S.X₃ A 2) ≤ p := by
    have h := Nat.card_le_card_of_injective
      (fun u : Abelian.Ext S.X₃ A 2 => (Abelian.Ext.mk₀ e.inv).comp u (zero_add 2)) hinj
    exact h.trans hE2card
  haveI hfin₁ : Finite (Rep.res f S.X₁) := ‹Finite S.X₁›
  haveI hWfin : Finite (extH (Rep.res f S.X₁) 1) :=
    local_duality_ext_extH_finite (Rep.res f S.X₁) 1
  -- the connecting map `d` of the sequence `S` in the first variable
  let d : Abelian.Ext S.X₁ A 1 →+ Abelian.Ext S.X₃ A 2 :=
    { toFun := fun z => hS.extClass.comp z rfl
      map_zero' := by simp
      map_add' := fun a b => by simp }
  -- push `h` forward along `S.g`
  let hg : extH (Rep.res f S.X₃) 1 :=
    h.comp (Abelian.Ext.mk₀ ((S.map (Rep.resFunctor f)).g)) (add_zero 1)
  by_cases hg0 : hg = 0
  · -- ## the case where `h` is the image of a class in `H¹(G, S.X₁)`
    obtain ⟨hsub, hhsub⟩ := Abelian.Ext.covariant_sequence_exact₂
      (X := unitRep G) (S := S.map (Rep.resFunctor f))
      (hS := hS.map_of_exact (Rep.resFunctor f)) (n := 1) h hg0
    have hsubne : hsub ≠ 0 := by
      intro h0
      apply hne
      rw [← hhsub, h0]
      exact Abelian.Ext.zero_comp (unitRep G) 1
        (Abelian.Ext.mk₀ ((S.map (Rep.resFunctor f)).f)) 1 (add_zero 1)
    -- the element of `S.X₃` over `1`
    let u₃ : S.X₃ := (Rep.Hom.hom e.inv) 1
    have hu₃ : (Rep.Hom.hom e.hom) u₃ = 1 := by
      show (Rep.Hom.hom e.hom) ((Rep.Hom.hom e.inv) 1) = 1
      rw [Rep.hom_inv_apply]
    have hcancelE : ∀ x : S.X₃, (Rep.Hom.hom e.inv) ((Rep.Hom.hom e.hom) x) = x :=
      fun x => by rw [Rep.inv_hom_apply]
    have hu₃fixD : ∀ δ : D, S.X₃.ρ δ u₃ = u₃ := by
      intro δ
      have h1 : (Rep.Hom.hom e.hom) (S.X₃.ρ δ u₃) = (Rep.Hom.hom e.hom) u₃ := by
        rw [Rep.hom_comm_apply, hu₃]
        simp
      calc S.X₃.ρ δ u₃
          = (Rep.Hom.hom e.inv) ((Rep.Hom.hom e.hom) (S.X₃.ρ δ u₃)) := (hcancelE _).symm
        _ = (Rep.Hom.hom e.inv) ((Rep.Hom.hom e.hom) u₃) := by rw [h1]
        _ = u₃ := hcancelE u₃
    have hu₃fixG : ∀ γ : G, (Rep.res f S.X₃).ρ γ u₃ = u₃ := fun γ => hu₃fixD (f γ)
    let one₃ : unitRep G ⟶ Rep.res f S.X₃ := powHomRep u₃ hu₃fixG
    have hone₃ : (Rep.Hom.hom one₃) (1 : Coeff) = u₃ := by
      rw [powHomRep_apply, one_smul]
    have hone : e.hom (one₃ 1) = 1 := by
      show (Rep.Hom.hom e.hom) ((Rep.Hom.hom one₃) (1 : Coeff)) = 1
      rw [hone₃, hu₃]
    -- the connecting class
    let eG : extH (Rep.res f S.X₁) 1 :=
      (Abelian.Ext.mk₀ one₃).comp ((hS.map_of_exact (Rep.resFunctor f)).extClass) (zero_add 1)
    by_cases heG : eG = 0
    · -- ### the case where the connecting class vanishes: `S` splits over `D`
      obtain ⟨m, hmD, hm1⟩ :=
        exists_fixed_element_of_connecting_eq_zero p f hf S hS e one₃ hone heG
      obtain ⟨s, hs⟩ := exists_section_of_fixed_generator p S e hp₂ m hmD hm1
      let Sp := ShortComplex.Splitting.ofExactOfSection S hS.exact s hs hS.mono_f
      obtain ⟨z₀, hz₀⟩ := h₁ hsub hsubne
      refine ⟨(Abelian.Ext.mk₀ Sp.r).comp z₀ (zero_add 1), ?_⟩
      have hnat : levelPair f ι ((Abelian.Ext.mk₀ S.f).comp
            ((Abelian.Ext.mk₀ Sp.r).comp z₀ (zero_add 1)) (zero_add 1)) hsub
          = levelPair f ι ((Abelian.Ext.mk₀ Sp.r).comp z₀ (zero_add 1))
            (hsub.comp (Abelian.Ext.mk₀ ((S.map (Rep.resFunctor f)).f)) (add_zero 1)) :=
        levelPair_coeff_naturality_map f S.f ι _ hsub
      have hkey : (Abelian.Ext.mk₀ S.f).comp ((Abelian.Ext.mk₀ Sp.r).comp z₀ (zero_add 1))
          (zero_add 1) = z₀ := by
        rw [Abelian.Ext.mk₀_comp_mk₀_assoc, Sp.f_r, Abelian.Ext.mk₀_id_comp]
      rw [← hhsub, ← hnat, hkey]
      exact hz₀
    · -- ### the case where the connecting class is nonzero: the "K"-argument
      have hy : ∃ z : Abelian.Ext S.X₁ A 1,
          hS.extClass.comp z rfl = 0 ∧ levelPair f ι z hsub ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        have heGK : ∀ z : Abelian.Ext S.X₁ A 1, hS.extClass.comp z rfl = 0 →
            levelPair f ι z eG = 0 := by
          intro z hz
          rw [show eG = (Abelian.Ext.mk₀ one₃).comp
              ((hS.map_of_exact (Rep.resFunctor f)).extClass) (zero_add 1) from rfl,
            levelPair_extClass_comp f ι S hS z (Abelian.Ext.mk₀ one₃), hz]
          exact levelPair_zero f ι (Abelian.Ext.mk₀ one₃)
        have hWp : ∀ w : extH (Rep.res f S.X₁) 1, p • w = 0 :=
          fun w => ext_nsmul_p_torsion (A := Rep.res f S.X₁) p hp₁ w
        letI : Module (ZMod p) (extH (Rep.res f S.X₁) 1) := AddCommGroup.zmodModule hWp
        obtain ⟨c, hc⟩ := exists_smul_eq_of_annihilator p hpE hEcard hWp hT
          d (fun z w => levelPair f ι z w)
          (fun v₁ v₂ w => levelPair_add f ι v₁ v₂ w)
          (fun v w₁ w₂ => levelPair_add_h f ι v w₁ w₂)
          (fun c z w => by
            have hcw : c • w = c.val • w := by
              rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) c.val w, ZMod.natCast_zmod_val c]
            rw [hcw]
            exact map_nsmul (levelPairFunctional f ι z) c.val w)
          (fun z w => by
            have h1 : levelPair f ι z (p • w) = p • levelPair f ι z w :=
              map_nsmul (levelPairFunctional f ι z) p w
            rw [← h1, hWp w]
            exact levelPair_zero_h f ι z)
          h₁ heG heGK hcon
        exfalso
        have heGker : eG.comp (Abelian.Ext.mk₀ ((S.map (Rep.resFunctor f)).f)) (add_zero 1) = 0 := by
          rw [show eG = (Abelian.Ext.mk₀ one₃).comp
              ((hS.map_of_exact (Rep.resFunctor f)).extClass) (zero_add 1) from rfl,
            Abelian.Ext.comp_assoc_of_third_deg_zero, ShortComplex.ShortExact.extClass_comp]
          simp
        have hcv : c • eG = c.val • eG := by
          rw [← Nat.cast_smul_eq_nsmul (R := ZMod p) c.val eG, ZMod.natCast_zmod_val c]
        apply hne
        rw [← hhsub, ← hc, hcv]
        let iStar : extH (Rep.res f S.X₁) 1 →+ extH (Rep.res f S.X₂) 1 :=
          { toFun := fun u => u.comp (Abelian.Ext.mk₀ ((S.map (Rep.resFunctor f)).f))
              (add_zero 1)
            map_zero' := by simp
            map_add' := fun a b => by simp }
        have hsm : (c.val • eG).comp (Abelian.Ext.mk₀ ((S.map (Rep.resFunctor f)).f))
              (add_zero 1)
            = c.val • (eG.comp (Abelian.Ext.mk₀ ((S.map (Rep.resFunctor f)).f))
                (add_zero 1)) :=
          map_nsmul iStar c.val eG
        rw [hsm, heGker, smul_zero]
      obtain ⟨z, hz0, hz⟩ := hy
      obtain ⟨y, hy⟩ := Abelian.Ext.contravariant_sequence_exact₁ (S := S) hS A z (by omega) hz0
      refine ⟨y, ?_⟩
      have hnat : levelPair f ι ((Abelian.Ext.mk₀ S.f).comp y (zero_add 1)) hsub
          = levelPair f ι y (hsub.comp (Abelian.Ext.mk₀ ((S.map (Rep.resFunctor f)).f))
              (add_zero 1)) :=
        levelPair_coeff_naturality_map f S.f ι y hsub
      rw [← hhsub, ← hnat, hy]
      exact hz
  · -- ## the case `π_* h ≠ 0`: use the base case for `𝔽_p`
    let hg3 : extH (Rep.res f (Rep.trivial Coeff D (ZMod p))) 1 :=
      hg.comp (Abelian.Ext.mk₀ (Rep.resMap f e.hom)) (add_zero 1)
    have hg3ne : hg3 ≠ 0 := fun h0 =>
      hg0 (ext_eq_zero_of_comp_mk₀_iso ((Rep.resFunctor f).mapIso e) hg h0)
    obtain ⟨y₃, hy₃⟩ := h₃ hg3 hg3ne
    refine ⟨(Abelian.Ext.mk₀ S.g).comp ((Abelian.Ext.mk₀ e.hom).comp y₃ (zero_add 1))
      (zero_add 1), ?_⟩
    have hnat1 : levelPair f ι ((Abelian.Ext.mk₀ S.g).comp
          ((Abelian.Ext.mk₀ e.hom).comp y₃ (zero_add 1)) (zero_add 1)) h
        = levelPair f ι ((Abelian.Ext.mk₀ e.hom).comp y₃ (zero_add 1))
          (h.comp (Abelian.Ext.mk₀ ((S.map (Rep.resFunctor f)).g)) (add_zero 1)) :=
      levelPair_coeff_naturality_map f S.g ι _ h
    have hnat2 : levelPair f ι ((Abelian.Ext.mk₀ e.hom).comp y₃ (zero_add 1))
          (h.comp (Abelian.Ext.mk₀ ((S.map (Rep.resFunctor f)).g)) (add_zero 1))
        = levelPair f ι y₃ (hg.comp (Abelian.Ext.mk₀ (Rep.resMap f e.hom)) (add_zero 1)) :=
      levelPair_coeff_naturality_map f e.hom ι y₃ _
    rw [hnat1, hnat2]
    exact hy₃

end Work.SSGRoute
