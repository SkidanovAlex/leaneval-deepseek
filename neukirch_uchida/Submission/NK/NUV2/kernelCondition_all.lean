import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Target
import Submission.NK.LocalReciprocityLubinTate.Unramified.adicResidual
import Submission.NK.LocalReciprocityLubinTate.Unramified.nonempty_symbolTower_adicCompletion
import Submission.NK.Summary.NUV2.CanonicalTowerResidue
import Submission.NK.NUV2.Final.Assembly

/-! Guidance from the project lead (the requester):

## Context (orchestrator, 2026-09-23)
The old wall `NK.EndgameRepair.ClassicalChaptersRepaired` is UNSATISFIABLE — do not use it or any of its fields'
catalogues as targets: `IndecomposedDeep.DeepInputs.indexOne` fails (quartic K with 2 = 𝔭₁𝔭₂³, K_{𝔭₂} ≅ ℚ₂(∛2):
G_{ℚ₂(∛2)} ≤ D_A is self-normalising, ≅ a local Galois group, of index 3), and `TowerRankCore.finiteIndex_isClosed`
is false without `FiniteDimensional κ M`. Also avoid `LocalStructure.LocalNUExistence` (G_M ≅ G_κ ⇒ M ≅ κ is false,
Yamagata/Jarden–Ritter), `UchidaKummer.IsWeakUchida`, `CyclicPrimeReduction`.
The new wall is `NK.NUV2.ChaptersV2` (`Submission/Work/NUV2/Wall.lean`, do NOT edit): the four inputs of the proved
`NK.EndgameRepair.exists_sigma_of_correctedResiduals`. Library inputs being proved elsewhere in this workspace and
allowed as hypotheses where the statement has them: `NK.GlobalCFTdeep.FundamentalClassElement` (global
fundamental class ⇒ class-formation axioms, reciprocity C_K/N C_L ≅ Gal(L/K)ᵃᵇ via
`artinReciprocity_of_cohomologicalFieldAxiom`, Tate's theorem, Albert–Brauer–Hasse–Noether) and
`NK.LocalArtin.KernelCondition` at every completion (⇒ `NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion`).
Design rules: state every local isomorphism as a CONTINUOUS isomorphism (ϕ is a homeomorphism; this removes
Nikolov–Segal entirely); for Brauer arguments use an ODD prime p (Br(ℝ)[p] = 0). Instantiate every new sub-statement
at K = ℚ and at the quartic above as a satisfiability check before relying on it. Delegate; one lemma per step.
## This lemma: `NK.LocalArtin.KernelCondition` at every completion (local reciprocity law)
Data: a hom artin : Fˣ →* AbGal F F' with ker (levelRestrict L ∘ artin) = normGroup F L for every finite abelian
normal L. Lubin–Tate gives the totally ramified part (Honda's law proved: `Unramified.hondaReciprocity`; existence
and norm index proved). Remaining: base-change invariance. Route A (README of LocalReciprocityLubinTate §21.15):
the different identity Tr(𝔡⁻¹) = 𝒪_F for the Eisenstein extension + the trace formula. Alternative route B: the
local fundamental class (Commons `fundamental_class_local_galois`) + Tate's theorem iso form
(`ArtinMap.addEquiv_tateCohomology_of_fundamental_class`) give Artin maps at each level with kernel = norms
(`exists_artinMap_of_abelian_local`); the missing point is compatibility across levels (canonical normalisation via
the unramified invariant). Run whichever is shorter; both as sub-lemmas if unsure.
-/

namespace NK.NUV2

/-! ## Where the proof stands, and the two sharp residues it rests on

The target is the local reciprocity law in the "kernel condition" form for `F = Q.adicCompletion K`
and `F' = SeparableClosure F`.  The proof is routed through the chapter
`Submission/Work/LocalReciprocityLubinTate/`, whose boundary theorem
`NK.LocalReciprocityLubinTate.Unramified.artinReciprocity_adicCompletion_of_towerCover` produces
the full Artin reciprocity datum from **exactly two** inputs:

* `NormInKernel` for the canonical Lubin–Tate symbol tower (`adicSymbolTower`) — the
  norm-compatibility of the canonical Artin symbols: *the Artin symbol of a norm is trivial*.  This
  is Serre, *Local Fields* XI §2 / XV §5.2, and Iwasawa, *Local Class Field Theory*, Theorem 6.9
  (the base-change compatibility `Art_{K'}(x)|K^{LT} = Art_K(N_{K'/K}(x))`) together with the norm
  computation of the Lubin–Tate levels (Honda); the *tower-level* case is a theorem here
  (`NK.LocalReciprocityLubinTate.normInKernel_level`), and so is the *cyclic* case
  (`NormInKernel.of_isCyclic_adicCompletion`).
* the *tower-level covering*: if the norm group of a tower level `E_{m,n}` is contained in the norm
  group of a finite abelian level `L`, then `L ≤ E_{m,n}` (Hasse's *Normensatz* / Umkehrsatz
  restricted to the tower levels).

Everything else is proved in the chapter: the Lubin–Tate symbol tower and its canonical symbols,
Honda's explicit reciprocity law (the norm groups `N_{E_{m,n}/F} = ⟨π^{(m+1)!}⟩·U^{n+1}`), the norm
index theorem `[Fˣ : N_{L/F}Lˣ] = [L : F]`, the existence theorem, and the assembly of the level
symbols into the reciprocity law (which uses *counting*, `NormIndex`, and the two inputs above).

Both residues are the *same* classical theorem seen from two sides (the canonicity of the norm
residue symbol); the covering is a consequence of the norm-compatibility plus the norm index (apply
the level conditions to `N_{E_{m,n}} ≤ N_L` and compare indices), and conversely the covering plus
`NormInKernel` produces the norm-subgroup correspondence.  They are delegated as the lemmas
`NK.Summary.NUV2.normInKernel_adicCompletion`,
`NK.Summary.NUV2.normGroup_towerCover_adicCompletion` (and the stronger
`NK.Summary.NUV2.normCorrespondence_adicCompletion`).

The final assembly — the body of `kernelCondition_all` below — is then, verbatim:

```
obtain ⟨π, hπ⟩ := NK.LocalReciprocityLubinTate.exists_isUniformizer_adicCompletion Q
exact ⟨NK.LocalReciprocityLubinTate.kernelCondition_of_artinReciprocity
  (NK.LocalReciprocityLubinTate.Unramified.artinReciprocity_adicCompletion_of_towerCover
    Q hπ (normGroup_towerCover_adicCompletion Q hπ) (normInKernel_adicCompletion Q hπ)).some⟩
```

(verified to elaborate, with the two residues as hypotheses, in the probe file
`_kc_cov_probe.lean` of this workspace), so that `KernelCondition` — the datum consumed by
`NK.LocalReciprocityLubinTate.artinReciprocity_adicCompletion` and hence by the Neukirch–Uchida
wall `NK.NUV2.ChaptersV2` — is *strictly weaker* than what the chapter delivers.
-/

/-! ## Status of the relative Lubin–Tate route (session log)

The route to `CanonicalTowerResidue` is the *relative* Lubin–Tate theory of de Shalit / Yoshida
(arXiv:math/0606108), whose §3 (the relative formal group and the `Θ`-action) is now **complete** in
`Submission/Work/NUV2/RelativeLT/` (all sorry-free, axiom-clean):

| Yoshida | Lean name |
|---|---|
| Lemma 3.4 (unique relative solution) | `NK.NUV2.RelativeLT.existsUnique_relativeLubinTate_solution` |
| Prop. 3.5(1) (group law) | `…existsUnique_relativeLubinTate_groupLaw`, `…formalGroupLaw` |
| Prop. 3.5(2) (`[θ]` exists, unique) | `…existsUnique_relativeLubinTate_smulLaw` |
| Prop. 3.5(2) (`[θ'][θ] = [θθ']`) | `NK.NUV2.RelativeLT.relativeLubinTate_smul_comp` |
| Prop. 3.5(2) (`[θ]+[θ'] = [θ+θ']`) | `NK.NUV2.RelativeLT.relativeLubinTate_add`, `…add_aux` |
| Prop. 3.5(3) (`[θ]` is a formal-group hom) | `NK.NUV2.RelativeLT.relativeLubinTate_smul_hom` |
| Cor. 3.7(i) base case `[1] = X` | `NK.NUV2.RelativeLT.relativeLubinTate_smul_one_eq` |
| Cor. 3.7(ii) (`[θ]` iso for `θ` a unit) | `NK.NUV2.RelativeLT.relativeLubinTate_smul_unit_eq` |
| Def. 3.9 (`f_m`, the pair equation, `π_m`) | `NK.NUV2.RelativeLT.fIter`, `IsRelEndoPair`, `coeff_fIter_linear` |

The *interface* for this layer is `NK.NUV2.RelativeLT.RelData` (`Submission/Work/NUV2/RelativeLT/
Smul.lean`), which bundles the standing hypotheses of §3, and `NK.NUV2.RelativeLT.smulRel`, the
choice-form of `[θ]_{f,f'}` together with its specification lemmas
(`smulRel_linear`, `smulRel_spec`, `eq_smulRel`).

## What is *mathematically* left (the honest residual)

The target `KernelCondition` at `F = Q.adicCompletion K` is the full local reciprocity law.  With
the workspace's machinery the missing content is exactly **two** classical theorems:

1. **the base change** `Art_{K'}(x)|K^{LT} = Art_K(N_{K'/K}(x))` (Yoshida Theorem 5.15), which —
   together with the already proved Honda reciprocity law `Unramified.hondaReciprocity` and the
   relative Lubin–Tate theory — gives the norm-kernel property `NormInKernel`;
2. **the local Kronecker–Weber theorem** `F^{ab} = F^{ur}·F^{LT}` (Yoshida §6, via Hasse–Arf),
   which gives the covering `LevelCovered`.

Both are needed: `LevelCovered` is not a consequence of `NormInKernel` (given a finite abelian
`L ≤ F^{ab}` one can always find a tower level `E` with `N_E ≤ N_L`, but concluding `L ≤ E` from
`N_E ≤ N_L` *is* the norm-subgroup correspondence, i.e. the canonicity again), and `NormInKernel` is
not a consequence of `LevelCovered`.

## Where the canonicity (1) actually bites: the *graph* subfields

Write `E_{m,n} = F^{ur}_{a m}·K_n` with `K_n = F(Λ_{n+1})` the absolute Lubin–Tate level, so that
`Gal(E_{m,n}/F) = G_1 × G_2` with `G_1 = Gal(F^{ur}_{a m}/F)` cyclic and `G_2 = Gal(K_n/F)`.  The
canonical level symbol is the pair

`Φ_{m,n}(x) = (Frob^{v(x)}, [u_x])`,  `x = π^{v(x)}·u_x`.

For a subfield `L = E^H` (`H ≤ G_1 × G_2`) the assertion `Φ_{m,n}(N_L) = Gal(E_{m,n}/L)` splits:

* the **unramified component** is free: for `x = N_{L/F}(y)` one has
  `v(x) = f(L/F)·v_L(y)`, and `[M:F] ∣ f(L/F)` for `M = L ∩ F^{ur}_{a m}`, so the Frobenius part
  always acts trivially on `M` — no canonicity is consumed;
* the **ramified component** is free as long as `L` contains all of `L ∩ K_n` "on its own", i.e.
  as long as `H = p_1 H × p_2 H` (a *direct-product* subgroup): then `L = M·T` with
  `T = L ∩ K_n`, and `x ∈ N_L ⊆ N_T` gives the claim from the totally ramified case;
* the **obstruction** is exactly the *graph* subgroups `H ≰ p_1H × p_2H`, i.e. subfields
  `L/F` that are totally ramified over `F` yet are *not* contained in `F^{LT}` (the smallest
  example is the diagonal quadratic subfield of a biquadratic `F^{ur}_2·K_1`).  For these,
  `L = E^H` with `H` a graph, `Φ_{m,n}(N_L) ≤ G_1 × G_2` has the right order `|H|` but the
  *containment* `Φ_{m,n}(N_L) ≤ H` is precisely Theorem 5.15 (Yoshida Prop. 5.14, Cor. 5.12,
  Prop. 5.10 — Coleman's operator — and Honda over the unramified base).

So the residual (1) is *not* removable by a counting/norm-index argument: it is consumed at the
graph subfields, and any proof must produce the explicit reciprocity law for the Lubin–Tate symbol
(Yoshida §5.2–5.3, equivalently Serre XV §5.2 via the trace/different: `Algebra.trace` is in
Mathlib but `Ideal.different` is **not** in this pin).

## The next stones, in the order of the paper

1. §4.1–4.2: the relative Lubin–Tate extensions `L_m` over a complete unramified `L/K` (splitting
   fields of `f_m`, `µ_{f,m}`), the Galois structure `Gal(L_m/L) ≅ (𝒪/π^m)^×` (Yoshida Prop. 4.4),
   and the Artin maps `ψ, ρ` of Prop. 4.7–4.8, Cor. 4.9.  (The *algebraic* input `fIter` is now in
   place; what is needed is the field-theoretic layer, mirroring `LubinTate/{LTLevel,isGalois_LTLevel,
   nonempty_autLTLevel_mulEquiv_units}.lean` of the absolute theory.)
2. §5.1: `Prop. 5.4` — for `x ∈ Kˣ` with `v(x) > 0`, `Art_K(x)` is characterised by
   `v(Art_K(x)) = v(x)` and `Art_K(x)|K_x^{ram} = id`.
3. §5.2: Coleman's operator (`N(g) ∘ f = ∏_{α ∈ µ_1} g(X +_f α)`, Lemma 5.5, Lemma 5.7, Lemma 5.8)
   and `N(K_x^m/K) = (1 + 𝔭^m)×⟨x⟩` (Prop. 5.10).
4. §5.3: `Cor. 5.12`, `Prop. 5.14`, and the base change `Theorem 5.15`.
5. §6: Hasse–Arf (via Sen's theorem, *not* via reciprocity) and the local Kronecker–Weber theorem.

## Session 3: the *normalisation* of the symbol tower is part of the residual

The decisive structural point found in this session (and the reason the residual is stated
*existentially*, `∃ T, NormInKernel T ∧ LevelCovered T`) is that **the `LubinTateSymbolTower` axioms do
not determine the conventions of the level symbols**: two towers can have the same levels, the same
norm groups, the same kernels at the *tower* levels and the same compatibility, and yet differ at the
*subfields*.  Concretely, `Gal(E_{m,n}/F) = Gal(F^{ur}_{a_m}/F) × Gal(K_{n+1}/F)`, and the axiom
`symbol_ker` only pins the symbol down as a *homomorphism with a prescribed kernel*, hence only up to
composition with an automorphism of `Gal(E_{m,n}/F)`; twisting both components by the inversion
automorphism of the second factor gives another tower with the *same* data.

The *correct* normalisation is the one for which the canonicity (`NormInKernel`) holds — i.e. the
level symbol has to be the reciprocity map, not merely *some* map with the right tower-level kernels.
It is fixed by the classical convention

  `Art(π) = Frob`  (arithmetic Frobenius) **and** `Art(u) = [u^{-1}]`  on `Λ_{n+1}`   (`u ∈ 𝒪[F]ˣ`),

i.e. the *inverse* of the `[·]`-action on the Lubin–Tate module — the convention of Serre,
*Local Fields*, Ch. XV.  The tower of `Submission/Work/LocalReciprocityLubinTate` is built with the
`[u]`-convention (`LubinTate/exists_ltSymbol_family.lean`, "acts on every division point `z ∈ Λ_n` by
the Lubin–Tate action `[u]`").

*A check of the convention, and of the canonicity at the `p`-adic* tame *graph subfields.*  Let
`F = ℚ₅`, `x = 5i` (`i = √-1 ∈ ℚ₅`) and `M = F(y)` with `y⁴ = -5i`; then `M/F` is the *tame* cyclic
quartic extension `F(π'^{1/4})` for `π' = -5i`, and `M ⊆ F^{ur}_4·K₁` (the graph-type subfield of a
tower level).  Two independent computations of `Art(x)|_M`:

* **Kummer/tame symbol.**  For `M = F(π'^{1/4})` (`4 ∣ q-1 = 4`) the tame reciprocity gives
  `(x, M/F)(π'^{1/4}) = ζ₄^{s}·π'^{1/4}` with `s` the class of
  `(-1)^{v(x)v(π')}x^{v(π')}π'^{-v(x)}` in `𝒪^×/(𝒪^×)⁴ ≅ μ₄`; for `x = -π' = 5i` this symbol is `1`,
  so `Art(5i)` **fixes** `M`.
* **The `[θ]`-computation on the Lubin–Tate side.**  With `y = λ·θ₀`, `λ⁴ = -5` (the `π`-primary
  torsion) and `θ₀ ∈ μ₁₆ ⊆ F^{ur}` (`θ₀⁴ = i`, i.e. `θ₀^φ/θ₀ = x/π`, Yoshida Lemma 4.5), the
  compatibility `Frob([θ₀](α)) = [θ₀^φ](Frob α)` gives, for `Art(x) = (Frob, [u])` with `u = i`,

  `Art(x)(y) = [θ₀^φ·u](λ) = [θ₀·u·u](λ) = [u²]([θ₀](λ)) = [i²](y) = -y`  — **not** `y`;

  while for the normalisation `Art(x) = (Frob, [u^{-1}])` the same computation gives
  `[θ₀^φ·u^{-1}](λ) = [θ₀](λ) = y`  — **fixed**, as the tame symbol requires.

  (The only general inputs used are: `[θ]` is an isomorphism of `𝒪`-modules between the torsion of the
  Lubin–Tate groups of parameters `π` and `x` (Yoshida Prop. 4.6/§3, in the workspace
  `NK.NUV2.RelativeLT`), and the equivariance of `[θ]` under the Frobenius of `F^{ur}/F`.)

So the `[u]`-tower of the chapter **fails** `NormInKernel` at the graph subfields, while the
`[u^{-1}]`-tower satisfies it there.  This is independent confirmation of the interface trap recorded
above ("`NormInKernel (adicSymbolTower …)` is not a theorem"): the well-posed residual really is the
*existential* one, and its witness has to be built with the normalisation `Art(u) = [u^{-1}]`.

## What is reachable with the tools on disk

* **Prop. 5.10** (`N(K_x^m/K) = (1+𝔭^m)×⟨x⟩`, `L = K_n` unramified of degree `n = v(x)`,
  `N_{L/K}(π_L) = x`, `K_x^m = L(Λ^{(π_L)}_m)`) needs **no** relative theory: `K_x^m` is *by
  definition* the `m`-th Lubin–Tate level over the local field `L` with parameter `π_L`, so Honda's law
  over `L` (`Eval.hondaReciprocity_intermediateField`) gives `N_{K_x^m/L}K_x^mˣ = ⟨π_L⟩·U_L^m`; the
  transfer to `K` is then the elementary computation
  `N_{L/K}(⟨π_L⟩U_L^m) = ⟨x⟩·N_{L/K}(U_L^m) ⊆ ⟨x⟩(1+𝔭^m)`, and the reverse inclusion follows from the
  index squeeze `[Kˣ : N_{K_x^m/K}] ≤ [K_x^m : K] = n(q-1)q^{m-1} = [Kˣ : ⟨x⟩(1+𝔭^m)]`
  (using `(Kˣ)^{[K_x^m:K]} ⊆ N_{K_x^m/K}`).  **This is a clean, self-contained classical theorem and the
  first thing to build** — it is the `§5.2` half of the route and it does not need the relative level
  fields.
* **Prop. 5.4** (`Art(x)` fixes `K_x^{ram}`) is the `[θ]`-computation above; its general form needs the
  torsion of the Lubin–Tate groups of *all* parameters, over `K^{ur}` (and, for the `n > 1` case, over the
  unramified levels `K_n`), together with the equivariance of `[θ]` under the relative Frobenius.
  The level-`1`, `n = 1` case is the computation displayed above.
* **Cor. 5.12 / Prop. 5.14 / Thm. 5.15 / Cor. 5.16** then assemble (`∏`-criterion, uniformizers are
  norms, the fixed field `E_σ` of `σ ∈ W(K^{sep}/K)`), and are pure field/norm bookkeeping on top of
  Prop. 5.10 and Prop. 5.4.
* **§6** (local Kronecker–Weber) is *not* LT theory; it is pursued in parallel by
  `NK.LocalKW` / `Submission/Work/Chebotarev/LocalKW*` (for `ℚ_p`) and needs Hasse–Arf (via Sen).

Finally, note that `KernelCondition` itself (the deliverable) is *blind* to the normalisation: for an
abelian Galois group, `Art` and `Art^{-1}` have the same level kernels, and so do the two tower
normalisations above at the tower levels.  Only the *proof* of the residual is affected.  (Careful:
`NormInKernel` *is* invariant under inverting the symbols of one fixed tower, since `σ` and `σ⁻¹`
have the same fixed points; but the two normalisations above are *not* related by inversion — they
differ by inverting the Lubin–Tate component alone, which does change the fixed fields.)

## Concrete delegations for the next session (in order)

1. `NK.NUV2.Canonicity.norm_principalUnits_surjective_of_ramificationIdx_eq_one` — **PROVED**
   (2026-09-24, `Submission/Work/NUV2/Canonicity/norm_principalUnits_surjective_of_ramificationIdx_eq_one.lean`):
   the norm of the `m`-th higher unit group of an *unramified* local extension is onto.
   Together with Honda's law over `L` (`Eval.hondaReciprocity_intermediateField`) and the transitivity
   of the norm, this gives **Prop. 5.10** (`N(K_x^m/K) = (1+𝔭^m)×⟨x⟩`), the `§5.2` half of the route.
2. **The level-wise `[u^{-1}]`-normalised symbol family** (delegated in this session as
   `NK.NUV2.Canonicity.exists_ltSymbol_family_invNormalised`): `LubinTate/exists_ltSymbol_family.lean`
   with the added clause that the symbol of `x` *itself* acts on the division points `z ∈ Λ_n` by
   `Eval.smulDiv … (unitPartHom x)⁻¹`.  Caution (found in review): the clause must **not** be phrased
   as "`(Φ n x)⁻¹` acts by `[u^{-1}]`" — that is equivalent to the existing `[u]`-convention and adds
   nothing; the two normalisations differ by inverting the Lubin–Tate component alone.  The family is
   obtained from the existing one by pointwise inversion (so its symbols are `x ↦ (Ψ n x)⁻¹`), which
   is where the `[u^{-1}]`-action comes from.  The abstract `LubinTateSymbolTower` axioms cannot express
   this normalisation.  **PROVED** (2026-09-24):
   `Submission/Work/NUV2/Canonicity/exists_ltSymbol_family_invNormalised.lean`,
   `NK.NUV2.Canonicity.exists_ltSymbol_family_invNormalised`.
3. **The `[θ]`-equivariance** (the engine of Prop. 5.4)4. **The `[u^{-1}]`-normalised `LubinTateSymbolTower`** for `F = 𝔮.adicCompletion K`, `a m = (m+1)!`:
   the tower-level (unramified + Lubin–Tate) assembly of item 2, mirroring
   `Unramified/nonempty_symbolTower_adicCompletion`.  This is the *witness candidate* for the
   existential residual `CanonicalTowerResidue`; only the canonicity (`NormInKernel` for it) remains
   afterwards, and that is items 3 and below.
5. **Cohomological route (to be checked against the lead's 2026-09-24 message).**  The project lead
   reports that the *global* fundamental class `NK.CFTLib.fundamentalClassElement` is now proved and
   that class-formation axioms, the reciprocity iso `C_K/N C_L ≅ Gal(L/K)ᵃᵇ` and Tate's theorem are
   available.  If the underlying *cup-product* and corestriction/restriction machinery came with it,
   Route B of `README.md` §21.13 (local fundamental class + Tate's isomorphism in iso form
   `ArtinMap.addEquiv_tateCohomology_of_fundamental_class`) becomes viable again; the missing point
   there was exactly the `Res`-compatibility of the local fundamental classes, i.e. the same
   canonicity.  Worth a careful look *before* committing to the relative-Lubin–Tate build of §4.
: for a finite unramified `L/F` with Frobenius
   `φ`, parameters `π, π' ∈ O_F^×`-uniformizers and `θ ∈ O_L^×` with `θ^φ/θ = π'/π`, the
   `[θ]`-isomorphism of the two Lubin–Tate torsion modules satisfies
   `φ([θ](z)) = [θ^φ](φ(z))`.  In the absolute vocabulary this is a statement about `Eval.smulDiv` and
   the Frobenius action on the torsion (`LubinTate/map_mem_LTdivisionSet_of_algEquiv`).
4. Then `Cor. 5.12 → Prop. 5.14 → Thm. 5.15 → Cor. 5.16` are field/norm bookkeeping on top of
   (1)+(3), and §6 (local Kronecker–Weber) is the parallel `NK.LocalKW` project.
-/

/-- **The local reciprocity law in kernel form, at every completion, from the canonical-tower
residual.**

This is the *aligned* form of the reduction: the fleet's well-posed residual
`NK.Summary.NUV2.CanonicalTowerResidue K Q` (the existence of a Lubin–Tate symbol tower whose
symbols annihilate norms and whose levels cover `F^{ab}`) implies the target; the proof
`NK.Summary.NUV2.kernelCondition_of_canonicalTower` is sorry-free and axiom-clean, and uses only
proved theorems of this workspace (the norm index theorem, the assembly of the compatible level
isomorphisms into one Artin map, and the passage from the reciprocity law to the kernel condition).

The residual itself — the *canonicity* of the Lubin–Tate symbol (Iwasawa, *Local Class Field
Theory*, Theorem 6.9, equivalently the `Res`-compatibility of the local fundamental classes /
`Br(F) ≅ ℚ/ℤ`) — is the single unproved classical input of the local side, and is being attacked in
parallel in `Submission/Work/Summary/NUV2/TowerCrux/` and
`Submission/Work/Summary/NUV2/exists_canonicalTower_normInKernel_and_exhausts.lean`.

## Two interface traps, found and recorded here

1. **The opaque tower.** `NK.LocalReciprocityLubinTate.adicSymbolTower` is
   `Classical.choice (nonempty_symbolTower_adicCompletion Q hπ)`, and `Nonempty` has no
   specification lemma, so a theorem about it is a theorem about *every* tower satisfying the
   `LubinTateSymbolTower` axioms.  Those axioms are closed under twists of the level symbols, and
   `NormInKernel` fails for some twists; hence `NormInKernel (adicSymbolTower …)` is *not provable*
   (two colleagues verified this independently).  The *existential* form
   (`∃ T, NormInKernel T`, as in `CanonicalTowerResidue`) is the well-posed statement.
2. **The tower-level covering is not weaker.** The hypothesis `hcov` of
   `artinReciprocity_adicCompletion_of_towerCover` (`N_{E_{m,n}} ≤ N_L ⟹ L ≤ E_{m,n}`) is, by the
   proved reductions on disk, *equivalent* to the kernel condition / the norm-subgroup
   correspondence, i.e. to the residual itself — it is the second class-formation axiom restricted
   to the tower.  So it is not an independent, easier input.

## The route being built (relative Lubin–Tate theory, Yoshida arXiv:math/0606108)

Stones already **proved** in this workspace (`Submission/Work/NUV2/RelativeLT/`, all sorry-free):

* `NK.NUV2.RelativeLT.existsUnique_relativeLubinTate_solution` — Yoshida's Lemma 3.4: the unique
  `F` with prescribed linear part and `f' ∘ F = F^φ ∘ f` (the twisted form of Milne's Lemma 2.11);
* `NK.NUV2.RelativeLT.existsUnique_relativeLubinTate_groupLaw` — Proposition 3.5(i), series form;
* `NK.NUV2.RelativeLT.existsUnique_relativeLubinTate_formalGroupLaw` — Proposition 3.5(i), bundled
  `FormalGroup` + `FormalGroup.IsComm`;
* `NK.NUV2.RelativeLT.existsUnique_relativeLubinTate_smulLaw` — Proposition 3.5(ii), the `[θ]`-action;
* `NK.NUV2.RelativeLT.relativeLubinTate_smul_comp` — `[θ']∘[θ] = [θθ']` (Proposition 3.5(ii));
* `NK.NUV2.RelativeLT.relativeLubinTate_add_aux` and `NK.NUV2.RelativeLT.relativeLubinTate_add`
  — `[θ]+_{F_{f'}}[θ'] = [θ+θ']` (Proposition 3.5(ii); the auxiliary file is sorry-free).

Stones still to build, in order:

1. `existsUnique_relativeLubinTate_formalGroupLaw` (Prop. 3.5(i), bundled `FormalGroup` + `IsComm`);
2. the action laws `[θ'+θ] = [θ']+_{F_{f'}}[θ]`, `[θθ'] = [θ']∘[θ]` (Prop. 3.5(ii)) and
   `[θ] ∈ Hom(F_f,F_{f'})` (Prop. 3.5(iii)); `[·]_{f,f}` is an injective ring hom and `[θ]` is an
   isomorphism for `θ` a unit (Cor. 3.7);
3. `§4`: the relative Lubin–Tate levels `L'_m` over a complete unramified extension `L/K` with the
   relative Frobenius `φ`, their Galois structure `Gal(L'_m/L) ≅ Θ/…`, and the Artin map
   `θ_π : K^× → Gal(K^{LT}/K)` with `θ_π(π)|K^{ur} = Frob` and `θ_π(a)|L'_m = id` for
   `a ∈ (1+𝔭^m)·⟨π^m⟩` (Prop. 4.4, 4.7, 4.8, Cor. 4.9);
4. `§5.2`: the Coleman operator over `L` and the norm computation `N(K_x^m/K) = (1+𝔭^m)×⟨x⟩`
   (Prop. 5.10) — the absolute Coleman machinery (`NormOp.lean`, `LTGain.lean`,
   `resultant_LTpolyEis_*`) is the model;
5. `§5.3`: `N(E/K) = ⟨x⟩` for `E/L` totally ramified containing `K_x^ram` (Cor. 5.12), the
   fixed-field description `N(E_σ/K) = ⟨Art^{-1}(σ|K^{LT})⟩` (Prop. 5.14), and finally the
   **base change** `Art_{K'}(x)|K^{LT} = Art_K(N_{K'/K}(x))` (Theorem 5.15).

The base change (5.15) gives the canonicity, hence `NormInKernel` and the covering, hence
`CanonicalTowerResidue`, hence — by the theorem above — `KernelCondition` at every completion.

## The routes that would need missing library

Cup products (for the `Res`-compatibility of the local fundamental classes) and the
different/trace layer (`Ideal.different` is not in this Mathlib pin) are both absent, so the
relative-Lubin–Tate route above is the one being built.

## The route the fleet is pursuing (older note)

The only route not blocked by missing library (the trace/different layer and cup products are both
absent from Mathlib) is the *relative* Lubin–Tate theory of de Shalit / Yoshida (arXiv:math/0606108,
§3–§5), whose first stone is Yoshida's Lemma 3.4 — the twisted form of Milne's Lemma 2.11, delegated
as `NK.NUV2.RelativeLT.existsUnique_relativeLubinTate_solution` — followed by Proposition 3.5
(the relative formal group and the `[θ]`-action), §4 (the Artin map of the relative tower) and
§5 (Coleman's operator, the norm groups, and the base change `Art_{K'}(x)|K^{LT} = Art_K(N_{K'/K}(x))`). -/
theorem kernelCondition_all_of_canonicalTowerResidue (K : Type) [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hres : NK.Summary.NUV2.CanonicalTowerResidue K Q) :
    Nonempty (NK.LocalArtin.KernelCondition (Q.adicCompletion K) (SeparableClosure (Q.adicCompletion K))) :=
  NK.Summary.NUV2.kernelCondition_of_canonicalTower K Q hres

/-- **The target from a `ReciprocityLaw`** (`NK.LocalCFT.ReciprocityLaw`): the canonical,
compatible form of the norm-residue reciprocity law at every finite abelian level of `F^{ab}`.

This is the shape in which the *cohomological* route (Route C, `Submission/Work/NUV2/RouteC/`)
delivers the local reciprocity law: its final step (L8 of `RouteC/NOTES_serre_route.md`) produces
exactly `NK.LocalCFT.ReciprocityLaw (Q.adicCompletion K) (SeparableClosure …)`, namely the level
isomorphisms `Fˣ ⧸ N_{L/F}Lˣ ≃* Gal(L/F)` built from the character formula together with their
restriction compatibility.  The bridge is the proved
`NK.LocalReciprocityLubinTate.Unramified.nonempty_kernelCondition_of_reciprocityLaw`. -/
theorem kernelCondition_all_of_reciprocityLaw (K : Type) [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hlaw : NK.LocalCFT.ReciprocityLaw (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K))) :
    Nonempty (NK.LocalArtin.KernelCondition (Q.adicCompletion K)
      (SeparableClosure (Q.adicCompletion K))) :=
  NK.LocalReciprocityLubinTate.Unramified.nonempty_kernelCondition_of_reciprocityLaw hlaw

/-- **The local reciprocity law in kernel form, at every completion.**  PROVED.

Proof (the "character formula" / class-formation route, all of its steps sorry-free on disk):

* `NK.NUV2.FinalKoenig.exists_compatible_fundamentalClasses` (step L3, König's lemma): there is a
  *coherent* family of fundamental classes `u_L ∈ H²(Gal(L/F), Lˣ)` over the finite Galois levels
  `L ≤ F^{ab}`, i.e. `Inf_{L ≤ E} u_L = [E : L] • u_E`;
* `NK.NUV2.Final.levelSymbol_ker_alt` (step L7): at every finite abelian level the level symbol
  `θ_L := levelSymbol hcomm u_L` attached to a fundamental class `u_L` has kernel the norm group
  and is surjective (the cyclic case is `NK.NUV2.Final.levelSymbol_ker_cyclic`; the reduction to
  cyclic levels is `NK.NUV2.Final.exists_cyclic_quotient_of_ne_top_mul`/`…_of_isMulCommutative`);
* the compatibility of the level symbols (step L5, `NK.NUV2.RouteE.levelSymbol_restrict`) and the
  proved assembly `NK.NUV2.RouteE.nonempty_kernelCondition_of_levelMaps` (step L8) then produce
  the reciprocity law in kernel form, as packaged in
  `NK.NUV2.Final.nonempty_kernelCondition_of_L7` (`Submission/Work/NUV2/Final/Assembly.lean`).

The two reductions above (`kernelCondition_all_of_canonicalTowerResidue` for Route A and
`kernelCondition_all_of_reciprocityLaw` for the cohomological route) remain valid corollaries: the
present proof does *not* use them, it produces the conclusion directly. -/
theorem kernelCondition_all (K : Type) [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Nonempty (NK.LocalArtin.KernelCondition (Q.adicCompletion K) (SeparableClosure (Q.adicCompletion K))) :=
  NK.NUV2.Final.nonempty_kernelCondition_of_L7 (K := K) Q

end NK.NUV2
