import Mathlib
import Submission.Work.SSGRoute.Nakayama.kummerH2
import Submission.Work.SSGRoute.PT.resH2
import Submission.Work.SSGRoute.PT.AlphaTwoKummer
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The Kummer step of the corestriction wall: `μ_ℓ`-coefficients imply `Ωˣ`-coefficients

The wall of the local-arithmetic chapter (`PT.corH2_injective_ptorsion_of_dvd_index`, Milne *ADT*
(1.1b); equivalently `PT.resH2_eq_zero_of_index_nsmul_eq_zero`) is proved at the *completion* in
`PT.local_resH2_eq_zero_of_index_nsmul_eq_zero`, and its transport to `D_A` is most conveniently
carried out for **`μ_ℓ`-coefficients** — the coefficient groups of `Ω` and of the completion there
being the same finite cyclic group.  This file supplies the last formal step: the passage from
`μ_ℓ`-coefficients to the units `Ωˣ`, by the Kummer sequence

  `0 → μ_ℓ → Ωˣ →^{ℓ} Ωˣ → 0`     (`ℓ` prime, `Ω` algebraically closed, so `Ωˣ` is `ℓ`-divisible),

together with `cd_ℓ(D_A) ≤ 2` (the *proved* `PT.h3loc_decomp_subsingleton`, ruling out `H³(μ_ℓ)`) and
the commutativity of `resH2` with coefficient maps.

The content is:

* `E7Fin.H2_nsmul_eq_zero_of_exponent` — `H²(G, M)` has exponent dividing `ℓ` when `M` does;
* `E7Fin.resH2_mapH2` — `resH2` commutes with the map induced by a coefficient homomorphism (the
  `AbsoluteKummer` twin of `Work.GroupCohomology.resH2_natural`); re-proved here so that this file
  does not depend on a lane's work-in-progress module;
* **`E7Fin.resH2_eq_zero_of_mu_eq_zero`** — if `resH2` kills the index-torsion on
  `H²(D_A, μ_ℓ)`, then it kills the `ℓ`-torsion on `H²(D_A, Ωˣ)`.

The proof of the last one: `ℓ • e = 0` puts `e` in `H²(D_A, Ωˣ)[ℓ]`, which by the Kummer sequence is
the image of `H²(D_A, μ_ℓ) → H²(D_A, Ωˣ)` — this is `PT.range_mapH2_eq_ker_nsmul` applied to the
Kummer sequence of `Work.SSGRoute.Nakayama.kummer_h2_muAdd_pTorsion`, which also records
`S.pi = (·)^ℓ`.  `resH2` commutes with that map, and the `μ_ℓ`-hypothesis kills the value at any
image of a `μ_ℓ`-class of index-torsion (every `μ_ℓ`-class has exponent `ℓ`).
-/

open SSGRoute
open scoped TensorProduct

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.E7Fin

open Work.AbsoluteKummer

noncomputable section

/-- **`H²(G, M)` has exponent dividing `ℓ` when `M` does.**  A class is `H2π` of a cocycle and
`H2π` is additive, so `ℓ • x = H2π (ℓ • c)`, and `ℓ • c` vanishes pointwise. -/
theorem H2_nsmul_eq_zero_of_exponent {G : Type*} [Group G] [TopologicalSpace G]
    {M : Type*} [AddCommGroup M] [DistribMulAction G M] (ℓ : ℕ)
    (hM : ∀ m : M, ℓ • m = 0) (x : Work.AbsoluteKummer.H2 G M) : ℓ • x = 0 := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 G M).comap (Work.AbsoluteKummer.Z2 G M).subtype) x
  have h1 : ℓ • x = Work.AbsoluteKummer.H2π G M (ℓ • c) := by
    rw [show x = Work.AbsoluteKummer.H2π G M c from hc.symm, map_nsmul]
  have hc0 : (ℓ • c : ↥(Work.AbsoluteKummer.Z2 G M)) = 0 := by
    apply Subtype.ext
    show (ℓ • (c : G × G → M)) = 0
    funext p
    obtain ⟨g, h⟩ := p
    exact hM (c.1 (g, h))
  rw [h1, hc0, map_zero]

/-- **`resH2` commutes with the map induced by a coefficient homomorphism.**  The `AbsoluteKummer`
version of the restriction/coefficient-map naturality used in the Kummer argument; stated here to
keep the Kummer step independent of a lane's work-in-progress module. -/
theorem resH2_mapH2 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) {M N : Type*} [AddCommGroup M] [DistribMulAction G M]
    [AddCommGroup N] [DistribMulAction G N] (φ : M →+ N)
    (hφ : Work.GroupCohomology.IsEquivariant G φ) (x : Work.AbsoluteKummer.H2 G M) :
    Work.SSGRoute.PT.resH2 U (Work.AbsoluteKummer.mapH2 φ hφ x)
      = Work.AbsoluteKummer.mapH2 φ (fun (u : ↥U) (m : M) => hφ (u : G) m)
          (Work.SSGRoute.PT.resH2 U x) := by
  obtain ⟨c, hc⟩ := QuotientAddGroup.mk'_surjective
    ((Work.AbsoluteKummer.B2 G M).comap (Work.AbsoluteKummer.Z2 G M).subtype) x
  have hc' : x = Work.AbsoluteKummer.H2π G M c := hc.symm
  rw [hc']
  have h2 : Work.AbsoluteKummer.mapH2 (G := ↥U) φ (fun (u : ↥U) (m : M) => hφ (u : G) m)
      (Work.AbsoluteKummer.H2π ↥U M (Work.SSGRoute.PT.resZ2 U c))
      = Work.AbsoluteKummer.H2π ↥U N
          (Work.AbsoluteKummer.mapZ2 (G := ↥U) φ (fun (u : ↥U) (m : M) => hφ (u : G) m)
            (Work.SSGRoute.PT.resZ2 U c)) :=
    Work.AbsoluteKummer.mapH2_H2π (G := ↥U) φ (fun (u : ↥U) (m : M) => hφ (u : G) m)
      (Work.SSGRoute.PT.resZ2 U c)
  rw [Work.AbsoluteKummer.mapH2_H2π (G := G) φ hφ c,
    Work.SSGRoute.PT.resH2_H2π U (Work.AbsoluteKummer.mapZ2 (G := G) φ hφ c),
    Work.SSGRoute.PT.resH2_H2π (A := M) U c, h2]
  exact congrArg (Work.AbsoluteKummer.H2π ↥U N) (by
    apply Subtype.ext
    funext p
    obtain ⟨p1, p2⟩ := p
    rfl)

/-- **The Kummer transfer of the corestriction wall.**  If the restriction `resH2 U` kills the
index-torsion on the `μ_ℓ`-coefficient cohomology `H²(D_A, μ_ℓ)` (the form in which the wall is
proved at the completion), then it kills the `ℓ`-torsion on the units `H²(D_A, Ωˣ)`.

`ℓ • e = 0` makes `e` an element of the image of `H²(D_A, μ_ℓ) → H²(D_A, Ωˣ)` (exactness of the
Kummer sequence at the middle term); `resH2` commutes with that map, and the `μ_ℓ` hypothesis kills
the value at any `μ_ℓ`-class of index-torsion — and every `μ_ℓ`-class has exponent `ℓ`. -/
theorem resH2_eq_zero_of_mu_eq_zero (ℓ : ℕ) [Fact ℓ.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ ℓ) (hζK : ζ ∈ K) (A : ValuationSubring Ω)
    (hA : SSGRoute.IsFinPlace k A) (U : Subgroup ↥(SSGRoute.decomp k A))
    (hU : IsOpen (U : Set ↥(SSGRoute.decomp k A))) [U.FiniteIndex]
    [Fintype (↥(SSGRoute.decomp k A) ⧸ U)]
    (hℓ : ℓ ∣ Nat.card (↥(SSGRoute.decomp k A) ⧸ U))
    (hμ : ∀ x : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A)
        (PTembedding.MupCard.MuAdd ℓ K),
      Nat.card (↥(SSGRoute.decomp k A) ⧸ U) • x = 0 →
        Work.SSGRoute.PT.resH2 U x = 0)
    (e : Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)))
    (he : ℓ • e = 0) :
    Work.SSGRoute.PT.resH2 U e = 0 := by
  classical
  -- the Kummer sequence over `D_A`, with `μ_ℓ = MuAdd ℓ K` coefficients
  obtain ⟨S, _hiota, hpi, _⟩ :=
    Work.SSGRoute.Nakayama.kummer_h2_muAdd_pTorsion ℓ k Ω K ζ hζ hζK A hA
  have hpi' : ∀ u : Additive (Units Ω), S.pi u = ℓ • u := by
    intro u
    rw [hpi u]
    exact PTembedding.MupCard.powPi_eq_nsmul u
  -- exactness at the middle: the `ℓ`-torsion is the image of `H²(μ_ℓ)`
  have hrange := Work.SSGRoute.PT.range_mapH2_eq_ker_nsmul ℓ S hpi'
  have hemem : e ∈ (Work.SSGRoute.PT.nsmulHom ℓ
      (Work.AbsoluteKummer.H2 ↥(SSGRoute.decomp k A) (Additive (Units Ω)))).ker := by
    rw [AddMonoidHom.mem_ker, Work.SSGRoute.PT.nsmulHom_apply]
    exact he
  obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp (by rw [hrange]; exact hemem)
  -- the `μ_ℓ`-coefficient module has exponent `ℓ`, so `x` is index-torsion
  have hCoeff : ∀ m : PTembedding.MupCard.MuAdd ℓ K, ℓ • m = 0 := by
    intro m
    show Additive.ofMul ((Additive.toMul m : ↥(rootsOfUnity ℓ K)) ^ ℓ) = 0
    have hm : ((Additive.toMul m : ↥(rootsOfUnity ℓ K)) : Kˣ) ^ ℓ = 1 :=
      (mem_rootsOfUnity ℓ ((Additive.toMul m : ↥(rootsOfUnity ℓ K)) : Kˣ)).mp
        (Additive.toMul m : ↥(rootsOfUnity ℓ K)).2
    rw [show (Additive.toMul m : ↥(rootsOfUnity ℓ K)) ^ ℓ = 1 from
      Subtype.ext (by simpa using hm)]
    rfl
  have hidx : Nat.card (↥(SSGRoute.decomp k A) ⧸ U) • x = 0 := by
    obtain ⟨k', hk'⟩ := hℓ
    rw [hk', mul_nsmul, H2_nsmul_eq_zero_of_exponent ℓ hCoeff x, smul_zero]
  -- conclude by naturality of `resH2` in the coefficient module
  rw [← hx, resH2_mapH2 U S.iota S.iota_equivariant x, hμ x hidx, map_zero]

end

end Work.SSGRoute.E7Fin

/-!
## Where this sits in the wall

`PT.resH2_eq_zero_of_index_nsmul_eq_zero` (the `res`-form of Milne *ADT* (1.1b), from which
`PT.corH2_injective_ptorsion_of_dvd_index` and hence `hcor` / `hα₂` / the degree-`0`/`2` duality
`(02)` follow) reduces to `PT.corH2_injective_on_ptorsion_aux`, whose route on disk is:

1. the statement at the **completion** — *proved* (`PT.local_resH2_eq_zero_of_index_nsmul_eq_zero`);
2. its transport to `D_A` — carried out for **`μ_n`-coefficients**
   (`PT.resH2_mu_eq_zero_decomp`, the lane's current work-in-progress; the coefficient groups of `Ω`
   and of the completion are then the same finite cyclic group);
3. **this file**: from `μ_ℓ`-coefficients to the units `Ωˣ`, by the Kummer sequence
   (`E7Fin.resH2_eq_zero_of_mu_eq_zero`).

Step 3 consumes only the `μ_ℓ`-form of the statement.  Its hypothesis is stated for the coefficient
module `PTembedding.MupCard.MuAdd ℓ K = Additive (rootsOfUnity ℓ K)`; a caller holding
`PT.resH2_mu_eq_zero_decomp` for `Additive (rootsOfUnity n Ω)` reaches it along the standard
`K`-equivariant isomorphism of the two root-of-unity modules
(`PTembedding.rootsOfUnity_addEquiv_adjoinLocalEquiv` and friends), which is a small transport.
-/

/-!
## The one remaining bookkeeping step, with its recipe (delegation was refused)

To consume `PT.resH2_mu_eq_zero_decomp` — which is stated for the coefficient module
`Additive (rootsOfUnity n Ω)` — directly with `E7Fin.resH2_eq_zero_of_mu_eq_zero` (stated for
`PTembedding.MupCard.MuAdd ℓ K`), one needs the coefficient transport

```
theorem resH2_mu_coeff_transfer (hμ : ∀ x : H²(D_A, Additive (rootsOfUnity ℓ Ω)),
                                   index • x = 0 → resH2 U x = 0) :
    ∀ x : H²(D_A, MuAdd ℓ K), index • x = 0 → resH2 U x = 0
```

Two independent reviewers read this statement (path `SSGRoute/E7Fin/resH2_mu_coeff_transfer`) and
both reported it correct and non-vacuous, with the *proof* being the following five lines, whose
pieces are all on disk:

1. `PTembedding.dualMod_rootsOfUnity_equiv.muInclAddEquiv (hζ) (hζK) : MuAdd ℓ K ≃+ Additive
   (rootsOfUnity ℓ Ω)` — bijective because `ℓ` is prime and `ζ ∈ K`;
2. `PTembedding.dualMod_rootsOfUnity_equiv.muInclAddEquiv_smul` — its `Gal(Ω/k)`-equivariance
   (hence `↥(decomp k A)`-equivariance);
3. `E7Fin.resH2_mapH2` — `resH2` commutes with `mapH2` of an equivariant coefficient map;
4. `mapH2 Ψ` is additive, so `index • x = 0` transports to `index • mapH2 Ψ x = 0`; `hμ` then
   kills `mapH2 Ψ' (resH2 U x)`, and functoriality of `mapH2` on the *inverse* equivariance makes
   `mapH2 Ψ'` injective on classes of exponent dividing the index.

`request_lemma` on that path was refused three times ("the team is busy"), and the direct attempt
made in the same session did not close; two concrete obstacles were found and are recorded here so
that the next attempt starts from the right place:

* the *name* of the isomorphism (resolved): `section Incl` in
  `PTembedding/dualMod_rootsOfUnity_equiv.lean` is a **section**, not a namespace, so the
  declaration is simply `Work.SSGRoute.PTembedding.muInclAddEquiv` (and
  `PTembedding.muInclAddEquiv_smul`), taking `(p := ℓ) (K := K) hζ hζK`;
* the *instance* (identified): the action of `↥(decomp k A)` on `Additive (rootsOfUnity ℓ Ω)` is
  `PTembedding.instDistribMulActionSubgroupAddRootsOfUnity (n := ℓ) (H := SSGRoute.decomp k A)`
  (`PTembedding/kummer_ses_decomp.lean:37`);
* the *equivariance* `IsEquivariant ↥(decomp k A) Ψ.toAddMonoidHom` (DONE, see
  `E7Fin/muInclAddEquiv_equivariant.lean`, `Work.SSGRoute.E7Fin.muInclAddEquiv_isEquivariant`): built from
  `muInclAddEquiv_smul` *after* rewriting `SSGRoute.res k K (g : Ω ≃ₐ[k] Ω) = g` for
  `g : ↥(SSGRoute.decomp k A)` (`rfl`, since the `decomp`-action is *defined* through `res k K`);
  the naive `simpa` does **not** see through the instance mismatch, so the two `smul`s have to be
  identified by hand (`show`/`congrArg`), not by `simp`;
* the *injectivity tool* (located): `mapH2_symm_comp` lives in namespace `Work.SSGRoute.PT.H2Fin`
  (`PT/akH2Setup.lean`, lines 37–459), so it is `Work.SSGRoute.PT.H2Fin.mapH2_symm_comp`; its shape is
  `mapH2 Φ.symm.toAddMonoidHom hΨ (mapH2 Φ.toAddMonoidHom hΦ x) = x` for `Φ : A ≃+ B`, which is
  exactly what turns `mapH2 Ψ (resH2 U x) = 0` into `resH2 U x = 0`;
* `Ψ.apply_symm_apply`/`Ψ.symm_apply_apply` for the `AddEquiv` and `map_nsmul` for the
  index-torsion step `index • mapH2 Ψ x = mapH2 Ψ (index • x) = 0`.

A direct attempt with `PTembedding.muInclAddEquiv` and that instance elaborated the statement and
the first three steps and stopped on exactly the last three bullets, so the next attempt starts from
a resolved name, a known instance, and three known lemma-shape questions.
-/
