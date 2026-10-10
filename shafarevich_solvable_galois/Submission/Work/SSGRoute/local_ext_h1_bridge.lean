import Mathlib.FieldTheory.KrullTopology
import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.TotallySplit
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Submission.Work.SSGRoute.ext_continuous_descent
import Submission.Work.SSGRoute.ext_localUnits_iso_Q
import Submission.Work.SSGRoute.h1_coeff_transfer_localClosure
import Submission.Work.SSGRoute.h1cont_iso_H1loc
import Submission.Work.SSGRoute.localField_subfield_place_compat
import Submission.Work.SSGRoute.local_ext_h1_assembly

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/SSGRoute/DESIGN_EXT.md (the lead's Ext-core design for Poitou–Tate) + DESIGN_PT.md. Definitions: Submission/Work/SSGRoute/PTDefs.lean (namespace SSGRoute.PTExt; do NOT edit). NK.* CFT library available. Siblings run in parallel.

# E7a `local_ext_h1_bridge` — local Hilbert 90 bridge `H¹(D_A, E) ≅ Ext¹_{D_w}(E', K_wˣ)`

**Statement.** `A` is a finite place of `Ω` over the finite place `q` of `K`: `x ∈ q ↔ v_A(x) > 0` on
`𝒪_K`. Continuous `1`-cocycles `D_A → E` (with `G_k` acting through `res k K`) map to
`Ext¹_{D_w}(res E', K_wˣ)`, `w = ofFinite q`. The map is additive on cocycles, has kernel the
coboundaries, and is onto.

**Route.** This is the local copy of E1c.
- Resolve `E'` over `ℤ[D_w]`.
- Apply `Hom(·, Ω̄_Aˣ)`.
- Hilbert 90 for `K_w` and for the local extensions `L_{w'}/K_w`.
- `D_A ≃ Gal(k̄_v/k_v)`: `localGaloisEquiv`.

The only local input is Hilbert 90 over complete fields. NK has it in `Inclusion/hilbert90_cocycle`
and in the `HassePrinciple` local units files.

**Consumer.** G1 `pt_localPairing` (the Galois-side local pairing), and E9's translation.

**Size.** 1–1.5k. **Risk:** medium (place glue).

**Imports.** `Submission.Work.SSGRoute.PTDefs Submission.Work.SSGRoute.Interfaces Submission.Work.SSGRoute.DualMod.Main`.
-/


/-! ## Roadmap for E7a (findings of the first stretch of work; no statement was changed)

**What the statement is.**  `H¹(D_A, E) ≅ Ext¹_{ℤ[D_w]}(res E', K_wˣ)` with `D_A = decomp k A`
(the decomposition group of the finite place `A` of `Ω`, so `D_A ≅ G_{k_v}` for the completion
`k_v` of `k` at the place under `A`), `D_w = decompK (ofFinite q) ≅ Gal(K_w/k_v)`, `E' = E^∨(1) =
DualMod p (E ⊗ T) ≅ Hom(E, μ_p)`, and `K_w = q.adicCompletion K` (a p-adic field, `μ_p ⊆ K_w`
because `ζ ∈ K`).

**It is NOT a consequence of Hilbert 90 alone.**  The route recorded in `DESIGN_EXT.md` ("resolve
`E'` over `ℤ[D_w]`, apply `Hom(·, Ω̄_Aˣ)`, Hilbert 90") silently needs the identity
`Ext^n_{ℤ[G]}(M,N) ≅ H^n(G, Hom_ℤ(M,N))`, which is FALSE for a finite `M` (e.g. `G = 1`,
`M = 𝔽_p`, `N = ℤ_p`: the left side is `𝔽_p`, the right side is `0`).  It is valid only for a
`ℤ`-free first argument — this is why the design's *global* node E1a is stated with the syzygy `R`
of the resolution (a `ℤ`-lattice) and not with `E'` itself.

**What it is.**  A form of local Tate duality over the completion.  Using the *valid* resolution
step (`0 → R → F → E' → 0` with `F = ℤ[D_w]^r` free, `R` a `ℤ`-lattice, so that
`Hom_{ℤ[G]}(R,N) = Hom_ℤ(R,N)^G` and `Ext¹_G(R,N) ≅ H¹(G, Hom_ℤ(R,N))`):

* `Ext¹_{ℤ[D_w]}(E', K_wˣ) ≅ coker(Hom_G(F, K_wˣ) → Hom_G(R, K_wˣ))`;
* `Hom_ℤ(E', K_wˣ) = Hom_{𝔽_p}(E', μ_p) ≅ E` (double duality; `μ_p ⊆ K_w`);
consequently the statement is *equivalent* to the conjunction of

  (a) `Ext¹_{ℤ[D_w]}(M, K_wˣ) ≅ H¹(D_A, M)`  (Ext-form Kummer/local-reciprocity duality over the
      completion, for finite `𝔽_p[Gal(K/k)]`-modules `M`; for `D_w = 1` this is
      `k_vˣ/(k_vˣ)^p ≅ Hom_cont(G_{k_v}, 𝔽_p)`, i.e. Kummer + local reciprocity + double duality),
  (b) `H¹(D_A, E) ≅ H¹(D_A, E^∨(1))`  (local Tate duality in degree `1`, equal dimension).

**Status of (b) in the workspace.**  (b) is precisely the target of the local-Tate-duality lane
(`LTD_DESIGN.md`): its *formal* reduction is complete and sorry-free in `LTDDefs/` (`H0loc/1loc/2loc`,
`H1locEquivH1`, `H1locEquivH1_decomp`, `Herbrand`), and the two arithmetic inputs it needs are
  (E)  the local Euler characteristic  `dim H¹(D_A,M) = dim H⁰ + dim H² + ε·dim M`, and
  (02) duality in degrees 0 and 2      `dim H²(D_A,M) = dim H⁰(D_A, M^∨(1))`;
both are unproved, and the lane's own main files (`local_tate_duality.lean`, `local_euler_char.lean`,
`local_deg02_duality.lean`) are absent, which also leaves `hasPerfectLocalPairing_finite.lean`,
`local_tate_duality_mup_dim.lean` and `H2locEquivH2sub.lean` broken.  Delegated as
`SSGRoute/local_euler_char` and `SSGRoute/local_tate_duality_deg_zero_two` (both reviewed and
approved); (02) follows from the workspace's Tate–Nakayama machinery
(`Commons.…ArtinMap.addEquiv_tateCohomology_of_fundamental_class`), (E) from Shapiro + Herbrand
(`LTDDefs/Herbrand.lean`) + the norm-index theorem.

**Status of (a) in the workspace.**  Not available.  It needs the local reciprocity/Kummer
structure over the completion (`NK.NUV2`, `NK.LocalArtin`, `NK.CFTLib`) together with
`Ext¹ ≅ H¹(G, Hom)` for lattices (Grothendieck spectral sequence degenerating because
`Hom_ℤ(R, −)` is exact for a lattice `R`).

**Evidence that the statement is true.**  The two sides were checked to have equal order in:
`p = 3, k = ℚ, K = ℚ(ζ₃)` at the place over `3` (`D_w = ℤ/2`): both `9`; `K = ℚ(ζ₉)` at the
place over `3` (`D_w = ℤ/6`, reduced to `ℤ/2` by `Ext¹_G(M,N) ≅ Ext¹_{G/H}(M, N^H)` for `H`
acting trivially on `M`): both `9`; a completely split place (`D_w = 1`): both
`|k_vˣ/(k_vˣ)^p| = p^{d+1}|μ_p(k_v)|`; `p = 2, k = ℚ, K = ℚ(i)` at the place over `2`: both `8`;
and a non-abelian instance `K = ℚ(ζ₃, 2^{1/3})`, `D_w = S₃`, place over `3`: both `9`.  No
counterexample was found.

**Remaining work for this file.**  (i) the resolution computation of `Ext¹` in `Rep Coeff G`
(the Mathlib `Abelian.Ext` long exact sequence); (ii) `Hom_ℤ(E', K_wˣ) ≅ E`; (iii) (a) and (b)
above; (iv) the assembly: from a group isomorphism `H¹(D_A,E) ≅ Ext¹`, both sides being finite
`𝔽_p`-vector spaces killed by `p` (the cocycle side through `LTDDefs`, the `Ext` side through the
resolution), produce `β` additive on `lcCocycles`, with kernel `coboundaries`, and onto — using
`LTDDefs/Basic`'s `toClass`, `toClass_add`, `toClass_eq_zero_iff`, `toClass_surjective`.
-/


/-! ## Lane (a): `Ext¹_{ℤ[D_w]}(M, K_wˣ) ≅ H¹(D_A, M)` — status and plan

The statement of this file is equivalent to (a) + (b) (see the first roadmap note).  This is the
state of lane (a) (`H¹(k_v, M) ≅ Ext¹_{ℤ[Gal(K_w/k_v)]}(M, K_wˣ)`, `M` a finite
`𝔽_p[Gal(K/k)]`-module, `k_v` the completion of `k` under `A`, `K_w = q.adicCompletion K`).

**Proved here (permanent, usable by E1a/E1c as well).**

* `ext_shift_of_projective_presentation` — for `0 → X₁ → X₂ → X₃ → 0` in `Rep Coeff G` with `X₂`
  projective and `n ≥ 1`: `Ext^n(X₁, Y) ≅ Ext^{n+1}(X₃, Y)`.  (This is the design's
  `Ext²_G(E', X) ≅ Ext¹_G(R, X)`.)
* `ext_one_kernel_identification` — the kernel of the connecting map `Ext⁰(X₁,Y) → Ext¹(X₃,Y)` is
  exactly `AddMonoidHom.range` of the restriction `Ext⁰(X₂,Y) → Ext⁰(X₁,Y)`.
* `ext_one_iso_of_projective_presentation` — consequently
  `Ext¹(X₃, Y) ≅ Ext⁰(X₁, Y) / ker`.

So for a presentation `0 → R → F → E' → 0` with `F = ℤ[G]^r` free (which exists: `E'` is finite,
hence finitely generated over `ℤ[G]`), the `Ext` side of E7a is computed as
`Ext¹_G(E', K_wˣ) ≅ Hom_G(R, K_wˣ) / im(K_wˣ^r)` (up to `Ext⁰ ≅ Hom` via `Abelian.Ext.homEquiv₀`),
with `R` a `ℤ`-lattice (a submodule of a finitely generated free `ℤ`-module, `ℤ` a PID).

**Next lemmas, in order.**

1. `homRep` (`R.V →ₗ[Coeff] N.V` with the conjugation action `(g·f)(x) = g·(f(g⁻¹·x))`) and
   `Ext^n_{ℤ[G]}(R, N) ≅ H^n(G, Hom_ℤ(R, N))` for `R` a lattice.  Pure homological algebra: with a
   `ℤ[G]`-free resolution `P_• ↠ R`, `Hom_ℤ(P_•, N)` is a resolution of `Hom_ℤ(R,N)` by coinduced
   `G`-modules, and the coinduced modules have vanishing `H^n` (`n ≥ 1`)
   (`Work.SSGRoute.H1Dual.Vanish.isZero_groupCohomology_coindRep` is the `n ≥ 1` instance at hand).
   This is the identity the design uses in E1a; it is *not* available in Mathlib.
2. `Hom_ℤ(E', N) ≅ Hom_{𝔽_p}(E', N[p])` for `E'` killed by `p` (`N[p]` the `p`-torsion), and with
   `N = K_wˣ`, `μ_p ⊆ K_w`: `Hom_ℤ(E', K_wˣ) ≅ Hom_{𝔽_p}(E', μ_p) ≅ E` (double duality of the
   rank-one module `μ_p`).
3. The arithmetic: Kummer/reciprocity over the completion,
   `Hom_cont(G_{K_w}, μ_p) ≅ K_wˣ/(K_wˣ)^p` as `Gal(K_w/k_v)`-modules (Kummer theory over the
   p-adic field `K_w`), and the comparison of `H¹(D_A, M)` with the finite-level data via
   inflation–restriction.  Available raw material: `NK.LocalAnabelian.Kummer` (Kummer
   correspondence over local fields), `NK.NUV2.LC` (`localInvariant`, `localLevelSystem`,
   `natCard_groupCohomology_two_units_local_eq_finrank`), `NK.LocalArtin.KernelCondition` (local
   reciprocity at `Q.adicCompletion K`).
4. Assembly: from `Nonempty (H1loc p k Ω K E (decomp k A) ≃+ Ext¹(...))` produce `β` via
   `Work.SSGRoute.toClass` / `toClass_add` / `toClass_eq_zero_iff` / `toClass_surjective`
   (`LTDDefs/Basic`): send a locally constant cocycle to its class followed by the isomorphism,
   send everything else to `0`.

**Queued for the fleet (reviewed and approved, refused only because the team is busy at the
moment).** `SSGRoute/local_euler_char` (E) and `SSGRoute/local_tate_duality_deg_zero_two` (02) —
the two arithmetic inputs needed for (b).
-/


/-! ## ROUTE (v2, current): dualise into the DIVISIBLE `Ω̄ˣ`, then descend.

The old `(a)+(b)` decomposition (Ext-vs-H¹ for finite coefficients + local Tate duality in degree 1
`H¹(D_A,E) ≅ H¹(D_A,E^∨(1))`) is superseded: local Tate duality needs Milne ADT I.1.8 (class
formations) which is *not* in the workspace, and lane `PT/localTatePairing_deg02` is stuck there.
The route below needs **no** local Tate duality and no local reciprocity: only Hilbert 90 and the
`Ext`-vs-cohomology dictionary with a *divisible* coefficient module.

**Setting.**  `A` is a finite place of `Ω` over the finite place `q` of `K`.  Let
`𝔭 := ` the prime of `k` under `A`, `κ := NK.FrobeniusBridge.localField ⟨A,hA⟩ = adicCompletion k 𝔭`
(the completion `k_v` of `k`), `κ̄ := localClosure ⟨A,hA⟩ = SeparableClosure κ`.  Then

* `NK.FrobeniusBridge.localGaloisEquiv ⟨A,hA⟩ : ↥(decomp k A) ≃* Gal(κ̄/κ)`,
* `D_w = decompK (ofFinite q)` and `K_w = Place.localField K (ofFinite q)` is (a copy of) an
  intermediate field `K ⊆ κ̄`, finite Galois over `κ`, with `Gal(K_w/κ) ≅ D_w` and
  `(κ̄ˣ)^{Gal(κ̄/K_w)} = K_wˣ` (infinite Galois correspondence),
* `κ̄ˣ` is **divisible** (κ̄ is a separable closure of a char-0 field, hence algebraically closed).

**Chain (all steps are pure algebra + Hilbert 90):**

1. `Ext¹_{D_w}(res_{D_w} E', K_wˣ) ≅ Ext¹_{G}(E', κ̄ˣ)`, `G := Gal(κ̄/κ)`, by the degree-1 descent
   (`SSGRoute/ext_local_descent`, `H¹(Gal(κ̄/K_w), κ̄ˣ) = 0` is Hilbert 90; the higher `H^q` do
   *not* vanish, so degree 1 is essential) plus `K_wˣ = (κ̄ˣ)^{Gal(κ̄/K_w)}` and
   `Rep.res`/`localGaloisEquiv` for the group change (place glue).
2. `Ext¹_G(E', κ̄ˣ) ≅ Ext¹_G(ℤ, Hom_ℤ(E', κ̄ˣ))` by `SSGRoute/ext_one_iso_divisible_cohomology`
   (`κ̄ˣ` divisible ⟹ `Hom_ℤ(-,κ̄ˣ)` exact; Shapiro kills `H¹(G, Hom_ℤ(ℤ[G]^r,κ̄ˣ))`).
3. `Hom_ℤ(E', κ̄ˣ) ≅ E` as `Rep Coeff G` by `SSGRoute/hom_dualMod_local_units`
   (`E' = DualMod p (E⊗T)`, `κ̄ˣ[p] = μ_p` since `p` is invertible in κ̄, double duality, and the
   twist cancellation `T ⊗ μ_p ≅ 𝔽_p`).
4. `Ext¹_G(ℤ, infl E) ≅ H1loc(D_A, E)`: the abstract-vs-continuous comparison for the **finite**
   coefficient module `E` (every crossed homomorphism `G → E` with `E` finite is locally constant,
   since `E` finite makes every finite-index subgroup open) together with
   `H1locEquivH1_decomp`.
5. Assembly: `Work.SSGRoute.exists_beta_of_addEquiv`
   (`Submission/Work/SSGRoute/local_ext_h1_assembly.lean`) turns the resulting additive
   equivalence `H1loc p k Ω K E (decomp k A) ≃+ Ext¹_{D_w}(res E', K_wˣ)` into the `β` demanded by
   the statement.

**Status.**  Pieces 2, 3 delegated as `SSGRoute/ext_one_iso_divisible_cohomology` and
`SSGRoute/hom_dualMod_local_units`; piece 1's abstract core delegated as
`SSGRoute/ext_local_descent`.  Still to do: the place glue of 1 (identify `K_wˣ` with
`(κ̄ˣ)^{Gal(κ̄/K_w)}` and move the `Rep` along `localGaloisEquiv`), piece 4, and the assembly.


**The place glue of step 1 (the only genuinely arithmetic-looking piece left).**  Nothing here needs
reciprocity: it is Galois theory plus the local-field bookkeeping of `NK`.

* `A` a finite place of `Ω` over `k` gives `A' := ⟨A, hA⟩ : NK.FrobeniusBridge.FinitePlaceOf k Ω`.
  Then `L₀ := NK.FrobeniusBridge.localField A'` is `k_v = adicCompletion k 𝔭` (`𝔭` = prime of `k`
  under `A`) and `M₀ := NK.FrobeniusBridge.localClosure A'` is its separable closure; both have
  `char 0`, so `M₀` is algebraically closed and `M₀ˣ` divisible.  The group isomorphism is
  `NK.FrobeniusBridge.localGaloisEquiv A' : ↥(decomp k A) ≃* Gal(M₀/L₀)`.
* `K_w := Place.localField K (Place.ofFinite q)` is an `L₀`-algebra (`Commons`'
  `adicCompletionMap` for the prime `q` over `𝔭`, which is what `hAq` records: `x ∈ q ↔
  A.valuation (x : Ω) < 1`).  Since `M₀` is a separable closure of `L₀`, there is an
  `L₀`-embedding `K_w ↪ M₀`; its image is `K : IntermediateField L₀ M₀` with
  `Nonempty (↥K ≃ₐ[L₀] K_w)`, whence `FiniteDimensional L₀ K` and `IsGalois L₀ K` by transport, and
  `ζ` has a transportable copy in `K`.
* `Gal(K_w/L₀) ≅ ↥(decompK (ofFinite q))`: both are the image of `Gal(K/k)`-stabiliser of `w`; in
  NK this is the `localAutHom`/`localGaloisEquiv` pair (`localAut w σ` is the automorphism of
  `K_w` induced by `σ`, and it is bijective because `K_w/L₀` is Galois).
* Consequently `localUnitsK (k := k) (ofFinite q) ≅ Rep.res e (modRep (K ≃ₐ[L₀] K) (Additive
  (Units ↥K)))` for the group isomorphism `e` above — an isomorphism of `Rep`s over the *same*
  group `↥(decompK w)` whose carrier is `K_wˣ` on both sides (NK's `localUnitsEquiv` action is
  `localAut`-by-definition), so this transport is `rfl`-level once the types are identified.
* Then `SSGRoute/ext_local_descent` at `(L₀, M₀, K)` (with `X := E'` inflated along
  `Gal(M₀/L₀) ↠ Gal(K/L₀)`) gives `Ext¹_{Gal(M₀/L₀)}(infl E', M₀ˣ) ≅ Ext¹_{D_w}(res E', K_wˣ)`,
  using `Kˣ = (M₀ˣ)^{Gal(M₀/K)}` (infinite Galois correspondence) and Hilbert 90.
* Finally `SSGRoute/ext_res_mulEquiv` moves `Ext¹_{Gal(M₀/L₀)}` to `Ext¹_{↥(decomp k A)}` along
  `localGaloisEquiv`.

**Assembly order in this file** (once the pieces exist):
`H1loc(D_A,E) ≃+ extH (decompRep …) 1` [step 4, reversed] `≃+ Ext¹_G(infl E, M₀ˣ)` [steps 2–3
reversed] `≃+ Ext¹_{D_w}(res E', K_wˣ)` [step 1].  Then `exists_beta_of_addEquiv`.


/-! ## ROUTE (v3): why v2 fails — ABSTRACT `Ext` is not CONTINUOUS cohomology.

Route v2 above is **dead**, and the reason is worth recording in full because the same trap sits
under the global siblings `E1a`/`E1c` and under any use of `SSGRoute.PTExt.extH` at a level whose
group is *infinite*.

`SSGRoute.PTExt.extH A 1 = Ext¹_{ℤ[G]}(ℤ, A)` with `G` the plain abstract group and `A : Rep Coeff G`.
For `G` an infinite profinite group this is **abstract** group cohomology
`Der(G,A)/Prin`, and it is *strictly bigger* than the continuous cohomology that
`H1loc`/`Work.AbsoluteKummer.H1` compute:

* `Hom_grp(Ĝ, C₂) ⊋ Hom_cont(Ĝ, C₂)` for `Ĝ = ∏_n C₂`: every subgroup of finite index of a compact
  group need **not** be open (a finite-index subgroup need not even be closed), so the ultrafilter
  homomorphism `x ↦ lim_U x_n : ∏_n C₂ → C₂` is a group homomorphism with non-open (hence
  non-continuous) kernel of index `2`.  Every continuous hom is finite-dimensional, so the abstract
  `Hom` is uncountable while the continuous one is countable.
* Concretely the model bridge `H1loc p k Ω K E (decomp k A) ≃+ extH (decompRep …) 1` was
  **refuted** for the admissible instance `k = ℚ`, `A = ⊤`, `E = 𝔽₂`: the right side contains
  `Hom_grp(G_ℚ,𝔽₂)`, which is uncountable, while the left side is countable.
  (`h1loc_iso_extH` was declared FALSE by its prover for exactly this reason.)
* Consequently the "descent" `Ext¹_G(res X, Mˣ) ≅ Ext¹_{G/H}(X, Kˣ)` (delegated as
  `SSGRoute/ext_local_descent`) is **also FALSE** in the abstract world: with `L = ℚ`,
  `M = ℚ̄`, `K = L`, `X = 𝔽₂`, the left side is (via the divisible-coefficient dictionary)
  `Ext¹_{G_ℚ}(ℤ, μ₂) = Hom_grp(G_ℚ, C₂)`, uncountable, while the right side is
  `Ext¹_1(𝔽₂, ℚˣ) = ℚˣ/(ℚˣ)²`.  The *continuous* descent is a different (true) statement.

**What that means.**  The statement of this file relates two objects of *different flavours*:
`Ext¹_{D_w}(res E', K_wˣ)` is `Ext` over the **finite** group `D_w = decompK (ofFinite q)` — where
abstract and continuous coincide and where `Rep Coeff`-`Ext` is the right theory — while the left
side `H1loc(D_A,E)` is **continuous** cohomology of the profinite group `D_A ≅ G_{k_v}`.  A correct
route must therefore stay inside the continuous theory (`Work.AbsoluteKummer.H1`, whose
`Coind`/Shapiro calculus is developed in `Submission/Work/SSGRoute/ext_h1_bridge.lean` for the
global case) and may only use `Rep`-`Ext` over *finite* groups.

**The two halves that a correct proof needs.**

* *Continuous Kummer over `K_w`*: `H¹_cont(G_{K_w}, E) = Hom_cont(G_{K_w}, E) = E ⊗ (K_wˣ/(K_wˣ)^p)`
  as `D_w`-modules.  **Available**: `Work.SSGRoute.kummer_reciprocity_general` (proved) gives
  `kˣ/(kˣ)^p ≅ lcHoms p Gal(K'/k)` for `[IsSepClosure k K']`, in particular over `k = K_w`; and
  `Work.AbsoluteKummer` has the continuous-cochain `H¹` and its Shapiro/coind calculus.
* *Finite-level Tate duality over `K_w/k_v`*: `H¹(D_w,E) ≅ H¹(D_w,E^∨(1))` and
  `Ĥ^i(D_w, K_wˣ)` for the finite Galois extension `K_w/k_v` — i.e. Tate's theorem for the class
  formation `(D_w, K_wˣ)`; the workspace has the local reciprocity/invariant machinery in
  `NK.LocalArtin`, `NK.NUV2.LC`, `NK.CFTLib` but not this comparison in the needed form.
* *The identification of the two extension classes*: both
  `Ext¹_{D_w}(res E', K_wˣ)` and `H¹_cont(D_A,E)` sit in
  `0 → H¹(D_w,E^{∨(1)}) → · → (E ⊗ K_wˣ/(K_wˣ)^p)^{D_w} → 0`
  (for the left one via the resolution of `E'` over `ℤ[D_w]`, for the right one via the
  inflation–restriction 5-term sequence), and one must show the two extensions agree.  This is the
  genuine arithmetic content of E7a; no cheap route (resolution into `Ω̄ˣ`, dimension count) avoids
  it, because the naive comparisons use abstract `Ext` over an infinite group.


**Refined reduction of the crux (v3 cont.).**  With `N := K_wˣ` (NOT divisible), `M := E'`
(finite, killed by `p`), `G := D_w` finite, a presentation `0 → R → F → E' → 0` with `F = ℤ[G]^r`
free gives, using that `R` is a `ℤ`-lattice,

  `Ext¹_G(E',N) ≅ coker(Hom_G(F,N) → Hom_G(R,N)) = H⁰(Hom_ℤ(R,N)) ⧸ im(H⁰(Hom_ℤ(F,N)))`,

and the (non-short) exact sequence `0 → Hom_ℤ(E',N) → Hom_ℤ(F,N) → Hom_ℤ(R,N) →
Ext¹_ℤ(E',N) → 0` has `Hom_ℤ(E',N) = Hom_{𝔽_p}(E', μ_p) ≅ E` and
`Ext¹_ℤ(E',N) = Hom_ℤ(E', N/pN)`, so both sides of E7a sit in

  `0 → H¹(D_w, E) → · → (E ⊗ K_wˣ/(K_wˣ)^p)^{D_w}  → H²(D_w, E)`,

the left-hand group `H¹_cont(D_A, E)` through the inflation–restriction five-term sequence (with
`H¹_cont(G_{K_w}, E) ≅ E ⊗ K_wˣ/(K_wˣ)^p` from continuous Kummer,
`Work.SSGRoute.kummer_reciprocity_general`) and `Ext¹_{D_w}(E', K_wˣ)` through the presentation
above.  Proving E7a therefore amounts to identifying these two extensions; when the transgression
`(E ⊗ K_wˣ/(K_wˣ)^p)^{D_w} → H²(D_w,E)` happens to vanish both are even isomorphic to
`Hom_{D_w}(E', K_wˣ/(K_wˣ)^p)`, which is what makes the equality of orders in the examples look
"free" — it is not, it is Tate's local duality for the finite extension `K_w/k_v` (class formation
`(D_w, K_wˣ)`), on top of continuous Kummer.


**State of play (end of the session that produced v3).**  Proved and importable:
`SSGRoute/hom_dualMod_local_units` (`Hom_ℤ(DualMod p (E⊗T), Ωˣ) ≅ E` as `Rep`s, the local twin of
the `E1a/2` node), `SSGRoute/ext_res_mulEquiv` (group change along a group isomorphism on `Ext¹`),
`SSGRoute/extH_congr` (`Ext`-cohomology is invariant under an isomorphism of the coefficient
module), plus everything banked in this file.  Refuted (both by their provers, both for the same
abstract-vs-continuous reason): `SSGRoute/h1loc_iso_extH` (the model bridge) and
`SSGRoute/ext_local_descent` (the descent).  `SSGRoute/ext_one_iso_divisible_cohomology`
(`Ext¹_G(M,N) ≅ H¹(G, Hom_ℤ(M,N))` for `N` divisible) is true and remains useful.

The lead reports `Work.SSGRoute.extH_groupCohomology_iso` (`Hⁿ(G,A) ≃+ Extⁿ_G(ℤ,A)`) PROVED — that
is the *abstract* `Work.GroupCohomology` dictionary, so it does **not** repair the abstract-vs-
continuous gap recorded above; it is the correct tool only over finite groups (e.g. `D_w`).

**To finish E7a one still has to** (i) identify `Ext¹_{D_w}(res E', K_wˣ)` with the cokernel
`H⁰(Hom_ℤ(R,K_wˣ))/im(H⁰(Hom_ℤ(F,K_wˣ)))` (available above, `ext_one_iso_of_projective_presentation`),
(ii) compute `H¹_cont(D_A, E)` from the continuous inflation–restriction sequence with the
continuous Kummer input `H¹_cont(G_{K_w}, E) ≅ E ⊗ K_wˣ/(K_wˣ)^p`
(`Work.SSGRoute.kummer_reciprocity_general`, proved, over `k = K_w`, plus the `Work.AbsoluteKummer`
cochain calculus), and (iii) match the two extension classes using **Tate's local duality for the
finite extension `K_w/k_v`** (class formation `(D_w, K_wˣ)`, currently available only in fragments:
`NK.LocalArtin`, `NK.NUV2.LC`, `NK.CFTLib`).  Step (iii) is the genuine missing theorem; its
finite-halves are delegated as `SSGRoute/tate_duality_finiteLevel` (Tate duality for the
*finite* group `D_w = Gal(K_w/k_v)`, classical, no Milne I.1.8 needed) and its unbounded
companion is the lead's `PT/localTatePairing_deg02` lane; **that finite-level statement was
itself refuted by its prover** (concrete counterexample: `k = ℚ`, `K = ℚ(ζ₈)`, `p = 2`,
`D_w = (ℤ/2)²`, `E = 𝔽₂³` with a unipotent `D_w`-action gives `|H¹(D_w,E)| = 8` but
`|H¹(D_w,E^∨(1))| = 2`, checked by `#eval`), so **the correct duality is NOT a finite-level
statement**: it is Tate duality for the *full* profinite group `G_{k_v}` with the divisible class
module `k̄_v^×` (Milne ADT I.2.1/I.2.3), i.e. exactly the lead's unbounded-level lane.  The
correct route for E7a is therefore route v2 *carried out in the continuous
(`Work.AbsoluteKummer.H1`) framework*, where `k̄_v^×` is divisible, `(k̄_v^×)^{Gal(k̄_v/K_w)} = K_wˣ`,
`H¹_cont(G_{K_w}, k̄_v^×) = 0` (Hilbert 90) and `Hom_ℤ(E^∨(1), k̄_v^×) = E`; the abstract
`Rep`-`Ext` over the infinite group `Gal(k̄_v/k_v)` must be replaced everywhere by the continuous
`H¹_cont`, and the finite-group `Ext¹_{D_w}` of the statement enters only through a presentation of
`E'` over `ℤ[D_w]` (where `D_w` is finite), together with the fact that the continuous cohomology of
`D_A` restricts to the finite levels `Gal(K_w/k_v)`.  This is a substantial but *self-contained*
programme: it needs (1) the continuous-cochain `Ext`/Shapiro calculus over profinite groups
(`ext_h1_bridge.lean`'s `CoindU`/`coinduction` material), (2) the locconst description of
`H¹_cont(H, E) = Hom_cont(H,E) = E ⊗ K_wˣ/(K_wˣ)^p` (continuous Kummer,
`Work.SSGRoute.kummer_reciprocity_general`), (3) Milne ADT I.2.1 for `(G_{k_v}, k̄_v^×)` (the lead's
lane), and (4) the place glue of the previous block.

**Pieces that survive v2 and are worth keeping** (all true, all usable):
`SSGRoute/ext_one_iso_divisible_cohomology` (`Ext¹_G(M,N) ≅ H¹(G,Hom_ℤ(M,N))` for `N` divisible,
`M` arbitrary), `SSGRoute/hom_dualMod_local_units` (PROVED: `Hom_ℤ(E^∨(1), Ωˣ) ≅ E`),
`SSGRoute/ext_res_mulEquiv` (PROVED), `SSGRoute/extH_congr`, plus the banked
`ext_playing`-calculus lemmas below.
-/


**BOTTOM LINE for E7a (for whoever picks this up).**  E7a is *not* independent glue: after three
refutations (`h1loc_iso_extH`, `ext_local_descent`, `tate_duality_finiteLevel`) the surviving
mathematics is Milne, *Arithmetic Duality Theorems*, I.2.1/I.2.3 for the **full** local class
formation `(G_{k_v}, k̄_v^×)` — the same unbounded-level input the lead's
`Submission/Work/SSGRoute/PT/localTatePairing_deg02` lane is stuck on — together with (i) the
*continuous* (`Work.AbsoluteKummer`-style) descent fixing `K_wˣ = (k̄_v^×)^{Gal(k̄_v/K_w)}` and
(ii) the place glue identifying `K_w = Place.localField K (Place.ofFinite q)` with the
`L₀`-subfield `k̄_v^{Gal(k̄_v/K_w)}` and `D_w = ↥(decompK (ofFinite q))` with
`Gal(K_w/k_v) = Gal(k̄_v/k_v)/Gal(k̄_v/K_w)`.  Do **not** attack E7a before the class-formation
duality is available; do **not** re-derive it from `Rep`-`Ext` over an infinite group.


**The one statement to delegate next (route v2-cont, continuous descent).**  All three refuted
pieces failed for the *same* reason (abstract `Rep`-`Ext` over an infinite group); the true
statement is the continuous one, and it is expressible in the workspace's continuous vocabulary
(`Work.AbsoluteKummer.H1`, imported via `Submission.Work.SSGRoute.LTDDefs.H1loc_iso_H1cont`):

> Let `L` be a field of characteristic `0`, `M` a separable closure of `L`, `K ⊆ M` a finite
> Galois intermediate field with `G = Gal(M/L)` and `H = Gal(M/K)`, and let `X` be a finite
> `𝔽_p[Gal(K/L)]`-module.  Then
> `Ext¹_{ℤ[Gal(K/L)]}(X, Kˣ) ≅ H¹_cont(G, Hom_ℤ(infl X, Mˣ))`,
> where `Hom_ℤ(infl X, Mˣ)` carries the conjugation action and its `H`-invariants are
> `Hom_ℤ(X, Kˣ) = X^∨(1)`, `H¹_cont(H, Mˣ) = 0` (Hilbert 90) and `H¹_cont(G, Hom_ℤ(ℤ[G]^r, Mˣ)) = 0`
> (Shapiro).

This is the honest replacement of `SSGRoute/ext_local_descent`: the right-hand side is the
*continuous* `H¹`, and the finite-group `Ext` on the left is legitimate because `Gal(K/L)` is
finite.  Two warnings for its prover: (1) the analogous abstract statement is FALSE (see above);
(2) `Kˣ` and `Mˣ` are *not* divisible/`ℤ`-injective, so `Ext¹ ≅ H¹(Hom)` is unavailable and the
argument must go through continuous cochains (`Work.AbsoluteKummer`), Shapiro/coind
(`ext_h1_bridge.lean`'s `CoindU`, `Subsingleton` of `H1` for coinduced modules), and the
inflation map `H¹_cont(G, Hom_ℤ(infl X, Mˣ)) → H¹_cont(H, …)`.


**Verified assembly (checked in `_e7a_asm.lean`, which compiles).**  With
`hφ : Nonempty (H1loc p k Ω K E (decomp k A) ≃+ Ext¹_{D_w}(res E', K_wˣ))` the body of
`local_ext_h1_bridge` is discharged by the *exact* term

  `obtain ⟨φ⟩ := hφ; exact exists_beta_of_addEquiv p k Ω K E A _ φ`

(`Submission/Work/SSGRoute/local_ext_h1_assembly.lean`).  So nothing else has to be built in *this*
file: the whole content of E7a is the single additive equivalence `hφ`, and `hφ` is the local
Tate/Kummer duality of the preceding blocks.


**NOTE TO THE LEAD (exact mismatch with `local_duality_ext_in`, requested rather than worked
around).**  Per your routing: E7a's whole content is the single iso
`hφ : H1loc p k Ω K E (decomp k A) ≃+ Ext¹_{D_w}(res E', K_wˣ)` (`D_w = decompK (Place.ofFinite q)`,
`E' = DualMod p (E ⊗ T)`), and `exists_beta_of_addEquiv` closes the target from it (verified,
`_e7a_asm.lean`).  `Work.SSGRoute.local_duality_ext_in` supplies clauses (i)/(ii) for the `levelPair`
between `Ext¹_{D_w}(M, K_wˣ)` (a *finite* group `D_w`, so abstract = continuous there) and level
`H¹`s `extH (Rep.res f (Rep.res (decompK w).subtype M)) 1`, i.e. `H¹` of *finite* subgroups of
`Gal(L/k)` with *finite* coefficients; `local_duality_ext_extH_finite` gives finiteness of those.

The mismatch is in the **module and the group on the `H¹` side**:

* the target's left side is `H1loc p k Ω K E (decomp k A)`: the **continuous** `H¹` of the
  **profinite** group `D_A ≅ G_{k_v}` with coefficients `E`, whereas clause (i)/(ii) pair with
  `H¹` of *finite* groups `D_{w'}` (levels `L ⊇ K`) with coefficients `M`;
* so (i)+(ii) yield `Ext¹_{D_w}(M, K_wˣ) ≅ (level-`H¹` space)^∨`, and what is still needed is the
  comparison `H1loc(D_A, E) ≅ (level-`H¹` space)^∨`, i.e. local Tate duality *in the `H¹` form*
  `H¹_cont(G_{k_v}, E) ≅ H¹_cont(G_{k_v}, E^∨(1))^∨` (unbounded level), together with the
  identification of the coefficient module: the pairing's `M` must be instantiated at
  `M = E' = DualMod p (E ⊗ T)`, so that the dual functional space is the *twist* of `E`'s `H¹`.
  Concretely the two things that have to line up are (a) `M = E^∨(1)` vs `E` (the Tate twist) and
  (b) `H¹` at the full profinite `D_A` vs at finite levels `w'`.
  An `Ext`-side statement that would plug straight into `exists_beta_of_addEquiv` is
  `Nonempty (H1loc p k Ω K E (decomp k A) ≃+ Ext¹_{D_w}(res E', K_wˣ))`; anything phrased purely
  with `levelPair` + `extH` over finite `D_{w'}` needs the extra comparison above.

**Warnings.**
* `Ext^n_G(M,N) ≅ H^n(G,Hom_ℤ(M,N))` is **false** for `n ≥ 2` even with `N` divisible
  (`H²(ℤ/2,ℂˣ) ≅ ℤ/2`) and **false** for `n = 1` without divisibility (`G = 1`, `M = ℤ/2`,
  `N = ℤ_p`): both hypotheses matter.  `Ext^n_G(R,N) ≅ H^n(G,Hom_ℤ(R,N))` for `R` a `ℤ`-lattice
  (sibling node `E1a/1`) is a *different* statement.
* The statement's `Ext` is over `D_w` (finite), so `SSGRoute.PTExt.extH`'s abstract `Rep`-cohomology
  is the right theory there; do **not** try to use it over the profinite `D_A` with infinite
  coefficients (there `H¹` is `Hom_abs ≠ 0`; the lead's `PT/localTatePairing_deg02` docstring warns
  about exactly this).
-/

namespace Work.SSGRoute

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option autoImplicit false

open SSGRoute.PTExt CategoryTheory
open scoped TensorProduct


/-! ## Lane (a), first lemma: the dimension shift for `Ext` along a presentation

This is the "resolve `E'` over `ℤ[D_w]`" step of the `Ext` core, in the form needed here: for a
short exact sequence `0 → R → F → E' → 0` of `Rep Coeff G` with `F` projective (e.g. free), it
turns `Ext^{n+1}(E', Y)` into `Ext^n(R, Y)`.  It is the `n ≥ 1` part of the long exact sequence,
where the two neighbouring `Ext`-groups of `F` vanish by projectivity. -/




/-- **Lane (a), step (2a): `Hom_ℤ(E', N) ≅ Hom_{𝔽_p}(E', N[p])`, first half.**

Let `M` be a `Coeff = ℤ`-module of a `Rep Coeff G` that is killed by `p` (which is the case for
`M = E' = DualMod p (E ⊗ T)`, an `𝔽_p`-module).  Then every `G`-equivariant `ℤ`-linear map
`M ⟶ N` takes values in the `p`-torsion of `N`: for the intended `N = K_wˣ` this says that
`Hom_ℤ(E', K_wˣ) = Hom_{𝔽_p}(E', K_wˣ[p]) = Hom_{𝔽_p}(E', μ_p)`, whence (by the rank-one double
duality of `μ_p`, and `E' ≅ Hom_{𝔽_p}(E, μ_p)`) the identification `Hom_ℤ(E', K_wˣ) ≅ E` used in
the design's route. -/
theorem map_intSmul_eq_zero_of_pTorsion (p : ℕ) {G : Type} [Group G]
    {M N : Rep.{0} SSGRoute.PTExt.Coeff G}
    (hM : ∀ m : M.V, (p : ℤ) • m = 0) (φ : M ⟶ N) (m : M.V) :
    (p : ℤ) • (φ.hom m) = 0 := by
  have h := AddMonoidHom.map_zsmul φ.hom.toAddMonoidHom (p : ℤ) m
  rw [hM m, map_zero] at h
  exact h.symm


/-- **Lane (a), step (2c): double duality, with the twist action.**

For a finite `𝔽_p[G]`-module `F` there is a `G`-equivariant additive isomorphism
`F ≃+ DualMod p (DualMod p F)`, realised by the *canonical* evaluation `x ↦ (φ ↦ φ x)` — so it is
natural and keeps the `G`-action, unlike an arbitrary isomorphism obtained from `finrank` equality.
Applied to `F = E` this is the `Hom_{𝔽_p}(Hom_{𝔽_p}(E, μ_p), μ_p) ≅ E` step of the design's route
to `Hom_ℤ(E', K_wˣ) ≅ E` (with `E' = DualMod p (E ⊗ T) ≅ Hom_{𝔽_p}(E, μ_p)`).

The proof is the classical one: the canonical evaluation has trivial kernel
(`ker eval = ⊤.dualCoannihilator = ⊥`, using that a module over the field `ZMod p` is projective),
and injectivity plus equal `finrank` (`Subspace.dual_finrank_eq`, twice) gives bijectivity; the
equivariance is `Module.Dual.eval_apply` against the contragredient action `DualMod.dualSMul_apply`. -/
theorem doubleDual_addEquiv (p : ℕ) [Fact p.Prime] {G : Type} [Group G] {F : Type}
    [AddCommGroup F] [Module (ZMod p) F] [DistribMulAction G F] [SMulCommClass G (ZMod p) F]
    [Finite F] [FiniteDimensional (ZMod p) F] :
    ∃ e : F ≃+ DualMod p (DualMod p F), ∀ (g : G) (x : F), e (g • x) = g • e x := by
  have hinj : Function.Injective (Module.Dual.eval (ZMod p) F) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    rw [Submodule.mem_bot]
    have hmem : x ∈ (⊤ : Submodule (ZMod p) (DualMod p F)).dualCoannihilator := by
      rw [Submodule.mem_dualCoannihilator]
      intro φ _
      have h := DFunLike.congr_fun hx φ
      rwa [Module.Dual.eval_apply, LinearMap.zero_apply] at h
    rwa [Submodule.dualCoannihilator_top, Submodule.mem_bot] at hmem
  have hdim : Module.finrank (ZMod p) F = Module.finrank (ZMod p) (DualMod p (DualMod p F)) := by
    rw [Subspace.dual_finrank_eq (K := ZMod p) (V := DualMod p F),
      Subspace.dual_finrank_eq (K := ZMod p) (V := F)]
  have hbij : Function.Bijective (Module.Dual.eval (ZMod p) F) :=
    ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hinj⟩
  have hev : ∀ (g : G) (x : F),
      Module.Dual.eval (ZMod p) F (g • x) = g • (Module.Dual.eval (ZMod p) F x) := by
    intro g x
    ext φ
    simp only [Module.Dual.eval_apply, DualMod.dualSMul_apply, inv_inv]
  exact ⟨(LinearEquiv.ofBijective _ hbij).toAddEquiv, hev⟩


/-- **Lane (a)/(iii), the sub-object identification `K_wˣ[p] = μ_p`.**

Let `ζ ∈ K` be a primitive `p`-th root of unity (`hζ`).  Then the `p`-torsion of the local field
`K_w` — equivalently of `K_wˣ`, since a unit `u` with `u ^ p = 1` is a `p`-torsion element —
consists exactly of the powers of the image of `ζ`:

  `u ^ p = 1 ↔ ∃ i, (algebraMap K K_w ζ) ^ i = u`.

So `K_wˣ[p]` is cyclic of order `p`, with the *specified* generator `algebraMap K K_w ζ`: this is the
`K_wˣ[p] ≅ μ_p` identification that turns `Hom_ℤ(E', K_wˣ) = Hom_{𝔽_p}(E', K_wˣ[p])` into
`Hom_{𝔽_p}(E', μ_p)`.  Because the generator is specified, the `Gal(K_w/k_v)`-action on `K_wˣ[p]`
is determined by its value on `algebraMap K K_w ζ` — the cyclotomic character, by
`NK.HassePrinciple.localAut_algebraMap` — which is what the `IsCyclotomicDual` hypothesis `hT`
pins down for `T`. -/
theorem pow_eq_one_iff_powers_local (p : ℕ) [Fact p.Prime] {K : Type*} [Field K] [NumberField K]
    (w : NK.GlobalCFT.Place K) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (u : NK.GlobalCFT.Place.localField K w) :
    u ^ p = 1 ↔ ∃ i : ℕ, (algebraMap K (NK.GlobalCFT.Place.localField K w) ζ) ^ i = u := by
  constructor
  · intro hu
    obtain ⟨i, -, hi⟩ :=
      (hζ.map_of_injective (algebraMap K (NK.GlobalCFT.Place.localField K w)).injective)
        |>.eq_pow_of_pow_eq_one hu
    exact ⟨i, hi⟩
  · rintro ⟨i, rfl⟩
    rw [← pow_mul, mul_comm, pow_mul, ← map_pow, hζ.pow_eq_one, map_one, one_pow]




/-- **Lane (a)/(iii), the unit-level `K_wˣ[p] = μ_p`.**

The units form of `pow_eq_one_iff_powers_local`: for `ζu : Kˣ` a primitive `p`-th root of unity, the
`p`-torsion of `K_wˣ` is exactly the cyclic group generated by the image of `ζu`.  Together with
`localAut_algebraMap_zeta_pow` this exhibits `K_wˣ[p] ≅ μ_p` as a `Gal(K_w/k_v)`-module — the
*name* of the generator is what pins the action — the identification used in
`Hom_ℤ(E', K_wˣ) = Hom_{𝔽_p}(E', K_wˣ[p]) = Hom_{𝔽_p}(E', μ_p)`.

Formal note (the shapes that had to be pinned): the coercion of a power is already reduced, so
`Units.val_pow_eq_pow_val` does *not* fire on `↑((Units.map f ζu) ^ i)`; `rw [Units.coe_map]` alone
then leaves a defeq-but-not-syntactic goal, closed by `rfl`.  The converse needs `map_pow` at the
monoid hom `Units.map f : Kˣ →* K_wˣ` *after* `← pow_mul`, and the exponent as `i * p`. -/
theorem units_pow_eq_one_iff_powers_local (p : ℕ) [Fact p.Prime] {K : Type} [Field K]
    [NumberField K] (w : NK.GlobalCFT.Place K) (ζu : Kˣ) (hζ : IsPrimitiveRoot (ζu : K) p)
    (u : (NK.GlobalCFT.Place.localField K w)ˣ) :
    u ^ p = 1 ↔ ∃ i : ℕ,
      (Units.map (algebraMap K (NK.GlobalCFT.Place.localField K w)).toMonoidHom ζu) ^ i = u := by
  have hcoe : ∀ i : ℕ,
      ((Units.map (algebraMap K (NK.GlobalCFT.Place.localField K w)).toMonoidHom ζu) ^ i :
          NK.GlobalCFT.Place.localField K w) =
        (algebraMap K (NK.GlobalCFT.Place.localField K w) (ζu : K)) ^ i := by
    intro i
    rw [Units.coe_map]
    rfl
  constructor
  · intro hu
    obtain ⟨i, hi⟩ :=
      (pow_eq_one_iff_powers_local p w hζ (u : NK.GlobalCFT.Place.localField K w)).mp
        (by simpa using congrArg (fun v : (NK.GlobalCFT.Place.localField K w)ˣ =>
          (v : NK.GlobalCFT.Place.localField K w)) hu)
    exact ⟨i, Units.ext (by rw [Units.val_pow_eq_pow_val, hcoe i, hi])⟩
  · rintro ⟨i, rfl⟩
    have hζu : ζu ^ p = 1 := Units.ext hζ.pow_eq_one
    have hpow : ζu ^ (i * p) = 1 := by rw [mul_comm i p, pow_mul, hζu, one_pow]
    rw [← pow_mul, ← map_pow, hpow, map_one]

/-- **Lane (a)/(iii), the equivariance of the torsion generator.**

For `σ` in the decomposition group `D_w ≤ Gal(K/k)` and `c` with `σ ζ = ζ ^ c`, the local
automorphism `localAut w σ` of `K_w` sends the image of `ζ` to its `c`-th power:

  `localAut w σ (algebraMap K K_w ζ) = (algebraMap K K_w ζ) ^ c`.

Together with `pow_eq_one_iff_powers_local` (which says `K_wˣ[p]` *is* the group generated by that
element) this pins the `Gal(K_w/k_v)`-module `K_wˣ[p] ≅ μ_p`: its action is the cyclotomic
character, i.e. the same `T ≅ μ_p^∨` twist that `IsCyclotomicDual` (`hT`) fixes for `T`.  This is
the coherence that turns `Hom_ℤ(E', K_wˣ) = Hom_{𝔽_p}(E', K_wˣ[p])` into `Hom_{𝔽_p}(E', μ_p)`
*as `Gal`-modules*.

Note the universes: NK's local layer (`NK.GlobalCFT.Place`, `NK.HassePrinciple.localAut`) lives at
`Type 0`, so this lemma is stated there; `Place : (K : Type) → [Field K] → [NumberField K] → Type`. -/
theorem localAut_algebraMap_zeta_pow {k : Type} [Field k] [NumberField k]
    {K : Type} [Field K] [NumberField K] [Algebra k K] (w : NK.GlobalCFT.Place K) {ζ : K}
    (σ : ↥(MulAction.stabilizer (K ≃ₐ[k] K) w)) {c : ℕ} (hc : (σ : K ≃ₐ[k] K) ζ = ζ ^ c) :
    NK.HassePrinciple.localAut w σ (algebraMap K (NK.GlobalCFT.Place.localField K w) ζ)
      = (algebraMap K (NK.GlobalCFT.Place.localField K w) ζ) ^ c := by
  rw [NK.HassePrinciple.localAut_algebraMap, hc, map_pow]

/-- **Assembly tool.**  Two finite `𝔽_p`-vector spaces of the same dimension are additively
isomorphic.  This is the freedom used at the end of `local_ext_h1_bridge`: the two sides are
`𝔽_p`-vector spaces and only the *existence* of an additive isomorphism is needed, so a dimension
count (the content of (b), local Tate duality) suffices. -/
theorem nonempty_addEquiv_of_finrank_eq (p : ℕ) [Fact p.Prime] (A B : Type) [AddCommGroup A]
    [Module (ZMod p) A] [AddCommGroup B] [Module (ZMod p) B] [Finite A] [Finite B]
    (h : Module.finrank (ZMod p) A = Module.finrank (ZMod p) B) : Nonempty (A ≃+ B) :=
  ⟨(LinearEquiv.ofFinrankEq (R := ZMod p) (M := A) (M' := B) h).toAddEquiv⟩

set_option linter.style.haveILetI false in
set_option linter.unnecessarySimpa false in
/-- **The degree-one presentation of `Ext¹`.**  For a short exact sequence
`0 → X₁ → X₂ → X₃ → 0` in `Rep Coeff G` with `X₂` projective, the kernel of the connecting map
`Ext⁰(X₁, Y) → Ext¹(X₃, Y)` is exactly the image of the restriction `Ext⁰(X₂, Y) → Ext⁰(X₁, Y)`.

Combined with `ext_one_iso_of_projective_presentation` this is the classical description

  `Ext¹(X₃, Y) ≅ Hom_G(X₁, Y) / im(Hom_G(X₂, Y) → Hom_G(X₁, Y))`

(up to the degree-zero identification `Ext⁰(X, Y) ≅ (X ⟶ Y)`): the "resolve `E'` over `ℤ[G]`" step
of the `Ext` core, with `0 → R → F → E' → 0`, `F` free. -/
theorem ext_one_kernel_identification (G : Type) [Group G]
    (S : ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G)) (hS : S.ShortExact) [Projective S.X₂]
    (Y : Rep.{0} SSGRoute.PTExt.Coeff G) :
    (hS.extClass.precomp Y (Nat.add_zero 1)).ker =
      AddMonoidHom.range ((Abelian.Ext.mk₀ S.f).precomp Y (zero_add 0)) := by
  ext x
  rw [AddMonoidHom.mem_ker]
  constructor
  · intro hx
    obtain ⟨x₂, hx₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS Y x (Nat.add_zero 1) hx
    exact ⟨x₂, hx₂⟩
  · rintro ⟨x₂, rfl⟩
    simpa using hS.extClass_comp_assoc (Y := Y) x₂

set_option linter.style.haveILetI false in
/-- **`Ext¹` is the cokernel of the restriction along a projective presentation.**  For
`0 → X₁ → X₂ → X₃ → 0` in `Rep Coeff G` with `X₂` projective, the connecting map
`Ext⁰(X₁, Y) → Ext¹(X₃, Y)` is surjective, hence induces an isomorphism
`Ext¹(X₃, Y) ≅ Ext⁰(X₁, Y) / ker`; with `ext_one_kernel_identification` the kernel is the image of
the restriction from `Ext⁰(X₂, Y)`. -/
theorem ext_one_iso_of_projective_presentation (G : Type) [Group G]
    (S : ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G)) (hS : S.ShortExact) [Projective S.X₂]
    (Y : Rep.{0} SSGRoute.PTExt.Coeff G) :
    Nonempty (Abelian.Ext S.X₃ Y 1 ≃+
      (Abelian.Ext S.X₁ Y 0 ⧸ (hS.extClass.precomp Y (Nat.add_zero 1)).ker)) := by
  haveI : Subsingleton (Abelian.Ext S.X₂ Y 1) := Abelian.Ext.subsingleton_of_projective S.X₂ Y 0
  refine ⟨(QuotientAddGroup.quotientKerEquivOfSurjective
    (hS.extClass.precomp Y (Nat.add_zero 1)) (fun y => ?_)).symm⟩
  have hy : (Abelian.Ext.mk₀ S.g).comp y (zero_add 1) = 0 := Subsingleton.elim _ _
  obtain ⟨x, hx⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS Y y hy (Nat.add_zero 1)
  exact ⟨x, hx⟩

set_option linter.style.haveILetI false in
/-- **Dimension shift along a projective presentation.**  If `0 → X₁ → X₂ → X₃ → 0` is a short
exact sequence in `Rep Coeff G` with `X₂` projective and `n ≥ 1`, then the connecting map
`Ext^n(X₁, Y) → Ext^{n+1}(X₃, Y)` is an isomorphism. -/
theorem ext_shift_of_projective_presentation (G : Type) [Group G]
    (S : ShortComplex (Rep.{0} SSGRoute.PTExt.Coeff G)) (hS : S.ShortExact) [Projective S.X₂]
    (Y : Rep.{0} SSGRoute.PTExt.Coeff G) (n : ℕ) (hn1 : 1 ≤ n) :
    Nonempty (Abelian.Ext S.X₁ Y n ≃+ Abelian.Ext S.X₃ Y (n + 1)) := by
  have hn : 1 + n = n + 1 := Nat.one_add n
  haveI hsub : Subsingleton (Abelian.Ext S.X₂ Y n) := by
    have h := Abelian.Ext.subsingleton_of_projective S.X₂ Y (n - 1)
    rwa [Nat.sub_add_cancel hn1] at h
  haveI hsub' : Subsingleton (Abelian.Ext S.X₂ Y (n + 1)) :=
    Abelian.Ext.subsingleton_of_projective S.X₂ Y n
  have hker : ∀ z : Abelian.Ext S.X₁ Y n, (hS.extClass.precomp Y hn) z = 0 → z = 0 := by
    intro z hz
    obtain ⟨x₂, hx₂⟩ := Abelian.Ext.contravariant_sequence_exact₁ hS Y z hn hz
    have h0 : (Abelian.Ext.mk₀ S.f).comp (0 : Abelian.Ext S.X₂ Y n) (zero_add n) = 0 :=
      Abelian.Ext.comp_zero (Abelian.Ext.mk₀ S.f) Y n n (zero_add n)
    have hx2' : (Abelian.Ext.mk₀ S.f).comp x₂ (zero_add n) = 0 := by
      rw [Subsingleton.elim x₂ 0]; exact h0
    rw [hx2'] at hx₂
    exact hx₂.symm
  refine ⟨AddEquiv.ofBijective (hS.extClass.precomp Y hn) ⟨?_, ?_⟩⟩
  · intro x y hxy
    exact sub_eq_zero.mp (hker (x - y) (by rw [map_sub, hxy, sub_self]))
  · intro y
    have hy : (Abelian.Ext.mk₀ S.g).comp y (zero_add (n + 1)) = 0 := Subsingleton.elim _ _
    obtain ⟨x, hx⟩ := Abelian.Ext.contravariant_sequence_exact₃ hS Y y hy hn
    exact ⟨x, hx⟩

/-- **E7a.** Local Hilbert 90 bridge: at a finite place `A` of `Ω` lying over the place
`w = q` of `K`, continuous `1`-cocycles of the decomposition group `D_A ≤ G_k` with values in `E`
are classified by `Ext¹_{D_w}(E', K_wˣ)`, `E' = DualMod p (E ⊗ T) = E^∨(1)`: there is a map,
additive on cocycles, with kernel the coboundaries, and onto. -/
theorem local_ext_h1_bridge (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [NumberField K] (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (E : Type) [AddCommGroup E] [Module (ZMod p) E] [DistribMulAction (K ≃ₐ[k] K) E]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) E] [Finite E]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1) :
    ∃ β : ((Ω ≃ₐ[k] Ω) → E) →
        Abelian.Ext
          (Rep.res (decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
            (modRep (K ≃ₐ[k] K) (DualMod p (E ⊗[ZMod p] T))))
          (localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)) 1,
      (∀ b b' : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b' →
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b' →
          β (b + b') = β b + β b') ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → E,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b →
          SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b →
          (β b = 0 ↔ SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (SSGRoute.decomp k A) b)) ∧
      ∀ y, ∃ b : (Ω ≃ₐ[k] Ω) → E,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (SSGRoute.decomp k A) b ∧
        SSGRoute.IsLocConstOn (SSGRoute.decomp k A) b ∧ β b = y := by
  classical
  -- ## (0) the place glue
  obtain ⟨hLies, hcompat', _⟩ := Work.SSGRoute.exists_adicCompletion_algebra_compat k Ω K A hA q hAq
  letI : Algebra (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K) :=
    (Work.SSGRoute.adicCompletionMapAt k Ω K A hA q hLies).toAlgebra
  have hcompat : ∀ x : k, algebraMap k (q.adicCompletion K) x =
      algebraMap (Work.SSGRoute.localFieldAt k A hA) (q.adicCompletion K)
        (algebraMap k (Work.SSGRoute.localFieldAt k A hA) x) := fun x => (hcompat' x).symm
  obtain ⟨K', hfdK', hgalK', ψ, eG, Φ, hΦ, hRep, hpin, hcompatΦ⟩ :=
    localField_subfield_place_compat p k Ω K A hA q hAq hLies hcompat
  haveI hfdKi : FiniteDimensional (Work.SSGRoute.localFieldAt k A hA) K' := hfdK'
  haveI hgalKi : IsGalois (Work.SSGRoute.localFieldAt k A hA) K' := hgalK'
  -- ## (1) the primitive root of unity in the local closure
  let ζi : ↥K := ⟨ζ, hζK⟩
  let ζK : ↥K' := ψ.symm (algebraMap ↥K (q.adicCompletion K) ζi)
  let ζ' : Work.SSGRoute.localClosureAt k A hA :=
    algebraMap ↥K' (Work.SSGRoute.localClosureAt k A hA) ζK
  have hζi : IsPrimitiveRoot ζi p := by
    show IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) p
    exact IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥K Ω) (by simpa using hζ)
      (RingHom.injective _)
  have hζKprim : IsPrimitiveRoot ζK p := by
    have h1 : IsPrimitiveRoot (algebraMap ↥K (q.adicCompletion K) ζi) p :=
      hζi.map_of_injective (f := algebraMap ↥K (q.adicCompletion K)) (RingHom.injective _)
    have h2 : ψ ζK = algebraMap ↥K (q.adicCompletion K) ζi := AlgEquiv.apply_symm_apply ψ ζi
    rw [← h2] at h1
    have h3 := h1.map_of_injective (f := ψ.symm.toMulEquiv)
      (fun a b hab => MulEquiv.injective ψ.symm.toMulEquiv hab)
    simpa using h3
  have hζ' : IsPrimitiveRoot ζ' p :=
    hζKprim.map_of_injective (f := algebraMap ↥K' (Work.SSGRoute.localClosureAt k A hA))
      (RingHom.injective _)
  -- ## (2) the comparison map and the cyclotomic-dual property
  let act : (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
      Work.SSGRoute.localClosureAt k A hA) →* (K ≃ₐ[k] K) :=
    (decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype.comp
      (eG.symm.toMonoidHom.comp
        (AlgEquiv.restrictNormalHom (F := Work.SSGRoute.localFieldAt k A hA)
          (K₁ := Work.SSGRoute.localClosureAt k A hA) ↥K'))
  have hcyc : SSGRoute.IsCyclotomicDual p (T := T) act ζ' := by
    refine ⟨hT.1, ?_⟩
    intro γ c hc t
    have hkey : (act γ) ζi = ζi ^ c := by
      let τ : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) :=
        eG.symm (AlgEquiv.restrictNormalHom (F := Work.SSGRoute.localFieldAt k A hA)
          (K₁ := Work.SSGRoute.localClosureAt k A hA) ↥K' γ)
      have hτ : τ =
        eG.symm (AlgEquiv.restrictNormalHom (F := Work.SSGRoute.localFieldAt k A hA)
          (K₁ := Work.SSGRoute.localClosureAt k A hA) ↥K' γ) := rfl
      have hactγ : act γ = (decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype τ := rfl
      have heGτ : eG τ = AlgEquiv.restrictNormalHom (F := Work.SSGRoute.localFieldAt k A hA)
          (K₁ := Work.SSGRoute.localClosureAt k A hA) ↥K' γ := by
        rw [hτ]; exact MulEquiv.apply_symm_apply _ _
      have hψ : ψ ζK = algebraMap ↥K (q.adicCompletion K) ζi := AlgEquiv.apply_symm_apply ψ ζi
      have hgam : (γ : Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
            Work.SSGRoute.localClosureAt k A hA) (ζK : Work.SSGRoute.localClosureAt k A hA)
          = ((eG τ) ζK : Work.SSGRoute.localClosureAt k A hA) := by
        rw [heGτ, AlgEquiv.restrictNormalHom_apply]
      have hstep : (γ : Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
            Work.SSGRoute.localClosureAt k A hA) (ζK : Work.SSGRoute.localClosureAt k A hA)
          = ((ψ.symm (NK.HassePrinciple.localAut (K := k) (L := ↥K)
              (NK.GlobalCFT.Place.ofFinite q) τ (ψ ζK)))
            : Work.SSGRoute.localClosureAt k A hA) := by
        rw [hgam, hpin τ ζK]
      have hc' : (γ : Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
            Work.SSGRoute.localClosureAt k A hA) (ζK : Work.SSGRoute.localClosureAt k A hA)
          = ((ζK : Work.SSGRoute.localClosureAt k A hA)) ^ c := hc
      have hconv : ψ.symm (NK.HassePrinciple.localAut (K := k) (L := ↥K)
            (NK.GlobalCFT.Place.ofFinite q) τ (ψ ζK)) = ζK ^ c := by
        apply Subtype.ext
        have hcoe : ∀ z : ↥K',
            (↑z : Work.SSGRoute.localClosureAt k A hA)
              = algebraMap ↥K' (Work.SSGRoute.localClosureAt k A hA) z := fun z => rfl
        rw [hcoe (ζK ^ c), map_pow (algebraMap ↥K' (Work.SSGRoute.localClosureAt k A hA)) ζK c]
        rw [hcoe ζK] at hstep
        exact hstep.symm.trans hc
      have h6 : NK.HassePrinciple.localAut (K := k) (L := ↥K) (NK.GlobalCFT.Place.ofFinite q) τ
            (algebraMap ↥K (q.adicCompletion K) ζi)
          = (algebraMap ↥K (q.adicCompletion K) ζi) ^ c := by
        have hh := congrArg (fun z : ↥K' => ψ z) hconv
        rw [map_pow] at hh
        simpa [hψ] using hh
      have h8 : algebraMap ↥K (q.adicCompletion K) (τ.1 ζi)
          = (algebraMap ↥K (q.adicCompletion K) ζi) ^ c := by
        have hlemma : NK.HassePrinciple.localAut (K := k) (L := ↥K)
              (NK.GlobalCFT.Place.ofFinite q) τ (algebraMap ↥K (q.adicCompletion K) ζi)
            = algebraMap ↥K (q.adicCompletion K) (τ.1 ζi) :=
          NK.HassePrinciple.localAut_algebraMap (K := k) (L := ↥K)
            (NK.GlobalCFT.Place.ofFinite q) τ ζi
        rw [← hlemma]
        exact h6
      have h9 : τ.1 ζi = ζi ^ c := by
        apply RingHom.injective (algebraMap ↥K (q.adicCompletion K))
        rw [map_pow]
        exact h8
      rw [hactγ]
      exact h9
    obtain ⟨σtilde, hσtilde⟩ :=
      AlgEquiv.restrictNormalHom_surjective (F := k) Ω (act γ)
    have hσζ : σtilde • ζ = ζ ^ c := by
      show σtilde ζ = ζ ^ c
      have hone : ((SSGRoute.res k K σtilde) ζi : Ω) = ζ ^ c := by
        have h : (SSGRoute.res k K σtilde) ζi = ζi ^ c := by
          rw [show SSGRoute.res k K σtilde = act γ from hσtilde]
          exact hkey
        have h2 := congrArg (fun z : ↥K => (z : Ω)) h
        simpa [ζi] using h2
      rwa [AlgEquiv.restrictNormalHom_apply] at hone
    have hfin := hT.2 σtilde c hσζ t
    simpa [SSGRoute.res, hσtilde] using hfin
  -- ## (3) finiteness
  haveI : Module.Finite (ZMod p) T := Module.finite_of_finrank_pos (by rw [hT.1]; norm_num)
  let u : T ≃ₗ[ZMod p] ZMod p :=
    LinearEquiv.ofFinrankEq (R := ZMod p) T (ZMod p) (by rw [hT.1, Module.finrank_self])
  haveI : Finite T := Finite.of_injective u (fun a b h => u.injective h)
  let isoE : E ≃ₗ[ZMod p] (E ⊗[ZMod p] T) :=
    (TensorProduct.rid (ZMod p) E).symm.trans
      ((TensorProduct.congr (LinearEquiv.refl (ZMod p) E) u).symm)
  haveI : Finite (E ⊗[ZMod p] T) := Finite.of_injective isoE.symm isoE.symm.injective
  haveI : Finite (DualMod p (E ⊗[ZMod p] T)) :=
    Finite.of_injective (fun f : DualMod p (E ⊗[ZMod p] T) => (f : (E ⊗[ZMod p] T) → ZMod p))
      (fun f g h => LinearMap.ext (fun x => congrFun h x))
  -- ## (4) abbreviations
  let Y0 : Rep.{0} Coeff (K' ≃ₐ[Work.SSGRoute.localFieldAt k A hA] K') :=
    Rep.res eG.symm.toMonoidHom
      (Rep.res (decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
        (modRep (K ≃ₐ[k] K) (DualMod p (E ⊗[ZMod p] T))))
  haveI hY0fin : Finite (Y0 : Type) := inferInstanceAs (Finite (DualMod p (E ⊗[ZMod p] T)))
  haveI hY0mod : Module (ZMod p) (Y0 : Type) :=
    inferInstanceAs (Module (ZMod p) (DualMod p (E ⊗[ZMod p] T)))
  -- ## (5) the rows
  obtain ⟨φab⟩ := ext_localUnits_iso_Q (p := p) (k := k) (Ω := Ω) (K := K) (T := T) (E := E)
    (A := A) (hA := hA) (q := q) (K' := K') (eG := eG) (hRep := hRep)
  obtain ⟨φc⟩ := ext_continuous_descent (L := Work.SSGRoute.localFieldAt k A hA)
    (M := Work.SSGRoute.localClosureAt k A hA) K' p Y0
    (fun x => by
      rw [← Nat.cast_smul_eq_nsmul (ZMod p) p x, ZMod.natCast_self]
      exact zero_smul _ _)
  obtain ⟨φd⟩ := homRep_dualMod_units_localClosure (p := p) (k := k) (Ω := Ω) (K := K)
    (A := A) (hA := hA) (T := T) (E := E) (act := act) (ζ' := ζ') (hζ' := hζ') (hcyc := hcyc)
  letI instE : DistribMulAction (Work.SSGRoute.localClosureAt k A hA ≃ₐ[Work.SSGRoute.localFieldAt k A hA]
      Work.SSGRoute.localClosureAt k A hA) E :=
    { smul := fun γ e => act γ • e
      one_smul := fun e => by
        show act 1 • e = e
        rw [map_one, one_smul]
      mul_smul := fun γ δ e => by
        show act (γ * δ) • e = act γ • (act δ • e)
        rw [map_mul, mul_smul]
      smul_add := fun γ e e' => smul_add (act γ) e e'
      smul_zero := fun γ => smul_zero (act γ) }
  have hact_eq : ∀ σ : ↥(SSGRoute.decomp k A),
      act (Φ σ) = SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω) := by
    intro σ
    refine AlgEquiv.ext fun x => ?_
    let τ : ↥(decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)) :=
      eG.symm (AlgEquiv.restrictNormalHom (F := Work.SSGRoute.localFieldAt k A hA)
        (K₁ := Work.SSGRoute.localClosureAt k A hA) ↥K' (Φ σ))
    have hτ : τ =
      eG.symm (AlgEquiv.restrictNormalHom (F := Work.SSGRoute.localFieldAt k A hA)
        (K₁ := Work.SSGRoute.localClosureAt k A hA) ↥K' (Φ σ)) := rfl
    have hactσ : act (Φ σ) =
        (decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype τ := rfl
    have heGτ : eG τ = AlgEquiv.restrictNormalHom (F := Work.SSGRoute.localFieldAt k A hA)
        (K₁ := Work.SSGRoute.localClosureAt k A hA) ↥K' (Φ σ) := by
      rw [hτ]; exact MulEquiv.apply_symm_apply _ _
    have h1 : NK.HassePrinciple.localAut (K := k) (L := ↥K) (NK.GlobalCFT.Place.ofFinite q) τ
        (algebraMap ↥K (q.adicCompletion K) x) =
        algebraMap ↥K (q.adicCompletion K) ((SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) x) := by
      have h2 := congrArg (fun z : ↥K' => (z : Work.SSGRoute.localClosureAt k A hA))
        (hpin τ (ψ.symm (algebraMap ↥K (q.adicCompletion K) x)))
      rw [AlgEquiv.apply_symm_apply] at h2
      rw [heGτ, AlgEquiv.restrictNormalHom_apply] at h2
      rw [hcompatΦ σ x] at h2
      exact ψ.symm.injective (Subtype.ext h2.symm)
    rw [NK.HassePrinciple.localAut_algebraMap (K := k) (L := ↥K)
      (NK.GlobalCFT.Place.ofFinite q) τ x] at h1
    have h4 : τ.1 x = (SSGRoute.res k K (σ : Ω ≃ₐ[k] Ω)) x :=
      RingHom.injective (algebraMap ↥K (q.adicCompletion K)) h1
    show (act (Φ σ)) x = _
    rw [hactσ]
    exact h4
  obtain ⟨φe⟩ := h1cont_iso_H1loc p k Ω K E A hA Φ hΦ
    (fun σ e => by
      show act (Φ σ) • e = (SSGRoute.res k K) (σ : Ω ≃ₐ[k] Ω) • e
      rw [hact_eq σ])
  obtain ⟨φseam⟩ := h1_coeff_transfer_localClosure (p := p) (k := k) (Ω := Ω) (K := K)
    (A := A) (hA := hA) (T := T) (E := E) (act := act) (ζ' := ζ') (hζ' := hζ') (hcyc := hcyc)
    (inst := instE) (hinst := fun γ e => rfl)
  -- ## (6) assemble
  have hφ : Nonempty (H1loc p k Ω K E (SSGRoute.decomp k A) ≃+
      Abelian.Ext
        (Rep.res (decompK (k := k) (NK.GlobalCFT.Place.ofFinite q)).subtype
          (modRep (K ≃ₐ[k] K) (DualMod p (E ⊗[ZMod p] T))))
        (localUnitsK (k := k) (NK.GlobalCFT.Place.ofFinite q)) 1) :=
    ⟨(φe.symm).trans ((φseam.symm).trans ((φc.symm).trans (φab.symm)))⟩
  exact exists_beta_of_addEquiv p k Ω K E A _ (Classical.choice hφ)



end Work.SSGRoute
