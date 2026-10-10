import Mathlib.RingTheory.Henselian
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.E9Nodes.e9_baseS
import Submission.Work.SSGRoute.Sha2Lib.exists_isLocTrivial_inflH
import Submission.Work.SSGRoute.Sha2Lib.phiAt_inflH
import Submission.Work.SSGRoute.e9_caseB_descent_wide
import Submission.Work.SSGRoute.e9_infl_local_compat
import Submission.Work.SSGRoute.e9_inflation_descent
import Submission.Work.SSGRoute.local_duality_ext_extH_finite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

LEAD NOTES (SSG E9 split). Your node `e9_vanish_off_finite` is one of three sub-lemmas (E9a vanish_off_finite, E9b local_decomposition, E9c glue_phiAt). Together with E7cΩ (local_phi_realization_in, in flight), E6Ω (phi1_mono_sylow_in, PROVED) and PT.exists_glue_extLoc, they close E9 pt_sha2_core: an assembly compiling against the live workspace already exists. Your statement's doc comment gives the proof idea. Import siblings; do not reprove them. Do NOT route through tatePoitouEmbedding / poitouTate_pairing_var. The designer's answer follows.

===== ANSWER_E9_route.md =====
# Answer: the E9 `pt_sha2_core` route, and H7's two claims

2026-09-27. Everything below was elaborated on 3.144 in `/tmp/e7bd/`, using `lake env lean` under
`systemd-run --user --scope -q -p MemoryMax=12G`. No workspace file was touched.

## Verdict

**E9 is provable from the listed inputs.** H7's two claims are both wrong. However, the ssg4 note
bundles three real sub-steps into a "1–2k" node, and that bundling is too coarse.
- The sub-steps are finite-`S` continuity, the local decomposition, and the glue/sum formula.
- They should be dispatched as three nodes, E9a, E9b and E9c.
- E9 then becomes an assembly. `e9_assembly_check.lean` elaborates against the live workspace.
- The **body** of `pt_sha2_core` in that file is complete. Apart from E9a/b/c it uses only E7cΩ,
  E6Ω, `PT.exists_glue_extLoc`, and two trivial helpers: `phiAt_sub_aux` (additivity of the
  pairing) and `exists_orbit_transversal` (a choice of one place per orbit).

**Status of the inputs** (checked with `#print axioms`):
- **Clean:** `phi1_mono_sylow_in` (E6Ω), `PT.exists_glue_extLoc` (E2 glue),
  `Sha2Lib.exists_isLocTrivial_inflH` (L3), `Sha2Lib.phiAt_inflH`, `phiAt_level_infl`.
- **Still `sorryAx`:** `local_phi_realization_in` (E7cΩ).

## 1. The bridge: where it enters, and whether it is true

**Where it enters.** It is used in exactly one place: E9a, step 1.
- E9's hypothesis is stated at level `K`.
- E9a needs the all-levels form: `phiAt x h = 0` for every `h` that is locally trivial at level `L`.
- That form follows from **L3**, `Sha2Lib.exists_isLocTrivial_inflH` (proved). L3 says a level-`L`
  locally trivial class is `inflH h'` with `h'` locally trivial at level `K`.
- Then `phiAt x (inflH h') = inflC (pairK x h') = 0` by `Sha2Lib.phiAt_inflH`.
- Only this direction is used, and it is proved.

**H7's "⇒ is false" is itself false.** Take `f : D_w(L) → D_v(K)`.
- `f` is **surjective**. This is Y2, `decompK_restrict_surjective`.
- `M` is inflated along `f`, so `M^{ker f} = M`.
- The first term of inflation–restriction then gives an injection `H¹(D_v, M) ↪ H¹(D_w, M)`.
- H7's counterexample has `D_v = ℤ/2` and `D_w = 1`. That violates surjectivity.
- H7's "kernel = transgression image in `H¹`" misreads the five-term sequence: the transgression
  lands in `H²`.
- So the level-`K` ⟺ level-`L` "iff" is true. In any case it is not needed beyond L2 and L3, which
  are both proved.

## 2. "`PhiOneVanishesIn` is unobtainable": false

H7 conflates `x` with `x − extToClasses z`.
- It is true that the hypothesis constrains only locally trivial classes.
- It is also true that `PhiOneVanishesIn Ω x` would force `x = 0`.
- But `z` is **built from `x`'s own functional**, so that
  `phiAt (extToClasses z) h = phiAt x h` for **every** `h` at every level.
- The hypothesis is used only to make that construction possible: it lets `ψ = φ¹(x)` factor
  through localisation.

## 3. E9 proof skeleton (compiled; see `e9_assembly_check.lean`)

Take `Ω := AlgebraicClosure K`.

1. **E9a `e9_vanish_off_finite`.** It returns a finite `S` (containing the archimedean places, the
   places above `p`, and the places where `M` ramifies). At every Ω-level, `φ¹(x)` kills classes
   that are locally trivial over `S` and unramified at every finite place.
   - Step 1: the all-levels form via L3 (§1).
   - Step 2: the sets `B_S` of such classes are finite and decreasing in `S`, and they stabilise at
     the locally trivial classes. The only arithmetic input is that there are finitely many
     everywhere-unramified degree-`p` extensions of `K` (Hermite–Minkowski or the class group).
   - Size 1.5–2.5k.
2. **E9b `e9_local_decomposition`.** Choose a transversal `R` of the orbits of places. E9b returns
   families `lam v` (`v ∈ R`), each satisfying E7cΩ's hypotheses at `w = v`:
   - `hp`, `hcompat` and `hloc`;
   - `lam v` kills unramified classes when `v ∉ S`;
   - `phiAt x h = ∑ᶠ v, lam v L h`, with finite support.

   Route: `ψ` on `colim_L H¹(Gal(L/k), M)`, valued in `colim H²(C_L)[p] ≅ ℤ/p` (inflation is
   injective), factors through `V/U ↪ ⊕_{v∈R} Q_v`. Here `Q_v = H¹(k_v, M)` for `v ∈ S`, and
   `H¹(k_v, M)/H¹_ur` otherwise. Extend to the direct sum, split into components, and read off
   levelwise. Size 1.5–3k.
3. **E7cΩ `local_phi_realization_in`, once per `v`.**
   - It gives `z_v` supported on the orbit of `v` with `phiAt(extToClasses z_v) = lam v` at every
     level.
   - Its unramified clause gives `IsUnramifiedExt v (extLoc v z_v)` for `v ∉ S`. The hypotheses
     come from E9a's `S`: `v` is finite, `p ∉ q`, `M` is unramified, and `lam v` kills unramified
     classes.
4. **`PT.exists_glue_extLoc`** with `r = 1`, applied to `a v := extLoc v (z_v)`, gives `z`.
   - Its admissibility (finitely many ramified components) holds because the ramified components
     lie in `S`.
5. **E9c `e9_glue_phiAt`.** `phiAt(extToClasses z) h = ∑ᶠ v, phiAt(extToClasses z_v) h`, with
   finite support.
   - Let `T` be `S` together with the places where `h` ramifies.
   - `z − Σ_{v∈T} z_v` has zero components over `T` and unramified components elsewhere.
   - An unramified local class pairs to zero with an unramified `h` (the value lies in
     `H²(D/I, 𝒪_urˣ) = 0`).
   - So all local components of the level-`L` idèle value vanish (`PT.extLoc_yonedaPair`), and by
     E2 clause (i) at level `L` the value itself is `0`.
   - Size 1–2k.
6. **Conclusion.**
   - By steps 2, 3 and 5, `phiAt (x − extToClasses z) h = 0` for all `L, h`. That is
     `PhiOneVanishesIn Ω (x − extToClasses z)`.
   - E6Ω then gives `x − extToClasses z = 0`, i.e. `x = extToClasses z`.
   - A correction to the question: there is no `z′`. E6Ω gives `= 0` directly.

**Total.** About 4.5–8k lines instead of 1–2k, plus E7cΩ.

## 4. Repair: nothing is broken; split the node

The route is sound. Dispatch the following. Each statement elaborates, with only
`declaration uses sorry`, when imported together with `phi1_mono_sylow_in`,
`local_phi_realization_in` and `PT.exists_glue_extLoc` (no import clash).

| File | Node | `--imports` |
|---|---|---|
| `e9_vanish_off_finite.lean` | E9a | `PTDefsOmega` |
| `e9_local_decomposition.lean` | E9b | `PTDefsOmega` |
| `e9_glue_phiAt.lean` | E9c | `PTDefsOmega` |
| `e9_assembly_check.lean` | E9 = the ssg4 statement, proved from the above | `phi1_mono_sylow_in`, `local_phi_realization_in`, `PT.exists_glue_extLoc` |

In `e9_assembly_check.lean`, the helpers `phiAt_sub_aux` and `exists_orbit_transversal` are
0.1–0.3k each.

**What not to do.**
- Do not route through `tatePoitouEmbedding`, `poitouTate_pairing` or `sha_card_euler`.
- Do not restate E9 with an all-levels hypothesis; L3 already supplies it.
-/

namespace Work.SSGRoute

set_option linter.unusedVariables false

open SSGRoute.PTExt CategoryTheory

/-! ## The ingredients of the finite-`S` continuity -/

/-- **The level-`K` stabilisation.**  The family, indexed by finite sets of places of `K`, of the
classes of `H¹(Gal(K/k), M)` which vanish on the decomposition group of every place of the set, is
a decreasing family of subsets of the finite set `H¹(Gal(K/k), M)`; hence it stabilises, and its
stable value is the set of locally trivial classes. -/
theorem e9_locTrivial_stabilisation (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] :
    ∃ S : Finset (NK.GlobalCFT.Place K), ∀ h : extH M 1,
      (∀ v ∈ S, extHRestrict (decompK (k := k) v) h = 0) →
        IsLocTrivial (k := k) (K := K) h := by
  classical
  haveI : Finite (K ≃ₐ[k] K) := Nat.finite_of_card_ne_zero (by
    rw [IsGalois.card_aut_eq_finrank]
    exact (Module.finrank_pos (R := k) (M := K)).ne')
  haveI hfin : Finite (extH M 1) := Work.SSGRoute.local_duality_ext_extH_finite M 1
  haveI : Fintype (extH M 1) := Fintype.ofFinite _
  -- the witness place of a non-locally-trivial class
  have hwit : ∀ h : extH M 1, ¬ IsLocTrivial (k := k) (K := K) h →
      ∃ v : NK.GlobalCFT.Place K, extHRestrict (decompK (k := k) v) h ≠ 0 := by
    intro h hh
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hh hcon
  let Bad : Finset (extH M 1) :=
    Finset.univ.filter (fun h => ¬ IsLocTrivial (k := k) (K := K) h)
  have hkey : ∀ h : ↥Bad, ∃ v : NK.GlobalCFT.Place K,
      extHRestrict (decompK (k := k) v) h.1 ≠ 0 := by
    intro h
    refine hwit h.1 ?_
    have h2 := h.2
    rw [Finset.mem_filter] at h2
    exact h2.2
  refine ⟨Bad.attach.image (fun h => Classical.choose (hkey h)), ?_⟩
  intro h hh
  by_contra hne
  have hbad : h ∈ Bad := Finset.mem_filter.mpr ⟨Finset.mem_univ h, hne⟩
  have hmem : Classical.choose (hkey ⟨h, hbad⟩) ∈
      Bad.attach.image (fun h => Classical.choose (hkey h)) :=
    Finset.mem_image.mpr ⟨⟨h, hbad⟩, Finset.mem_attach _ _, rfl⟩
  exact Classical.choose_spec (hkey ⟨h, hbad⟩) (hh _ hmem)

/-- **E9a in its finite-`S`-continuity form, without the maximal unramified abelian extension.**
The witness set is produced by `e9_witness_of_classGroup` (a class-group generating set) and the
descent by `e9_caseB_descent_wide`, so no Hilbert class field is needed. -/
theorem e9_finiteS_stab_wide (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M]
    (S₀ : Finset (NK.GlobalCFT.Place K))
    (hS₀arch : ∀ v : NK.GlobalCFT.Place K,
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        v ≠ NK.GlobalCFT.Place.ofFinite q) → v ∈ S₀) :
    ∃ T : Finset (NK.GlobalCFT.Place K), S₀ ⊆ T ∧
      ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (h : extH (Rep.res (galRes k K L) M) 1),
        (∀ w' : NK.GlobalCFT.Place L, (∃ v ∈ T, NK.GlobalCFT.Place.LiesOver w' v) →
          extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h = 0) →
        (∀ q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
          IsUnramifiedClassAt q' h) →
        IsLocTrivialLevel (k := k) (K := K) (L := L) h := by
  classical
  -- the set of witness places, from a class-group generating set
  obtain ⟨W, hW⟩ := e9_witness_of_classGroup K
  -- the level-`K` stabilising set
  obtain ⟨S_K, hS_K⟩ := e9_locTrivial_stabilisation (k := k) (K := K) M
  refine ⟨S₀ ∪ S_K ∪ W, ?_, ?_⟩
  · intro v hv
    exact Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl hv)))
  · intro L _ hLfd hLgal h hT hunr
    -- every place of `L` lies over a place of `K`
    have hunder : ∀ w' : NK.GlobalCFT.Place ↥L, ∃ v : NK.GlobalCFT.Place K,
        NK.GlobalCFT.Place.LiesOver w' v := fun w' =>
      NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := ↥L) w'
    -- every place of `K` has a place of `L` above it
    have hover : ∀ v : NK.GlobalCFT.Place K, ∃ w' : NK.GlobalCFT.Place ↥L,
        NK.GlobalCFT.Place.LiesOver w' v := by
      intro v
      rcases v with w | Q
      · obtain ⟨w', hw'⟩ := NumberField.InfinitePlace.comap_surjective (k := K) (K := ↥L) w
        exact ⟨NK.GlobalCFT.Place.ofInfinite w',
          NK.GlobalCFT.Place.liesOver_ofInfinite
            ((NK.GlobalCFT.Norm.liesOver_iff_comap_eq w' w).mpr hw')⟩
      · obtain ⟨q, hq⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
          (K := K) (L := ↥L) Q
        exact ⟨NK.GlobalCFT.Place.ofFinite q, NK.GlobalCFT.Place.liesOver_ofFinite hq⟩
    -- `h` is trivial at the archimedean places of `L`
    have harch : ∀ w' : NK.GlobalCFT.Place ↥L,
        (∀ q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L),
          w' ≠ NK.GlobalCFT.Place.ofFinite q') →
        extHRestrict (MulAction.stabilizer (↥L ≃ₐ[k] ↥L) w') h = 0 := by
      intro w' hw'
      obtain ⟨v, hv⟩ := hunder w'
      have hvarch : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          v ≠ NK.GlobalCFT.Place.ofFinite q := by
        intro q hq
        have hfinv : NK.GlobalCFT.Place.IsFinite v :=
          hq ▸ ((NK.GlobalCFT.Place.isFinite_iff).mpr ⟨q, rfl⟩)
        have hfin : NK.GlobalCFT.Place.IsFinite w' :=
          (NK.GlobalCFT.Place.isFinite_of_liesOver hv).mpr hfinv
        rw [NK.GlobalCFT.Place.isFinite_iff] at hfin
        obtain ⟨q', hq'⟩ := hfin
        exact hw' q' hq'
      have hvT : v ∈ S₀ ∪ S_K ∪ W :=
        Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inl (hS₀arch v hvarch))))
      exact hT w' ⟨v, hvT, hv⟩
    -- Case B: `h` descends to the level `K`
    have hN : extHRestrict (galRes k K ↥L).ker h = 0 :=
      e9_caseB_descent_wide k K M W hW ↥L h hunr harch
        (fun w' hw' => hT w' (by
          obtain ⟨v, hvT, hv⟩ := hw'
          exact ⟨v, Finset.mem_union.mpr (Or.inr hvT), hv⟩))
    obtain ⟨h', hh'⟩ := e9_inflation_descent k K ↥L M h hN
    -- the descended class is locally trivial at the level `K`
    have hlt' : IsLocTrivial (k := k) (K := K) h' := by
      refine hS_K h' (fun v hv => ?_)
      obtain ⟨w', hw'⟩ := hover v
      have h1 : extHRestrict (MulAction.stabilizer (↥L ≃ₐ[k] ↥L) w')
          (inflH (k := k) (K := K) (L := ↥L) h') = 0 := by
        rw [hh']
        exact hT w' ⟨v, Finset.mem_union.mpr (Or.inl (Finset.mem_union.mpr (Or.inr hv))), hw'⟩
      exact (e9_infl_local_compat k K ↥L M h' v w' hw').mp h1
    -- `h` is locally trivial at the level `L`
    intro w'
    obtain ⟨v, hv⟩ := hunder w'
    rw [← hh']
    exact (e9_infl_local_compat k K ↥L M h' v w' hv).mpr (hlt' v)

/-- **E9a (finite-`S` continuity).**  If `x` kills the level-`K` locally trivial classes, there is
a finite set `S` of places of `K` — containing every archimedean place, every place above `p` and
every place where `M` is ramified — such that at every `Ω`-level `L`, `φ¹(x)` kills every class
that is locally trivial at all places over `S` and unramified at every finite place.
Route: (1) `x` kills level-`L` locally trivial classes (`Sha2Lib.exists_isLocTrivial_inflH` +
`Sha2Lib.phiAt_inflH`); (2) the classes unramified at all finite places and trivial at the
archimedean ones form a finite set up to inflation (only finitely many everywhere-unramified
degree-`p` extensions of `K`: Hermite–Minkowski or the class group), so the decreasing family
`B_S` stabilises at the locally trivial classes. -/
theorem e9_vanish_off_finite (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (ζ : K) (hζ : IsPrimitiveRoot ζ p)
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (x : Abelian.Ext M (classesK k K) 1)
    (hx : ∀ h : extH M 1, IsLocTrivial h → pairK x h = 0) :
    ∃ S : Finset (NK.GlobalCFT.Place K),
      (∀ v : NK.GlobalCFT.Place K,
        (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
          v ≠ NK.GlobalCFT.Place.ofFinite q) → v ∈ S) ∧
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        NK.GlobalCFT.Place.ofFinite q ∉ S →
          (p : NumberField.RingOfIntegers K) ∉ q.asIdeal ∧
          ∀ σ : K ≃ₐ[k] K, IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m) ∧
      ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
        (h : extH (Rep.res (galRes k K L) M) 1),
        (∀ w' : NK.GlobalCFT.Place L, (∃ v ∈ S, NK.GlobalCFT.Place.LiesOver w' v) →
          extHRestrict (MulAction.stabilizer (L ≃ₐ[k] L) w') h = 0) →
        (∀ q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L),
          IsUnramifiedClassAt q' h) →
        phiAt (k := k) (K := K) (L := L) x h = 0 := by
  obtain ⟨S₀, hS₀arch, hS₀bad⟩ := Work.SSGRoute.E9Nodes.e9_baseS p k K M
  obtain ⟨T, hS₀T, hT⟩ := e9_finiteS_stab_wide k K Ω M S₀ hS₀arch
  refine ⟨T, ?_, ?_, ?_⟩
  · intro v hv
    exact hS₀T (hS₀arch v hv)
  · intro q hq
    exact hS₀bad q (fun hmem => hq (hS₀T hmem))
  · intro L _ _ _ h h1 h2
    have hlt : IsLocTrivialLevel (k := k) (K := K) (L := L) h := hT L h h1 h2
    obtain ⟨h', hh', hinf⟩ := Work.SSGRoute.Sha2Lib.exists_isLocTrivial_inflH k K L h hlt
    rw [← hinf, Work.SSGRoute.Sha2Lib.phiAt_inflH (k := k) (K := K) (L := L) x h']
    rw [show yonedaPair x h' = pairK x h' from rfl]
    rw [hx h' hh']
    exact Work.SSGRoute.E6Util.extHMap_zero (galRes k K L) (classIncl k K L)

end Work.SSGRoute
