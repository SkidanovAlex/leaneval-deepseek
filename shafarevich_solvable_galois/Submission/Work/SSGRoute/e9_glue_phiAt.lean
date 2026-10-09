import Mathlib
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.E9c.Core
import Submission.Work.SSGRoute.E9c.Unram
import Submission.Work.SSGRoute.e9c_transport_zero
import Submission.Work.SSGRoute.e9c_transport_unram
import Submission.Work.SSGRoute.e9c_unram_pairing
import Submission.Work.SSGRoute.e9c_extLoc_conj_zero
import Submission.Work.SSGRoute.e9c_phiAt_eq_zero_of_local
import Submission.Work.SSGRoute.exists_finset_unramifiedPlaces
import Submission.Work.SSGRoute.PT.pt_pairing_ext
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

/-! Guidance from the project lead (the requester):

LEAD NOTES (SSG E9 split). Your node `e9_glue_phiAt` is one of three sub-lemmas (E9a vanish_off_finite, E9b local_decomposition, E9c glue_phiAt). Together with E7cΩ (local_phi_realization_in, in flight), E6Ω (phi1_mono_sylow_in, PROVED) and PT.exists_glue_extLoc, they close E9 pt_sha2_core: an assembly compiling against the live workspace already exists. Your statement's doc comment gives the proof idea. Import siblings; do not reprove them. Do NOT route through tatePoitouEmbedding / poitouTate_pairing_var. The designer's answer follows.

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

open SSGRoute.PTExt CategoryTheory
open NK.GlobalCFT (Idele Place IdeleClassGroup)

/-! ## Helper constructions for the E9c assembly -/

/-- The place of the base field below a place of a finite extension. -/
private noncomputable def e9cUnder {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (w : Place L) : Place K :=
  Classical.choose (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w)

private theorem e9cUnder_liesOver {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] (w : Place L) :
    Place.LiesOver w (e9cUnder (K := K) w) :=
  Classical.choose_spec (NK.GlobalCFT.Inclusion.globalCFT_exists_placeUnder (K := K) (L := L) w)

private theorem e9cUnder_eq_of_liesOver {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] {w : Place L} {v : Place K} (h : Place.LiesOver w v) :
    e9cUnder (K := K) w = v :=
  NK.GlobalCFT.Inclusion.globalCFT_liesOver_unique (e9cUnder_liesOver (K := K) w) h

/-- **The good finite `Gal(K/k)`-stable set of places.** -/
private theorem e9c_exists_good_T (k : Type) [Field k] [NumberField k] (K L : Type) [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L]
    [IsScalarTower k K L] [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L]
    [IsGalois k L] [FiniteDimensional K L] (S : Finset (Place K)) :
    ∃ T : Set (Place K), T.Finite ∧
      (∀ (σ : K ≃ₐ[k] K) ⦃u : Place K⦄, u ∈ T → σ • u ∈ T) ∧
      (∀ u : Place K, u ∈ (S : Set (Place K)) → u ∈ T) ∧
      (∀ w : Place L, (∀ u : Place K, u ∈ T → ¬ Place.LiesOver w u) →
        ∃ (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
          (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k)),
          w = Place.ofFinite q ∧ q.asIdeal.LiesOver Q.asIdeal ∧
            q.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1) := by
  classical
  obtain ⟨Texc, hTexc⟩ := exists_finset_unramifiedPlaces k L
  let T₀ : Set (Place K) := (S : Set (Place K)) ∪ {u : Place K | ∃ w ∈ Texc,
    e9cUnder (K := K) w = u}
  have hT₀fin : T₀.Finite := by
    refine Set.Finite.union (S.finite_toSet) ?_
    refine (Texc.finite_toSet.image (fun w => e9cUnder (K := K) w)).subset ?_
    rintro u ⟨w, hw, rfl⟩
    exact ⟨w, hw, rfl⟩
  obtain ⟨G, hGfin, hGsub⟩ :=
    NK.HassePrinciple.exists_gstable_finite_superset (K := k) (L := K) T₀ hT₀fin
  refine ⟨G.carrier, hGfin, fun σ u hu => G.smul_mem' σ hu, fun u hu => hGsub (Or.inl hu), ?_⟩
  intro w hw
  have hwT : e9cUnder (K := K) w ∉ G.carrier := fun hmem =>
    hw _ hmem (e9cUnder_liesOver (K := K) w)
  have hwnot : w ∉ Texc := by
    intro hmem
    exact hwT (hGsub (Or.inr ⟨w, hmem, rfl⟩))
  exact hTexc w hwnot

/-- A choice of a representative of the orbit of a place. -/
private noncomputable def e9cRep {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] (R : Set (Place K))
    (hR : ∀ w : Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1) (u : Place K) : R :=
  Classical.choose (hR u)

private theorem e9cRep_spec {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] {R : Set (Place K)}
    (hR : ∀ w : Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1) (u : Place K) :
    ∃ σ : K ≃ₐ[k] K, σ • u = (e9cRep R hR u).1 :=
  (Classical.choose_spec (hR u)).1

private theorem e9cRep_eq_of_exists {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K] {R : Set (Place K)}
    (hR : ∀ w : Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1) (u : Place K) (v : R)
    (h : ∃ σ : K ≃ₐ[k] K, σ • v.1 = u) : v = e9cRep R hR u := by
  obtain ⟨σ, hσ⟩ := h
  have h2 : ∃ τ : K ≃ₐ[k] K, τ • u = v.1 := ⟨σ⁻¹, by rw [← hσ, inv_smul_smul]⟩
  exact (Classical.choose_spec (hR u)).2 v h2

/-! ## The assembly -/

/-- `extLoc` is additive over a `Finset` sum. -/
private theorem extLoc_sum' {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)} {r : ℕ} (u : Place K) {ι : Type}
    (s : Finset ι) (f : ι → Abelian.Ext M (idelesRepP k K) r) :
    extLoc (k := k) (K := K) u (∑ i ∈ s, f i)
      = ∑ i ∈ s, extLoc (k := k) (K := K) u (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [extLoc_zero]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, extLoc_add, ih]

/-- `extLoc` of a difference. -/
private theorem extLoc_sub' {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)} {r : ℕ} (u : Place K)
    (a b : Abelian.Ext M (idelesRepP k K) r) :
    extLoc (k := k) (K := K) u (a - b)
      = extLoc (k := k) (K := K) u a - extLoc (k := k) (K := K) u b := by
  have hneg : extLoc (k := k) (K := K) u (-b) = -extLoc (k := k) (K := K) u b := by
    have h := extLoc_add (k := k) (K := K) u (-b) b
    rw [neg_add_cancel, extLoc_zero (k := k) (K := K) u] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  rw [sub_eq_add_neg, extLoc_add, hneg, sub_eq_add_neg]

/-- `IsUnramifiedExt` of the zero class. -/
private theorem isUnramifiedExt_zero' {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    {M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)} {r : ℕ} (u : Place K) :
    IsUnramifiedExt (k := k) (K := K) u
      (0 : Abelian.Ext (Rep.res (decompK (k := k) u).subtype M) (localUnitsK (k := k) u) r) :=
  ⟨0, by rw [Abelian.Ext.zero_comp]⟩


/-- `phiAt` of the zero class. -/
private theorem phiAt_zero' {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L]
    {M : Rep.{0, 0, 0} Coeff (K ≃ₐ[k] K)}
    (h : extH (Rep.res (galRes k K L) M) 1) :
    phiAt (k := k) (K := K) (L := L)
      (0 : Abelian.Ext M (classesRepP k K) 1) h = 0 := by
  rw [phiAt, levelPair, extRes, Abelian.Ext.mapExactFunctor_zero, Abelian.Ext.zero_comp,
    Abelian.Ext.comp_zero]


/-- **E9c (the global value of a glued idèle class is the sum of its orbit pieces).**  Let
`z_v ∈ Ext¹(M, 𝕀_K)` (`v ∈ R`) be supported on the orbit of `v`, unramified at `v` when `v ∉ S`
(`S` containing the archimedean places and the places where `M` ramifies), and let `z` have the
same `R`-components (`PT.exists_glue_extLoc`).  Then at every level, only finitely many
`φ(extToClasses z_v)(h)` are nonzero, and `φ(extToClasses z)(h)` is their sum.
Route: for fixed `(L, h)` let `T` be `S` plus the places where `h` ramifies; `z - Σ_{v∈T} z_v`
has zero components over `T` and unramified components elsewhere; an unramified local class pairs
to zero with an unramified `h` (the value is inflated from `H²(D/I, 𝒪_urˣ) = 0`), so the idèle
value at level `L` has all local components zero (`PT.extLoc_yonedaPair`), hence is zero
(`ext_idele_shapiro` clause (i) at level `L`); push to `C_L`. -/
theorem e9_glue_phiAt (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (M : Rep Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (R : Set (NK.GlobalCFT.Place K))
    (hR : ∀ w : NK.GlobalCFT.Place K, ∃! w' : R, ∃ σ : K ≃ₐ[k] K, σ • w = w'.1)
    (S : Finset (NK.GlobalCFT.Place K))
    (hSarch : ∀ v : NK.GlobalCFT.Place K,
      (∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
        v ≠ NK.GlobalCFT.Place.ofFinite q) → v ∈ S)
    (hSram : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      NK.GlobalCFT.Place.ofFinite q ∉ S →
        ∀ σ : K ≃ₐ[k] K, IsInertiaAt q σ → ∀ m : M, M.ρ σ m = m)
    (zv : R → Abelian.Ext M (idelesK k K) 1)
    (hsupp : ∀ (v : R) (u : NK.GlobalCFT.Place K), (∀ σ : K ≃ₐ[k] K, σ • v.1 ≠ u) →
      extLoc u (zv v) = 0)
    (hunr : ∀ v : R, v.1 ∉ S → IsUnramifiedExt v.1 (extLoc v.1 (zv v)))
    (z : Abelian.Ext M (idelesK k K) 1) (hz : ∀ v : R, extLoc v.1 z = extLoc v.1 (zv v)) :
    ∀ (L : IntermediateField K Ω) [NumberField L] [FiniteDimensional k L] [IsGalois k L]
      (h : extH (Rep.res (galRes k K L) M) 1),
      (Function.support (fun v : R => phiAt (k := k) (K := K) (L := L)
          (extToClasses (zv v)) h)).Finite ∧
      phiAt (k := k) (K := K) (L := L) (extToClasses z) h =
        ∑ᶠ v : R, phiAt (k := k) (K := K) (L := L) (extToClasses (zv v)) h := by
  classical
  intro L _instNF _instFD _instGal h
  -- the good finite Galois-stable set of places
  obtain ⟨T, hTfin, hTsmul, hST, hram⟩ := e9c_exists_good_T k K L S
  have hRfin : {v : R | v.1 ∈ T}.Finite :=
    hTfin.preimage (f := fun v : R => v.1) (fun a _ b _ hab => Subtype.eq hab)
  let V : Finset R := hRfin.toFinset
  have hVmem : ∀ v : R, v ∈ V ↔ v.1 ∈ T := fun v => Set.Finite.mem_toFinset hRfin
  let W : Abelian.Ext M (idelesRepP k K) 1 := ∑ v ∈ V, zv v
  let y : Abelian.Ext M (idelesRepP k K) 1 := z - W
  -- the sums over `V` have a single (resp. no) surviving term
  have hsum_rep : ∀ u : Place K, u ∈ T →
      ∑ v ∈ V, extLoc (k := k) (K := K) u (zv v)
        = extLoc (k := k) (K := K) u (zv (e9cRep R hR u)) := by
    intro u hu
    refine Finset.sum_eq_single (e9cRep R hR u) ?_ ?_
    · intro v _ hvne
      exact hsupp v u (fun σ hσ => hvne (e9cRep_eq_of_exists hR u v ⟨σ, hσ⟩))
    · intro hnot
      have hmem : (e9cRep R hR u).1 ∈ T := by
        obtain ⟨σ, hσ⟩ := e9cRep_spec (R := R) hR u
        rw [← hσ]
        exact hTsmul σ hu
      exact absurd ((hVmem _).mpr hmem) hnot
  have hsum_zero : ∀ u : Place K, u ∉ T →
      ∑ v ∈ V, extLoc (k := k) (K := K) u (zv v) = 0 := by
    intro u hu
    refine Finset.sum_eq_zero (fun v hv => ?_)
    exact hsupp v u (fun σ hσ => hu (by
      have hσu : σ • v.1 ∈ T := hTsmul σ ((hVmem v).mp hv)
      rwa [hσ] at hσu))
  -- the conjugacy: the components of `z` and of its orbit pieces agree
  have hconj : ∀ u : Place K,
      extLoc (k := k) (K := K) u z
        = extLoc (k := k) (K := K) u (zv (e9cRep R hR u)) := by
    intro u
    obtain ⟨σ, hσ⟩ := e9cRep_spec (R := R) hR u
    have h0 : extLoc (k := k) (K := K) (e9cRep R hR u).1 (z - zv (e9cRep R hR u)) = 0 := by
      rw [extLoc_sub', hz (e9cRep R hR u), sub_self]
    have h1 : extLoc (k := k) (K := K) u (z - zv (e9cRep R hR u)) = 0 := by
      have h2 := e9c_extLoc_conj_zero (k := k) (K := K)
        (z := z - zv (e9cRep R hR u)) (σ := σ⁻¹) (v := (e9cRep R hR u).1) h0
      rwa [show σ⁻¹ • (e9cRep R hR u).1 = u from by rw [← hσ, inv_smul_smul]] at h2
    rw [extLoc_sub'] at h1
    exact sub_eq_zero.mp h1
  -- y vanishes on `T`
  have hTz_y : ∀ u ∈ T, extLoc (k := k) (K := K) u y = 0 := by
    intro u hu
    change extLoc (k := k) (K := K) u (z - W) = 0
    rw [extLoc_sub', extLoc_sum' u V (fun v => zv v), hsum_rep u hu, hconj u, sub_self]
  -- y is unramified everywhere
  have hy_unram : ∀ u : Place K,
      IsUnramifiedExt (k := k) (K := K) u (extLoc (k := k) (K := K) u y) := by
    refine isUnramifiedExt_of_components_unramified M 1 R hR y ?_
    intro v
    change IsUnramifiedExt (k := k) (K := K) v.1 (extLoc (k := k) (K := K) v.1 (z - W))
    by_cases hvT : v.1 ∈ T
    · rw [extLoc_sub', extLoc_sum' v.1 V (fun v' => zv v'), hsum_rep v.1 hvT, hconj v.1,
        sub_self]
      exact isUnramifiedExt_zero' v.1
    · rw [extLoc_sub', extLoc_sum' v.1 V (fun v' => zv v'), hsum_zero v.1 hvT, hz v,
        sub_zero]
      exact hunr v (fun hmem => hvT (hST v.1 hmem))
  -- the global value of `y` vanishes
  have hy0 : phiAt (k := k) (K := K) (L := L) (extToClasses y) h = 0 :=
    e9c_phiAt_eq_zero_of_local L M h T y hTz_y (fun u _ => hy_unram u) hram
  -- the orbit pieces with `v ∉ T` are globally unramified, hence have vanishing value
  have hzv_unram : ∀ v : R, v.1 ∉ T → ∀ u : Place K,
      IsUnramifiedExt (k := k) (K := K) u (extLoc (k := k) (K := K) u (zv v)) := by
    intro v hvT
    refine isUnramifiedExt_of_components_unramified M 1 R hR (zv v) ?_
    intro v'
    by_cases hvv : v' = v
    · rw [hvv]
      exact hunr v (fun hmem => hvT (hST v.1 hmem))
    · have hzero : extLoc (k := k) (K := K) v'.1 (zv v) = 0 :=
        hsupp v v'.1 (fun σ hσ => hvv (((e9cRep_eq_of_exists hR v'.1 v ⟨σ, hσ⟩).trans
          (e9cRep_eq_of_exists hR v'.1 v' ⟨1, by simp⟩).symm).symm))
      rw [hzero]
      exact isUnramifiedExt_zero' v'.1
  have hFv0 : ∀ v : R, v.1 ∉ T →
      phiAt (k := k) (K := K) (L := L) (extToClasses (zv v)) h = 0 := by
    intro v hvT
    refine e9c_phiAt_eq_zero_of_local L M h T (zv v) ?_ (fun u _ => hzv_unram v hvT u) hram
    intro u hu
    exact hsupp v u (fun σ hσ => hvT (by
      have hσu : σ⁻¹ • u ∈ T := hTsmul σ⁻¹ hu
      rwa [← hσ, inv_smul_smul] at hσu))
  -- the value of `W` is the sum of the values of the orbit pieces
  have hWval : phiAt (k := k) (K := K) (L := L) (extToClasses W) h
      = ∑ v ∈ V, phiAt (k := k) (K := K) (L := L) (extToClasses (zv v)) h := by
    have hmap : ∀ s : Finset R,
        phiAt (k := k) (K := K) (L := L) (extToClasses (∑ v ∈ s, zv v)) h
          = ∑ v ∈ s, phiAt (k := k) (K := K) (L := L) (extToClasses (zv v)) h := by
      intro s
      induction s using Finset.induction with
      | empty =>
          rw [Finset.sum_empty, Finset.sum_empty, extToClasses_zero]
          exact phiAt_zero' L h
      | insert a s ha ih =>
          rw [Finset.sum_insert ha, Finset.sum_insert ha, extToClasses_add, phiAt_add, ih]
    exact hmap V
  -- additivity in the class
  have hzy : phiAt (k := k) (K := K) (L := L) (extToClasses z) h
      = phiAt (k := k) (K := K) (L := L) (extToClasses W) h
        + phiAt (k := k) (K := K) (L := L) (extToClasses y) h := by
    rw [← show W + y = z from by change W + (z - W) = z; abel, extToClasses_add, phiAt_add]
  constructor
  · refine hRfin.subset ?_
    intro v hv
    by_contra hvT
    exact hv (hFv0 v (fun h => hvT h))
  · rw [hzy, hy0, add_zero, hWval]
    refine (finsum_eq_finsetSum_of_support_subset (s := V)
      (fun v : R => phiAt (k := k) (K := K) (L := L) (extToClasses (zv v)) h) ?_).symm
    intro v hv
    by_contra hvT
    exact hv (hFv0 v (fun h => hvT (Finset.mem_coe.mpr ((hVmem v).mpr h))))




end Work.SSGRoute
