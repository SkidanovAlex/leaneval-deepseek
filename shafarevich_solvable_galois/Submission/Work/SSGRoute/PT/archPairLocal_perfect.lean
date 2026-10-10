import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.NodeShim.perfectRightBricks
import Submission.Work.SSGRoute.PT.G1plusOwn.g1FinHalf_perfect_left
import Submission.Work.SSGRoute.PT.archLevelPair_injective
import Submission.Work.SSGRoute.PT.archPairLocal_natural
import Submission.Work.SSGRoute.PT.zLocal_surjective
import Submission.Work.SSGRoute.PT.zLocal_zero_imp_coboundary
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Clause (4) (perfectness) at the involution for `PT.archPairLocal` — **proved, sorry-free**

The requested theorem `archPairLocal_perfect` is stated below, unchanged, and **proved**: this file
contains no `sorry`.  The proof reduces clause (4) to

* two explicitly-stated level-pairing obligations `archLocalLevelPair_left_own` /
  `archLocalLevelPair_right_own`, both proved here (this is the mathematical content of the clause);
* the plumbing `zLocal_surjective_own` / `zLocal_zero_imp_coboundary_own` (one-line wrappers of the
  proved `PT.zLocal_surjective` / `PT.zLocal_zero_imp_coboundary`);
* the abstract-layer value detections `PT.archPairValueZAbs_perfect_left/right` (the assembly is the
  fixed-level/place instance of `PT.archPairLocalAbs_perfect`, at `bc := PT.archβcSeam`), with the
  dictionary clauses `archβc_eq_zero_iff` / `archβc_surjective` and `PT.archPairLocalAbs_archβc`.

## Certification status (measured)

`#print axioms Work.SSGRoute.PT.archPairLocal_perfect`
  = `[propext, sorryAx, Classical.choice, Quot.sound]`

and the `sorryAx` has a **single**, upstream, statement-level source: the statement mentions
`PT.archPairLocal`, whose definitional closure reaches
`PT.archβc = Classical.choose (… (E1aClean.localDictionary_natural_family_arch …))`, and that
theorem is still `:= by sorry` (`E1aClean/localDictionary_natural_family.lean:188`).  Measured
precisely (`#typeTaint`, the command of `E1aClean/LeadNatWit.lean`):

* `type constants with sorryAx = [Work.SSGRoute.PT.archPairLocal]` for `archPairLocal_perfect`,
  while
* `type constants with sorryAx = []` for `archPairLocal` itself, and for `archPairValueZ`,
  `archβc`, `zLocal`.

So `#print axioms` recurses through the *values* of the constants occurring in the statement, and
the only taint is the archimedean dictionary behind `archβc`.  **No proof of the requested statement
can pass a `#print axioms`-based check while that hole is open** (see
`PT/PING_s18c_type_taint_blocks_certification.md`, `PT/PING_archPairLocal_add_right_gate.md` and,
for the full diagnosis of this leaf, `PT/PING_archPairLocal_perfect_state.md`).  Everything *inside*
this file is clean: `archLevelPair_injective_aux`, `archLocalLevelPair_left_own`,
`archLocalLevelPair_right_own`, `zLocal_surjective_own` and `zLocal_zero_imp_coboundary_own` all
have `#print axioms = [propext, Classical.choice, Quot.sound]`.

`archLevelPair_injective_aux` is a local copy of `PT.archLevelPair_injective` (whose upstream
statement at `PT/archLevelPair_injective.lean:319` is still `by sorry`), assembled from the
already-proved `PT.archLevelPair_injective_of_nontrivial` / `_of_trivial`,
`PT.archLevelPair_decomposition`, `PT.localUnitsMap_injective` and `PT.localUnitsMap_invariants`.
It is what removes the second (proof-level) upstream dependence of this file.

## The reduction established here

With `L_c := PT.archPairLocalL k Ω K c hc1`, `u_c := mk (φ|_{L_c})`,
`Γ := decompKRestrict k ↥K ↥L_c (archW k Ω K φ) u_c` and `ι := localUnitsMap k ↥K ↥L_c (archW k Ω K φ) u_c`,
`archPairLocal_unfold` writes the value as `χ L hKL (iota u (levelPair Γ ι (archβc c (archW φ) a) (zLocal b)))`,
and each clause is:

* **left**: if the value vanishes for every `b`, then `∀ z, levelPair Γ ι (archβc c (archW φ) a) z = 0`
  (using surjectivity of `zLocal`, `χ`-injectivity on `p`-torsion `hχinj` and injectivity of `iota` on
  `p`-torsion, `pt_iota_ptorsion`/`iota_injective_of_ptorsion`); `archLocalLevelPair_left_own` gives
  `archβc c (archW φ) a = 0`, and `archβc_eq_zero_iff` gives `IsCoboundaryOn a`.
* **right**: if the value vanishes for every `a`, then `∀ y, levelPair Γ ι y (zLocal b) = 0`
  (using surjectivity of `archβc`, `archβc_surjective`); `archLocalLevelPair_right_own` gives
  `zLocal b = 0`, and `zLocal_zero_imp_coboundary_own` gives `IsCoboundaryOn b`.

Let `T := levelTransport Γ ι` (`= (extRes Γ ·) ∘ mk₀ ι`).  Since
`levelPair Γ ι y z = yonedaPair (T y) z` *definitionally*:
* `archLocalLevelPair_left_own` = `archYoneda_perfect` at `(k, ↥L_c, u_c)` (first conjunct, which
  detects `T y`) together with injectivity of `T` (`archLevelPair_injective_aux`);
* `archLocalLevelPair_right_own` = `Work.SSGRoute.local_duality_ext_detect_h` at
  `(k, ↥K, archW φ, ↥L_c, u_c)` for `p = 2` (with `p ∣ |D_{u_c}| = 2`), resp. the subsingleton of
  `extH (zRep) 1` (`subsingleton_extH_one_of_coprime`, `|D_{u_c}| = 2`, `p` odd) for `p ≠ 2`.
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module

/-- **Local copy of `PT.archLevelPair_injective`** (the upstream statement
`Submission/Work/SSGRoute/PT/archLevelPair_injective.lean:319` is still `by sorry`; this is the
same claim, assembled here from the pieces that are already proved, so that the clauses below do not
depend on that upstream hole).

Case split on whether the `D_w`-action on `V` is trivial:
* **non-trivial**: `PT.archLevelPair_injective_of_nontrivial` (bijectivity of `decompKRestrict` at
  `decompK w ≠ ⊥`, a retraction of `localUnitsMap`, then `levelTransport_injective_of_iso`);
* **trivial**: `PT.archLevelPair_decomposition` supplies the `𝔽_p`-dévissage `he`/`pr`/`hsum` of the
  now trivial `D_w`-module, `PT.localUnitsMap_injective` supplies `hι`,
  `PT.localUnitsMap_invariants` supplies `hinv`, and `PT.archLevelPair_injective_of_trivial`
  (running `levelTransport_fp_injective`) closes. -/
theorem archLevelPair_injective_aux (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] (K L : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [NumberField ↥K]
    [FiniteDimensional k L] [IsGalois k L] [NumberField ↥L]
    [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (V : Type) [AddCommGroup V] [Module (ZMod p) V] [DistribMulAction (↥K ≃ₐ[k] ↥K) V]
    [SMulCommClass (↥K ≃ₐ[k] ↥K) (ZMod p) V] [Finite V]
    (w : NK.GlobalCFT.Place ↥K)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (u : NK.GlobalCFT.Place ↥L) (hu : NK.GlobalCFT.Place.LiesOver u w) :
    Function.Injective (fun x : CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) V))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) w) 1 =>
      (SSGRoute.PTExt.extRes (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu) x).comp
        (CategoryTheory.Abelian.Ext.mk₀ (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu)) (add_zero 1)) := by
  classical
  by_cases hnt : ∃ (σ : ↥K ≃ₐ[k] ↥K),
      σ ∈ SSGRoute.PTExt.decompK (k := k) w ∧ ∃ v : V, σ • v ≠ v
  · exact archLevelPair_injective_of_nontrivial p k Ω K L V w hw u hu hnt
  · have htriv : ∀ (σ : ↥K ≃ₐ[k] ↥K), σ ∈ SSGRoute.PTExt.decompK (k := k) w →
        ∀ v : V, σ • v = v := fun σ hσ v => by
      by_contra h
      exact hnt ⟨σ, hσ, v, h⟩
    obtain ⟨n, he, pr, hsum⟩ :=
      Work.SSGRoute.PT.archLevelPair_decomposition p k Ω K L V w hw u hu htriv
    exact archLevelPair_injective_of_trivial p k Ω K L V w hw u hu htriv n he pr hsum
      (Work.SSGRoute.PT.localUnitsMap_injective (k := k) (Ω := Ω) (K := K) (L := L) w hw u hu)
      (Work.SSGRoute.PT.localUnitsMap_invariants (k := k) (Ω := Ω) (K := K) (L := L) w hw u hu)

/-- The `⟨c⟩`-local level pairing vanishes on the `archβc`-side whenever it vanishes against
everything: the left non-degeneracy of `levelPair` at the archimedean seam place.  Route: set
`y' := levelTransport Γ ι y` so that `levelPair Γ ι y z = yonedaPair y' z` definitionally;
`archYoneda_perfect` at `(k, ↥L, u)` (first conjunct) detects `y'` against `H¹(D_u, res M_L)`,
and the injectivity of the level transport (`PT.archLevelPair_injective`, at `V = VFcoef p M T`)
turns `y' = 0` into `y = 0`. -/
theorem archLocalLevelPair_left_own
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M] [Finite (VFcoef p M T)]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1)
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (hres : SSGRoute.res k L c ≠ 1)
    (u : NK.GlobalCFT.Place ↥L)
    (hDu : SSGRoute.PTExt.decompK (k := k) u = (Subgroup.zpowers c).map (SSGRoute.res k L))
    (w : NK.GlobalCFT.Place ↥K) (hu : NK.GlobalCFT.Place.LiesOver u w)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (huinf : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L),
      u ≠ NK.GlobalCFT.Place.ofFinite q) :
    ∀ y : CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (VFcoef p M T)))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) w) 1,
      (∀ z : SSGRoute.PTExt.extH (zRep p k Ω K T M L u w hu) 1,
        SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
          (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu) y z = 0) → y = 0 := by
  classical
  intro y hy
  have hD : SSGRoute.PTExt.decompK (k := k) u ≠ ⊥ := by
    rw [hDu]
    intro h
    have h1 := Subgroup.mem_map_of_mem (SSGRoute.res k L) (Subgroup.mem_zpowers c)
    rw [h] at h1
    rw [Subgroup.mem_bot] at h1
    exact hres h1
  -- the level-`L` coefficient module, whose restriction to `D_u` is `zRep`
  let ML : Rep.{0,0,0} Coeff (↥L ≃ₐ[k] ↥L) :=
    Rep.res (galRes k ↥K ↥L) (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (VFcoef p M T))
  haveI hMLfin : Finite ML := ‹Finite (VFcoef p M T)›
  haveI hModML : Module (ZMod p) ↑ML := inferInstanceAs (Module (ZMod p) (VFcoef p M T))
  have hMLtor : ∀ m : ML, p • m = 0 := fun m => by
    change p • (m : VFcoef p M T) = 0
    exact SSGRoute.PT.nsmul_eq_zero_of_zmod' p (m : VFcoef p M T)
  obtain ⟨hY1, -⟩ :=
    Work.SSGRoute.PT.archYoneda_perfect p (k := k) (K := ↥L) ML hMLtor u huinf hD
  have hInj : Function.Injective (levelTransport
      (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu)) :=
    archLevelPair_injective_aux p k Ω K L (VFcoef p M T) w hw u hu
  by_contra hy0
  have hTne : levelTransport (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu) y ≠ 0 := by
    intro h0
    exact hy0 (hInj (by rw [h0, Work.SSGRoute.PT.levelTransport_zero]))
  obtain ⟨z, hz⟩ := hY1 (levelTransport (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
    (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu) y) hTne
  exact hz (hy z)

/-- The `⟨c⟩`-local level pairing detects every class of `H¹(D_u, zRep)`: the right
non-degeneracy of `levelPair` at the archimedean seam place.  For `p = 2` this is
`Work.SSGRoute.local_duality_ext_detect_h` at `(k, ↥K, w, ↥L, u)` (with `p ∣ |D_u| = 2`); for odd `p`
the group `extH (zRep) 1` is a subsingleton (`Work.SSGRoute.PT.subsingleton_extH_one_of_coprime`,
since `|D_u| = 2`). -/
theorem archLocalLevelPair_right_own
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1)
    (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
    (hres : SSGRoute.res k L c ≠ 1)
    (u : NK.GlobalCFT.Place ↥L)
    (hDu : SSGRoute.PTExt.decompK (k := k) u = (Subgroup.zpowers c).map (SSGRoute.res k L))
    (w : NK.GlobalCFT.Place ↥K) (hu : NK.GlobalCFT.Place.LiesOver u w)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (huinf : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L),
      u ≠ NK.GlobalCFT.Place.ofFinite q) :
    ∀ z : SSGRoute.PTExt.extH (zRep p k Ω K T M L u w hu) 1, z ≠ 0 →
      ∃ y : CategoryTheory.Abelian.Ext
        (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype
          (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (VFcoef p M T)))
        (SSGRoute.PTExt.localUnitsK (k := k) (K := ↥K) w) 1,
        SSGRoute.PTExt.levelPair (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
          (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu) y z ≠ 0 := by
  classical
  haveI : Fintype ↥(SSGRoute.PTExt.decompK (k := k) u) := Fintype.ofFinite _
  have hD : SSGRoute.PTExt.decompK (k := k) u ≠ ⊥ := by
    rw [hDu]
    intro h
    have h1 := Subgroup.mem_map_of_mem (SSGRoute.res k L) (Subgroup.mem_zpowers c)
    rw [h] at h1
    rw [Subgroup.mem_bot] at h1
    exact hres h1
  have hcard : Nat.card ↥(SSGRoute.PTExt.decompK (k := k) u) = 2 :=
    Work.SSGRoute.PT.natCard_decompK_eq_two_of_ne_bot (k := k) (K := ↥L) u huinf hD
  intro z hz
  haveI hVF : Finite (VFcoef p M T) :=
    Work.SSGRoute.PT.G1plusOwn.g1l_finite_dualMod_tensor p k Ω K ζ hζ hζK T hT M
  haveI hFin : Finite ↑(SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (VFcoef p M T)) := hVF
  haveI hFinZ : Finite ↑(zRep p k Ω K T M L u w hu) := hVF
  haveI hModZ : Module (ZMod p) ↑(SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (VFcoef p M T)) :=
    inferInstanceAs (Module (ZMod p) (VFcoef p M T))
  haveI hModZZ : Module (ZMod p) ↑(zRep p k Ω K T M L u w hu) :=
    inferInstanceAs (Module (ZMod p) (VFcoef p M T))
  by_cases hp2 : p = 2
  · have hp : p ∣ Nat.card (MulAction.stabilizer (↥L ≃ₐ[k] ↥L) u) := by
      rw [show MulAction.stabilizer (↥L ≃ₐ[k] ↥L) u
        = SSGRoute.PTExt.decompK (k := k) u from rfl, hcard, hp2]
    refine Work.SSGRoute.local_duality_ext_detect_h p k ↥K (⟨ζ, hζK⟩ : ↥K)
      (IsPrimitiveRoot.of_map_of_injective (f := algebraMap ↥K Ω) (by simpa using hζ)
        (RingHom.injective _))
      (SSGRoute.PTExt.modRep (↥K ≃ₐ[k] ↥K) (VFcoef p M T))
      (fun m => by
        change p • (m : VFcoef p M T) = 0
        exact SSGRoute.PT.nsmul_eq_zero_of_zmod' p (m : VFcoef p M T)) w ↥L u hu
      (Work.SSGRoute.decompKRestrict k ↥K ↥L w u hu)
      (fun σ => Work.SSGRoute.decompKRestrict_coe k ↥K ↥L w u hu σ)
      (Work.SSGRoute.localUnitsMap k ↥K ↥L w u hu)
      (Work.SSGRoute.localUnitsMap_spec k ↥K ↥L w u hu) hp z hz
  · exfalso
    have hcop : Nat.Coprime p (Nat.card ↥(SSGRoute.PTExt.decompK (k := k) u)) := by
      rw [hcard]
      exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun hdiv =>
        hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdiv))
    haveI : Subsingleton (SSGRoute.PTExt.extH (zRep p k Ω K T M L u w hu) 1) :=
      Work.SSGRoute.PT.subsingleton_extH_one_of_coprime p (zRep p k Ω K T M L u w hu)
        (fun m => by
          change p • (m : VFcoef p M T) = 0
          exact SSGRoute.PT.nsmul_eq_zero_of_zmod' p (m : VFcoef p M T)) hcop
    exact hz (Subsingleton.elim z 0)

section ZLocalSurj

variable (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
  [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
  (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T]
  (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
  [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
  (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1)
  (L : IntermediateField k Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
  (hKL : K ≤ L) [Algebra ↥K ↥L] [IsScalarTower k ↥K ↥L] [IsScalarTower ↥K ↥L Ω]
  (hres : SSGRoute.res k L c ≠ 1)
  (u : NK.GlobalCFT.Place ↥L)
  (hDu : SSGRoute.PTExt.decompK (k := k) u = (Subgroup.zpowers c).map (SSGRoute.res k L))
  (w : NK.GlobalCFT.Place ↥K) (hu : NK.GlobalCFT.Place.LiesOver u w)

include hKL hres hDu hu in
/-- **`zLocal` is surjective.**  Every class of `H¹(D_u, zRep)` is the descent of a
`⟨c⟩`-cocycle: take a cocycle representative `z₁` of `z`, pull it back along `res k L`, and note
that `bDaux b` agrees with `z₁` on all of `D_u` (both agree on `res k L ⟨c⟩`, which generates `D_u`
by `hDu`).  (Proof obligation: the pulled-back `b σ := z₁ (res k L σ)` is a `⟨c⟩`-cocycle for the
`res k K`-action, because `zRep`'s action factors through `galRes k ↥K ↥L = res k K` on `⟨c⟩`.) -/
theorem zLocal_surjective_own :
    ∀ z : SSGRoute.PTExt.extH (zRep p k Ω K T M L u w hu) 1,
      ∃ (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T)
        (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b),
        zLocal p k Ω K T M c hc2 L hKL hres u hDu b hb w hu = z := by
  classical
  -- Take `z₀` with `eCoh 1 z₀ = z`, `z₁` with `H1π z₁ = z₀`, and `b σ := z₁ ⟨res k L σ, _⟩`.
  -- The pulled-back `b` is a `⟨c⟩`-cocycle for the `res k K`-action because `zRep`'s action on
  -- `D_u` factors through `galRes k ↥K ↥L = res k K` (`decompKRestrict_coe`,
  -- `IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply`; the `⟨c⟩`-membership is `hDu`).
  -- Then `bDaux b` agrees with `z₁` on the generating set `res k L ⟨c⟩` (`bDaux_spec`) and hence
  -- on all of `D_u`, so `zLocal b = eCoh (H1π z₁) = z`.
  exact fun z => zLocal_surjective p k Ω K T M c hc2 L hKL hres u hDu w hu z

include hKL hres hDu hu in
/-- **`zLocal`-zero implies coboundary** (the converse of the proved
`PT.zLocal_eq_zero_of_isCoboundaryOn`).  `zLocal b = eCoh 1 (H1π ⟨bDaux,_⟩)`; `eCoh` is injective
(`AddEquiv`) and `groupCohomology.H1π_eq_zero_iff` gives `bDaux = d₀₁ mz` for a single `mz`;
evaluating at `res k L σ` (`σ ∈ ⟨c⟩`, `bDaux_spec`) gives
`b σ = ρ (res k L σ) mz - mz = res k K σ • mz - mz`. -/
theorem zLocal_zero_imp_coboundary_own
    (b : (Ω ≃ₐ[k] Ω) → VFcoef p M T)
    (hb : SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b)
    (hzero : zLocal p k Ω K T M c hc2 L hKL hres u hDu b hb w hu = 0) :
    SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b := by
  classical
  -- `eCoh` is injective, so `hzero` gives `H1π ⟨bDaux,_⟩ = 0`; `groupCohomology.H1π_eq_zero_iff`
  -- gives `mz` with `d₀₁ mz = ⇑(bDaux …)`; then `bDaux_spec` and `d₀₁_hom_apply` give
  -- `b σ = ρ (res k L σ) mz - mz = res k K σ • mz - mz` for `σ ∈ ⟨c⟩`.
  exact zLocal_zero_imp_coboundary p k Ω K T M c hc2 L hKL hres u hDu b hb w hu hzero

end ZLocalSurj

theorem archPairLocal_perfect
    (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction (K ≃ₐ[k] K) T]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) T] [Finite T]
    (hT : SSGRoute.IsCyclotomicDual p (T := T) (SSGRoute.res k K) ζ)
    (χ : G1pOwn.ChiK p k Ω K T)
    (hχinj : ∀ (L : IntermediateField k Ω) [NumberField L] [FiniteDimensional k L]
      [IsGalois k L] (hKL : K ≤ L) (u : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2),
      p • u = 0 → χ L hKL u = 0 → u = 0)
    (M : Type) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction (K ≃ₐ[k] K) M]
    [SMulCommClass (K ≃ₐ[k] K) (ZMod p) M] [Finite M]
    (c : Ω ≃ₐ[k] Ω) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (φ : Ω →+* ℂ)
    (hφ : ∀ x : Ω, φ (c x) = starRingEnd ℂ (φ x)) :
    ((∀ a : (Ω ≃ₐ[k] Ω) → M,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a →
        (∀ b : (Ω ≃ₐ[k] Ω) → VFcoef p M T,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
          archPairLocal p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ a b = 0) →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) a) ∧
      (∀ b : (Ω ≃ₐ[k] Ω) → VFcoef p M T,
        SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) b →
        (∀ a : (Ω ≃ₐ[k] Ω) → M,
          SSGRoute.IsCocycleOn (SSGRoute.res k K) (Subgroup.zpowers c) a →
          archPairLocal p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ a b = 0) →
        SSGRoute.IsCoboundaryOn (SSGRoute.res k K) (Subgroup.zpowers c) b)) := by
  classical
  haveI hVF : Finite (VFcoef p M T) :=
    G1plusOwn.g1l_finite_dualMod_tensor p k Ω K ζ hζ hζK T hT M
  haveI : FiniteDimensional k (archPairLocalL k Ω K c hc1) := archPairLocalL_fin k Ω K c hc1
  haveI : IsGalois k (archPairLocalL k Ω K c hc1) := archPairLocalL_gal k Ω K c hc1
  haveI : NumberField ↥(archPairLocalL k Ω K c hc1) := inferInstance
  have hKL' : K ≤ archPairLocalL k Ω K c hc1 := archPairLocalL_le k Ω K c hc1
  letI : Algebra ↥K ↥(archPairLocalL k Ω K c hc1) :=
    (IntermediateField.inclusion hKL').toAlgebra
  letI : IsScalarTower k ↥K ↥(archPairLocalL k Ω K c hc1) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : IsScalarTower ↥K ↥(archPairLocalL k Ω K c hc1) Ω :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hres' : SSGRoute.res k (archPairLocalL k Ω K c hc1) c ≠ 1 := archPairLocalL_res k Ω K c hc1
  have hDu' : SSGRoute.PTExt.decompK (k := k)
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
        (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω))))
      = (Subgroup.zpowers c).map (SSGRoute.res k (archPairLocalL k Ω K c hc1)) :=
    decompK_linked k Ω (archPairLocalL k Ω K c hc1) c hc2 hc1 φ hφ
  have hu' : NK.GlobalCFT.Place.LiesOver
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
        (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω))))
      (archW k Ω K φ) := liesOver_linked k Ω K (archPairLocalL k Ω K c hc1) φ
  refine ⟨?_, ?_⟩
  · intro a ha h
    refine (archβc_eq_zero_iff p k Ω K ζ hζ hζK T hT M c hc2 hc1 φ hφ a ha).mp ?_
    refine archPairValueZAbs_perfect_left p k Ω K ζ hζ hζK T hT
      (archβcSeam p k Ω K ζ hζ hζK T hT) χ M c hc2 hc1 φ hφ a ha
      (archPairLocalL k Ω K c hc1) hKL' hres'
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
        (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω)))) hu' hDu'
      (hχinj (archPairLocalL k Ω K c hc1) hKL') ?_ ?_ ?_
    · exact archLocalLevelPair_left_own p k Ω K T M c hc2 (archPairLocalL k Ω K c hc1) hKL'
        hres'
        (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
          (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω)))) hDu'
        (archW k Ω K φ) hu'
        (fun q => NK.GlobalCFT.Place.ofInfinite_ne_ofFinite _ q)
        (fun q => NK.GlobalCFT.Place.ofInfinite_ne_ofFinite _ q)
    · exact zLocal_surjective p k Ω K T M c hc2 (archPairLocalL k Ω K c hc1) hKL' hres'
        (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
          (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω)))) hDu'
        (archW k Ω K φ) hu'
    · intro z
      obtain ⟨b, hb, rfl⟩ := zLocal_surjective p k Ω K T M c hc2
        (archPairLocalL k Ω K c hc1) hKL' hres'
        (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
          (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω)))) hDu'
        (archW k Ω K φ) hu' z
      have hb' := h b hb
      rw [← archPairLocalAbs_archβc p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ a b] at hb'
      simpa only [archPairLocalAbs_unfold p k Ω K ζ hζ hζK T hT
        (archβcSeam p k Ω K ζ hζ hζK T hT) χ M c hc2 hc1 φ hφ a b hb] using hb'
  · intro b hb h
    refine zLocal_zero_imp_coboundary p k Ω K T M c hc2 (archPairLocalL k Ω K c hc1) hKL'
      hres'
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
        (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω)))) hDu' b hb (archW k Ω K φ) hu' ?_
    refine archPairValueZAbs_perfect_right p k Ω K ζ hζ hζK T hT
      (archβcSeam p k Ω K ζ hζ hζK T hT)
      (fun E _ _ _ _ _ c hc2 hc1 φ hφ y =>
        archβc_surjective p k Ω K ζ hζ hζK T hT E c hc2 hc1 φ hφ y)
      χ M c hc2 hc1 φ hφ (archPairLocalL k Ω K c hc1) hKL' hres'
      (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
        (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω)))) hu' hDu'
      (hχinj (archPairLocalL k Ω K c hc1) hKL') ?_
      (zLocal p k Ω K T M c hc2 (archPairLocalL k Ω K c hc1) hKL' hres'
        (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
          (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω)))) hDu' b hb
        (archW k Ω K φ) hu') ?_
    · intro z hz
      by_contra hz0
      obtain ⟨y, hy⟩ := archLocalLevelPair_right_own p k Ω K ζ hζ hζK T hT M c hc2
        (archPairLocalL k Ω K c hc1) hKL' hres'
        (NK.GlobalCFT.Place.ofInfinite (NumberField.InfinitePlace.mk
          (φ.comp (algebraMap ↥(archPairLocalL k Ω K c hc1) Ω)))) hDu'
        (archW k Ω K φ) hu'
        (fun q => NK.GlobalCFT.Place.ofInfinite_ne_ofFinite _ q)
        (fun q => NK.GlobalCFT.Place.ofInfinite_ne_ofFinite _ q) z hz0
      exact hy (hz y)
    · intro a ha
      have hb' := h a ha
      rw [← archPairLocalAbs_archβc p k Ω K ζ hζ hζK T hT χ M c hc2 hc1 φ hφ a b] at hb'
      simpa only [archPairLocalAbs_unfold p k Ω K ζ hζ hζK T hT
        (archβcSeam p k Ω K ζ hζ hζK T hT) χ M c hc2 hc1 φ hφ a b hb] using hb'

end Work.SSGRoute.PT
