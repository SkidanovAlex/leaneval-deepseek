import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.e9c_transport_unram
import Submission.Work.SSGRoute.eq_zero_of_isUnramifiedExt_of_unramified
import Submission.Work.SSGRoute.local_duality_ext
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

Lead guidance. The design is in the workspace at _lead_design/ssg_pt_design_1002/DESIGN.md. Read the section for your statement FIRST (§2 C6 via the induced module from the normal closure of inertia; §3 CRUX-a 3-step; §4 G1+COUNT via the canonical class-formation pairing). It gives the proof route as numbered steps and the proved workspace names to reuse (local_duality_ext_in, detectsAt_of_coeff_surjection, grunwald_over_K_general, countingIdentity_of_reciprocity_and_converse, ...). Do not re-derive what is proved.
Memory: Lean only through the harness; no sleep loops around lake.
-/

namespace Work.SSGRoute.PT

open CategoryTheory

/-! ## Two auxiliary facts about inertia in a finite place

The first identifies `SSGRoute.PTExt.IsInertiaAt` with membership in Mathlib's ideal-theoretic
inertia subgroup `Ideal.inertia`; the second extracts from triviality of that inertia group the
ramification index `e(q' | q' ∩ k) = 1` needed by the local vanishing theorem. -/

/-- `IsInertiaAt q σ` is exactly membership of `σ` in the ideal-theoretic inertia subgroup of the
finite prime `q`. -/
lemma isInertiaAt_iff_mem_inertia_local {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (σ : L ≃ₐ[k] L) :
    SSGRoute.PTExt.IsInertiaAt q σ ↔ σ ∈ Ideal.inertia (L ≃ₐ[k] L) q.asIdeal := by
  rw [Ideal.inertia, AddSubgroup.mem_inertia]
  refine forall_congr' fun x => ?_
  have key : ((σ • x - x : NumberField.RingOfIntegers L) : L) = σ (x : L) - (x : L) := by
    have h : algebraMap (NumberField.RingOfIntegers L) L (σ • x - x) =
        algebraMap (NumberField.RingOfIntegers L) L (σ • x) -
          algebraMap (NumberField.RingOfIntegers L) L x := map_sub _ _ _
    rw [show ((σ • x - x : NumberField.RingOfIntegers L) : L) =
        algebraMap (NumberField.RingOfIntegers L) L (σ • x - x) from rfl, h]
    congr 1
  rw [← key]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) (v := q) _

/-- Triviality of the inertia group at `q'` forces the ramification index of `q'` over the prime of
`k` below it to be `1`. -/
lemma ramificationIdx_under_eq_one_of_isInertiaAt {k L : Type} [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hunr : ∀ σ : L ≃ₐ[k] L, SSGRoute.PTExt.IsInertiaAt q' σ → σ = 1) :
    q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 := by
  haveI : q'.asIdeal.IsPrime := q'.isPrime
  have hprime : (q'.asIdeal.under (NumberField.RingOfIntegers k)).IsPrime :=
    Ideal.isPrime_of_liesOver (p := q'.asIdeal.under (NumberField.RingOfIntegers k)) q'.asIdeal
  haveI := hprime
  refine (Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one
    (F := k) (K := L) (q'.asIdeal.under (NumberField.RingOfIntegers k)) q'.asIdeal).mp ?_
  rw [Subgroup.eq_bot_iff_forall]
  intro σ hσ
  exact hunr σ ((isInertiaAt_iff_mem_inertia_local q' σ).mpr hσ)

/-- The finite place of `k` under `q'`. -/
noncomputable def underHeightOneSpectrum (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L]
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k) where
  asIdeal := q'.asIdeal.under (NumberField.RingOfIntegers k)
  isPrime := Ideal.isPrime_of_liesOver
    (p := q'.asIdeal.under (NumberField.RingOfIntegers k)) q'.asIdeal
  ne_bot := Ideal.under_ne_bot (A := NumberField.RingOfIntegers k) (P := q'.asIdeal) q'.ne_bot

@[simp] lemma underHeightOneSpectrum_asIdeal (k L : Type) [Field k] [NumberField k] [Field L]
    [NumberField L] [Algebra k L]
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L)) :
    (underHeightOneSpectrum k L q').asIdeal =
      q'.asIdeal.under (NumberField.RingOfIntegers k) := rfl

/-! ## Clause (6): the pairing of an unramified local class vanishes

Proof route (the hard pieces are already in the workspace, they are *not* re-derived here):

1. `ramificationIdx_under_eq_one_of_isInertiaAt`: `hunr` says the inertia group of `q'` in
   `Gal(L/k)` is trivial; via `Ideal.card_inertia_eq_ramificationIdxIn`
   (`Commons.NumberTheory.RamificationInertia.inertia_eq_bot_iff_ramificationIdx_eq_one`) this is
   `e(q' | q' ∩ k) = 1`, i.e. the local extension at `q'` is unramified over `k`.
2. `hy` splits `y = z ≫ mk₀ (𝒪_wˣ ↪ K_wˣ)`, and `Work.SSGRoute.exists_factor_localUnitsIncl`
   (which uses `hι`: `ι` is the local algebra map on units) produces `ι'` with
   `resMap f (𝒪_wˣ ↪ K_wˣ) ≫ ι = ι' ≫ (𝒪_{q'}ˣ ↪ L_{q'}ˣ)`.  The two `levelPair` functoriality
   lemmas `Work.SSGRoute.levelPair_comp_mk₀` and `Work.SSGRoute.levelPair_comp` then exhibit the
   pairing value as the image of a class of `Ext²(ℤ, 𝒪_{q'}ˣ)`: it is `IsUnramifiedExt` at `q'`.
3. `Work.SSGRoute.eq_zero_of_isUnramifiedExt_of_unramified` — namely `H²(D_{q'}, 𝒪_{q'}ˣ) = 0` for
   an unramified local extension, via Herbrand's theorem and the periodicity of the cohomology of a
   cyclic group — kills it. -/

/-- Clause (6) input: the level pairing of an unramified local class vanishes at a level that is
unramified over the base.

`y ∈ Ext¹_{D_w}(res M, K_wˣ)` comes from the integral units (`IsUnramifiedExt`), and the level
`L` has trivial inertia at the finite place `q'` of `L` over `w`.  Then for every
`h ∈ H¹(D_{w'}, res M)` the value `levelPair f ι y h ∈ H²(D_{w'}, L_{w'}ˣ)` is `0`: it is the image of
a class of `H²(D_{w'}, 𝒪_{w'}ˣ)` (because `ι` maps integral units to integral units, by `hι` and
`localAlgebraMapUnits`), and `H²` of the units of an unramified local extension vanishes (units are
cohomologically trivial: filtration by `U^{(n)}`, residue field `H²` of a finite field,
`H^i(Gal, 𝔽_qˣ)` and the additive groups `𝔽_q` are trivial for `i ≥ 1` in the cyclic/unramified
case).  No hypothesis on `h` is needed. -/
theorem levelPair_unramified_eq_zero (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (w : NK.GlobalCFT.Place K)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L]
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hw' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
    (hunr : ∀ σ : L ≃ₐ[k] L, SSGRoute.PTExt.IsInertiaAt q' σ → σ = 1)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofFinite q') →*
      SSGRoute.PTExt.decompK (k := k) w)
    (hf : ∀ σ, ((f σ : SSGRoute.PTExt.decompK (k := k) w) : K ≃ₐ[k] K) =
      SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L))
    (ι : Rep.res f (SSGRoute.PTExt.localUnitsK (k := k) w) ⟶
      NK.HassePrinciple.localUnitsRep k L (NK.GlobalCFT.Place.ofFinite q'))
    (hι : ∀ u : (NK.GlobalCFT.Place.localField K w)ˣ,
      ι.hom (Additive.ofMul u) =
        Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofFinite q') w hw' u))
    (y : CategoryTheory.Abelian.Ext (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype M)
      (SSGRoute.PTExt.localUnitsK (k := k) w) 1)
    (hy : SSGRoute.PTExt.IsUnramifiedExt w y)
    (h : SSGRoute.PTExt.extH (Rep.res f (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype M)) 1) :
    SSGRoute.PTExt.levelPair f ι y h = 0 := by
  -- The local extension at `q'` is unramified over the prime of `k` below it.
  have hunrIdx : q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers k) = 1 :=
    ramificationIdx_under_eq_one_of_isInertiaAt q' hunr
  -- Split `y` through the integral local units `𝒪_wˣ` (`hy`).
  obtain ⟨z, hz⟩ := hy
  -- `ι` carries the integral units of `K_w` into the integral units of `L_{q'}`.
  obtain ⟨ι', hι'⟩ := Work.SSGRoute.exists_factor_localUnitsIncl (k := k) (K := K) (L := L)
    w (NK.GlobalCFT.Place.ofFinite q') hw' f ι hι
  -- Hence the pairing value is the image of a class of `H²(D_{q'}, 𝒪_{q'}ˣ)`.
  have key : SSGRoute.PTExt.levelPair f ι y h
      = (SSGRoute.PTExt.levelPair f ι' z h).comp
          (CategoryTheory.Abelian.Ext.mk₀
            (Work.SSGRoute.localUnitsInclP k L (NK.GlobalCFT.Place.ofFinite q')))
          (add_zero 2) := by
    rw [hz,
      Work.SSGRoute.levelPair_comp_mk₀ f ι (Work.SSGRoute.localUnitsInclP k K w) z h, hι']
    exact Work.SSGRoute.levelPair_comp f ι'
      (Work.SSGRoute.localUnitsInclP k L (NK.GlobalCFT.Place.ofFinite q')) z h
  have hunrExt : SSGRoute.PTExt.IsUnramifiedExt (k := k) (K := L)
      (NK.GlobalCFT.Place.ofFinite q') (SSGRoute.PTExt.levelPair f ι y h) :=
    ⟨SSGRoute.PTExt.levelPair f ι' z h, key⟩
  -- `H²` of the units of an unramified local extension vanishes.
  exact Work.SSGRoute.eq_zero_of_isUnramifiedExt_of_unramified k L q'
    (underHeightOneSpectrum k L q') (Ideal.over_under q'.asIdeal) hunrIdx _ hunrExt

end Work.SSGRoute.PT
