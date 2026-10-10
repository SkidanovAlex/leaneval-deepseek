import Mathlib.GroupTheory.Nilpotent
import Mathlib.RepresentationTheory.Coinduced
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.Work.SSGRoute.C6Detector.block_iff_of_concentrated
import Submission.Work.SSGRoute.C6Detector.exists_leftCosetRepresentative
import Submission.Work.SSGRoute.TPatom.blockSystemTransversal
import Submission.Work.SSGRoute.TPatom.levelCocycleDatum_of_blockData
import Submission.Work.SSGRoute.TPatom.noninvariantLevelDefs
import Submission.Work.SSGcrux.mackeyInvDirac
import Submission.Work.SSGcrux.muDirac_ne_zero_of_doubleCoset
import Submission.Work.SSGcrux.zmodAddHom_ne_zero

/-!
# Wiring the concentrated level data into the level-cocycle datum

**Local copy.**  This is `Submission.Work.SSGRoute.C6Detector.wiringNoninvariant` re-homed in the
`Work.Sha2Lib.C6Wiring` namespace with one change: the import of
`Submission.Work.SSGcrux.noninvariantLevelDatum` is dropped (it is a heavy assembly module whose own
import cone carries the still-in-flux `Submission.Work.SSGRoute.C6Detector.rankOneLevelDatumAlgClosure`),
and the single use made of it — the two-line place-theoretic lemma `isInertiaAt_galRes` — is
re-proved locally below.  Everything else is verbatim.

This file contains the *wiring* half of the non-invariant case of node `C6`: from

* the concentrated level data (level `L ⊇ K` inside a fixed algebraically closed ambient `Ω`,
  a place `q' | q` with `p ∤ e(q'|q)`, the element `d ∈ D_{q'}` with `d^f ∈ H = N.comap (galRes)`,
  and the concentrated character `y : H →* 𝔽_p`)
* and the `μ`-detection of the block of `γ`,

it produces `PTdualControl.LevelCocycleDatum` for the coinduced permutation module
`M = coInd_N^{Gal(K/k)} 𝔽_p`, by an application of the *proved*
`TPatom.levelCocycleDatum_of_blockData`.
-/

namespace Work.Sha2Lib.C6Wiring

open CategoryTheory SSGRoute.PTExt

attribute [local instance] Classical.decEq

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- **Inertia descends along restriction** (local copy of the two-line place-theoretic API needed
here, so that this module does not depend on `Submission.Work.SSGcrux.noninvariantLevelDatum`). -/
theorem isInertiaAt_galRes {k K L : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq' : q'.asIdeal.LiesOver q.asIdeal)
    (γ : L ≃ₐ[k] L) (hγ : SSGRoute.PTExt.IsInertiaAt q' γ) :
    SSGRoute.PTExt.IsInertiaAt (k := k) q (SSGRoute.PTExt.galRes k K L γ) := by
  haveI : FiniteDimensional K L := FiniteDimensional.right k K L
  exact SSGRoute.E9Nodes.e9_inertia_restrict k K L q q' hq' γ (SSGRoute.PTExt.galRes k K L γ)
    (fun x => (AlgEquiv.restrictNormal_commutes γ K x).symm) hγ

/-- The coefficient module `M = coInd_N^{Γ} 𝔽_p` of the rank-one brick, `Γ = Gal(K/k)`. -/
noncomputable abbrev coindMod (p : ℕ) (N : Subgroup (K ≃ₐ[k] K)) :
    Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) :=
  Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p))

/-- The trivial representation of `↥N` on `𝔽_p`, the coefficient module of the Shapiro model. -/
noncomputable abbrev coindCoeff (p : ℕ) (N : Subgroup (K ≃ₐ[k] K)) :
    Rep.{0} SSGRoute.PTExt.Coeff ↥N :=
  Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)

/-- The kernel of the inclusion `↥N → Γ` acts trivially on `𝔽_p`; the hypothesis of the Dirac
construction. -/
noncomputable abbrev coindKer (p : ℕ) (N : Subgroup (K ≃ₐ[k] K)) :
    Work.SSGRoute.C6ValueFormula.KerActsTrivially N.subtype (coindCoeff (K := K) p N) :=
  fun _ _ _ => rfl

/-- The Dirac element of `coInd_N^Γ 𝔽_p` at the left coset `N γ` with value `a`. -/
noncomputable abbrev coindDirac (p : ℕ) (N : Subgroup (K ≃ₐ[k] K)) (γ : K ≃ₐ[k] K)
    (a : ZMod p) : (coindMod (K := K) p N).V :=
  Work.SSGRoute.C6ValueFormula.dirac N.subtype (coindCoeff (K := K) p N) (coindKer (K := K) p N)
    γ a

/-- The Dirac element as an additive homomorphism in its value. -/
noncomputable abbrev coindDiracHom (p : ℕ) (N : Subgroup (K ≃ₐ[k] K)) (γ : K ≃ₐ[k] K) :
    ZMod p →+ (coindMod (K := K) p N).V :=
  Work.Sha2Lib.diracHom (coindCoeff (K := K) p N) (coindKer (K := K) p N) γ

/-- The Dirac vanishes off its coset. -/
lemma coindDirac_apply_of_not (p : ℕ) (N : Subgroup (K ≃ₐ[k] K)) (x : K ≃ₐ[k] K) (a : ZMod p)
    {γ : K ≃ₐ[k] K} (h : ¬ ∃ d : N, (d : K ≃ₐ[k] K) * x = γ) :
    (coindDirac (K := K) p N x a : (K ≃ₐ[k] K) → ZMod p) γ = 0 :=
  Work.SSGRoute.C6ValueFormula.dirac_apply_of_not N.subtype (coindCoeff (K := K) p N)
    (coindKer (K := K) p N) x a h

/-- The Dirac takes the value prescribed by any witness of its coset. -/
lemma coindDirac_apply_eq (p : ℕ) (N : Subgroup (K ≃ₐ[k] K)) (x : K ≃ₐ[k] K) (a : ZMod p)
    {γ : K ≃ₐ[k] K} {d : N} (hd : (d : K ≃ₐ[k] K) * x = γ) :
    (coindDirac (K := K) p N x a : (K ≃ₐ[k] K) → ZMod p) γ = a :=
  Work.SSGRoute.C6ValueFormula.dirac_apply_eq N.subtype (coindCoeff (K := K) p N)
    (coindKer (K := K) p N) x a hd

/-- The Diracs are translates of the Dirac at the identity: `δ_{x,a} = x⁻¹ · δ_{1,a}`. -/
lemma coindDirac_eq_smul (p : ℕ) (N : Subgroup (K ≃ₐ[k] K)) (x : K ≃ₐ[k] K) (a : ZMod p) :
    coindDirac (K := K) p N x a =
      (coindMod (K := K) p N).ρ x⁻¹ (coindDirac (K := K) p N 1 a) :=
  Work.SSGRoute.C6ValueFormula.dirac_eq_smul N.subtype (coindCoeff (K := K) p N)
    (coindKer (K := K) p N) x a

/-- The Dirac at the coset of `x` takes the value `a` at `x`. -/
@[simp]
lemma coindDirac_self (p : ℕ) (N : Subgroup (K ≃ₐ[k] K)) (x : K ≃ₐ[k] K) (a : ZMod p) :
    (coindDirac (K := K) p N x a : (K ≃ₐ[k] K) → ZMod p) x = a :=
  Work.SSGRoute.C6ValueFormula.dirac_apply_self N.subtype (coindCoeff (K := K) p N)
    (coindKer (K := K) p N) x a

/-- **An additive homomorphism out of `ℤ/p` vanishing at `1` vanishes identically.**  (`ℤ/p` is
generated as an additive group by `1`.) -/
lemma zmod_addHom_eq_zero {p : ℕ} [NeZero p] {M : Type} [AddCommGroup M] (f : ZMod p →+ M)
    (h : f 1 = 0) : ∀ a : ZMod p, f a = 0 := by
  intro a
  have h2 : a = a.val • (1 : ZMod p) := by
    rw [nsmul_eq_mul, mul_one]
    exact (ZMod.natCast_zmod_val a).symm
  rw [h2, map_nsmul, h, nsmul_zero]

/-- **The `μ`-detecting coset exists.**  A non-zero `D_w`-equivariant functional on
`coInd_N^Γ 𝔽_p` is non-zero on some Dirac element. -/
theorem exists_coindDirac_apply_ne_zero (p : ℕ) [Fact p.Prime] (N : Subgroup (K ≃ₐ[k] K))
    (w : NK.GlobalCFT.Place K)
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
        (coindMod (K := K) p N) ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (hμ : μ ≠ 0) :
    ∃ γ : K ≃ₐ[k] K, μ.hom (coindDirac (K := K) p N γ 1) ≠ 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨rep, hrep1, hrep2⟩ := Work.SSGRoute.C6Detector.exists_leftCosetRepresentative N
  have hrep : ∀ γ : K ≃ₐ[k] K, γ * (rep γ)⁻¹ ∈ (N.subtype : ↥N →* (K ≃ₐ[k] K)).range := by
    intro γ
    obtain ⟨n, hn⟩ := hrep2 γ
    exact ⟨n, (eq_mul_inv_iff_mul_eq).mpr hn⟩
  have hidem : ∀ γ : K ≃ₐ[k] K, rep (rep γ) = rep γ := by
    intro γ
    obtain ⟨n, hn⟩ := hrep2 γ
    have h1 : rep γ = ((n⁻¹ : ↥N) : K ≃ₐ[k] K) * γ := by
      rw [Subgroup.coe_inv]
      exact (eq_inv_mul_iff_mul_eq).mpr hn
    have h2 : rep (rep γ) = rep (((n⁻¹ : ↥N) : K ≃ₐ[k] K) * γ) := congrArg rep h1
    rw [h2, hrep1]
  have heq : ∀ γ γ' : K ≃ₐ[k] K,
      γ * γ'⁻¹ ∈ (N.subtype : ↥N →* (K ≃ₐ[k] K)).range → rep γ = rep γ' := by
    intro γ γ' h
    obtain ⟨n, hn⟩ := h
    have hn' : (n : K ≃ₐ[k] K) = γ * γ'⁻¹ := hn
    have h1 : γ = (n : K ≃ₐ[k] K) * γ' := by
      rw [hn']
      group
    rw [h1, hrep1]
  have hzero : ∀ v : (coindMod (K := K) p N).V, μ.hom v = 0 := by
    intro v
    have hdec := Work.SSGRoute.C6ValueFormula.coind_eq_sum_dirac N.subtype
      (coindCoeff (K := K) p N) (coindKer (K := K) p N) rep hrep hidem heq v
    conv_lhs => rw [hdec]
    rw [map_sum]
    refine Finset.sum_eq_zero fun x _ => ?_
    exact zmod_addHom_eq_zero
      ((μ.hom.toAddMonoidHom).comp (coindDiracHom (K := K) p N x)) (hcon x)
      ((v : (K ≃ₐ[k] K) → ZMod p) x)
  apply hμ
  apply Rep.hom_ext
  rw [Rep.zero_hom, Representation.IntertwiningMap.ext_iff]
  exact LinearMap.ext hzero

/-! ## Two small ambient-field compatibilities -/

/-- **The ideal-level `LiesOver` from the place-level one** at finite places. -/
theorem ideal_liesOver_of_place_liesOver {k K L : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra k L] [Algebra K L]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (h : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
      (NK.GlobalCFT.Place.ofFinite q)) :
    q'.asIdeal.LiesOver q.asIdeal := by
  rcases (NK.GlobalCFT.Place.liesOver_iff _ _).1 h with
    ⟨w', v', hw', -, -⟩ | ⟨q₁, Q₁, hq1, hQ1, hl⟩
  · exact absurd hw'.symm (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite w' q')
  · obtain rfl : q₁ = q' := (NK.GlobalCFT.Place.ofFinite_inj.mp hq1).symm
    obtain rfl : Q₁ = q := (NK.GlobalCFT.Place.ofFinite_inj.mp hQ1).symm
    exact hl

/-- **The Mackey isomorphism at the trivial representation, for a general ambient field.**  The
specialisation to `Ω = AlgebraicClosure K` is
`Work.SSGRoute.C6Detector.coind_res_mackey_trivialIso`; the proof is the same. -/
theorem coind_res_mackey_trivialIso_gen (p : ℕ) [Fact p.Prime] {k K Ω : Type} [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K]
    [IsGalois k K] [Field Ω] [Algebra k Ω] [Algebra K Ω] [IsScalarTower k K Ω]
    (L : IntermediateField K Ω) [FiniteDimensional k L] [IsGalois k L]
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal] :
    ∃ θ : Rep.res (SSGRoute.PTExt.galRes k K ↥L)
          (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p))) ≅
        Rep.coind (Subgroup.comap (SSGRoute.PTExt.galRes k K ↥L) N).subtype
          (Rep.trivial SSGRoute.PTExt.Coeff ↥(Subgroup.comap (SSGRoute.PTExt.galRes k K ↥L) N)
            (ZMod p)),
      ∀ (φ : (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p))).V)
        (x : ↥L ≃ₐ[k] ↥L),
        (θ.hom.hom φ).1 x = φ.1 (SSGRoute.PTExt.galRes k K ↥L x) := by
  classical
  -- Finiteness of the two Galois groups.
  haveI : Fintype (K ≃ₐ[k] K) := AlgEquiv.fintype k K
  haveI : Fintype (↥L ≃ₐ[k] ↥L) := AlgEquiv.fintype k ↥L
  -- Finiteness of the quotients by `N` and by its preimage.
  haveI h1 : DecidableRel (QuotientGroup.rightRel N) := Classical.decRel _
  haveI h2 : DecidableRel
      (QuotientGroup.rightRel (Subgroup.comap (SSGRoute.PTExt.galRes k K ↥L) N)) :=
    Classical.decRel _
  haveI : Fintype ((K ≃ₐ[k] K) ⧸ N) := inferInstance
  haveI : Fintype ((↥L ≃ₐ[k] ↥L) ⧸ Subgroup.comap (SSGRoute.PTExt.galRes k K ↥L) N) :=
    inferInstance
  -- Galois extensions are normal, so restriction of automorphisms is surjective.
  haveI : Normal k K := inferInstance
  haveI : Normal k ↥L := inferInstance
  have hf : Function.Surjective (SSGRoute.PTExt.galRes k K ↥L) :=
    AlgEquiv.restrictNormalHom_surjective (F := k) (K₁ := K) (↥L)
  -- Apply the Mackey isomorphism for the surjection `galRes` and the subgroup `N`.
  obtain ⟨θ₀, hθ₀, _, _⟩ :=
    Work.SSGRoute.coind_res_mackey (SSGRoute.PTExt.galRes k K ↥L) hf N
  -- The target representation of `↥N` is the trivial one, so that the restriction of the trivial
  -- representation of `↥N` to `N.comap galRes` is literally the trivial representation there.
  refine ⟨θ₀.app (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)), ?_⟩
  intro φ x
  exact hθ₀ (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)) φ x

section Concentrated

open scoped Pointwise

/-- **The level-cocycle datum from the concentrated level data.**

Given a `D_w`-equivariant functional `μ` on `M = coInd_N^{Γ} 𝔽_p` which does not kill the Dirac at
the coset `N γ`, the concentrated level data at `γ` (a finite Galois level `L ⊇ K` inside the
algebraically closed ambient `Ω`, a place `q' | w` with `p ∤ e(q'|q)`, an element `d ∈ D_{q'}` with
`d^f ∈ H = galRes⁻¹ N`, and a character `y` of `H` concentrated on the block of `γ`), and the
hypothesis that `N` contains the inertia at `q`, the level-cocycle datum holds.

The proof assembles the block data of `Work.SSGRoute.TPatom.levelCocycleDatum_of_blockData`: the
Mackey isomorphism `θ` of `Work.SSGRoute.coind_res_mackey`, the Shapiro factor `cfunc H`, the block
system `X` of `Work.SSGRoute.TPatom.exists_orbitBlockSystem`, the detecting block `x₀` of `γ`, the
detection `hinj` (transporting `μ` and using `Work.SSGcrux.mackeyInvDirac`), and the inertia
clause. -/
theorem levelCocycleDatum_of_concentrated (p : ℕ) [Fact p.Prime] (k K : Type) [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (N : Subgroup (K ≃ₐ[k] K)) [N.Normal]
    (hNI : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.IsInertiaAt q σ → σ ∈ N)
    (μ : Rep.res (SSGRoute.PTExt.decompK (k := k) (K := K) w).subtype
        (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) ⟶
      Work.SSGRoute.E7cOmega.divRep (SSGRoute.PTExt.decompK (k := k) (K := K) w))
    (γ : K ≃ₐ[k] K)
    (hγ : μ.hom (coindDirac (K := K) p N γ 1) ≠ 0)
    (hconc : ∃ (L : IntermediateField K Ω) (_ : NumberField ↥L) (_ : FiniteDimensional k ↥L)
      (_ : IsGalois k ↥L)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ↥L))
      (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q') w)
      (hcop : Nat.Coprime (q.asIdeal.ramificationIdx' q'.asIdeal) p)
      (d : ↥L ≃ₐ[k] ↥L) (f : ℕ)
      (hdH : d ^ f ∈ N.comap (SSGRoute.PTExt.galRes k K ↥L))
      (y : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L)) →* Multiplicative (ZMod p)),
      d ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q') ∧
      0 < f ∧
      (∀ δ ∈ SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q'),
        ∃ m : ℕ, δ⁻¹ * d ^ m ∈ N.comap (SSGRoute.PTExt.galRes k K ↥L)) ∧
      (∀ m : ℕ, 0 < m → m < f → d ^ m ∉ N.comap (SSGRoute.PTExt.galRes k K ↥L)) ∧
      (∀ x : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L)),
        (x : ↥L ≃ₐ[k] ↥L) ∈
          Subgroup.normalClosure {σ : ↥L ≃ₐ[k] ↥L | SSGRoute.PTExt.IsInertiaAt q' σ} →
        y x = 1) ∧
      (∀ x : ↥L ≃ₐ[k] ↥L,
        y (Work.SSGRoute.TatePoitouRoute.cfunc (N.comap (SSGRoute.PTExt.galRes k K ↥L)) x
            (⟨d ^ f, hdH⟩ : ↥(N.comap (SSGRoute.PTExt.galRes k K ↥L)))) = 1 ↔
          SSGRoute.PTExt.galRes k K ↥L x ∉ Work.SSGRoute.TPatom.concSet k K w N γ)) :
    Work.SSGRoute.PTdualControl.LevelCocycleDatum p k K Ω w q hwq
      (Rep.coind N.subtype (Rep.trivial SSGRoute.PTExt.Coeff N (ZMod p))) μ := by
  classical
  obtain ⟨L, hnfL, hfdL, hgalL, q', hq', hcop, d, f, hdH, y, hdmem, hf, hdgen, hfmin, hinert,
    hconcc⟩ := hconc
  letI : FiniteDimensional k ↥L := hfdL
  letI : IsGalois k ↥L := hgalL
  haveI hFinL : Fintype (↥L ≃ₐ[k] ↥L) := Fintype.ofFinite _
  haveI hFinK : Fintype (K ≃ₐ[k] K) := AlgEquiv.fintype k K
  -- ## the level subgroup `H = galRes⁻¹ N` and the decomposition group `D`
  let H : Subgroup (↥L ≃ₐ[k] ↥L) := Subgroup.comap (SSGRoute.PTExt.galRes k K ↥L) N
  haveI hHN : H.Normal := Subgroup.Normal.comap (inferInstance : N.Normal) _
  let D : Subgroup (↥L ≃ₐ[k] ↥L) :=
    SSGRoute.PTExt.decompK (k := k) (K := ↥L) (NK.GlobalCFT.Place.ofFinite q')
  have hdD : d ∈ D := hdmem
  -- ## the block system
  obtain ⟨X, hpart, hblock⟩ :=
    Work.SSGRoute.TPatom.exists_orbitBlockSystem H hHN D ⟨d, hdD⟩ f hf hdH
      (fun δ => hdgen (δ : ↥L ≃ₐ[k] ↥L) δ.2) (fun m hm hlt => hfmin m hm hlt)
  -- ## the detecting block: the block of a lift of `γ`
  have hsurjGR : Function.Surjective (SSGRoute.PTExt.galRes k K ↥L) :=
    AlgEquiv.restrictNormalHom_surjective (E := ↥L)
  obtain ⟨γ₀, hγ₀⟩ := hsurjGR γ
  let x₀ : ↥L ≃ₐ[k] ↥L := (Classical.choose (hpart γ₀)).1
  let j₀ : Fin f := (Classical.choose (hpart γ₀)).2
  have hx₀X : x₀ ∈ X := (Classical.choose_spec (hpart γ₀)).1.1
  have hx₀H : γ₀ * (x₀ * d ^ (j₀ : ℕ))⁻¹ ∈ H := (Classical.choose_spec (hpart γ₀)).1.2
  have huniq : ∀ (x : ↥L ≃ₐ[k] ↥L) (j : Fin f), x ∈ X →
      γ₀ * (x * d ^ (j : ℕ))⁻¹ ∈ H → x = x₀ := by
    intro x j hx hxj
    exact congrArg Prod.fst ((Classical.choose_spec (hpart γ₀)).2 (x, j) ⟨hx, hxj⟩)
  -- ## `galRes` maps the decomposition groups
  obtain ⟨fD, hfD⟩ := Work.SSGRoute.decompK_restrict_exists k K ↥L w
    (NK.GlobalCFT.Place.ofFinite q') hq'
  have hgal : ∀ σ : ↥D, SSGRoute.PTExt.galRes k K ↥L (σ : ↥L ≃ₐ[k] ↥L) ∈
      SSGRoute.PTExt.decompK (k := k) (K := K) w := by
    intro σ
    have h2 : (fD σ : K ≃ₐ[k] K) = SSGRoute.PTExt.galRes k K ↥L (σ : ↥L ≃ₐ[k] ↥L) := hfD σ
    rw [← h2]
    exact (fD σ).2
  -- the surjectivity of the restriction of the decomposition groups
  have hsurjD : Function.Surjective fD :=
    Work.SSGRoute.decompK_restrict_surjective k K w ↥L
      (NK.GlobalCFT.Place.ofFinite q') hq' fD hfD
  have hsurjDw : ∀ δ ∈ SSGRoute.PTExt.decompK (k := k) (K := K) w,
      ∃ δ' : ↥D, SSGRoute.PTExt.galRes k K ↥L (δ' : ↥L ≃ₐ[k] ↥L) = δ := by
    intro δ hδ
    obtain ⟨σ, hσ⟩ := hsurjD ⟨δ, hδ⟩
    exact ⟨σ, by rw [← hfD σ, hσ]⟩
  -- ## the block/coset dictionary
  have hconcSet : ∀ x : ↥L ≃ₐ[k] ↥L,
      (SSGRoute.PTExt.galRes k K ↥L x ∈ Work.SSGRoute.TPatom.concSet k K w N γ ↔
        ∃ j : Fin f, γ₀ * (x * d ^ (j : ℕ))⁻¹ ∈ H) := by
    intro x
    have hdgenD : ∀ δ : D, ∃ m : ℕ, ((δ : ↥L ≃ₐ[k] ↥L))⁻¹ * d ^ m ∈ H :=
      fun δ => hdgen (δ : ↥L ≃ₐ[k] ↥L) δ.2
    have key := Work.SSGRoute.C6Detector.block_iff_of_concentrated
      (SSGRoute.PTExt.galRes k K ↥L) hsurjGR N H
      (rfl : H = N.comap (SSGRoute.PTExt.galRes k K ↥L))
      (SSGRoute.PTExt.decompK (k := k) (K := K) w) D hgal hsurjDw
      (⟨d, hdD⟩ : ↥D) f hf hdH (fun δ => hdgenD δ) γ₀ x
    rw [hγ₀] at key
    simpa only [Work.SSGRoute.TPatom.concSet, Set.mem_setOf_eq] using key
  have hx₀conc : SSGRoute.PTExt.galRes k K ↥L x₀ ∈
      Work.SSGRoute.TPatom.concSet k K w N γ := (hconcSet x₀).mpr ⟨j₀, hx₀H⟩
  have huniqConc : ∀ x ∈ X, SSGRoute.PTExt.galRes k K ↥L x ∈
      Work.SSGRoute.TPatom.concSet k K w N γ → x = x₀ := by
    intro x hx hc
    obtain ⟨j, hj⟩ := (hconcSet x).mp hc
    exact huniq x j hx hj
  -- ## the concentration clauses
  have hne : Multiplicative.toAdd (y (Work.SSGRoute.TatePoitouRoute.cfunc H x₀
      (⟨d ^ f, hdH⟩ : ↥H))) ≠ 0 := by
    have h1 : y (Work.SSGRoute.TatePoitouRoute.cfunc H x₀ (⟨d ^ f, hdH⟩ : ↥H)) ≠ 1 :=
      fun hc => ((hconcc x₀).mp hc) hx₀conc
    intro h0
    refine h1 ?_
    simpa using congrArg Multiplicative.ofAdd h0
  have hvan : ∀ x ∈ X, x ≠ x₀ → Multiplicative.toAdd (y (Work.SSGRoute.TatePoitouRoute.cfunc H x
      (⟨d ^ f, hdH⟩ : ↥H))) = 0 := by
    intro x hx hxne
    have hnot : SSGRoute.PTExt.galRes k K ↥L x ∉ Work.SSGRoute.TPatom.concSet k K w N γ :=
      fun hc => hxne (huniqConc x hx hc)
    rw [(hconcc x).mpr hnot]
    rfl
  -- ## the Mackey isomorphism
  haveI hdecN : DecidableRel (QuotientGroup.rightRel N) := Classical.decRel _
  haveI hdecH : DecidableRel (QuotientGroup.rightRel H) := Classical.decRel _
  haveI hfinqN : Fintype ((K ≃ₐ[k] K) ⧸ N) := Fintype.ofFinite _
  haveI hfinqH : Fintype ((↥L ≃ₐ[k] ↥L) ⧸ H) := Fintype.ofFinite _
  let W : Rep.{0} SSGRoute.PTExt.Coeff ↥H := Rep.trivial SSGRoute.PTExt.Coeff ↥H (ZMod p)
  -- the Mackey isomorphism (proved elsewhere): the component at the trivial representation
  obtain ⟨θ, hθ⟩ := coind_res_mackey_trivialIso_gen (k := k) (K := K) (Ω := Ω) p L N
  -- ## the value of `θ⁻¹` on a detecting Dirac
  have hdirac_inv : ∀ a : ZMod p, θ.inv.hom (Work.Sha2Lib.diracHom
        (Rep.res ((SSGRoute.PTExt.galRes k K ↥L).subgroupComap N)
          (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p))) (fun _ _ _ => rfl) x₀ a) =
      coindDirac (K := K) p N (SSGRoute.PTExt.galRes k K ↥L x₀) a := by
    intro a
    apply Subtype.ext
    funext g
    have key := Work.SSGcrux.mackeyInvDirac (SSGRoute.PTExt.galRes k K ↥L) hsurjGR N
      (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p)) (fun _ _ => rfl) θ hθ x₀ a g
    exact key.trans (Work.SSGcrux.diracApply (Rep.trivial SSGRoute.PTExt.Coeff ↥N (ZMod p))
      (fun _ _ => rfl) (fun _ _ _ => rfl) (SSGRoute.PTExt.galRes k K ↥L x₀) a g).symm
  -- ## the detection
  have hdet : μ.hom (coindDirac (K := K) p N (SSGRoute.PTExt.galRes k K ↥L x₀) 1) ≠ 0 := by
    have hmem := hx₀conc
    simp only [Work.SSGRoute.TPatom.concSet, Set.mem_setOf_eq] at hmem
    obtain ⟨δ, hδ, n, hn, heq⟩ := hmem
    exact Work.SSGcrux.muDirac_ne_zero_of_doubleCoset N
      (SSGRoute.PTExt.decompK (k := k) (K := K) w) μ γ (SSGRoute.PTExt.galRes k K ↥L x₀) hγ
      ⟨δ, hδ, n, hn, heq⟩
  -- ## the detection of the block, transported through the Mackey isomorphism
  have hinj : ∀ a : W.V, a ≠ 0 →
      (Work.SSGRoute.TPatom.transportedFunctional p k K ↥L w N H μ θ D hgal).hom
        (Work.Sha2Lib.diracHom W (fun _ _ _ => rfl) x₀ a) ≠ 0 := by
    intro a ha
    have hstep : (Work.SSGRoute.TPatom.transportedFunctional p k K ↥L w N H μ θ D hgal).hom
        (Work.Sha2Lib.diracHom W (fun _ _ _ => rfl) x₀ a)
        = μ.hom (coindDirac (K := K) p N (SSGRoute.PTExt.galRes k K ↥L x₀) a) := by
      rw [Work.SSGRoute.TPatom.transportedFunctional_apply]
      exact congrArg μ.hom (hdirac_inv a)
    rw [hstep]
    exact Work.SSGcrux.zmodAddHom_ne_zero
      ((μ.hom.toAddMonoidHom).comp
        (coindDiracHom (K := K) p N (SSGRoute.PTExt.galRes k K ↥L x₀))) hdet a ha
  -- ## the inertia clause
  have hinertia : ∀ γ' : ↥L ≃ₐ[k] ↥L, SSGRoute.PTExt.IsInertiaAt q' γ' →
      θ.inv.hom (Work.SSGRoute.TPatom.shapiroTerm W (fun _ _ => rfl)
        (Work.SSGRoute.TatePoitouRoute.cfunc H)
        (fun g γ n => Work.SSGRoute.TatePoitouRoute.cfunc_inv H g γ n) y γ') = 0 := by
    intro γ' hγ'
    have hq'id : q'.asIdeal.LiesOver q.asIdeal := by
      have h : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
          (NK.GlobalCFT.Place.ofFinite q) := by rw [← hwq]; exact hq'
      exact ideal_liesOver_of_place_liesOver (k := k) q q' h
    have hγH : γ' ∈ H := Subgroup.mem_comap.mpr
      (hNI (SSGRoute.PTExt.galRes k K ↥L γ')
        (isInertiaAt_galRes q q' hq'id γ' hγ'))
    have hterm : Work.SSGRoute.TPatom.shapiroTerm W (fun _ _ => rfl)
        (Work.SSGRoute.TatePoitouRoute.cfunc H)
        (fun g γ n => Work.SSGRoute.TatePoitouRoute.cfunc_inv H g γ n) y γ' = 0 := by
      apply Subtype.ext
      funext g
      show Multiplicative.toAdd
        (y (Work.SSGRoute.TatePoitouRoute.cfunc H g γ')) = 0
      have hsec : Work.SSGRoute.TatePoitouRoute.sect H (g * γ')
          = Work.SSGRoute.TatePoitouRoute.sect H g := by
        have hconj : g * γ' * g⁻¹ ∈ H := hHN.conj_mem γ' hγH g
        have h := Work.SSGRoute.TatePoitouRoute.sect_const H
          (⟨g * γ' * g⁻¹, hconj⟩ : ↥H) g
        rwa [show ((⟨g * γ' * g⁻¹, hconj⟩ : ↥H) : ↥L ≃ₐ[k] ↥L) * g = g * γ' from by
          show (g * γ' * g⁻¹) * g = g * γ'; group] at h
      have hcg : ((Work.SSGRoute.TatePoitouRoute.cfunc H g γ' : ↥H) : ↥L ≃ₐ[k] ↥L)
          = Work.SSGRoute.TatePoitouRoute.sect H g * γ'
            * (Work.SSGRoute.TatePoitouRoute.sect H g)⁻¹ := by
        rw [Work.SSGRoute.TatePoitouRoute.coe_cfunc, hsec]
      have hmem : ((Work.SSGRoute.TatePoitouRoute.cfunc H g γ' : ↥H) : ↥L ≃ₐ[k] ↥L) ∈
          Subgroup.normalClosure {σ : ↥L ≃ₐ[k] ↥L | SSGRoute.PTExt.IsInertiaAt q' σ} := by
        rw [hcg]
        exact (Subgroup.normalClosure_normal (s := {σ : ↥L ≃ₐ[k] ↥L |
            SSGRoute.PTExt.IsInertiaAt q' σ})).conj_mem γ'
          (Subgroup.subset_normalClosure hγ')
          (Work.SSGRoute.TatePoitouRoute.sect H g)
      rw [hinert _ hmem]
      rfl
    rw [hterm]
    exact map_zero θ.inv.hom
  -- ## the assembly
  exact Work.SSGRoute.TPatom.levelCocycleDatum_of_blockData p k K Ω w q hwq N μ L q' hq' hcop H θ
    (Work.SSGRoute.TatePoitouRoute.cfunc H)
    (fun g γ γ' => Work.SSGRoute.TatePoitouRoute.cfunc_mul H g γ γ')
    (fun g => Work.SSGRoute.TatePoitouRoute.cfunc_one H g)
    (fun g γ n => Work.SSGRoute.TatePoitouRoute.cfunc_inv H g γ n)
    hgal ⟨d, hdD⟩ f hf hdH X hpart hblock y x₀ hx₀X hinj hne hvan hinertia

end Concentrated

end Work.Sha2Lib.C6Wiring
