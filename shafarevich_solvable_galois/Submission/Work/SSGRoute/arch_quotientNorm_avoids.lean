import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Submission.Work.SSGRoute.E7bDefs
import Submission.Work.SSGRoute.exists_complex_place_above
import Submission.Work.SSGRoute.infinitePlace_units_mul_pow
import Submission.Work.SSGRoute.localAlgebraMapUnits_self
import Submission.Work.SSGRoute.localUnitsEquiv_fixed_iff_ringEquiv_fixed
import Submission.Work.SSGRoute.not_norm_complex_place
import Submission.Work.SSGRoute.real_units_not_pow

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false

/-- **Composition of the restriction of an infinite place.**  If `u` is an infinite place of `L`
lying over `u₀` of `K`, and `k ⊆ K ⊆ L`, then the place of `k` below `u` is the place of `k`
below `u₀`. -/
private lemma liesOver_comap_comp {k K L : Type} [Field k] [NumberField k] [Field K]
    [NumberField K] [Field L] [NumberField L] [Algebra k K] [Algebra K L] [Algebra k L]
    [IsScalarTower k K L] {u : NumberField.InfinitePlace L} {u₀ : NumberField.InfinitePlace K}
    (h : u.LiesOver u₀) : u.comap (algebraMap k L) = u₀.comap (algebraMap k K) := by
  rw [IsScalarTower.algebraMap_eq k K L, NumberField.InfinitePlace.comap_comp,
    NumberField.InfinitePlace.LiesOver.comap_eq u u₀]

/-- **The image of a unit of the base local field is fixed by the decomposition group.** -/
private lemma localUnitsEquiv_localAlgebraMapUnits_eq_self {k K : Type} [Field k]
    [NumberField k] [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (v : NK.GlobalCFT.Place k) (hv : NK.GlobalCFT.Place.LiesOver w v)
    (c : (NK.GlobalCFT.Place.localField k v)ˣ)
    (σ : MulAction.stabilizer (K ≃ₐ[k] K) w) :
    NK.HassePrinciple.localUnitsEquiv (K := k) w σ
      (NK.GlobalCFT.Place.localAlgebraMapUnits w v hv c)
      = NK.GlobalCFT.Place.localAlgebraMapUnits w v hv c := by
  have h := NK.NUV2.LC.RouteB.localUnitsEquiv_localAlgebraMapUnits_tower
    (F := k) (L := k) (M := K) hv σ c
  rw [← h]
  congr 1
  have hτ : NK.NUV2.LC.RouteB.localStabilizerMapTower (F := k) (L := k) (M := K) hv σ = 1 :=
    Subsingleton.elim _ _
  rw [hτ, NK.HassePrinciple.localUnitsEquiv_one]
  rfl

/-- **A complex infinite place above a real place has a two-element stabiliser.** -/
private lemma natCard_stabilizer_ofInfinite_eq_two {k L : Type} [Field k] [NumberField k]
    [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (u : NumberField.InfinitePlace L) (hu : u.IsComplex)
    (v : NumberField.InfinitePlace k) [u.LiesOver v] (hv : v.IsReal) :
    Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite u)) = 2 := by
  have hram : NumberField.InfinitePlace.IsRamified k u :=
    NumberField.InfinitePlace.not_isUnramified_iff.mpr
      ⟨hu, by rw [NumberField.InfinitePlace.LiesOver.comap_eq u v]; exact hv⟩
  have h2 : Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) u) = 2 :=
    (NumberField.InfinitePlace.isRamified_iff_card_stabilizer_eq_two).mp hram
  have hstab : MulAction.stabilizer (L ≃ₐ[k] L) u
      = MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite u) := by
    ext σ
    rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff,
      NK.GlobalCFT.Place.smul_ofInfinite, NK.GlobalCFT.Place.ofInfinite_inj]
  rwa [← hstab]

/-- The place of a number field lies over itself. -/
private lemma liesOver_self_infinite {L : Type} [Field L] (w : NumberField.InfinitePlace L) :
    w.LiesOver w := by
  refine AbsoluteValue.LiesOver.mk ?_
  show w.val.comp (algebraMap L L).injective = w.val
  rw [show (algebraMap L L : L →+* L) = RingHom.id L from rfl]
  rfl

/-- **The core archimedean witness**: for a tower `k ⊆ K ⊆ L₀ ⊆ L` of number fields, an
archimedean place `u'` of `L` which is complex and lies over `u₀`, and a local unit `a` of `K_w`
which is the image of `a₀ ∈ k_vˣ` with negative real part, the place `u'` with `N = ⊥` realises
the required witness. -/
private theorem arch_core
    {k K L₀ L : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Field L₀]
    [NumberField L₀] [Field L] [NumberField L]
    [Algebra k K] [Algebra K L₀] [Algebra k L₀] [IsScalarTower k K L₀]
    [Algebra k L] [Algebra L₀ L] [IsScalarTower k L₀ L]
    [FiniteDimensional k L₀] [IsGalois k L₀] [FiniteDimensional k L] [IsGalois k L]
    (p : ℕ) [Fact p.Prime] (hp2 : p = 2)
    {u : NumberField.InfinitePlace K} {v₀ : NumberField.InfinitePlace k}
    {u₀ : NumberField.InfinitePlace L₀}
    (u' : NumberField.InfinitePlace L)
    (hu' : u'.LiesOver u₀) [hu'v : u'.LiesOver v₀]
    (hu'C : u'.IsComplex) (hv₀real : v₀.IsReal)
    (hv : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofInfinite u)
      (NK.GlobalCFT.Place.ofInfinite v₀))
    (hvw : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofInfinite u₀)
      (NK.GlobalCFT.Place.ofInfinite u))
    (hv2 : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofInfinite u₀)
      (NK.GlobalCFT.Place.ofInfinite v₀))
    (a : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite u))ˣ)
    (a₀ : (NK.GlobalCFT.Place.localField k (NK.GlobalCFT.Place.ofInfinite v₀))ˣ)
    (ha₀ : NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite u)
      (NK.GlobalCFT.Place.ofInfinite v₀) hv a₀ = a)
    (hneg : (NumberField.InfinitePlace.Completion.extensionEmbedding v₀
      (a₀ : v₀.Completion)).re < 0) :
    ∃ (w' : NK.GlobalCFT.Place L)
      (hw' : NK.GlobalCFT.Place.LiesOver w' (NK.GlobalCFT.Place.ofInfinite u₀))
      (N : Subgroup (MulAction.stabilizer (L ≃ₐ[k] L) w')) (_ : N.Normal)
      (_ : Fintype (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N)),
      IsCyclic (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) ∧
      Nat.card (MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N) = p ∧
      ¬ (∃ bb : NK.HassePrinciple.localUnitsRep k L w',
        (∀ n : N, (NK.HassePrinciple.localUnitsRep k L w').ρ
          (n : MulAction.stabilizer (L ≃ₐ[k] L) w') bb = bb) ∧
        (∑ x : MulAction.stabilizer (L ≃ₐ[k] L) w' ⧸ N,
          (NK.HassePrinciple.localUnitsRep k L w').ρ (Quotient.out x) bb) =
          Additive.ofMul (NK.GlobalCFT.Place.localAlgebraMapUnits w'
            (NK.GlobalCFT.Place.ofInfinite u₀) hw'
            (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite u₀)
              (NK.GlobalCFT.Place.ofInfinite u) hvw a))) := by
  classical
  have hcard2 : Nat.card (MulAction.stabilizer (L ≃ₐ[k] L)
      (NK.GlobalCFT.Place.ofInfinite u')) = 2 :=
    natCard_stabilizer_ofInfinite_eq_two u' hu'C v₀ hv₀real
  have hv3 : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofInfinite u')
      (NK.GlobalCFT.Place.ofInfinite v₀) :=
    NK.GlobalCFT.Place.liesOver_ofInfinite hu'v
  refine ⟨NK.GlobalCFT.Place.ofInfinite u', NK.GlobalCFT.Place.liesOver_ofInfinite hu',
    ⊥, ?_, ?_, ?_, ?_, ?_⟩
  · exact (inferInstance : (⊥ : Subgroup
      (MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite u'))).Normal)
  · exact inferInstance
  · have hq : Nat.card (MulAction.stabilizer (L ≃ₐ[k] L)
        (NK.GlobalCFT.Place.ofInfinite u') ⧸
        (⊥ : Subgroup (MulAction.stabilizer (L ≃ₐ[k] L)
          (NK.GlobalCFT.Place.ofInfinite u')))) = 2 := by
      rw [Nat.card_congr (QuotientGroup.quotientBot).toEquiv, hcard2]
    exact isCyclic_of_prime_card (p := 2) hq
  · have hq : Nat.card (MulAction.stabilizer (L ≃ₐ[k] L)
        (NK.GlobalCFT.Place.ofInfinite u') ⧸
        (⊥ : Subgroup (MulAction.stabilizer (L ≃ₐ[k] L)
          (NK.GlobalCFT.Place.ofInfinite u')))) = 2 := by
      rw [Nat.card_congr (QuotientGroup.quotientBot).toEquiv, hcard2]
    rw [hq, hp2]
  · -- the non-norm clause
    have him : NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite u')
          (NK.GlobalCFT.Place.ofInfinite u₀)
          (NK.GlobalCFT.Place.liesOver_ofInfinite hu')
          (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite u₀)
            (NK.GlobalCFT.Place.ofInfinite u) hvw a)
        = NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite u')
            (NK.GlobalCFT.Place.ofInfinite v₀) hv3 a₀ := by
      have h1 : (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite u₀)
            (NK.GlobalCFT.Place.ofInfinite u) hvw)
            (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite u)
              (NK.GlobalCFT.Place.ofInfinite v₀) hv a₀)
          = NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite u₀)
            (NK.GlobalCFT.Place.ofInfinite v₀) hv2 a₀ :=
        (MonoidHom.comp_apply
          (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite u₀)
            (NK.GlobalCFT.Place.ofInfinite u) hvw)
          (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite u)
            (NK.GlobalCFT.Place.ofInfinite v₀) hv) a₀).symm.trans
        (DFunLike.congr_fun (localAlgebraMapUnits_comp (K := k) (L := K) (M := L₀)
          hvw hv hv2) a₀)
      have h2 : (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite u')
            (NK.GlobalCFT.Place.ofInfinite u₀) (NK.GlobalCFT.Place.liesOver_ofInfinite hu'))
            (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite u₀)
              (NK.GlobalCFT.Place.ofInfinite v₀) hv2 a₀)
          = NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite u')
            (NK.GlobalCFT.Place.ofInfinite v₀) hv3 a₀ :=
        (MonoidHom.comp_apply
          (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite u')
            (NK.GlobalCFT.Place.ofInfinite u₀) (NK.GlobalCFT.Place.liesOver_ofInfinite hu'))
          (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite u₀)
            (NK.GlobalCFT.Place.ofInfinite v₀) hv2) a₀).symm.trans
        (DFunLike.congr_fun (localAlgebraMapUnits_comp (K := k) (L := L₀) (M := L)
          (NK.GlobalCFT.Place.liesOver_ofInfinite hu') hv2 hv3) a₀)
      rw [← ha₀, h1, h2]
    have hneg' : (NumberField.InfinitePlace.Completion.extensionEmbedding u'
        (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite u')
          (NK.GlobalCFT.Place.ofInfinite v₀) hv3 a₀ : u'.Completion)).re < 0 := by
      rw [NK.NUV2.LC.RouteB.localAlgebraMapUnits_ofInfinite_tower (h := hv3), Units.coe_map]
      convert hneg using 2
      exact NK.GlobalCFT.Galois.completionMap_extensionEmbedding (w := u') (v := v₀) hv₀real _
    rintro ⟨bb, hfix, hsum⟩
    exact not_norm_complex_place u' hcard2
      (NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite u')
        (NK.GlobalCFT.Place.ofInfinite v₀) hv3 a₀) hneg'
      ⟨bb, hfix, by rw [hsum, him]⟩

/-- **The archimedean case of the Z5a arithmetic input** (the case `w` infinite of
`Work.SSGRoute.exists_level_above_quotientNorm_avoids`; the statement of that case is already on disk
as the *unproved* `Submission/Work/SSGRoute/exists_level_above_quotientNorm_avoids_infinite.lean`).

For a number-field tower `k ⊆ K` and an **archimedean** place `w = Place.ofInfinite u` of `K`: given a
unit `a ∈ K_wˣ` fixed by the whole decomposition group `D_w` (so `a` is the image of a unit of
`k_vˣ`, `v = w|_k`) which is not the `p`-th power of a `D_w`-fixed unit, and an arbitrary level
`L₀ ⊇ K` with a place `w₀ ∣ w`, there are a level `L ⊇ L₀` (finite Galois over `k`), a place
`w' ∣ w₀`, and `N ⊴ D_{w'}` with `D_{w'}/N` cyclic of order `p`, such that the image of `a` in
`L_{w'}ˣ` is not an `N`-relative norm (the norm being the sum `∑_{x ∈ D_{w'}/N} ρ(out x) ·` of the
`localUnitsRep`).

Route (the hypotheses force `p = 2` and `k_v = ℝ` with `a < 0`): if `K_w = ℂ` then `(L₀)_{w₀} = ℂ`,
`D_{w₀} ≅ ℤ/2`, and `L := L₀`, `w' := w₀`, `N := ⊥` works (the sum of a `z ∈ ℂˣ` with its conjugate
is `Complex.normSq z ≥ 0`, never `a < 0`); if `K_w = ℝ` then take `L := L₀ ⊔ ℚ(i)` (a compositum of
Galois extensions inside `AlgebraicClosure k`), any archimedean place `w'` of `L` over `w₀`, which is
complex, so `D_{w'} ≅ ℤ/2`, and again `N := ⊥`.  When `k_v = ℂ` (i.e. `K_w = ℂ` over `ℂ`) every
`a ∈ ℂˣ` is a `p`-th power, so the hypothesis `ha` is vacuous. -/
theorem arch_quotientNorm_avoids
    (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (u : NumberField.InfinitePlace K)
    (a : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite u))ˣ)
    (hafix : ∀ σ : decompK (k := k) (NK.GlobalCFT.Place.ofInfinite u),
      NK.HassePrinciple.localUnitsEquiv (K := k) (NK.GlobalCFT.Place.ofInfinite u) σ a = a)
    (ha : ¬ ∃ b : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofInfinite u))ˣ,
      (∀ σ : decompK (k := k) (NK.GlobalCFT.Place.ofInfinite u),
        NK.HassePrinciple.localUnitsEquiv (K := k) (NK.GlobalCFT.Place.ofInfinite u) σ b = b) ∧
        b ^ p = a)
    (L₀ : Type) [Field L₀] [NumberField L₀] [Algebra k L₀] [Algebra K L₀] [IsScalarTower k K L₀]
    [FiniteDimensional k L₀] [IsGalois k L₀]
    (w₀ : NK.GlobalCFT.Place L₀)
    (hw₀ : NK.GlobalCFT.Place.LiesOver w₀ (NK.GlobalCFT.Place.ofInfinite u)) :
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
            (NK.GlobalCFT.Place.localAlgebraMapUnits w₀ (NK.GlobalCFT.Place.ofInfinite u) hw₀ a))) := by
  classical
  -- ## the place `v₀` of `k` below `u`, and the local map at it
  let v₀ : NumberField.InfinitePlace k := u.comap (algebraMap k K)
  haveI hv₀inst : u.LiesOver v₀ := ⟨rfl⟩
  have hv : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofInfinite u)
      (NK.GlobalCFT.Place.ofInfinite v₀) := NK.GlobalCFT.Place.liesOver_ofInfinite hv₀inst
  -- ## step 1: `a` is the image of a unit `a₀` of `k_vˣ`
  have hafix' : ∀ (σ : K ≃ₐ[k] K)
      (hσ : σ • NK.GlobalCFT.Place.ofInfinite u = NK.GlobalCFT.Place.ofInfinite u),
      Units.map (NK.GlobalCFT.Place.localRingEquiv σ (NK.GlobalCFT.Place.ofInfinite u)).toMonoidHom a
        = hσ.symm ▸ a :=
    (localUnitsEquiv_fixed_iff_ringEquiv_fixed_general k K
      (NK.GlobalCFT.Place.ofInfinite u) a).mp hafix
  obtain ⟨a₀, ha₀⟩ :=
    NK.GlobalCFT.Galois.globalCFT_localFixed_infinite (K := k) (L := K) hv₀inst a hafix'
  -- ## step 2: `a₀` is not a `p`-th power in `k_vˣ`
  have ha₀notpow : ¬ ∃ c : (NK.GlobalCFT.Place.localField k
      (NK.GlobalCFT.Place.ofInfinite v₀))ˣ, c ^ p = a₀ := by
    rintro ⟨c, hc⟩
    refine ha ⟨NK.GlobalCFT.Place.localAlgebraMapUnits (NK.GlobalCFT.Place.ofInfinite u)
        (NK.GlobalCFT.Place.ofInfinite v₀) hv c, fun σ => ?_, ?_⟩
    · exact localUnitsEquiv_localAlgebraMapUnits_eq_self
        (NK.GlobalCFT.Place.ofInfinite u) (NK.GlobalCFT.Place.ofInfinite v₀) hv c σ
    · rw [← map_pow, hc, ha₀]
  -- ## step 3: `k_v = ℝ`, `p = 2`, and the real value of `a₀` is negative
  have hv₀real : v₀.IsReal := by
    by_contra hreal
    have hcomp : v₀.IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hreal
    let Ψ : (v₀.Completion)ˣ ≃* ℂˣ := Units.mapEquiv
      (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hcomp).toMulEquiv
    obtain ⟨z, hz⟩ := Work.SSGRoute.exists_pow_eq_complex_units p (Ψ a₀)
    exact ha₀notpow ⟨Ψ.symm z, by rw [← map_pow, hz, MulEquiv.symm_apply_apply]⟩
  set x : ℝˣ := Units.mapEquiv
    (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv₀real).toMulEquiv a₀ with hxdef
  have hxnotpow : ¬ ∃ y : ℝˣ, y ^ p = x := by
    rintro ⟨y, hy⟩
    refine ha₀notpow ⟨(Units.mapEquiv
      (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv₀real).toMulEquiv).symm y, ?_⟩
    rw [← map_pow, hy, hxdef, MulEquiv.symm_apply_apply]
  obtain ⟨hp2, hxneg⟩ := Work.SSGRoute.real_units_not_pow p x hxnotpow
  have hxre : (NumberField.InfinitePlace.Completion.extensionEmbedding v₀
      (a₀ : v₀.Completion)).re = (x : ℝ) := by
    rw [← NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply hv₀real
      (a₀ : v₀.Completion), Complex.ofReal_re, hxdef, Units.coe_mapEquiv]
    rfl
  have hneg : (NumberField.InfinitePlace.Completion.extensionEmbedding v₀
      (a₀ : v₀.Completion)).re < 0 := by
    rw [hxre]; exact hxneg
  -- ## step 4: the place `w₀` and the level `L`
  rcases w₀ with u₀ | q₀
  · -- `w₀ = Place.ofInfinite u₀` with `u₀` an infinite place of `L₀`
    have hLu₀' : u₀.LiesOver u := by
      rcases hw₀ with ⟨w', v', e1, e2, hL⟩ | ⟨q, Q, e1, e2, hL⟩
      · have h1 : u₀ = w' := NK.GlobalCFT.Place.ofInfinite_inj.mp e1
        have h2 : u = v' := NK.GlobalCFT.Place.ofInfinite_inj.mp e2
        rw [← h1, ← h2] at hL
        exact hL
      · exact absurd e1 (NK.GlobalCFT.Place.ofInfinite_ne_ofFinite u₀ q)
    haveI hlu : u₀.LiesOver u := hLu₀'
    have hvw : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofInfinite u₀)
        (NK.GlobalCFT.Place.ofInfinite u) := NK.GlobalCFT.Place.liesOver_ofInfinite hlu
    haveI hu₀v : u₀.LiesOver v₀ :=
      ⟨congrArg Subtype.val (liesOver_comap_comp (k := k) (K := K) (L := L₀) hLu₀')⟩
    have hv2 : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofInfinite u₀)
        (NK.GlobalCFT.Place.ofInfinite v₀) := NK.GlobalCFT.Place.liesOver_ofInfinite hu₀v
    rcases u₀.isReal_or_isComplex with hu₀real | hu₀C
    · -- `u₀` real: enlarge `L₀` so that a place above it becomes complex
      obtain ⟨L, hLf, hLn, hLk, hLL₀, hST, hLfd, hLgal, u', hu'Lies, hu'C⟩ :=
        exists_complex_place_above k L₀ u₀ hu₀real
      letI : Algebra k L := hLk
      letI : Algebra L₀ L := hLL₀
      letI : IsScalarTower k L₀ L := hST
      letI : FiniteDimensional k L := hLfd
      letI : IsGalois k L := hLgal
      have hcomap : u'.comap (algebraMap k L) = v₀ := by
        rw [liesOver_comap_comp (k := k) (K := L₀) (L := L) hu'Lies]
        exact liesOver_comap_comp (k := k) (K := K) (L := L₀) hLu₀'
      haveI hu'v : u'.LiesOver v₀ := ⟨congrArg Subtype.val hcomap⟩
      obtain ⟨w', hw'', N, hN, hF, hyc, hcard, hnn⟩ :=
        arch_core (k := k) (K := K) (L₀ := L₀) (L := L) p hp2 u' hu'Lies hu'C hv₀real
          hv hvw hv2 a a₀ ha₀ hneg
      exact ⟨L, hLf, hLn, hLk, hLL₀, hST, hLfd, hLgal, w', hw'', N, hN, hF, hyc, hcard, hnn⟩
    · -- `u₀` complex: keep `L := L₀`
      have hself : u₀.LiesOver u₀ := liesOver_self_infinite u₀
      obtain ⟨w', hw'', N, hN, hF, hyc, hcard, hnn⟩ :=
        arch_core (k := k) (K := K) (L₀ := L₀) (L := L₀) p hp2 u₀ hself hu₀C hv₀real
          hv hvw hv2 a a₀ ha₀ hneg
      exact ⟨L₀, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
        inferInstance, inferInstance, w', hw'', N, hN, hF, hyc, hcard, hnn⟩
  · -- `w₀` finite: impossible over the archimedean place `u`
    exact absurd ((NK.GlobalCFT.Place.isFinite_of_liesOver hw₀).mp
      (NK.GlobalCFT.Place.isFinite_ofFinite q₀)) (NK.GlobalCFT.Place.not_isFinite_ofInfinite u)

end Work.SSGRoute
