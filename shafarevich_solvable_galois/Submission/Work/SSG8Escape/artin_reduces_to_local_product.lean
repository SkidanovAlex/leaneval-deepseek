import Mathlib.GroupTheory.Nilpotent
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Submission.Work.SSGRoute.HRec.exists_conjInv_kummerChar_eq_zero_iff
import Submission.Work.SSGRoute.SSG8Escape.Setup
import Submission.Work.SSGRoute.ZDataMup.ideleArtin_ideleOfPrime_of_unramified
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise BigOperators
open NumberField IsDedekindDomain
open NK.GlobalCFT

namespace Work.SSG8Escape

/-! ## Auxiliary lemmas for the reciprocity reduction -/

/-- `cprod` is the ordinary `Finset`-product in the (irrelevant) commutative monoid structure
determined by `hcomm`. -/
theorem cprod_eq_finset_prod {G : Type} [CommGroup G] {ι : Type} (s : Finset ι) (f : ι → G) :
    NK.CFTLib.IdeleHasse.cprod (fun a b : G => mul_comm a b) s f = ∏ i ∈ s, f i := rfl

/-- The `cprod` over the image of the finite places is the `cprod` over the source. -/
theorem cprod_image_ofFinite_place {G : Type} [Group G] (hcomm : ∀ x y : G, x * y = y * x)
    {K : Type} [Field K] [NumberField K] [DecidableEq (NK.GlobalCFT.Place K)]
    (T : Finset (NK.Chebotarev.PrimeIdeal K)) (f : NK.GlobalCFT.Place K → G) :
    NK.CFTLib.IdeleHasse.cprod hcomm (T.image (NK.GlobalCFT.Place.ofFinite (K := K))) f
      = NK.CFTLib.IdeleHasse.cprod hcomm T (fun 𝔮 => f (NK.GlobalCFT.Place.ofFinite 𝔮)) := by
  letI : CommMonoid G := { ‹Group G› with mul_comm := hcomm }
  unfold NK.CFTLib.IdeleHasse.cprod
  exact Finset.prod_image (fun a _ b _ hab => Sum.inr.inj hab)

/-! ## No real places, from a primitive root of unity and the hypothesis at `p = 2` -/

/-- **`↥K` has no real place.**  For odd `p` this follows from the presence of a primitive `p`-th
root of unity `ζ ∈ ↥K` (`↥K` is totally imaginary); for `p = 2` it is the converse of the
Artin–Schreier dictionary, which says that a real place of `↥K` produces a nontrivial involution
of `Gal(Ω/↥K)` — exactly what `hKimag` forbids. -/
theorem no_real_place_of_primitive_root_hKimag
    (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p) :
    ∀ w : NumberField.InfinitePlace ↥K, w.IsComplex := by
  intro w
  by_contra hwc
  have hwr : w.IsReal := NumberField.InfinitePlace.not_isComplex_iff_isReal.mp hwc
  by_cases hp2 : p = 2
  · -- `p = 2`: a real place yields a nontrivial involution of `Gal(Ω/↥K)`.
    haveI : IsAlgClosure ↥K Ω :=
      ⟨‹IsAlgClosed Ω›, Algebra.IsAlgebraic.tower_top (K := k) (L := ↥K) (A := Ω)⟩
    obtain ⟨c, hc2, hc1, _⟩ :=
      Work.SSGRoute.HRec.exists_conjInv_kummerChar_eq_zero_iff (k := ↥K) (Ω := Ω) ζ
        (hp2 ▸ hζ) w hwr
    let c' : Ω ≃ₐ[k] Ω := ((K.fixingSubgroupEquiv.symm c : K.fixingSubgroup) : Ω ≃ₐ[k] Ω)
    have hc'mem : c' ∈ K.fixingSubgroup := (K.fixingSubgroupEquiv.symm c).2
    have hc'2 : c' ^ 2 = 1 := by
      have h1 : ((K.fixingSubgroupEquiv.symm c) ^ 2 : K.fixingSubgroup) = 1 := by
        rw [← map_pow, hc2, map_one]
      change (((K.fixingSubgroupEquiv.symm c : K.fixingSubgroup) : Ω ≃ₐ[k] Ω)) ^ 2 = 1
      rw [← Subgroup.coe_pow, h1, Subgroup.coe_one]
    have hc'1 : c' ≠ 1 := by
      intro h
      apply hc1
      have h2 : K.fixingSubgroupEquiv.symm c = 1 := Subtype.ext h
      calc c = K.fixingSubgroupEquiv (K.fixingSubgroupEquiv.symm c) :=
            (MulEquiv.apply_symm_apply _ _).symm
        _ = K.fixingSubgroupEquiv 1 := by rw [h2]
        _ = 1 := map_one _
    exact hc'1 (hKimag hp2 c' hc'mem hc'2)
  · -- `p ≠ 2`: `ζ` is a primitive root of unity of odd order `≥ 3`, so `↥K` is totally imaginary.
    haveI : NumberField ↥K := inferInstance
    have hpodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
    have hp3 : 3 ≤ p := by
      obtain ⟨m, hm⟩ := hpodd
      have h2 : 2 ≤ p := (Fact.out : p.Prime).two_le
      omega
    exact hwc ((NK.CFTLib.IdeleHasse.isTotallyComplex_of_primitiveRoot hp3 ζ hζ).isComplex w)

/-! ## The product formula for a norm-killing homomorphism -/

/-- **The product formula.**  A homomorphism `Ψ` out of the idèle group which kills the principal
idèles and the norm idèles is the product of its local factors, over any finite set of places off
which every component of `y` is already a local norm. -/
theorem productFormula_of_mem_localNormSubgroup
    {K F A : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
    [FiniteDimensional K F] [IsGalois K F] [CommGroup A]
    (Ψ : NK.GlobalCFT.Idele K →* A)
    (_hprin : ∀ x : Kˣ, Ψ (NK.GlobalCFT.Idele.principalIdele K x) = 1)
    (hnorm : ∀ y : NK.GlobalCFT.Idele F, Ψ (NK.GlobalCFT.Idele.normIdeleHom K F y) = 1)
    (y : NK.GlobalCFT.Idele K) (s : Finset (NK.GlobalCFT.Place K))
    (hs : ∀ v, v ∉ s → y v ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := F) v) :
    Ψ y = NK.CFTLib.IdeleHasse.cprod (fun a b : A => mul_comm a b) s
      (fun v => Ψ (NK.HassePrinciple.onePlace v (y v))) := by
  classical
  set w : NK.GlobalCFT.Idele K := y * (∏ v ∈ s, NK.HassePrinciple.onePlace v (y v))⁻¹ with hw
  have hwmem : w ∈ NK.GlobalCFT.Idele.normImage K F := by
    rw [Work.SSGRoute.ZDataMup.mem_normImage_iff_forall_mem_localNormSubgroup]
    intro v
    by_cases hv : v ∈ s
    · have h1 : (∏ u ∈ s, NK.HassePrinciple.onePlace u (y u)) v = y v := by
        rw [Work.SSGRoute.ZDataMup.Idele_prod_apply,
          Finset.prod_eq_single_of_mem v hv (fun b _ hbv => by
            rw [NK.HassePrinciple.onePlace_apply_ne (Ne.symm hbv)]),
          NK.HassePrinciple.onePlace_apply_self]
      rw [hw, NK.GlobalCFT.Idele.mul_apply, NK.GlobalCFT.Idele.inv_apply, h1, mul_inv_cancel]
      exact Subgroup.one_mem _
    · have h1 : (∏ u ∈ s, NK.HassePrinciple.onePlace u (y u)) v = 1 := by
        rw [Work.SSGRoute.ZDataMup.Idele_prod_apply]
        exact Finset.prod_eq_one (fun b hb => by
          rw [NK.HassePrinciple.onePlace_apply_ne (fun h : v = b => hv (by rw [h]; exact hb))])
      rw [hw, NK.GlobalCFT.Idele.mul_apply, NK.GlobalCFT.Idele.inv_apply, h1, inv_one, mul_one]
      exact hs v hv
  have hwΨ : Ψ w = 1 := by
    obtain ⟨y', hy'⟩ := NK.GlobalCFT.Idele.mem_normImage.mp hwmem
    rw [show w = NK.GlobalCFT.Idele.normIdeleHom K F y' from NK.GlobalCFT.Idele.ext (fun v => hy' v)]
    exact hnorm y'
  have hy_eq : y = w * (∏ v ∈ s, NK.HassePrinciple.onePlace v (y v)) := by
    rw [hw, mul_assoc, inv_mul_cancel, mul_one]
  have hmain : Ψ y = Ψ (w * (∏ v ∈ s, NK.HassePrinciple.onePlace v (y v))) := by
    conv_lhs => rw [hy_eq]
  rw [hmain, map_mul, hwΨ, one_mul]
  exact Work.SSGRoute.ZDataMup.map_prod_onePlace (K := K) (L := F)
    (fun a b : A => mul_comm a b) Ψ s (fun v => y v)

/-! ## The reciprocity reduction -/

theorem artin_reduces_to_local_product
    (p : ℕ) [Fact p.Prime] {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (hKimag : p = 2 → ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → c = 1)
    (ζ : ↥K) (hζ : IsPrimitiveRoot ζ p)
    (F : IntermediateField ↥K Ω) [FiniteDimensional ↥K F] [IsGalois ↥K F] [NumberField ↥F]
    (c : (↥K)ˣ) (hc : NK.LocalAnabelian.kummerField (p := p) (K' := Ω) c ≤ F)
    (χ : (↥F ≃ₐ[↥K] ↥F) →* Multiplicative (ZMod p))
    (hχ : ∀ σ : Ω ≃ₐ[↥K] Ω,
      χ (AlgEquiv.restrictNormalHom F σ) =
        Multiplicative.ofAdd (Work.SSGRoute.kummerCharZMod (K := ↥K) (Ω := Ω) p (ζ := ζ) hζ c σ))
    (a : (↥K)ˣ) (T' : Finset (NK.Chebotarev.PrimeIdeal ↥K))
    (hLT : ∀ 𝔮 : NK.Chebotarev.PrimeIdeal ↥K, 𝔮 ∉ T' →
      NK.HeckeL.IsUnramifiedIn (K := ↥K) (L := ↥F) 𝔮)
    (Φ : NK.GlobalCFT.Idele ↥K →* (↥F ≃ₐ[↥K] ↥F))
    (hΦprin : ∀ x : (↥K)ˣ, Φ (NK.GlobalCFT.Idele.principalIdele ↥K x) = 1)
    (hΦnorm : ∀ y : NK.GlobalCFT.Idele ↥F, Φ (NK.GlobalCFT.Idele.normIdeleHom ↥K ↥F y) = 1)
    (hTfix : (∏ 𝔭 ∈ T', χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
        (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a)))) = 1) :
    χ (Φ (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))) = 1 := by
  classical
  -- `Ψ := χ ∘ Φ`
  set Ψ : NK.GlobalCFT.Idele ↥K →* Multiplicative (ZMod p) := χ.comp Φ with hΨ
  have hΨapply : ∀ x : NK.GlobalCFT.Idele ↥K, Ψ x = χ (Φ x) := fun x => by rw [hΨ]; rfl
  have hprinΨ : ∀ x : (↥K)ˣ, Ψ (NK.GlobalCFT.Idele.principalIdele ↥K x) = 1 := by
    intro x; rw [hΨapply, hΦprin x, map_one]
  have hnormΨ : ∀ y : NK.GlobalCFT.Idele ↥F,
      Ψ (NK.GlobalCFT.Idele.normIdeleHom ↥K ↥F y) = 1 := by
    intro y; rw [hΨapply, hΦnorm y, map_one]
  -- `↥K` has no real place
  have hcomplex : ∀ w : NumberField.InfinitePlace ↥K, w.IsComplex :=
    no_real_place_of_primitive_root_hKimag p K hKimag ζ hζ
  -- the idèle `y = ρ(a) · 𝔡⁻¹`
  set y : NK.GlobalCFT.Idele ↥K := NK.GlobalCFT.Idele.principalIdele ↥K a *
    (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))⁻¹ with hy
  -- every place outside `T'` has `y`-component a local norm
  have hYnorm : ∀ v : NK.GlobalCFT.Place ↥K,
      v ∉ T'.image (NK.GlobalCFT.Place.ofFinite (K := ↥K)) →
      y v ∈ NK.CFTLib.IdeleHasse.localNormSubgroup (K := ↥K) (L := ↥F) v := by
    intro v hv
    rcases v with w | 𝔮
    · -- archimedean place
      have hfrac : (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))
          (NK.GlobalCFT.Place.ofInfinite w) = 1 := rfl
      have hyv : y (NK.GlobalCFT.Place.ofInfinite w)
          = NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofInfinite w) a := by
        rw [hy, NK.GlobalCFT.Idele.mul_apply, NK.GlobalCFT.Idele.inv_apply, hfrac, inv_one,
          mul_one, Work.SSGRoute.ZDataMup.principalIdele_apply_eq_localImageAt]
      rw [hyv, NK.CFTLib.HR.localNormSubgroup_ofInfinite_eq_top_of_isTotallyComplex (M := ↥K)
        (E := ↥F) (⟨hcomplex⟩ : NumberField.IsTotallyComplex ↥K) w]
      exact Subgroup.mem_top _
    · -- finite place outside `T'`: unramified, and the component is a local unit
      have h𝔮T : 𝔮 ∉ T' := fun h => hv (Finset.mem_image.mpr ⟨𝔮, h, rfl⟩)
      have hmem : y (NK.GlobalCFT.Place.ofFinite 𝔮)
          ∈ NK.GlobalCFT.Place.localUnits ↥K (NK.GlobalCFT.Place.ofFinite 𝔮) := by
        rw [NK.NUV2.RouteB.RayModulus.mem_localUnits_iff_exp_eq_zero]
        rw [hy, NK.GlobalCFT.Idele.exp_mul, NK.NUV2.RouteB.RayModulus.exp_inv,
          NK.GlobalCFT.IdeleClassGroup.exp_ideleOfFun,
          Work.SSGRoute.tFreePart_count_eq_exp (K := ↥K) T' a h𝔮T]
        ring
      exact NK.CFTLib.IdeleHasse.localUnits_le_localNormSubgroup_of_unramified (K := ↥K) (L := ↥F)
        𝔮 (hLT 𝔮 h𝔮T) hmem
  -- the product formula
  have hPF := productFormula_of_mem_localNormSubgroup (K := ↥K) (F := ↥F)
    (A := Multiplicative (ZMod p)) Ψ hprinΨ hnormΨ y
    (T'.image (NK.GlobalCFT.Place.ofFinite (K := ↥K))) hYnorm
  -- collapse the `cprod` over the image of the finite places
  have hImage : NK.CFTLib.IdeleHasse.cprod (fun a b : Multiplicative (ZMod p) => mul_comm a b)
        (T'.image (NK.GlobalCFT.Place.ofFinite (K := ↥K)))
        (fun v => Ψ (NK.HassePrinciple.onePlace v (y v)))
      = NK.CFTLib.IdeleHasse.cprod (fun a b : Multiplicative (ZMod p) => mul_comm a b) T'
        (fun 𝔭 => Ψ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
          (y (NK.GlobalCFT.Place.ofFinite 𝔭)))) :=
    cprod_image_ofFinite_place (K := ↥K) (fun a b : Multiplicative (ZMod p) => mul_comm a b) T'
      (fun v => Ψ (NK.HassePrinciple.onePlace v (y v)))
  -- `y` at a prime of `T'` is the local image of `a`
  have hyT : ∀ 𝔭 ∈ T', y (NK.GlobalCFT.Place.ofFinite 𝔭)
      = NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a := by
    intro 𝔭 h𝔭
    have hzero : (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))
        (NK.GlobalCFT.Place.ofFinite 𝔭) = 1 := by
      rw [Work.SSGRoute.fracIdele_apply_ofFinite,
        Work.SSGRoute.tFreePart_count_eq_zero (K := ↥K) T' a h𝔭, zpow_zero]
    rw [hy, NK.GlobalCFT.Idele.mul_apply, NK.GlobalCFT.Idele.inv_apply, hzero, inv_one,
      mul_one, Work.SSGRoute.ZDataMup.principalIdele_apply_eq_localImageAt]
  -- the local product is the hypothesis `hTfix`
  have hT'prod : NK.CFTLib.IdeleHasse.cprod (fun a b : Multiplicative (ZMod p) => mul_comm a b) T'
        (fun 𝔭 => Ψ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
          (y (NK.GlobalCFT.Place.ofFinite 𝔭))))
      = ∏ 𝔭 ∈ T', χ (Φ (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite 𝔭)
          (NK.CFTLib.IdeleHasse.localImageAt (K := ↥K) (NK.GlobalCFT.Place.ofFinite 𝔭) a))) := by
    rw [cprod_eq_finset_prod]
    exact Finset.prod_congr rfl (fun 𝔭 h𝔭 => by rw [hyT 𝔭 h𝔭, hΨapply])
  -- `Ψ y = (Ψ 𝔡)⁻¹`
  have hyval : Ψ y
      = (Ψ (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a)))⁻¹ := by
    rw [hy, map_mul, map_inv, hprinΨ a, one_mul]
  have hkey : (Ψ (NK.NUV2.RouteB.RayModulus.fracIdele
      (Work.SSGRoute.tFreePart (K := ↥K) T' a)))⁻¹ = 1 := by
    rw [← hyval, hPF, hImage, hT'prod, hTfix]
  have hPsi : Ψ (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))
      = 1 := inv_eq_one.mp hkey
  rw [show χ (Φ (NK.NUV2.RouteB.RayModulus.fracIdele
        (Work.SSGRoute.tFreePart (K := ↥K) T' a)))
      = Ψ (NK.NUV2.RouteB.RayModulus.fracIdele (Work.SSGRoute.tFreePart (K := ↥K) T' a))
      from (hΨapply _).symm, hPsi]

end Work.SSG8Escape
