import Mathlib
import Submission.Work.CurveBasics.Order.module_finite_integralClosure_of_ringEquiv
import Submission.Work.CurveBasics.Order.kx_pure_insep
import Submission.Work.CurveBasics.Order.perfectClosure_adjoin_gen_aux
import Submission.Work.CurveBasics.Order.integralClosure_adjoin_finite_general_assembly

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped IntermediateField.algebraAdjoinAdjoin
open IntermediateField

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000

namespace Work.CurveBasics.Order

/-- Gluing: if `A ⊆ B ⊆ N ⊆ L`, `B` is a finite `A`-algebra, `N` is the fraction field of `B`
(with `L / N` finite separable), and the integral closure `B^int_L` is finite over `B`, then the
integral closure `A^int_L` is finite over `A`. -/
theorem glue_general_rtp
    {A B N L : Type*} [CommRing A] [CommRing B] [Field N] [Field L]
    [Algebra A B] [Algebra A N] [Algebra B N] [IsScalarTower A B N] [IsFractionRing B N]
    [Algebra A L] [Algebra N L] [Algebra B L] [IsScalarTower A N L] [IsScalarTower B N L]
    [IsScalarTower A B L]
    [FiniteDimensional N L] [Algebra.IsSeparable N L]
    [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B]
    (h1 : Module.Finite A B) :
    Module.Finite A ↥(integralClosure A L) := by
  haveI : Module.Finite A B := h1
  haveI h3 : Module.Finite B ↥(integralClosure B L) :=
    IsIntegralClosure.finite B N L ↥(integralClosure B L)
  have h4 : Module.Finite A ↥(integralClosure B L) :=
    Module.Finite.trans B ↥(integralClosure B L)
  have hEq : Subalgebra.restrictScalars A (integralClosure B L) = integralClosure A L := by
    ext y
    rw [Subalgebra.mem_restrictScalars, mem_integralClosure_iff, mem_integralClosure_iff]
    exact ⟨fun hy => isIntegral_trans (A := B) y hy, fun hy => IsIntegral.tower_top hy⟩
  rw [← hEq]
  exact h4

/-- **The normal case.**  If `x` is transcendental over `k` and `L / k(x)` is a finite *normal*
extension, then the integral closure of `k[x]` in `L` is a finite `k[x]`-module.

Write `K := k(x)`, `A := k[x]` and `P := perfectClosure K L`, the largest purely inseparable
subextension of `L / K`.  Then `P / K` is finite purely inseparable, so `k[x]^int ⊆ P` is finite
over `k[x]` (`kx_pure_insep`); `L / P` is finite separable because `L / K` is normal
(`perfectClosure_separable_of_normal`); and `k[x]^int ⊆ P` is an integrally closed Noetherian
domain with fraction field `P`, so `glue_general_rtp` finishes. -/
theorem normal_case {k L : Type*} [Field k] [Field L] [Algebra k L] (x : L)
    (hx : Transcendental k x)
    [FiniteDimensional (IntermediateField.adjoin k ({x} : Set L)) L]
    [Normal (IntermediateField.adjoin k ({x} : Set L)) L] :
    Module.Finite ↥(Algebra.adjoin k ({x} : Set L))
      ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set L)) L) := by
  classical
  -- ===================== Setup =====================
  let A : Subalgebra k L := Algebra.adjoin k ({x} : Set L)
  let K : IntermediateField k L := IntermediateField.adjoin k ({x} : Set L)
  have hxK : x ∈ K := IntermediateField.mem_adjoin_simple_self k x
  have hSTAKLfull : IsScalarTower ↥(Algebra.adjoin k ({x} : Set L))
      ↥(IntermediateField.adjoin k ({x} : Set L)) L := inferInstance
  have hFrAKfull : IsFractionRing ↥(Algebra.adjoin k ({x} : Set L))
      ↥(IntermediateField.adjoin k ({x} : Set L)) := inferInstance
  haveI hSTAKL : IsScalarTower ↥A ↥K L := hSTAKLfull
  haveI hFrAK : IsFractionRing ↥A ↥K := hFrAKfull
  let P : IntermediateField ↥K L := perfectClosure ↥K L
  haveI hfdK : FiniteDimensional ↥K L := ‹_›
  haveI halgK : Algebra.IsAlgebraic ↥K L := Algebra.IsAlgebraic.of_finite ↥K L
  haveI hnrmK : Normal ↥K L := ‹_›
  haveI hfdKP : FiniteDimensional ↥K ↥P := inferInstance
  haveI hpiKP : IsPurelyInseparable ↥K ↥P := inferInstance
  haveI hfdPL : FiniteDimensional ↥P L := inferInstance
  haveI hsepPL : Algebra.IsSeparable ↥P L :=
    perfectClosure_separable_of_normal (K := ↥K) (L := L)
  -- `A` acting on `P`
  have tAKP : IsScalarTower ↥A ↥K ↥P :=
    IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI := tAKP
  have tAPL : IsScalarTower ↥A ↥P L :=
    IsScalarTower.of_algebraMap_eq (fun a => rfl)
  haveI := tAPL
  -- ===================== the element y = image of x in P =====================
  have hxP : x ∈ (P : Set L) := by
    have h1 : ((⟨x, hxK⟩ : ↥K) : L) = x := rfl
    rw [← h1]
    exact Subalgebra.algebraMap_mem _ (⟨x, hxK⟩ : ↥K)
  let y : ↥P := ⟨x, hxP⟩
  have hyval : (y : L) = x := rfl
  obtain ⟨hyT, hyfd, hypi⟩ := perfectClosure_adjoin_gen_aux x hx y hyval
  -- ===================== pure case =====================
  haveI hfdA' : FiniteDimensional (IntermediateField.adjoin k ({y} : Set ↥P)) ↥P := hyfd
  haveI hpiA' : IsPurelyInseparable (IntermediateField.adjoin k ({y} : Set ↥P)) ↥P := hypi
  have hpure : Module.Finite ↥(Algebra.adjoin k ({y} : Set ↥P))
      ↥(integralClosure ↥(Algebra.adjoin k ({y} : Set ↥P)) ↥P) :=
    kx_pure_insep y hyT
  -- ===================== transfer to A = k[x] =====================
  haveI hSTkPL : IsScalarTower k ↥P L := IsScalarTower.of_algebraMap_eq (fun c => rfl)
  have hinclP : Function.Injective (IsScalarTower.toAlgHom k ↥P L) := by
    intro a b h; exact Subtype.ext h
  have hmap : (Algebra.adjoin k ({y} : Set ↥P)).map (IsScalarTower.toAlgHom k ↥P L) = A := by
    rw [AlgHom.map_adjoin]
    congr 1
    ext z
    simp only [Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨w, rfl, rfl⟩; exact hyval
    · intro hz; exact ⟨y, rfl, hz.symm⟩
  have h1 : Module.Finite ↥A ↥(integralClosure ↥A ↥P) := by
    have hmem : ∀ a : ↥A, (algebraMap ↥A ↥P a : ↥P) ∈ Algebra.adjoin k ({y} : Set ↥P) := by
      intro a
      have ha : (a : L) ∈ (Algebra.adjoin k ({y} : Set ↥P)).map
          (IsScalarTower.toAlgHom k ↥P L) := by
        rw [hmap]; exact a.2
      obtain ⟨z, hz, hfz⟩ := Subalgebra.mem_map.mp ha
      have hza : algebraMap ↥A ↥P a = z := by
        apply Subtype.ext
        rw [show (((algebraMap ↥A ↥P a : ↥P) : L)) = (a : L) from
          (IsScalarTower.algebraMap_apply ↥A ↥P L a).symm]
        exact hfz.symm
      rw [hza]
      exact hz
    let e' : ↥A →+* ↥(Algebra.adjoin k ({y} : Set ↥P)) :=
      { toFun := fun a => ⟨algebraMap ↥A ↥P a, hmem a⟩
        map_one' := Subtype.ext (map_one _)
        map_mul' := fun a b => Subtype.ext (map_mul _ _ _)
        map_zero' := Subtype.ext (map_zero _)
        map_add' := fun a b => Subtype.ext (map_add _ _ _) }
    have hbij : Function.Bijective e' := by
      constructor
      · intro a b hab
        apply Subtype.ext
        have h2 : ((algebraMap ↥A ↥P a : ↥P) : L) = ((algebraMap ↥A ↥P b : ↥P) : L) :=
          congrArg Subtype.val (congrArg Subtype.val hab)
        rw [show (((algebraMap ↥A ↥P a : ↥P) : L)) = (a : L) from
              (IsScalarTower.algebraMap_apply ↥A ↥P L a).symm,
            show (((algebraMap ↥A ↥P b : ↥P) : L)) = (b : L) from
              (IsScalarTower.algebraMap_apply ↥A ↥P L b).symm] at h2
        exact h2
      · intro z
        have hza : (z : L) ∈ A := by
          have h1 : (z : L) ∈ (Algebra.adjoin k ({y} : Set ↥P)).map
              (IsScalarTower.toAlgHom k ↥P L) :=
            Subalgebra.mem_map.mpr ⟨z, z.2, rfl⟩
          rwa [hmap] at h1
        refine ⟨⟨(z : L), hza⟩, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        show (((algebraMap ↥A ↥P ⟨(z : L), hza⟩ : ↥P) : L)) = ((z : ↥P) : L)
        rw [show (((algebraMap ↥A ↥P ⟨(z : L), hza⟩ : ↥P) : L))
            = ((⟨(z : L), hza⟩ : ↥A) : L) from
          (IsScalarTower.algebraMap_apply ↥A ↥P L ⟨(z : L), hza⟩).symm]
    exact module_finite_integralClosure_of_ringEquiv
      (RingEquiv.ofBijective e' hbij) (by ext a; rfl) hpure
  -- ===================== glue =====================
  haveI hNoethA : IsNoetherianRing ↥A :=
    isNoetherianRing_of_ringEquiv (Polynomial k)
      (Polynomial.algEquivOfTranscendental k x hx).toRingEquiv
  haveI hICA : IsIntegrallyClosed ↥A :=
    IsIntegrallyClosed.of_equiv (Polynomial.algEquivOfTranscendental k x hx).toRingEquiv
  haveI h1i : Module.Finite ↥A ↥(integralClosure ↥A ↥P) := h1
  haveI hFrB : IsFractionRing ↥(integralClosure ↥A ↥P) ↥P :=
    IsIntegralClosure.isFractionRing_of_finite_extension ↥A ↥K ↥P ↥(integralClosure ↥A ↥P)
  haveI hICB : IsIntegrallyClosed ↥(integralClosure ↥A ↥P) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension ↥K
  haveI hNoethB : IsNoetherianRing ↥(integralClosure ↥A ↥P) :=
    IsNoetherianRing.of_finite ↥A _
  exact glue_general_rtp (A := ↥A) (B := ↥(integralClosure ↥A ↥P)) (N := ↥P) (L := L) h1

/-- **Reduction of the general case to the purely inseparable case.**

The statement holds for an arbitrary finite extension `L / k(x)` once it is known for all finite
extensions `E / k(y)` with `y` transcendental and `E / k(y)` purely inseparable: pass to the
normal closure `M` of `L` over `K = k(x)` (which is finite normal over `K`, hence over `k(y)`
where `y` is the image of `x`), apply `normal_case` there, and descend along the embedding
`L ↪ M` (see `normalClosure_reduction`). -/
theorem reduce_to_pure_case {k L : Type*} [Field k] [Field L] [Algebra k L] (x : L)
    (hx : Transcendental k x) [FiniteDimensional (IntermediateField.adjoin k ({x} : Set L)) L]
    (hPI : ∀ {E : Type*} [Field E] [Algebra k E] (y : E), Transcendental k y →
      FiniteDimensional (IntermediateField.adjoin k ({y} : Set E)) E →
      IsPurelyInseparable (IntermediateField.adjoin k ({y} : Set E)) E →
      Module.Finite ↥(Algebra.adjoin k ({y} : Set E))
        ↥(integralClosure ↥(Algebra.adjoin k ({y} : Set E)) E)) :
    Module.Finite ↥(Algebra.adjoin k ({x} : Set L))
      ↥(integralClosure ↥(Algebra.adjoin k ({x} : Set L)) L) :=
  normalClosure_reduction (fun y _ _ hy => normal_case y hy) x hx

end Work.CurveBasics.Order
