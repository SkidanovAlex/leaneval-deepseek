import Mathlib
import Submission.Work.Hering.AppVII.brauer_lift_aux
import Submission.Work.Hering.AppVII.iota_injective
import Submission.Work.Hering.AppVII.brauer_central
import Submission.Work.CharCore.Main
import Submission.Work.CharCore.classFun_eq_zero_of_orthogonal
import Submission.Work.CharCore.irr_orthonormal
import Submission.Work.CharCore.star_Irr

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Orthogonality of the lifted primitive central idempotents `tildeE χ`

Let `A` be a finite group, `n = |A|`, `R = ℤ[ζ_n] = ℤ[X]/(Φ_n)` and, for an irreducible
complex character `χ` of `A`,

`tildeE χ = (χ(1) : R) • ∑ g : A, charLift χ g⁻¹ • single g 1 ∈ R[A]`

the `|A|`-multiple of the central primitive idempotent `e_χ = (χ(1)/|A|) ∑_g χ(g⁻¹) g` of
`ℂ[A]`, lifted to `R[A]` along `iota : R → ℂ`
(`Submission/Work/Hering/AppVII/brauer_lift_aux.lean`, `brauer_central.lean`).

Here we prove that `tildeE χ` and `tildeE χ'` are orthogonal for distinct irreducible
characters:

`tildeE χ * tildeE χ' = 0`.

The proof is the standard transfer along the injective ring homomorphism
`MonoidAlgebra.map (iota |A|) : R[A] → ℂ[A]` (`Work.Hering.AppVII.iota_injective`):

* `Work.Hering.AppVII.Eℂ χ = (χ(1) : ℂ) • ∑_g χ(g⁻¹) g = (χ(1) : ℂ) • classSum χ` is the
  image of `tildeE χ` (`map_iota_tildeE`), and `map (iota |A|)` is injective;
* in `ℂ[A]`, `classSum χ = ∑_g χ(g⁻¹) g` acts on every simple submodule `N` of the regular
  module as a scalar, and it acts as `0` on `N` whenever `χ` is not the character of `N`
  (`classSum_irr_smul_simple_eq_zero`): the operator `T = ∑_g χ(g⁻¹) ρ_N(g)` is
  `ℂ[A]`-linear (because `χ` is a class function, hence `classSum χ` is central), so it is
  scalar on the simple module `N`, with trace `∑_g χ(g⁻¹) χ_N(g) = |A| ⟨χ, χ_N⟩ = 0` by the
  first orthogonality relation;
* an element of `ℂ[A]` which annihilates every `N` of the spanning family
  `Work.CharCore.irrSubmodules A` is `0` (`eq_zero_of_smul_irrSubmodules`);
* hence `classSum χ * classSum χ' = 0` (`classSum_mul_classSum_eq_zero`) and so
  `Eℂ χ * Eℂ χ' = 0`.
-/

noncomputable section

open Classical Finset

open scoped BigOperators

namespace Work.NormalComplement.AppVII

/-! ## A central element of the group algebra which annihilates every simple submodule is `0` -/

/-- If a central element `z` of `ℂ[G]` annihilates every member of the chosen spanning family
`irrSubmodules G` of simple submodules of the regular module, then `z = 0`. -/
theorem eq_zero_of_smul_irrSubmodules {G : Type*} [Group G] [Fintype G]
    (z : MonoidAlgebra ℂ G) (hcent : ∀ a : MonoidAlgebra ℂ G, z * a = a * z)
    (hz : ∀ N ∈ Work.CharCore.irrSubmodules G, ∀ x : N, z • x = 0) : z = 0 := by
  let K : Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G) :=
    { carrier := {y | z * y = 0}
      add_mem' := by
        intro a b ha hb
        show z * (a + b) = 0
        rw [mul_add, ha, hb, add_zero]
      zero_mem' := by
        show z * 0 = 0
        simp
      smul_mem' := by
        intro a b hb
        show z * (a * b) = 0
        rw [← mul_assoc, hcent a, mul_assoc, hb, mul_zero] }
  have hle : sSup ((Work.CharCore.irrSubmodules G :
      Finset (Submodule (MonoidAlgebra ℂ G) (MonoidAlgebra ℂ G))) : Set _) ≤ K := by
    refine sSup_le fun N hN y hy => ?_
    show z * y = 0
    have hthis := hz N hN ⟨y, hy⟩
    simpa using congrArg Subtype.val hthis
  have htop : K = ⊤ := top_unique (by rw [← Work.CharCore.sSup_irrSubmodules G]; exact hle)
  have hone : z * (1 : MonoidAlgebra ℂ G) = 0 := by
    have : (1 : MonoidAlgebra ℂ G) ∈ K := by rw [htop]; exact Submodule.mem_top
    exact this
  simpa using hone

/-! ## `classSum χ` kills the simple submodules not affording `χ` -/

/-- The class sum `classSum χ = ∑_g χ(g⁻¹) g ∈ ℂ[G]` attached to an irreducible character `χ`
acts as `0` on a simple submodule `N` of the regular module whose character differs from `χ`.

Indeed the operator `T = ∑_g χ(g⁻¹) ρ_N(g)` is `ℂ[G]`-linear (because `classSum χ` is central),
hence scalar on the simple module `N`; its trace is `∑_g χ(g⁻¹) χ_N(g) = |G| ⟨χ, χ_N⟩ = 0` by
the first orthogonality relation. -/
theorem classSum_irr_smul_simple_eq_zero {G : Type*} [Group G] [Fintype G]
    (χ : G → ℂ) (hχ : χ ∈ Work.CharCore.Irr G)
    (N : Submodule (Work.CharCore.groupAlgebra G) (Work.CharCore.groupAlgebra G))
    (hN : N ∈ Work.CharCore.irrSubmodules G)
    (hne : χ ≠ (Work.CharCore.submoduleRep N).character) :
    ∀ x : N, Work.CharCore.classSum χ • x = 0 := by
  classical
  have hcent : ∀ a : MonoidAlgebra ℂ G,
      Work.CharCore.classSum χ * a = a * Work.CharCore.classSum χ :=
    Work.CharCore.classSum_central (Work.CharCore.isClassFun_of_mem_Irr hχ)
  haveI hsimp : IsSimpleModule (Work.CharCore.groupAlgebra G) N :=
    Work.CharCore.isSimpleModule_of_mem_irrSubmodules N hN
  haveI hnt : Nontrivial N := IsSimpleModule.nontrivial (Work.CharCore.groupAlgebra G) N
  set T : N →ₗ[ℂ] N := ∑ g : G, χ (g⁻¹) • (Work.CharCore.submoduleRep N) g with hTdef
  have hTapply : ∀ y : N, T y = Work.CharCore.classSum χ • y := by
    intro y
    rw [hTdef, Work.CharCore.classSum, Finset.sum_smul, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, smul_assoc]
    congr 1
  have hTsmul : ∀ (a : MonoidAlgebra ℂ G) (y : N), T (a • y) = a • T y := by
    intro a y
    rw [hTapply, hTapply, ← mul_smul, hcent a, mul_smul]
  have htrace : LinearMap.trace ℂ N T
      = ∑ g : G, χ (g⁻¹) * (Work.CharCore.submoduleRep N).character g := by
    rw [hTdef, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [map_smul, smul_eq_mul]
    rfl
  have hψIrr : (Work.CharCore.submoduleRep N).character ∈ Work.CharCore.Irr G := by
    rw [Work.CharCore.Irr]
    exact Finset.mem_image.mpr ⟨N, hN, rfl⟩
  have hsum0 : (∑ g : G, χ (g⁻¹) * (Work.CharCore.submoduleRep N).character g) = 0 := by
    have hcard : (Fintype.card G : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    have h1 : (∑ g : G, χ (g⁻¹) * (Work.CharCore.submoduleRep N).character g)
        = ∑ g : G, χ g * (Work.CharCore.submoduleRep N).character g⁻¹ := by
      rw [← Equiv.sum_comp (Equiv.inv G)
        (fun g : G => χ g * (Work.CharCore.submoduleRep N).character g⁻¹)]
      refine Finset.sum_congr rfl fun g _ => ?_
      simp
    rw [h1]
    have h2 : ∀ g : G, (Work.CharCore.submoduleRep N).character g⁻¹
        = starRingEnd ℂ ((Work.CharCore.submoduleRep N).character g) :=
      fun g => (Work.CharCore.star_Irr _ hψIrr g).symm
    simp only [h2]
    have h3 : (∑ g : G, χ g * starRingEnd ℂ ((Work.CharCore.submoduleRep N).character g))
        = (Fintype.card G : ℂ) *
            Work.CharCore.cfInner χ (Work.CharCore.submoduleRep N).character := by
      rw [Work.CharCore.cfInner_apply, ← mul_assoc, mul_inv_cancel₀ hcard, one_mul]
    rw [h3, Work.CharCore.irr_orthonormal χ _ hχ hψIrr, if_neg hne, mul_zero]
  have htrace0 : LinearMap.trace ℂ N T = 0 := by rw [htrace, hsum0]
  -- the `ℂ[G]`-linear endomorphism `T` of the simple module `N` is scalar
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  rw [Module.End.hasEigenvector_iff] at hv
  obtain ⟨hv_mem, hv_ne⟩ := hv
  rw [Module.End.mem_eigenspace_iff] at hv_mem
  have hM_ne : Submodule.span (MonoidAlgebra ℂ G) ({v} : Set N) ≠ ⊥ := by
    intro hbot
    have hvbot : v ∈ (⊥ : Submodule (MonoidAlgebra ℂ G) N) := by
      rw [← hbot]
      exact Submodule.subset_span (Set.mem_singleton v)
    exact hv_ne (by simpa using hvbot)
  have hM_top : Submodule.span (MonoidAlgebra ℂ G) ({v} : Set N) = ⊤ :=
    (eq_bot_or_eq_top _).resolve_left hM_ne
  have hscalar : ∀ y : N, T y = c • y := by
    intro y
    have hy : y ∈ Submodule.span (MonoidAlgebra ℂ G) ({v} : Set N) := by
      rw [hM_top]; exact Submodule.mem_top
    exact Submodule.span_induction (s := ({v} : Set N))
      (p := fun y _ => T y = c • y)
      (fun z hz => by
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact hv_mem)
      (by rw [map_zero, smul_zero])
      (fun z w _ _ hz hw => by rw [map_add, hz, hw, smul_add])
      (fun a z _ hz => by
        rw [hTsmul, hz]
        exact (smul_comm c a z).symm)
      hy
  have hT_eq : T = c • LinearMap.id := by
    apply LinearMap.ext
    intro y
    rw [LinearMap.smul_apply, LinearMap.id_apply]
    exact hscalar y
  have htrace_scalar : LinearMap.trace ℂ N T = c * (Module.finrank ℂ N : ℂ) := by
    rw [hT_eq, map_smul, LinearMap.trace_id, smul_eq_mul]
  have hfind : (Module.finrank ℂ N : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos_iff.mpr hnt).ne'
  have hc0 : c = 0 := by
    have h2 : c * (Module.finrank ℂ N : ℂ) = 0 := by rw [← htrace_scalar, htrace0]
    exact (mul_eq_zero.mp h2).resolve_right hfind
  have hT0 : T = 0 := by rw [hT_eq, hc0]; simp
  intro x
  rw [← hTapply x, hT0]
  simp

/-! ## Orthogonality of the class sums -/

/-- The class sums of distinct irreducible characters are orthogonal in `ℂ[A]`:
`classSum χ * classSum χ' = 0`. -/
theorem classSum_mul_classSum_eq_zero {A : Type*} [Group A] [Fintype A]
    {χ χ' : A → ℂ} (hχ : χ ∈ Work.CharCore.Irr A) (hχ' : χ' ∈ Work.CharCore.Irr A)
    (hne : χ ≠ χ') :
    Work.CharCore.classSum χ * Work.CharCore.classSum χ' = 0 := by
  have hcent : ∀ a : MonoidAlgebra ℂ A,
      (Work.CharCore.classSum χ * Work.CharCore.classSum χ') * a =
        a * (Work.CharCore.classSum χ * Work.CharCore.classSum χ') := by
    intro a
    rw [mul_assoc, Work.CharCore.classSum_central (Work.CharCore.isClassFun_of_mem_Irr hχ') a,
      ← mul_assoc, Work.CharCore.classSum_central (Work.CharCore.isClassFun_of_mem_Irr hχ) a,
      mul_assoc]
  refine eq_zero_of_smul_irrSubmodules (Work.CharCore.classSum χ * Work.CharCore.classSum χ')
    hcent ?_
  intro N hN x
  by_cases hψ : χ' = (Work.CharCore.submoduleRep N).character
  · have hne' : χ ≠ (Work.CharCore.submoduleRep N).character := by rw [← hψ]; exact hne
    rw [mul_smul, classSum_irr_smul_simple_eq_zero χ hχ N hN hne']
  · rw [mul_smul, classSum_irr_smul_simple_eq_zero χ' hχ' N hN hψ, smul_zero]

/-! ## The image of `tildeE χ` in `ℂ[A]` -/

/-- The image of the lifted idempotent `tildeE χ` under `MonoidAlgebra.map (iota |A|)` is the
element `Eℂ χ = (χ(1) : ℂ) • ∑_g χ(g⁻¹) g` of `ℂ[A]`. -/
theorem map_iota_tildeE {A : Type*} [Group A] [Fintype A] (χ : A → ℂ)
    (hχ : χ ∈ Work.CharCore.Irr A) :
    MonoidAlgebra.map (Work.Hering.AppVII.iota (Nat.card A)) (Work.Hering.AppVII.tildeE χ hχ)
      = Work.Hering.AppVII.Eℂ χ := by
  ext k
  rw [MonoidAlgebra.coeff_map, Finsupp.mapRange_apply, Work.Hering.AppVII.Eℂ,
    MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [Work.Hering.AppVII.tildeE]
  simp only [MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    MonoidAlgebra.coeff_smul_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  show (Work.Hering.AppVII.iota (Nat.card A))
      (↑(Work.CharCore.irrDeg χ) * Work.Hering.AppVII.charLift χ hχ k⁻¹) = _
  rw [map_mul, Work.Hering.AppVII.iota_charLift, map_natCast]

/-- `Eℂ χ` is the `classSum` of `χ` scaled by the degree: the two are definitionally the same
element of `ℂ[A]`. -/
theorem Eℂ_eq_smul_classSum {A : Type*} [Group A] [Fintype A] (χ : A → ℂ) :
    Work.Hering.AppVII.Eℂ χ = (Work.CharCore.irrDeg χ : ℂ) • Work.CharCore.classSum χ := rfl

/-- `Eℂ χ * Eℂ χ' = 0` for distinct irreducible characters `χ ≠ χ'`. -/
theorem Eℂ_mul_Eℂ_eq_zero {A : Type*} [Group A] [Fintype A] {χ χ' : A → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr A) (hχ' : χ' ∈ Work.CharCore.Irr A) (hne : χ ≠ χ') :
    Work.Hering.AppVII.Eℂ χ * Work.Hering.AppVII.Eℂ χ' = 0 := by
  have hcs : Work.CharCore.classSum χ * Work.CharCore.classSum χ' = 0 :=
    classSum_mul_classSum_eq_zero hχ hχ' hne
  rw [Eℂ_eq_smul_classSum, Eℂ_eq_smul_classSum, smul_mul_smul_comm, hcs, smul_zero]

/-! ## The main theorem -/

/-- **Orthogonality of the lifted central primitive idempotents.** For distinct irreducible
complex characters `χ ≠ χ'` of a finite group `A`, the lifted idempotents
`tildeE χ, tildeE χ' ∈ ℤ[ζ_|A|][A]` are orthogonal: `tildeE χ * tildeE χ' = 0`. -/
theorem LiftTildeEMulEqZero {A : Type*} [Group A] [Fintype A] {χ χ' : A → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr A) (hχ' : χ' ∈ Work.CharCore.Irr A) (hne : χ ≠ χ') :
    Work.Hering.AppVII.tildeE χ hχ * Work.Hering.AppVII.tildeE χ' hχ' = 0 := by
  have hE : Work.Hering.AppVII.Eℂ χ * Work.Hering.AppVII.Eℂ χ' = 0 :=
    Eℂ_mul_Eℂ_eq_zero hχ hχ' hne
  refine MonoidAlgebra.map_injective (M := A)
    (↑(Work.Hering.AppVII.iota (Nat.card A)) :
      Work.Hering.AppVII.CycloRing (Nat.card A) →+ ℂ)
    (show Function.Injective (↑(Work.Hering.AppVII.iota (Nat.card A))) from
      Work.Hering.AppVII.iota_injective) ?_
  rw [MonoidAlgebra.map_mul, map_iota_tildeE, map_iota_tildeE, hE, MonoidAlgebra.map_zero]

end Work.NormalComplement.AppVII
