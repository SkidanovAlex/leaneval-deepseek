import Mathlib.GroupTheory.Nilpotent
import Mathlib.Tactic.Have
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Submission.Work.CohomologicallyTrivial.shortComplexOfStableSubmodule_shortExact
import Submission.Work.SSGRoute.ExtChain.ext2_zmod_trivial
import Submission.Work.SSGRoute.ExtChain.ext_iso_subsingleton
import Submission.Work.SSGRoute.ExtChain.finite_ptorsion_module
import Submission.Work.SSGRoute.ExtChain.pgroup_invariants_coeff_rep
import Submission.Work.SSGRoute.powHomRepDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Ext²(N,U)` vanishes for `N` a `p`-torsion module over a `p`-group

The engine of this file is the induction on `Nat.card N.V` described in the statement of
`ext2_ptorsion_pgroup_vanish`; the file below builds it in pieces.
-/

namespace Work.SSGRoute.ExtChain

open CategoryTheory SSGRoute.PTExt

attribute [local instance 10000] Rep.hV2 Rep.hV1 Submodule.module
attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass
attribute [local instance 1] ULift.distribSMul ULift.distribMulAction ULift.smulWithZero
attribute [local instance 1] ULift.mulActionWithZero

noncomputable section

set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Fintype G]

/-! ## The base computation: `Ext²` of the trivial `𝔽_p`-representation -/

/-- `Ext²_G(𝔽_p, U)` vanishes whenever `H¹(G,U) = Ext¹(ℤ,U)` and `H²(G,U) = Ext²(ℤ,U)` do.
This is the contravariant long exact sequence of the coefficient sequence
`0 → ℤ --p--> ℤ → 𝔽_p → 0` at `n₀ = 1`. -/
theorem ext2_zmod_trivial_subsingleton (U : Rep.{0} Coeff G)
    (hU1 : Subsingleton (Abelian.Ext.{0} (unitRep G) U 1))
    (hU2 : Subsingleton (Abelian.Ext.{0} (unitRep G) U 2)) :
    Subsingleton (Abelian.Ext.{0} (Rep.trivial Coeff G (ZMod p)) U 2) :=
  ext2_zmod_trivial U hU1 hU2

/-! ## Two general `Ext`-facts -/

/-- `Ext` in the first variable is invariant under isomorphism. -/
theorem subsingleton_ext_iff_of_iso {C : Type*} [Category C] [Abelian C] [HasExt C]
    {X Y Z : C} (e : X ≅ Y) (n : ℕ) :
    Subsingleton (Abelian.Ext X Z n) ↔ Subsingleton (Abelian.Ext Y Z n) :=
  ext_iso_subsingleton e n

/-- A representation whose underlying module is a subsingleton has vanishing `Ext`
(its endomorphism ring is trivial). -/
theorem subsingleton_ext_of_subsingleton_carrier {M : Rep.{0} Coeff G} (h : Subsingleton M.V)
    (U : Rep.{0} Coeff G) (n : ℕ) : Subsingleton (Abelian.Ext.{0} M U n) := by
  have hhom : Subsingleton (M ⟶ M) := by
    refine ⟨fun f g => Rep.hom_ext ?_⟩
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    exact Subsingleton.elim _ _
  refine ⟨fun x y => ?_⟩
  have h1 : (𝟙 M : M ⟶ M) = 0 := Subsingleton.elim _ _
  have h2 : (Abelian.Ext.mk₀ (𝟙 M) : Abelian.Ext.{0} M M 0) = 0 := by
    rw [h1, Abelian.Ext.mk₀_zero]
  have hx : x = 0 := by
    rw [← Abelian.Ext.mk₀_id_comp x, h2, Abelian.Ext.zero_comp]
  have hy : y = 0 := by
    rw [← Abelian.Ext.mk₀_id_comp y, h2, Abelian.Ext.zero_comp]
  rw [hx, hy]

/-! ## `p`-group invariants over `Coeff` -/

/-- A nonzero `Coeff`-representation of a finite `p`-group on which `p` acts as `0` has a nonzero
fixed vector.  This is `Work.CohomologicallyTrivial.pgroup_invariants_ne_bot_int` with `ℤ`
replaced by `Coeff = ULift ℤ`. -/
theorem pgroup_invariants_coeff (hpG : IsPGroup p G) (N : Rep.{0} Coeff G)
    (hN : ∀ x : N.V, p • x = 0) [Nontrivial N.V] :
    ∃ v : N.V, v ≠ 0 ∧ ∀ g : G, N.ρ g v = v :=
  pgroup_invariants_coeff_rep hpG N hN

/-! ## Finiteness of `p`-torsion modules of finite type -/

/-- A finitely generated `ℤ`-module killed by the prime `p` is finite. -/
theorem finite_of_moduleFinite_ptorsion (M : Type) [AddCommGroup M] [Module ℤ M]
    (hfin : Module.Finite ℤ M) (hM : ∀ x : M, p • x = 0) : Finite M :=
  finite_ptorsion_module M hfin hM

/-! ## The arithmetic lemma -/

/-- If `v ≠ 0` is killed by `(p : Coeff)` then the scalar `c` can only kill `v` when `p ∣ c.down`:
the annihilator of `v` is contained in `p·ℤ`. -/
theorem dvd_of_smul_eq_zero {V : Type} [AddCommGroup V] [Module Coeff V] {v : V} (hv : v ≠ 0)
    (hpv : (p : Coeff) • v = 0) {c : Coeff} (hc : c • v = 0) : (p : ℤ) ∣ c.down := by
  have hpv' : (p : ℤ) • v = 0 := by
    rw [← Int.cast_smul_eq_zsmul Coeff]
    simpa using hpv
  have hcv : c.down • v = 0 := by
    rw [← Int.cast_smul_eq_zsmul Coeff]
    rw [show ((c.down : ℤ) : Coeff) = c from ULift.ext rfl]
    exact hc
  have hord : addOrderOf v = p := by
    refine addOrderOf_eq_prime ?_ hv
    rw [← natCast_zsmul]
    exact hpv'
  rw [← hord]
  exact (addOrderOf_dvd_iff_zsmul_eq_zero (x := v) (i := c.down)).mpr hcv

/-- If the annihilator `K` of a nonzero `p`-torsion vector is exactly `p·Coeff`, then `unitRep G`
and the subrepresentation on `K` are isomorphic (both are the trivial representation on `ℤ`). -/
theorem unitRep_iso_subRep {K : Submodule Coeff Coeff}
    (hK : ∀ g : G, K ≤ Submodule.comap ((unitRep G).ρ g) K)
    (hpK : ∀ c : Coeff, (p : Coeff) * c ∈ K)
    (hKp : ∀ c ∈ K, ∃ d : Coeff, c = (p : Coeff) * d) :
    Nonempty (unitRep G ≅ Work.CohomologicallyTrivial.subRep (unitRep G) K hK) := by
  -- the action of the subrepresentation (of the trivial representation) is trivial
  have htriv : ∀ (g : G) (x : ↥K),
      (Work.CohomologicallyTrivial.subRep (unitRep G) K hK).ρ g x = x := by
    intro g x
    apply Subtype.ext
    simp only [Work.CohomologicallyTrivial.subRep, Representation.subrepresentation_apply,
      LinearMap.coe_restrict_apply, Representation.trivial_apply]
  -- multiplication by `p` is a `Coeff`-linear bijection `Coeff → ↥K`
  let f : Coeff →ₗ[Coeff] ↥K :=
    (LinearMap.mulLeft SSGRoute.PTExt.Coeff (p : Coeff)).codRestrict K (fun c => hpK c)
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have h2 : (p : Coeff) * a = (p : Coeff) * b := by
        have h3 : (f a : Coeff) = (f b : Coeff) := congrArg Subtype.val hab
        exact h3
      have hd : (p : ℤ) * a.down = (p : ℤ) * b.down := by
        have h3 := congrArg ULift.down h2
        exact h3
      have hpz : (p : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
      exact ULift.ext (mul_left_cancel₀ hpz hd)
    · intro y
      obtain ⟨d, hd⟩ := hKp y.1 y.2
      exact ⟨d, Subtype.ext hd.symm⟩
  let e : Coeff ≃ₗ[Coeff] ↥K := LinearEquiv.ofBijective f hf
  refine ⟨⟨Rep.ofHom ⟨e.toLinearMap, ?_⟩, Rep.ofHom ⟨e.symm.toLinearMap, ?_⟩, ?_, ?_⟩⟩
  · intro g
    apply LinearMap.ext
    intro c
    show e ((unitRep G).ρ g c) =
      (Work.CohomologicallyTrivial.subRep (unitRep G) K hK).ρ g (e c)
    rw [show (unitRep G).ρ g = LinearMap.id from Rep.trivial_ρ g, LinearMap.id_apply]
    exact (htriv g (e c)).symm
  · intro g
    apply LinearMap.ext
    intro x
    show e.symm ((Work.CohomologicallyTrivial.subRep (unitRep G) K hK).ρ g x) =
      (unitRep G).ρ g (e.symm x)
    rw [htriv g x, show (unitRep G).ρ g = LinearMap.id from Rep.trivial_ρ g, LinearMap.id_apply]
  · apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro c
    show e.symm (e c) = c
    exact e.symm_apply_apply c
  · apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro x
    show e (e.symm x) = x
    exact e.apply_symm_apply x

/-! ## Cardinality of submodules and quotients -/

/-- A proper submodule of a finite module has strictly smaller cardinality. -/
theorem natCard_subtype_lt {M : Type} [AddCommGroup M] (W : Submodule Coeff M) (hfin : Finite M)
    (h : W ≠ ⊤) : Nat.card ↥W < Nat.card M := by
  classical
  haveI := hfin
  haveI : Fintype ↥W := Fintype.ofFinite _
  haveI : Fintype M := Fintype.ofFinite _
  obtain ⟨x, hx⟩ : ∃ x : M, x ∉ W := by
    by_contra hc
    push_neg at hc
    exact h (top_unique fun y _ => hc y)
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Fintype.card_subtype_lt hx

/-- A nontrivial quotient of a finite module has strictly smaller cardinality. -/
theorem natCard_quotient_lt {M : Type} [AddCommGroup M] (W : Submodule Coeff M) (hfin : Finite M)
    (h : W ≠ ⊥) : Nat.card (M ⧸ W) < Nat.card M := by
  classical
  haveI := hfin
  haveI : Finite ↥W := Subtype.finite
  haveI : Finite (M ⧸ W) := Finite.of_surjective W.mkQ W.mkQ_surjective
  haveI : Fintype ↥W := Fintype.ofFinite _
  have hcard := Submodule.card_eq_card_quotient_mul_card (R := Coeff) W
  have h2 : 1 < Nat.card ↥W := by
    obtain ⟨w, hw⟩ : ∃ w : ↥W, w ≠ 0 := by
      by_contra hc
      push_neg at hc
      refine h (le_antisymm (fun y hy => ?_) bot_le)
      rw [Submodule.mem_bot]
      exact congrArg Subtype.val (hc ⟨y, hy⟩)
    have hinj : Function.Injective
        (fun i : Fin 2 => if (i : ℕ) = 0 then (0 : ↥W) else w) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    have hle : 2 ≤ Nat.card ↥W := by
      have := Nat.card_le_card_of_injective _ hinj
      simpa using this
    omega
  haveI : Nonempty (M ⧸ W) := ⟨0⟩
  have hq : 0 < Nat.card (M ⧸ W) := Nat.card_pos
  have hmul : Nat.card (M ⧸ W) < Nat.card ↥W * Nat.card (M ⧸ W) := by
    calc Nat.card (M ⧸ W) = Nat.card (M ⧸ W) * 1 := (Nat.mul_one _).symm
      _ < Nat.card (M ⧸ W) * Nat.card ↥W := Nat.mul_lt_mul_of_pos_left h2 hq
      _ = Nat.card ↥W * Nat.card (M ⧸ W) := Nat.mul_comm _ _
  rw [hcard]
  exact hmul

/-! ## The cyclic case: the kernel of `powHomRep` and the short exact sequence -/

/-- The kernel of the `G`-map `Coeff → N`, `1 ↦ v`, as a submodule of `Coeff`. -/
def powHomKer {N : Rep.{0} Coeff G} (v : N.V) (hv : ∀ g : G, N.ρ g v = v) :
    Submodule Coeff Coeff :=
  LinearMap.ker ((Rep.Hom.hom (Work.SSGRoute.powHomRep v hv)).toLinearMap)

/-- The kernel of `powHomRep v hv` is `G`-stable. -/
theorem powHomKer_stable {N : Rep.{0} Coeff G} (v : N.V) (hv : ∀ g : G, N.ρ g v = v) :
    ∀ g : G, powHomKer v hv ≤ Submodule.comap ((unitRep G).ρ g) (powHomKer v hv) := by
  intro g c hc
  rw [Submodule.mem_comap]
  show (Rep.Hom.hom (Work.SSGRoute.powHomRep v hv)) ((unitRep G).ρ g c) = 0
  rw [show (unitRep G).ρ g = LinearMap.id from Rep.trivial_ρ g]
  exact hc

/-- The short complex `0 → K → ℤ → N → 0` attached to the `G`-map `1 ↦ v`. -/
def powHomSES {N : Rep.{0} Coeff G} (v : N.V) (hv : ∀ g : G, N.ρ g v = v) :
    ShortComplex (Rep.{0} Coeff G) :=
  ShortComplex.mk
    (Work.CohomologicallyTrivial.subRepIncl (unitRep G) (powHomKer v hv) (powHomKer_stable v hv))
    (Work.SSGRoute.powHomRep v hv) (by
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro c
      show (Rep.Hom.hom (Work.SSGRoute.powHomRep v hv))
        ((Work.CohomologicallyTrivial.subRepIncl (unitRep G) (powHomKer v hv)
          (powHomKer_stable v hv)) c) = 0
      rw [show (Work.CohomologicallyTrivial.subRepIncl (unitRep G) (powHomKer v hv)
          (powHomKer_stable v hv)) c = (c : Coeff) from rfl]
      exact c.2)

/-- `0 → K → ℤ → N → 0` is short exact when `1 ↦ v` is surjective. -/
theorem powHomSES_shortExact {N : Rep.{0} Coeff G} (v : N.V) (hv : ∀ g : G, N.ρ g v = v)
    (hsurj : Function.Surjective ⇑(Rep.Hom.hom (Work.SSGRoute.powHomRep v hv))) :
    (powHomSES v hv).ShortExact := by
  let F : Rep.{0} Coeff G ⥤ ModuleCat Coeff := forget₂ (Rep.{0} Coeff G) (ModuleCat Coeff)
  refine ShortComplex.ShortExact.mk' ?_ ?_ ?_
  · refine (ShortComplex.exact_map_iff_of_faithful (S := powHomSES v hv) F).1 ?_
    rw [ShortComplex.moduleCat_exact_iff]
    intro x₂ hx₂
    exact ⟨⟨x₂, hx₂⟩, rfl⟩
  · rw [Rep.mono_iff_injective]
    intro a b hab
    exact Subtype.ext hab
  · rw [Rep.epi_iff_surjective]
    exact hsurj

/-! ## The induction -/

/-- Auxiliary: the induction on `Nat.card N.V`. -/
theorem ext2_aux (hpG : IsPGroup p G) (U : Rep.{0} Coeff G)
    (hU1 : Subsingleton (Abelian.Ext.{0} (unitRep G) U 1))
    (hU2 : Subsingleton (Abelian.Ext.{0} (unitRep G) U 2)) :
    ∀ n : ℕ, ∀ (N : Rep.{0} Coeff G), Module.Finite ℤ N.V →
      (∀ x : N.V, p • x = 0) → Nat.card N.V = n →
      Subsingleton (Abelian.Ext.{0} N U 2) := by
  intro n
  refine Nat.strong_induction_on n ?_
  intro n ih N hfin hk hcard
  haveI hFin : Finite N.V := finite_of_moduleFinite_ptorsion N.V hfin hk
  by_cases htriv : Nontrivial N.V
  · haveI : Nontrivial N.V := htriv
    obtain ⟨v, hv0, hvfix⟩ := pgroup_invariants_coeff hpG N hk
    have hpv : (p : Coeff) • v = 0 := by
      rw [Nat.cast_smul_eq_nsmul]
      exact hk v
    by_cases hW : Submodule.span Coeff ({v} : Set N.V) = ⊤
    · -- The cyclic case: `N` is generated by the fixed vector `v`, so `0 → K → ℤ → N → 0` is
      -- short exact and `K ≅ ℤ` is `Ext¹`-acyclic.
      have hsurj : Function.Surjective ⇑(Rep.Hom.hom (Work.SSGRoute.powHomRep v hvfix)) := by
        intro x
        have hx : x ∈ Submodule.span Coeff ({v} : Set N.V) := by
          rw [hW]; exact Submodule.mem_top
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx
        exact ⟨c, by rw [Work.SSGRoute.powHomRep_apply, hc]⟩
      have hse := powHomSES_shortExact v hvfix hsurj
      have hpK : ∀ c : Coeff, (p : Coeff) * c ∈ powHomKer v hvfix := by
        intro c
        show (Rep.Hom.hom (Work.SSGRoute.powHomRep v hvfix)) ((p : Coeff) * c) = 0
        rw [Work.SSGRoute.powHomRep_apply, mul_comm, mul_smul, hpv, smul_zero]
      have hKp : ∀ c ∈ powHomKer v hvfix, ∃ d : Coeff, c = (p : Coeff) * d := by
        intro c hc
        have hcz : (p : ℤ) ∣ c.down := dvd_of_smul_eq_zero hv0 hpv hc
        obtain ⟨d, hd⟩ := hcz
        exact ⟨ULift.up d, by
          apply ULift.ext
          show c.down = (p : ℤ) * d
          rw [hd]⟩
      obtain ⟨e⟩ := unitRep_iso_subRep (K := powHomKer v hvfix) (powHomKer_stable v hvfix) hpK hKp
      haveI hX₁ : Subsingleton (Abelian.Ext.{0} (powHomSES v hvfix).X₁ U 1) :=
        (subsingleton_ext_iff_of_iso e 1).mp hU1
      haveI hX₂ : Subsingleton (Abelian.Ext.{0} (powHomSES v hvfix).X₂ U 2) := hU2
      have hzero : ∀ z : Abelian.Ext.{0} N U 2, z = 0 := by
        intro z
        have hx : (Abelian.Ext.mk₀ (powHomSES v hvfix).g).comp z (zero_add 2) = 0 :=
          Subsingleton.elim _ _
        obtain ⟨x₁, hx₁⟩ :=
          Abelian.Ext.contravariant_sequence_exact₃ hse U z hx (n₀ := 1) (by norm_num)
        have h0 : x₁ = 0 := Subsingleton.elim _ _
        rw [h0] at hx₁
        rw [Abelian.Ext.comp_zero] at hx₁
        exact hx₁.symm
      exact ⟨fun x y => by rw [hzero x, hzero y]⟩
    · -- The general case: induct on the subrepresentation `W = ⟨v⟩` and on the quotient `N/W`.
      set W : Submodule Coeff N.V := Submodule.span Coeff ({v} : Set N.V) with hWdef
      have hWle : ∀ g : G, W ≤ Submodule.comap (N.ρ g) W :=
        Work.CohomologicallyTrivial.span_singleton_le_comap_of_fixed N v hvfix
      have hWne : W ≠ ⊥ := by
        intro hbot
        have : v ∈ (⊥ : Submodule Coeff N.V) := by
          rw [← hbot]; exact Submodule.subset_span (Set.mem_singleton v)
        rw [Submodule.mem_bot] at this
        exact hv0 this
      have hWtop : W ≠ ⊤ := by
        rw [hWdef]; exact hW
      haveI hFinW : Finite ↥W := Subtype.finite
      haveI hFinQ : Finite (N.V ⧸ W) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
      haveI hModFinW : Module.Finite ℤ ↥W := Module.Finite.of_finite
      haveI hModFinQ : Module.Finite ℤ (N.V ⧸ W) := Module.Finite.of_finite
      have hlt₁ : Nat.card ↥W < n := by
        rw [← hcard]
        haveI : Fintype ↥W := Fintype.ofFinite _
        haveI : Fintype N.V := Fintype.ofFinite _
        obtain ⟨x, hx⟩ : ∃ x : N.V, x ∉ W := by
          by_contra hc
          push_neg at hc
          exact hWtop (top_unique fun y _ => hc y)
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        exact Fintype.card_subtype_lt hx
      have hlt₂ : Nat.card (N.V ⧸ W) < n := by
        rw [← hcard]
        haveI : Fintype ↥W := Fintype.ofFinite _
        haveI : Nonempty (N.V ⧸ W) := ⟨0⟩
        have hcardq := Submodule.card_eq_card_quotient_mul_card (R := Coeff) W
        have h2 : 1 < Nat.card ↥W := by
          obtain ⟨w, hw⟩ : ∃ w : ↥W, w ≠ 0 := by
            by_contra hc
            push_neg at hc
            refine hWne (le_antisymm (fun y hy => ?_) bot_le)
            rw [Submodule.mem_bot]
            exact congrArg Subtype.val (hc ⟨y, hy⟩)
          have hinj : Function.Injective
              (fun i : Fin 2 => if (i : ℕ) = 0 then (0 : ↥W) else w) := by
            intro i j hij
            fin_cases i <;> fin_cases j <;> simp_all
          have hle : 2 ≤ Nat.card ↥W := by
            have := Nat.card_le_card_of_injective _ hinj
            simpa using this
          omega
        have hmul : Nat.card (N.V ⧸ W) < Nat.card ↥W * Nat.card (N.V ⧸ W) := by
          calc Nat.card (N.V ⧸ W) = Nat.card (N.V ⧸ W) * 1 := (Nat.mul_one _).symm
            _ < Nat.card (N.V ⧸ W) * Nat.card ↥W :=
                  Nat.mul_lt_mul_of_pos_left h2 (Nat.card_pos)
            _ = Nat.card ↥W * Nat.card (N.V ⧸ W) := Nat.mul_comm _ _
        rw [hcardq]
        exact hmul
      have hcard_W : Nat.card (Work.CohomologicallyTrivial.subRep N W hWle).V =
          Nat.card ↥W := rfl
      have hcard_Q : Nat.card (Work.CohomologicallyTrivial.quotRep N W hWle).V =
          Nat.card (N.V ⧸ W) := rfl
      have hsub₁ : Subsingleton (Abelian.Ext.{0}
          (Work.CohomologicallyTrivial.subRep N W hWle) U 2) :=
        ih (Nat.card ↥W) hlt₁ (Work.CohomologicallyTrivial.subRep N W hWle) hModFinW
          (fun x => Subtype.ext (hk x.1)) hcard_W
      have hsub₂ : Subsingleton (Abelian.Ext.{0}
          (Work.CohomologicallyTrivial.quotRep N W hWle) U 2) :=
        ih (Nat.card (N.V ⧸ W)) hlt₂ (Work.CohomologicallyTrivial.quotRep N W hWle) hModFinQ
          (fun x => by
            obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective W x
            have h1 : (p • y : N.V) ∈ W := by rw [hk y]; exact W.zero_mem
            have h2 : W.mkQ (p • y) = 0 := (Submodule.Quotient.mk_eq_zero W).mpr h1
            rwa [map_nsmul] at h2) hcard_Q
      have hS := Work.CohomologicallyTrivial.shortComplexOfStableSubmodule_shortExact N W hWle
      suffices hmain : Subsingleton (Abelian.Ext.{0}
          (Work.CohomologicallyTrivial.shortComplexOfStableSubmodule N W hWle).X₂ U 2) by
        rwa [Work.CohomologicallyTrivial.shortComplexOfStableSubmodule_X₂] at hmain
      haveI hX₁ : Subsingleton (Abelian.Ext.{0}
          (Work.CohomologicallyTrivial.shortComplexOfStableSubmodule N W hWle).X₁ U 2) := by
        rw [Work.CohomologicallyTrivial.shortComplexOfStableSubmodule_X₁]
        exact hsub₁
      haveI hX₃ : Subsingleton (Abelian.Ext.{0}
          (Work.CohomologicallyTrivial.shortComplexOfStableSubmodule N W hWle).X₃ U 2) := by
        rw [Work.CohomologicallyTrivial.shortComplexOfStableSubmodule_X₃]
        exact hsub₂
      have hzero : ∀ z : Abelian.Ext.{0}
          (Work.CohomologicallyTrivial.shortComplexOfStableSubmodule N W hWle).X₂ U 2,
          z = 0 := by
        intro z
        have hx : (Abelian.Ext.mk₀
            (Work.CohomologicallyTrivial.shortComplexOfStableSubmodule N W hWle).f).comp z
            (zero_add 2) = 0 := Subsingleton.elim _ _
        obtain ⟨x₁, hx₁⟩ := Abelian.Ext.contravariant_sequence_exact₂ hS U z hx
        have h0 : x₁ = 0 := Subsingleton.elim _ _
        rw [h0] at hx₁
        rw [Abelian.Ext.comp_zero] at hx₁
        exact hx₁.symm
      exact ⟨fun x y => by rw [hzero x, hzero y]⟩
  · haveI : Subsingleton N.V := ⟨fun x y => by
      by_contra hxy
      exact htriv ⟨⟨x, y, hxy⟩⟩⟩
    exact subsingleton_ext_of_subsingleton_carrier ‹Subsingleton N.V› U 2

/-- For a finite `p`-group `G` and a finitely generated representation `N` killed by `p`, the
second `Ext` group `Ext²_G(N,U)` vanishes as soon as `H¹(G,U) = H²(G,U) = 0` (i.e.
`Ext¹(unitRep G, U)` and `Ext²(unitRep G, U)` are subsingletons).

Proof route (induction on the size of `N`): if `N ≠ 0`, the `p`-group invariants lemma
(`Work.CohomologicallyTrivial.pgroup_invariants_ne_bot_int`, adaptable from `Rep ℤ G` to
`Rep Coeff G`) gives `0 ≠ v` fixed by `G`; the `G`-stable submodule `W = ⟨v⟩ ≅ 𝔽_p` (trivial).
The contravariant long exact sequence of `0 → W → N → N/W → 0`, together with
`Subsingleton (Ext²_G(𝔽_p, U))` (from `SSGRoute.Phi1.coeffSES G p` and the two hypotheses),
propagates `Ext²_G(N/W,U) = 0` to `Ext²_G(N,U) = 0`, and `|N/W| < |N|`. -/
theorem ext2_ptorsion_pgroup_vanish {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Fintype G]
    (hpG : IsPGroup p G) (U N : Rep.{0} SSGRoute.PTExt.Coeff G) [Module.Finite ℤ N.V]
    (hN : ∀ x : N.V, p • x = 0)
    (hU1 : Subsingleton (CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.unitRep G) U 1))
    (hU2 : Subsingleton (CategoryTheory.Abelian.Ext.{0} (SSGRoute.PTExt.unitRep G) U 2)) :
    Subsingleton (CategoryTheory.Abelian.Ext.{0} N U 2) :=
  ext2_aux hpG U hU1 hU2 (Nat.card N.V) N ‹Module.Finite ℤ N.V› hN rfl

end

end Work.SSGRoute.ExtChain
