import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Localization
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Algebra.OpenSubgroup
import Submission.Work.SSGRoute.PTembedding.h3_devissage_shortExactSeq
import Submission.Work.SSGRoute.PTembedding.h3_subsingleton_of_finrank_eq_one
import Submission.Work.SSGRoute.PTembedding.pgroup_fixed_vector
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H³(Γ,M) = 0` for a finite `𝔽_p[P]`-module `M`, `P` a `p`-group

If `Γ` is a topological group acting on a finite `𝔽_p`-module `M` through a homomorphism
`act : Γ →* P` into a finite `p`-group `P`, then the vanishing of `H³(Γ,𝔽_p)` (with trivial
coefficients) implies the vanishing of `H³(Γ,M)`.  This is the dévissage of the third continuous
cohomology along a filtration of the coefficient module with trivial quotients, whose existence is
the classical fact that a nonzero module over a finite `p`-group has a nonzero fixed vector.

The proof is a strong induction on the `𝔽_p`-dimension of the coefficient module.  The induction
step uses a nonzero fixed vector `m₀` of `P` to split off the one-dimensional trivial submodule
`N = span{m₀}`: the short exact sequence `0 → N → M → M/N → 0` of `Γ`-modules, together with
exactness of the long exact sequence at `H³(Γ,M)`, gives the vanishing for `M` from that for `N`
and for `M ⧸ N`, both of strictly smaller dimension.  The one-dimensional case is handled
separately: there `M` actually carries the trivial action and is isomorphic to `𝔽_p`.
-/

open Work.AbsoluteKummer

namespace Work.SSGRoute.PTembedding

/-! ## The induced action on a quotient by a stable submodule -/

section QuotientAction

variable {G R M : Type*} [Group G] [Ring R] [AddCommGroup M] [Module R M]
  [DistribMulAction G M] [SMulCommClass G R M]

/-- The function underlying the induced `G`-action on `M ⧸ N`, for a `G`-stable submodule `N`:
it is defined on representatives by `x ↦ g • x`. -/
noncomputable def quotientSMulFun (N : Submodule R M)
    (hN : ∀ (g : G) (x : M), x ∈ N → g • x ∈ N) (g : G) : M ⧸ N → M ⧸ N :=
  Quotient.map' (fun x => g • x) fun a b hab => by
    rw [Submodule.quotientRel_def] at hab ⊢
    rw [← smul_sub]
    exact hN g (a - b) hab

/-- The computation rule of `quotientSMulFun` on representatives. -/
theorem quotientSMulFun_mk (N : Submodule R M)
    (hN : ∀ (g : G) (x : M), x ∈ N → g • x ∈ N) (g : G) (x : M) :
    quotientSMulFun N hN g (Submodule.Quotient.mk x : M ⧸ N) = Submodule.Quotient.mk (g • x) := by
  rw [← Submodule.Quotient.mk''_eq_mk x, ← Submodule.Quotient.mk''_eq_mk (g • x)]
  exact Quotient.map'_mk'' (fun x => g • x) _ x

/-- The `SMul` structure on the quotient induced by a stable submodule. -/
@[instance_reducible]
noncomputable def quotientSMul (N : Submodule R M)
    (hN : ∀ (g : G) (x : M), x ∈ N → g • x ∈ N) : SMul G (M ⧸ N) where
  smul := quotientSMulFun N hN

/-- The computation rule of the induced `SMul`. -/
theorem quotientSMul_apply (N : Submodule R M)
    (hN : ∀ (g : G) (x : M), x ∈ N → g • x ∈ N) (g : G) (x : M) :
    @SMul.smul G (M ⧸ N) (quotientSMul N hN) g (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (g • x) :=
  quotientSMulFun_mk N hN g x

/-- The `DistribMulAction` on the quotient induced by a stable submodule. -/
@[instance_reducible]
noncomputable def quotientDistribMulAction (N : Submodule R M)
    (hN : ∀ (g : G) (x : M), x ∈ N → g • x ∈ N) : DistribMulAction G (M ⧸ N) :=
  letI : SMul G (M ⧸ N) := quotientSMul N hN
  Function.Surjective.distribMulAction (Submodule.mkQ N).toAddMonoidHom
    (Submodule.Quotient.mk_surjective N) fun g x => (quotientSMul_apply N hN g x).symm

/-- The computation rule of the induced `DistribMulAction`. -/
theorem quotientDistribMulAction_apply (N : Submodule R M)
    (hN : ∀ (g : G) (x : M), x ∈ N → g • x ∈ N) (g : G) (x : M) :
    letI : DistribMulAction G (M ⧸ N) := quotientDistribMulAction N hN
    g • (Submodule.Quotient.mk x : M ⧸ N) = Submodule.Quotient.mk (g • x) := by
  letI : DistribMulAction G (M ⧸ N) := quotientDistribMulAction N hN
  exact quotientSMul_apply N hN g x

/-- The two scalar actions on the quotient commute. -/
theorem smulCommClass_quotient (N : Submodule R M)
    (hN : ∀ (g : G) (x : M), x ∈ N → g • x ∈ N) :
    letI : DistribMulAction G (M ⧸ N) := quotientDistribMulAction N hN
    SMulCommClass G R (M ⧸ N) := by
  letI : DistribMulAction G (M ⧸ N) := quotientDistribMulAction N hN
  refine ⟨fun g r q => ?_⟩
  induction q using Submodule.Quotient.induction_on N with
  | _ x =>
    rw [← Submodule.Quotient.mk_smul (p := N) (r := r) (x := x),
      quotientDistribMulAction_apply N hN g (r • x), smul_comm g r x,
      quotientDistribMulAction_apply N hN g x, Submodule.Quotient.mk_smul]

section Discrete

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Discreteness descends to quotients. -/
theorem isDiscreteModule_quotient (hM : IsDiscreteModule G M) (N : Submodule R M)
    (hN : ∀ (g : G) (x : M), x ∈ N → g • x ∈ N) :
    letI : DistribMulAction G (M ⧸ N) := quotientDistribMulAction N hN
    IsDiscreteModule G (M ⧸ N) := by
  letI : DistribMulAction G (M ⧸ N) := quotientDistribMulAction N hN
  intro q
  induction q using Submodule.Quotient.induction_on N with
  | _ x =>
    refine Subgroup.isOpen_mono ?_ (hM x)
    intro g hg
    rw [MulAction.mem_stabilizer_iff] at hg ⊢
    rw [quotientDistribMulAction_apply N hN g x, hg]

end Discrete

end QuotientAction

/-! ## Modules with a trivial action are discrete -/

/-- A module with a trivial action is a discrete module (all stabilisers are `⊤`). -/
theorem isDiscreteModule_of_trivial_smul {G M : Type*} [Group G] [TopologicalSpace G]
    [AddCommGroup M] [DistribMulAction G M]
    (h : ∀ (g : G) (m : M), g • m = m) : IsDiscreteModule G M := by
  intro m
  have hstab : MulAction.stabilizer G m = ⊤ := by
    ext g
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_top, iff_true]
    exact h g m
  rw [hstab]
  exact isOpen_univ

/-! ## The main induction -/

open scoped Classical

theorem h3_subsingleton_of_pgroup_action (p : ℕ) [Fact p.Prime] {Γ P M : Type} [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [Group P] [Finite P]
    (hP : IsPGroup p P) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction P M]
    [SMulCommClass P (ZMod p) M] [Finite M] (act : Γ →* P) :
    letI : DistribMulAction Γ M := DistribMulAction.compHom M act
    Work.AbsoluteKummer.IsDiscreteModule Γ M →
    Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.Triv p) Γ) →
      Subsingleton (Work.SSGRoute.H3 (M := M) Γ) := by
  letI : DistribMulAction Γ M := DistribMulAction.compHom M act
  intro hdisc hT
  have main : ∀ n : ℕ, ∀ (M' : Type) [AddCommGroup M'] [Module (ZMod p) M']
      [DistribMulAction P M'] [SMulCommClass P (ZMod p) M'] [Finite M'] [DistribMulAction Γ M'],
      (∀ (g : Γ) (m : M'), g • m = act g • m) →
      Module.finrank (ZMod p) M' = n → IsDiscreteModule Γ M' →
      Subsingleton (Work.SSGRoute.H3 (M := M') Γ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
     intro M' instAdd instMod instP instComm instFin instG hcompat hdim hdisc'
     haveI hFinMod : Module.Finite (ZMod p) M' := Module.Finite.of_finite
     haveI hCommG : SMulCommClass Γ (ZMod p) M' :=
       ⟨fun g c m => by rw [hcompat g (c • m), smul_comm (act g) c m, hcompat g m]⟩
     by_cases h0 : Module.finrank (ZMod p) M' = 0
     · -- dimension zero: the coefficients form a subsingleton
       have hcard : Nat.card M' = 1 := by
         rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := M'), Nat.card_zmod, h0, pow_zero]
       haveI hsub : Subsingleton M' := (Nat.card_eq_one_iff_unique.mp hcard).1
       refine ⟨fun x y => ?_⟩
       have hz : ∀ x : Work.SSGRoute.H3 (M := M') Γ, x = 0 := fun x => by
         refine Work.SSGRoute.H3Map.H3_induction_on (C := fun z => z = 0) x ?_
         intro c
         rw [show c = 0 from Subsingleton.elim c 0, map_zero]
       rw [hz x, hz y]
     · by_cases h1 : Module.finrank (ZMod p) M' = 1
       · -- one-dimensional: `M'` is `𝔽_p` with the trivial action
         haveI : Fintype M' := Fintype.ofFinite M'
         have hcardF : Fintype.card M' = p := by
           rw [Module.card_eq_pow_finrank (K := ZMod p) (V := M'), ZMod.card, h1, pow_one]
         haveI hnt : Nontrivial M' := Fintype.one_lt_card_iff_nontrivial.mp
           (by rw [hcardF]; exact (Fact.out : Nat.Prime p).one_lt)
         obtain ⟨m₀, hm₀, hfixP⟩ := pgroup_fixed_vector (p := p) (P := P) (M := M') hP hnt
         have hspan : (Submodule.span (ZMod p) {m₀} : Submodule (ZMod p) M') = ⊤ := by
           refine Submodule.eq_top_of_finrank_eq ?_
           rw [finrank_span_singleton hm₀, h1]
         have hfixΓ : ∀ g : Γ, g • m₀ = m₀ := fun g => by rw [hcompat g m₀, hfixP (act g)]
         have htriv : ∀ (g : Γ) (m : M'), g • m = m := by
           intro g m
           have hm : m ∈ Submodule.span (ZMod p) {m₀} := by
             rw [hspan]; exact Submodule.mem_top
           rw [Submodule.mem_span_singleton] at hm
           obtain ⟨c, rfl⟩ := hm
           rw [smul_comm g c m₀, hfixΓ g]
         exact h3_subsingleton_of_finrank_eq_one htriv h1 hT
       · -- dimension at least two: split off a one-dimensional trivial submodule
         have hn2 : 2 ≤ Module.finrank (ZMod p) M' := by omega
         haveI : Fintype M' := Fintype.ofFinite M'
         have hcardF : Fintype.card M' = p ^ Module.finrank (ZMod p) M' := by
           rw [Module.card_eq_pow_finrank (K := ZMod p) (V := M'), ZMod.card]
         haveI hnt : Nontrivial M' := Fintype.one_lt_card_iff_nontrivial.mp (by
           rw [hcardF]
           exact Nat.one_lt_pow h0 (Fact.out : Nat.Prime p).one_lt)
         obtain ⟨m₀, hm₀, hfixP⟩ := pgroup_fixed_vector (p := p) (P := P) (M := M') hP hnt
         have hfixΓ : ∀ g : Γ, g • m₀ = m₀ := fun g => by rw [hcompat g m₀, hfixP (act g)]
         set N : Submodule (ZMod p) M' := Submodule.span (ZMod p) {m₀} with hNdef
         have hNdim : Module.finrank (ZMod p) ↥N = 1 := by
           rw [hNdef]; exact finrank_span_singleton hm₀
         have hNtriv : ∀ (g : Γ) (x : M'), x ∈ N → g • x = x := by
           intro g x hx
           rw [hNdef, Submodule.mem_span_singleton] at hx
           obtain ⟨c, rfl⟩ := hx
           rw [smul_comm g c m₀, hfixΓ g]
         have hNstab : ∀ (g : Γ) (x : M'), x ∈ N → g • x ∈ N := fun g x hx => by
           rw [hNtriv g x hx]; exact hx
         have hNPstab : ∀ (g : P) (x : M'), x ∈ N → g • x ∈ N := by
           intro g x hx
           rw [hNdef, Submodule.mem_span_singleton] at hx
           obtain ⟨c, rfl⟩ := hx
           rw [hNdef, Submodule.mem_span_singleton]
           exact ⟨c, by rw [smul_comm g c m₀, hfixP g]⟩
         -- the trivial actions on the one-dimensional submodule
         letI : DistribMulAction Γ ↥N :=
           { smul := fun _ x => x
             one_smul := fun _ => rfl
             mul_smul := fun _ _ _ => rfl
             smul_zero := fun _ => rfl
             smul_add := fun _ _ _ => rfl }
         letI : DistribMulAction P ↥N :=
           { smul := fun _ x => x
             one_smul := fun _ => rfl
             mul_smul := fun _ _ _ => rfl
             smul_zero := fun _ => rfl
             smul_add := fun _ _ _ => rfl }
         haveI hNcomm : SMulCommClass P (ZMod p) ↥N := ⟨fun g c x => rfl⟩
         have hNdisc : IsDiscreteModule Γ ↥N := isDiscreteModule_of_trivial_smul fun g x => rfl
         -- the induced actions on the quotient
         letI : DistribMulAction Γ (M' ⧸ N) := quotientDistribMulAction N hNstab
         letI : DistribMulAction P (M' ⧸ N) := quotientDistribMulAction N hNPstab
         haveI hQcomm : SMulCommClass P (ZMod p) (M' ⧸ N) := smulCommClass_quotient N hNPstab
         have hQdisc : IsDiscreteModule Γ (M' ⧸ N) := isDiscreteModule_quotient hdisc' N hNstab
         have hQcompat : ∀ (g : Γ) (q : M' ⧸ N), g • q = act g • q := by
           intro g q
           induction q using Submodule.Quotient.induction_on N with
           | _ x =>
             rw [quotientDistribMulAction_apply N hNstab g x,
               quotientDistribMulAction_apply (G := P) N hNPstab (act g) x, hcompat g x]
         -- the induction hypothesis for the submodule and for the quotient
         have hIHN : Subsingleton (Work.SSGRoute.H3 (M := ↥N) Γ) :=
           ih (Module.finrank (ZMod p) ↥N) (by rw [hNdim]; omega) ↥N (fun g x => rfl) rfl hNdisc
         have hIHQ : Subsingleton (Work.SSGRoute.H3 (M := M' ⧸ N) Γ) :=
           ih (Module.finrank (ZMod p) (M' ⧸ N))
             (by have hq := Submodule.finrank_quotient_add_finrank N; rw [hNdim] at hq; omega)
             (M' ⧸ N) hQcompat rfl hQdisc
         -- the short exact sequence `0 → N → M' → M' ⧸ N → 0`
         have hS : Work.AbsoluteKummer.ShortExactSeq Γ ↥N M' (M' ⧸ N) :=
           { iota := (Submodule.subtype N).toAddMonoidHom
             pi := (Submodule.mkQ N).toAddMonoidHom
             iota_equivariant := fun g x => (hNtriv g x.1 x.2).symm
             pi_equivariant := fun g x => (quotientDistribMulAction_apply N hNstab g x).symm
             iota_injective := fun x y h => Subtype.ext h
             pi_surjective := fun q => by
               obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
               exact ⟨x, rfl⟩
             range_iota_eq_ker_pi := by
               ext x
               constructor
               · intro hx
                 rw [AddMonoidHom.mem_range] at hx
                 obtain ⟨y, rfl⟩ := hx
                 rw [AddMonoidHom.mem_ker]
                 exact (Submodule.Quotient.mk_eq_zero N).mpr y.2
               · intro hx
                 rw [AddMonoidHom.mem_ker] at hx
                 rw [AddMonoidHom.mem_range]
                 exact ⟨⟨x, (Submodule.Quotient.mk_eq_zero N).mp hx⟩, rfl⟩
             isDiscreteM := hNdisc
             isDiscreteN := hdisc'
             isDiscreteP := hQdisc }
         exact h3_devissage_shortExactSeq hS hIHN hIHQ
  exact main (Module.finrank (ZMod p) M) M (fun g m => rfl) rfl hdisc

end Work.SSGRoute.PTembedding
