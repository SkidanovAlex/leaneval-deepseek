import Mathlib
import Submission.Work.SSGRoute.kummerBase_euler_h3_absKummer
import Submission.Work.SSGRoute.range_mapH3_eq_ker_mapH3
import Submission.Work.SSGRoute.H3Map.mapC3c_mem_Z3_mem_B3
import Submission.Work.SSGRoute.sha2_defs
import Submission.Work.SSGRoute.PTembedding.h3_devissage_shortExactSeq
import Submission.Work.SSGRoute.PTembedding.h3_subsingleton_of_finrank_eq_one
import Submission.Work.SSGRoute.PTembedding.h3_subsingleton_of_pgroup_action
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H³(G,M) = 0` for finite `𝔽_ℓ[P]`-modules whose group action factors through a finite `ℓ`-group

Dévissage of the third continuous cohomology along a filtration of the coefficient module with
trivial quotients: if a topological group `G` acts on a finite `𝔽_ℓ`-module `M` through a
homomorphism `φ : G →* P` into a finite `ℓ`-group `P`, and `H³(G, 𝔽_ℓ) = 0` for trivial
coefficients, then `H³(G, M) = 0`.

A nonzero finite `𝔽_ℓ[P]`-module has a nonzero `P`-fixed vector
(`pgroup_fixed_vector_finite`), which splits off a one-dimensional trivial submodule `N`; the
short exact sequence `0 → N → M → M ⧸ N → 0`, together with `H³(G, ↥N) = 0` (the one-dimensional
case, the action being trivial) and `H³(G, M ⧸ N) = 0` (strong induction on the `𝔽_ℓ`-dimension),
gives `H³(G, M) = 0` by exactness at the middle term of the long exact sequence
(`Work.SSGRoute.range_mapH3_eq_ker_mapH3`, packaged as `h3_devissage_shortExactSeq_gen`).

The two dévissage lemmas are stated here universe-polymorphically (the coefficient modules are
arbitrary types), because the requested statement quantifies over `M : Type*`.

This is the `H³`-coefficient reduction needed for the prime-`2` correction in Shafarevich's
theorem on solvable Galois groups, in the form requested by `Work.SSGRoute.PTfin`.
-/

universe u v w

namespace Work.SSGRoute.PTfin

open Work.AbsoluteKummer

open scoped Classical

/-! ## A nonzero fixed vector for a finite `p`-group action -/

/-- **Fixed vectors exist.** A nonzero finite `𝔽_p`-module carrying a linear action of a finite
`p`-group has a nonzero fixed vector.

Indeed `Nat.card M = p ^ finrank M` is a positive power of `p`, `0` is a fixed point, and
`#fixed ≡ Nat.card M ≡ 0 (mod p)`, so the fixed points cannot be just `{0}`
(`IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point`). -/
theorem pgroup_fixed_vector_finite {p : ℕ} [Fact p.Prime] {P M : Type*} [Group P] [Finite P]
    (hP : IsPGroup p P) [AddCommGroup M] [Module (ZMod p) M] [DistribMulAction P M]
    [SMulCommClass P (ZMod p) M] [Finite M] (hM : Nontrivial M) :
    ∃ m : M, m ≠ 0 ∧ ∀ g : P, g • m = m := by
  haveI : Module.Finite (ZMod p) M := Module.Finite.of_finite
  have hcard : Nat.card M = p ^ Module.finrank (ZMod p) M := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := M), Nat.card_zmod]
  have hfr : Module.finrank (ZMod p) M ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hcard
    exact (Finite.one_lt_card_iff_nontrivial.mpr hM).ne' hcard
  have hdvd : p ∣ Nat.card M := by
    rw [hcard]
    exact dvd_pow_self p hfr
  obtain ⟨m, hm, hne⟩ :=
    IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point hP M hdvd (a := (0 : M)) (by simp)
  exact ⟨m, hne.symm, fun g => MulAction.mem_fixedPoints.mp hm g⟩

/-! ## The dévissage lemmas -/

/-- **Dévissage of `H³` along a short exact sequence** (universe-polymorphic form): if both
`H³(Γ,A)` and `H³(Γ,C)` are trivial then so is `H³(Γ,B)`.

By exactness at the middle term of the long exact sequence,
`range H³(ι) = ker H³(π)` (`Work.SSGRoute.range_mapH3_eq_ker_mapH3`).  As `H³(Γ,A) = 0` the range
of `H³(ι)` is trivial and as `H³(Γ,C) = 0` the kernel of `H³(π)` is everything, so `H³(Γ,B)` is
trivial. -/
theorem h3_devissage_shortExactSeq_gen {Γ : Type u} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] {A B C : Type v} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [DistribMulAction Γ A] [DistribMulAction Γ B] [DistribMulAction Γ C]
    (S : Work.AbsoluteKummer.ShortExactSeq Γ A B C)
    (hA : Subsingleton (Work.SSGRoute.H3 (M := A) Γ))
    (hC : Subsingleton (Work.SSGRoute.H3 (M := C) Γ)) :
    Subsingleton (Work.SSGRoute.H3 (M := B) Γ) := by
  refine ⟨fun x y => ?_⟩
  -- `x - y` lies in the kernel of `π_*`, which by exactness is the range of `ι_*`
  have hmem : x - y ∈ (Work.SSGRoute.H3Map.mapH3 S.iota S.iota_equivariant).range := by
    rw [Work.SSGRoute.range_mapH3_eq_ker_mapH3 S, AddMonoidHom.mem_ker]
    have h1 : Work.SSGRoute.H3Map.mapH3 S.pi S.pi_equivariant x
        = Work.SSGRoute.H3Map.mapH3 S.pi S.pi_equivariant y :=
      Subsingleton.elim (h := hC) _ _
    rw [map_sub, h1, sub_self]
  -- the range of `ι_*` is trivial, so `x - y = 0`
  obtain ⟨z, hz⟩ := hmem
  have hz0 : z = 0 := Subsingleton.elim (h := hA) z 0
  rw [hz0, map_zero] at hz
  exact sub_eq_zero.mp hz.symm


/-- **Coefficient reduction to the one-dimensional case** (universe-polymorphic form): if `Γ` acts
trivially on a one-dimensional `𝔽_p`-module `M` — so that `M ≅ 𝔽_p` as a `Γ`-module, the action
being trivial on both sides — then `H³(Γ,M)` is a subsingleton as soon as `H³(Γ,𝔽_p)` is. -/
theorem h3_subsingleton_of_finrank_eq_one_gen {p : ℕ} [Fact p.Prime] {Γ M : Type*} [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] [AddCommGroup M] [Module (ZMod p) M]
    [DistribMulAction Γ M] [Finite M] (htriv : ∀ (g : Γ) (m : M), g • m = m)
    (hdim : Module.finrank (ZMod p) M = 1)
    (h : Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.Triv p) Γ)) :
    Subsingleton (Work.SSGRoute.H3 (M := M) Γ) := by
  -- a one-dimensional `𝔽_p`-module is isomorphic to `𝔽_p`
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one (R := ZMod p) (M := M) hdim
  -- both coefficient isomorphisms are `Γ`-equivariant, the actions being trivial
  have hφ : Work.GroupCohomology.IsEquivariant Γ
      ((e.symm : M →ₗ[ZMod p] ZMod p).toAddMonoidHom) := by
    intro g m
    show e.symm (g • m) = g • e.symm m
    rw [htriv g m]
    rfl
  have hψ : Work.GroupCohomology.IsEquivariant Γ
      ((e : ZMod p →ₗ[ZMod p] M).toAddMonoidHom) := by
    intro g x
    show e (g • x) = g • e x
    rw [htriv g (e x)]
    rfl
  -- `(e⁻¹)_*` is a left inverse of `e_*`, by the computation rule on the classes of cocycles
  have hcomp : ∀ x : Work.SSGRoute.H3 (M := M) Γ,
      Work.SSGRoute.H3Map.mapH3 ((e : ZMod p →ₗ[ZMod p] M).toAddMonoidHom) hψ
        (Work.SSGRoute.H3Map.mapH3 ((e.symm : M →ₗ[ZMod p] ZMod p).toAddMonoidHom) hφ x) = x := by
    intro x
    induction x using Work.SSGRoute.H3Map.H3_induction_on with
    | _ c =>
      rw [Work.SSGRoute.H3Map.mapH3_H3π, Work.SSGRoute.H3Map.mapH3_H3π]
      congr 1
      exact Subtype.ext (funext fun q => by
        rw [Work.SSGRoute.H3Map.mapZ3_apply, Work.SSGRoute.H3Map.mapZ3_apply]
        exact LinearEquiv.apply_symm_apply e (c.1 q))
  refine ⟨fun a b => ?_⟩
  have hab : Work.SSGRoute.H3Map.mapH3 ((e.symm : M →ₗ[ZMod p] ZMod p).toAddMonoidHom) hφ a
      = Work.SSGRoute.H3Map.mapH3 ((e.symm : M →ₗ[ZMod p] ZMod p).toAddMonoidHom) hφ b :=
    h.allEq _ _
  have h1 := congrArg (Work.SSGRoute.H3Map.mapH3 ((e : ZMod p →ₗ[ZMod p] M).toAddMonoidHom) hψ) hab
  rw [hcomp a, hcomp b] at h1
  exact h1


/-! ## The induction on the `𝔽_ℓ`-dimension -/

/-- Strong induction on the `𝔽_ℓ`-dimension of the coefficient module: a finite `𝔽_ℓ`-module on
which `G` acts through `φ : G →* P`, `P` a finite `ℓ`-group, has trivial `H³`. -/
theorem subsingleton_H3_of_isPGroup_action_aux (ℓ : ℕ) [Fact ℓ.Prime]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup ℓ P) (φ : G →* P)
    (htriv : Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.Triv ℓ) G)) :
    ∀ n : ℕ, ∀ (M' : Type*) [AddCommGroup M'] [Module (ZMod ℓ) M']
      [DistribMulAction P M'] [SMulCommClass P (ZMod ℓ) M'] [Finite M'] [DistribMulAction G M'],
      (∀ (g : G) (m : M'), g • m = φ g • m) →
      Module.finrank (ZMod ℓ) M' = n → IsDiscreteModule G M' →
      Subsingleton (Work.SSGRoute.H3 (M := M') G) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
   intro M' instAdd instMod instP instComm instFin instG hcompat hdim hdisc'
   haveI hFinMod : Module.Finite (ZMod ℓ) M' := Module.Finite.of_finite
   haveI hCommG : SMulCommClass G (ZMod ℓ) M' :=
     ⟨fun g c m => by rw [hcompat g (c • m), smul_comm (φ g) c m, hcompat g m]⟩
   by_cases h0 : Module.finrank (ZMod ℓ) M' = 0
   · -- dimension zero: the coefficients form a subsingleton
     have hcard : Nat.card M' = 1 := by
       rw [Module.natCard_eq_pow_finrank (K := ZMod ℓ) (V := M'), Nat.card_zmod, h0, pow_zero]
     haveI hsub : Subsingleton M' := (Nat.card_eq_one_iff_unique.mp hcard).1
     refine ⟨fun x y => ?_⟩
     have hz : ∀ x : Work.SSGRoute.H3 (M := M') G, x = 0 := fun x => by
       refine Work.SSGRoute.H3Map.H3_induction_on (C := fun z => z = 0) x ?_
       intro c
       rw [show c = 0 from Subsingleton.elim c 0, map_zero]
     rw [hz x, hz y]
   · by_cases h1 : Module.finrank (ZMod ℓ) M' = 1
     · -- one-dimensional: `M'` is `𝔽_p` with the trivial action
       haveI : Fintype M' := Fintype.ofFinite M'
       have hcardF : Fintype.card M' = ℓ := by
         rw [Module.card_eq_pow_finrank (K := ZMod ℓ) (V := M'), ZMod.card, h1, pow_one]
       haveI hnt : Nontrivial M' := Fintype.one_lt_card_iff_nontrivial.mp
         (by rw [hcardF]; exact (Fact.out : Nat.Prime ℓ).one_lt)
       obtain ⟨m₀, hm₀, hfixP⟩ := pgroup_fixed_vector_finite (p := ℓ) (P := P) (M := M') hP hnt
       have hspan : (Submodule.span (ZMod ℓ) {m₀} : Submodule (ZMod ℓ) M') = ⊤ := by
         refine Submodule.eq_top_of_finrank_eq ?_
         rw [finrank_span_singleton hm₀, h1]
       have hfixΓ : ∀ g : G, g • m₀ = m₀ := fun g => by rw [hcompat g m₀, hfixP (φ g)]
       have htrivAct : ∀ (g : G) (m : M'), g • m = m := by
         intro g m
         have hm : m ∈ Submodule.span (ZMod ℓ) {m₀} := by
           rw [hspan]; exact Submodule.mem_top
         rw [Submodule.mem_span_singleton] at hm
         obtain ⟨c, rfl⟩ := hm
         rw [smul_comm g c m₀, hfixΓ g]
       exact h3_subsingleton_of_finrank_eq_one_gen htrivAct h1 htriv
     · -- dimension at least two: split off a one-dimensional trivial submodule
       have hn2 : 2 ≤ Module.finrank (ZMod ℓ) M' := by omega
       haveI : Fintype M' := Fintype.ofFinite M'
       have hcardF : Fintype.card M' = ℓ ^ Module.finrank (ZMod ℓ) M' := by
         rw [Module.card_eq_pow_finrank (K := ZMod ℓ) (V := M'), ZMod.card]
       haveI hnt : Nontrivial M' := Fintype.one_lt_card_iff_nontrivial.mp (by
         rw [hcardF]
         exact Nat.one_lt_pow h0 (Fact.out : Nat.Prime ℓ).one_lt)
       obtain ⟨m₀, hm₀, hfixP⟩ := pgroup_fixed_vector_finite (p := ℓ) (P := P) (M := M') hP hnt
       have hfixΓ : ∀ g : G, g • m₀ = m₀ := fun g => by rw [hcompat g m₀, hfixP (φ g)]
       set N : Submodule (ZMod ℓ) M' := Submodule.span (ZMod ℓ) {m₀} with hNdef
       have hNdim : Module.finrank (ZMod ℓ) ↥N = 1 := by
         rw [hNdef]; exact finrank_span_singleton hm₀
       have hNtriv : ∀ (g : G) (x : M'), x ∈ N → g • x = x := by
         intro g x hx
         rw [hNdef, Submodule.mem_span_singleton] at hx
         obtain ⟨c, rfl⟩ := hx
         rw [smul_comm g c m₀, hfixΓ g]
       have hNstab : ∀ (g : G) (x : M'), x ∈ N → g • x ∈ N := fun g x hx => by
         rw [hNtriv g x hx]; exact hx
       have hNPstab : ∀ (g : P) (x : M'), x ∈ N → g • x ∈ N := by
         intro g x hx
         rw [hNdef, Submodule.mem_span_singleton] at hx
         obtain ⟨c, rfl⟩ := hx
         rw [hNdef, Submodule.mem_span_singleton]
         exact ⟨c, by rw [smul_comm g c m₀, hfixP g]⟩
       -- the trivial actions on the one-dimensional submodule
       letI : DistribMulAction G ↥N :=
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
       haveI hNcomm : SMulCommClass P (ZMod ℓ) ↥N := ⟨fun g c x => rfl⟩
       have hNdisc : IsDiscreteModule G ↥N := Work.SSGRoute.PTembedding.isDiscreteModule_of_trivial_smul fun g x => rfl
       -- the induced actions on the quotient
       letI : DistribMulAction G (M' ⧸ N) := Work.SSGRoute.PTembedding.quotientDistribMulAction N hNstab
       letI : DistribMulAction P (M' ⧸ N) := Work.SSGRoute.PTembedding.quotientDistribMulAction N hNPstab
       haveI hQcomm : SMulCommClass P (ZMod ℓ) (M' ⧸ N) := Work.SSGRoute.PTembedding.smulCommClass_quotient N hNPstab
       have hQdisc : IsDiscreteModule G (M' ⧸ N) := Work.SSGRoute.PTembedding.isDiscreteModule_quotient hdisc' N hNstab
       have hQcompat : ∀ (g : G) (q : M' ⧸ N), g • q = φ g • q := by
         intro g q
         induction q using Submodule.Quotient.induction_on N with
         | _ x =>
           rw [Work.SSGRoute.PTembedding.quotientDistribMulAction_apply N hNstab g x,
             Work.SSGRoute.PTembedding.quotientDistribMulAction_apply (G := P) N hNPstab (φ g) x, hcompat g x]
       -- the induction hypothesis for the submodule and for the quotient
       have hIHN : Subsingleton (Work.SSGRoute.H3 (M := ↥N) G) :=
         ih (Module.finrank (ZMod ℓ) ↥N) (by rw [hNdim]; omega) ↥N (fun g x => rfl) rfl hNdisc
       have hIHQ : Subsingleton (Work.SSGRoute.H3 (M := M' ⧸ N) G) :=
         ih (Module.finrank (ZMod ℓ) (M' ⧸ N))
           (by have hq := Submodule.finrank_quotient_add_finrank N; rw [hNdim] at hq; omega)
           (M' ⧸ N) hQcompat rfl hQdisc
       -- the short exact sequence `0 → N → M' → M' ⧸ N → 0`
       have hS : Work.AbsoluteKummer.ShortExactSeq G ↥N M' (M' ⧸ N) :=
         { iota := (Submodule.subtype N).toAddMonoidHom
           pi := (Submodule.mkQ N).toAddMonoidHom
           iota_equivariant := fun g x => (hNtriv g x.1 x.2).symm
           pi_equivariant := fun g x => (Work.SSGRoute.PTembedding.quotientDistribMulAction_apply N hNstab g x).symm
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
       exact h3_devissage_shortExactSeq_gen hS hIHN hIHQ

/-! ## The requested statement -/

theorem subsingleton_H3_of_isPGroup_action (ℓ : ℕ) [Fact ℓ.Prime]
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup ℓ P) (φ : G →* P)
    {M : Type*} [AddCommGroup M] [Module (ZMod ℓ) M] [DistribMulAction P M]
    [SMulCommClass P (ZMod ℓ) M] [Finite M] [DistribMulAction G M]
    (hact : ∀ (g : G) (m : M), g • m = φ g • m)
    (hMdisc : Work.AbsoluteKummer.IsDiscreteModule G M)
    (htriv : Subsingleton (Work.SSGRoute.H3 (M := Work.SSGRoute.Triv ℓ) G)) :
    Subsingleton (Work.SSGRoute.H3 (M := M) G) := by
  exact subsingleton_H3_of_isPGroup_action_aux ℓ hP φ htriv
    (Module.finrank (ZMod ℓ) M) M hact rfl hMdisc

end Work.SSGRoute.PTfin
