import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
import Submission.Work.SSGRoute.CFTSide.cyclicNormCriterion_classesK
import Submission.Work.SSGRoute.powHomRepDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory
open SSGRoute.PTExt

noncomputable section

/- `ULift.module` and friends compete with the module structure stored in a representation; prefer
the structure instances, as in `powHomRepDefs.lean`. -/
attribute [local instance 10000] Rep.hV2 Rep.hV1
attribute [local instance 1] ULift.module ULift.smulLeft ULift.mulAction ULift.smulZeroClass
attribute [local instance 1] ULift.distribSMul ULift.distribMulAction ULift.smulWithZero
attribute [local instance 1] ULift.mulActionWithZero

/-! ## The "kills norms" half, for an arbitrary representation -/

/-- **The factorisation of `powHomRep a` through the regular representation when `a` is a norm.**

For `a = N b` (with `N` the norm endomorphism of `A`), the coefficient map `1 ↦ a` factors as
`Coeff --(trace)--> Coeff[G] --(σ ↦ σ • b)--> A`. This is the arbitrary-representation port of
`Work.SSGRoute.CFTSide.powHomCls_eq_traceHomC_comp`. -/
lemma powHomRep_eq_traceHomC_comp {G : Type} [Group G] [Fintype G]
    (A : Rep SSGRoute.PTExt.Coeff G) (a : A)
    (hafix : ∀ σ : G, A.ρ σ a = a) (b : A) (hb : A.norm.hom b = a) :
    powHomRep a hafix = CFTSide.traceHomC G ≫ Rep.leftRegularHom A b := by
  apply Rep.hom_ext
  rw [Representation.IntertwiningMap.ext_iff]
  apply LinearMap.ext
  intro n
  show n • a = (Rep.leftRegularHom A b).hom.toLinearMap (n • CFTSide.leftRegularTraceC G)
  have hsum : (Rep.leftRegularHom A b).hom.toLinearMap (CFTSide.leftRegularTraceC G)
      = ∑ σ : G, A.ρ σ b := by
    rw [CFTSide.leftRegularTraceC, map_sum]
    exact Finset.sum_congr rfl (fun σ _ =>
      (Rep.leftRegularHom_hom_single (A := A) σ b (1 : Coeff)).trans (one_smul _ _))
  rw [map_smul]
  congr 1
  rw [← hb, CFTSide.norm_apply_eq_sum_coeff, hsum]

/-- **The "kills norms" half of the cyclic norm criterion for an arbitrary representation.**

For a finite group `G`, a `Coeff`-linear representation `A`, an element `a : A` which is a norm
(i.e. lies in the image of the norm endomorphism of `A`) and any class
`h ∈ H¹(G, 𝔽_p)`, the cup product class `map (powHomRep a) 2 (δ h)` vanishes: `powHomRep a`
factors through the left regular representation `Coeff[G]`, which is acyclic in positive degrees
(Shapiro/coinduction acyclicity).  Port of
`Work.SSGRoute.CFTSide.cyclicNormCriterion_kills_norms`. -/
theorem cyclicNormCriterion_rep_kills_norms {G : Type} [Group G] [Fintype G] (p : ℕ) [Fact p.Prime]
    (A : Rep SSGRoute.PTExt.Coeff G) (a : A) (hafix : ∀ σ : G, A.ρ σ a = a)
    (hnorm : a ∈ Set.range (Rep.Hom.hom A.norm))
    (h : groupCohomology (Rep.trivial SSGRoute.PTExt.Coeff G (ZMod p)) 1) :
    (groupCohomology.map (MonoidHom.id G) (powHomRep a hafix) 2
        ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact G p) 1 2 rfl).hom h)) = 0 := by
  classical
  obtain ⟨b, hb⟩ := hnorm
  have hfac := powHomRep_eq_traceHomC_comp A a hafix b hb
  haveI : Subsingleton (groupCohomology (Rep.leftRegular SSGRoute.PTExt.Coeff G) 2) :=
    CFTSide.subsingleton_groupCohomology_leftRegular_commRing SSGRoute.PTExt.Coeff G 1
  have h0 : (groupCohomology.map (MonoidHom.id G) (CFTSide.traceHomC G) 2)
      ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact G p) 1 2 rfl).hom h) = 0 :=
    Subsingleton.elim _ _
  have hcomp := groupCohomology.map_id_comp (CFTSide.traceHomC G) (Rep.leftRegularHom A b) 2
  set_option backward.isDefEq.respectTransparency false in
  rw [hfac, hcomp]
  change (ConcreteCategory.hom
        (groupCohomology.map (MonoidHom.id G) (Rep.leftRegularHom A b) 2))
      ((ConcreteCategory.hom
        (groupCohomology.map (MonoidHom.id G) (CFTSide.traceHomC G) 2))
        ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact G p) 1 2 rfl).hom h)) = 0
  rw [h0]
  exact map_zero _

/-! ## The transgression half, for an arbitrary representation -/

/-- **The transgression half of the cyclic norm criterion for an arbitrary representation.**

For a finite cyclic group `G` of prime order `p`, a `Coeff`-linear `G`-representation `A`, a
`G`-fixed element `a : A` and a nonzero class `h ∈ H¹(G, 𝔽_p)`: if `map (powHomRep a) 2 (δ h)`
vanishes, then `a` is a norm.  Port of
`Work.SSGRoute.CFTSide.cyclicNormCriterion_transgression`. -/
theorem cyclicNormCriterion_rep_transgression {G : Type} [Group G] [Fintype G] (p : ℕ)
    [Fact p.Prime] (hcyc : IsCyclic G) (hcard : Nat.card G = p)
    (A : Rep SSGRoute.PTExt.Coeff G) (a : A) (hafix : ∀ σ : G, A.ρ σ a = a)
    (h : groupCohomology (Rep.trivial SSGRoute.PTExt.Coeff G (ZMod p)) 1) (hne : h ≠ 0)
    (hvan : (groupCohomology.map (MonoidHom.id G) (powHomRep a hafix) 2
        ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact G p) 1 2 rfl).hom h)) = 0) :
    a ∈ Set.range (Rep.Hom.hom A.norm) := by
  classical
  haveI : IsCyclic G := hcyc
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := G)
  have hcard' : Fintype.card G = p := by rw [← Nat.card_eq_fintype_card, hcard]
  -- the character and its integral lift
  obtain ⟨f, Y, hfne, hfg₀, hY, hhπ⟩ :=
    CFTSide.exists_lift_and_hom_of_ne_zero G p g₀ hg₀ h hne
  -- the carry cocycle and its transgression
  obtain ⟨Z, hZ, hZsum, -, ⟨j, l, hjl⟩⟩ :=
    CFTSide.transgression_carry G p g₀ hg₀ hcard' f hfne Y hY
  have hX : (⇑(Rep.Hom.hom (SSGRoute.Phi1.coeffSES G p).f)) ∘
        (fun q : G × G => (ULift.up (Z q) : Coeff))
      = ⇑(groupCohomology.d₁₂ (Rep.trivial Coeff G Coeff))
          (fun g : G => (ULift.up (Y g) : Coeff)) :=
    CFTSide.carryCocycle_compat G p Y Z hZ
  have hzc_mem : (fun q : G × G => (ULift.up (Z q) : Coeff))
      ∈ groupCohomology.cocycles₂ (Rep.trivial Coeff G Coeff) :=
    groupCohomology.mem_cocycles₂_of_comp_eq_d₁₂
      (SSGRoute.Phi1.coeffSES_shortExact G p) hX
  set zc : groupCohomology.cocycles₂ (Rep.trivial Coeff G Coeff) :=
    ⟨fun q : G × G => (ULift.up (Z q) : Coeff), hzc_mem⟩ with hzc
  -- `δ h` is the class of the carry cocycle
  have hδ : (groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact G p) 1 2 rfl).hom h
      = groupCohomology.H2π (Rep.trivial Coeff G Coeff) zc :=
    CFTSide.coeffSES_delta_eq_H2π_carry G p f Y hY Z h hhπ hX
  -- the vanishing hypothesis, rewritten
  have hvan1 : groupCohomology.map (MonoidHom.id G) (powHomRep a hafix) 2
        (groupCohomology.H2π (Rep.trivial Coeff G Coeff) zc) = 0 := by
    rw [← hδ]
    exact hvan
  -- naturality of `H2π`
  have hnat : (groupCohomology.map (MonoidHom.id G) (powHomRep a hafix) 2)
        (groupCohomology.H2π (Rep.trivial Coeff G Coeff) zc)
      = groupCohomology.H2π A
          (groupCohomology.mapCocycles₂ (MonoidHom.id G) (powHomRep a hafix) zc) :=
    congrArg (fun m => m zc)
      (groupCohomology.H2π_comp_map (A := Rep.trivial Coeff G Coeff) (B := A)
        (MonoidHom.id G) (powHomRep a hafix))
  rw [hnat, groupCohomology.H2π_eq_zero_iff, groupCohomology.coboundaries₂] at hvan1
  obtain ⟨e, he⟩ := hvan1
  -- the transported cocycle is `q ↦ (Z q) • a`
  have hxa : ∀ q : G × G,
      (groupCohomology.mapCocycles₂ (MonoidHom.id G) (powHomRep a hafix) zc) q
        = (Z q) • a := by
    intro q
    show (Rep.Hom.hom (powHomRep a hafix)) (zc q) = (Z q) • a
    rw [powHomRep_apply, hzc]
    show (ULift.up (Z q) : Coeff) • a = (Z q) • a
    exact Int.cast_smul_eq_zsmul Coeff (Z q) a
  have he' : (groupCohomology.d₁₂ A).hom e = fun q : G × G => (Z q) • a :=
    he.trans (funext hxa)
  -- the transgression of the vanishing class is a norm
  have hsum2 : (∑ t ∈ Finset.range p,
        ((fun q : G × G => (Z q) • a) (g₀ ^ t, g₀)))
      = A.norm.hom (e g₀) := by
    rw [← CFTSide.sum_range_d12_eq_norm p hcard' g₀ hg₀ A e]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    exact (congrFun he' (g₀ ^ t, g₀)).symm
  have hTz_a : (∑ t ∈ Finset.range p, Z (g₀ ^ t, g₀)) • a = A.norm.hom (e g₀) := by
    rw [← hsum2, Finset.sum_smul]
  have hYa : (Y g₀) • a ∈ Set.range (Rep.Hom.hom A.norm) := by
    rw [← hZsum]
    exact ⟨e g₀, hTz_a.symm⟩
  -- `p • a` is a norm too
  have hpa : ((p : ℤ)) • a = A.norm.hom a := by
    rw [CFTSide.norm_apply_eq_sum]
    rw [Finset.sum_congr rfl (fun σ _ => hafix σ), Finset.sum_const, Finset.card_univ, hcard',
      Nat.cast_smul_eq_nsmul ℤ p a]
  have hpa' : ((p : ℤ)) • a ∈ Set.range (Rep.Hom.hom A.norm) := by
    rw [hpa]
    exact ⟨a, rfl⟩
  -- Bézout
  obtain ⟨w₁, hw₁⟩ := hYa
  obtain ⟨w₂, hw₂⟩ := hpa'
  refine ⟨j • w₁ + l • w₂, ?_⟩
  rw [map_add, map_zsmul, map_zsmul, hw₁, hw₂]
  rw [smul_smul, smul_smul, ← add_zsmul]
  rw [show j * (Y g₀) + l * (p : ℤ) = 1 from hjl, one_zsmul]

/-- **The cyclic norm criterion for an arbitrary `Coeff`-representation of a cyclic group of
prime order.**  For a finite cyclic group `G` of order `p`, a `Coeff`-linear `G`-representation `A`,
a `G`-fixed element `a : A` and a nonzero character `h ∈ H¹(G, 𝔽_p)`, the cup-product class
`groupCohomology.map (id) (powHom a) 2 (δ h)` (with `δ` the Bockstein, the connecting map of the
coefficient sequence `0 → ℤ --p--> ℤ → 𝔽_p → 0`) vanishes if and only if `a` is a norm, i.e. lies
in the image of the norm endomorphism of `A`.

This is the port of `Work.SSGRoute.CFTSide.cyclicNormCriterion_classesK` (the case
`A = classesK k L`, `G = Gal(L/k)`) to an arbitrary representation; its two halves are the ports of
`CFTSide.cyclicNormCriterion_kills_norms` (`powHomCls_eq_traceHomC_comp` + Shapiro acyclicity of the
left regular representation) and `CFTSide.cyclicNormCriterion_transgression` (the carry cocycle). -/
theorem cyclicNormCriterion_rep {G : Type} [Group G] [Fintype G] (p : ℕ) [Fact p.Prime]
    (hcyc : IsCyclic G) (hcard : Nat.card G = p) (A : Rep SSGRoute.PTExt.Coeff G)
    (a : A) (hafix : ∀ σ : G, A.ρ σ a = a)
    (h : groupCohomology (Rep.trivial SSGRoute.PTExt.Coeff G (ZMod p)) 1) (hne : h ≠ 0) :
    (groupCohomology.map (MonoidHom.id G) (Work.SSGRoute.powHomRep a hafix) 2
        ((groupCohomology.δ (SSGRoute.Phi1.coeffSES_shortExact G p) 1 2 rfl).hom h) = 0) ↔
      a ∈ Set.range (Rep.Hom.hom A.norm) :=
  ⟨fun hvan => cyclicNormCriterion_rep_transgression p hcyc hcard A a hafix h hne hvan,
   fun hnorm => cyclicNormCriterion_rep_kills_norms p A a hafix hnorm h⟩

end

end Work.SSGRoute
