import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Submission.Work.SSGRoute.eCoh_map
import Submission.Work.SSGRoute.exists_H1_inflated_ne_zero
import Submission.Work.SSGRoute.groupCohomology_levelInf_nat
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **Every nonzero class of `H¹(G, 𝔽_p)` with trivial coefficients is inflated from a cyclic quotient of order `p`.**

For a finite group `G`, a prime `p` and `h ≠ 0` in `H¹(G, 𝔽_p)` (trivial action, coefficients in
`ZMod p`), there is a normal subgroup `N ⊴ G` with `G ⧸ N` cyclic of order `p` and
`h = infl(h̄)` for some `h̄ ∈ H¹(G ⧸ N, 𝔽_p)`.

Maths: `H¹(G, 𝔽_p) = Hom(G, 𝔽_p)`; a nonzero homomorphism `z : G → 𝔽_p` has image `𝔽_p`
(prime order), so `N := ker z` has `G ⧸ N ≅ ℤ/p`, and `z` factors through `G ⧸ N`.

Toolkit (all available; used sorry-free in `Submission/Work/SSGRoute/PT/e3_character_inflation.lean`
and `Submission/Work/SSGRoute/exists_H1_inflated_ne_zero.lean`):
`groupCohomology.H1_induction_on`, `groupCohomology.H1π`, `groupCohomology.H1π_eq_zero_iff`,
`groupCohomology.coboundaries₁_eq_bot_of_isTrivial`, `groupCohomology.cocycles₁_ext`,
`groupCohomology.mapCocycles₁`, `groupCohomology.H1π_comp_map_apply`,
`groupCohomology.coe_mapCocycles₁`. -/
theorem cyclic_quotient_of_H1_ne_zero
    (p : ℕ) [Fact p.Prime] {G : Type} [Group G] [Fintype G]
    (h : groupCohomology (Rep.trivial SSGRoute.PTExt.Coeff G (ZMod p)) 1) (hne : h ≠ 0) :
    ∃ (N : Subgroup G) (_ : N.Normal) (_ : Fintype (G ⧸ N)),
      IsCyclic (G ⧸ N) ∧ Nat.card (G ⧸ N) = p ∧
      ∃ hb : groupCohomology (Rep.trivial SSGRoute.PTExt.Coeff (G ⧸ N) (ZMod p)) 1,
        (groupCohomology.map (QuotientGroup.mk' N)
          (SSGRoute.PTExt.trivResInv (QuotientGroup.mk' N) (ZMod p)) 1).hom hb = h := by
  classical
  -- Reduce to a nonzero cocycle; since the coefficients are trivial, `B¹ = 0`.
  revert hne
  refine groupCohomology.H1_induction_on h ?_
  intro z hne
  have hz0 : z ≠ 0 := fun h0 => hne (by rw [h0, map_zero])
  -- The additive character of `G` attached to the cocycle `z` (trivial coefficients).
  let φ : Additive G →+ ZMod p :=
    { toFun := fun x => z x.toMul
      map_zero' := by simpa using (groupCohomology.cocycles₁_map_one z)
      map_add' := fun x y => by
        simpa using (groupCohomology.cocycles₁_map_mul_of_isTrivial z x.toMul y.toMul) }
  have hφ_ne : φ ≠ 0 := by
    intro h0
    refine hz0 (groupCohomology.cocycles₁_ext fun g => ?_)
    have h1 : φ (Additive.ofMul g) = 0 := by rw [h0]; rfl
    exact h1
  -- Its range is a nonzero additive subgroup of the prime field, hence everything.
  have hφ_surj : Function.Surjective φ := by
    rw [← AddMonoidHom.range_eq_top]
    rcases (show φ.range.Normal from inferInstance).eq_bot_or_eq_top with hbot | htop
    · exfalso
      refine hφ_ne (AddMonoidHom.ext fun x => ?_)
      have hmem : φ x ∈ φ.range := ⟨x, rfl⟩
      rw [hbot] at hmem
      simpa using hmem
    · exact htop
  -- The associated character of `G` in the multiplicative group of the prime field.
  let ψ : G →* Multiplicative (ZMod p) := AddMonoidHom.toMultiplicativeRight φ
  have hψ_apply : ∀ g : G, ψ g = Multiplicative.ofAdd (z g) := fun g => rfl
  have hψ_surj : Function.Surjective ψ := by
    intro y
    obtain ⟨x, hx⟩ := hφ_surj y.toAdd
    refine ⟨x.toMul, ?_⟩
    rw [hψ_apply]
    have hx' : z x.toMul = y.toAdd := hx
    rw [hx']
    exact ofAdd_toAdd y
  -- The kernel of `ψ` has cyclic quotient of order `p`, and `z` factors through it.
  let N : Subgroup G := ψ.ker
  have hN : N.Normal := ψ.normal_ker
  haveI : N.Normal := hN
  let e : G ⧸ N ≃* Multiplicative (ZMod p) :=
    QuotientGroup.quotientKerEquivOfSurjective ψ hψ_surj
  -- The cocycle on the quotient induced by `z`.
  let zbAdd : Additive (G ⧸ N) →+ ZMod p :=
    { toFun := fun X => ((QuotientGroup.kerLift ψ) X.toMul).toAdd
      map_zero' := by simp
      map_add' := fun X Y => by simp }
  let zb : groupCohomology.cocycles₁
      (Rep.trivial SSGRoute.PTExt.Coeff (G ⧸ N) (ZMod p)) :=
    ⟨⇑zbAdd ∘ ⇑Additive.ofMul,
      groupCohomology.mem_cocycles₁_of_addMonoidHom
        (A := Rep.trivial SSGRoute.PTExt.Coeff (G ⧸ N) (ZMod p)) zbAdd⟩
  have hzb : ∀ g : G, zb (QuotientGroup.mk' N g) = z g := by
    intro g
    show ((QuotientGroup.kerLift ψ) (QuotientGroup.mk' N g)).toAdd = z g
    rw [QuotientGroup.mk'_apply, QuotientGroup.kerLift_mk, hψ_apply]
    rfl
  -- Inflation of `zb` is `z`.
  have hmap : groupCohomology.mapCocycles₁ (QuotientGroup.mk' N)
      (SSGRoute.PTExt.trivResInv (QuotientGroup.mk' N) (ZMod p)) zb = z := by
    refine groupCohomology.cocycles₁_ext fun g => ?_
    rw [coe_mapCocycles₁_trivResInv_aux']
    exact hzb g
  refine ⟨N, hN, Fintype.ofFinite (G ⧸ N), ?_, ?_,
    (groupCohomology.H1π (Rep.trivial SSGRoute.PTExt.Coeff (G ⧸ N) (ZMod p))).hom zb, ?_⟩
  · exact (MulEquiv.isCyclic e).mpr inferInstance
  · rw [Nat.card_congr e.toEquiv]
    exact Nat.card_zmod p
  · rw [groupCohomology.H1π_comp_map_apply, hmap]

end Work.SSGRoute
