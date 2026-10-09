import Mathlib
import Submission.NK.HassePrinciple.CyclicBase
import Submission.NK.HassePrinciple.IdelesLevel
import Submission.NK.HassePrinciple.subsingleton_groupCohomology_one_ideleClassGroup_all
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open CategoryTheory NK.GlobalCFT

namespace NK.HassePrinciple

/-- **`H¹` of a `ℤ`-coefficient representation vanishes iff every multiplicative `1`-cocycle is a
coboundary.**  The low-degree API of `groupCohomology` is coefficient-agnostic: `H1π_eq_zero_iff`
identifies the kernel of the projection `Z¹ → H¹` with the coboundaries, and
`H1_induction_on` reduces a statement about `H¹` to its values on cocycles.  Hence `H¹ = 0`
translated to the multiplicative language of `IsMulCocycle₁`/`IsMulCoboundary₁`. -/
theorem mulCoboundary_of_subsingleton_groupCohomology_one {G M : Type} [Group G] [CommGroup M]
    [MulDistribMulAction G M]
    (h : Subsingleton (groupCohomology (Rep.ofMulDistribMulAction G M) 1)) :
    ∀ c : G → M, groupCohomology.IsMulCocycle₁ c →
      groupCohomology.IsMulCoboundary₁ (M := M) c := by
  intro c hc
  have hzero : groupCohomology.H1π (Rep.ofMulDistribMulAction G M)
      (groupCohomology.cocyclesOfIsMulCocycle₁ hc) = 0 := h.elim _ _
  have hmem : c ∈ groupCohomology.coboundaries₁ (Rep.ofMulDistribMulAction G M) :=
    (groupCohomology.H1π_eq_zero_iff _).1 hzero
  exact groupCohomology.isMulCoboundary₁_of_mem_coboundaries₁ c hmem

/-- **`H¹` of a `k`-linear representation vanishes if every multiplicative `1`-cocycle is a
coboundary.**  This is the "same carrier, same action, different coefficient ring" transfer: the
complex of inhomogeneous cochains of `Rep.ofDistribMulAction k G (Additive M)` has carriers
`(Fin n → G) → Additive M` and differentials built from `ρ` and `+` only, so vanishing of `H¹` is
a statement about the `G`-action on `M`, not about the coefficient ring. -/
theorem subsingleton_groupCohomology_one_of_mulCoboundary (k : Type) [CommRing k] {G M : Type}
    [Group G] [CommGroup M] [MulDistribMulAction G M] [Module k (Additive M)]
    [SMulCommClass G k (Additive M)]
    (h : ∀ c : G → M, groupCohomology.IsMulCocycle₁ c →
      groupCohomology.IsMulCoboundary₁ (M := M) c) :
    Subsingleton (groupCohomology (Rep.ofDistribMulAction k G (Additive M)) 1) := by
  have key : ∀ a : groupCohomology (Rep.ofDistribMulAction k G (Additive M)) 1, a = 0 := by
    intro a
    refine groupCohomology.H1_induction_on a (fun x => ?_)
    refine (groupCohomology.H1π_eq_zero_iff x).2 ?_
    let y : G → Additive M := fun g => x.1 g
    have hunits : ∀ (g : G) (a : Additive M),
        (Rep.ofDistribMulAction k G (Additive M)).ρ g a = Additive.ofMul (g • a.toMul) :=
      fun _ _ => rfl
    have hcoc : groupCohomology.IsMulCocycle₁ (M := M) (fun g => Additive.toMul (y g)) := by
      intro g h'
      have h1 : y (g * h') = Additive.ofMul (g • Additive.toMul (y h')) + y g := by
        have h0 := (groupCohomology.mem_cocycles₁_iff
          (A := Rep.ofDistribMulAction k G (Additive M)) (x.1)).1 x.2 g h'
        rw [hunits g (y h')] at h0
        exact h0
      calc Additive.toMul (y (g * h'))
          = Additive.toMul (Additive.ofMul (g • Additive.toMul (y h')) + y g) := by rw [h1]
        _ = Additive.toMul (Additive.ofMul (g • Additive.toMul (y h'))) * Additive.toMul (y g) :=
            toMul_add _ _
        _ = (g • Additive.toMul (y h')) * Additive.toMul (y g) := by rw [toMul_ofMul]
    obtain ⟨β, hβ⟩ := h (fun g => Additive.toMul (y g)) hcoc
    let hw : (Rep.ofDistribMulAction k G (Additive M)).V := Additive.ofMul β
    refine ⟨hw, ?_⟩
    funext g
    rw [groupCohomology.d₀₁_hom_apply]
    simp only [hw]
    rw [show (Rep.ofDistribMulAction k G (Additive M)).ρ g (Additive.ofMul β)
        = Additive.ofMul (g • β) from rfl]
    change Additive.ofMul (g • β) - Additive.ofMul β = y g
    rw [← ofMul_div (x := g • β) (y := β), hβ g]
    exact ofMul_toMul (y g)
  exact ⟨fun a b => by rw [key a, key b]⟩

set_option maxHeartbeats 1600000 in
/-- **`H¹(Γ, C_E) = 0` in this chapter's coefficient ring**: the `CoeffInt`-linear version of
`NK.HassePrinciple.subsingleton_groupCohomology_one_ideleClassGroup_all`.

`NK.HassePrinciple.classGroupRep F E` is the idèle class group `C_E` as a
`CoeffInt = ULift ℤ`-linear representation of `Gal(E/F)`
(`NK.HassePrinciple.classGroupRep F E = Rep.ofDistribMulAction CoeffInt (E ≃ₐ[F] E)
(Additive (IdeleClassGroup E))`), whereas `NK.GlobalCFT.IdeleClassGroup.rep F E` is the same
group with the same action, but `ℤ`-linear.  The two have the same carrier and the same
`Gal(E/F)`-action, and `groupCohomology` is computed by an explicit cochain complex
(`groupCohomology.inhomogeneousCochains`) whose carriers `(Fin n → Γ) → V` and whose differentials
are given by the same formulas in the action and the addition, so the *sets* of cocycles and
coboundaries agree; hence `Subsingleton` of `H¹` transfers between the two coefficient rings.  (A
general transfer statement for `groupCohomology` along `ℤ → ULift ℤ` would be the clean way to
phrase this.)

This is what the assembly of the relative Hasse–Brauer–Noether result needs: the edge map
`H²(Γ, Lˣ) → H²(Γ, 𝕀_L)` is injective as soon as `H¹(Γ, C_L) = 0` in the same coefficient ring
(`NK.HassePrinciple.injective_h2_units_of_subsingleton_h1_classGroupRep`). -/
theorem subsingleton_classGroupRep_one (h : NK.HassePrinciple.CyclicHasseInput) {F E : Type}
    [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [FiniteDimensional F E]
    [IsGalois F E] :
    Subsingleton (groupCohomology (NK.HassePrinciple.classGroupRep F E) 1) :=
  subsingleton_groupCohomology_one_of_mulCoboundary CoeffInt
    (mulCoboundary_of_subsingleton_groupCohomology_one
      (subsingleton_groupCohomology_one_ideleClassGroup_all h))

end NK.HassePrinciple
