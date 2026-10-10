import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupHomology.LowDegree
import Submission.Work.SSGRoute.H1Pair.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open CategoryTheory

namespace Work.SSGRoute.H1Pair

universe u

variable {k : Type u} [CommRing k] {G : Type u} [Group G]

/-- The contragredient representation `A^∨`. -/
abbrev contra (A : Rep k G) : Rep k G := Rep.of A.ρ.dual

/-! ## Compatibility of the pairing with the differentials -/

/-- The pairing of a degree-`2` chain `single (g₁,g₂) a` with a cochain `θ`: both sides expand to
`θ g₂ (A.ρ g₁⁻¹ a) - θ (g₁g₂) a + θ g₁ a`. -/
theorem pairFun_d₂₁_single (A : Rep k G) (g : G × G) (a : A) (θ : G → Module.Dual k A) :
    pairFun ((groupHomology.d₂₁ A).hom (Finsupp.single g a)) θ
      = pairFun (Finsupp.single g a) ((groupCohomology.d₁₂ (contra A)).hom θ) := by
  rw [groupHomology.d₂₁_single, pairFun_add_left, pairFun_sub_left, pairFun_single, pairFun_single,
    pairFun_single, pairFun_single]
  have h1 : ((groupCohomology.d₁₂ (contra A)).hom θ) g
      = (A.ρ.dual g.1) (θ g.2) - θ (g.1 * g.2) + θ g.1 := rfl
  rw [h1, LinearMap.add_apply, LinearMap.sub_apply]
  have h2 : ((A.ρ.dual g.1) (θ g.2)) a = θ g.2 ((A.ρ g.1⁻¹) a) := by
    rw [Representation.dual_apply, Module.Dual.transpose_apply]
    rfl
  rw [h2]

/-- **Compatibility of the evaluation pairing with the differentials**: for a degree-`2` chain `x`
and a degree-`1` cochain `θ`, the pairing of `d₂₁ x` with `θ` equals the pairing of `x` with
`d₁₂ θ`. -/
theorem pairFun_d₂₁ (A : Rep k G) (x : G × G →₀ A) (θ : G → Module.Dual k A) :
    pairFun ((groupHomology.d₂₁ A).hom x) θ
      = pairFun x ((groupCohomology.d₁₂ (contra A)).hom θ) := by
  induction x using Finsupp.induction with
  | zero => simp
  | single_add g a x hg ha ih =>
      rw [map_add, pairFun_add_left, pairFun_add_left, pairFun_d₂₁_single A g a θ, ih]

/-- The pairing of a degree-`1` chain `single g a` with the coboundary of a functional `ψ`:
`⟨a·[g], d₀₁ ψ⟩ = ψ (A.ρ g⁻¹ a - a) = ψ (d₁₀ (a·[g]))`. -/
theorem pairFun_d₀₁_single (A : Rep k G) (g : G) (a : A) (ψ : Module.Dual k A) :
    pairFun (Finsupp.single g a) ((groupCohomology.d₀₁ (contra A)).hom ψ)
      = ψ ((groupHomology.d₁₀ A).hom (Finsupp.single g a)) := by
  rw [groupHomology.d₁₀_single]
  have h1 : (groupCohomology.d₀₁ (contra A)).hom ψ = fun g : G => A.ρ.dual g ψ - ψ := rfl
  rw [h1, pairFun_single]
  show ((A.ρ.dual g) ψ - ψ) a = ψ ((A.ρ g⁻¹) a - a)
  rw [LinearMap.sub_apply, map_sub]
  congr 1

/-- The pairing of a degree-`1` chain with the coboundary of a functional `ψ` against the
augmentation: `⟨c, d₀₁ ψ⟩ = ψ (d₁₀ c)`. -/
theorem pairFun_d₀₁ (A : Rep k G) (c : G →₀ A) (ψ : Module.Dual k A) :
    pairFun c ((groupCohomology.d₀₁ (contra A)).hom ψ)
      = ψ ((groupHomology.d₁₀ A).hom c) := by
  induction c using Finsupp.induction with
  | zero => simp
  | single_add g a c hg ha ih =>
      simp only [map_add, pairFun_add_left]
      rw [pairFun_d₀₁_single A g a ψ, ih]

/-! ## The two descents -/

/-- The pairing `Z₁(G,A) × Z¹(G,A^∨) → k`, as a linear map in the first variable. -/
def phiLin (A : Rep k G) : ↥(groupHomology.cycles₁ A) →ₗ[k]
    Module.Dual k ↥(groupCohomology.cocycles₁ (contra A)) where
  toFun c := (evalForm (ι := G) (A := A.V) c.1).comp
    (groupCohomology.cocycles₁ (contra A)).subtype
  map_add' c c' := by
    refine LinearMap.ext fun θ => ?_
    show pairFun (c.1 + c'.1) θ.1 = pairFun c.1 θ.1 + pairFun c'.1 θ.1
    rw [pairFun_add_left]
  map_smul' r c := by
    refine LinearMap.ext fun θ => ?_
    show pairFun (r • c.1) θ.1 = r • pairFun c.1 θ.1
    rw [pairFun_smul_left]

@[simp]
theorem phiLin_apply (A : Rep k G) (c : ↥(groupHomology.cycles₁ A))
    (θ : ↥(groupCohomology.cocycles₁ (contra A))) :
    phiLin A c θ = pairFun c.1 θ.1 := rfl

/-- The pairing vanishes on the boundaries in the first variable. -/
theorem phiLin_boundaries (A : Rep k G) (c : ↥(groupHomology.cycles₁ A))
    (hc : c.1 ∈ groupHomology.boundaries₁ A) : phiLin A c = 0 := by
  obtain ⟨x, hx⟩ := hc
  refine LinearMap.ext fun θ => ?_
  show pairFun c.1 θ.1 = 0
  rw [hx.symm, pairFun_d₂₁ A x θ.1, θ.2, pairFun_zero_right]

/-- A cycle pairs trivially with a coboundary. -/
theorem pairFun_coboundary (A : Rep k G) (c : ↥(groupHomology.cycles₁ A))
    (ψ : Module.Dual k A) :
    pairFun c.1 ((groupCohomology.d₀₁ (contra A)).hom ψ) = 0 := by
  rw [pairFun_d₀₁, c.2, map_zero]

/-- The pairing vanishes on the coboundaries in the second variable. -/
theorem phiLin_coboundaries (A : Rep k G) (c : ↥(groupHomology.cycles₁ A))
    (θ : ↥(groupCohomology.cocycles₁ (contra A)))
    (hθ : θ.1 ∈ groupCohomology.coboundaries₁ (contra A)) : phiLin A c θ = 0 := by
  obtain ⟨ψ, hψ⟩ := hθ
  rw [phiLin_apply, ← hψ, pairFun_coboundary]

/-- The pairing descends in the cycle variable to `H₁(G, A)`. -/
def phiQuot (A : Rep k G) :
    (↥(groupHomology.cycles₁ A) ⧸ (groupHomology.H1π A).hom.ker) →ₗ[k]
      Module.Dual k ↥(groupCohomology.cocycles₁ (contra A)) :=
  Submodule.liftQ _ (phiLin A) (by
    intro c hc
    rw [LinearMap.mem_ker]
    exact phiLin_boundaries A c ((groupHomology.H1π_eq_zero_iff (A := A) c).1 hc))

@[simp]
theorem phiQuot_apply (A : Rep k G) (c : ↥(groupHomology.cycles₁ A))
    (θ : ↥(groupCohomology.cocycles₁ (contra A))) :
    phiQuot A (Submodule.Quotient.mk c) θ = pairFun c.1 θ.1 := by
  rw [phiQuot, Submodule.liftQ_apply]
  rfl

/-- The pairing descends in the cochain variable as well. -/
def tatePairQuot (A : Rep k G) :
    (↥(groupCohomology.cocycles₁ (contra A)) ⧸
        (groupCohomology.H1π (contra A)).hom.ker) →ₗ[k]
      Module.Dual k (↥(groupHomology.cycles₁ A) ⧸ (groupHomology.H1π A).hom.ker) :=
  Submodule.liftQ _ (phiQuot A).flip (by
    intro θ hθ
    rw [LinearMap.mem_ker]
    refine LinearMap.ext fun x => ?_
    refine Submodule.Quotient.induction_on _ x fun c => ?_
    rw [LinearMap.flip_apply, phiQuot_apply]
    obtain ⟨ψ, hψ⟩ := (groupCohomology.H1π_eq_zero_iff (A := contra A) θ).1 hθ
    rw [show θ.1 = (groupCohomology.d₀₁ (contra A)).hom ψ from hψ.symm, pairFun_coboundary]
    rfl)

/-- `H₁(G, A)` presented as the quotient of the 1-cycles by the 1-boundaries. -/
def H1QuotEquiv (A : Rep k G) :
    (↥(groupHomology.cycles₁ A) ⧸ (groupHomology.H1π A).hom.ker) ≃ₗ[k] groupHomology.H1 A :=
  ((groupHomology.H1π A).hom).quotKerEquivOfSurjective
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

/-- The inverse of `H1QuotEquiv` on a cycle is the class of that cycle. -/
theorem H1QuotEquiv_symm_apply (A : Rep k G) (c : ↥(groupHomology.cycles₁ A)) :
    (H1QuotEquiv A).symm.toLinearMap ((groupHomology.H1π A).hom c) = Submodule.Quotient.mk c := by
  rw [H1QuotEquiv]
  exact LinearMap.quotKerEquivOfSurjective_symm_apply (f := (groupHomology.H1π A).hom) _ c

/-- `H¹(G, A)` presented as the quotient of the 1-cocycles by the 1-coboundaries. -/
def H1QuotEquivCoh (A : Rep k G) :
    (↥(groupCohomology.cocycles₁ A) ⧸ (groupCohomology.H1π A).hom.ker) ≃ₗ[k]
      groupCohomology.H1 A :=
  ((groupCohomology.H1π A).hom).quotKerEquivOfSurjective
    ((ModuleCat.epi_iff_surjective _).1 inferInstance)

/-- The inverse of `H1QuotEquivCoh` on a cocycle is the class of that cocycle. -/
theorem H1QuotEquivCoh_symm_apply (A : Rep k G)
    (θ : ↥(groupCohomology.cocycles₁ A)) :
    (H1QuotEquivCoh A).symm.toLinearMap ((groupCohomology.H1π A).hom θ)
      = Submodule.Quotient.mk θ := by
  rw [H1QuotEquivCoh]
  exact LinearMap.quotKerEquivOfSurjective_symm_apply (f := (groupCohomology.H1π A).hom) _ θ

/-- **The canonical pairing `H₁(G, A) × H¹(G, A^∨) → k`**, as a linear map
`H₁(G, A) →ₗ (H¹(G, A^∨))^∨`. -/
def tatePairLin (A : Rep k G) : groupHomology.H1 A →ₗ[k]
    Module.Dual k (groupCohomology.H1 (contra A)) :=
  (Module.Dual.transpose (H1QuotEquivCoh (contra A)).symm.toLinearMap).comp
    ((tatePairQuot A).flip.comp (H1QuotEquiv A).symm.toLinearMap)

/-- **Computation rule for the canonical pairing**: on representatives,
`⟨⟦c⟧, ⟦θ⟧⟩ = ∑_g θ g (c g)`. -/
theorem tatePairLin_apply_mk (A : Rep k G) (c : ↥(groupHomology.cycles₁ A))
    (θ : ↥(groupCohomology.cocycles₁ (contra A))) :
    tatePairLin A ((groupHomology.H1π A).hom c)
      ((groupCohomology.H1π (contra A)).hom θ) = pairFun c.1 θ.1 := by
  rw [tatePairLin, LinearMap.comp_apply, LinearMap.comp_apply, Module.Dual.transpose_apply,
    LinearMap.comp_apply, H1QuotEquivCoh_symm_apply, H1QuotEquiv_symm_apply, LinearMap.flip_apply,
    tatePairQuot, Submodule.liftQ_apply, LinearMap.flip_apply, phiQuot_apply]

end Work.SSGRoute.H1Pair
