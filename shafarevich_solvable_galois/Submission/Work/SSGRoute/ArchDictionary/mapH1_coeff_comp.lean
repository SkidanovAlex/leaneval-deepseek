import Mathlib
import Submission.Work.GroupCohomology.Functoriality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ArchDictionary

open Work.GroupCohomology

/-- `mapH1` depends only on the underlying additive map, not on the supplied proof of
`G`-equivariance (proof irrelevance for the `Prop`-valued hypothesis). -/
theorem mapH1_equivariant_proof_irrel {G : Type*} [Group G]
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction G A] [DistribMulAction G B]
    (φ : A →+ B) (h₁ h₂ : IsEquivariant G φ) :
    mapH1 G φ h₁ = mapH1 G φ h₂ := by
  refine AddMonoidHom.ext fun z => ?_
  induction z using H1_induction_on with
  | h f => rw [mapH1_H1π]

/-- `mapH1` is invariant under replacing the coefficient map by an equal coefficient map
(regardless of the two equivariance proofs). -/
theorem mapH1_congr_hom {G : Type*} [Group G]
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction G A] [DistribMulAction G B]
    {φ₁ φ₂ : A →+ B} (h : φ₁ = φ₂) (h₁ : IsEquivariant G φ₁) (h₂ : IsEquivariant G φ₂) :
    mapH1 G φ₁ h₁ = mapH1 G φ₂ h₂ := by
  cases h
  exact mapH1_equivariant_proof_irrel φ₁ h₁ h₂

/-- Functoriality of `H¹` in the coefficient, in "comparison" form: given coefficient maps
`f : A →+ A'`, `Ψ : A →+ B`, `Ψ' : A' →+ B'` and a comparison `g : B →+ B'` with `Ψ' ∘ f = g ∘ Ψ`
(all equivariant for the action of `G`), the two composite maps on `H¹` agree. -/
theorem mapH1_coeff_comp {G : Type*} [Group G]
    {A A' B B' : Type*} [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B] [AddCommGroup B']
    [DistribMulAction G A] [DistribMulAction G A'] [DistribMulAction G B] [DistribMulAction G B']
    (f : A →+ A') (hf : IsEquivariant G f) (Ψ : A →+ B) (hΨ : IsEquivariant G Ψ)
    (Ψ' : A' →+ B') (hΨ' : IsEquivariant G Ψ') (g : B →+ B') (hg : IsEquivariant G g)
    (hcomp : Ψ'.comp f = g.comp Ψ) (z : H1 G A) :
    mapH1 G Ψ' hΨ' (mapH1 G f hf z) = mapH1 G g hg (mapH1 G Ψ hΨ z) := by
  have h1 := mapH1_comp G f Ψ' hf hΨ'
  have h2 := mapH1_comp G Ψ g hΨ hg
  calc mapH1 G Ψ' hΨ' (mapH1 G f hf z)
      = (mapH1 G Ψ' hΨ').comp (mapH1 G f hf) z := rfl
    _ = mapH1 G (Ψ'.comp f) (hΨ'.comp hf) z := by rw [h1]
    _ = mapH1 G (g.comp Ψ) (hg.comp hΨ) z := by
          rw [mapH1_congr_hom hcomp (hΨ'.comp hf) (hg.comp hΨ)]
    _ = (mapH1 G g hg).comp (mapH1 G Ψ hΨ) z := by rw [h2]
    _ = mapH1 G g hg (mapH1 G Ψ hΨ z) := rfl

end Work.SSGRoute.ArchDictionary
