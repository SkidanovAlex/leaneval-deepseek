import Mathlib
import Submission.Work.ShafarevichKoch.CohomologyAction

/-!
# `Work.ShafarevichKoch.conjKer_mem_coboundaries1`

The conjugation action of `G` on `ker π` (see `CohomologyAction.lean`) induces an action of `G`
on the module of 1-coboundaries `B¹(ker π, A)`, by twisting a cochain `f` by `g`:
`(g · f)(n) = A.ρ g (f (g⁻¹ n g))`.  This file shows that this operation preserves the
1-coboundaries -- the companion fact that it preserves the 1-cocycles is
`conjKer_mem_cocycles1`.  Together they give `G`-equivariance of the identification
`B¹(ker π, A) ⊆ Z¹(ker π, A)`.

The proof is the standard conjugation computation: if `f = d₀₁ x` for some `x`, then the
twisted cochain is `d₀₁ (A.ρ g x)`.
-/

namespace Work.ShafarevichKoch

/-- Conjugation identity for a representation: `ρ h (ρ g x) = ρ g (ρ (g⁻¹ h g) x)`. -/
lemma rho_conj_apply {k G : Type} [CommRing k] [Group G] (A : Rep k G) (g h : G) (x : A.V) :
    A.ρ h (A.ρ g x) = A.ρ g (A.ρ (g⁻¹ * h * g) x) := by
  simp only [← Module.End.mul_apply, ← map_mul]
  congr 1
  group

theorem conjKer_mem_coboundaries1 {k G Q : Type} [CommRing k] [Group G] [Group Q]
    (π : G →* Q) (A : Rep k G) (g : G)
    (f : ↥(groupCohomology.coboundaries₁ (Rep.res (MonoidHom.ker π).subtype A))) :
    (fun n : MonoidHom.ker π => A.ρ g (f (Work.ShafarevichKoch.conjKer π g⁻¹ n)))
      ∈ groupCohomology.coboundaries₁ (Rep.res (MonoidHom.ker π).subtype A) := by
  obtain ⟨x, hx⟩ := LinearMap.mem_range.mp f.2
  refine LinearMap.mem_range.mpr ⟨A.ρ g x, ?_⟩
  funext n
  simp only [← groupCohomology.coboundaries₁.val_eq_coe] at hx ⊢
  rw [groupCohomology.d₀₁_hom_apply, ← congr_fun hx (conjKer π g⁻¹ n),
    groupCohomology.d₀₁_hom_apply, map_sub]
  show A.ρ (n : G) (A.ρ g x) - A.ρ g x
      = A.ρ g (A.ρ ((conjKer π g⁻¹ n : MonoidHom.ker π) : G) x) - A.ρ g x
  rw [rho_conj_apply A g (n : G) x, conjKer_coe, inv_inv]

end Work.ShafarevichKoch
