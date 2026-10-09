import Mathlib
import Submission.Work.SSGRoute.PT.shapiro_H2_inj
import Submission.Work.SSGRoute.PT.shapiro_H2_coind
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Transferring the kernel of Shapiro's map `H²` across an equivariant isomorphism

Shapiro's lemma in degree `2` (`Submission.Work.SSGRoute.PT.shapiro_H2_inj`) says that a locally
constant `2`-cocycle `c` of `G` with values in the coinduced module `Coind_U^G M` whose restriction
to `U` (i.e. `(u, v) ↦ c (u, v) 1`) is the coboundary of a locally constant `1`-cochain of `U` is
itself a coboundary of a locally constant `1`-cochain of `G`.

The present file *transfers* that statement across an abstract `G`-module `W` which is only
*equivariantly isomorphic* to `Coind_U^G M`.  Concretely, from a `G`-equivariant additive
isomorphism `Φ : W ≃+ Coind_U^G M`, a locally constant `2`-cocycle `z` of `G` with values in `W`
becomes a locally constant `2`-cocycle `Φ ∘ z` of `G` with values in `Coind_U^G M`; if its
restriction to `U` is a coboundary then Shapiro produces a primitive `B` of `Φ ∘ z`, and `Φ.symm ∘ B`
is a primitive of `z` (it is locally constant because local constancy only constrains the *domain*,
`Work.AbsoluteKummer.IsLocallyConstant.map`).

This is exactly the shape needed downstream (`Submission.Work.SSGRoute.PT.e1a_sha2_mem_deltaRange`):
there `W` is the "free / hom-coinduced" model `Hom_ℤ(ℤ[Gal(K/k)]^n, Ωˣ)` of the coinduced module.
-/

namespace Work.SSGRoute.PT

/-- **Kernel half of Shapiro's lemma, transferred along an equivariant isomorphism.**

Let `G` be a topological group, `U ≤ G` an open subgroup of finite index and `M` a `U`-module. Let
`W` be a `G`-module equivariantly isomorphic to the coinduced module `Coind_U^G M` through an
additive isomorphism `Φ`.  If `z : G × G → W` is a locally constant `2`-cocycle of `G` whose
`Φ`-image restricts on `U` to a `1`-coboundary of a locally constant `1`-cochain of `U`, then `z`
is a `2`-coboundary of a locally constant `1`-cochain of `G`. -/
theorem shapiro_kernel_transfer {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (U : Subgroup G) (hU : IsOpen (U : Set G)) [U.FiniteIndex]
    {M : Type*} [AddCommGroup M] [DistribMulAction U M]
    {W : Type*} [AddCommGroup W] [DistribMulAction G W]
    (Φ : W ≃+ Work.SSGRoute.PT.Coind G U M)
    (hΦ : ∀ (g : G) (w : W), Φ (g • w) = g • Φ w)
    (z : G × G → W) (hz : z ∈ Work.AbsoluteKummer.Z2 G W)
    (hb : ∃ b ∈ Work.AbsoluteKummer.C1c U M,
        Work.GroupCohomology.d1 U M b = fun p : U × U => (Φ (z (p.1, p.2))) 1) :
    z ∈ Work.AbsoluteKummer.B2 G W := by
  -- Unpack the hypotheses on `z`: it is a `2`-cocycle which is locally constant.
  obtain ⟨hcoc, hlc⟩ := (Work.AbsoluteKummer.mem_Z2_iff z).mp hz
  -- The transported cocycle `Φ ∘ z` on the coinduced module.
  have hcZ2 : (fun p : G × G => Φ (z p)) ∈
      Work.AbsoluteKummer.Z2 G (Work.SSGRoute.PT.Coind G U M) := by
    rw [Work.AbsoluteKummer.mem_Z2_iff]
    refine ⟨?_, hlc.map Φ⟩
    intro g h k
    -- additivity of `Φ` turns the `Z²`-condition for `z` into that for `Φ ∘ z`, and the
    -- `G`-equivariance of `Φ` matches the two `G`-actions.
    show Φ (z (g * h, k)) + Φ (z (g, h)) = g • Φ (z (h, k)) + Φ (z (g, h * k))
    rw [← hΦ g (z (h, k)), ← map_add, ← map_add, hcoc g h k]
  rw [Work.AbsoluteKummer.mem_B2_iff]
  -- Shapiro's lemma (kernel half) produces a locally constant primitive `B` of `Φ ∘ z` on `G`.
  obtain ⟨B, hBC1c, hBeq⟩ :=
    shapiro_H2_inj U hU (fun p : G × G => Φ (z p)) hcZ2 hb
  -- Pull `B` back along `Φ`: it is locally constant (only the domain is constrained), and `Φ`
  -- intertwines `d¹` on `W` with `d¹` on `Coind_U^G M`, so it is a primitive of `z`.
  refine ⟨fun g => Φ.symm (B g), ?_, ?_⟩
  · exact hBC1c.map Φ.symm
  · have hkey : ∀ g h : G, Φ ((Work.GroupCohomology.d1 G W (fun g => Φ.symm (B g))) (g, h))
        = (Work.GroupCohomology.d1 G (Work.SSGRoute.PT.Coind G U M) B) (g, h) := by
      intro g h
      simp only [Work.GroupCohomology.d1_apply, map_add, map_sub, hΦ,
        AddEquiv.apply_symm_apply]
    funext p
    obtain ⟨g, h⟩ := p
    apply Φ.injective
    rw [hkey, hBeq]

end Work.SSGRoute.PT
