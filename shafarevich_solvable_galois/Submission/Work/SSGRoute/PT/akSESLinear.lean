import Mathlib
import Submission.Work.SSGRoute.PT.akZmodLinear
import Submission.Work.AbsoluteKummer.SES.Connecting
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `𝔽_p`-linearity of the connecting map `δ : H⁰(P) → H¹(M)` of a short exact sequence

`PT/akZmodLinear.lean` proves the `ebot` inputs of the `r = 1` descent (`α¹`) up to the
`𝔽_p`-linearity of the maps involved.  For the *module* short exact sequence
`0 → M → N → P → 0` of a `𝔽_p[G]`-module sequence, the connecting map
`δ : H⁰(G,P) →+ H¹(G,M)` (`PT.Connecting`'s `delta`) is `𝔽_p`-linear — even though its definition
goes through the `Classical.choose`-based lift `liftOf` and the section `iotaInv`.

This file supplies that linearity (`delta_smul`), with the linearity of `iota` and `pi` as
hypotheses (both hold in the dévissage application, where the maps are those of `𝔽_p`-modules), so
that `AKZmodLin.exact_transpDelta_of_zmod` / `exact_transpInvariants_of_zmod` can be applied with
`δm := S.delta`.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

open Classical

namespace Work.SSGRoute.PT

namespace AKZmodLin

section SESLin

variable {p : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module (ZMod p) M] [Module (ZMod p) N] [Module (ZMod p) P]
  [DistribMulAction G M] [DistribMulAction G N] [DistribMulAction G P]
  [SMulCommClass G (ZMod p) M] [SMulCommClass G (ZMod p) N] [SMulCommClass G (ZMod p) P]

/-- **The inverse of `ι` on `range ι` is `𝔽_p`-linear**, `ι` being `𝔽_p`-linear. -/
theorem iotaInv_smul (S : Work.AbsoluteKummer.ShortExactSeq G M N P)
    (hι : ∀ (c : ZMod p) (m : M), S.iota (c • m) = c • S.iota m)
    (c : ZMod p) {y : N} (hy : y ∈ S.iota.range) :
    S.iotaInv (c • y) = c • S.iotaInv y := by
  have hy' : c • y ∈ S.iota.range := by
    obtain ⟨m, rfl⟩ := hy
    exact ⟨c • m, by rw [hι]⟩
  apply S.iota_injective
  rw [S.iota_iotaInv hy', hι, S.iota_iotaInv hy]

/-- **The cocycle `g ↦ ι⁻¹(g • n − n)` is `𝔽_p`-homogeneous in its lift** (as an element of
`Z¹_c(G,M)`), `ι` being `𝔽_p`-linear. -/
theorem cocycleOf_smul (S : Work.AbsoluteKummer.ShortExactSeq G M N P)
    (hι : ∀ (c : ZMod p) (m : M), S.iota (c • m) = c • S.iota m)
    (c : ZMod p) (n : N) (hn : S.pi n ∈ Work.AbsoluteKummer.H0 G P)
    (hn' : S.pi (c • n) ∈ Work.AbsoluteKummer.H0 G P) :
    S.cocycleOf (c • n) hn' = c • S.cocycleOf n hn := by
  refine Subtype.ext (funext fun g => ?_)
  simp only [S.cocycleOf_apply, Work.SSGRoute.PTembedding.instModuleZ1c_coe_smul, Pi.smul_apply]
  rw [show g • (c • n) - (c • n) = c • (g • n - n) by
    rw [smul_comm g c n]
    exact (smul_sub c (g • n) n).symm]
  exact iotaInv_smul S hι c (S.mem_range_of_mem_ker (S.mem_ker_smul_sub n hn g))

/-- **The connecting map `δ : H⁰(G,P) →+ H¹(G,M)` is `𝔽_p`-linear** for an `𝔽_p`-linear short exact
sequence of `𝔽_p[G]`-modules. -/
theorem delta_smul (S : Work.AbsoluteKummer.ShortExactSeq G M N P)
    (hι : ∀ (c : ZMod p) (m : M), S.iota (c • m) = c • S.iota m)
    (hπ : ∀ (c : ZMod p) (n : N), S.pi (c • n) = c • S.pi n)
    (c : ZMod p) (q : Work.AbsoluteKummer.H0 G P) :
    S.delta (c • q) = c • S.delta q := by
  have hn' : S.pi (c • S.liftOf q) ∈ Work.AbsoluteKummer.H0 G P := by
    rw [hπ]
    intro g
    rw [smul_comm g c (S.pi (S.liftOf q)), S.liftOf_invariant q g]
  have hpi : S.pi (S.liftOf (c • q)) = S.pi (c • S.liftOf q) := by
    rw [S.pi_liftOf, hπ, S.pi_liftOf,
      Work.SSGRoute.PT.AKZmodLin.instModuleH0_coe_smul]
  rw [S.delta_apply, S.delta_apply, smul_H1π,
    S.class_eq (S.liftOf_invariant (c • q)) hn' hpi,
    cocycleOf_smul S hι c (S.liftOf q) (S.liftOf_invariant q) hn']

/-- **`ebot₂` for the connecting map of a short exact sequence**: the transposed exactness at
`(H¹(N))^∨` with `δm := S.delta`, its `𝔽_p`-linearity coming from `delta_smul`. -/
theorem exact_transpDelta_delta [Fact p.Prime]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P)
    (hι : ∀ (c : ZMod p) (m : M), S.iota (c • m) = c • S.iota m)
    (hπ : ∀ (c : ZMod p) (n : N), S.pi (c • n) = c • S.pi n)
    (c₀ : Type) [AddCommGroup c₀] [DistribMulAction G c₀]
    (φ : M →+ N) (hφ : Work.GroupCohomology.IsEquivariant G φ)
    (hlinφ : ∀ (c : ZMod p) (m : M), φ (c • m) = c • φ m)
    (hex : S.delta.range = (Work.AbsoluteKummer.mapH1 φ hφ).ker) :
    Function.Exact
      (transpMapH1' (G := G) (N := M) (N₂ := N) (C := c₀) φ hφ)
      (transpDelta (G := G) (N := M) (N₁ := P) (C := c₀) S.delta) :=
  exact_transpDelta_of_zmod (G := G) (N := M) (N₁ := P) (N₂ := N) (C := c₀)
    φ hφ hlinφ S.delta (fun c x => delta_smul S hι hπ c x) hex

/-- **`ebot₃` for the connecting map of a short exact sequence**: the transposed exactness at
`(H⁰(P))^∨` with `δm := S.delta`, its `𝔽_p`-linearity coming from `delta_smul`. -/
theorem exact_transpInvariants_delta [Fact p.Prime]
    (S : Work.AbsoluteKummer.ShortExactSeq G M N P)
    (hι : ∀ (c : ZMod p) (m : M), S.iota (c • m) = c • S.iota m)
    (hπ : ∀ (c : ZMod p) (n : N), S.pi (c • n) = c • S.pi n)
    (c₀ : Type) [AddCommGroup c₀] [DistribMulAction G c₀]
    (ψ : N →+ P) (hψ : Work.GroupCohomology.IsEquivariant G ψ)
    (hlinψ : ∀ (c : ZMod p) (n : N), ψ (c • n) = c • ψ n)
    (hex : (invariantsHom ψ hψ).range = S.delta.ker) :
    Function.Exact
      (transpDelta (G := G) (N := M) (N₁ := P) (C := c₀) S.delta)
      (transpInvariants (G := G) (N₁ := P) (N₂ := N) (C := c₀) ψ hψ) :=
  exact_transpInvariants_of_zmod (G := G) (N := M) (N₁ := P) (N₂ := N) (C := c₀)
    ψ hψ hlinψ S.delta (fun c x => delta_smul S hι hπ c x) hex

end SESLin

end AKZmodLin

end Work.SSGRoute.PT
