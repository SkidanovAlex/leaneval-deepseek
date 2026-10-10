import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.FreeGroup.Basic
import Submission.Work.SSGRoute.exists_kerSuccAddEquiv_equivariant
import Submission.Work.SSGRoute.isCocycle2_isLocConst2_transported_cocycle
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Work.CohomologicalShrinking

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

/-- **The transported section cocycle is a `2`-cocycle.**

Let `π = flowGroupSucc p G m i j : Γ(τ+1) →* Γ(τ)` be the projection of the refined filtration,
with commutative kernel `A = ker π`, `s` a normalized section of `π`, `ρ : H →* Γ(τ)` a
homomorphism and `κ = kerSuccCocycle ρ s` the pulled back section cocycle, with values in
`Additive A` (with the conjugation `H`-module structure obtained from the `Γ(τ)`-action via
`kernelAction` and `ρ`).  Let `e : Additive A →+ E(m,τ)` be an additive map that is
`G`-equivariant with respect to conjugation by the canonical lifts `mk 1 g`:

`e (mk 1 g · x · (mk 1 g)⁻¹) = g • e x`.

Then `e ∘ κ` is a `2`-cocycle on `H` with coefficients in `E(m,τ)`, where `H` acts through
`flowQuot ∘ ρ : H →* G`.  This is what lets the extension class of the pulled back extension be
read off in the coefficient module `E(m,τ)` of the shrinking argument.

The proof combines two inputs: the cocycle identity of `κ` with respect to conjugation by the
chosen lift `s (ρ σ)` (`kerSuccCocycle_cocycle_conj`), and the fact that this conjugation action
only depends on the `G`-coordinate (`kerSucc_conj_eq_mk_one`), so that `e` turns it into the
`G`-action used in `he`. -/
theorem kerSuccCocycle_transport_mem_Z2 (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    {H : Type*} [Group H] (ρ : H →* Work.CohomologicalShrinking.flowGroup p G m i j)
    (s : Work.CohomologicalShrinking.flowGroup p G m i j →
      Work.CohomologicalShrinking.flowGroup p G m
        (Work.CohomologicalShrinking.tauSucc i j).1 (Work.CohomologicalShrinking.tauSucc i j).2)
    (hs : ∀ x, Work.SSGRoute.flowGroupSucc p G m i j (s x) = x) (h1 : s 1 = 1)
    (hcomm : ∀ a b : ↥(Work.SSGRoute.flowGroupSucc p G m i j).ker, a * b = b * a)
    (e : Additive ↥(Work.SSGRoute.flowGroupSucc p G m i j).ker →+
        Work.CohomologicalShrinking.E p G m i j)
    (he : ∀ (g : G) (x : Additive ↥(Work.SSGRoute.flowGroupSucc p G m i j).ker),
        e (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul
            (Work.SSGRoute.flowGroupSucc p G m i j)
            (SemidirectProduct.mk 1 g : Work.CohomologicalShrinking.flowGroup p G m
              (Work.CohomologicalShrinking.tauSucc i j).1
              (Work.CohomologicalShrinking.tauSucc i j).2) (Additive.toMul x))) = g • e x) :
    letI : CommGroup ↥(Work.SSGRoute.flowGroupSucc p G m i j).ker :=
      { (inferInstance : Group ↥(Work.SSGRoute.flowGroupSucc p G m i j).ker) with
        mul_comm := hcomm }
    letI : DistribMulAction (Work.CohomologicalShrinking.flowGroup p G m i j)
        (Additive ↥(Work.SSGRoute.flowGroupSucc p G m i j).ker) :=
      Work.AbsoluteGalois.kernelAction (Work.SSGRoute.flowGroupSucc p G m i j) s hs h1 hcomm
    letI : DistribMulAction H (Additive ↥(Work.SSGRoute.flowGroupSucc p G m i j).ker) :=
      DistribMulAction.compHom _ ρ
    letI : DistribMulAction H (Work.CohomologicalShrinking.E p G m i j) :=
      DistribMulAction.compHom (Work.CohomologicalShrinking.E p G m i j)
        ((Work.CohomologicalShrinking.flowQuot p G m i j).comp ρ)
    (fun x : H × H => e (Work.SSGRoute.kerSuccCocycle p G m i j ρ s hs x.1 x.2))
      ∈ Work.GroupCohomology.Z2 H (Work.CohomologicalShrinking.E p G m i j) := by
  letI : CommGroup ↥(flowGroupSucc p G m i j).ker :=
    { (inferInstance : Group ↥(flowGroupSucc p G m i j).ker) with mul_comm := hcomm }
  letI : DistribMulAction (flowGroup p G m i j)
      (Additive ↥(flowGroupSucc p G m i j).ker) :=
    Work.AbsoluteGalois.kernelAction (flowGroupSucc p G m i j) s hs h1 hcomm
  letI : DistribMulAction H (Additive ↥(flowGroupSucc p G m i j).ker) :=
    DistribMulAction.compHom _ ρ
  letI : DistribMulAction H (E p G m i j) :=
    DistribMulAction.compHom (E p G m i j) ((flowQuot p G m i j).comp ρ)
  -- The `H`-action on `E p G m i j` transported through `ρ` computes as conjugation by the
  -- chosen lift `s (ρ σ)`; this is `he` combined with centrality of the kernel.
  have hsmul : ∀ (σ : H) (y : ↥(flowGroupSucc p G m i j).ker),
      σ • (e (Additive.ofMul y))
        = e (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul (flowGroupSucc p G m i j)
            (s (ρ σ)) y)) := by
    intro σ y
    -- the `G`-coordinate of `s (ρ σ)` is that of `ρ σ`, since `s` is a section
    have hsr : (s (ρ σ)).right = (ρ σ).right := by
      rw [← flowGroupSucc_right p G m i j (s (ρ σ)), hs (ρ σ)]
    have hconj := kerSucc_conj_eq_mk_one p G i j m (s (ρ σ)).left (s (ρ σ)).right y
    rw [show (SemidirectProduct.mk (s (ρ σ)).left (s (ρ σ)).right :
        flowGroup p G m (tauSucc i j).1 (tauSucc i j).2) = s (ρ σ) from rfl] at hconj
    rw [hsr] at hconj
    rw [show σ • (e (Additive.ofMul y))
          = ((flowQuot p G m i j) (ρ σ)) • (e (Additive.ofMul y)) from rfl,
      show ((flowQuot p G m i j) (ρ σ)) = (ρ σ).right from rfl]
    rw [hconj]
    exact (he (ρ σ).right (Additive.ofMul y)).symm
  rw [Work.GroupCohomology.mem_Z2_iff]
  intro σ τ υ
  -- the cocycle identity for `κ`, with the conjugation action by `s (ρ σ)`
  have hkey := kerSuccCocycle_cocycle_conj p m i j ρ s hs h1 σ τ υ
  have hkey2 := congrArg e hkey
  simp only [map_sub, map_add, map_zero] at hkey2
  -- rewrite the `H`-action on `c (τ, υ)` as that conjugation
  have hσ : σ • e (kerSuccCocycle p G m i j ρ s hs τ υ)
      = e (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul (flowGroupSucc p G m i j)
          (s (ρ σ)) (Additive.toMul (kerSuccCocycle p G m i j ρ s hs τ υ)))) :=
    hsmul σ (kerSuccCocycleMul p G m i j ρ s hs τ υ)
  rw [hσ]
  -- solve the resulting additive identity in the abelian group `E p G m i j`
  have hA : e (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul (flowGroupSucc p G m i j)
        (s (ρ σ)) (Additive.toMul (kerSuccCocycle p G m i j ρ s hs τ υ))))
      = e (kerSuccCocycle p G m i j ρ s hs (σ * τ) υ)
        - e (kerSuccCocycle p G m i j ρ s hs σ (τ * υ))
        + e (kerSuccCocycle p G m i j ρ s hs σ τ) := by
    have hh : e (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul (flowGroupSucc p G m i j)
          (s (ρ σ)) (Additive.toMul (kerSuccCocycle p G m i j ρ s hs τ υ))))
        - (e (kerSuccCocycle p G m i j ρ s hs (σ * τ) υ)
          - e (kerSuccCocycle p G m i j ρ s hs σ (τ * υ))
          + e (kerSuccCocycle p G m i j ρ s hs σ τ)) = 0 := by
      rw [show e (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul (flowGroupSucc p G m i j)
            (s (ρ σ)) (Additive.toMul (kerSuccCocycle p G m i j ρ s hs τ υ))))
          - (e (kerSuccCocycle p G m i j ρ s hs (σ * τ) υ)
            - e (kerSuccCocycle p G m i j ρ s hs σ (τ * υ))
            + e (kerSuccCocycle p G m i j ρ s hs σ τ))
        = e (Additive.ofMul (Work.AbsoluteGalois.conjKernelMul (flowGroupSucc p G m i j)
            (s (ρ σ)) (Additive.toMul (kerSuccCocycle p G m i j ρ s hs τ υ))))
          - e (kerSuccCocycle p G m i j ρ s hs (σ * τ) υ)
          + e (kerSuccCocycle p G m i j ρ s hs σ (τ * υ))
          - e (kerSuccCocycle p G m i j ρ s hs σ τ) from by abel]
      exact hkey2
    exact sub_eq_zero.mp hh
  rw [hA]
  abel

end Work.SSGRoute
