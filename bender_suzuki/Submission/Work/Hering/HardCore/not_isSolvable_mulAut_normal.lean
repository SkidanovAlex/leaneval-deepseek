import Mathlib
import Submission.Work.Hering.Config
import Submission.Work.Hering.GL32.gl32_not_solvable_v2
import Submission.Work.Hering.Step5.mulAut_eight_order21

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Aut(D)` is not solvable for `D` a normal subgroup containing the reduced configuration's `V`

Let `G` be a finite group with a normal elementary abelian subgroup `V` of order `8`
(`Work.Hering.ActsAsAut V hV`: the conjugation action of `G` realises *all* automorphisms of `V`,
i.e. `G/C_G(V) ≅ GL(3,2)`).  Then for every normal subgroup `D ⊴ G` with `V ≤ D`, the
automorphism group `MulAut ↥D` is not solvable.

The proof is short and structural.  `G` acts by conjugation on `D` (`ψ`) and on `V` (`θ`); since
`V ≤ D`, we have `ker ψ ≤ ker θ`.  Hence `θ` descends to a surjection
`G ⧸ ker ψ →* MulAut ↥V`, while `G ⧸ ker ψ ≃* ψ.range ≤ MulAut ↥D`.  As `V` is elementary abelian
of order `8`, `MulAut ↥V ≅ GL(3,2)` is not solvable
(`Work.Hering.GL32.gl32_not_solvable_v2` via `Work.Hering.Step5.iso_fin3`).  So the non-solvable
group `G ⧸ ker ψ` is (up to isomorphism) a subgroup of `MulAut ↥D`, and subgroups of a solvable
group are solvable; contradiction.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.Hering.HardCore

theorem not_isSolvable_mulAut_normal {G : Type} [Group G] [Finite G]
    (V D : Subgroup G) (hV : V.Normal) (hcard : Nat.card V = 8)
    (hexp : ∀ x ∈ V, x * x = 1) (hAut : Work.Hering.ActsAsAut V hV)
    (hD : D.Normal) (hVD : V ≤ D) :
    ¬ Group.IsSolvable (MulAut ↥D) := by
  -- the normality hypotheses as instances, for `MulAut.conjNormal`
  haveI hVn : V.Normal := hV
  haveI hDn : D.Normal := hD
  intro hsol
  -- `Aut(V) ≅ GL(3,2)` is not solvable
  have hVns : ¬ Group.IsSolvable (MulAut ↥V) := by
    intro hs
    obtain ⟨e⟩ := Work.Hering.Step5.iso_fin3 hcard (fun x => Subtype.ext (hexp x x.2))
    haveI : Group.IsSolvable (MulAut ↥V) := hs
    have : Group.IsSolvable (MulAut (Multiplicative (Fin 3 → ZMod 2))) :=
      Group.isSolvable_of_surjective (f := (MulAut.congr e).toMonoidHom)
        (MulAut.congr e).surjective
    exact Work.Hering.GL32.gl32_not_solvable_v2 this
  -- the conjugation hom `G →* MulAut ↥V` is surjective, by `hAut`
  have hθsurj : Function.Surjective (MulAut.conjNormal (H := V)) := by
    intro φ
    obtain ⟨g, hg⟩ := hAut φ
    refine ⟨g, ?_⟩
    ext v
    rw [MulAut.conjNormal_apply]
    exact (congrArg Subtype.val (hg v)).symm
  -- `ker ψ ≤ ker θ`, because `V ≤ D`: an automorphism of `D` that is trivial on `D`
  -- is trivial on `V`
  have hker : MonoidHom.ker (MulAut.conjNormal (H := D)) ≤
      MonoidHom.ker (MulAut.conjNormal (H := V)) := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    ext v
    have h1 : (g : G) * (v : G) * g⁻¹ = (v : G) := by
      have h3 : MulAut.conjNormal (H := D) g ⟨(v : G), hVD v.2⟩ = ⟨(v : G), hVD v.2⟩ := by
        rw [hg]; rfl
      calc (g : G) * (v : G) * g⁻¹
          = ((MulAut.conjNormal (H := D) g ⟨(v : G), hVD v.2⟩ : ↥D) : G) :=
              (MulAut.conjNormal_apply g ⟨(v : G), hVD v.2⟩).symm
        _ = (v : G) := by rw [h3]
    rw [MulAut.conjNormal_apply]
    exact h1
  -- `ψ.range ≅ G ⧸ ker ψ` is solvable, because `ψ.range ≤ MulAut ↥D` is
  haveI : Group.IsSolvable (MulAut ↥D) := hsol
  haveI hq : Group.IsSolvable (G ⧸ MonoidHom.ker (MulAut.conjNormal (H := D))) :=
    Group.isSolvable_of_surjective
      (f := (QuotientGroup.quotientKerEquivRange (MulAut.conjNormal (H := D))).symm.toMonoidHom)
      (QuotientGroup.quotientKerEquivRange (MulAut.conjNormal (H := D))).symm.surjective
  -- `θ` descends to a surjection `G ⧸ ker ψ →* MulAut ↥V`
  have hlift : Function.Surjective
      (QuotientGroup.lift (MonoidHom.ker (MulAut.conjNormal (H := D)))
        (MulAut.conjNormal (H := V)) hker) := by
    intro φ
    obtain ⟨g, hg⟩ := hθsurj φ
    exact ⟨QuotientGroup.mk g, by rw [QuotientGroup.lift_mk]; exact hg⟩
  -- hence `MulAut ↥V` is solvable, contradicting `hVns`
  exact hVns (Group.isSolvable_of_surjective
    (f := QuotientGroup.lift (MonoidHom.ker (MulAut.conjNormal (H := D)))
      (MulAut.conjNormal (H := V)) hker)
    hlift)

end Work.Hering.HardCore
