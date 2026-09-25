import Mathlib
import Submission.Work.ShafarevichKoch.exists_H2Infl_with_kernel
import Submission.Work.ShafarevichKoch.zmodTwoInstances
import Submission.Work.ShafarevichKoch.ZModTwoTrivialAction
import Submission.Work.ShafarevichKoch.exists_openNormal_factorization_of_locallyConstant

/-!
# `Work.ShafarevichKoch.exists_factored_of_mem_H2Infl_kernel`

The **kernel of the inflation in degree `2`, in factored form**.  Let `Γ` be a profinite group
(here: a compact, Hausdorff, totally disconnected topological group), `U : OpenNormalSubgroup Γ` and
`z : Z²(Γ ⧸ U, 𝔽₂)`.  If the class of `z` dies under the inflation
`inf : H²(Γ ⧸ U, 𝔽₂) → H²(Γ, 𝔽₂)`

`Work.ShafarevichKoch.H2Infl U hcomp (H2.mk z) = 0`,

then `z` is a **coboundary already on a smaller open quotient**: there is an open normal subgroup
`U' ≤ U` and a `1`-cochain `f'` of `Γ ⧸ U'` such that

`z (σ U, τ U) = d¹ f' (σ, τ)   for all σ, τ : Γ`,

where the right hand side is computed in `Γ` (through the quotient map `Γ → Γ ⧸ U'`).

Two ingredients are used, both already in the workspace:

* `Work.ShafarevichKoch.exists_H2Infl_with_kernel` — the kernel of the inflation consists exactly of
  the classes of the cocycles that become coboundaries after pullback, i.e. that are the
  differential of *some* locally constant `1`-cochain `g : Γ → 𝔽₂`;
* `Work.ShafarevichKoch.exists_openNormal_factorization_of_locallyConstant` — a locally constant
  function on `Γ` (with discrete target) factors through the quotient by an open normal subgroup
  `U₀`; replacing `U₀` by `U ⊓ U₀` puts the factorization on a subgroup of `U`.

The coefficients `𝔽₂` matter only through `hcomp`, the compatibility of the (necessarily trivial)
actions of `Γ` and `Γ ⧸ U` on `𝔽₂`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Work.ConCohomology

namespace Work.ShafarevichKoch

theorem exists_factored_of_mem_H2Infl_kernel
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ]
    [TotallyDisconnectedSpace Γ]
    (U : OpenNormalSubgroup Γ) (z : Work.ConCohomology.Z2 (Γ ⧸ U.toSubgroup) (ZMod 2))
    (hker : Work.ShafarevichKoch.H2Infl U
        (fun σ m => (Work.ShafarevichKoch.smul_zmodTwo_eq σ m).trans
          (Work.ShafarevichKoch.smul_zmodTwo_eq (QuotientGroup.mk' U.toSubgroup σ) m).symm)
        (Work.ConCohomology.H2.mk z) = 0) :
    ∃ U' : OpenNormalSubgroup Γ, U' ≤ U ∧
      ∃ f' : Work.ConCohomology.Cochain1 (Γ ⧸ U'.toSubgroup) (ZMod 2),
        ∀ p : Γ × Γ,
          (z : Work.ConCohomology.Cochain2 (Γ ⧸ U.toSubgroup) (ZMod 2))
              (QuotientGroup.mk' U.toSubgroup p.1, QuotientGroup.mk' U.toSubgroup p.2)
            = Work.ConCohomology.d1Fun (G := Γ)
                (fun σ : Γ => (f' : (Γ ⧸ U'.toSubgroup) → ZMod 2)
                  (QuotientGroup.mk' U'.toSubgroup σ)) p := by
  -- the compatibility of the (trivial) actions of `Γ` and `Γ ⧸ U` on `𝔽₂`
  have hcomp : ∀ (σ : Γ) (m : ZMod 2),
      σ • m = (QuotientGroup.mk' U.toSubgroup σ) • m :=
    fun σ m => (Work.ShafarevichKoch.smul_zmodTwo_eq σ m).trans
      (Work.ShafarevichKoch.smul_zmodTwo_eq (QuotientGroup.mk' U.toSubgroup σ) m).symm
  -- the class of `z` dies under inflation, i.e. the pullback `Z2Infl U hcomp z` is a coboundary
  have hz : Work.ShafarevichKoch.Z2Infl U hcomp z ∈ Work.ConCohomology.B2' Γ (ZMod 2) := by
    rw [← Work.ConCohomology.H2.mk_eq_zero_iff]
    rw [← Work.ShafarevichKoch.H2Infl_mk U hcomp z]
    exact hker
  obtain ⟨g, hg⟩ := (Work.ConCohomology.mem_B2 (G := Γ) (M := ZMod 2)).mp
    ((Work.ConCohomology.mem_B2' (G := Γ) (M := ZMod 2)).mp hz)
  -- `d¹ g` computes the pullback of `z`, i.e. `z (σ U, τ U) = d¹ g (σ, τ)`
  have hgexp : ∀ p : Γ × Γ,
      Work.ConCohomology.d1Fun (g : Γ → ZMod 2) p
        = (z : Work.ConCohomology.Cochain2 (Γ ⧸ U.toSubgroup) (ZMod 2))
            (QuotientGroup.mk' U.toSubgroup p.1, QuotientGroup.mk' U.toSubgroup p.2) := by
    intro p
    have h := DFunLike.congr_fun hg p
    simp only [Work.ShafarevichKoch.Z2Infl_coe,
      Work.ShafarevichKoch.cochain2Infl_apply] at h
    exact h
  -- `g` is locally constant, hence factors through an open normal subgroup `U₀`
  obtain ⟨U₀, h₀, hfac⟩ :=
    Work.ShafarevichKoch.exists_openNormal_factorization_of_locallyConstant
      (g : LocallyConstant Γ (ZMod 2))
  -- shrink `U₀` to `U' = U ⊓ U₀ ≤ U`
  set U' : OpenNormalSubgroup Γ := U ⊓ U₀ with hU'def
  have hle : U' ≤ U := inf_le_left
  have hle₀ : U' ≤ U₀ := inf_le_right
  let q : Γ ⧸ U'.toSubgroup →* Γ ⧸ U₀.toSubgroup :=
    QuotientGroup.map U'.toSubgroup U₀.toSubgroup (MonoidHom.id Γ) (fun x hx => hle₀ hx)
  -- the factorization of `g` through `Γ ⧸ U'` is `h₀` precomposed with the projection
  let φ : Γ ⧸ U'.toSubgroup → ZMod 2 := fun qq => h₀ (q qq)
  have hq : ∀ σ : Γ, q (QuotientGroup.mk' U'.toSubgroup σ)
      = QuotientGroup.mk' U₀.toSubgroup σ :=
    fun σ => QuotientGroup.map_mk' U'.toSubgroup U₀.toSubgroup (MonoidHom.id Γ) _ σ
  have hφ : ∀ σ : Γ, φ (QuotientGroup.mk' U'.toSubgroup σ) = (g : Γ → ZMod 2) σ := by
    intro σ
    show h₀ (q (QuotientGroup.mk' U'.toSubgroup σ)) = (g : Γ → ZMod 2) σ
    rw [hq σ]
    exact (hfac σ).symm
  -- `Γ ⧸ U'` is discrete (as `U'` is open in the compact group `Γ`), so `φ` is locally constant
  haveI : DiscreteTopology (Γ ⧸ U'.toSubgroup) := QuotientGroup.discreteTopology U'.isOpen'
  let f' : Work.ConCohomology.Cochain1 (Γ ⧸ U'.toSubgroup) (ZMod 2) :=
    ⟨φ, IsLocallyConstant.of_discrete φ⟩
  have hf' : ∀ σ : Γ, (f' : (Γ ⧸ U'.toSubgroup) → ZMod 2)
      (QuotientGroup.mk' U'.toSubgroup σ) = (g : Γ → ZMod 2) σ := fun σ => hφ σ
  refine ⟨U', hle, f', ?_⟩
  intro p
  -- `d¹` of the factored cochain is `d¹ g` in degree `2`
  have key : Work.ConCohomology.d1Fun (G := Γ)
      (fun σ : Γ => (f' : (Γ ⧸ U'.toSubgroup) → ZMod 2)
        (QuotientGroup.mk' U'.toSubgroup σ)) p =
      Work.ConCohomology.d1Fun (g : Γ → ZMod 2) p := by
    obtain ⟨σ, τ⟩ := p
    simp only [Work.ConCohomology.d1Fun_apply]
    rw [hf' τ, hf' (σ * τ), hf' σ]
  rw [key, hgexp p]

end Work.ShafarevichKoch
