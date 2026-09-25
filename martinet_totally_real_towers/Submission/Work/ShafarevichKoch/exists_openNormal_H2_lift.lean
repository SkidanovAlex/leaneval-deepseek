import Mathlib
import Submission.Work.ShafarevichKoch.exists_H2Infl_with_kernel
import Submission.Work.ShafarevichKoch.zmodTwoInstances
import Submission.Work.ShafarevichKoch.ZModTwoTrivialAction
import Submission.Work.ShafarevichKoch.exists_openNormal_factorization_of_locallyConstant

/-!
# `Work.ShafarevichKoch.exists_openNormal_H2_lift`

Every class in `H²(Γ, 𝔽₂)` of a profinite group `Γ` is inflated from a finite quotient:
there is an open normal subgroup `U ≤ Γ` and a class `y ∈ H²(Γ ⧸ U, 𝔽₂)` with
`inf y = x`.

The proof is the standard "continuity means factorisation through a finite quotient"
argument for profinite cohomology with discrete coefficients: a (locally constant) `2`-cocycle
on `Γ` is constant on the cosets of `V × V` for some open normal subgroup `V ≤ Γ`
(`exists_openNormal_factorization_prod` below, obtained by applying the one-variable
factorisation theorem to the group `Γ × Γ` and cutting `V` down to a product of open
subgroups of `Γ`), and the induced function on `(Γ ⧸ V) × (Γ ⧸ V)` is a `2`-cocycle there
(`exists_Z2_factorization`).
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

noncomputable section

open Work.ConCohomology

namespace Work.ShafarevichKoch

/-- **Two-variable factorisation of a locally constant function through a finite quotient.**
If `f : Γ × Γ → M` is locally constant, then `f` is constant on each `U`-coset pair for some
open normal subgroup `U ≤ Γ`, i.e. `f (σ, τ) = g (σ̄, τ̄)` for a function `g` on `Γ ⧸ U × Γ ⧸ U`.

The subgroup is obtained by applying `exists_openNormal_factorization_of_locallyConstant` to the
group `Γ × Γ` and then intersecting the resulting open normal subgroup `V ≤ Γ × Γ` with
`{u | (u, 1) ∈ V} × {v | (1, v) ∈ V}`. -/
theorem exists_openNormal_factorization_prod
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [T2Space Γ] [TotallyDisconnectedSpace Γ]
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M]
    (f : LocallyConstant (Γ × Γ) M) :
    ∃ U : OpenNormalSubgroup Γ, ∃ g : (Γ ⧸ U.toSubgroup) × (Γ ⧸ U.toSubgroup) → M,
      ∀ σ τ : Γ, f (σ, τ) = g (QuotientGroup.mk' U.toSubgroup σ, QuotientGroup.mk' U.toSubgroup τ) := by
  obtain ⟨V, gV, hgV⟩ :=
    exists_openNormal_factorization_of_locallyConstant (Γ := Γ × Γ) f
  have hper : ∀ (p q : Γ × Γ), q ∈ (V : Set (Γ × Γ)) → f (p * q) = f p := by
    intro p q hq
    rw [hgV (p * q), hgV p, map_mul]
    have hq1 : QuotientGroup.mk' V.toSubgroup q = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hq
    rw [hq1, mul_one]
  let A : Subgroup Γ := (V.toSubgroup).comap (MonoidHom.inl Γ Γ)
  let B : Subgroup Γ := (V.toSubgroup).comap (MonoidHom.inr Γ Γ)
  have hAopen : IsOpen (A : Set Γ) := by
    have hcont : Continuous fun u : Γ => (u, (1 : Γ)) := continuous_id.prodMk continuous_const
    have : (A : Set Γ) = (fun u : Γ => (u, (1 : Γ))) ⁻¹' (V : Set (Γ × Γ)) := rfl
    rw [this]
    exact hcont.isOpen_preimage _ V.isOpen'
  have hBopen : IsOpen (B : Set Γ) := by
    have hcont : Continuous fun u : Γ => ((1 : Γ), u) := continuous_const.prodMk continuous_id
    have : (B : Set Γ) = (fun u : Γ => ((1 : Γ), u)) ⁻¹' (V : Set (Γ × Γ)) := rfl
    rw [this]
    exact hcont.isOpen_preimage _ V.isOpen'
  have hU₀open : IsOpen ((A ⊓ B : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.coe_inf]
    exact hAopen.inter hBopen
  have hqfin : Finite (Γ ⧸ (A ⊓ B : Subgroup Γ)) :=
    Subgroup.quotient_finite_of_isOpen (A ⊓ B) hU₀open
  have hU₀fin : (A ⊓ B : Subgroup Γ).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  let U : OpenNormalSubgroup Γ :=
    { toSubgroup := (A ⊓ B).normalCore
      isOpen' := Subgroup.isOpen_of_isClosed_of_finiteIndex (A ⊓ B).normalCore
        ((A ⊓ B).normalCore_isClosed (Subgroup.isClosed_of_isOpen (A ⊓ B) hU₀open))
      isNormal' := (A ⊓ B).normalCore_normal }
  have hUV : ∀ u v : Γ, u ∈ U.toSubgroup → v ∈ U.toSubgroup →
      (u, v) ∈ (V : Subgroup (Γ × Γ)) := by
    intro u v hu hv
    have huAB : u ∈ A ⊓ B := (A ⊓ B).normalCore_le hu
    have hvAB : v ∈ A ⊓ B := (A ⊓ B).normalCore_le hv
    have huA : u ∈ A := (Subgroup.mem_inf.mp huAB).1
    have hvB : v ∈ B := (Subgroup.mem_inf.mp hvAB).2
    have h1 : (u, 1) ∈ (V : Subgroup (Γ × Γ)) := huA
    have h2 : (1, v) ∈ (V : Subgroup (Γ × Γ)) := hvB
    have h3 : (u, 1) * (1, v) ∈ (V : Subgroup (Γ × Γ)) := mul_mem h1 h2
    simpa using h3
  have hstar : ∀ (σ τ u v : Γ), u ∈ U.toSubgroup → v ∈ U.toSubgroup →
      f (σ * u, τ * v) = f (σ, τ) := by
    intro σ τ u v hu hv
    have hq : (u, v) ∈ (V : Set (Γ × Γ)) := hUV u v hu hv
    have := hper (σ, τ) (u, v) hq
    simpa using this
  have hrel : ∀ σ : Γ, ∃ z ∈ U.toSubgroup,
      Quotient.out (QuotientGroup.mk' U.toSubgroup σ) * z = σ := by
    intro σ
    have h := Quotient.out_eq (QuotientGroup.mk' U.toSubgroup σ)
    have h2 : QuotientGroup.mk' U.toSubgroup
        (Quotient.out (QuotientGroup.mk' U.toSubgroup σ))
        = QuotientGroup.mk' U.toSubgroup σ := h
    exact (QuotientGroup.mk'_eq_mk' U.toSubgroup).mp h2
  refine ⟨U, fun q => f (Quotient.out q.1, Quotient.out q.2), ?_⟩
  intro σ τ
  show f (σ, τ) = f (Quotient.out (QuotientGroup.mk' U.toSubgroup σ),
      Quotient.out (QuotientGroup.mk' U.toSubgroup τ))
  obtain ⟨z₁, hz₁U, hz₁⟩ := hrel σ
  obtain ⟨z₂, hz₂U, hz₂⟩ := hrel τ
  have e1 : Quotient.out (QuotientGroup.mk' U.toSubgroup σ) = σ * z₁⁻¹ :=
    eq_mul_inv_of_mul_eq hz₁
  have e2 : Quotient.out (QuotientGroup.mk' U.toSubgroup τ) = τ * z₂⁻¹ :=
    eq_mul_inv_of_mul_eq hz₂
  rw [e1, e2]
  exact (hstar σ τ z₁⁻¹ z₂⁻¹ (inv_mem hz₁U) (inv_mem hz₂U)).symm

/-- **A `2`-cocycle with values in `𝔽₂` on a profinite group is inflated from a finite
quotient**: there is an open normal subgroup `U` and a `2`-cocycle `z'` on `Γ ⧸ U` whose
cochain inflation is `z`. -/
theorem exists_Z2_inflation_factorization
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [T2Space Γ] [TotallyDisconnectedSpace Γ]
    (z : Z2 Γ (ZMod 2)) :
    ∃ U : OpenNormalSubgroup Γ, ∃ z' : Z2 (Γ ⧸ U.toSubgroup) (ZMod 2),
      cochain2Infl U (z' : Cochain2 (Γ ⧸ U.toSubgroup) (ZMod 2)) =
        (z : Cochain2 Γ (ZMod 2)) := by
  obtain ⟨U, g, hg⟩ :=
    exists_openNormal_factorization_prod (Γ := Γ) (f := (z : Cochain2 Γ (ZMod 2)))
  have hcoc : IsCocycle2 (g : (Γ ⧸ U.toSubgroup) × (Γ ⧸ U.toSubgroup) → ZMod 2) := by
    intro σ τ ρ
    obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup σ
    obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup τ
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective U.toSubgroup ρ
    have key := mem_Z2.mp z.2 s t r
    rw [smul_zmodTwo_eq] at key
    simp only [smul_zmodTwo_eq, ← map_mul]
    rw [← hg t r, ← hg (s * t) r, ← hg s (t * r), ← hg s t]
    exact key
  refine ⟨U, ⟨⟨g, IsLocallyConstant.of_discrete g⟩, ?_⟩, ?_⟩
  · rw [mem_Z2]
    exact hcoc
  · refine LocallyConstant.ext fun p => ?_
    obtain ⟨σ, τ⟩ := p
    rw [cochain2Infl_apply]
    show g (QuotientGroup.mk' U.toSubgroup σ, QuotientGroup.mk' U.toSubgroup τ)
      = (z : Cochain2 Γ (ZMod 2)) (σ, τ)
    exact (hg σ τ).symm

theorem exists_openNormal_H2_lift
    {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    [T2Space Γ] [TotallyDisconnectedSpace Γ]
    (x : Work.ConCohomology.H2 Γ (ZMod 2)) :
    ∃ U : OpenNormalSubgroup Γ, ∃ y : Work.ConCohomology.H2 (Γ ⧸ U.toSubgroup) (ZMod 2),
      Work.ShafarevichKoch.H2Infl U
        (fun σ m => (Work.ShafarevichKoch.smul_zmodTwo_eq σ m).trans
          (Work.ShafarevichKoch.smul_zmodTwo_eq (QuotientGroup.mk' U.toSubgroup σ) m).symm) y = x := by
  obtain ⟨z, hz⟩ := QuotientAddGroup.mk_surjective x
  obtain ⟨U, z', hz'⟩ := exists_Z2_inflation_factorization z
  refine ⟨U, H2.mk z', ?_⟩
  rw [H2Infl_mk]
  have hcomp : ∀ (σ : Γ) (m : ZMod 2),
      σ • m = (QuotientGroup.mk' U.toSubgroup σ) • m :=
    fun σ m => (smul_zmodTwo_eq σ m).trans
      (smul_zmodTwo_eq (QuotientGroup.mk' U.toSubgroup σ) m).symm
  have hzZ : Z2Infl U hcomp z' = z := by
    refine Subtype.ext ?_
    rw [Z2Infl_coe]
    exact hz'
  rw [hzZ]
  exact hz

end Work.ShafarevichKoch
