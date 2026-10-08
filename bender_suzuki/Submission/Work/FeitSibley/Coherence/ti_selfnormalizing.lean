import Submission.Work.FeitSibley.Coherence.engine
import Submission.Work.BrauerSuzuki.TI.cfInner_indFun_eq_of_TISet

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Coherence for a T.I. subgroup equal to its own normalizer

Let `H ≤ G` be a T.I. subgroup with `N_G(H) = H` (a **self-normalizing** T.I. subgroup: distinct
conjugates of `H` intersect trivially).  Then *every* orthonormal set of irreducible characters
of `H` is coherent for `Ind_H^G`.

The extension of `Ind_H^G` to `ℤ[S]` is the **Dade shift**

`dade H χ = Ind_H^G (χ - χ(1)·1_H) + χ(1)·1_G = Ind_H^G χ + χ(1)·a`,

with the *single* vector `a = 1_G - Ind_H^G 1_H` (exactly the shape required by
`Work.FeitSibley.Coherence.coherent_of_linearShift`).  The two ingredients are

* `dade H χ` is a virtual character of `G` whenever `χ ∈ Irr H`;
* `⟨dade θ, dade ψ⟩ = ⟨θ, ψ⟩`, which reduces to the Brauer–Suzuki/Dade isometry
  `⟨Ind α, Ind β⟩ = ⟨α, β⟩` for degree-zero class functions `α, β` on `H`
  (`Work.BrauerSuzuki.TI.cfInner_indFun_eq_of_TISet`, applied to the TI set `H \ {1}`).

Since `dade H χ - Ind χ = χ(1)·a` is a multiple of the degree, the shift agrees with `Ind_H^G`
on `ℤ[S]°`; since `⟨dade θ, dade ψ⟩ = ⟨θ, ψ⟩` it is an isometry of `ℤ[S]`.  Hence `S` is
coherent.

## Application

For `FSData` with `D = ⊥` one has `H = Q`, and `Q` is a T.I. subgroup with `N_G(Q) = H = Q`.
This settles the case `D = ⊥` of `Work.FeitSibley.Coherence.coherent_scriptS`, which is outside
the range of Peterfalvi II App. XII (there `D ≠ 1`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

open Classical

namespace Work.FeitSibley.Coherence

open Work.Coherence

variable {G : Type} [Group G] [Fintype G]

section TI

variable {H : Subgroup G}

/-- The principal character is a class function. -/
theorem isClassFun_one' (G : Type) [Group G] : Work.Coherence.IsClassFun (1 : G → ℂ) :=
  fun _ _ => rfl

/-- `H \ {1}` is a T.I. set with normalizer `H`, for a nontrivial T.I. subgroup `H`. -/
theorem isTISet_compl_one (hbot : H ≠ ⊥)
    (hTI : ∀ g : G, g ∉ H → H ⊓ Submission.Blueprint.conj g H = ⊥) :
    Work.BrauerSuzuki.IsTISet {x : G | x ∈ H ∧ x ≠ 1} H := by
  classical
  refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact hx.1
  · intro x hx
    exact ⟨H.inv_mem hx.1, inv_ne_one.mpr hx.2⟩
  · intro h hh x hx
    refine ⟨H.mul_mem (H.mul_mem hh hx.1) (H.inv_mem hh), ?_⟩
    intro hcon
    have hx1 : x = 1 := by
      have h2 : h * x = h * 1 := by
        rw [mul_one]
        exact mul_inv_eq_one.mp hcon
      exact mul_left_cancel h2
    exact hx.2 hx1
  · intro g hg
    by_contra hgH
    haveI : Nontrivial H := (Subgroup.nontrivial_iff_ne_bot H).mpr hbot
    obtain ⟨h, hh1⟩ := exists_ne (1 : H)
    have hmem_set : (h : G) ∈ {x : G | x ∈ H ∧ x ≠ 1} :=
      ⟨h.2, fun hc => hh1 (Subtype.ext hc)⟩
    obtain ⟨hmem, hne⟩ := hg (x := (h : G)) hmem_set
    have h1 : g * (h : G) * g⁻¹ ∈ H ⊓ Submission.Blueprint.conj g H :=
      ⟨hmem, Subgroup.mem_map.mpr ⟨(h : G), h.2, by simp [MulAut.conj_apply]⟩⟩
    rw [hTI g hgH, Subgroup.mem_bot] at h1
    exact hne h1
  · intro g hgH x y hx hy hconj
    have hybot : y ∈ H ⊓ Submission.Blueprint.conj g H :=
      ⟨hy.1, Subgroup.mem_map.mpr ⟨x, hx.1,
        by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; exact hconj⟩⟩
    rw [hTI g hgH, Subgroup.mem_bot] at hybot
    exact hy.2 hybot

/-- **The Dade/Brauer–Suzuki isometry** for degree-zero class functions of a nontrivial T.I.
subgroup: induction `Ind_H^G` preserves the character inner product on class functions of `H`
vanishing at `1`. -/
theorem cfInner_indFun_eq_of_degree_zero (hbot : H ≠ ⊥)
    (hTI : ∀ g : G, g ∉ H → H ⊓ Submission.Blueprint.conj g H = ⊥)
    {α β : H → ℂ} (hαc : Work.CharCore.IsClassFun α) (hβc : Work.CharCore.IsClassFun β)
    (hα : α 1 = 0) (hβ : β 1 = 0) :
    cfInner (Work.Induction.indFun H α) (Work.Induction.indFun H β) = cfInner α β := by
  refine Work.BrauerSuzuki.TI.cfInner_indFun_eq_of_TISet (isTISet_compl_one hbot hTI) hαc hβc
    (fun h hh => ?_) (fun h hh => ?_)
  · by_cases hone : (h : G) = 1
    · rw [show h = 1 from Subtype.ext hone, hα]
    · exact absurd ⟨h.2, hone⟩ hh
  · by_cases hone : (h : G) = 1
    · rw [show h = 1 from Subtype.ext hone, hβ]
    · exact absurd ⟨h.2, hone⟩ hh

/-- The **Dade shift** of `Ind_H^G`: `χ ↦ Ind_H^G (χ - χ(1)·1_H) + χ(1)·1_G`. -/
def dade (H : Subgroup G) (χ : H → ℂ) : G → ℂ :=
  Work.Induction.indFun H (χ - (χ 1) • (1 : H → ℂ)) + (χ 1) • (1 : G → ℂ)

/-- The Dade shift is a shift of `Ind_H^G` by the single vector `a = 1_G - Ind_H^G 1_H`. -/
theorem dade_eq_linearShift (χ : H → ℂ) :
    Work.FeitSibley.indLin H χ
        + (χ 1) • ((1 : G → ℂ) - Work.FeitSibley.indLin H (1 : H → ℂ))
      = dade H χ := by
  rw [Work.FeitSibley.indLin_apply, Work.FeitSibley.indLin_apply, dade]
  have hsub : Work.Induction.indFun H (χ - (χ 1) • (1 : H → ℂ))
      = Work.Induction.indFun H χ - (χ 1) • Work.Induction.indFun H (1 : H → ℂ) := by
    rw [Work.Induction.indFun_sub, Work.Induction.indFun_smul]
  rw [hsub, smul_sub]
  abel

/-- The Dade shift of an irreducible character of `H` is a virtual character of `G`. -/
theorem isVChar_dade {χ : H → ℂ} (hχ : χ ∈ Work.CharCore.Irr H) :
    Work.Coherence.IsVChar (dade H χ) := by
  classical
  have hχv : Work.CharCore.IsVChar χ := Work.CharCore.IsVChar.of_mem_Irr hχ
  have h1H : Work.CharCore.IsVChar (1 : H → ℂ) :=
    Work.CharCore.IsVChar.of_mem_Irr Work.CharCore.principalChar_mem_Irr
  have hdeg : χ 1 = (Work.CharCore.irrDeg χ : ℂ) := Work.CharCore.irrDeg_spec hχ
  have hsub : Work.CharCore.IsVChar (χ - (χ 1) • (1 : H → ℂ)) := by
    have hsm : Work.CharCore.IsVChar ((χ 1) • (1 : H → ℂ)) := by
      rw [hdeg, Nat.cast_smul_eq_nsmul]
      exact AddSubgroup.nsmul_mem _ h1H _
    exact hχv.sub hsm
  have hind : Work.CharCore.IsVChar (Work.Induction.indFun H (χ - (χ 1) • (1 : H → ℂ))) :=
    Work.Induction.isVChar_indFun hsub
  have h1G : Work.CharCore.IsVChar (1 : G → ℂ) :=
    Work.CharCore.IsVChar.of_mem_Irr Work.CharCore.principalChar_mem_Irr
  have hsm : Work.CharCore.IsVChar ((χ 1) • (1 : G → ℂ)) := by
    rw [hdeg, Nat.cast_smul_eq_nsmul]
    exact AddSubgroup.nsmul_mem _ h1G _
  rw [dade]
  exact (Work.CharCore.IsVChar_iff_coherence _).mp (hind.add hsm)

/-- **The Dade shift is an isometry** on the class functions spanned by `Irr H`, for a nontrivial
self-normalizing T.I. subgroup `H`. -/
theorem cfInner_dade_eq (hbot : H ≠ ⊥)
    (hTI : ∀ g : G, g ∉ H → H ⊓ Submission.Blueprint.conj g H = ⊥)
    {θ ψ : H → ℂ} (hθ : θ ∈ Work.CharCore.Irr H) (hψ : ψ ∈ Work.CharCore.Irr H) :
    cfInner (dade H θ) (dade H ψ) = cfInner θ ψ := by
  classical
  set α : H → ℂ := θ - (θ 1) • (1 : H → ℂ) with hαdef
  set β : H → ℂ := ψ - (ψ 1) • (1 : H → ℂ) with hβdef
  have hθc : Work.CharCore.IsClassFun θ :=
    Work.Coherence.isClassFun_of_mem_Irr ((Work.CharCore.mem_Irr_iff_coherence).mp hθ)
  have hψc : Work.CharCore.IsClassFun ψ :=
    Work.Coherence.isClassFun_of_mem_Irr ((Work.CharCore.mem_Irr_iff_coherence).mp hψ)
  have hαc : Work.CharCore.IsClassFun α :=
    (Work.CharCore.IsClassFun_iff_coherence α).mpr
      (hθc.sub (IsClassFun.smul (θ 1) (isClassFun_one' H)))
  have hβc : Work.CharCore.IsClassFun β :=
    (Work.CharCore.IsClassFun_iff_coherence β).mpr
      (hψc.sub (IsClassFun.smul (ψ 1) (isClassFun_one' H)))
  have hα1 : α 1 = 0 := by simp [hαdef]
  have hβ1 : β 1 = 0 := by simp [hβdef]
  have hθsplit : θ = α + (θ 1) • (1 : H → ℂ) := by rw [hαdef]; abel
  have hψsplit : ψ = β + (ψ 1) • (1 : H → ℂ) := by rw [hβdef]; abel
  have hVs : dade H θ = Work.Induction.indFun H α + (θ 1) • (1 : G → ℂ) := rfl
  have hWs : dade H ψ = Work.Induction.indFun H β + (ψ 1) • (1 : G → ℂ) := rfl
  have hDade : cfInner (Work.Induction.indFun H α) (Work.Induction.indFun H β) = cfInner α β :=
    cfInner_indFun_eq_of_degree_zero hbot hTI hαc hβc hα1 hβ1
  have hrecα : cfInner (Work.Induction.indFun H α) (1 : G → ℂ) = cfInner α (1 : H → ℂ) :=
    Work.Induction.frobenius_reciprocity H α (1 : G → ℂ) (isClassFun_one' G)
  have hrecβ : cfInner (1 : G → ℂ) (Work.Induction.indFun H β) = cfInner (1 : H → ℂ) β := by
    have h1 : cfInner (1 : G → ℂ) (Work.Induction.indFun H β)
        = (starRingEnd ℂ) (cfInner (Work.Induction.indFun H β) (1 : G → ℂ)) :=
      cfInner_conj_symm _ _
    have h2 : (starRingEnd ℂ) (cfInner (Work.Induction.indFun H β) (1 : G → ℂ))
        = (starRingEnd ℂ) (cfInner β (1 : H → ℂ)) := by
      rw [show cfInner (Work.Induction.indFun H β) (1 : G → ℂ) = cfInner β (1 : H → ℂ) from
        Work.Induction.frobenius_reciprocity H β (1 : G → ℂ) (isClassFun_one' G)]
    have h3 : (starRingEnd ℂ) (cfInner β (1 : H → ℂ)) = cfInner (1 : H → ℂ) β := by
      rw [cfInner_conj_symm β (1 : H → ℂ)]
      simp
    exact h1.trans (h2.trans h3)
  have honeG : cfInner (1 : G → ℂ) (1 : G → ℂ) = 1 := by simp [cfInner]
  have honeH : cfInner (1 : H → ℂ) (1 : H → ℂ) = 1 := by simp [cfInner]
  rw [hVs, hWs, hθsplit, hψsplit]
  simp only [cfInner_add_left, cfInner_add_right, cfInner_smul_left, cfInner_smul_right]
  rw [hDade, hrecα, hrecβ, honeG, honeH]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.one_apply, mul_one, hα1, hβ1,
    zero_add]

end TI

section Main

variable {H : Subgroup G}

/-- **Coherence of any orthonormal set of `Irr H` for a self-normalizing T.I. subgroup `H`.**
The extension of `Ind_H^G` is the Dade shift `χ ↦ dade H χ`, i.e. the shift of `Ind_H^G` by
`1_G - Ind_H^G 1_H`. -/
theorem coherent_of_ti_selfNormalizing (hbot : H ≠ ⊥)
    (hTI : ∀ g : G, g ∉ H → H ⊓ Submission.Blueprint.conj g H = ⊥)
    (S : Finset (H → ℂ)) (hS : S ⊆ Work.CharCore.Irr H) :
    Work.Coherence.Coherent S (Work.FeitSibley.indLin H) := by
  classical
  refine Work.FeitSibley.Coherence.coherent_of_linearShift (τ := Work.FeitSibley.indLin H)
    (a := (1 : G → ℂ) - Work.FeitSibley.indLin H (1 : H → ℂ)) ?_ ?_ ?_
  · exact Work.Coherence.irr_orthonormal_finset
      (fun x hx => (Work.CharCore.mem_Irr_iff_coherence).mp (hS hx))
  · intro χ hχ
    rw [dade_eq_linearShift]
    exact isVChar_dade (hS hχ)
  · intro χ hχ ψ hψ
    rw [dade_eq_linearShift χ, dade_eq_linearShift ψ]
    exact cfInner_dade_eq hbot hTI (hS hχ) (hS hψ)

end Main

end Work.FeitSibley.Coherence
