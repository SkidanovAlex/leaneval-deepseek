import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.sconjLam
import Submission.Work.BG.Lambda
import Submission.Work.BG.s02_quotCyclic
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.units_sq_eq_one_eq_one_or_eq_neg_one

/-!
# Area BG: an `s`-fixed member of `Λ` is `-1` at `t₁t₂`

Bender–Glauberman 1981, §2.  Let `C` be a §2 context compatible with the data `D` of
Hypothesis 1.1 (`H₀ = U ⊔ S₀`, `U = D.U`, `H = D.H`, `t = D.t`, `s = D.t₁`) and let
`β : H₀/U →* ℂˣ` be a non-trivial linear character whose inflation `λ_β = lamCF C β` is
fixed by the action `ν ↦ ν^s` of `s = t₁` on `CF(H₀)` (BG Lemma 2.1(b) computes
`λ_β^s = λ_{β⁻¹}`).

**Claim.** `λ_β(t₁t₂) = -1`.

The mathematics is the paper's "reflection character" computation: `λ_β^s = λ_β` forces
`β = β⁻¹`, i.e. `β` has order two; since `t₁t₂` generates the cyclic `2`-group
`S₀ = ⟨t₁t₂⟩` and `H₀/U = (U S₀)/U` is the image of `S₀` (every `x ∈ H₀ = U·S₀` is `u s`
with `s ∈ S₀`, so `xU = sU`), the class of `t₁t₂` generates `H₀/U`; as `β ≠ 1` it cannot
vanish there, so `β(t₁t₂U) = ±1` is `-1`.

The auxiliary lemmas below record the two ingredients (the decomposition `H₀ = U·S₀`,
needed for the surjectivity of `S₀ → H₀/U`, and Lemma 2.1(b)) for reuse.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Subgroup

variable {G : Type} [Group G] [Finite G]

namespace LamCFFixed

/-! ## The decomposition `H₀ = U · S₀` -/

/-- `S₀ ≤ H₀`: `H₀ = U ⊔ S₀` by compatibility. -/
theorem S0_le_H0 (D : Work.GW2.BGData G) (C : Sec2Ctx G)
    (hC : Work.GW2.C16.Compat D C) : D.S0 ≤ C.P.H0 := by
  rw [hC.H0_eq]
  exact le_sup_right

/-- `U ≤ H₀`: `H₀ = U ⊔ S₀` by compatibility. -/
theorem U_le_H0 (D : Work.GW2.BGData G) (C : Sec2Ctx G)
    (hC : Work.GW2.C16.Compat D C) : C.P.U ≤ C.P.H0 := by
  rw [hC.H0_eq, hC.U_eq]
  exact le_sup_left

/-- `S₀` normalises `U` inside `G` (because `U ◁ H₀` and `S₀ ≤ H₀`). -/
theorem S0_le_normalizer_U (D : Work.GW2.BGData G) (C : Sec2Ctx G)
    (hC : Work.GW2.C16.Compat D C) : D.S0 ≤ Subgroup.normalizer (C.P.U : Set G) :=
  (S0_le_H0 D C hC).trans
    (Subgroup.le_normalizer_of_normal_subgroupOf (H := C.P.U) (K := C.P.H0) (U_le_H0 D C hC))

/-- **Every element of `H₀ = U ⊔ S₀` is a product `u · s` with `u ∈ U`, `s ∈ S₀`.** -/
theorem H0_decomp (D : Work.GW2.BGData G) (C : Sec2Ctx G) (hC : Work.GW2.C16.Compat D C)
    (x : ↥C.P.H0) :
    ∃ u : ↥C.P.H0, (u : G) ∈ C.P.U ∧ ∃ s : ↥C.P.H0, (s : G) ∈ D.S0 ∧ u * s = x := by
  have hx : (x : G) ∈ ((C.P.U ⊔ D.S0 : Subgroup G) : Set G) := by
    have h : (x : G) ∈ H1 D := by rw [← hC.H0_eq]; exact x.2
    rw [hC.U_eq]
    exact h
  rw [Subgroup.coe_mul_of_right_le_normalizer_left C.P.U D.S0
    (S0_le_normalizer_U D C hC)] at hx
  rw [Set.mem_mul] at hx
  obtain ⟨u, hu, s, hs, hus⟩ := hx
  refine ⟨⟨u, U_le_H0 D C hC hu⟩, hu, ⟨s, S0_le_H0 D C hC hs⟩, hs, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_mul]
  exact hus

/-! ## Lemma 2.1(b): `(λ_β)^s = λ_{β⁻¹}`, and injectivity of `β ↦ λ_β` -/

/-- The trivial class function of `H₀` is `s`-invariant. -/
theorem sconj_linear_one (C : Sec2Ctx G) :
    sconj C (linearClassFunction (1 : ↥C.P.H0 →* ℂˣ)) =
      linearClassFunction (1 : ↥C.P.H0 →* ℂˣ) := by
  ext h
  simp only [sconj, conjByH, ClassFunction.compHom_apply, linearClassFunction_apply,
    MonoidHom.one_apply, Units.val_one]

/-- **Bender–Glauberman 1981, Lemma 2.1(b) with `ν = 1`**: `(λ_β)^s = λ_{β⁻¹}`. -/
theorem sconj_lamCF (C : Sec2Ctx G) (β : lamDual C) :
    sconj C (lamCF C β) = lamCF C β⁻¹ := by
  have h := sconjLam C β (linearClassFunction (1 : ↥C.P.H0 →* ℂˣ))
  rw [sconj_linear_one C, ClassFunction.mul_linearClassFunction_one] at h
  simpa using h

/-- `β ↦ λ_β` is injective (the quotient map `H₀ → H₀/U` is surjective). -/
theorem lamCF_injective (C : Sec2Ctx G) : Function.Injective (lamCF C) := by
  intro β γ h
  refine MonoidHom.ext fun y => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (C.P.U.subgroupOf C.P.H0) y
  have h' := congrArg (fun f : ClassFunction ↥C.P.H0 ℂ => f x) h
  rw [lamCF_apply, lamCF_apply] at h'
  exact Units.ext h'

end LamCFFixed

theorem lamCF_fixed_eq_neg_one {G : Type} [Group G] [Finite G]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (hC : Work.GW2.C16.Compat D C)
    (β : Work.BG.quotGroup C.P →* ℂˣ) (hβ : β ≠ 1)
    (hfix : Work.BG.sconj C (Work.BG.lamCF C β) = Work.BG.lamCF C β)
    (g : ↥C.P.H0) (hg : (g : G) = D.t1 * D.t2) :
    Work.BG.lamCF C β g = -1 := by
  -- Lemma 2.1(b): `s` sends `λ_β` to `λ_{β⁻¹}`; `s`-invariance of `λ_β` forces `β = β⁻¹`.
  have hsconj : sconj C (lamCF C β) = lamCF C β⁻¹ := LamCFFixed.sconj_lamCF C β
  have hβinv : β⁻¹ = β := LamCFFixed.lamCF_injective C (hsconj.symm.trans hfix)
  have hββ : β * β = 1 := by
    have h : β⁻¹ * β = 1 := inv_mul_cancel β
    rwa [hβinv] at h
  -- Hence `β (gU)² = 1`.
  have hsq : β (quotMk C.P g) ^ 2 = 1 := by
    have h : (β * β) (quotMk C.P g) = 1 := by rw [hββ]; rfl
    simpa [MonoidHom.mul_apply, pow_two] using h
  -- `g` (more precisely `gU`) generates `H₀/U`: `S₀ = ⟨t₁t₂⟩` and `H₀ = U·S₀`.
  have hgen : β (quotMk C.P g) ≠ 1 := by
    intro h1
    refine hβ (MonoidHom.ext fun y => ?_)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (C.P.U.subgroupOf C.P.H0) y
    obtain ⟨u, hu, s, hs, hus⟩ := LamCFFixed.H0_decomp D C hC x
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (show (s : G) ∈ Subgroup.zpowers (D.t1 * D.t2) by rw [← D.gen]; exact hs)
    have hsg : s = g ^ k := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow, hg]
      exact hk.symm
    have hu1 : quotMk C.P u = 1 :=
      (QuotientGroup.eq_one_iff (N := C.P.U.subgroupOf C.P.H0) u).mpr hu
    have hπ : quotMk C.P x = (quotMk C.P g) ^ k := by
      rw [← hus, map_mul, hsg, map_zpow, hu1, one_mul]
    rw [hπ, map_zpow, h1]
    simp
  -- A unit squaring to `1` is `±1`, and it is not `1`.
  rcases units_sq_eq_one_eq_one_or_eq_neg_one (β (quotMk C.P g)) hsq with h | h
  · exact absurd h hgen
  · rw [lamCF_apply, h]
    norm_num

end Work.BG
