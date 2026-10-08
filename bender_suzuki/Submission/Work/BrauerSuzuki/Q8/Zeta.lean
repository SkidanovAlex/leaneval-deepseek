import Mathlib
import Submission.Work.BrauerSuzuki.Q8.Ctx
import Submission.Work.BrauerSuzuki.Q8.Card
import Submission.Work.BrauerSuzuki.Q8.LamEta
import Submission.Work.BrauerSuzuki.Q8.IndTwo
import Submission.Work.CharCore.principalChar_mem_Irr
import Submission.Work.Induction.isVChar_indFun
import Submission.Work.Induction.isClassFun_indFun

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Glauberman's character `ζ = Ind_{C*}^{N*}(1 - λ)` (step (2))

With `C* ≤ N* = N_G(⟨x⟩)` of index `2` and `λ` the linear character of `C*` with kernel
`T H*`, the function `φ = 1 - λ` on `C*` has support `A* = C* \ T H*` and value `2` there.
This file constructs `ζ := Ind_{C*}^{N*} φ` as a virtual character of `N*`
(`Work.Induction.isVChar_indFun`) and computes its values from the index-`2` value formula
`Work.BrauerSuzuki.Q8.indFun_eq_of_index_two`:

* `ζ (y) = 2 (1 - λ (y))` for `y ∈ C*` (hence `4` on `A*` and `0` on `T H*`), and
* `ζ (y) = 0` for `y ∈ N* \ C*`.
-/

set_option autoImplicit false

open Classical
open scoped Pointwise

namespace Work.BrauerSuzuki.Q8

variable {G : Type*} [Group G] [Finite G]

/-- A homomorphism into the abelian group `ℂˣ` gives a class function. -/
theorem isClassFun_coe_monoidHom {H : Type*} [Group H] (φ : H →* ℂˣ) :
    Work.CharCore.IsClassFun (fun h => ((φ h : ℂˣ) : ℂ)) := by
  intro a b
  show ((φ (b * a * b⁻¹) : ℂˣ) : ℂ) = ((φ a : ℂˣ) : ℂ)
  congr 1
  rw [map_mul, map_mul, map_inv, mul_assoc, mul_comm (φ a), ← mul_assoc, mul_inv_cancel, one_mul]

namespace Ctx

variable {x : G} {S : Sylow 2 G}
variable [Fintype G]

/-- `C*` is normal in `N*`. -/
theorem Cstar_normal_Nstar (h : Ctx G x S) : ((Cstar x).subgroupOf (Nstar x)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer h.Cstar_le_Nstar, Subgroup.le_normalizer_iff]
  intro n hn c hc
  exact h.Cstar_conj_Nstar hn hc

/-- `λ` transported to `↥(C*.subgroupOf N*)`. -/
noncomputable def lamKc (h : Ctx G x S) (k : ↥((Cstar x).subgroupOf (Nstar x))) : ℂ :=
  lamFun x ⟨((k : ↥(Nstar x)) : G), Subgroup.mem_subgroupOf.mp k.2⟩

/-- `φ' = 1 - λ` on `↥(C*.subgroupOf N*)`. -/
noncomputable def phiKc (h : Ctx G x S) (k : ↥((Cstar x).subgroupOf (Nstar x))) : ℂ :=
  1 - h.lamKc k

/-- Glauberman's generalized character `ζ = Ind_{C*}^{N*}(1 - λ)`. -/
noncomputable def zeta (h : Ctx G x S) : ↥(Nstar x) → ℂ :=
  Work.Induction.indFun ((Cstar x).subgroupOf (Nstar x)) h.phiKc

/-- `λ` on `↥Kc` as a `ℂˣ`-valued homomorphism. -/
noncomputable def lamKcHom (h : Ctx G x S) :
    ↥((Cstar x).subgroupOf (Nstar x)) →* ℂˣ :=
  h.lamHom.comp (Subgroup.subgroupOfEquivOfLe h.Cstar_le_Nstar).toMonoidHom

theorem lamKc_eq_comp (h : Ctx G x S) :
    h.lamKc = fun k => (((h.lamKcHom k : ℂˣ)) : ℂ) := by
  funext k
  show lamFun x ⟨((k : ↥(Nstar x)) : G), Subgroup.mem_subgroupOf.mp k.2⟩ =
    ((h.lamHom ((Subgroup.subgroupOfEquivOfLe h.Cstar_le_Nstar) k) : ℂˣ) : ℂ)
  rw [h.lamHom_coe]
  rfl

theorem lamKc_mem_Irr (h : Ctx G x S) :
    h.lamKc ∈ Work.CharCore.Irr ↥((Cstar x).subgroupOf (Nstar x)) := by
  obtain ⟨χ, hχ, hχeq⟩ := Work.CharCore.exists_irr_of_monoidHom h.lamKcHom
  have hχ' : χ = h.lamKc := by
    rw [h.lamKc_eq_comp]
    exact funext fun k => hχeq k
  rwa [hχ'] at hχ

theorem isVChar_phiKc (h : Ctx G x S) : Work.CharCore.IsVChar h.phiKc := by
  have h1 : h.phiKc = (fun _ : ↥((Cstar x).subgroupOf (Nstar x)) => (1 : ℂ)) - h.lamKc := by
    funext k
    simp [phiKc]
  rw [h1]
  refine Work.CharCore.IsVChar.sub ?_ ?_
  · exact Work.CharCore.IsVChar.of_mem_Irr Work.CharCore.principalChar_mem_Irr
  · exact Work.CharCore.IsVChar.of_mem_Irr h.lamKc_mem_Irr

theorem isVChar_zeta (h : Ctx G x S) : Work.CharCore.IsVChar h.zeta := by
  rw [zeta]
  exact Work.Induction.isVChar_indFun h.isVChar_phiKc

theorem isClassFun_lamKc (h : Ctx G x S) :
    Work.CharCore.IsClassFun h.lamKc := by
  rw [h.lamKc_eq_comp]
  exact isClassFun_coe_monoidHom h.lamKcHom

theorem isClassFun_phiKc (h : Ctx G x S) : Work.CharCore.IsClassFun h.phiKc := by
  have h1 : h.phiKc = (fun _ : ↥((Cstar x).subgroupOf (Nstar x)) => (1 : ℂ)) - h.lamKc := by
    funext k; simp [phiKc]
  rw [h1]
  exact Work.CharCore.IsClassFun.sub (Work.CharCore.isClassFun_const _) h.isClassFun_lamKc

theorem isClassFun_zeta (h : Ctx G x S) : Work.CharCore.IsClassFun h.zeta := by
  rw [zeta]
  exact Work.Induction.isClassFun_indFun _ h.phiKc

theorem subgroupOf_index_two (h : Ctx G x S) :
    ((Cstar x).subgroupOf (Nstar x)).index = 2 := by
  have h1 : Nat.card ↥((Cstar x).subgroupOf (Nstar x)) = Nat.card ↥(Cstar x) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Cstar_le_Nstar).toEquiv
  have h2 := Subgroup.card_mul_index ((Cstar x).subgroupOf (Nstar x))
  rw [h1, h.card_Cstar, h.card_Nstar] at h2
  have hpos : 0 < 4 * Nat.card ↥(Hstar x) := by
    have : 0 < Nat.card ↥(Hstar x) := Nat.card_pos_iff.mpr ⟨⟨1, (Hstar x).one_mem⟩, inferInstance⟩
    positivity
  have h3 : 4 * Nat.card ↥(Hstar x) * ((Cstar x).subgroupOf (Nstar x)).index =
      4 * Nat.card ↥(Hstar x) * 2 := by
    rw [h2]; ring
  exact Nat.mul_left_cancel hpos h3

/-- The invariance hypothesis of the index-`2` value formula for `φ' = 1 - λ`. -/
theorem phiKc_conj (h : Ctx G x S) (l : ↥(Nstar x))
    (k : ↥((Cstar x).subgroupOf (Nstar x))) :
    h.phiKc ⟨l * k * l⁻¹, (h.Cstar_normal_Nstar).conj_mem k k.2 l⟩ = h.phiKc k := by
  have hkey : h.lamKc ⟨l * k * l⁻¹, (h.Cstar_normal_Nstar).conj_mem k k.2 l⟩ = h.lamKc k := by
    rw [lamKc, lamKc]
    refine h.lamFun_conj_Nstar l.2 ⟨((k : ↥(Nstar x)) : G), Subgroup.mem_subgroupOf.mp k.2⟩
  simp only [phiKc, hkey]

theorem zeta_apply_of_mem (h : Ctx G x S) {y : ↥(Nstar x)}
    (hy : y ∈ (Cstar x).subgroupOf (Nstar x)) :
    h.zeta y = 2 * h.phiKc ⟨y, hy⟩ := by
  rw [zeta]
  exact indFun_eq_of_index_two h.Cstar_normal_Nstar h.subgroupOf_index_two h.isClassFun_phiKc
    h.phiKc_conj hy

theorem zeta_apply_of_notMem (h : Ctx G x S) {y : ↥(Nstar x)}
    (hy : y ∉ (Cstar x).subgroupOf (Nstar x)) : h.zeta y = 0 := by
  rw [zeta]
  exact indFun_eq_zero_of_index_two h.Cstar_normal_Nstar hy

/-- The value of `ζ` at an element of `C*`: `2 (1 - λ (y))`. -/
theorem zeta_apply_of_mem_Cstar (h : Ctx G x S) {y : ↥(Nstar x)} (hy : (y : G) ∈ Cstar x) :
    h.zeta y = 2 * (1 - lamFun x ⟨(y : G), hy⟩) := by
  have hy' : y ∈ (Cstar x).subgroupOf (Nstar x) := Subgroup.mem_subgroupOf.mpr hy
  rw [h.zeta_apply_of_mem hy']
  have h2 : h.phiKc ⟨y, hy'⟩ = 1 - lamFun x ⟨(y : G), hy⟩ := by
    simp only [phiKc, lamKc]
  rw [h2]

/-- The value of `ζ` off `C*`: `0`. -/
theorem zeta_apply_of_notMem_Cstar (h : Ctx G x S) {y : ↥(Nstar x)} (hy : (y : G) ∉ Cstar x) :
    h.zeta y = 0 :=
  h.zeta_apply_of_notMem (fun hc => hy (Subgroup.mem_subgroupOf.mp hc))

end Ctx

end Work.BrauerSuzuki.Q8
