import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.Lambda
import Submission.Work.BG.CharBridge
import Submission.Work.BG.conjByH_basic
import Submission.Work.BG.sconjLam
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.lemma17_ii_aux

/-!
# Area BG: the dual group of `H₀/U` acting on `CF(H₀)` (support module for Lemma 2.1-d)

Bender–Glauberman's `Λ` is the group of linear characters of `H₀/U`; in area BG it is
realised as the inflations `lamCF C β` of the homomorphisms `β : H₀/U →* ℂˣ`.  This module
collects the group-theoretic packaging of that realisation, used by the proof of
`Work.BG.Lemma21ExtProp` (= BG Lemma 2.1's "extension" clause, p. 204):

* `Work.BG.lamDual C` — the group `(H₀/U) →* ℂˣ`;
* `Work.BG.tU C` — the class of `t` in `H₀/U`;
* `Work.BG.lamEvt C` — evaluation at `tU`, a homomorphism `lamDual C →* ℂˣ`;
* the `lamDual C`-action `β • f = lamCF C β * f` on `CF(H₀)`, whose orbits are exactly the
  sets `lamOrbit C ν`;
* `Work.BG.lamStab C ν` — the stabiliser of `ν` under that action;
* the basic algebra of `lamCF` (`lamCF_mul`, `lamCF_one`), the `t`-value formula, and the twist
  formula `sconj (lamCF C β * ν) = lamCF C β⁻¹ * sconj C ν`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-- The dual group `(H₀/U) →* ℂˣ`, i.e. Bender–Glauberman's `Λ` before inflation to `H₀`. -/
abbrev lamDual (C : Sec2Ctx G) : Type := quotGroup C.P →* ℂˣ

/-- The class of the involution `t` in `H₀/U`. -/
def tU (C : Sec2Ctx G) : quotGroup C.P := quotMk C.P C.t

/-- `tU ≠ 1` in `H₀/U`. -/
theorem tU_ne_one (C : Sec2Ctx G) : tU C ≠ 1 := fun h =>
  C.t_not_mem_U ((QuotientGroup.eq_one_iff C.t).mp h)

/-- `tU` is an involution of `H₀/U`. -/
theorem tU_sq (C : Sec2Ctx G) : tU C ^ 2 = 1 := by
  rw [tU, ← map_pow, C.t_sq, map_one]

/-- **Evaluation at `tU`**: the homomorphism `Λ → ℂˣ`, `β ↦ β tU`. -/
def lamEvt (C : Sec2Ctx G) : lamDual C →* ℂˣ where
  toFun β := β (tU C)
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem lamEvt_apply (C : Sec2Ctx G) (β : lamDual C) : lamEvt C β = β (tU C) := rfl

/-- The kernel of evaluation at `tU` (BG's `Λ¹ = {λ ∈ Λ | λ(t) = 1}`). -/
def lamKernel (C : Sec2Ctx G) : Subgroup (lamDual C) := (lamEvt C).ker

@[simp] theorem mem_lamKernel (C : Sec2Ctx G) (β : lamDual C) :
    β ∈ lamKernel C ↔ β (tU C) = 1 := Iff.rfl

/-- `lamCF` is multiplicative. -/
theorem lamCF_mul (C : Sec2Ctx G) (β γ : lamDual C) :
    lamCF C (β * γ) = lamCF C β * lamCF C γ := by
  ext x
  simp only [lamCF, ClassFunction.mul_apply, ClassFunction.compHom_apply,
    linearClassFunction_apply, MonoidHom.mul_apply, Units.val_mul]

/-- `lamCF C 1 = 1` (the trivial function `linearClassFunction 1`). -/
theorem lamCF_one (C : Sec2Ctx G) :
    lamCF C 1 = linearClassFunction (1 : ↥C.P.H0 →* ℂˣ) := by
  ext x
  simp [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply]

/-- The value of `lamCF C β` at `t` is `β tU`, as a complex number. -/
theorem lamCF_apply_t (C : Sec2Ctx G) (β : lamDual C) :
    lamCF C β C.t = ((β (tU C) : ℂˣ) : ℂ) := by
  simp [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply, tU]

/-- The value at `t` of the twist `lamCF C β * ν`. -/
theorem mul_apply_t (C : Sec2Ctx G) (β : lamDual C) (ν : ClassFunction ↥C.P.H0 ℂ) :
    (lamCF C β * ν) C.t = ((β (tU C) : ℂˣ) : ℂ) * ν C.t := by
  rw [ClassFunction.mul_apply, lamCF_apply_t]

-- The three product lemmas `mul_assoc_cf`, `mul_comm_cf`, `one_mul_cf` used below are
-- declared (in more general form) in `Submission.Work.BG.lemma17_ii_aux`, which this module
-- imports; they were duplicated here once and the duplicate caused an environment clash
-- (`Work.BG.mul_assoc_cf` already present) for callers importing both modules.

/-- The `Λ`-action on class functions of `H₀`: `β • f = lamCF C β * f`. -/
noncomputable instance instSMulLamDual (C : Sec2Ctx G) :
    SMul (lamDual C) (ClassFunction ↥C.P.H0 ℂ) :=
  ⟨fun β f => lamCF C β * f⟩

theorem smul_def (C : Sec2Ctx G) (β : lamDual C) (f : ClassFunction ↥C.P.H0 ℂ) :
    β • f = lamCF C β * f := rfl

noncomputable instance instMulActionLamDual (C : Sec2Ctx G) :
    MulAction (lamDual C) (ClassFunction ↥C.P.H0 ℂ) where
  one_smul f := by
    show lamCF C 1 * f = f
    rw [lamCF_one, one_mul_cf]
  mul_smul β γ f := by
    show lamCF C (β * γ) * f = lamCF C β * (lamCF C γ * f)
    rw [lamCF_mul, mul_assoc_cf]

theorem lamCF_apply (C : Sec2Ctx G) (β : lamDual C) (x : ↥C.P.H0) :
    lamCF C β x = ((β (quotMk C.P x) : ℂˣ) : ℂ) := by
  simp [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply]

/-- The orbit of `ν` under the `Λ`-action is the `Λ`-orbit `lamOrbit C ν`. -/
theorem orbit_eq_lamOrbit (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) :
    MulAction.orbit (lamDual C) ν = lamOrbit C ν := by
  ext χ
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨β, hβ⟩
    exact ⟨β, hβ.symm⟩
  · rintro ⟨β, hβ⟩
    exact ⟨β, hβ.symm⟩

/-- The stabiliser of `ν` under the `Λ`-action (BG's `Λ_ν`, in dual form). -/
noncomputable def lamStab (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) : Subgroup (lamDual C) :=
  MulAction.stabilizer (lamDual C) ν

theorem mem_lamStab (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) (β : lamDual C) :
    β ∈ lamStab C ν ↔ lamCF C β * ν = ν := Iff.rfl

/-- Conjugation by `1 ∈ H`. -/
theorem conjMulEquiv_one (C : Sec2Ctx G) (h : ↥C.P.H0) : conjMulEquiv C.P 1 h = h := by
  apply Subtype.ext
  rw [conjMulEquiv_apply]
  simp

/-- `s`-conjugation is an involution on class functions of `H₀`. -/
theorem sconj_sconj (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) :
    sconj C (sconj C ν) = ν := by
  rw [sconj, sconj, ← conjByH_mul, ← pow_two, C.s_sq]
  ext h
  simp [conjByH_apply, conjMulEquiv_one]

/-- The `s`-conjugate of a member of the orbit, in `Λ`-parameters. -/
theorem sconj_image_lamOrbit_subset (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) :
    sconj C '' lamOrbit C ν ⊆ lamOrbit C (sconj C ν) := by
  rintro _ ⟨χ, ⟨β, rfl⟩, rfl⟩
  exact ⟨β⁻¹, sconjLam C β ν⟩

end Work.BG
