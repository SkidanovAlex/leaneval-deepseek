import Mathlib
import Submission.Work.BG.s02_lemma21_aux

/-!
# Area BG: BG Lemma 2.1 — the two "halves" of the `Λ`-orbit of a character

Bender–Glauberman 1981, Lemma 2.1 (p. 204): for `ν ∈ Irr(H₀)` exactly half of the
characters of the orbit `Λν` have `t` in their kernel, i.e.

`{χ ∈ Λν : χ(t) = χ(1)}.ncard = {χ ∈ Λν : χ(t) = -χ(1)}.ncard`.

The proof here does not even need `ν ∈ Irr(H₀)`, and it never uses the structure of `Λ`:
by `exists_negChar` there is `λ = λ_γ ∈ Λ` with `λ(t) = -1`.  Multiplication by `λ` is a
nowhere-zero pointwise multiplication of class functions, hence injective, and it carries
the first set into the second and the second set into the first: for any class function
`χ` on `H₀`,

* `(λχ)(t) = λ(t)χ(t) = -χ(t)` and `(λχ)(1) = λ(1)χ(1) = χ(1)`.

So `χ ↦ λχ` injects each of the two sets into the other, and with the orbit finite
(`Λ` is finite) the two cardinalities agree.  (The irreducibility hypothesis is used in
the paper only to know `ν(t) ≠ 0`, which is not needed for the counting statement.)

The finiteness of `Λν` is `Set.finite_range` of `β ↦ λ_β ν` over the finite group
`Λ = Hom(H₀/U, ℂˣ)`; no `Fintype G` is required.
-/

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-! ## Values of the linear characters `λ_β` -/

/-- The value of `λ_β` at a group element, in terms of the corresponding unit of `ℂˣ`. -/
theorem lamCF_apply_val (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ) (g : ↥C.P.H0) :
    lamCF C β g = ((β (quotMk C.P g) : ℂˣ) : ℂ) := by
  rw [lamCF, ClassFunction.compHom_apply, linearClassFunction_apply]

/-- `λ_β(1) = 1`. -/
theorem lamCF_apply_one_eq_one (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ) :
    lamCF C β 1 = 1 := by
  rw [lamCF_apply_val]
  simp

/-- Values of `λ_β` are units of `ℂ`, in particular never zero. -/
theorem lamCF_apply_ne_zero (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ) (g : ↥C.P.H0) :
    lamCF C β g ≠ 0 := by
  rw [lamCF_apply_val]
  exact Units.ne_zero _

/-- Multiplying by `λ_β` preserves the `Λ`-orbit `Λν`. -/
theorem lamCF_mul_mem_lamOrbit (C : Sec2Ctx G) (β : quotGroup C.P →* ℂˣ)
    {ν χ : ClassFunction ↥C.P.H0 ℂ} (hχ : χ ∈ lamOrbit C ν) :
    lamCF C β * χ ∈ lamOrbit C ν := by
  obtain ⟨β', rfl⟩ := hχ
  exact ⟨β * β', by rw [s02c_lamCF_mul, s02c_cf_mul_assoc]⟩

/-! ## Lemma 2.1: the two halves have the same size -/

theorem s02_lemma21_halves {G : Type} [Group G] [Finite G] (C : Work.BG.Sec2Ctx G)
    (ν : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ)
    (hν : OddOrder.RepresentationTheory.IsIrreducibleCharacter ν) :
    {χ ∈ Work.BG.lamOrbit C ν | χ C.t = χ 1}.ncard =
      {χ ∈ Work.BG.lamOrbit C ν | χ C.t = -χ 1}.ncard := by
  classical
  -- a linear character of `H₀/U` of value `-1` at `t`
  obtain ⟨γ, hγ⟩ := exists_negChar C
  -- multiplication by `λ_γ` negates the value at `t` and fixes the degree
  have hval_t : ∀ χ : ClassFunction ↥C.P.H0 ℂ, (lamCF C γ * χ) C.t = -(χ C.t) := by
    intro χ
    rw [ClassFunction.mul_apply, hγ, neg_one_mul]
  have hval_one : ∀ χ : ClassFunction ↥C.P.H0 ℂ, (lamCF C γ * χ) 1 = χ 1 := by
    intro χ
    rw [ClassFunction.mul_apply, lamCF_apply_one_eq_one, one_mul]
  -- `χ ↦ λ_γ χ` maps the first set into the second ...
  have hAB : ∀ χ ∈ ({χ ∈ lamOrbit C ν | χ C.t = χ 1} : Set (ClassFunction ↥C.P.H0 ℂ)),
      lamCF C γ * χ ∈ {χ ∈ lamOrbit C ν | χ C.t = -χ 1} := by
    intro χ hχ
    obtain ⟨horb, hval⟩ := hχ
    refine ⟨lamCF_mul_mem_lamOrbit C γ horb, ?_⟩
    rw [hval_t, hval, hval_one]
  -- ... and the second set into the first
  have hBA : ∀ χ ∈ ({χ ∈ lamOrbit C ν | χ C.t = -χ 1} : Set (ClassFunction ↥C.P.H0 ℂ)),
      lamCF C γ * χ ∈ {χ ∈ lamOrbit C ν | χ C.t = χ 1} := by
    intro χ hχ
    obtain ⟨horb, hval⟩ := hχ
    refine ⟨lamCF_mul_mem_lamOrbit C γ horb, ?_⟩
    rw [hval_t, hval, hval_one, neg_neg]
  -- pointwise multiplication by `λ_γ` is injective (its values are nonzero)
  have hinj : ∀ χ₁ ∈ ({χ ∈ lamOrbit C ν | χ C.t = χ 1} : Set (ClassFunction ↥C.P.H0 ℂ)),
      ∀ χ₂ ∈ ({χ ∈ lamOrbit C ν | χ C.t = χ 1} : Set (ClassFunction ↥C.P.H0 ℂ)),
      lamCF C γ * χ₁ = lamCF C γ * χ₂ → χ₁ = χ₂ := by
    intro χ₁ _ χ₂ _ h
    ext g
    have hg : (lamCF C γ * χ₁) g = (lamCF C γ * χ₂) g := by rw [h]
    rw [ClassFunction.mul_apply, ClassFunction.mul_apply] at hg
    exact mul_left_cancel₀ (lamCF_apply_ne_zero C γ g) hg
  have hinj' : ∀ χ₁ ∈ ({χ ∈ lamOrbit C ν | χ C.t = -χ 1} : Set (ClassFunction ↥C.P.H0 ℂ)),
      ∀ χ₂ ∈ ({χ ∈ lamOrbit C ν | χ C.t = -χ 1} : Set (ClassFunction ↥C.P.H0 ℂ)),
      lamCF C γ * χ₁ = lamCF C γ * χ₂ → χ₁ = χ₂ := by
    intro χ₁ _ χ₂ _ h
    ext g
    have hg : (lamCF C γ * χ₁) g = (lamCF C γ * χ₂) g := by rw [h]
    rw [ClassFunction.mul_apply, ClassFunction.mul_apply] at hg
    exact mul_left_cancel₀ (lamCF_apply_ne_zero C γ g) hg
  -- `Λν` is finite: it is the range of `β ↦ λ_β ν` over the finite group `Λ`
  have horbFin : (lamOrbit C ν).Finite := by
    have hrange : lamOrbit C ν =
        Set.range (fun β : quotGroup C.P →* ℂˣ => lamCF C β * ν) := by
      ext χ
      exact ⟨fun ⟨β, hβ⟩ => ⟨β, hβ.symm⟩, fun ⟨β, hβ⟩ => ⟨β, hβ.symm⟩⟩
    rw [hrange]
    exact Set.finite_range _
  have hAfin : ({χ ∈ lamOrbit C ν | χ C.t = χ 1} : Set (ClassFunction ↥C.P.H0 ℂ)).Finite :=
    horbFin.subset fun _ hχ => hχ.1
  have hBfin : ({χ ∈ lamOrbit C ν | χ C.t = -χ 1} : Set (ClassFunction ↥C.P.H0 ℂ)).Finite :=
    horbFin.subset fun _ hχ => hχ.1
  refine le_antisymm ?_ ?_
  · exact Set.ncard_le_ncard_of_injOn (fun χ : ClassFunction ↥C.P.H0 ℂ => lamCF C γ * χ)
      hAB hinj hBfin
  · exact Set.ncard_le_ncard_of_injOn (fun χ : ClassFunction ↥C.P.H0 ℂ => lamCF C γ * χ)
      hBA hinj' hAfin

end Work.BG
