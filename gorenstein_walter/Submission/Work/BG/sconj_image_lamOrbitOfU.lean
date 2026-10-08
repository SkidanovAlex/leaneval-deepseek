import Mathlib
import Submission.Work.BG.lemma36Defs
import Submission.Work.BG.L33DDefs
import Submission.Work.BG.sconjLam

/-!
# Area BG: `s`-conjugation permutes the `Λ`-orbit `Λ(a)` of a character of `U`

**Bender–Glauberman 1981, Lemma 2.1 / Remark 3.1, `U`-form.**  The involution `s ∈ H ∖ H₀`
acts on the class functions of `H₀` by `ν ↦ ν^s = Work.BG.sconj C ν`, and on the class
functions of `U = O(H)` by the conjugation action `L33D.phiS D C hDC ⟨t₁, t₁_mem⟩`
(`s = t₁` in the compatible §2 context, `Work.GW2.C16.Compat.s_eq`).

The main result `Work.BG.sconj_image_lamOrbitOfU` is that `s`-conjugation carries the set
`Work.BG.lamOrbitOfU C a` of irreducibles of `H₀` whose restriction to `U` contains `a` onto
the corresponding set for the `s`-conjugate `a ∘ φ_S(t₁)` of `a`:

  `sconj C '' lamOrbitOfU C a = lamOrbitOfU C (a ∘ φ_S(t₁))`.

The mathematics is one line.  For `u ∈ U`,

  `(ν^s)(u) = ν(s u s⁻¹) = ν(φ_S(t₁) u)`,

that is, restriction to `U` intertwines `sconj` with the pullback `φ_S(t₁)`:

  `restrict U (sconj C ν) = compHom φ_S(t₁) (restrict U ν)`

(`restrict_sconj_eq_compHom_phiS`).  Since `φ_S(t₁)` is an automorphism of `U`, the inner
product on `U` is invariant under it (`ClassFunction.inner_compHom_mulEquiv`), so

  `⟨(ν^s)|_U, a ∘ φ_S(t₁)⟩ = ⟨ν|_U, a⟩`.

Irreducibility is preserved by `sconj` (it is a pullback along the group automorphism
`h ↦ s h s⁻¹` of `H₀`), whence

  `ν^s ∈ lamOrbitOfU C (a ∘ φ_S(t₁))  ↔  ν ∈ lamOrbitOfU C a`

for every class function `ν` of `H₀` (`mem_lamOrbitOfU_sconj_iff`).  As `sconj` is an
involution (`sconj_sconj`, from `s² = 1` and `conjByH_mul`), this equivalence is exactly the
statement that `sconj` is a bijection from `lamOrbitOfU C a` onto
`lamOrbitOfU C (a ∘ φ_S(t₁))`, which is the goal.

No hypothesis on `a` is needed: the identity `⟨(ν^s)|_U, a^s⟩ = ⟨ν|_U, a⟩` holds for every
class function `a` of `U`, and when `a` is not irreducible both sides of the target are empty.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

set_option maxHeartbeats 800000

/-! ## Auxiliary structural facts

These are placed in their own namespace so that the module can be imported alongside the
other `Work.BG` modules that prove the same elementary facts (e.g. `sconj_sconj`). -/

namespace SconjImageLamOrbit

variable {G : Type} [Group G] [Finite G]

/-- Conjugation by `1 ∈ H` is the identity on class functions of `H₀`. -/
theorem conjByH_one (P : Hyp12 G) (ν : ClassFunction ↥P.H0 ℂ) :
    conjByH P (1 : ↥P.H) ν = ν := by
  ext h
  rw [conjByH_apply]
  exact congrArg ν (Subtype.ext (by rw [conjMulEquiv_apply]; simp))

/-- `s`-conjugation is an involution on the class functions of `H₀`. -/
theorem sconj_sconj (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) :
    sconj C (sconj C ν) = ν := by
  have h1 : C.s * C.s = (1 : ↥C.P.H) := by
    have h := C.s_sq
    rwa [pow_two] at h
  simp only [sconj]
  rw [← conjByH_mul, h1]
  exact conjByH_one C.P ν

/-- `sconj` preserves irreducibility, in both directions. -/
theorem isIrreducibleCharacter_sconj_iff (C : Sec2Ctx G) (ν : ClassFunction ↥C.P.H0 ℂ) :
    IsIrreducibleCharacter (sconj C ν) ↔ IsIrreducibleCharacter ν := by
  constructor
  · intro h
    have h' : IsIrreducibleCharacter (sconj C (sconj C ν)) :=
      IsIrreducibleCharacter.conjByH C.P C.s h
    rwa [sconj_sconj C ν] at h'
  · intro h
    exact IsIrreducibleCharacter.conjByH C.P C.s h

/-- Restriction to `U` intertwines `sconj` (conjugation by `s ∈ H ∖ H₀`) with the pullback
`L33D.phiS D C hDC ⟨t₁, t₁_mem⟩` (conjugation by `t₁ = s`) along the embedding `U ↪ H₀`. -/
theorem restrict_sconj_eq_compHom_phiS (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (ν : ClassFunction ↥C.P.H0 ℂ) :
    ClassFunction.restrict (Uin C) (sconj C ν) =
      ClassFunction.compHom (L33D.phiS D C hDC ⟨D.t1, D.t1_mem⟩).toMonoidHom
        (ClassFunction.restrict (Uin C) ν) := by
  ext u
  show ν (conjMulEquiv C.P C.s (u : ↥C.P.H0)) =
      ν ↑(((L33D.phiS D C hDC ⟨D.t1, D.t1_mem⟩) u : ↥(Uin C)) : ↥C.P.H0)
  have hkey : conjMulEquiv C.P C.s (u : ↥C.P.H0)
      = (((L33D.phiS D C hDC ⟨D.t1, D.t1_mem⟩) u : ↥(Uin C)) : ↥C.P.H0) := by
    apply Subtype.ext
    rw [conjMulEquiv_apply, L33D.phiS_apply, hDC.s_eq]
  rw [hkey]

/-- The inner product with `a ∘ φ_S(t₁)` of `(ν^s)|_U` equals the inner product of `ν|_U`
with `a`: both are `(1/|U|) Σ_{u ∈ U} ν(s u s⁻¹) \overline{a(s u s⁻¹)}`, and `u ↦ s u s⁻¹`
is a bijection of `U`. -/
theorem inner_restrict_sconj_eq (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    [Fintype ↥(Uin C)] [Invertible (Nat.card ↥(Uin C) : ℂ)]
    (ν : ClassFunction ↥C.P.H0 ℂ) (a : ClassFunction ↥(Uin C) ℂ) :
    ClassFunction.inner (ClassFunction.restrict (Uin C) (sconj C ν))
        (ClassFunction.compHom (L33D.phiS D C hDC ⟨D.t1, D.t1_mem⟩).toMonoidHom a) =
      ClassFunction.inner (ClassFunction.restrict (Uin C) ν) a := by
  have h := ClassFunction.inner_compHom_mulEquiv (L33D.phiS D C hDC ⟨D.t1, D.t1_mem⟩)
    (ClassFunction.restrict (Uin C) ν) a
  rw [← restrict_sconj_eq_compHom_phiS D C hDC ν] at h
  exact h

/-- **Key equivalence.**  `ν^s` has `a ∘ φ_S(t₁)` as a constituent of its restriction to `U`
if and only if `ν` has `a` as one. -/
theorem mem_lamOrbitOfU_sconj_iff (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    [Fintype ↥(Uin C)] [Invertible (Nat.card ↥(Uin C) : ℂ)]
    (a : ClassFunction ↥(Uin C) ℂ) (ν : ClassFunction ↥C.P.H0 ℂ) :
    sconj C ν ∈ lamOrbitOfU C
        (ClassFunction.compHom (L33D.phiS D C hDC ⟨D.t1, D.t1_mem⟩).toMonoidHom a)
      ↔ ν ∈ lamOrbitOfU C a := by
  constructor
  · rintro ⟨hirr, hinner⟩
    refine ⟨(isIrreducibleCharacter_sconj_iff C ν).mp hirr, ?_⟩
    rw [← inner_restrict_sconj_eq D C hDC ν a]
    exact hinner
  · rintro ⟨hirr, hinner⟩
    refine ⟨(isIrreducibleCharacter_sconj_iff C ν).mpr hirr, ?_⟩
    rw [inner_restrict_sconj_eq D C hDC ν a]
    exact hinner

end SconjImageLamOrbit

/-! ## The main statement -/

theorem sconj_image_lamOrbitOfU {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (hDC : Work.GW2.C16.Compat D C)
    [Fintype ↥(Work.GW2.C16.Uin C)] [Invertible (Nat.card ↥(Work.GW2.C16.Uin C) : ℂ)]
    (a : OddOrder.RepresentationTheory.ClassFunction ↥(Work.GW2.C16.Uin C) ℂ) :
    Work.BG.sconj C '' (Work.BG.lamOrbitOfU C a) =
      Work.BG.lamOrbitOfU C
        (OddOrder.RepresentationTheory.ClassFunction.compHom
          (Work.BG.L33D.phiS D C hDC ⟨D.t1, D.t1_mem⟩).toMonoidHom a) := by
  have hiff : ∀ ν : ClassFunction ↥C.P.H0 ℂ,
      sconj C ν ∈ lamOrbitOfU C
          (ClassFunction.compHom (L33D.phiS D C hDC ⟨D.t1, D.t1_mem⟩).toMonoidHom a)
        ↔ ν ∈ lamOrbitOfU C a :=
    fun ν => SconjImageLamOrbit.mem_lamOrbitOfU_sconj_iff D C hDC a ν
  ext μ
  constructor
  · rintro ⟨ν, hν, rfl⟩
    exact (hiff ν).mpr hν
  · intro hμ
    exact ⟨sconj C μ,
      (hiff (sconj C μ)).mp (by rwa [SconjImageLamOrbit.sconj_sconj C μ]),
      SconjImageLamOrbit.sconj_sconj C μ⟩

end Work.BG
