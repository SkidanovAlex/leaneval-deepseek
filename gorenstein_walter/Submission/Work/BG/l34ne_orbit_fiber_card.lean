import Mathlib
import Submission.Work.BG.lemma24
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.lambda_mul_irreducible
import Submission.Work.BG.s02_lemma21

namespace Work.BG

/-!
# Area BG: the `Λ`-orbit `Λr` at an orbit representative, counted inside `Irr(H₀)`

Bender–Glauberman 1981, §2.  At an `Λ`-orbit representative `r` (`orbitRep C r = r`), the
orbit `Λr = lamOrbit C r` consists *entirely* of irreducible characters — twisting by a
linear character `λ ∈ Λ` preserves `Irr(H₀)` (`Work.BG.lambda_mul_irreducible`) — and two
members `λ·r`, `μ·r` are equal only for `λ = μ`.  Hence counting the orbit `Λr` as a set of
class functions is the same as counting the irreducible characters of `H₀` lying in it,
i.e. the irreducible characters whose `Λ`-orbit representative is `r`:

`(Λr).ncard = #{ν ∈ Irr(H₀) | orbitRep C ν = r}`.

This is the bookkeeping step used when a character-theoretic count runs over
`Finset.univ.filter (fun ν => orbitRep C ν = r)` and must be read as a sum over the orbit
`Λr` (or conversely).
-/

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem l34ne_orbit_fiber_card {G : Type} [Group G] [Finite G] [Fintype G]
    (C : Work.BG.Sec2Ctx G) [Fintype ↥C.P.H0] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    [DecidableEq (IrreducibleCharacter ↥C.P.H0)]
    (r : IrreducibleCharacter ↥C.P.H0) (hr : Work.BG.orbitRep C r = r) :
    (Work.BG.lamOrbit C (r : ClassFunction ↥C.P.H0 ℂ)).ncard =
      (Finset.univ.filter (fun ν : IrreducibleCharacter ↥C.P.H0 =>
        Work.BG.orbitRep C ν = r)).card := by
  classical
  -- The orbit `Λr`, as a set of class functions, is exactly the image of the set of
  -- irreducible characters in the orbit `Λr` under the coercion `Irr(H₀) → CF(H₀)`.
  have himg : Work.BG.lamOrbit C (r : ClassFunction ↥C.P.H0 ℂ) =
      (Subtype.val '' {ν : IrreducibleCharacter ↥C.P.H0 | Work.BG.orbitRep C ν = r}) := by
    ext χ
    constructor
    · intro hχ
      obtain ⟨β, rfl⟩ := hχ
      -- twisting `r` by the linear character `lamCF C β ∈ Λ` stays irreducible
      have hlam : Work.BG.lamCF C β ∈ Work.BG.Lambda C.P := ⟨β, rfl⟩
      have hirr : IsIrreducibleCharacter
          (Work.BG.lamCF C β * (r : ClassFunction ↥C.P.H0 ℂ)) :=
        Work.BG.lambda_mul_irreducible C.P hlam r.2
      refine ⟨⟨_, hirr⟩, ?_, rfl⟩
      -- `lamCF C β * r` is `Λ`-equivalent to `r`, hence has the same orbit representative
      have h2 := Work.BG.orbitRep_eq_of_lamEquiv (C := C) (μ := r) (ν := ⟨_, hirr⟩)
        (show Work.BG.LamEquiv C (r : ClassFunction ↥C.P.H0 ℂ)
          ((⟨_, hirr⟩ : IrreducibleCharacter ↥C.P.H0) : ClassFunction ↥C.P.H0 ℂ)
          from ⟨β, rfl⟩)
      rw [hr] at h2
      exact h2.symm
    · rintro ⟨ν, hν, rfl⟩
      -- `ν ≡ r (mod Λ)` because `ν` is `Λ`-equivalent to its orbit representative `r`
      have h1 : Work.BG.LamEquiv C (ν : ClassFunction ↥C.P.H0 ℂ)
          (r : ClassFunction ↥C.P.H0 ℂ) := by
        rw [← hν]
        exact Work.BG.orbitRep_mem C ν
      exact Work.BG.s02c_LamEquiv_symm C h1
  rw [← Set.ncard_coe_finset (Finset.univ.filter (fun ν : IrreducibleCharacter ↥C.P.H0 =>
        Work.BG.orbitRep C ν = r))]
  have hS : ((Finset.univ.filter (fun ν : IrreducibleCharacter ↥C.P.H0 =>
        Work.BG.orbitRep C ν = r) : Finset _) : Set _) =
      {ν : IrreducibleCharacter ↥C.P.H0 | Work.BG.orbitRep C ν = r} := by
    ext ν; simp
  rw [hS, himg, Set.ncard_image_of_injective _ (Subtype.coe_injective)]

end Work.BG
