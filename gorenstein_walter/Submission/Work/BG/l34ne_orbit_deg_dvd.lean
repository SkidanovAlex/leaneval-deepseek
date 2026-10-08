import Mathlib
import Submission.Work.BG.rem31Shape
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.HatInjDefs
import Submission.Work.BG.congContra

/-!
# Area BG: `l34ne_orbit_deg_dvd` — the orbit-size/degree divisibility of Remark 3.1

Bender–Glauberman 1981, Remark 3.1 (p. 208) describes the two possible shapes of the
restriction `ν|_U` of an irreducible character `ν` of `H₀ = U S₀` (§3 hypotheses,
`Work.GW2.C16.Sec3Hyp`):

* `ν|_U = a` with `a ∈ Irr(U)` and `|Λν| = |H₀ : U| = D.n`, or
* `ν|_U = a + a₂` with `a, a₂ ∈ Irr(U)` distinct of equal degree and `2 |Λν| = D.n`.

Evaluating at `1` and multiplying by `|Λν|` gives, in both cases,

  `|Λν| · ν(1) = D.n · a(1)`,

and `a` is an irreducible character of the odd-order group `U`, so `a(1)` is an odd integer
(`Work.BG.exists_odd_nat_degree`).  This is the statement proved here; it is the arithmetic
leaf behind the degree congruences of Lemma 3.4.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem l34ne_orbit_deg_dvd {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C16.Compat D C → Work.GW2.C16.Sec3Hyp D →
    ∀ r : ClassFunction ↥C.P.H0 ℂ, IsIrreducibleCharacter r →
      ∃ a : ℤ, Odd a ∧ ((Work.BG.lamOrbit C r).ncard : ℂ) * r 1 = (D.n : ℂ) * (a : ℂ) := by
  intro hDC hS3 r hr
  -- Remark 3.1: the shape of `r|_U`.
  obtain ⟨a, ha, hcase⟩ := rem31Shape D C hDC hS3 r hr
  -- Transport the constituent of `r|_U` to the abstract group `↥C.P.U` (which has odd order).
  let e : ↥C.P.U ≃* ↥(Uin C) := (Subgroup.subgroupOfEquivOfLe C.P.U_le_H0).symm
  have haU : IsIrreducibleCharacter (ClassFunction.compHom e.toMonoidHom a) :=
    IsIrreducibleCharacter.compHom_of_surjective e.surjective ha
  -- The degree of an irreducible character of an odd-order group is odd.
  obtain ⟨n₁, hn₁odd, hn₁⟩ := exists_odd_nat_degree (K := ↥C.P.U)
    (odd_card_U_of_compat (D := D) (C := C) hDC) haU
  have hdeg : a 1 = (n₁ : ℂ) := by
    have h := hn₁
    simpa [ClassFunction.compHom_apply] using h
  rcases hcase with ⟨hres, hcard⟩ | ⟨a₂, ha₂, hne, hdeg₂, hres, hcard⟩
  · -- Case (i): `r|_U = a` is irreducible and `|Λr| = D.n`.
    have hr1 : r 1 = (n₁ : ℂ) := by
      have h := congrArg (fun f : ClassFunction ↥(Uin C) ℂ => f 1) hres
      simpa [hdeg] using h
    refine ⟨(n₁ : ℤ), ?_, ?_⟩
    · exact_mod_cast hn₁odd
    · rw [hcard, hr1]
      push_cast
      ring
  · -- Case (ii): `r|_U = a + a₂` with `a₂ 1 = a 1` and `2 |Λr| = D.n`.
    have hr1 : r 1 = 2 * (n₁ : ℂ) := by
      have h := congrArg (fun f : ClassFunction ↥(Uin C) ℂ => f 1) hres
      have h' : r 1 = a 1 + a₂ 1 := by simpa using h
      rw [h', hdeg₂, hdeg]
      ring
    refine ⟨(n₁ : ℤ), ?_, ?_⟩
    · exact_mod_cast hn₁odd
    · have hDn : (D.n : ℂ) = 2 * ((lamOrbit C r).ncard : ℂ) := by
        rw [← hcard]; push_cast; ring
      rw [hr1, hDn]
      push_cast
      ring

end Work.BG
