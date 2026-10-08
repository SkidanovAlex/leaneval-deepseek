import Mathlib
import Submission.Work.BG.lemma36Defs
import Submission.Work.BG.isCharacterRestrict

/-!
# Step 1 of the repaired route to BG Lemma 3.6: the degree count

If `a ∈ Irr(U)` is a constituent of `χ|_U` for an irreducible character `χ` of `G`, with
multiplicity `c = ⟨χ|_U, a⟩`, then

  `|S·a| · c · a(1) ≤ χ(1)`.

Proof: `χ|_U` is a genuine character of `U` (`isCharacterRestrict`), so
`χ|_U = ∑_{b ∈ Irr U} m_b·b` with `m_b = ⟨χ|_U, b⟩ ∈ ℕ`
(`IsCharacter.exists_natFinsupp_eq_sum`), and `χ(1) = ∑_b m_b·b(1)`.  Every element of the
`S`-orbit of `a` is again a constituent with the same multiplicity `m_a = c` and the same degree
(`S`-invariance of `classFunction.inner` via `inner_compHom_mulEquiv`, using that `χ|_U` is
invariant under the `S`-conjugation action `L33D.phiS` on `U`), so the orbit contributes
`|S·a|·c·a(1)` to `χ(1)`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

variable {G : Type} [Group G] [Finite G] [Fintype G]

/-- Elementwise form: restriction to `U` of a class function of `G` is invariant under the
conjugation action `L33D.phiS` of `S` on `U`. -/
theorem restrict_phiS_apply (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (s : ↥(D.S)) (χ : ClassFunction G ℂ) (u : ↥(Uin C)) :
    (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ)) (L33D.phiS D C hDC s u) =
      (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ)) u := by
  simp only [ClassFunction.restrict_apply]
  rw [L33D.phiS_apply D C hDC s u]
  exact χ.conj_eq _ _

/-- Restriction to `U = ↥(Uin C)` of a class function of `G` is invariant under the
conjugation action `L33D.phiS` of `S` on `U` (a class function of `G` does not change under
conjugation by `s ∈ S ⊆ G`). -/
theorem compHom_phiS_restrict (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    (s : ↥(D.S)) (χ : ClassFunction G ℂ) :
    ClassFunction.compHom (L33D.phiS D C hDC s).toMonoidHom
        (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ)) =
      ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ) := by
  ext u
  rw [ClassFunction.compHom_apply]
  show (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ))
      (L33D.phiS D C hDC s u) =
    (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ)) u
  exact restrict_phiS_apply D C hDC s χ u

/-- Multiplicities in `χ|_U` are `S`-invariant. -/
theorem inner_phiS_eq (D : BGData G) (C : Sec2Ctx G) (hDC : Compat D C)
    [Fintype ↥(Uin C)] [Invertible (Nat.card ↥(Uin C) : ℂ)]
    (s : ↥(D.S)) (χ : ClassFunction G ℂ) (b : ClassFunction ↥(Uin C) ℂ) :
    ClassFunction.inner (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ))
        (ClassFunction.compHom (L33D.phiS D C hDC s).toMonoidHom b) =
      ClassFunction.inner (ClassFunction.restrict (Uin C) (ClassFunction.restrict C.P.H0 χ)) b := by
  conv_lhs => rw [← compHom_phiS_restrict D C hDC s χ]
  exact ClassFunction.inner_compHom_mulEquiv (L33D.phiS D C hDC s) _ _

end Work.BG
