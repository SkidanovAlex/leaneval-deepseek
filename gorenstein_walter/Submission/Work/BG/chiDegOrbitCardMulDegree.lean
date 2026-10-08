import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.rem31Shape

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem chiDegOrbitCardMulDegree {G : Type} [Group G] [Finite G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    (hDC : Work.GW2.C16.Compat D C) (hS3 : Work.GW2.C16.Sec3Hyp D) (hn4 : D.n = 4)
    (θ : ClassFunction ↥C.P.H0 ℂ) (hθ : IsIrreducibleCharacter θ) :
    ∃ z : ℤ, ((Work.BG.lamOrbit C θ).ncard : ℂ) * θ 1 = 4 * (z : ℂ) := by
  -- Remark 3.1 (`Work.BG.rem31Shape`): `θ|_U` is either a single irreducible `a`
  -- (then `|Λθ| = D.n = 4`) or a sum `a + a₂` of two distinct irreducibles of equal
  -- degree (then `2 |Λθ| = D.n = 4`, i.e. `|Λθ| = 2`).
  obtain ⟨a, ha, hcase⟩ := rem31Shape D C hDC hS3 θ hθ
  -- the degree `a 1` of any irreducible character is a natural number
  obtain ⟨d, -, hd⟩ :=
    irreducibleCharacter_apply_one_eq_pos_natCast (⟨a, ha⟩ : IrreducibleCharacter ↥(Uin C))
  have hd' : a 1 = (d : ℂ) := by simpa using hd
  -- `θ 1` is the value at `1` of the restriction of `θ` to `U`
  have hθ1 : θ 1 = (ClassFunction.restrict (Uin C) θ) 1 := by simp
  rcases hcase with ⟨hres, hcard⟩ | ⟨a₂, ha₂, hne, hdeg, hres, hcard⟩
  · -- Case (i): `θ|_U = a` is irreducible, and `|Λθ| = D.n = 4`.
    -- Then `|Λθ| · θ(1) = 4 · a(1)`.
    refine ⟨(d : ℤ), ?_⟩
    rw [hθ1, hres, hcard, hn4, hd']
    push_cast
    ring
  · -- Case (ii): `θ|_U = a + a₂` with `a₂ ≠ a`, `a₂(1) = a(1)`, and `2 |Λθ| = D.n = 4`.
    -- Then `θ(1) = 2 a(1)` and `|Λθ| = 2`, so `|Λθ| · θ(1) = 4 · a(1)`.
    refine ⟨(d : ℤ), ?_⟩
    have hval : (a + a₂ : ClassFunction ↥(Uin C) ℂ) 1 = 2 * (d : ℂ) := by
      rw [ClassFunction.add_apply, hd', hdeg, hd']
      ring
    have hnc : (lamOrbit C θ).ncard = 2 := by
      have h2 : 2 * (lamOrbit C θ).ncard = 4 := by rw [hcard, hn4]
      omega
    rw [hθ1, hres, hval, hnc]
    push_cast
    ring

end Work.BG
