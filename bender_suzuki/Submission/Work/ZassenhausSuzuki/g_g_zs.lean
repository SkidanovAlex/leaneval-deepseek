import Mathlib
import Submission.Work.ZassenhausSuzuki.TitsDefs
import Submission.Work.ZassenhausSuzuki.szTildeAux
import Submission.Work.ZassenhausSuzuki.canon_aux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-- **H1** (`NOTES_LEAD_bs_zs_tits.md` §3; design copy `Work.ZassenhausSuzuki.TitsDesign.g_g`):
`g` is an involution on `Q^#`, `C.g (C.g x) = x` for `x ≠ 1`.  (`C : Work.ZassenhausPSL2.Canon
H Q t` is the canonical structure `t x t = g x · h x · t · f x`; `canon_g_g` in
`hG_conj_gG_eq_tilde.lean` has the same conclusion with extra hypotheses, so this is the
hypothesis-weakened form.)  Route: `canon_H1`, `canon_H2`. -/
theorem g_g_zs {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t) (C : Work.ZassenhausPSL2.Canon H Q t)
    {x : Q} (hx : (x : G) ≠ 1) : C.g (C.g x) = x := by
  -- `C.g x ≠ 1`: H1 identifies `(C.g x)⁻¹` with `C.f x⁻¹`, and `f` never vanishes on `Q#`
  -- (`canon_f_ne_one`), so `C.g x` cannot be trivial either.
  have hgne : ((C.g x : Q) : G) ≠ 1 := by
    intro hc
    have h1 := canon_H1 hsplit C x hx
    have h2' := canon_f_ne_one hsplit C (canon_inv_ne_one hx)
    rw [← h1] at h2'
    exact h2' (by simp [hc])
  -- H1 at `x` and at `C.g x`, H2 at `x⁻¹`, glued together:
  -- `(C.g (C.g x))⁻¹ = C.f ((C.g x)⁻¹) = C.f (C.f x⁻¹) = x⁻¹`.
  have hA := canon_H1 hsplit C (C.g x) hgne
  have hB := canon_H1 hsplit C x hx
  have hD := canon_H2 hsplit C (x := x⁻¹) (canon_inv_ne_one hx)
  have key : (C.g (C.g x))⁻¹ = x⁻¹ := by rw [hA, hB, hD]
  exact inv_injective key

end Work.ZassenhausSuzuki
