import Mathlib
import Submission.Work.ZassenhausSuzuki.TitsDefs
import Submission.Work.ZassenhausSuzuki.muZ_fixes_tilde
import Submission.Work.ZassenhausSuzuki.muZ_smul_qPt
import Submission.Work.ZassenhausSuzuki.hG_conj_gG_eq_tilde
import Submission.Work.ZassenhausSuzuki.canon_aux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

theorem mu_fix_center_zs {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) {z : Q} (hz1 : z ≠ 1) (hz2 : z * z = 1) :
    Work.ZassenhausSuzuki.TitsDesign.muPt hsplit C z (Work.ZassenhausSuzuki.tildeOf C z)
      = Work.ZassenhausSuzuki.tildeOf C z := by
  -- `z ≠ 1` as an element of `G`, and `z` is its own inverse.
  have hz1G : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_left hz2
  -- **H1** at `z` reads `(g z)⁻¹ = f (z⁻¹) = f z`, i.e. `f z = (g z)⁻¹`.
  have hfz : C.f z = (C.g z)⁻¹ := by
    have h := Work.ZassenhausSuzuki.canon_H1 hsplit C z hz1G
    rw [hzinv] at h
    exact h.symm
  -- The interior `h z · ∼z · (h z)⁻¹` of `muPt` equals `f z` (`tildeOf_eq`, BG 3.1 (j)).
  have hconj : Work.ZassenhausSuzuki.TitsDesign.conjH hsplit C z (Work.ZassenhausSuzuki.tildeOf C z)
      = C.f z := by
    apply Subtype.ext
    simp only [Work.ZassenhausSuzuki.TitsDesign.conjH, Subtype.coe_mk]
    rw [Work.ZassenhausSuzuki.tildeOf_eq hsplit hzass h2 C hz1G]
    group
  -- Hence `μ_z(∼z) = g(f z) = g((g z)⁻¹) = ∼z`.
  rw [Work.ZassenhausSuzuki.TitsDesign.muPt, hconj, hfz]
  rw [Work.ZassenhausSuzuki.tildeOf, ite_eq_right hz1G]

end Work.ZassenhausSuzuki
