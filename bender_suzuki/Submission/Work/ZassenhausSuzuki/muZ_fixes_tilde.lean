import Mathlib
import Submission.Work.ZassenhausSuzuki.szTildeAux
import Submission.Work.ZassenhausSuzuki.canon_relations

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-!
# The Moufang involution `μ_z = t·h(z)` fixes the point `qPt(∼z)`

With `μ_z = t · h(z)` (`h(z)` the `D`-component of the canonical form of `t z t`, the
`muZ` of `Submission/Work/ZassenhausSuzuki/card_fixTheta_le_six_zs.lean`) and `∼ = tildeOf C`
the Suzuki reflection `∼x = g (g x)⁻¹` (BG 3.1 (j)), the point of `Ω = G ⧸ H` attached to `∼z`
is fixed by `μ_z`, for every involution `z ∈ Q#` (no centrality hypothesis is needed).

The proof is a direct consequence of the *structure equation* of the reflection, BG 3.3 (a)
(`tildeOf_conj_mu` in `szTildeAux.lean`):

  `(∼z)⁻¹ · (t h_z) · (∼z) = (t h_z)⁻¹ · z · (t h_z)`,

conjugated by the involution `t` (which inverts `D = twoPoint H t`): with `u := ∼z ∈ Q` and
`h := h(z) ∈ D`,

  `(u t)⁻¹ μ_z (u t) = t (u⁻¹ μ_z u) t = h · z · h⁻¹ ∈ H`,

so `μ_z` lies in the point stabiliser `H^{ut}` of `qPt H t u = u t H`, i.e. it fixes that point.
-/

theorem muZ_fixes_tilde {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) {z : Q}
    (hz1 : (z : G) ≠ 1) (hz2 : z * z = 1) :
    (t * Work.ZassenhausSuzuki.hG C z) • Work.RankOneUniqueness.qPt H t
        (Work.ZassenhausSuzuki.tildeOf C z)
      = Work.RankOneUniqueness.qPt H t (Work.ZassenhausSuzuki.tildeOf C z) := by
  classical
  -- `u := ∼z ∈ Q`, `h := h(z) ∈ D`, `μ_z = t·h`.
  set u : G := ((Work.ZassenhausSuzuki.tildeOf C z : Q) : G) with hu
  set h : G := Work.ZassenhausSuzuki.hG C z with hh
  have ht2 : t * t = 1 := canon_t_mul_t hsplit
  have htinv : t⁻¹ = t := canon_t_inv hsplit
  -- `t` inverts `D ∋ h`.
  have hth : t * h * t = h⁻¹ := by
    rw [hh]; exact canon_t_conj_inv_D hsplit hzass h2 (C.h z).2
  have hth' : t * h⁻¹ * t = h := by
    rw [← hth]
    rw [show t * (t * h * t) * t = (t * t) * h * (t * t) from by group, ht2]
    group
  -- BG 3.3 (a), with the right factor `(t h)⁻¹` expanded as `h⁻¹ · t`.
  have hconj : u⁻¹ * (t * h) * u = h⁻¹ * (t * (z : G) * t) * h := by
    have h1 := Work.ZassenhausSuzuki.tildeOf_conj_mu hsplit hzass h2 C hz1 hz2
    rw [← hu, ← hh] at h1
    rw [show (t * h)⁻¹ = h⁻¹ * t from by rw [mul_inv_rev, htinv]] at h1
    rw [h1]
    group
  -- Conjugation by `t` turns the above into the desired `h · z · h⁻¹`.
  have hXu : (u * t)⁻¹ * (t * h) * (u * t) = h * (z : G) * h⁻¹ := by
    have h1 : (u * t)⁻¹ * (t * h) * (u * t) = t * (u⁻¹ * (t * h) * u) * t := by
      rw [mul_inv_rev, htinv]; group
    rw [h1, hconj]
    rw [show t * (h⁻¹ * (t * (z : G) * t) * h) * t
          = (t * h⁻¹ * t) * (z : G) * (t * h * t) from by group, hth', hth]
  -- The point `qPt H t u = u·t·H` is fixed by `μ_z = t·h`.
  rw [Work.RankOneUniqueness.qPt_def, Work.RankOneUniqueness.smul_mk, QuotientGroup.eq]
  have hzG2 : (z : G) * (z : G) = 1 := by rw [← Subgroup.coe_mul, hz2, Subgroup.coe_one]
  -- `(μ_z·(ut))⁻¹·(ut) = (u t)⁻¹ μ_z (u t)⁻¹⁻¹` reduces to the previous computation.
  have hZ : ((t * h) * (u * t))⁻¹ * (u * t) = h * (z : G) * h⁻¹ := by
    have h2' : ((t * h) * (u * t))⁻¹ * (u * t)
        = ((u * t)⁻¹ * (t * h) * (u * t))⁻¹ := by group
    rw [h2', hXu, mul_inv_rev, mul_inv_rev, inv_inv, inv_eq_of_mul_eq_one_right hzG2]
    group
  rw [hZ]
  exact H.mul_mem (H.mul_mem ((C.h z).2.1) (hsplit.le z.2)) (H.inv_mem ((C.h z).2.1))

end Work.ZassenhausSuzuki
