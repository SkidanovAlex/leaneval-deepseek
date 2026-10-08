import Mathlib
import Submission.Work.ZassenhausSuzuki.szTildeAux
import Submission.Work.ZassenhausSuzuki.canon_relations
import Submission.Work.RankOneUniqueness.qPt_injective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.muZ_smul_qPt` — the reflection `μ z` on the `Q`-labelling of `Ω`

With `μ z := t · h(z)` (the reflection attached to `z ∈ Q`, an involution by `t_mul_h_sq`)
the involution `μ z` acts on the labelling `x ↦ qPt H t x` of `Ω ∖ {∞}` by conjugation with
`h(z)`:

`(t · h z) • qPt H t x = qPt H t y`,  where `y = h(z)⁻¹ · g(x) · h(z)`.

The proof is the group computation
`(t h_z x t)⁻¹ · (y t) = f(x)⁻¹ · h(z)⁻¹ · h(x) ∈ H` (using `t h_z t = h_z⁻¹` and the
canonical form `t x t = g(x) h(x) t f(x)`), which exhibits the two cosets `t h_z x t · H` and
`y t · H` as the same point of `Ω = G ⧸ H`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Submission.Blueprint

namespace Work.ZassenhausSuzuki

theorem muZ_smul_qPt {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) {z x : Q} (hx : (x : G) ≠ 1) {y : Q}
    (hy : (y : G) = (Work.ZassenhausSuzuki.hG C z)⁻¹ * Work.ZassenhausSuzuki.gG C x
      * Work.ZassenhausSuzuki.hG C z) :
    (t * Work.ZassenhausSuzuki.hG C z) • Work.RankOneUniqueness.qPt H t x
      = Work.RankOneUniqueness.qPt H t y := by
  have ht2 : t * t = 1 := canon_t_mul_t hsplit
  have htinv : t⁻¹ = t := canon_t_inv hsplit
  -- the canonical form of `t x t`
  have hspec : t * (x : G) * t = gG C x * hG C x * t * fG C x := C.spec x hx
  -- `t` inverts `D ∋ h(z)`, `h(x)`
  have hzt : t * hG C z * t = (hG C z)⁻¹ := canon_t_conj_inv_D hsplit hzass h2 (C.h z).2
  have hzi : (hG C z)⁻¹ * t = t * hG C z := by
    calc (hG C z)⁻¹ * t = (t * hG C z * t) * t := by rw [hzt]
      _ = t * hG C z * (t * t) := by group
      _ = t * hG C z := by rw [ht2, mul_one]
  have hinv1 : (t * hG C z * (x : G) * t)⁻¹ = t * (x : G)⁻¹ * (hG C z)⁻¹ * t := by
    simp only [mul_inv_rev, htinv]; group
  have hinv2 : t * (x : G)⁻¹ * t = (t * (x : G) * t)⁻¹ := by
    simp only [mul_inv_rev, htinv]; group
  have h4 : t * ((hG C x)⁻¹ * hG C z) * t = ((hG C x)⁻¹ * hG C z)⁻¹ :=
    canon_t_conj_inv_D hsplit hzass h2
      ((twoPoint H t).mul_mem ((twoPoint H t).inv_mem (C.h x).2) (C.h z).2)
  -- the whole computation
  have hEX : (t * hG C z * (x : G) * t)⁻¹ * ((hG C z)⁻¹ * gG C x * hG C z * t)
      = (fG C x)⁻¹ * (hG C z)⁻¹ * hG C x := by
    calc (t * hG C z * (x : G) * t)⁻¹ * ((hG C z)⁻¹ * gG C x * hG C z * t)
        = t * (x : G)⁻¹ * (hG C z)⁻¹ * t * (hG C z)⁻¹ * gG C x * hG C z * t := by
            rw [hinv1]; group
      _ = t * (x : G)⁻¹ * ((hG C z)⁻¹ * t) * (hG C z)⁻¹ * gG C x * hG C z * t := by
            group
      _ = t * (x : G)⁻¹ * (t * hG C z) * (hG C z)⁻¹ * gG C x * hG C z * t := by
            rw [hzi]
      _ = t * (x : G)⁻¹ * t * gG C x * hG C z * t := by group
      _ = (t * (x : G) * t)⁻¹ * gG C x * hG C z * t := by rw [hinv2]
      _ = (gG C x * hG C x * t * fG C x)⁻¹ * gG C x * hG C z * t := by rw [hspec]
      _ = (fG C x)⁻¹ * t * (hG C x)⁻¹ * (gG C x)⁻¹ * gG C x * hG C z * t := by
            simp only [mul_inv_rev, htinv]; group
      _ = (fG C x)⁻¹ * t * (hG C x)⁻¹ * hG C z * t := by group
      _ = (fG C x)⁻¹ * (t * ((hG C x)⁻¹ * hG C z) * t) := by group
      _ = (fG C x)⁻¹ * ((hG C x)⁻¹ * hG C z)⁻¹ := by rw [h4]
      _ = (fG C x)⁻¹ * (hG C z)⁻¹ * hG C x := by group
  -- the difference of the two representatives lies in `H`
  have hmem : (t * hG C z * (x : G) * t)⁻¹ * ((hG C z)⁻¹ * gG C x * hG C z * t) ∈ H := by
    rw [hEX]
    exact H.mul_mem (H.mul_mem (H.inv_mem (hsplit.le (C.f x).2))
      (Subgroup.mem_inf.mp ((twoPoint H t).inv_mem (C.h z).2)).1)
      (Subgroup.mem_inf.mp (C.h x).2).1
  have hmain : ((t * hG C z) * ((x : G) * t))⁻¹ * ((y : G) * t) ∈ H := by
    have hmain' : (t * hG C z * (x : G) * t)⁻¹ * ((y : G) * t) ∈ H := by
      rw [hy]
      exact hmem
    simpa only [mul_assoc] using hmain'
  rw [Work.RankOneUniqueness.qPt_def, Work.RankOneUniqueness.qPt_def,
    Work.RankOneUniqueness.smul_mk]
  exact QuotientGroup.eq.mpr hmain

end Work.ZassenhausSuzuki
