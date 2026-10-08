import Mathlib
import Submission.Work.ZassenhausSuzuki.ttc_defs
import Submission.Work.ZassenhausSuzuki.exists_mulD_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-- **The multiplier of `h(z_w)`.**  For `w ≠ 0` and `z_w = zc e w`,
`mulD (h(z_w)) = mulD (h(z_1)) / w²`, where `mulD htorus d = lamOf d · θ(lamOf d)` is the
multiplier of `d ∈ D` on the centre of `Q` (`ttc_defs`).

Route: pick `d ∈ D` with `mulD hsplit htorus d = w` (as in
`Work/ZassenhausSuzuki.exists_mulD_eq`; re-derive the existence in this file with
`units_mul_map_surjective` + `torusLambda_surjective_of_split` if that module is not available),
so `z_w = conjQ hsplit d (zc e 1)` by `conjQ_zc` (`ttc_defs`).  Then `canon_H6`
(`h(d x d⁻¹) = d⁻¹ d⁻¹ h(x)`, in `Submission/Work/ZassenhausSuzuki/canon_aux.lean`) gives
`C.h (zc e w) = d⁻¹ * d⁻¹ * C.h (zc e 1)` in `twoPoint H t` (apply `Subtype.ext` to the coercion
formula); `mulD` is multiplicative (`mulD_mul`, `mulD_inv`, `mulD_one` in `ttc_defs`), and in
characteristic two `w⁻¹ * w⁻¹ * c₀ = c₀ / w²`. -/
theorem mulD_h_zc {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθodd : Odd (orderOf θ))
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x))
    (C : Work.ZassenhausPSL2.Canon H Q t)
    {w : GaloisField 2 m} (hw : w ≠ 0) :
    Work.ZassenhausSuzuki.mulD hsplit htorus (C.h (Work.ZassenhausSuzuki.zc e w))
      = Work.ZassenhausSuzuki.mulD hsplit htorus (C.h (Work.ZassenhausSuzuki.zc e 1)) / w ^ 2 := by
  classical
  -- Pick `d ∈ D = twoPoint H t` with `mulD hsplit htorus d = w`.
  obtain ⟨d, hd_eq⟩ := exists_mulD_eq hsplit hzass h2 hθodd htorus hw
  -- `z_1 ≠ 1`, so `canon_H6` applies at `x = z_1`.
  have hxQ : zc e (1 : GaloisField 2 m) ≠ (1 : Q) := (zc_ne_one_iff e).mpr one_ne_zero
  have hx : ((zc e (1 : GaloisField 2 m) : Q) : G) ≠ 1 := fun hc => hxQ (Subtype.ext hc)
  -- `z_w` is the `d`-conjugate of `z_1`.
  have hconj : zc e w = conjQ hsplit d (zc e (1 : GaloisField 2 m)) := by
    have h := conjQ_zc hsplit htorus d (1 : GaloisField 2 m)
    rw [mul_one, hd_eq] at h
    exact h.symm
  -- `canon_H6` (Hua): `h(d x d⁻¹) = d⁻¹ d⁻¹ h(x)`.
  have hH6 := canon_H6 hsplit hzass h2 C d (zc e (1 : GaloisField 2 m)) hx
    (mem_conj_mem hsplit d.2 (zc e (1 : GaloisField 2 m)).2)
  have hkey : C.h (zc e w) = d⁻¹ * d⁻¹ * C.h (zc e (1 : GaloisField 2 m)) := by
    rw [hconj]
    refine Subtype.ext ?_
    simpa [conjQ, conjQ_coe] using hH6
  -- `mulD` turns conjugation by `d` into division by `mulD d = w`.
  rw [hkey]
  rw [mulD_mul hsplit htorus (d⁻¹ * d⁻¹) (C.h (zc e (1 : GaloisField 2 m))),
      mulD_mul hsplit htorus d⁻¹ d⁻¹, mulD_inv hsplit htorus d]
  rw [hd_eq, div_eq_mul_inv, pow_two, mul_inv_rev]
  ring

end Work.ZassenhausSuzuki
