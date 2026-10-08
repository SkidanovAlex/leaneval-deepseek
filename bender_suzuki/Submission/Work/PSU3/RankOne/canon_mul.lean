import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.RankOneUniqueness.Basic
import Submission.Work.PSU3.RankOne.H16

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Peterfalvi II, Ch. VII §1: identity H6 for the canonical form

`H6`: the canonical data of `x * y` is computed from the canonical data of `x`, `y` and of
`f(x) g(y)`.  If

* `t x t = gx · dx · t · fx`,  `t y t = gy · dy · t · fy`,  `t (fx gy) t = gz · dz · t · fz`

with `gx, fx, gy, fy, gz, fz ∈ Q` and `dx, dy, dz ∈ D = H ∩ Hᵗ`, then

* `t (x y) t = (gx · (dx gz dx⁻¹)) · (dx dz dy) · t · ((t dy t)⁻¹ · fz · (t dy t) · fy)`.

The whole content is: conjugation by the involution `t` is multiplicative, `Q` is `H`-normal,
and `D` is stable under conjugation by `t`; the rest is the group identity
```
t (x y) t = (gx dx t fx)(gy dy t fy)
          = gx dx (t (fx gy) t) (t dy t) fy
          = gx dx gz dz (t fz t) dy t fy
          = gx (dx gz dx⁻¹) (dx dz dy) t ((t dy t)⁻¹ fz (t dy t) fy).
```
-/

namespace Work.PSU3.RankOne

open Work.RankOneUniqueness

/-- **H6.** The canonical data of a product. -/
theorem canon_mul {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) {x y gx dx fx gy dy fy gz dz fz : G}
    (hx : Work.PSU3.Canon3 H Q t x gx dx fx) (hy : Work.PSU3.Canon3 H Q t y gy dy fy)
    (hz : Work.PSU3.Canon3 H Q t (fx * gy) gz dz fz) :
    Work.PSU3.Canon3 H Q t (x * y) (gx * (dx * gz * dx⁻¹)) (dx * dz * dy)
      ((t * dy * t)⁻¹ * fz * (t * dy * t) * fy) := by
  obtain ⟨hgx, hdx, hfx, heqx⟩ := hx
  obtain ⟨hgy, hdy, hfy, heqy⟩ := hy
  obtain ⟨hgz, hdz, hfz, heqz⟩ := hz
  have ht : t * t = 1 := mul_self_eq_one h
  have hi : t⁻¹ = t := inv_eq_self h
  have ht2 : ∀ a : G, t * (t * a) = a := fun a => by rw [← mul_assoc, ht, one_mul]
  have htdyH : t * dy * t ∈ H := t_mul_mul_t_mem_of_mem_twoPoint ht hdy
  have hdxH : dx ∈ H := (mem_twoPoint_iff.mp hdx).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `gx * (dx gz dx⁻¹) ∈ Q`
    exact Q.mul_mem hgx (conj_mem_of_mem h hdxH hgz)
  · -- `dx dz dy ∈ D`
    exact (Submission.Blueprint.twoPoint H t).mul_mem
      ((Submission.Blueprint.twoPoint H t).mul_mem hdx hdz) hdy
  · -- `(t dy t)⁻¹ fz (t dy t) fy ∈ Q`
    refine Q.mul_mem ?_ hfy
    have hconj := conj_mem_of_mem h (H.inv_mem htdyH) hfz
    simpa only [inv_inv] using hconj
  · -- the group identity
    have hc : ∀ a b : G, t * (a * b) * t = (t * a * t) * (t * b * t) := by
      intro a b
      have hh := map_mul (MulAut.conj t) a b
      simpa only [MulAut.conj_apply, hi] using hh
    rw [hc x y, heqx, heqy]
    rw [show (gx * dx * t * fx) * (gy * dy * t * fy)
            = gx * dx * (t * (fx * gy) * t) * (t * dy * t) * fy from by
          simp only [mul_assoc, ht2],
      heqz,
      show gx * dx * (gz * dz * t * fz) * (t * dy * t) * fy
            = gx * dx * gz * dz * (t * fz * t) * dy * t * fy from by
          simp only [mul_assoc],
      show gx * dx * gz * dz * (t * fz * t) * dy * t * fy
            = gx * (dx * gz * dx⁻¹) * (dx * dz * dy) * t
                * ((t * dy * t)⁻¹ * fz * (t * dy * t) * fy) from by
          simp only [mul_assoc, ht2, mul_inv_rev, hi,
            inv_mul_cancel_left, mul_inv_cancel_left]]

end Work.PSU3.RankOne
