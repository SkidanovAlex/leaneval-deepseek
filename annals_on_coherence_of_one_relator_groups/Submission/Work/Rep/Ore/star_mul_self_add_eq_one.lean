import Mathlib
import Submission.Work.ORVonNeumann.Rep.GroupVonNeumann

namespace Work.Rep.Ore

/-- The abstract Hilbert-space form of the density/pairing computation.  If `h` is self-adjoint of
dense range, `h * h = star r * r + star s * s`, `v₁ * h = r` and `v₂ * h = s`, then
`star v₁ * v₁ + star v₂ * v₂ = 1`.

The proof pairs the identity against the dense set `ran h`: writing `A = star v₁ * v₁ +
star v₂ * v₂` one has `⟪A (h y), h z⟫ = ⟪r y, r z⟫ + ⟪s y, s z⟫ = ⟪(h * h) y, z⟫ = ⟪h y, h z⟫`
(self-adjointness of `h` enters only in the last step), so `A - 1` annihilates `ran h` in the
sense that `(A - 1) (h y) ⊥ h z` for all `y z`; since `ran h` is dense and `(A - 1) (h y)` is
orthogonal to a dense set it is `0`, and by continuity `A - 1 = 0`. -/
theorem star_mul_self_add_eq_one_aux {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (h v₁ v₂ r s : E →L[ℂ] E) (hself : star h = h) (hd : DenseRange h)
    (hh : h * h = star r * r + star s * s) (hv₁ : v₁ * h = r) (hv₂ : v₂ * h = s) :
    star v₁ * v₁ + star v₂ * v₂ = 1 := by
  -- The pairing of `A = star v₁ * v₁ + star v₂ * v₂` with the dense set `ran h` is the same as
  -- that of the identity.
  have key : ∀ y z : E,
      inner ℂ ((star v₁ * v₁ + star v₂ * v₂) (h y)) (h z) = inner ℂ (h y) (h z) := by
    intro y z
    have e1 : inner ℂ ((star v₁ * v₁ + star v₂ * v₂) (h y)) (h z)
        = inner ℂ (r y) (r z) + inner ℂ (s y) (s z) := by
      rw [add_apply, mul_apply_eq_comp, mul_apply_eq_comp,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
        inner_add_left, ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.adjoint_inner_left]
      rw [← mul_apply_eq_comp v₁ h y, hv₁, ← mul_apply_eq_comp v₁ h z, hv₁,
          ← mul_apply_eq_comp v₂ h y, hv₂, ← mul_apply_eq_comp v₂ h z, hv₂]
    have hsh : (star h) (h y) = h (h y) := by rw [hself]
    have hstep : inner ℂ ((h * h) y) z = inner ℂ (h y) (h z) := by
      rw [mul_apply_eq_comp, ← hsh, ContinuousLinearMap.star_eq_adjoint,
        ContinuousLinearMap.adjoint_inner_left]
    have e2 : inner ℂ (h y) (h z) = inner ℂ (r y) (r z) + inner ℂ (s y) (s z) := by
      rw [← hstep, hh, add_apply, mul_apply_eq_comp, mul_apply_eq_comp,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.star_eq_adjoint,
        inner_add_left, ContinuousLinearMap.adjoint_inner_left,
        ContinuousLinearMap.adjoint_inner_left]
    rw [e1, e2]
  -- Hence `(A - 1) (h y)` is orthogonal to `ran h`, and being orthogonal to a dense set it is `0`.
  have hzero : ∀ y : E, ((star v₁ * v₁ + star v₂ * v₂) - 1) (h y) = 0 := by
    intro y
    have horth : ∀ z : E,
        inner ℂ (((star v₁ * v₁ + star v₂ * v₂) - 1) (h y)) (h z) = 0 := by
      intro z
      rw [sub_apply, one_apply_eq_self, inner_sub_left, key y z, sub_self]
    have hself' : inner ℂ (((star v₁ * v₁ + star v₂ * v₂) - 1) (h y))
        (((star v₁ * v₁ + star v₂ * v₂) - 1) (h y)) = 0 := by
      have heq := hd.equalizer
        (g := fun x : E => inner ℂ (((star v₁ * v₁ + star v₂ * v₂) - 1) (h y)) x)
        (h := fun _ => (0 : ℂ)) (by fun_prop) continuous_const ?_
      · rw [funext_iff] at heq
        exact heq _
      · funext z
        exact horth z
    rwa [inner_self_eq_zero] at hself'
  -- `A - 1` is continuous and vanishes on the dense set `ran h`, so it vanishes everywhere.
  exact sub_eq_zero.mp (ContinuousLinearMap.ext fun x =>
    hd.induction_on x
      (isClosed_singleton.preimage ((star v₁ * v₁ + star v₂ * v₂) - 1).continuous) hzero)

/-- The density/pairing computation: if `h` is self-adjoint of dense range, `h * h = star r * r +
star s * s`, `v₁ * h = r` and `v₂ * h = s`, then `star v₁ * v₁ + star v₂ * v₂ = 1`.

Route: `A := star v₁ * v₁ + star v₂ * v₂`.  For all `y z` one has
`⟪A (h y), h z⟫ = ⟪v₁ (h y), v₁ (h z)⟫ + ⟪v₂ (h y), v₂ (h z)⟫ = ⟪r y, r z⟫ + ⟪s y, s z⟫
= ⟪(h * h) y, z⟫ = ⟪h y, h z⟫`, so `A - 1` kills the dense set `ran h` in the sense that
`⟪(A - 1) (h y), h z⟫ = 0` for all `y z`; the closedness of the zero set and the density of
`ran h` then give `(A - 1) (h y) = 0`, and a second application gives `A - 1 = 0`.-/
theorem star_mul_self_add_eq_one {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] (h v₁ v₂ r s : ↥(Work.ORVonNeumann.groupVonNeumann G)) (hself : star h = h) (hd : DenseRange (h : Work.ORVonNeumann.boundedEnd G)) (hh : h * h = star r * r + star s * s) (hv₁ : v₁ * h = r) (hv₂ : v₂ * h = s) : star v₁ * v₁ + star v₂ * v₂ = 1 := by
  -- All the structure lives in the underlying algebra `B(ℓ²(G))`; coerce the hypotheses.
  have hself' : star (h : Work.ORVonNeumann.boundedEnd G) = (h : Work.ORVonNeumann.boundedEnd G) :=
    congrArg Subtype.val hself
  have hh' : (h : Work.ORVonNeumann.boundedEnd G) * (h : Work.ORVonNeumann.boundedEnd G)
      = star (r : Work.ORVonNeumann.boundedEnd G) * (r : Work.ORVonNeumann.boundedEnd G)
        + star (s : Work.ORVonNeumann.boundedEnd G)
            * (s : Work.ORVonNeumann.boundedEnd G) :=
    congrArg Subtype.val hh
  have hv₁' : (v₁ : Work.ORVonNeumann.boundedEnd G) * (h : Work.ORVonNeumann.boundedEnd G)
      = (r : Work.ORVonNeumann.boundedEnd G) :=
    congrArg Subtype.val hv₁
  have hv₂' : (v₂ : Work.ORVonNeumann.boundedEnd G) * (h : Work.ORVonNeumann.boundedEnd G)
      = (s : Work.ORVonNeumann.boundedEnd G) :=
    congrArg Subtype.val hv₂
  have hkey := star_mul_self_add_eq_one_aux
    (h := (h : Work.ORVonNeumann.boundedEnd G))
    (v₁ := (v₁ : Work.ORVonNeumann.boundedEnd G))
    (v₂ := (v₂ : Work.ORVonNeumann.boundedEnd G))
    (r := (r : Work.ORVonNeumann.boundedEnd G))
    (s := (s : Work.ORVonNeumann.boundedEnd G)) hself' hd hh' hv₁' hv₂'
  refine Subtype.ext ?_
  exact hkey

end Work.Rep.Ore
