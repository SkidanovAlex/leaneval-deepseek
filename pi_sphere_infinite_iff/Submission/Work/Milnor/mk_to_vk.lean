import Mathlib
import Submission.Work.Milnor.VBundle
import Submission.Work.Milnor.Clutch

namespace Work.Milnor

open scoped Manifold ContDiff Topology
open Submission.Milnor

noncomputable section

/-! ## The inclusion `Mk k → Vk k` on the level of the two-chart descriptions

Both `Mk k` and `Vk k` are quotients of two copies of `MSpace = ℝ⁴ × S³`, respectively
`MSpace8 = ℝ⁴ × ℍ`, glued by the same clutching map (the fibre of `Mk k` is the unit sphere `S³`
of the quaternion line `ℍ`, and the clutching map `clutch` only uses the twist of the fibre, which
agrees with `vTwist`).  The inclusion of the unit sphere into the quaternion line, applied in each
chart, is therefore compatible with the two gluing relations, and descends to an injective map
`Mk k → Vk k` because a point of the glued space determines the chart point (up to the gluing).
-/

/-- The coerced value of the clutching function `clutch m` of the sphere bundle is the twist
`vTwist m` of the quaternion line: both are `q ↦ q ^ m * y * q⁻¹`. -/
theorem coe_clutch (m : ℤ) (u y : QS3) :
    ((clutch m (u, y) : QS3) : Quaternion ℝ) =
      vTwist m (u : Quaternion ℝ) (y : Quaternion ℝ) := rfl

/-- The gluing map of the vector-bundle charts, evaluated through the coercion of the open partial
homeomorphism. -/
theorem vData_φ_apply (k : ℤ) (p : MSpace8) :
    (((vData k).φ p : MSpace8)) = vMap k p := rfl

/-- The underlying map on the disjoint union of two copies of `MSpace`: the unit-sphere fibre is
included in the quaternion line in each chart. -/
def mkToVkAux (k : ℤ) : MSpace ⊕ MSpace → Vk k :=
  Sum.elim (fun p : MSpace => (vData k).ιX (p.1, (p.2 : Quaternion ℝ)))
           (fun p : MSpace => (vData k).ιY (p.1, (p.2 : Quaternion ℝ)))

@[simp] theorem mkToVkAux_inl (k : ℤ) (p : MSpace) :
    mkToVkAux k (Sum.inl p) = (vData k).ιX (p.1, (p.2 : Quaternion ℝ)) := rfl

@[simp] theorem mkToVkAux_inr (k : ℤ) (p : MSpace) :
    mkToVkAux k (Sum.inr p) = (vData k).ιY (p.1, (p.2 : Quaternion ℝ)) := rfl

/-- The inclusion is compatible with the gluing relation: two identified chart points have
identified images, because the two gluing maps have the same formula and the twist
`clutch` of the sphere agrees with the twist `vTwist` of the quaternion line. -/
theorem mkToVkAux_respects (k : ℤ) {a b : MSpace ⊕ MSpace}
    (h : (clutchData k).rel a b) : mkToVkAux k a = mkToVkAux k b := by
  rcases a with p | p <;> rcases b with q | q
  · rw [mkToVkAux_inl, mkToVkAux_inl]
    exact congrArg (fun z : MSpace => (vData k).ιX (z.1, (z.2 : Quaternion ℝ))) h
  · obtain ⟨hp, hq⟩ := h
    rw [mkToVkAux_inl, mkToVkAux_inr, (vData k).ιX_eq_ιY_iff]
    refine ⟨hp, ?_⟩
    have hq' : clutchMap k p = q := hq
    subst hq'
    rw [vData_φ_apply, vMap, clutchMap]
    exact Prod.ext rfl (coe_clutch (-k) (unitDir p.1) p.2).symm
  · obtain ⟨hq, hp⟩ := h
    rw [mkToVkAux_inr, mkToVkAux_inl, (vData k).ιY_eq_ιX_iff]
    refine ⟨hq, ?_⟩
    have hp' : clutchMap k q = p := hp.symm
    subst hp'
    rw [vData_φ_apply, vMap, clutchMap]
    exact Prod.ext rfl (coe_clutch (-k) (unitDir q.1) q.2).symm
  · rw [mkToVkAux_inr, mkToVkAux_inr]
    exact congrArg (fun z : MSpace => (vData k).ιY (z.1, (z.2 : Quaternion ℝ))) h

/-- **The inclusion `Mk k → Vk k`**, obtained by descending the chartwise inclusion of the fibre
`S³ ⊂ ℍ` to the two glued spaces. -/
def mkToVkFun (k : ℤ) : Mk k → Vk k :=
  Quotient.lift (mkToVkAux k) (fun _ _ h => mkToVkAux_respects k h)

@[simp] theorem mkToVk_ιX (k : ℤ) (p : MSpace) :
    mkToVkFun k ((clutchData k).ιX p) = (vData k).ιX (p.1, (p.2 : Quaternion ℝ)) := rfl

@[simp] theorem mkToVk_ιY (k : ℤ) (p : MSpace) :
    mkToVkFun k ((clutchData k).ιY p) = (vData k).ιY (p.1, (p.2 : Quaternion ℝ)) := rfl

/-- The chartwise inclusion is injective: a chart point of `Mk k` can be recovered from its image
in `Vk k` (the two charts are distinguished, and within one chart the inclusion `S³ ⊂ ℍ` of the
fibre is injective, the base coordinate being carried along unchanged). -/
theorem mkToVkFun_injective (k : ℤ) : Function.Injective (mkToVkFun k) := by
  intro z z' h
  have hz : (∃ p, (clutchData k).ιX p = z) ∨ (∃ p, (clutchData k).ιY p = z) := by
    have h0 : z ∈ Set.range (clutchData k).ιX ∪ Set.range (clutchData k).ιY := by
      rw [(clutchData k).range_ιX_union_range_ιY]; exact Set.mem_univ z
    rwa [Set.mem_union, Set.mem_range, Set.mem_range] at h0
  have hz' : (∃ p, (clutchData k).ιX p = z') ∨ (∃ p, (clutchData k).ιY p = z') := by
    have h0 : z' ∈ Set.range (clutchData k).ιX ∪ Set.range (clutchData k).ιY := by
      rw [(clutchData k).range_ιX_union_range_ιY]; exact Set.mem_univ z'
    rwa [Set.mem_union, Set.mem_range, Set.mem_range] at h0
  obtain ⟨p, rfl⟩ | ⟨p, rfl⟩ := hz
  · obtain ⟨q, rfl⟩ | ⟨q, rfl⟩ := hz'
    · rw [mkToVk_ιX, mkToVk_ιX] at h
      have h' := (vData k).ιX_injective h
      rw [Prod.mk.injEq] at h'
      obtain ⟨h1, h2⟩ := h'
      rw [Prod.ext h1 (Subtype.ext h2)]
    · rw [mkToVk_ιX, mkToVk_ιY] at h
      obtain ⟨hp, hmap⟩ := (vData k).ιX_eq_ιY_iff.mp h
      have h1 : invBase p.1 = q.1 := by
        simpa only [vData_φ_apply, vMap] using congrArg Prod.fst hmap
      have h2 : vTwist (-k) (↑(unitDir p.1)) (↑p.2) = (q.2 : Quaternion ℝ) := by
        simpa only [vData_φ_apply, vMap] using congrArg Prod.snd hmap
      refine (clutchData k).ιX_eq_ιY_iff.mpr ⟨hp, ?_⟩
      have hclutch : clutchMap k p = q := by
        rw [clutchMap]
        exact Prod.ext h1 (Subtype.ext (by rw [coe_clutch]; exact h2))
      exact hclutch
  · obtain ⟨q, rfl⟩ | ⟨q, rfl⟩ := hz'
    · rw [mkToVk_ιY, mkToVk_ιX] at h
      obtain ⟨hq, hmap⟩ := (vData k).ιY_eq_ιX_iff.mp h
      have h1 : invBase q.1 = p.1 := by
        simpa only [vData_φ_apply, vMap] using congrArg Prod.fst hmap
      have h2 : vTwist (-k) (↑(unitDir q.1)) (↑q.2) = (p.2 : Quaternion ℝ) := by
        simpa only [vData_φ_apply, vMap] using congrArg Prod.snd hmap
      refine (clutchData k).ιY_eq_ιX_iff.mpr ⟨hq, ?_⟩
      have hclutch : clutchMap k q = p := by
        rw [clutchMap]
        exact Prod.ext h1 (Subtype.ext (by rw [coe_clutch]; exact h2))
      exact hclutch
    · rw [mkToVk_ιY, mkToVk_ιY] at h
      have h' := (vData k).ιY_injective h
      rw [Prod.mk.injEq] at h'
      obtain ⟨h1, h2⟩ := h'
      rw [Prod.ext h1 (Subtype.ext h2)]

/-- The unit sphere bundle `Mk k` (two copies of `ℝ⁴ × S³` glued by the clutching map) sits inside
the total space `Vk k` of the vector bundle (two copies of `ℝ⁴ × ℍ` glued by the same map): the
inclusion of `S³ ⊂ ℍ` in the fibre induces an injective map `Mk k → Vk k`, characterised on the
two charts by `(x, y) ↦ (x, y)`. -/
theorem mk_to_vk (k : ℤ) :
    ∃ f : Submission.Milnor.Mk k → Submission.Milnor.Vk k,
      (∀ p : Submission.Milnor.MSpace,
        f ((Submission.Milnor.clutchData k).ιX p)
          = (Submission.Milnor.vData k).ιX (p.1, (p.2 : Quaternion ℝ))) ∧
      (∀ p : Submission.Milnor.MSpace,
        f ((Submission.Milnor.clutchData k).ιY p)
          = (Submission.Milnor.vData k).ιY (p.1, (p.2 : Quaternion ℝ))) ∧
      Function.Injective f :=
  ⟨mkToVkFun k, mkToVk_ιX k, mkToVk_ιY k, mkToVkFun_injective k⟩

end

end Work.Milnor
