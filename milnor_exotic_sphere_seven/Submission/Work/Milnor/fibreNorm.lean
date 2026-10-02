import Mathlib
import Submission.Work.Milnor.VBundle

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Milnor

open scoped Manifold ContDiff Topology

/-!
# The norm of the fibre coordinate on the total space of `ξ`

The total space `Vk k = (vData k).Glued` of the rank-4 vector bundle `ξ` over `S⁴` is obtained by
gluing two copies of `MSpace8 = ℝ⁴ × ℍ` along `{x ≠ 0} × ℍ` by the clutching map
`vMap k (x, y) = (x/‖x‖², û⁻ᵏ y û⁻¹)` (`û = x/‖x‖`, a unit quaternion).

The two coordinates in which a point is presented differ by a *rotation* of the fibre `ℍ`, so the
norm `‖y‖` of the fibre coordinate is *well defined* on the glued space.  Concretely, the twisting
`y ↦ q y q⁻¹` of `ℍ` by a unit quaternion `q` is isometric (`norm_vTwist` below), hence the
function `(x, y) ↦ ‖y‖` on the disjoint union `MSpace8 ⊕ MSpace8` (`vNormFun`) is constant on the
gluing relation and descends to the quotient; it is continuous because `(x, y) ↦ ‖y‖` is, and the
quotient carries the quotient topology.

This is the technical heart of the statement that the fibres of `ξ` are Euclidean and that the
`S³`-bundle `Mk k` is the unit sphere bundle of `ξ` (and, dually, that the unit disc bundle is a
manifold with boundary).
-/

noncomputable section

/-! ## The twist `y ↦ q y q⁻¹` of a norm-one quaternion is isometric -/

/-- The norm of the fibre coordinate is preserved by the twisting `y ↦ q ᵐ y q⁻¹` whenever
`q : ℍ` has norm one.  (Here `ℍ = Quaternion ℝ` is a normed division ring, so `‖a * b‖ =
‖a‖ * ‖b‖` and `‖q ^ m‖ = ‖q‖ ^ m`.) -/
lemma norm_vTwist (m : ℤ) {q : Quaternion ℝ} (hq : ‖q‖ = 1) (y : Quaternion ℝ) :
    ‖Submission.Milnor.vTwist m q y‖ = ‖y‖ := by
  rw [Submission.Milnor.vTwist, norm_mul, norm_mul, norm_zpow, norm_inv, hq, inv_one, one_zpow,
    one_mul, mul_one]

/-- The quaternion underlying the unit direction `unitDir x ∈ S³ ⊆ ℍ` has norm one. -/
lemma norm_unitDir_coe (x : EuclideanSpace ℝ (Fin 4)) :
    ‖((Submission.Milnor.unitDir x : Submission.Milnor.QS3) : Quaternion ℝ)‖ = 1 :=
  norm_eq_of_mem_sphere (Submission.Milnor.unitDir x)

/-- The clutching map of `ξ` preserves the norm of the fibre coordinate. -/
lemma norm_snd_vMap (k : ℤ) (p : Submission.Milnor.MSpace8) :
    ‖(Submission.Milnor.vMap k p).2‖ = ‖p.2‖ := by
  simp only [Submission.Milnor.vMap]
  exact norm_vTwist (-k) (norm_unitDir_coe p.1) p.2

end

/-! ## The descended function -/

noncomputable section

/-- The candidate function `‖y‖` on the disjoint union `MSpace8 ⊕ MSpace8` of the two charts of
the total space of `ξ` (both charts are copies of `ℝ⁴ × ℍ`, and we take the norm of the second
coordinate in each). -/
def vNormFun : Submission.Milnor.MSpace8 ⊕ Submission.Milnor.MSpace8 → ℝ :=
  Sum.elim (fun p => ‖p.2‖) (fun p => ‖p.2‖)

lemma vNormFun_inl (p : Submission.Milnor.MSpace8) : vNormFun (Sum.inl p) = ‖p.2‖ := rfl

lemma vNormFun_inr (p : Submission.Milnor.MSpace8) : vNormFun (Sum.inr p) = ‖p.2‖ := rfl

lemma vNormFun_continuous : Continuous vNormFun :=
  Continuous.sumElim continuous_snd.norm continuous_snd.norm

/-- On the gluing region, the norm of the fibre coordinate computed in the second chart agrees with
the one computed in the first. -/
lemma vNormFun_phi (k : ℤ) (p : Submission.Milnor.MSpace8) :
    vNormFun (Sum.inr ((Submission.Milnor.vData k).φ p)) = ‖p.2‖ := by
  have h : (Submission.Milnor.vData k).φ p = Submission.Milnor.vMap k p := rfl
  rw [h, vNormFun_inr]
  exact norm_snd_vMap k p

/-- The norm of the fibre coordinate is constant on the gluing relation of `vData k`. -/
lemma vNormFun_rel (k : ℤ) :
    ∀ a b : Submission.Milnor.MSpace8 ⊕ Submission.Milnor.MSpace8,
      (Submission.Milnor.vData k).rel a b → vNormFun a = vNormFun b := by
  rintro (u | u) (v | v) h
  · rw [vNormFun_inl, vNormFun_inl, h]
  · obtain ⟨_, hxy⟩ := h
    rw [vNormFun_inl, vNormFun_inr, ← hxy]
    exact (vNormFun_phi k u).symm
  · obtain ⟨_, hxy⟩ := h
    rw [vNormFun_inr, vNormFun_inl, hxy]
    exact vNormFun_phi k v
  · rw [vNormFun_inr, vNormFun_inr, h]

end

/-- The clutching map preserves the norm of the fibre coordinate, so the norm of the fibre
coordinate descends to a continuous function on the total space `Vk k` of the vector bundle. -/
theorem fibreNorm (k : ℤ) :
    ∃ N : Submission.Milnor.Vk k → ℝ,
      (∀ p : Submission.Milnor.MSpace8,
        N ((Submission.Milnor.vData k).ιX p) = ‖p.2‖) ∧
      (∀ p : Submission.Milnor.MSpace8,
        N ((Submission.Milnor.vData k).ιY p) = ‖p.2‖) ∧
      Continuous N := by
  refine ⟨Quotient.lift vNormFun (vNormFun_rel k), ?_, ?_, ?_⟩
  · intro p
    exact vNormFun_inl p
  · intro p
    exact vNormFun_inr p
  · exact vNormFun_continuous.quotient_lift (vNormFun_rel k)

end Work.Milnor
