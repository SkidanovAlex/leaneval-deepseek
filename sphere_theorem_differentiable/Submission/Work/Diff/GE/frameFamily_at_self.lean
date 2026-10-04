import Mathlib
import Submission.Work.Diff.GE.frame_family_defs
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Gram–Schmidt does not move an orthonormal family

The Gram–Schmidt recursion `gs b κ` of `frame_family_defs.lean`, evaluated at `s = t` on the family
`κ = onFrame (G t) x`, uses the bilinear form `b = frameB G x t = (G t).inner x`, for which `κ` is
*already* orthonormal.  Hence `frameFamily G t x t = gs (frameB G x t) (onFrame (G t) x)` is just
`onFrame (G t) x`.

The proof rests on two purely algebraic facts (no positivity and no completeness are needed):

* `gsU_self_of_ortho`: the pre-normalisation vector of an orthonormal family is the vector itself;
* `gs_eq_self_of_ortho`: hence Gram–Schmidt returns the family unchanged.

The only geometric input is that `onFrame g x` really is `g`-orthonormal at `x`, i.e. that
orthonormal frames exist at the single point `x` (`exists_isONFrame_self`).  That is a statement
about one fibre, so it needs no `T2Space M` (unlike the family version
`Work.Diff.GE.isONFrame_onFrame`, whose section carries `[T2Space M]`); this is why it is
re-proved here.

The content coincides with `Work.Diff.GE.frameFamily_at_t` in `gs_self.lean`; it is reproduced here
so that this module depends only on `frame_family_defs` and `curvbasic`.
-/

open scoped BigOperators Bundle

namespace Work.Diff.GE

/-! ## Orthonormal families are Gram–Schmidt fixed points -/

section GenericON

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- If `κ` is `b`-orthonormal, then the orthogonalisation `gsU b κ κ i` of `κ i` removes nothing:
the `b (κ i) (κ j)` with `j.val < i.val` vanish (there `j ≠ i`), so every term of the projection sum
is zero. -/
theorem gsU_self_of_ortho {n : ℕ} (b : V → V → ℝ) (κ : Fin n → V)
    (h : ∀ i j : Fin n, b (κ i) (κ j) = if i = j then 1 else 0) (i : Fin n) :
    gsU b κ κ i = κ i := by
  rw [gsU]
  have hsum : (∑ j : Fin n, if j.val < i.val then b (κ i) (κ j) • κ j else 0) = 0 := by
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j.val < i.val
    · have hne : ¬ (i = j) := fun hh => absurd (hh ▸ hj) (Nat.lt_irrefl j.val)
      rw [if_pos hj, h i j, if_neg hne, zero_smul]
    · rw [if_neg hj]
  rw [hsum, sub_zero]

/-- **Gram–Schmidt of an orthonormal family is the family itself**: if `b (κ i) (κ j) = δᵢⱼ`, then
`gs b κ = κ`.  The recursion is unfolded by strong induction on the index: below `i` the recursion
already returns `κ`, so `gsU` sees the family `κ` (`gsU_congr`), where it is the identity
(`gsU_self_of_ortho`), and the normalisation factor is `(√1)⁻¹ = 1`. -/
theorem gs_eq_self_of_ortho {n : ℕ} (b : V → V → ℝ) (κ : Fin n → V)
    (h : ∀ i j : Fin n, b (κ i) (κ j) = if i = j then 1 else 0) :
    gs b κ = κ := by
  have key : ∀ m : ℕ, ∀ i : Fin n, i.val < m → gs b κ i = κ i := by
    intro m
    induction m with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero i.val)
    | succ m ih =>
      intro i hi
      have hile : i.val ≤ m := Nat.lt_succ_iff.mp hi
      have hcong : gsU b κ (gs b κ) i = gsU b κ κ i :=
        gsU_congr fun j hj => ih j (lt_of_lt_of_le hj hile)
      rw [gs_apply b κ i, hcong, gsU_self_of_ortho b κ h i, h i i, if_pos rfl,
        Real.sqrt_one, inv_one, one_smul]
  funext i
  exact key (i.val + 1) i (Nat.lt_succ_self i.val)

end GenericON

/-! ## Orthonormal frames at a point exist -/

/-- Every point of `M` carries a `g`-orthonormal frame: endow the tangent space with the inner
product `g.inner x`, in which Mathlib's `stdOrthonormalBasis` is an orthonormal family, and transfer
along the definitional identity of the two inner products.  This concerns a single fibre, so no
`T2Space M` is needed. -/
theorem exists_isONFrame_self
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    (g : Submission.Diff.SMet I M) (x : M) :
    ∃ e : Fin (Module.finrank ℝ E) → TangentSpace I x, Submission.Diff.IsONFrame g x e := by
  letI : Bundle.RiemannianBundle (fun y : M ↦ TangentSpace I y) := ⟨g.toRiemannianMetric⟩
  have key : ∀ v w : TangentSpace I x, inner ℝ v w = g.inner x v w := fun v w => rfl
  refine ⟨fun i => stdOrthonormalBasis ℝ (TangentSpace I x) i, fun i j => ?_⟩
  have h := orthonormal_iff_ite.mp (stdOrthonormalBasis ℝ (TangentSpace I x)).orthonormal i j
  exact (key _ _).symm.trans h

/-! ## The frame family at `s = t` -/

/-- Gram–Schmidt does not move a family that is already orthonormal for the form used: at `s = t`
the family `frameFamily G t x` is the `G t`-orthonormal frame `onFrame (G t) x` it started from. -/
theorem frameFamily_at_self
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (x : M) :
    Work.Diff.GE.frameFamily G t x t = Submission.Diff.onFrame (G t) x := by
  have he : Submission.Diff.IsONFrame (G t) x (Submission.Diff.onFrame (G t) x) :=
    Classical.epsilon_spec (exists_isONFrame_self (I := I) (M := M) (G t) x)
  have hb : ∀ i j, frameB G x t (Submission.Diff.onFrame (G t) x i)
      (Submission.Diff.onFrame (G t) x j) = if i = j then 1 else 0 :=
    fun i j => he i j
  exact gs_eq_self_of_ortho (frameB G x t) (Submission.Diff.onFrame (G t) x) hb

end Work.Diff.GE
