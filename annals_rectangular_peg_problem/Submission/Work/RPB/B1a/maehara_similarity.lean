import Mathlib

namespace Work.RPB.B1a

/-- **The Maehara normalising similarity, as a homeomorphism of the plane.**

For distinct `α β : ℂ` the affine similarity
`z ↦ 2 (z - (α+β)/2) / (β - α)`  sends `α` to `-1` and `β` to `1`, hence normalises the ordered
pair `(α, β)` to the pair `(-1, 1)` of the real axis.  Transported through the standard
homeomorphism `ℂ ≃ₜ ℝ × ℝ` (given by `z ↦ (z.re, z.im)`) it becomes a self-homeomorphism `e` of the
plane.  `e` is affine with invertible linear part, so it (and its inverse) map bounded sets to
bounded sets; these are the two `Bornology.IsBounded` clauses.  The final clause records the
explicit formula of `e` in complex coordinates. -/
theorem maehara_similarity (α β : ℂ) (h : α ≠ β) :
    ∃ e : (ℝ × ℝ) ≃ₜ (ℝ × ℝ),
      (∀ S : Set (ℝ × ℝ), Bornology.IsBounded S → Bornology.IsBounded (e '' S)) ∧
      (∀ S : Set (ℝ × ℝ), Bornology.IsBounded S → Bornology.IsBounded (e.symm '' S)) ∧
      e (Complex.equivRealProd α) = ((-1:ℝ),(0:ℝ)) ∧
      e (Complex.equivRealProd β) = ((1:ℝ),(0:ℝ)) ∧
      (∀ z : ℂ, e (Complex.equivRealProd z) =
        (((2:ℂ)*(z - (α+β)/2)/(β-α)).re, ((2:ℂ)*(z - (α+β)/2)/(β-α)).im)) := by
  have hba : β - α ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
  -- The complex similarity and its inverse.
  let φ : ℂ → ℂ := fun z => 2 * (z - (α+β)/2) / (β-α)
  let ψ : ℂ → ℂ := fun w => (α+β)/2 + (β-α)*w/2
  have hcontφ : Continuous φ := by
    dsimp only [φ]
    exact (continuous_const.mul (continuous_id.sub continuous_const)).div_const (β - α)
  have hcontψ : Continuous ψ := by
    dsimp only [ψ]; fun_prop
  have hleft : Function.LeftInverse ψ φ := by
    intro z; dsimp only [φ, ψ]; field_simp; ring
  have hright : Function.RightInverse ψ φ := by
    intro w; dsimp only [φ, ψ]; field_simp; ring
  -- The similarity as a homeomorphism of `ℂ`.
  let F : ℂ ≃ₜ ℂ :=
    { toFun := φ, invFun := ψ, left_inv := hleft, right_inv := hright,
      continuous_toFun := hcontφ, continuous_invFun := hcontψ }
  -- The standard homeomorphism `ℂ ≃ₜ ℝ × ℝ`.
  have hcontR : Continuous ((Complex.equivRealProd : ℂ → ℝ × ℝ)) := by
    rw [show ((Complex.equivRealProd : ℂ → ℝ × ℝ)) = fun z => (z.re, z.im) from
      funext Complex.equivRealProd_apply]
    exact Complex.continuous_re.prodMk Complex.continuous_im
  have hcontRinv : Continuous ((Complex.equivRealProd.symm : ℝ × ℝ → ℂ)) := by
    rw [show ((Complex.equivRealProd.symm : ℝ × ℝ → ℂ)) =
      fun p => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I from funext Complex.equivRealProd_symm_apply]
    fun_prop
  let hR : ℂ ≃ₜ ℝ × ℝ :=
    { toFun := Complex.equivRealProd, invFun := Complex.equivRealProd.symm,
      left_inv := Complex.equivRealProd.left_inv, right_inv := Complex.equivRealProd.right_inv,
      continuous_toFun := hcontR, continuous_invFun := hcontRinv }
  have hRfun : ∀ z : ℂ, hR z = Complex.equivRealProd z := fun _ => rfl
  refine ⟨hR.symm.trans (F.trans hR), ?_, ?_, ?_, ?_, ?_⟩
  · -- `e` maps bounded sets to bounded sets.
    intro S hS
    exact (hS.isCompact_closure.image (hR.symm.trans (F.trans hR)).continuous).isBounded.subset
      (Set.image_mono subset_closure)
  · -- `e.symm` maps bounded sets to bounded sets.
    intro S hS
    exact (hS.isCompact_closure.image (hR.symm.trans (F.trans hR)).symm.continuous).isBounded.subset
      (Set.image_mono subset_closure)
  · -- `e` sends `α` to `(-1, 0)`.
    have hv : (hR.symm.trans (F.trans hR)) (Complex.equivRealProd α) =
        ((φ α).re, (φ α).im) := by
      have hs : hR.symm (Complex.equivRealProd α) = α := by
        rw [← hRfun α]; exact Homeomorph.symm_apply_apply hR α
      rw [Homeomorph.trans_apply, Homeomorph.trans_apply, hs, show F α = φ α from rfl,
        hRfun (φ α), Complex.equivRealProd_apply]
    have hphi : φ α = -1 := by dsimp only [φ]; field_simp; ring
    rw [hv, hphi]; norm_num
  · -- `e` sends `β` to `(1, 0)`.
    have hv : (hR.symm.trans (F.trans hR)) (Complex.equivRealProd β) =
        ((φ β).re, (φ β).im) := by
      have hs : hR.symm (Complex.equivRealProd β) = β := by
        rw [← hRfun β]; exact Homeomorph.symm_apply_apply hR β
      rw [Homeomorph.trans_apply, Homeomorph.trans_apply, hs, show F β = φ β from rfl,
        hRfun (φ β), Complex.equivRealProd_apply]
    have hphi : φ β = 1 := by dsimp only [φ]; field_simp; ring
    rw [hv, hphi]; norm_num
  · -- The explicit formula for `e`.
    intro z
    have hs : hR.symm (Complex.equivRealProd z) = z := by
      rw [← hRfun z]; exact Homeomorph.symm_apply_apply hR z
    rw [Homeomorph.trans_apply, Homeomorph.trans_apply, hs, show F z = φ z from rfl,
      hRfun (φ z), Complex.equivRealProd_apply]

end Work.RPB.B1a
