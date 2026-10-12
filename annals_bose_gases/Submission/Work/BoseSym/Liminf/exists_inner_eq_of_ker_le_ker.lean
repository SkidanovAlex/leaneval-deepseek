import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Module.HahnBanach
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseSym.Liminf

open scoped InnerProductSpace

/-- If a linear functional `ℓ` on a submodule `Y` of an inner product space vanishes on the
kernel of a continuous linear map `T : Y → W` into a Hilbert space `W`, and is bounded by
`c * ‖T y‖`, then `ℓ` is represented by the inner product with a single vector `h : W` of
norm at most `c`.

The proof factors `ℓ` through the range of `T` (first isomorphism theorem), bounds the induced
functional by `c`, extends it to all of `W` by Hahn–Banach without increasing its norm, and
finally represents it by a vector via the Fréchet–Riesz theorem. -/
theorem exists_inner_eq_of_ker_le_ker {E W : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]
    {Y : Submodule ℝ E} (T : Y →L[ℝ] W) (ℓ : Y →ₗ[ℝ] ℝ) (hker : T.ker ≤ ℓ.ker) {c : ℝ}
    (hc0 : 0 ≤ c) (hc : ∀ y : Y, |ℓ y| ≤ c * ‖T y‖) :
    ∃ h : W, ‖h‖ ≤ c ∧ ∀ y : Y, inner ℝ h (T y) = ℓ y := by
  let Tl : Y →ₗ[ℝ] W := T
  have hker' : Tl.ker ≤ ℓ.ker := hker
  -- `ℓ` factors through the quotient of `Y` by `ker T` ...
  let q : Y ⧸ Tl.ker →ₗ[ℝ] ℝ := Tl.ker.liftQ ℓ hker'
  -- ... which is canonically the range of `T`.
  let e : LinearMap.range Tl →ₗ[ℝ] Y ⧸ Tl.ker := (Tl.quotKerEquivRange.symm : _ →ₗ[ℝ] _)
  let f : LinearMap.range Tl →ₗ[ℝ] ℝ := q.comp e
  have hf_apply : ∀ (y : Y) (h : Tl y ∈ LinearMap.range Tl), f ⟨Tl y, h⟩ = ℓ y := by
    intro y h; simp [f, q, e]
  have hmem : ∀ y : Y, Tl y ∈ LinearMap.range Tl := fun y => LinearMap.mem_range.mpr ⟨y, rfl⟩
  -- the induced functional on the range is bounded by `c`
  have hbnd : ∀ z : LinearMap.range Tl, ‖f z‖ ≤ c * ‖z‖ := by
    rintro ⟨z, hz⟩
    rw [LinearMap.mem_range] at hz
    obtain ⟨y, hy⟩ := hz
    have hze : (⟨z, hz⟩ : LinearMap.range Tl) = ⟨Tl y, hmem y⟩ := Subtype.ext hy.symm
    rw [hze, hf_apply y (hmem y), Real.norm_eq_abs]
    exact hc y
  let G₀ : LinearMap.range Tl →L[ℝ] ℝ := f.mkContinuous c hbnd
  have hG₀ : ∀ z, G₀ z = f z := fun _ => rfl
  have hnormG₀ : ‖G₀‖ ≤ c := by
    refine ContinuousLinearMap.opNorm_le_bound G₀ hc0 (fun z => ?_)
    rw [hG₀ z]; exact hbnd z
  -- Hahn–Banach: extend norm-non-increasingly to all of `W`
  obtain ⟨G, hG, hGnorm⟩ := exists_extension_norm_eq (LinearMap.range Tl) G₀
  -- Fréchet–Riesz: represent `G` by a vector
  refine ⟨(InnerProductSpace.toDual ℝ W).symm G, ?_, ?_⟩
  · rw [LinearIsometryEquiv.norm_map, hGnorm]; exact hnormG₀
  · intro y
    rw [InnerProductSpace.toDual_symm_apply]
    exact (hG ⟨T y, LinearMap.mem_range.mpr ⟨y, rfl⟩⟩).trans (hf_apply y (hmem y))

end Work.BoseSym.Liminf
