/-
  `WilC4/invY_ulpmStruct_b` : `ULPMStruct` transfers to the *value-inverted* family at *halved*
  breakpoints.

  This is the assembly of two delegated pieces (both proved, imported below):

  * `Work.WilC4.goodFibre_invY` : the `GoodFibre` conjunct of `ULPMStruct (InvY Y) (HalfB B₀)`
    (a `HalfB B₀`-free interval is `B₀`-free, so the fibre `f = valY Y c` is a unique
    nonvanishing continuous function there and its reciprocal yields the `InvY` fibre);

  * `Work.WilC4.ratio_sign_halfB` : on a `HalfB B₀`-free interval `(a,b)` both `(a,b)` and `(2a,2b)`
    are `B₀`-free, so the fibre has constant sign on each and the doubling ratio `R(x) = f(2x)/f(x)`
    has constant sign on `(a,b)`.

  The remaining step (the monotonicity conjunct) is the following: `RatW (InvY Y) c xᵢ wᵢ` is
  `wᵢ ≠ 0` together with `RatW Y c xᵢ wᵢ⁻¹`.  Monotonicity of `Y`'s ratio on the `B₀`-free interval
  `(a,b)` gives `(w₁⁻¹ ≤ w₂⁻¹ ≤ w₃⁻¹) ∨ (w₃⁻¹ ≤ w₂⁻¹ ≤ w₁⁻¹)`, and `ratio_sign_halfB` says the
  `wᵢ⁻¹` share a sign, so inversion (which reverses order on a sign class,
  `inv_le_inv_iff_of_mul_pos`) transports the trichotomy to `(w₁ ≤ w₂ ≤ w₃) ∨ (w₃ ≤ w₂ ≤ w₁)`.
-/
import Mathlib
import Submission.Work.WilC4.InvFamDefs
import Submission.Work.WilC4.goodFibre_invY
import Submission.Work.WilC4.ratio_sign_halfB

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC4

open Work.WilC4.Route (Gr InD valY valY_mem)

/-- For `u`, `v` of the same (nonzero) sign, `u ≤ v ↔ v⁻¹ ≤ u⁻¹`. -/
theorem inv_le_inv_iff_of_mul_pos {u v : ℝ} (h : 0 < u * v) : u ≤ v ↔ v⁻¹ ≤ u⁻¹ := by
  rcases mul_pos_iff.mp h with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · exact (inv_le_inv₀ hv hu).symm
  · exact (inv_le_inv_of_neg hv hu).symm

theorem invY_ulpmStruct_b {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Work.WilC4.Route.Gr Y c x y →
      Work.WilC4.Route.Gr Y c x y' → y = y')
    (hst : Work.WilC4.ULPMStruct Y B₀) :
    Work.WilC4.ULPMStruct (Work.WilC4.InvY Y) (Work.WilC4.HalfB B₀) := by
  refine ⟨goodFibre_invY hfun hst.1, ?_⟩
  intro c a b hab hfree x₁ x₂ x₃ w₁ w₂ w₃ hx₁ hx₂ hx₃ h12 h23 hw₁ hw₂ hw₃
  -- a `HalfB B₀`-free interval is `B₀`-free
  have hfreeB : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B₀ :=
    fun x hx h => hfree x hx ((mem_halfB_iff B₀ x c).mpr (Or.inl h))
  -- invert the three ratios: `RatW (InvY Y) c xᵢ wᵢ` becomes `RatW Y c xᵢ wᵢ⁻¹`
  obtain ⟨-, hu₁⟩ := (ratW_invY_iff Y c x₁ w₁).mp hw₁
  obtain ⟨-, hu₂⟩ := (ratW_invY_iff Y c x₂ w₂).mp hw₂
  obtain ⟨-, hu₃⟩ := (ratW_invY_iff Y c x₃ w₃).mp hw₃
  -- monotonicity of the ratio of `Y` on the `B₀`-free interval `(a,b)`
  have hmono := hst.2 c a b hab hfreeB x₁ x₂ x₃ w₁⁻¹ w₂⁻¹ w₃⁻¹
    hx₁ hx₂ hx₃ h12 h23 hu₁ hu₂ hu₃
  -- the inverted ratios share a sign
  have hs₁₂ : 0 < w₁⁻¹ * w₂⁻¹ := ratio_sign_halfB hfun hst.1 hab hfree hx₁ hx₂ hu₁ hu₂
  have hs₂₃ : 0 < w₂⁻¹ * w₃⁻¹ := ratio_sign_halfB hfun hst.1 hab hfree hx₂ hx₃ hu₂ hu₃
  rcases hmono with ⟨hA, hB⟩ | ⟨hA, hB⟩
  · right
    refine ⟨?_, ?_⟩
    · simpa using (inv_le_inv_iff_of_mul_pos hs₂₃).mp hB
    · simpa using (inv_le_inv_iff_of_mul_pos hs₁₂).mp hA
  · left
    refine ⟨?_, ?_⟩
    · simpa using (inv_le_inv_iff_of_mul_pos (mul_comm (w₁⁻¹) (w₂⁻¹) ▸ hs₁₂)).mp hB
    · simpa using (inv_le_inv_iff_of_mul_pos (mul_comm (w₂⁻¹) (w₃⁻¹) ▸ hs₂₃)).mp hA

end Work.WilC4
