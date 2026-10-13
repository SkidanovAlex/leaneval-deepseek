import Mathlib
import Submission.Work.WilC4.InvFamDefs
import Submission.Work.WilC4.slot_aux

namespace Work.WilC4

/-- The `HalfB`-free interval condition is stronger than the `B₀`-free one (as `B₀ ⊆ HalfB B₀`). -/
theorem halfB_free_imp_free {k : ℕ} {B₀ : Set (Fin (k + 1) → ℝ)} {c : Fin k → ℝ} {a b : ℝ}
    (hfree : ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ HalfB B₀) :
    ∀ x ∈ Set.Ioo a b, Fin.cons x c ∉ B₀ :=
  fun x hx h => hfree x hx (Or.inl h)

/-- **Continuity of the reciprocal.**  If `f` is continuous on `Ioo a b` and nowhere zero there,
then `1/f` is continuous on `Ioo a b`: near a point `x` the values of `f` stay away from `0`. -/
theorem continuousOn_inv_of_continuousOn {f : ℝ → ℝ} {a b : ℝ}
    (hnz : ∀ x ∈ Set.Ioo a b, f x ≠ 0)
    (hcont : ∀ x ∈ Set.Ioo a b, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' ∈ Set.Ioo a b,
      |x' - x| < δ → |f x' - f x| < ε) :
    ∀ x ∈ Set.Ioo a b, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ x' ∈ Set.Ioo a b,
      |x' - x| < δ → |(f x')⁻¹ - (f x)⁻¹| < ε := by
  intro x hx ε hε
  have hfx0 : f x ≠ 0 := hnz x hx
  have hfxabs : 0 < |f x| := abs_pos.mpr hfx0
  obtain ⟨δ₁, hδ₁0, hδ₁⟩ := hcont x hx (|f x| / 2) (by linarith)
  obtain ⟨δ₂, hδ₂0, hδ₂⟩ := hcont x hx (ε * |f x| ^ 2 / 2) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁0 hδ₂0, fun x' hx' hxd => ?_⟩
  have hxe : |x' - x| < δ₁ := lt_of_lt_of_le hxd (min_le_left _ _)
  have hxf : |x' - x| < δ₂ := lt_of_lt_of_le hxd (min_le_right _ _)
  have h1 : |f x' - f x| < |f x| / 2 := hδ₁ x' hx' hxe
  have h2 : |f x| / 2 < |f x'| := by
    have habs : |f x| - |f x'| ≤ |f x - f x'| := abs_sub_abs_le_abs_sub (f x) (f x')
    rw [abs_sub_comm] at habs
    linarith
  have h3 : |f x' - f x| < ε * |f x| ^ 2 / 2 := hδ₂ x' hx' hxf
  have hM : |(f x')⁻¹ - (f x)⁻¹| = |f x - f x'| / (|f x'| * |f x|) := by
    rw [inv_sub_inv (hnz x' hx') hfx0, abs_div, abs_mul]
  rw [hM]
  have hnum : |f x - f x'| < ε * |f x| ^ 2 / 2 := by
    rw [abs_sub_comm]; exact h3
  have hden : 0 < |f x'| * |f x| := mul_pos (lt_trans (by linarith) h2) hfxabs
  rw [div_lt_iff₀ hden]
  have hkey : |f x| ^ 2 / 2 < |f x'| * |f x| := by nlinarith [h2, hfxabs]
  have hstep : ε * |f x| ^ 2 / 2 < ε * (|f x'| * |f x|) := by nlinarith [hkey, hε]
  linarith [hnum, hstep]

theorem goodFibre_invY {k : ℕ} {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Work.WilC4.Route.Gr Y c x y →
      Work.WilC4.Route.Gr Y c x y' → y = y')
    (hgf : Work.WilC4.GoodFibre Y B₀) :
    Work.WilC4.GoodFibre (Work.WilC4.InvY Y) (Work.WilC4.HalfB B₀) := by
  intro c a b hab hfree
  obtain ⟨hu, hnz, hcont⟩ := hgf c a b hab (halfB_free_imp_free hfree)
  refine ⟨?_, ?_, ?_⟩
  · -- uniqueness of the inverse value on the interval
    intro x hx
    obtain ⟨v, hv, huniq⟩ := hu x hx
    have hv0 : v ≠ 0 := hnz x hx v hv
    refine ⟨v⁻¹, (gr_invY_iff Y c x v⁻¹).mpr ⟨inv_ne_zero hv0, by rwa [inv_inv]⟩, ?_⟩
    intro y hy
    rw [gr_invY_iff] at hy
    rw [← huniq y⁻¹ hy.2, inv_inv]
  · -- non-vanishing of the inverse value
    intro x hx y hy
    rw [gr_invY_iff] at hy
    exact hy.1
  · -- continuity of the inverse value
    intro x hx ε hε
    obtain ⟨v, hv, huniq⟩ := hu x hx
    have hv0 : v ≠ 0 := hnz x hx v hv
    have hvpos : 0 < |v| := abs_pos.mpr hv0
    obtain ⟨δ₁, hδ₁0, hδ₁⟩ := hcont x hx (|v| / 2) (by linarith)
    obtain ⟨δ₂, hδ₂0, hδ₂⟩ := hcont x hx (ε * |v| ^ 2 / 2) (by positivity)
    refine ⟨min δ₁ δ₂, lt_min hδ₁0 hδ₂0, fun x' hx' y y' hxd hy hy' => ?_⟩
    rw [gr_invY_iff] at hy hy'
    obtain ⟨hy0, hyY⟩ := hy
    obtain ⟨hy'0, hy'Y⟩ := hy'
    have hxe : |x' - x| < δ₁ := lt_of_lt_of_le hxd (min_le_left _ _)
    have hxf : |x' - x| < δ₂ := lt_of_lt_of_le hxd (min_le_right _ _)
    have h1 : |y'⁻¹ - v| < |v| / 2 := hδ₁ x' hx' v y'⁻¹ hxe hv hy'Y
    have h2 : |v| / 2 < |y'⁻¹| := by
      have habs : |v| - |y'⁻¹| ≤ |v - y'⁻¹| := abs_sub_abs_le_abs_sub v y'⁻¹
      rw [abs_sub_comm] at habs
      linarith
    have h3 : |y'⁻¹ - v| < ε * |v| ^ 2 / 2 := hδ₂ x' hx' v y'⁻¹ hxf hv hy'Y
    have hyeq : y = v⁻¹ := by rw [← huniq y⁻¹ hyY, inv_inv]
    have hM : |y' - y| = |v - y'⁻¹| / (|y'⁻¹| * |v|) := by
      have hleft : y' - y = (y'⁻¹)⁻¹ - v⁻¹ := by rw [hyeq, inv_inv]
      rw [hleft, inv_sub_inv (inv_ne_zero hy'0) hv0, abs_div, abs_mul]
    rw [hM]
    have hnum : |v - y'⁻¹| < ε * |v| ^ 2 / 2 := by
      rw [abs_sub_comm]; exact h3
    have hden : 0 < |y'⁻¹| * |v| := mul_pos (lt_trans (by linarith) h2) hvpos
    rw [div_lt_iff₀ hden]
    have hkey : |v| ^ 2 / 2 < |y'⁻¹| * |v| := by nlinarith [h2, hvpos]
    have hstep : ε * |v| ^ 2 / 2 < ε * (|y'⁻¹| * |v|) := by nlinarith [hkey, hε]
    linarith [hnum, hstep]

end Work.WilC4
