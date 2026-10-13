/-
  WilC4/oneSided_ratio_deep : the one-sided monotonicity of the doubling ratio at a deep point.

  This is the P2 input of the C4 route (`sources/wilkiesC4route/wilkies_C4_route.md` §4, "Monotonicity
  gives `r ≥ B` on `[x, xB]`"): at a `β`-deep point `x` the doubling ratio `r_c(t) = f_c(2t)/f_c(t)`
  is either non-decreasing on the right of `x` (up to the scale `β`) or non-decreasing on the left of
  `x` (down to the scale `x/(2β)`).

  The content is not merely bookkeeping: `ULPMStruct` supplies the *three-point* betweenness of `r_c`
  on every interval free of the breakpoint family `B₀` (`mono_of_three_point` upgrades betweenness on
  an interval to global monotonicity or antimonotonicity), and deepness at `x` puts the whole
  interval `(x/(2β), βx)` -- together with the doubles of its points -- inside the window
  `(x/(2β), 2βx)` which `B₀` avoids.  Hence `r_c` is monotone or antitone there and the disjunction
  is the corresponding one-sided conclusion.
-/
import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.ULPMExp
import Submission.Work.WilC4.mono_of_three_point

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC4

open Work.WilC4.Route (Gr InD valY ratioY)

variable {k : ℕ}

/-- On the working interval `(x/(2β), βx)` of a `β`-deep point `x` (with `β > 1`), the number
`ratioY Y c z` is a genuine value of the doubling ratio relation `RatW`.  The point is that `z` and
`2z` both lie in the deep window `(x/(2β), 2βx)`, where `GoodFibre` makes the fibre a nowhere zero
function. -/
private theorem ratW_ratioY_of_deep {Y : Set (Fin (k + 2) → ℝ)} {B₀ : Set (Fin (k + 1) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Gr Y c x y → Gr Y c x y' → y = y')
    (hgood : GoodFibre Y B₀) {c : Fin k → ℝ} {β x : ℝ} (hβ : 1 < β) (hx : 0 < x)
    (hdeep : IsDeepR B₀ c β x) {z : ℝ} (hz : z ∈ Set.Ioo (x / (2 * β)) (β * x)) :
    RatW Y c z (ratioY Y c z) := by
  have hβ0 : 0 < β := by linarith
  have hβ1 : 1 ≤ β := le_of_lt hβ
  have hx2b : 0 < 2 * β := by linarith
  have hzdeep : z ∈ Set.Ioo (x / (2 * β)) (2 * β * x) :=
    ⟨hz.1, by nlinarith [hz.2, hx, hβ0]⟩
  have h2zdeep : 2 * z ∈ Set.Ioo (x / (2 * β)) (2 * β * x) := by
    refine ⟨?_, by nlinarith [hz.2, hx, hβ0]⟩
    have hz1 : x < z * (2 * β) := (div_lt_iff₀ hx2b).mp hz.1
    rw [div_lt_iff₀ hx2b]
    nlinarith [hz1, hz.1, hx2b, hx]
  obtain ⟨hg1, hnz⟩ := deep_val hgood hβ1 hx hdeep hzdeep
  obtain ⟨hg2, -⟩ := deep_val hgood hβ1 hx hdeep h2zdeep
  exact (ratW_iff_valY hfun c z (ratioY Y c z)).mpr ⟨hg1, hg2, hnz, rfl⟩

theorem oneSided_ratio_deep {k : ℕ}
    (Y : Set (Fin (k + 2) → ℝ)) (B₀ : Set (Fin (k + 1) → ℝ))
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Work.WilC4.Route.Gr Y c x y →
      Work.WilC4.Route.Gr Y c x y' → y = y')
    (hst : Work.WilC4.ULPMStruct Y B₀)
    (c : Fin k → ℝ) (β x : ℝ) (hβ : 1 < β) (hx : 0 < x)
    (hdeep : Work.WilC4.IsDeepR B₀ c β x) :
    (∀ t : ℝ, x < t → t < β * x →
      Work.WilC4.Route.ratioY Y c x ≤ Work.WilC4.Route.ratioY Y c t) ∨
    (∀ t : ℝ, x / (2 * β) < t → t < x →
      Work.WilC4.Route.ratioY Y c x ≤ Work.WilC4.Route.ratioY Y c t) := by
  have hβ0 : 0 < β := by linarith
  have hβ1 : 1 ≤ β := le_of_lt hβ
  have hgood : GoodFibre Y B₀ := hst.1
  have hx2b : 0 < 2 * β := by linarith
  -- the working interval `(x/(2β), βx)` and the two endpoint comparisons with `x`
  have hax : x / (2 * β) < x := div_lt_self hx (by linarith)
  have hxb : x < β * x := by nlinarith [hx, hβ]
  have hab : x / (2 * β) < β * x := by
    rw [div_lt_iff₀ hx2b]
    nlinarith [hx, hβ, sq_pos_of_pos hβ0]
  -- it is free of `B₀`, being contained in the deep window
  have hfree : ∀ z ∈ Set.Ioo (x / (2 * β)) (β * x), Fin.cons z c ∉ B₀ := by
    intro z hz
    exact deep_free hdeep z ⟨hz.1, by nlinarith [hz.2, hx, hβ0]⟩
  -- the three-point betweenness of `ratioY Y c ·` on the working interval
  have h3 : ∀ x₁ x₂ x₃ : ℝ, x₁ ∈ Set.Ioo (x / (2 * β)) (β * x) →
      x₂ ∈ Set.Ioo (x / (2 * β)) (β * x) → x₃ ∈ Set.Ioo (x / (2 * β)) (β * x) →
      x₁ < x₂ → x₂ < x₃ →
      (ratioY Y c x₁ ≤ ratioY Y c x₂ ∧ ratioY Y c x₂ ≤ ratioY Y c x₃) ∨
      (ratioY Y c x₃ ≤ ratioY Y c x₂ ∧ ratioY Y c x₂ ≤ ratioY Y c x₁) := by
    intro x₁ x₂ x₃ h1 h2 h3 h12 h23
    exact hst.2 c (x / (2 * β)) (β * x) hab hfree x₁ x₂ x₃
      (ratioY Y c x₁) (ratioY Y c x₂) (ratioY Y c x₃) h1 h2 h3 h12 h23
      (ratW_ratioY_of_deep hfun hgood hβ hx hdeep h1)
      (ratW_ratioY_of_deep hfun hgood hβ hx hdeep h2)
      (ratW_ratioY_of_deep hfun hgood hβ hx hdeep h3)
  -- betweenness on an interval upgrades to global monotonicity or antimonotonicity
  rcases mono_of_three_point (f := fun t => ratioY Y c t) hab h3 with hmono | hanti
  · exact Or.inl fun t ht1 ht2 =>
      hmono ⟨hax, hxb⟩ ⟨lt_trans hax ht1, ht2⟩ (le_of_lt ht1)
  · exact Or.inr fun t ht1 ht2 =>
      hanti ⟨ht1, by nlinarith [ht2, hx, hβ]⟩ ⟨hax, hxb⟩ (le_of_lt ht2)

end Work.WilC4
