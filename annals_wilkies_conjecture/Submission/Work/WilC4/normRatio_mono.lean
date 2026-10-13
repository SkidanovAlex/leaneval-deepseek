import Mathlib
import Submission.Work.WilC4.ULPMDev
import Submission.Work.WilC4.ErealDefs
import Submission.Work.WilC4.ULPMExp
import Submission.Work.WilC4.mono_of_three_point

/-
  WilC4/normRatio_mono: the *normalised* ratio `s ↦ f_c(x s)` is monotone or antitone on the
  multiplicative interval `(1/M, M)` at an `M`-deep point `x` (`M ≥ 2`).

  This is the shape in which the monotonicity of the doubling ratio is fed into the dyadic
  telescoping of the ULPM proof: everything is expressed in the rescaled variable `s = t/x`, so
  that the interval `(1/M, M)` does not depend on `x`.

  The content is the standard two-sided argument (cf. `oneSided_ratio_deep`):

  * `ULPMStruct` gives the *three-point betweenness* of the ratio relation `RatW` on every interval
    free of the breakpoint family `B` (`ULPMStruct = GoodFibre ∧ three-point property`);
  * deepness of `x` at scale `M` makes the interval `(x/M, x*M)` — and, crucially, the double of
    every one of its points — lie inside the deep window `(x/(2M), 2Mx)`, which `B` avoids;
  * on that window `GoodFibre` makes the fibre a nowhere-zero function, so `ratioY Y c t` is a
    genuine value of `RatW Y c t ·` (`ratW_ratioY_of_deep`);
  * `mono_of_three_point` upgrades betweenness on an interval to global monotonicity or
    antimonotonicity.
-/

namespace Work.WilC4

open Set

variable {k : ℕ}

/-- Inside the deep window: for `M ≥ 2` and `t ∈ (x/M, x*M)`, both `t` and `2 * t` lie in the deep
window `(x/(2M), 2Mx)` (the window that `B` avoids at an `M`-deep point `x`). -/
private theorem deep_window_mem {M x t : ℝ} (hM : 2 ≤ M) (hx : 0 < x)
    (ht : t ∈ Set.Ioo (x / M) (x * M)) :
    t ∈ Set.Ioo (x / (2 * M)) (2 * M * x) ∧
      2 * t ∈ Set.Ioo (x / (2 * M)) (2 * M * x) := by
  have hMpos : 0 < M := by linarith
  have h2M : 0 < 2 * M := by linarith
  have ht1 : x < t * M := (div_lt_iff₀ hMpos).mp ht.1
  refine ⟨⟨?_, by nlinarith [ht.2, hx, hM]⟩, ⟨?_, by nlinarith [ht.2, hx, hM]⟩⟩
  · rw [div_lt_iff₀ h2M]; nlinarith
  · rw [div_lt_iff₀ h2M]; nlinarith

/-- The rescaling `s ↦ x * s` maps the multiplicative interval `(1/M, M)` into `(x/M, x*M)`. -/
private theorem mul_mem_Ioo {M x s : ℝ} (hx : 0 < x) (hs : s ∈ Set.Ioo (1 / M) M) :
    x * s ∈ Set.Ioo (x / M) (x * M) := by
  constructor
  · have h : x * (1 / M) < x * s := mul_lt_mul_of_pos_left hs.1 hx
    rwa [mul_one_div] at h
  · exact mul_lt_mul_of_pos_left hs.2 hx

/-- On the working interval `(x/M, x*M)` of an `M`-deep point `x` (with `M ≥ 2`), `ratioY Y c t`
is a genuine value of the doubling-ratio relation `RatW Y c · ·`: `t` and `2t` both lie in the deep
window, where `GoodFibre` makes the fibre a nowhere-zero function. -/
private theorem ratW_ratioY_of_deep {Y : Set (Fin (k + 2) → ℝ)}
    {B : Set (Fin (k + 1) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Route.Gr Y c x y → Route.Gr Y c x y' → y = y')
    (hgood : GoodFibre Y B) {c : Fin k → ℝ} {M x t : ℝ} (hM : 2 ≤ M) (hx : 0 < x)
    (hdeep : IsDeepR B c M x) (ht : t ∈ Set.Ioo (x / M) (x * M)) :
    RatW Y c t (Route.ratioY Y c t) := by
  have hM1 : (1 : ℝ) ≤ M := by linarith
  obtain ⟨hmem, hmem2⟩ := deep_window_mem hM hx ht
  obtain ⟨hg1, hnz⟩ := deep_val hgood hM1 hx hdeep hmem
  obtain ⟨hg2, -⟩ := deep_val hgood hM1 hx hdeep hmem2
  exact (ratW_iff_valY hfun c t (Route.ratioY Y c t)).mpr ⟨hg1, hg2, hnz, rfl⟩

theorem normRatio_mono {k : ℕ}
    {Y : Set (Fin (k + 2) → ℝ)} {B : Set (Fin (k + 1) → ℝ)}
    (hfun : ∀ (c : Fin k → ℝ) (x y y' : ℝ), Work.WilC4.Route.Gr Y c x y →
      Work.WilC4.Route.Gr Y c x y' → y = y')
    (hst : Work.WilC4.ULPMStruct Y B)
    {c : Fin k → ℝ} {M x : ℝ} (hM : 2 ≤ M) (hx : 0 < x)
    (hdeep : Work.WilC4.IsDeepR B c M x) :
    MonotoneOn (fun s : ℝ => Work.WilC4.Route.ratioY Y c (x * s)) (Set.Ioo (1 / M) M) ∨
      AntitoneOn (fun s : ℝ => Work.WilC4.Route.ratioY Y c (x * s)) (Set.Ioo (1 / M) M) := by
  obtain ⟨hgood, hthree⟩ := hst
  have hMpos : 0 < M := by linarith
  have h2M : 0 < 2 * M := by linarith
  -- the working interval `(x/M, x*M)` is contained in the deep window `(x/(2M), 2Mx)` of `B`
  have hax : x / (2 * M) < x / M := by rw [div_lt_div_iff₀ h2M hMpos]; nlinarith
  have hxb : x * M < 2 * M * x := by nlinarith [hM, hx]
  have hsub : x / M < x * M := by
    rw [div_lt_iff₀ hMpos]
    nlinarith [mul_lt_mul_of_pos_left (show (1 : ℝ) < M * M by nlinarith) hx]
  have hfree : ∀ z ∈ Set.Ioo (x / M) (x * M), Fin.cons z c ∉ B := fun z hz =>
    deep_free hdeep z ⟨lt_trans hax hz.1, lt_trans hz.2 hxb⟩
  -- three-point betweenness of `s ↦ ratioY Y c (x * s)` on `(1/M, M)`, from `ULPMStruct`
  have hab : (1 : ℝ) / M < M := by rw [div_lt_iff₀ hMpos]; nlinarith
  refine mono_of_three_point (f := fun s : ℝ => Route.ratioY Y c (x * s))
    (a := 1 / M) (b := M) hab ?_
  intro s₁ s₂ s₃ hs₁ hs₂ hs₃ h12 h23
  exact hthree c (x / M) (x * M) hsub hfree (x * s₁) (x * s₂) (x * s₃) _ _ _
    (mul_mem_Ioo hx hs₁) (mul_mem_Ioo hx hs₂) (mul_mem_Ioo hx hs₃)
    (mul_lt_mul_of_pos_left h12 hx) (mul_lt_mul_of_pos_left h23 hx)
    (ratW_ratioY_of_deep hfun hgood hM hx hdeep (mul_mem_Ioo hx hs₁))
    (ratW_ratioY_of_deep hfun hgood hM hx hdeep (mul_mem_Ioo hx hs₂))
    (ratW_ratioY_of_deep hfun hgood hM hx hdeep (mul_mem_Ioo hx hs₃))

end Work.WilC4
