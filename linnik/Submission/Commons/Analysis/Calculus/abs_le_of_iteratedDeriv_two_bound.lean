import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Topology.Algebra.Module.ModuleTopology

namespace Commons.Analysis.Calculus

/-- Real-valued version of `dist_deriv_sub_le_of_iteratedDeriv_two_bound`:
if `f` is `C²` on `(0, x₀)` with `‖f''‖ ≤ B` there, then `deriv f` is `B`-Lipschitz on `(0, x₀)`. -/
lemma abs_deriv_sub_le_of_iteratedDeriv_two_bound {x₀ B : ℝ} (_hx₀ : 0 < x₀) {f : ℝ → ℝ}
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) :
    ∀ u ∈ Set.Ioo (0:ℝ) x₀, ∀ v ∈ Set.Ioo (0:ℝ) x₀, |deriv f u - deriv f v| ≤ B * |u - v| := by
  intro u hu v hv
  set s : Set ℝ := Set.Ioo 0 x₀ with hs_def
  have hsopen : IsOpen s := isOpen_Ioo
  have hs_unique : UniqueDiffOn ℝ s := hsopen.uniqueDiffOn
  have hh := (contDiffOn_nat_iff_continuousOn_differentiableOn_deriv (n := 2) hs_unique).mp hf2
  have hdiffWithin : DifferentiableOn ℝ (iteratedDerivWithin 1 f s) s := hh.2 1 (by norm_num)
  have heq : Set.EqOn (deriv f) (iteratedDerivWithin 1 f s) s := by
    intro x hx
    rw [iteratedDerivWithin_of_isOpen hsopen hx, iteratedDeriv_one]
  have hdiff : DifferentiableOn ℝ (deriv f) s := hdiffWithin.congr heq
  have hdiffAt : ∀ x ∈ s, DifferentiableAt ℝ (deriv f) x := fun x hx =>
    hdiff.differentiableAt (hsopen.mem_nhds hx)
  have h2 : deriv (deriv f) = iteratedDeriv 2 f := by
    ext t
    rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one]
  have hbound : ∀ x ∈ s, ‖deriv (deriv f) x‖ ≤ B := by
    intro x hx
    rw [congrFun h2 x]
    exact hBnd x hx
  have hconv : Convex ℝ s := convex_Ioo _ _
  have hmain := hconv.norm_image_sub_le_of_norm_deriv_le hdiffAt hbound hv hu
  simpa using hmain

theorem abs_le_of_iteratedDeriv_two_bound {x₀ B : ℝ} (hx₀ : 0 < x₀) {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici 0)) (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0)
    (hf2 : ContDiffOn ℝ 2 f (Set.Ioo 0 x₀))
    (hBnd : ∀ t ∈ Set.Ioo (0:ℝ) x₀, ‖iteratedDeriv 2 f t‖ ≤ B) :
    ∀ t ∈ Set.Ioo (0:ℝ) x₀, |f t| ≤ B * x₀ ^ 2 + |f 0| := by
  have hB : 0 ≤ B := by
    have hmem : x₀ / 2 ∈ Set.Ioo (0:ℝ) x₀ := ⟨by linarith, by linarith⟩
    have h := hBnd (x₀ / 2) hmem
    have h2 : (0:ℝ) ≤ ‖iteratedDeriv 2 f (x₀ / 2)‖ := norm_nonneg _
    linarith
  have hx₀ne : x₀ ≠ 0 := ne_of_gt hx₀
  have hLip := abs_deriv_sub_le_of_iteratedDeriv_two_bound hx₀ hf2 hBnd
  intro t ht
  have ht0 : 0 < t := ht.1
  have htx : t < x₀ := ht.2
  set c0 : ℝ := f 0 / x₀ with hc0
  set h : ℝ → ℝ := fun s => f s - c0 * (x₀ - s) with hh_def
  have hh0 : h 0 = 0 := by
    simp only [hh_def]
    rw [sub_zero, hc0, div_mul_cancel₀ _ hx₀ne, sub_self]
  have hhx : h x₀ = 0 := by
    simp only [hh_def]
    rw [hsupp x₀ le_rfl, sub_self, mul_zero, sub_zero]
  -- derivative of h
  have hderiv : ∀ s ∈ Set.Ioo (0:ℝ) x₀, HasDerivAt h (deriv f s + c0) s := by
    intro s hs
    show HasDerivAt (fun y : ℝ => f y - c0 * (x₀ - y)) (deriv f s + c0) s
    have hfd : HasDerivAt f (deriv f s) s := by
      have hd : DifferentiableAt ℝ f s :=
        (hf2.contDiffAt (isOpen_Ioo.mem_nhds hs)).differentiableAt (by norm_num)
      exact hd.hasDerivAt
    have hlin : HasDerivAt (fun y : ℝ => c0 * (x₀ - y)) (-c0) s := by
      have h0 := ((hasDerivAt_const s x₀).sub (hasDerivAt_id s)).const_mul c0
      have hthis : c0 * (0 - 1) = -c0 := by ring
      rw [hthis] at h0
      exact h0
    have hraw := hfd.sub hlin
    have hval : deriv f s - (-c0) = deriv f s + c0 := by ring
    rw [hval] at hraw
    exact hraw
  -- continuity of h on the two subintervals
  have hcont0t : ContinuousOn h (Set.Icc (0:ℝ) t) := by
    have hf : ContinuousOn f (Set.Icc (0:ℝ) t) := hcont.mono (fun s hs => hs.1)
    have hlin : ContinuousOn (fun s : ℝ => c0 * (x₀ - s)) (Set.Icc (0:ℝ) t) :=
      continuousOn_const.mul (continuousOn_const.sub continuousOn_id)
    exact (show ContinuousOn (fun s : ℝ => f s - c0 * (x₀ - s)) (Set.Icc (0:ℝ) t) from
      hf.sub hlin)
  have hconttx : ContinuousOn h (Set.Icc t x₀) := by
    have hf : ContinuousOn f (Set.Icc t x₀) :=
      hcont.mono (fun s hs => le_trans (le_of_lt ht0) hs.1)
    have hlin : ContinuousOn (fun s : ℝ => c0 * (x₀ - s)) (Set.Icc t x₀) :=
      continuousOn_const.mul (continuousOn_const.sub continuousOn_id)
    exact (show ContinuousOn (fun s : ℝ => f s - c0 * (x₀ - s)) (Set.Icc t x₀) from
      hf.sub hlin)
  -- first MVT on [0, t]
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope h (fun s => deriv f s + c0) ht0 hcont0t
    (fun s hs => hderiv s ⟨hs.1, lt_trans hs.2 htx⟩)
  -- second MVT on [t, x₀]
  obtain ⟨d, hd_mem, hdeq⟩ := exists_hasDerivAt_eq_slope h (fun s => deriv f s + c0) htx hconttx
    (fun s hs => hderiv s ⟨lt_trans ht0 hs.1, hs.2⟩)
  have hc_eq : (deriv f c + c0) * t = h t := by
    have hne : (t:ℝ) - 0 ≠ 0 := by simpa using ne_of_gt ht0
    have h' := (eq_div_iff hne).mp hceq
    simpa [hh0] using h'
  have hd_eq : (deriv f d + c0) * (x₀ - t) = -(h t) := by
    have hne : x₀ - t ≠ 0 := sub_ne_zero.mpr (ne_of_gt htx)
    have h' := (eq_div_iff hne).mp hdeq
    rw [hhx] at h'
    simpa using h'
  have hkey : h t * x₀ = t * (x₀ - t) * (deriv f c - deriv f d) := by
    linear_combination -(x₀ - t) * hc_eq + t * hd_eq
  have habs_key : |h t| * x₀ = t * (x₀ - t) * |deriv f c - deriv f d| := by
    have h1 : |h t * x₀| = |h t| * x₀ := by rw [abs_mul, abs_of_pos hx₀]
    rw [← h1, hkey, abs_mul, abs_mul, abs_of_pos ht0, abs_of_pos (sub_pos.mpr htx)]
  have hcm : c ∈ Set.Ioo (0:ℝ) x₀ := ⟨hc.1, lt_trans hc.2 htx⟩
  have hdm : d ∈ Set.Ioo (0:ℝ) x₀ := ⟨lt_trans ht0 hd_mem.1, hd_mem.2⟩
  have hbound_deriv : |deriv f c - deriv f d| ≤ B * x₀ := by
    have h1 := hLip c hcm d hdm
    have hcd : |c - d| ≤ x₀ := by
      rw [abs_of_neg (sub_neg.mpr (lt_trans hc.2 hd_mem.1))]
      linarith [hd_mem.2, hc.1]
    exact h1.trans (mul_le_mul_of_nonneg_left hcd hB)
  have hprod_le : t * (x₀ - t) ≤ x₀ ^ 2 := by nlinarith [ht0, htx]
  have hprod_nn : 0 ≤ t * (x₀ - t) := mul_nonneg (le_of_lt ht0) (by linarith)
  have hh_bound : |h t| ≤ B * x₀ ^ 2 := by
    have h1 : |h t| * x₀ ≤ t * (x₀ - t) * (B * x₀) := by
      rw [habs_key]
      exact mul_le_mul_of_nonneg_left hbound_deriv hprod_nn
    have h2 : |h t| * x₀ ≤ (B * x₀ ^ 2) * x₀ := by
      calc |h t| * x₀ ≤ t * (x₀ - t) * (B * x₀) := h1
        _ = B * (t * (x₀ - t)) * x₀ := by ring
        _ ≤ B * x₀ ^ 2 * x₀ := by
              apply mul_le_mul_of_nonneg_right _ (le_of_lt hx₀)
              exact mul_le_mul_of_nonneg_left hprod_le hB
    exact le_of_mul_le_mul_right h2 hx₀
  have hft : f t = h t + c0 * (x₀ - t) := by
    simp only [hh_def]
    ring
  rw [hft]
  calc |h t + c0 * (x₀ - t)| ≤ |h t| + |c0 * (x₀ - t)| := abs_add_le _ _
    _ ≤ B * x₀ ^ 2 + |f 0| := by
          apply add_le_add hh_bound
          rw [abs_mul, hc0, abs_div, abs_of_pos hx₀, abs_of_pos (sub_pos.mpr htx)]
          calc |f 0| / x₀ * (x₀ - t) ≤ |f 0| / x₀ * x₀ :=
                mul_le_mul_of_nonneg_left (by linarith [ht0])
                  (div_nonneg (abs_nonneg _) (le_of_lt hx₀))
            _ = |f 0| := div_mul_cancel₀ _ hx₀ne

end Commons.Analysis.Calculus