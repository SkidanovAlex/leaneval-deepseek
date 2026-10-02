import Mathlib
import Submission.Work.ThomBordism.Transversality.Sard.volume_range_eq_zero_of_contDiff_finrank_lt

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Smooth approximation of a continuous map by a nowhere-vanishing map

Let `K₁ ⊆ K₂ ⊆ ℝ^d` be compact sets, `d < k`, and let `h : K₂ → ℝ^k` be continuous.  Then any
`ε > 0` admits a `C^∞` map `P : ℝ^d → ℝ^k` which is `ε`-close to `h` on `K₂` and is
nowhere zero on `K₁`.

The proof extends `h` to a continuous map on `ℝ^d` (Tietze), approximates it by a `C^∞` map
`g` (Mathlib's `Continuous.exists_contDiff_approx`), and then shifts `g` by a small vector `c`
which is not a value of `g`.  Since `d < k`, the image of the smooth map `g` is Lebesgue-null
(the low-dimensional case of Sard's theorem,
`Work.ThomBordism.Transversality.Sard.volume_range_eq_zero_of_contDiff_finrank_lt`), so such a
small `c` exists.
-/

namespace Work.AttachPush

open MeasureTheory

theorem exists_contDiff_approx_ne_zero {d k : ℕ} (hdk : d < k)
    {K₁ K₂ : Set (EuclideanSpace ℝ (Fin d))} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
    (hsub : K₁ ⊆ K₂) (h : C(↥K₂, EuclideanSpace ℝ (Fin k))) {ε : ℝ} (hε : 0 < ε) :
    ∃ P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin k),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) P ∧ (∀ x : ↥K₂, ‖P x - h x‖ < ε) ∧
        (∀ x : ↥K₁, P x ≠ 0) := by
  -- Extend `h` to all of `ℝ^d` by Tietze.
  obtain ⟨hext, hext_eq⟩ := ContinuousMap.exists_restrict_eq hK₂.isClosed h
  have hh : ∀ x : ↥K₂, hext (x : EuclideanSpace ℝ (Fin d)) = h x := fun x => by
    rw [← ContinuousMap.restrict_apply]; exact congr($(hext_eq) x)
  -- Smooth approximation of the extension on all of `ℝ^d`.
  obtain ⟨g, hg_smooth, hg_approx, -⟩ :=
    hext.continuous.exists_contDiff_approx (⊤ : ℕ∞)
      (continuous_const : Continuous (fun _ : EuclideanSpace ℝ (Fin d) => ε / 2))
      (fun _ => by linarith)
  -- Low-dimensional Sard: the image of `g` is Lebesgue-null.
  have hg1 : ContDiff ℝ 1 g := hg_smooth.of_le (by exact_mod_cast le_top)
  have hnull : volume (Set.range g) = 0 :=
    Work.ThomBordism.Transversality.Sard.volume_range_eq_zero_of_contDiff_finrank_lt hdk g hg1
  have hballpos : 0 < volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (ε / 2)) :=
    Metric.measure_ball_pos volume 0 (by linarith)
  -- Pick a small vector `c` which is not a value of `g`.
  obtain ⟨c, hcball, hcnotin⟩ :
      ∃ c ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (ε / 2), c ∉ Set.range g := by
    by_contra hcon
    have hsub' : Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (ε / 2) ⊆ Set.range g := by
      intro c hc
      by_contra hcr
      exact hcon ⟨c, hc, hcr⟩
    have hle : volume (Metric.ball (0 : EuclideanSpace ℝ (Fin k)) (ε / 2)) ≤ 0 := by
      rw [← hnull]; exact measure_mono hsub'
    exact (lt_irrefl (0 : ENNReal)) (lt_of_lt_of_le hballpos hle)
  have hcx : ‖c‖ < ε / 2 := by
    rw [Metric.mem_ball, dist_zero_right] at hcball; exact hcball
  refine ⟨fun x => g x - c, ?_, ?_, ?_⟩
  · simpa using hg_smooth.sub contDiff_const
  · intro x
    have hgx : ‖g (x : EuclideanSpace ℝ (Fin d)) - h x‖ < ε / 2 := by
      have := hg_approx (x : EuclideanSpace ℝ (Fin d))
      rw [dist_eq_norm, hh x] at this; exact this
    have hbound : ‖(g (x : EuclideanSpace ℝ (Fin d)) - c) - h x‖
        ≤ ‖g (x : EuclideanSpace ℝ (Fin d)) - h x‖ + ‖c‖ := by
      rw [show (g (x : EuclideanSpace ℝ (Fin d)) - c) - h x
            = (g (x : EuclideanSpace ℝ (Fin d)) - h x) - c from by abel]
      exact norm_sub_le _ _
    linarith
  · intro x hzero
    exact hcnotin ⟨(x : EuclideanSpace ℝ (Fin d)), sub_eq_zero.mp hzero⟩

end Work.AttachPush
