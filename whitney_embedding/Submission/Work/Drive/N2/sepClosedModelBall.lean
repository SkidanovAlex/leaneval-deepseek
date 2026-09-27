import Mathlib
import Submission.Work.Drive.N2.windowDatum
-- NOTE (H8, 2026-09-27): the import of `Submission.Work.Drive.N2.levelSeparatingMap` that used to be
-- here was *unused* (this file's proof only uses `WindowDatum` fields: `hCball`, `hCcl`, `hφ`,
-- `hval`, `mem_K_of_mem_other`, `chartQ`) and it created an import *cycle* for the D2 endgame: the
-- chain `N2Lead/landingWide_band → N2/swlLanding → N2/sepClosedModelBall → N2/levelSeparatingMap`
-- put `Work.Drive.N2.levelSeparatingMap` (hence the D2 holder `Work.N2C.exists_certifiedWindow_saddle`
-- that it imports) into the closure of `Work.Drive.N2Lead.saddlePin_oneComp_or`, so that no file
-- imported by `levelSeparatingMap` could use the dichotomy.  Removed here; nothing else changed.

namespace Work.Drive.N2

/-- **The value separation of the closure of a model ball.**  The datum `WindowDatum` supplies the
separation `2 * ηd ≤ |f z - f (x j)|` on the *open* model balls of the charts other than the marked
one (`WindowDatum.mem_K_of_mem_other`); the consumers (the legality rows of the critical-window
drawing) need it on the *closures* of those balls.

The closure of a model ball is contained in the chart's source (`modelBall ⊆ C i` and
`closure (C i) ⊆ (φ i).source`), and on that source `f` agrees with the smooth function
`f (x i) + chartQ (φ i) (s₁ i) (s₂ i)`, hence is continuous there; continuity of the value function
on an open neighbourhood of the closure then upgrades the strict inequality on the open ball to the
non-strict inequality on the closure. -/
theorem sepClosedModelBall {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {p : M} (D : Work.Drive.N2.WindowDatum f p)
    {i : Fin D.N} (hi : i ≠ D.j) :
    ∀ y ∈ closure (Work.Drive.N2.modelBall (D.φ i) (D.ρ i / 8)),
      2 * D.ηd ≤ |f y - f p| := by
  intro y hy
  -- the closure of the ball lies in the chart's source
  have hcl_sub_s : closure (modelBall (D.φ i) (D.ρ i / 8)) ⊆ (D.φ i).source :=
    (closure_mono (D.hCball i)).trans (D.hCcl i).2
  have hy_s : y ∈ (D.φ i).source := hcl_sub_s hy
  -- `f` is continuous on the chart's source: it is the chart's quadratic normal form there
  have hQcont : ContinuousOn (fun z : M => chartQ (D.φ i) (D.s₁ i) (D.s₂ i) z)
      (D.φ i).source := by
    have hpoly : Continuous fun z : EuclideanSpace ℝ (Fin 2) =>
        D.s₁ i * (z 0) ^ 2 + D.s₂ i * (z 1) ^ 2 := by fun_prop
    have h := hpoly.comp_continuousOn (D.hφ i).continuousOn
    simpa [chartQ, Function.comp_def] using h
  have hfcont : ContinuousOn f (D.φ i).source := by
    have h : ContinuousOn (fun z : M => f (D.x i) + chartQ (D.φ i) (D.s₁ i) (D.s₂ i) z)
        (D.φ i).source :=
      (continuousOn_const (c := f (D.x i))).add hQcont
    exact h.congr (fun z hz => D.hval i z hz)
  have hgcont : ContinuousOn (fun z : M => |f z - f p|) (D.φ i).source :=
    (hfcont.sub continuousOn_const).abs
  -- the set of "bad" points (`|f · - f p| < 2 * ηd`) is open relative to the chart's source
  have hopen : IsOpen ((D.φ i).source ∩
      (fun z : M => |f z - f p|) ⁻¹' Set.Iio (2 * D.ηd)) :=
    hgcont.isOpen_inter_preimage (D.φ i).open_source isOpen_Iio
  have hclosed : IsClosed ((D.φ i).source ∩
      (fun z : M => |f z - f p|) ⁻¹' Set.Iio (2 * D.ηd))ᶜ := hopen.isClosed_compl
  -- the open ball carries no such point, so the closure carries none either
  have hball_sub : modelBall (D.φ i) (D.ρ i / 8) ⊆
      ((D.φ i).source ∩ (fun z : M => |f z - f p|) ⁻¹' Set.Iio (2 * D.ηd))ᶜ := by
    intro z hz hzmem
    obtain ⟨-, hzlt⟩ := hzmem
    simp only [Set.mem_preimage, Set.mem_Iio] at hzlt
    have h := D.mem_K_of_mem_other hi hz
    rw [D.hxj] at h
    exact absurd h (not_le.mpr hzlt)
  have hyV : y ∈ ((D.φ i).source ∩
      (fun z : M => |f z - f p|) ⁻¹' Set.Iio (2 * D.ηd))ᶜ :=
    (hclosed.closure_subset_iff).mpr hball_sub hy
  by_contra hcon
  exact hyV ⟨hy_s, not_le.mp hcon⟩

end Work.Drive.N2
