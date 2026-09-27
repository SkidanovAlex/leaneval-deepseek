import Mathlib
import Submission.Work.Drive.PushDisc.lensWiringDefs

namespace Work.Drive.PushDisc

open Set Metric

/-- Chain rule in the `x`-slot for a smooth map on `ℝ × ℝ^k`: the derivative of the slice
`t ↦ S (t, 0)` is the derivative of `S` at `(x,0)` restricted by `inl`. -/
theorem fderiv_slice_zero {k : ℕ} (S : ℝ × EuclideanSpace ℝ (Fin k) → Work.Drive.Whitney.Mdl k)
    (hS : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S) (x : ℝ) :
    fderiv ℝ (fun t : ℝ => S (t, (0 : EuclideanSpace ℝ (Fin k)))) x
      = (fderiv ℝ S (x, 0)).comp (ContinuousLinearMap.inl ℝ ℝ (EuclideanSpace ℝ (Fin k))) := by
  have hSx : HasFDerivAt S (fderiv ℝ S (x, 0)) (x, 0) :=
    (hS.contDiffAt.differentiableAt (by simp)).hasFDerivAt
  have h1 : HasFDerivAt (fun t : ℝ => (t, (0 : EuclideanSpace ℝ (Fin k))))
      (ContinuousLinearMap.inl ℝ ℝ (EuclideanSpace ℝ (Fin k))) x :=
    hasFDerivAt_prodMk_left x (0 : EuclideanSpace ℝ (Fin k))
  simpa [Function.comp_def] using (hSx.comp x h1).fderiv

/-- **The `B = S₂ (·,0)` rows of the finger.**  With `Φ₀` the flat-tube chart and `c` the finger's
`(x,v)`-chart straightening the second arc `γ₂` to the axis:

* `B` is injective on `[-1,1]` and its derivative vanishes nowhere (it is the axis slice of the
  injective, immersive parametrisation `S₂` on its window);
* `B` meets the model axis `(x,0,0,0)` only at the two corners `±1`, and there the parameters agree
  — this is the cleanliness of the bigon: `(x',0,0,0) = Φ₀ (f (γ₁ s))` is the first arc's image, so
  `f (γ₂ t) = f (γ₁ s)` forces `(s,t) = (0,0)` or `(1,1)` by `hγend`;
* `B (±1) = (±1,0,0,0)` are the pinned corners `Φ₀ (f p₂) = (-1,0,0,0)`, `Φ₀ (f q₂) = (1,0,0,0)`. -/
theorem lensFingerBRows {k : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (k + 1))) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (k + 1)))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M]
    (C : Work.Drive.PushDisc.LWConfig (k + 1) M)
    (T : Work.Drive.PushDisc.LWFlatTube k M C)
    (F : Work.Drive.PushDisc.LWFingerChart k M C)
    (G : Work.Drive.PushDisc.LWFingerData k M C T F) :
    Set.InjOn (fun x : ℝ => G.S₂ (x, (0 : EuclideanSpace ℝ (Fin k)))) (Set.Icc (-1 : ℝ) 1)
    ∧ (∀ x ∈ Set.Icc (-1 : ℝ) 1,
        fderiv ℝ (fun t : ℝ => G.S₂ (t, (0 : EuclideanSpace ℝ (Fin k)))) x 1 ≠ 0)
    ∧ (∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ x' ∈ Set.Icc (-1 : ℝ) 1,
        G.S₂ (x, (0 : EuclideanSpace ℝ (Fin k))) = (x', 0, 0, 0) →
          x = x' ∧ (x = 1 ∨ x = -1))
    ∧ G.S₂ (1, (0 : EuclideanSpace ℝ (Fin k))) = ((1 : ℝ), 0, 0, 0)
    ∧ G.S₂ (-1, (0 : EuclideanSpace ℝ (Fin k))) = ((-1 : ℝ), 0, 0, 0) := by
  classical
  -- `Φ₀` is injective, with left inverse `Θ₀`
  have hΦinj : Function.Injective T.Φ₀ := fun a b hab => by
    rw [← T.hΘ₀Φ₀ a, hab, T.hΘ₀Φ₀ b]
  -- the segment `[-1,1]` of the axis lies in the window of the finger's chart
  have hXt : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |x| ≤ F.X' := by
    intro x hx
    have h1 : |x| ≤ 1 := abs_le.mpr ⟨hx.1, hx.2⟩
    linarith [F.hX']
  have hwin : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      (x, (0 : EuclideanSpace ℝ (Fin k))) ∈
        {p : ℝ × EuclideanSpace ℝ (Fin k) | |p.1| ≤ F.X' ∧ ‖p.2‖ ≤ F.r} := by
    intro x hx
    exact ⟨hXt x hx, by simpa using F.hr.le⟩
  -- the chart-inverse of an axis point is the point of the second arc with the same parameter
  have hsymm : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      F.c.symm (splitE k (x, (0 : EuclideanSpace ℝ (Fin k)))) = C.γ₂ ((x + 1) / 2) := by
    intro x hx
    have hmem : splitE k (x, (0 : EuclideanSpace ℝ (Fin k))) ∈ F.c.target := by
      have h := F.hwin (x, (0 : EuclideanSpace ℝ (Fin k))) (hXt x hx) (by simp)
      simpa using h
    have hs : (x + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hsrc : C.γ₂ ((x + 1) / 2) ∈ F.c.source := F.hcarc ⟨(x + 1) / 2, hs, rfl⟩
    have hce : F.c (C.γ₂ ((x + 1) / 2)) = splitE k (x, (0 : EuclideanSpace ℝ (Fin k))) := by
      have h := F.harc₂ ((x + 1) / 2) hs
      have h2 : (2 : ℝ) * ((x + 1) / 2) - 1 = x := by ring
      rwa [h2] at h
    have hone : F.c (F.c.symm (splitE k (x, (0 : EuclideanSpace ℝ (Fin k)))))
        = F.c (C.γ₂ ((x + 1) / 2)) := by
      rw [F.c.right_inv hmem, hce]
    exact F.c.injOn (F.c.map_target hmem) hsrc hone
  -- the axis slice of the finger is the second arc, read in the flat-tube chart
  have hS₂ax : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      G.S₂ (x, (0 : EuclideanSpace ℝ (Fin k))) = T.Φ₀ (C.f (C.γ₂ ((x + 1) / 2))) := by
    intro x hx
    rw [G.hS₂ag (x, (0 : EuclideanSpace ℝ (Fin k))) (hXt x hx) (by simpa using F.hr.le),
      hsymm x hx]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- `B` is injective
    intro x hx x' hx' h
    exact (Prod.ext_iff.mp (G.hS₂inj (hwin x hx) (hwin x' hx') h)).1
  · -- the derivative of `B` vanishes nowhere
    intro x hx hzero
    rw [fderiv_slice_zero G.S₂ G.hS₂sm x, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inl_apply] at hzero
    have hinj := G.hS₂imm (x, (0 : EuclideanSpace ℝ (Fin k))) (hwin x hx)
    have hne : ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k)))
        ≠ (0 : ℝ × EuclideanSpace ℝ (Fin k)) := by
      intro hh
      exact one_ne_zero (α := ℝ) (by simpa using congrArg Prod.fst hh)
    exact hne (hinj (by rw [hzero, map_zero]))
  · -- `B` meets the axis only at the corners
    intro x hx x' hx' heq
    have ht : (x + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hs : (x' + 1) / 2 ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
    have hf : C.f (C.γ₁ ((x' + 1) / 2)) = C.f (C.γ₂ ((x + 1) / 2)) := by
      apply hΦinj
      have h2 : (2 : ℝ) * ((x' + 1) / 2) - 1 = x' := by ring
      rw [T.harc₁ ((x' + 1) / 2) hs, h2, ← hS₂ax x hx, heq]
    rcases C.hγend ((x' + 1) / 2) hs ((x + 1) / 2) ht hf with ⟨h0, h1⟩ | ⟨h0, h1⟩
    · exact ⟨by linarith, Or.inr (by linarith)⟩
    · exact ⟨by linarith, Or.inl (by linarith)⟩
  · -- the corner `x = 1`
    have hx : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨by norm_num, le_refl 1⟩
    rw [hS₂ax 1 hx, show ((1 : ℝ) + 1) / 2 = 1 by norm_num, C.hγ₂1]
    exact T.hpin₄
  · -- the corner `x = -1`
    have hx : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := ⟨le_refl _, by norm_num⟩
    rw [hS₂ax (-1) hx, show ((-1 : ℝ) + 1) / 2 = 0 by norm_num, C.hγ₂0]
    exact T.hpin₂

end Work.Drive.PushDisc
