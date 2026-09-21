import Mathlib

namespace Work.Anchor

open Filter Set
open scoped Topology

noncomputable section

/-- The function obtained from `ψ` on the half-line `[a, ∞)` by extending it by `0` on `(-∞, a)`. -/
private def glue (a : ℝ) (ψ : ℝ → ℝ) : ℝ → ℝ := fun x => if a ≤ x then ψ x else 0

private lemma glue_apply (a : ℝ) (ψ : ℝ → ℝ) (x : ℝ) :
    glue a ψ x = if a ≤ x then ψ x else 0 := rfl

/-- The glued function is continuous as soon as `ψ` is continuous on `[a, ∞)` and vanishes at `a`. -/
private lemma continuous_glue (a : ℝ) (ψ : ℝ → ℝ)
    (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ (Set.Ici a)) (h0 : ψ a = 0) :
    Continuous (glue a ψ) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases lt_trichotomy x a with hx | hx | hx
  · have h1 : glue a ψ =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [IsOpen.mem_nhds isOpen_Iio hx] with y hy
      simp only [Set.mem_Iio] at hy
      simp [glue, not_le.mpr hy]
    exact (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq h1
  · rw [hx]
    rw [continuousAt_iff_continuous_left'_right']
    constructor
    · have h1 : glue a ψ =ᶠ[𝓝[Set.Iio a] a] (fun _ => (0 : ℝ)) := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        simp only [Set.mem_Iio] at hy
        simp [glue, not_le.mpr hy]
      exact (continuousWithinAt_const (b := (0 : ℝ))).congr_of_eventuallyEq h1 (by simp [glue, h0])
    · have h1 : glue a ψ =ᶠ[𝓝[Set.Ioi a] a] ψ := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        simp only [Set.mem_Ioi] at hy
        exact if_pos hy.le
      have h2 : ContinuousWithinAt ψ (Set.Ici a) a := hψ.continuousOn.continuousWithinAt (by simp)
      have h3 : ContinuousWithinAt ψ (Set.Ioi a) a :=
        Filter.Tendsto.mono_left h2 (nhdsWithin_mono a Set.Ioi_subset_Ici_self)
      exact h3.congr_of_eventuallyEq h1 (by simp [glue])
  · have h1 : glue a ψ =ᶠ[𝓝 x] ψ := by
      filter_upwards [IsOpen.mem_nhds isOpen_Ioi hx] with y hy
      simp only [Set.mem_Ioi] at hy
      exact if_pos hy.le
    have h2 : ContinuousAt ψ x :=
      hψ.continuousOn.continuousAt (mem_of_superset (IsOpen.mem_nhds isOpen_Ioi hx)
        Set.Ioi_subset_Ici_self)
    exact h2.congr_of_eventuallyEq h1

/-- The glued function has, at every point, the derivative obtained by gluing the one-sided
derivative `derivWithin ψ (Ici a)`. -/
private lemma hasDerivAt_glue (a : ℝ) (ψ : ℝ → ℝ)
    (hψ : DifferentiableOn ℝ ψ (Set.Ioi a)) (h0 : ψ a = 0)
    (hd : HasDerivWithinAt ψ 0 (Set.Ici a) a) :
    ∀ x, HasDerivAt (glue a ψ) (glue a (derivWithin ψ (Set.Ici a)) x) x := by
  have hda : derivWithin ψ (Set.Ici a) a = 0 := hd.derivWithin (uniqueDiffWithinAt_Ici a)
  have hA : HasDerivAt (glue a ψ) 0 a := by
    have h1 : HasDerivWithinAt (glue a ψ) 0 (Set.Ici a) a :=
      hd.congr (fun y hy => if_pos hy) (by simp [glue])
    have h2 : HasDerivWithinAt (glue a ψ) 0 (Set.Iio a) a :=
      (hasDerivWithinAt_const a (Set.Iio a) (0 : ℝ)).congr
        (fun y hy => by
          simp only [Set.mem_Iio] at hy
          simp [glue, not_le.mpr hy])
        (by simp [glue, h0])
    have h3 := h1.union h2
    rw [Set.Ici_union_Iio] at h3
    exact hasDerivWithinAt_univ.mp h3
  intro x
  rcases lt_trichotomy x a with hx | hx | hx
  · have h1 : glue a ψ =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
      filter_upwards [IsOpen.mem_nhds isOpen_Iio hx] with y hy
      simp only [Set.mem_Iio] at hy
      simp [glue, not_le.mpr hy]
    have h2 : HasDerivAt (glue a ψ) 0 x :=
      (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq h1
    simpa [glue, not_le.mpr hx] using h2
  · rw [hx]
    simpa [glue, hda] using hA
  · have h1 : glue a ψ =ᶠ[𝓝 x] ψ := by
      filter_upwards [IsOpen.mem_nhds isOpen_Ioi hx] with y hy
      simp only [Set.mem_Ioi] at hy
      exact if_pos hy.le
    have h2 : HasDerivAt ψ (deriv ψ x) x :=
      (hψ.differentiableAt (IsOpen.mem_nhds isOpen_Ioi hx)).hasDerivAt
    have h3 : HasDerivAt (glue a ψ) (deriv ψ x) x := h2.congr_of_eventuallyEq h1
    have h4 : deriv ψ x = derivWithin ψ (Set.Ici a) x :=
      (derivWithin_of_mem_nhds (mem_of_superset (IsOpen.mem_nhds isOpen_Ioi hx)
        Set.Ioi_subset_Ici_self)).symm
    rw [h4] at h3
    simpa [glue, hx.le] using h3

private lemma deriv_glue (a : ℝ) (ψ : ℝ → ℝ)
    (hψ : DifferentiableOn ℝ ψ (Set.Ioi a)) (h0 : ψ a = 0)
    (hd : HasDerivWithinAt ψ 0 (Set.Ici a) a) :
    deriv (glue a ψ) = glue a (derivWithin ψ (Set.Ici a)) :=
  funext fun x => (hasDerivAt_glue a ψ hψ h0 hd x).deriv

private lemma differentiable_glue (a : ℝ) (ψ : ℝ → ℝ)
    (hψ : DifferentiableOn ℝ ψ (Set.Ioi a)) (h0 : ψ a = 0)
    (hd : HasDerivWithinAt ψ 0 (Set.Ici a) a) : Differentiable ℝ (glue a ψ) :=
  fun x => (hasDerivAt_glue a ψ hψ h0 hd x).differentiableAt

private lemma differentiableOn_Ioi_of_contDiffOn (a : ℝ) (φ : ℝ → ℝ)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ (Set.Ici a)) : DifferentiableOn ℝ φ (Set.Ioi a) :=
  (hφ.differentiableOn (by simp)).mono Set.Ioi_subset_Ici_self

private lemma eq_zero_at_of_jets (a : ℝ) (φ : ℝ → ℝ)
    (hjet : ∀ k : ℕ, iteratedDerivWithin k φ (Set.Ici a) a = 0) : φ a = 0 := by
  have h := hjet 0
  rwa [iteratedDerivWithin_zero] at h

private lemma hasDerivWithinAt_zero_of_jets (a : ℝ) (φ : ℝ → ℝ)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ (Set.Ici a))
    (hjet : ∀ k : ℕ, iteratedDerivWithin k φ (Set.Ici a) a = 0) :
    HasDerivWithinAt φ 0 (Set.Ici a) a := by
  have hdw : DifferentiableWithinAt ℝ φ (Set.Ici a) a :=
    (hφ.differentiableOn (by simp)) a (by simp)
  have h1 : HasDerivWithinAt φ (derivWithin φ (Set.Ici a) a) (Set.Ici a) a :=
    hdw.hasFDerivWithinAt.hasDerivWithinAt
  have hdr : derivWithin φ (Set.Ici a) a = 0 := by
    rw [← iteratedDerivWithin_one]
    exact hjet 1
  rwa [hdr] at h1

private lemma contDiffOn_derivWithin_of_contDiffOn (a : ℝ) (φ : ℝ → ℝ)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ (Set.Ici a)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (derivWithin φ (Set.Ici a)) (Set.Ici a) := by
  refine hφ.derivWithin (uniqueDiffOn_Ici a) ?_
  simp

private lemma jets_derivWithin_of_jets (a : ℝ) (φ : ℝ → ℝ)
    (hjet : ∀ k : ℕ, iteratedDerivWithin k φ (Set.Ici a) a = 0) :
    ∀ k : ℕ, iteratedDerivWithin k (derivWithin φ (Set.Ici a)) (Set.Ici a) a = 0 := by
  intro k
  rw [← iteratedDerivWithin_succ']
  exact hjet (k + 1)

/-- The glued function is `C^n` on `ℝ`. -/
private lemma contDiff_glue_nat (n : ℕ) (a : ℝ) (φ : ℝ → ℝ)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ (Set.Ici a))
    (hjet : ∀ k : ℕ, iteratedDerivWithin k φ (Set.Ici a) a = 0) :
    ContDiff ℝ n (glue a φ) := by
  induction n generalizing a φ with
  | zero =>
      exact contDiff_zero.mpr (continuous_glue a φ hφ (eq_zero_at_of_jets a φ hjet))
  | succ n ih =>
      rw [show (((n + 1 : ℕ)) : WithTop ℕ∞) = ((n : WithTop ℕ∞) + 1) from rfl]
      rw [contDiff_succ_iff_deriv]
      refine ⟨differentiable_glue a φ (differentiableOn_Ioi_of_contDiffOn a φ hφ)
        (eq_zero_at_of_jets a φ hjet) (hasDerivWithinAt_zero_of_jets a φ hφ hjet), ?_, ?_⟩
      · intro hcon
        exact absurd hcon (by simp)
      · rw [deriv_glue a φ (differentiableOn_Ioi_of_contDiffOn a φ hφ)
          (eq_zero_at_of_jets a φ hjet) (hasDerivWithinAt_zero_of_jets a φ hφ hjet)]
        exact ih a (derivWithin φ (Set.Ici a)) (contDiffOn_derivWithin_of_contDiffOn a φ hφ)
          (jets_derivWithin_of_jets a φ hjet)

end

/-- **Gluing a function that is flat at the endpoint.**  If `φ` is `C^∞` on the half-line `[a,∞)`
and all of its one-sided derivatives at `a` vanish, then extending `φ` by `0` to `(-∞,a)` gives a
`C^∞` function on `ℝ`, all of whose derivatives at `a` vanish. -/
theorem flat_glue (a : ℝ) (φ : ℝ → ℝ)
    (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ (Set.Ici a))
    (hjet : ∀ k : ℕ, iteratedDerivWithin k φ (Set.Ici a) a = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => if a ≤ x then φ x else 0) ∧
      (∀ k : ℕ, iteratedDeriv k (fun x : ℝ => if a ≤ x then φ x else 0) a = 0) := by
  have hmain : ∀ n : ℕ, ContDiff ℝ n (glue a φ) := fun n => contDiff_glue_nat n a φ hφ hjet
  have htop : ContDiff ℝ (⊤ : ℕ∞) (glue a φ) := (contDiff_all_iff_nat.mpr hmain) ⊤
  refine ⟨htop, ?_⟩
  intro k
  have hcontAt : ContDiffAt ℝ (↑k) (glue a φ) a :=
    htop.contDiffAt.of_le (show ((k : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
      WithTop.coe_le_coe.mpr le_top)
  have h1 : iteratedDerivWithin k (glue a φ) (Set.Ici a) a = iteratedDeriv k (glue a φ) a :=
    iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici a) hcontAt (by simp)
  have hcongr : iteratedDerivWithin k (glue a φ) (Set.Ici a) a
      = iteratedDerivWithin k φ (Set.Ici a) a :=
    iteratedDerivWithin_congr (s := Set.Ici a) (f := glue a φ) (g := φ) (n := k)
      (fun y hy => if_pos hy) (by simp)
  have h2 : iteratedDerivWithin k (glue a φ) (Set.Ici a) a = 0 := by
    rw [hcongr, hjet k]
  change iteratedDeriv k (glue a φ) a = 0
  rw [← h1, h2]

end Work.Anchor
