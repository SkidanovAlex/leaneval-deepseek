import Mathlib
import Submission.Work.Drive.N2C.isotopyCalc
import Submission.Work.Compat.MFDerivCongrV433

/-!
# B4: transporting a level isotopy along the level flow (proof)

`Work.Drive.N2C.IsLevelIsotopy f u e` is a jointly smooth family of *pictures* of the level `f = u`:
each `e s` is smooth near the level, injective there, and `ker df`-immersive there.  The present lemma
transports such a family from a level `u` to another level `b`: if `Φ` is a smooth global map of `M`
which moves every point of the value band `Icc lo hi` at *unit speed with respect to `f`*
(`f (Φ (t, x)) = f x + t`, whenever both `f x` and `f x + t` lie in the band) and satisfies the
conditional composition law on the band, and if `u, b ∈ Ioo lo hi`, then

    (s, y) ↦ e s (Φ (u - b, y))

is again a level isotopy at `b`.  The three rows are:

* smoothness: `Φ (u - b, ·)` maps the level `b` into the level `u` (`f_frozen_of_level`), where `e`
  is smooth;
* injectivity: `Φ (u - b, ·)` is injective on the level `b`, because its inverse there is the frozen
  transport `Φ (b - u, ·)` (`frozen_eq_of_level`, the conditional composition law `hΦcomp`);
* immersion: for a point `y` of the level `b` the two frozen transports `Φ (u - b, ·)` and
  `Φ (b - u, ·)` are mutually inverse *on a neighbourhood of `y`* (the value band is open, so the
  conditional laws apply on a neighbourhood), hence

      `d(Φ (b - u, ·))_{Φ (u - b, y)} ∘ d(Φ (u - b, ·))_y = id`.

  Writing `w = d(Φ (u - b, ·))_y v`, the two chain rules give `df (Φ (u - b, y)) w = df_y v = 0` and
  `d(e s)_{Φ (u - b, y)} w = d(e s ∘ Φ (u - b, ·))_y v = 0`, so the immersion row of `e` at the level
  `u` gives `w = 0`, and the identity above gives `v = 0`.

The band neighbourhood is packaged as `bandShift f lo hi c`; everything else is the chain rule.
-/

namespace Work.Drive.N2C

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Filter

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

variable {f : M → ℝ} {Φ : ℝ × M → M} {lo hi : ℝ}

/-! ### The band of the times available at a point -/

/-- The open set of points `x` for which both `f x` and the shifted value `f x + c` lie in `(lo, hi)`:
on it the conditional flow laws `hΦf` and `hΦcomp` are available for the time `c` and its negative. -/
def bandShift (f : M → ℝ) (lo hi c : ℝ) : Set M :=
  f ⁻¹' Set.Ioo (max lo (lo - c)) (min hi (hi - c))

lemma isOpen_bandShift {c : ℝ} (hf : Continuous f) : IsOpen (bandShift f lo hi c) :=
  isOpen_Ioo.preimage hf

lemma mem_bandShift_iff {c : ℝ} {x : M} :
    x ∈ bandShift f lo hi c ↔ max lo (lo - c) < f x ∧ f x < min hi (hi - c) := Iff.rfl

/-- Membership in the band set, from the four value inequalities. -/
lemma mem_bandShift_of {c : ℝ} {x : M} (h1 : lo < f x) (h2 : f x < hi)
    (h3 : lo < f x + c) (h4 : f x + c < hi) : x ∈ bandShift f lo hi c := by
  rw [bandShift, Set.mem_preimage, Set.mem_Ioo, max_lt_iff, lt_min_iff]
  exact ⟨⟨h1, by linarith⟩, ⟨h2, by linarith⟩⟩

/-- The two value rows of a point of the band set. -/
lemma band_rows {c : ℝ} {x : M} (hx : x ∈ bandShift f lo hi c) :
    f x ∈ Set.Icc lo hi ∧ f x + c ∈ Set.Icc lo hi :=
  ⟨⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hx.1),
    le_of_lt (lt_of_lt_of_le hx.2 (min_le_left _ _))⟩,
   ⟨by linarith [le_max_right lo (lo - c), hx.1],
    by linarith [min_le_right hi (hi - c), hx.2]⟩⟩

/-- **The conditional composition law at a point of the band set**, written for the time `c` and its
negative: the frozen transports `Φ (c, ·)` and `Φ (-c, ·)` are mutually inverse at `x`. -/
lemma frozen_comp_inv {c : ℝ} {x : M} (hx : x ∈ bandShift f lo hi c)
    (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦcomp : ∀ (x : M) (s t : ℝ), f x ∈ Set.Icc lo hi → f x + t ∈ Set.Icc lo hi →
      f x + t + s ∈ Set.Icc lo hi → Φ (s, Φ (t, x)) = Φ (s + t, x)) :
    Φ (-c, Φ (c, x)) = x := by
  obtain ⟨h1, h2⟩ := band_rows hx
  have h3 : f x + c + (-c) ∈ Set.Icc lo hi := by
    rw [show f x + c + (-c) = f x by ring]; exact h1
  have h := hΦcomp x (-c) c h1 h2 h3
  rw [neg_add_cancel, hΦ0 x] at h
  exact h

/-- **The unit-speed law at a point of the band set.** -/
lemma frozen_value {c : ℝ} {x : M} (hx : x ∈ bandShift f lo hi c)
    (hΦf : ∀ (x : M) (t : ℝ), f x ∈ Set.Icc lo hi → f x + t ∈ Set.Icc lo hi →
      f (Φ (t, x)) = f x + t) :
    f (Φ (c, x)) = f x + c :=
  hΦf x c (band_rows hx).1 (band_rows hx).2

/-- A point of the level `b` lies in the band set for the time `u - b`, when `u, b ∈ (lo, hi)`. -/
lemma mem_bandShift_of_eq_level {b u : ℝ} (hb : b ∈ Set.Ioo lo hi) (hu : u ∈ Set.Ioo lo hi)
    {x : M} (hx : f x = b) : x ∈ bandShift f lo hi (u - b) :=
  mem_bandShift_of (f := f) (c := u - b) (by rw [hx]; exact hb.1) (by rw [hx]; exact hb.2)
    (by rw [hx]; linarith [hu.1]) (by rw [hx]; linarith [hu.2])

/-- **The frozen transport at a level point, and its inverse.**  For a point of the level `b` (with
`u, b` in the band `(lo, hi)`), the transports by `u - b` and `b - u` are mutually inverse. -/
lemma frozen_eq_of_level {b u : ℝ} (hb : b ∈ Set.Ioo lo hi) (hu : u ∈ Set.Ioo lo hi)
    (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦcomp : ∀ (x : M) (s t : ℝ), f x ∈ Set.Icc lo hi → f x + t ∈ Set.Icc lo hi →
      f x + t + s ∈ Set.Icc lo hi → Φ (s, Φ (t, x)) = Φ (s + t, x))
    {x : M} (hx : f x = b) :
    Φ (b - u, Φ (u - b, x)) = x := by
  have h := frozen_comp_inv (f := f) (Φ := Φ) (lo := lo) (hi := hi)
    (mem_bandShift_of_eq_level (f := f) hb hu hx) hΦ0 hΦcomp
  rw [show -(u - b) = b - u by ring] at h
  exact h

/-- **The transported point lies on the level `u`.** -/
lemma f_frozen_of_level {b u : ℝ} (hb : b ∈ Set.Ioo lo hi) (hu : u ∈ Set.Ioo lo hi)
    (hΦf : ∀ (x : M) (t : ℝ), f x ∈ Set.Icc lo hi → f x + t ∈ Set.Icc lo hi →
      f (Φ (t, x)) = f x + t)
    {x : M} (hx : f x = b) : f (Φ (u - b, x)) = u := by
  have h := frozen_value (c := u - b) (mem_bandShift_of_eq_level hb hu hx) hΦf
  rw [hx, show b + (u - b) = u by ring] at h
  exact h

/-- **The two frozen transports are mutually inverse near every point of the level `b`.** -/
lemma eventually_frozen_comp_inv {b u : ℝ} (hf : Continuous f) (hb : b ∈ Set.Ioo lo hi)
    (hu : u ∈ Set.Ioo lo hi) (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦcomp : ∀ (x : M) (s t : ℝ), f x ∈ Set.Icc lo hi → f x + t ∈ Set.Icc lo hi →
      f x + t + s ∈ Set.Icc lo hi → Φ (s, Φ (t, x)) = Φ (s + t, x))
    {y : M} (hy : f y = b) :
    (fun z : M => Φ (b - u, Φ (u - b, z))) =ᶠ[𝓝 y] id := by
  filter_upwards [(isOpen_bandShift (f := f) (lo := lo) (hi := hi) (c := u - b) hf).mem_nhds
    (mem_bandShift_of_eq_level (f := f) hb hu hy)] with z hz
  have h := frozen_comp_inv (f := f) (Φ := Φ) (lo := lo) (hi := hi) hz hΦ0 hΦcomp
  rw [show -(u - b) = b - u by ring] at h
  exact h

/-- **The unit-speed law near every point of the level `b`.** -/
lemma eventually_frozen_value {b u : ℝ} (hf : Continuous f) (hb : b ∈ Set.Ioo lo hi)
    (hu : u ∈ Set.Ioo lo hi)
    (hΦf : ∀ (x : M) (t : ℝ), f x ∈ Set.Icc lo hi → f x + t ∈ Set.Icc lo hi →
      f (Φ (t, x)) = f x + t)
    {y : M} (hy : f y = b) :
    (fun z : M => f (Φ (u - b, z))) =ᶠ[𝓝 y] (fun z : M => f z + (u - b)) := by
  filter_upwards [(isOpen_bandShift (f := f) (lo := lo) (hi := hi) (c := u - b) hf).mem_nhds
    (mem_bandShift_of_eq_level (f := f) hb hu hy)] with z hz
  exact frozen_value (f := f) hz hΦf

/-! ## B4 -/

open scoped Manifold ContDiff Topology in
/-- **B4: transporting a level isotopy along the level flow.**  `e` is a level isotopy at `u`; the
flow `Φ` obeys the unit-speed level law on the value interval `Icc lo hi`, which contains `u` and `b`.
Then `(s, y) ↦ e s (Φ (u - b, y))` is a level isotopy at `b` (the transport of the pictures from the
level `u` to the level `b`). -/
theorem isLevelIsotopy_transport {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {b u : ℝ} {e : ℝ → M → EuclideanSpace ℝ (Fin 3)}
    (he : Work.Drive.N2C.IsLevelIsotopy f u e)
    {Φ : ℝ × M → M} {lo hi : ℝ} (hlohi : lo < hi)
    (hΦsm : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦf : ∀ (x : M) (t : ℝ), f x ∈ Set.Icc lo hi → f x + t ∈ Set.Icc lo hi →
      f (Φ (t, x)) = f x + t)
    (hΦcomp : ∀ (x : M) (s t : ℝ), f x ∈ Set.Icc lo hi → f x + t ∈ Set.Icc lo hi →
      f x + t + s ∈ Set.Icc lo hi → Φ (s, Φ (t, x)) = Φ (s + t, x))
    (hu : u ∈ Set.Ioo lo hi) (hb : b ∈ Set.Ioo lo hi) :
    Work.Drive.N2C.IsLevelIsotopy f b (fun s y => e s (Φ (u - b, y))) := by
  refine ⟨?_, ?_, ?_⟩
  · -- the uncurried family is smooth at the level points
    intro s y hy
    have hzy : f (Φ (u - b, y)) = u :=
      f_frozen_of_level (f := f) hb hu hΦf hy
    have h1 : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (𝓡 2)) ((𝓘(ℝ, ℝ)).prod (𝓡 2))
        ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × M => (p.1, Φ (u - b, p.2))) (s, y) :=
      ContMDiffAt.prodMk contMDiff_fst.contMDiffAt
        ((hΦsm.contMDiffAt (x := (u - b, y))).comp (s, y)
          (ContMDiffAt.prodMk (contMDiffAt_const (c := u - b)) contMDiff_snd.contMDiffAt))
    have h2 := (he.1 s (Φ (u - b, y)) hzy).comp (s, y) h1
    simpa only [Function.comp_def] using h2
  · -- injectivity on the level `b`
    intro s x y hx hy hxy
    have hxf : f (Φ (u - b, x)) = u := f_frozen_of_level (f := f) hb hu hΦf hx
    have hyf : f (Φ (u - b, y)) = u := f_frozen_of_level (f := f) hb hu hΦf hy
    have heq : Φ (u - b, x) = Φ (u - b, y) := he.2.1 s _ _ hxf hyf hxy
    calc x = Φ (b - u, Φ (u - b, x)) := (frozen_eq_of_level (f := f) hb hu hΦ0 hΦcomp hx).symm
      _ = Φ (b - u, Φ (u - b, y)) := by rw [heq]
      _ = y := frozen_eq_of_level (f := f) hb hu hΦ0 hΦcomp hy
  · -- the immersion row
    intro s y hy v hvf hvh
    have hzy : f (Φ (u - b, y)) = u := f_frozen_of_level (f := f) hb hu hΦf hy
    have hdiffc : MDifferentiableAt (𝓡 2) (𝓡 2) (fun z : M => Φ (u - b, z)) y :=
      ((hΦsm.comp ((contMDiff_const (c := u - b)).prodMk contMDiff_id))).mdifferentiableAt
        (by simp)
    have hdiffd : MDifferentiableAt (𝓡 2) (𝓡 2) (fun z : M => Φ (b - u, z))
        (Φ (u - b, y)) :=
      ((hΦsm.comp ((contMDiff_const (c := b - u)).prodMk contMDiff_id))).mdifferentiableAt
        (by simp)
    set w : TangentSpace (𝓡 2) (Φ (u - b, y)) :=
      mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (u - b, z)) y v with hw
    -- the composite of the two frozen transports is the identity near `y`, hence so is its tangent map
    have hid_ev : ((fun z : M => Φ (b - u, z)) ∘ (fun z : M => Φ (u - b, z))) =ᶠ[𝓝 y] id := by
      simpa only [Function.comp_def] using
        eventually_frozen_comp_inv (f := f) (Φ := Φ) (lo := lo) (hi := hi) hf.continuous hb hu
          hΦ0 hΦcomp hy
    have hid_mfderiv : mfderiv (𝓡 2) (𝓡 2)
        ((fun z : M => Φ (b - u, z)) ∘ (fun z : M => Φ (u - b, z))) y
        = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 2) y) := by
      rw [Filter.EventuallyEq.mfderiv_eq_v433 (I := 𝓡 2) (I' := 𝓡 2) hid_ev, mfderiv_id]
    have hv_eq : v = mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - u, z)) (Φ (u - b, y)) w := by
      have h1 : mfderiv (𝓡 2) (𝓡 2)
          ((fun z : M => Φ (b - u, z)) ∘ (fun z : M => Φ (u - b, z))) y v = v := by
        rw [hid_mfderiv]
        rfl
      have h2 := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 2)
        (f := fun z : M => Φ (u - b, z)) (g := fun z : M => Φ (b - u, z)) (x := y)
        hdiffd hdiffc v
      exact h1.symm.trans h2
    -- the level function is preserved by the frozen transport on a neighbourhood
    have hlaw_mfderiv : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => f (Φ (u - b, z))) y
        = mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f y := by
      have hev : (fun z : M => f (Φ (u - b, z))) =ᶠ[𝓝 y] (fun z : M => f z + (u - b)) :=
        eventually_frozen_value (f := f) (Φ := Φ) (lo := lo) (hi := hi) hf.continuous hb hu hΦf hy
      rw [Filter.EventuallyEq.mfderiv_eq_v433 (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) hev]
      rw [show (fun z : M => f z + (u - b)) = f + (fun _ : M => (u - b)) from rfl]
      rw [mfderiv_add (hf.mdifferentiableAt (by simp)) (mdifferentiableAt_const)]
      rw [mfderiv_const, add_zero]
    have hfz_w : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (Φ (u - b, y)) w = 0 := by
      have h3 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun z : M => f (Φ (u - b, z))) y v = 0 := by
        rw [hlaw_mfderiv]; exact hvf
      have h2 := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓘(ℝ, ℝ))
        (f := fun z : M => Φ (u - b, z)) (g := f) (x := y)
        (hf.mdifferentiableAt (by simp)) hdiffc v
      rw [← h2]
      exact h3
    have hes : ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) (e s) (Φ (u - b, y)) :=
      (he.1 s (Φ (u - b, y)) hzy).comp (Φ (u - b, y))
        (contMDiffAt_const.prodMk contMDiffAt_id)
    have hEz_w : mfderiv (𝓡 2) (𝓡 3) (e s) (Φ (u - b, y)) w = 0 := by
      have h2 := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 3)
        (f := fun z : M => Φ (u - b, z)) (g := e s) (x := y)
        (hes.mdifferentiableAt (by simp)) hdiffc v
      rw [← h2]
      exact hvh
    have hw0 : w = 0 := he.2.2 s (Φ (u - b, y)) hzy w hfz_w hEz_w
    calc v = mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - u, z)) (Φ (u - b, y)) w := hv_eq
      _ = 0 := by rw [hw0, map_zero]

end Work.Drive.N2C
