import Mathlib
import Submission.Work.Drive.N2C.isotopyCalc
import Submission.Work.Compat.MFDerivCongrV433

/-!
# B5: the window movie of the coherent-window design

`Work.Drive.N2C.IsLevelIsotopy f b e` (see `Submission/Work/Drive/N2C/defs.lean`) says that
`e : ℝ → M → ℝ³` is a jointly smooth family of *pictures* of the regular level `f ⁻¹' {b}`:
jointly smooth at `(s, y)` for `f y = b`, injective there, and `(df, d(e s))`-immersive there.

This file proves the **handover identity** of the coherent-window architecture
(`Submission/Work/Drive/N2Lead/NOTES_LEAD_coherentWindows.md` §3.4): if

* `W` is a good drawing of the value band `Ioo a' b'` (`GoodDrawingOn f (Ioo a' b') W`),
* `Φ` is a level flow lawful on `Icc lo hi` (`f (Φ (t, x)) = f x + t` and the composition law),
* `b ∈ Ioo lo hi` is the reference level, and
* `ρ` is a smooth time map with `ρ s ∈ Icc α β ⊆ Ioo lo hi ∩ Ioo a' b'`,

then the *movie* `(s, y) ↦ W (Φ (ρ s - b, y))` is a level isotopy at `b`.

The mathematical content is that each slice is `W` read through the time-`(ρ s - b)` flow map,
which carries the level `f = b` to the level `f = ρ s` *inside the band on which `W` is good*;
the flow map is a diffeomorphism (its inverse is the time-`(b - ρ s)` flow map, by the composition
law) and it translates the value function by `ρ s - b`, so all three rows are pure chain rule plus
the corresponding row of `GoodDrawingOn f (Ioo a' b') W`.
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set Filter

set_option maxHeartbeats 1000000

/-- **B5 (the window movie).**  A good drawing of the band `Ioo a' b'`, read through the level flow
`Φ` at the time `ρ s - b`, is a level isotopy at `b`. -/
theorem isLevelIsotopy_windowMovie {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {b : ℝ} {W : M → EuclideanSpace ℝ (Fin 3)}
    {Φ : ℝ × M → M} {lo hi a' b' : ℝ} (hlohi : lo < hi)
    (hΦsm : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦf : ∀ (x : M) (t : ℝ), f x ∈ Set.Icc lo hi → f x + t ∈ Set.Icc lo hi →
      f (Φ (t, x)) = f x + t)
    (hΦcomp : ∀ (x : M) (s t : ℝ), f x ∈ Set.Icc lo hi → f x + t ∈ Set.Icc lo hi →
      f x + t + s ∈ Set.Icc lo hi → Φ (s, Φ (t, x)) = Φ (s + t, x))
    (hb : b ∈ Set.Ioo lo hi)
    {α β : ℝ} (hαβlo : Set.Icc α β ⊆ Set.Ioo lo hi) (hαβ' : Set.Icc α β ⊆ Set.Ioo a' b')
    (hW : Work.Drive.N2.GoodDrawingOn f (Set.Ioo a' b') W)
    {ρ : ℝ → ℝ} (hρ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ρ)
    (hρmem : ∀ s : ℝ, ρ s ∈ Set.Icc α β) :
    Work.Drive.N2C.IsLevelIsotopy f b (fun s y => W (Φ (ρ s - b, y))) := by
  have hbIcc : b ∈ Set.Icc lo hi := ⟨le_of_lt hb.1, le_of_lt hb.2⟩
  have hρlo : ∀ s, ρ s ∈ Set.Ioo lo hi := fun s => hαβlo (hρmem s)
  have hρdraw : ∀ s, ρ s ∈ Set.Ioo a' b' := fun s => hαβ' (hρmem s)
  -- the value of the transported point
  have hval : ∀ (s : ℝ) (y : M), f y = b → f (Φ (ρ s - b, y)) = ρ s := by
    intro s y hy
    have h1 : f y ∈ Set.Icc lo hi := by rw [hy]; exact hbIcc
    have h2 : f y + (ρ s - b) ∈ Set.Icc lo hi := by
      rw [hy, show b + (ρ s - b) = ρ s by ring]
      exact ⟨le_of_lt (hρlo s).1, le_of_lt (hρlo s).2⟩
    have h := hΦf y (ρ s - b) h1 h2
    rw [hy] at h
    rwa [show b + (ρ s - b) = ρ s by ring] at h
  -- the inverse of the time-`(ρ s - b)` flow map on the level
  have hinvpoint : ∀ (s : ℝ) (y : M), f y = b → Φ (b - ρ s, Φ (ρ s - b, y)) = y := by
    intro s y hy
    have h1 : f y ∈ Set.Icc lo hi := by rw [hy]; exact hbIcc
    have h2 : f y + (ρ s - b) ∈ Set.Icc lo hi := by
      rw [hy, show b + (ρ s - b) = ρ s by ring]
      exact ⟨le_of_lt (hρlo s).1, le_of_lt (hρlo s).2⟩
    have h3 : f y + (ρ s - b) + (b - ρ s) ∈ Set.Icc lo hi := by
      rw [show f y + (ρ s - b) + (b - ρ s) = b by rw [hy]; ring]
      exact hbIcc
    have h := hΦcomp y (b - ρ s) (ρ s - b) h1 h2 h3
    rw [show (b - ρ s) + (ρ s - b) = 0 by ring, hΦ0 y] at h
    exact h
  refine ⟨?_, ?_, ?_⟩
  · -- joint smoothness: the flow map `p ↦ Φ (ρ p.1 - b, p.2)` is smooth, and `W` is smooth at the
    -- transported point because its value lies in the good band.
    intro s y hy
    have hWsm : ContMDiffAt (𝓡 2) (𝓡 3) ∞ W (Φ (ρ s - b, y)) :=
      hW.1 _ (by rw [hval s y hy]; exact hρdraw s)
    have hpair : ContMDiff ((𝓘(ℝ,ℝ)).prod (𝓡 2)) ((𝓘(ℝ,ℝ)).prod (𝓡 2)) ∞
        (fun p : ℝ × M => (ρ p.1 - b, p.2)) :=
      (((contDiff_id.sub contDiff_const).comp_contMDiff
        (hρ.contMDiff.comp contMDiff_fst)).prodMk contMDiff_snd)
    have hFsm : ContMDiffAt ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (𝓡 2) ∞
        (fun p : ℝ × M => Φ (ρ p.1 - b, p.2)) (s, y) :=
      (hΦsm.comp hpair).contMDiffAt
    have hmain := hWsm.comp (s, y) hFsm
    simpa only [Function.comp_def] using hmain
  · -- injectivity on the level: `W` separates the two transported points, and the flow map is
    -- injective on the level because it has the inverse `Φ (b - ρ s, ·)`.
    intro s x y hx hy hxy
    have hEq : Φ (ρ s - b, x) = Φ (ρ s - b, y) :=
      hW.2.2 _ _ (by rw [hval s x hx]; exact hρdraw s)
        (by rw [hval s y hy]; exact hρdraw s) (by rw [hval s x hx, hval s y hy]) hxy
    calc x = Φ (b - ρ s, Φ (ρ s - b, x)) := (hinvpoint s x hx).symm
      _ = Φ (b - ρ s, Φ (ρ s - b, y)) := by rw [hEq]
      _ = y := hinvpoint s y hy
  · -- immersion on `ker df`: `Φ (c, ·)` with `c = ρ s - b` is a local diffeomorphism which
    -- translates the value function by `c`; the derivative of `W` kills the image direction, so
    -- that direction is zero, and the inverse flow map returns `v = 0`.
    intro s y hy v hv hdv
    set c : ℝ := ρ s - b with hcdef
    have hvalc : f (Φ (c, y)) = ρ s := by rw [hcdef]; exact hval s y hy
    have hcydraw : f (Φ (c, y)) ∈ Set.Ioo a' b' := by rw [hvalc]; exact hρdraw s
    have hdv' : mfderiv (𝓡 2) (𝓡 3) (fun z : M => W (Φ (c, z))) y v = 0 := by
      rw [hcdef]; exact hdv
    have h1ev : ∀ᶠ z in 𝓝 y, f z ∈ Set.Ioo lo hi :=
      (hf.continuous.isOpen_preimage _ isOpen_Ioo).mem_nhds
        (by show f y ∈ Set.Ioo lo hi; rw [hy]; exact hb)
    have h2ev : ∀ᶠ z in 𝓝 y, f z + (ρ s - b) ∈ Set.Ioo lo hi := by
      have hcont : Continuous (fun z : M => f z + (ρ s - b)) := hf.continuous.add continuous_const
      have hthis : f y + (ρ s - b) = ρ s := by rw [hy]; ring
      refine (hcont.isOpen_preimage _ isOpen_Ioo).mem_nhds ?_
      show f y + (ρ s - b) ∈ Set.Ioo lo hi
      rw [hthis]; exact hρlo s
    have hΨsm : ContMDiff (𝓡 2) (𝓡 2) ∞ (fun z : M => Φ (c, z)) := by
      rw [hcdef]
      exact hΦsm.comp (contMDiff_const.prodMk contMDiff_id)
    set w : TangentSpace (𝓡 2) (Φ (c, y)) :=
      mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (c, z)) y v with hwdef
    -- the flow map translates the value function, hence `df` of the image direction is zero
    have hflow_ev : (fun z : M => f (Φ (c, z))) =ᶠ[𝓝 y] (fun z : M => f z + c) := by
      filter_upwards [h1ev, h2ev] with z hz1 hz2
      have hzc : f z + (ρ s - b) = f z + c := by rw [hcdef]
      have hz2' : f z + c ∈ Set.Ioo lo hi := by rwa [hzc] at hz2
      exact hΦf z c ⟨le_of_lt hz1.1, le_of_lt hz1.2⟩ ⟨le_of_lt hz2'.1, le_of_lt hz2'.2⟩
    have hmfslice : mfderiv (𝓡 2) (𝓘(ℝ,ℝ)) (fun z : M => f (Φ (c, z))) y
        = mfderiv (𝓡 2) (𝓘(ℝ,ℝ)) f y := by
      rw [hflow_ev.mfderiv_eq_v433]
      have hfun : (fun z : M => f z + c) = f + fun _ : M => c := rfl
      rw [hfun, mfderiv_add (hf.mdifferentiableAt (by simp)) mdifferentiableAt_const]
      rw [mfderiv_const]
      exact add_zero _
    have hchain1 : mfderiv (𝓡 2) (𝓘(ℝ,ℝ)) (fun z : M => f (Φ (c, z))) y v
        = mfderiv (𝓡 2) (𝓘(ℝ,ℝ)) f (Φ (c, y)) w := by
      have h := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓘(ℝ,ℝ))
        (f := fun z : M => Φ (c, z)) (g := f) (x := y) (hf.mdifferentiableAt (by simp))
        (hΨsm.mdifferentiableAt (by simp)) v
      simpa only [Function.comp_def, hwdef] using h
    have hfv0 : mfderiv (𝓡 2) (𝓘(ℝ,ℝ)) f (Φ (c, y)) w = 0 := by
      rw [← hchain1]
      have h2 : mfderiv (𝓡 2) (𝓘(ℝ,ℝ)) (fun z : M => f (Φ (c, z))) y v
          = mfderiv (𝓡 2) (𝓘(ℝ,ℝ)) f y v := congrArg (fun L => L v) hmfslice
      rw [h2]
      exact hv
    -- and the drawing's immersion row kills the image direction
    have hWsmc : ContMDiffAt (𝓡 2) (𝓡 3) ∞ W (Φ (c, y)) := hW.1 _ hcydraw
    have hchain2 : mfderiv (𝓡 2) (𝓡 3) (fun z : M => W (Φ (c, z))) y v
        = mfderiv (𝓡 2) (𝓡 3) W (Φ (c, y)) w := by
      have h := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 3)
        (f := fun z : M => Φ (c, z)) (g := W) (x := y) (hWsmc.mdifferentiableAt (by simp))
        (hΨsm.mdifferentiableAt (by simp)) v
      simpa only [Function.comp_def, hwdef] using h
    have hWv0 : mfderiv (𝓡 2) (𝓡 3) W (Φ (c, y)) w = 0 := by
      rw [← hchain2]; exact hdv'
    have hw0 : w = 0 := hW.2.1 (Φ (c, y)) hcydraw w hfv0 hWv0
    -- the composite of the two flow maps is the identity near `y`, so `v = 0`
    have hflowid_ev : (fun z : M => Φ (b - ρ s, Φ (ρ s - b, z))) =ᶠ[𝓝 y] id := by
      filter_upwards [h1ev, h2ev] with z hz1 hz2
      have hz3 : f z + (ρ s - b) + (b - ρ s) ∈ Set.Icc lo hi := by
        rw [show f z + (ρ s - b) + (b - ρ s) = f z by ring]
        exact ⟨le_of_lt hz1.1, le_of_lt hz1.2⟩
      have h := hΦcomp z (b - ρ s) (ρ s - b) ⟨le_of_lt hz1.1, le_of_lt hz1.2⟩
        ⟨le_of_lt hz2.1, le_of_lt hz2.2⟩ hz3
      rw [show (b - ρ s) + (ρ s - b) = 0 by ring, hΦ0 z] at h
      exact h
    have hid : mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - ρ s, Φ (ρ s - b, z))) y v = v := by
      have hmfid : mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - ρ s, Φ (ρ s - b, z))) y
          = ContinuousLinearMap.id ℝ (TangentSpace (𝓡 2) y) := by
        rw [hflowid_ev.mfderiv_eq_v433, mfderiv_id]
      rw [hmfid]
      rfl
    have hcomp2 : mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - ρ s, Φ (ρ s - b, z))) y v
        = mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - ρ s, z)) (Φ (ρ s - b, y)) w := by
      have hinner : ContMDiff (𝓡 2) (𝓡 2) ∞ (fun z : M => Φ (ρ s - b, z)) := by
        rw [← hcdef]
        exact hΨsm
      have houter : ContMDiff (𝓡 2) (𝓡 2) ∞ (fun z : M => Φ (b - ρ s, z)) :=
        hΦsm.comp (contMDiff_const.prodMk contMDiff_id)
      have h := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 2)
        (f := fun z : M => Φ (ρ s - b, z)) (g := fun z : M => Φ (b - ρ s, z)) (x := y)
        (houter.mdifferentiableAt (by simp)) (hinner.mdifferentiableAt (by simp)) v
      simpa only [Function.comp_def, hwdef, hcdef] using h
    have hfin : v = mfderiv (𝓡 2) (𝓡 2) (fun z : M => Φ (b - ρ s, Φ (ρ s - b, z))) y v :=
      hid.symm
    rw [hfin, hcomp2, hw0, map_zero]
    rfl

end Work.Drive.N2C
