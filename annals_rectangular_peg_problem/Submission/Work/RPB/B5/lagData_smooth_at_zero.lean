import Mathlib
import Submission.Work.RPB.B5.lagData_nearZero
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.chordPS_contDiff

/-!
# B5: smoothness of the assembled family at the junction `x = 0`

The assembled family `ℓ τ (x,t) = lagPt W Γc Ac rho τ x t` is

* `W τ t (rho τ x t)` for `x ≤ 0`, and
* `tau π (W τ (t-π) (rho τ (-x) (t-π)))` for `x ≥ 0`.

At the middle chord `x = 0` the two branches do not merely meet to first order: by the
`hrhonearδ` hypothesis of `LagData` the reparametrisation `rho` is the explicit quadratic
`π²/4 (1 + x/√2)²` on a *two-sided* window of `x = 0`, so that on the whole window
`|x| < δ` the assembled point is the single smooth expression

`ℓ τ (x,t) = chordSurf CI.c a τ t (π/2 + π x/(2√2))`

(`Work.RPB.B5.lagData_nearZero`).  Since `x ↦ π/2 + π x/(2√2)` is smooth and the chord surface
is `C⁸` in its arguments on `r ∈ (0,π)`, the assembled family is `C⁸` at `x = 0` in the `τ`-slab
`[0,1]` — which is exactly the assertion of `lagData_smooth_at_zero`.

## Layout

* `chordSurf_triple_contDiffOn_mid` : the chord surface `(τ,t,r) ↦ chordSurf CI.c a τ t r` is
  `C⁸` on `Icc 0 1 ×ˢ univ ×ˢ Ioo 0 π` (a local copy of the smoothing argument of
  `chordSurf_sqrt_contDiffOn`, whose version is `private`).
* `mid_r_mem` : the "middle chord" radius `π/2 + π x/(2√2)` lands in `(0,π)` for `|x| < 1`.
* `lagData_smooth_at_zero` : the junction statement.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-- The chord surface `(τ,t,r) ↦ chordSurf CI.c a τ t r` is `C⁸` on the annulus
`0 ≤ τ ≤ 1`, `t ∈ ℝ`, `0 < r < π`.

This is a local copy of the (private) lemma used in
`Submission/Work/RPB/B5/chordSurf_sqrt_contDiffOn.lean`: it is the composite of `chordPS`
(`C^∞` on `ℂ × ℂ × ℝ`) with the map `(τ,t,r) ↦ (c τ (t+r), c τ (t-r), a τ t r)`, whose third
component is smooth on the strip of `IsChordPhase`. -/
theorem chordSurf_triple_contDiffOn_mid (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) :
    ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => Work.RPB.chordSurf CI.c a z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (0 : ℝ) Real.pi) := by
  have hplus : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => CI.c z.1 (z.2.1 + z.2.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (0 : ℝ) Real.pi) := by
    have h : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => CI.c z.1 (z.2.1 + z.2.2)) :=
      (CI.smooth.of_le (by norm_num)).comp
        (by fun_prop : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => (z.1, z.2.1 + z.2.2)))
    exact h.contDiffOn.mono (Set.subset_univ _)
  have hminus : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => CI.c z.1 (z.2.1 - z.2.2))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (0 : ℝ) Real.pi) := by
    have h : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => CI.c z.1 (z.2.1 - z.2.2)) :=
      (CI.smooth.of_le (by norm_num)).comp
        (by fun_prop : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => (z.1, z.2.1 - z.2.2)))
    exact h.contDiffOn.mono (Set.subset_univ _)
  have ha' : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => a z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (0 : ℝ) Real.pi) :=
    (ha.1.of_le (by norm_num)).mono
      (fun z hz => ⟨hz.1, trivial, ⟨le_of_lt hz.2.2.1, le_of_lt hz.2.2.2⟩⟩)
  have hphi : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) =>
      (CI.c z.1 (z.2.1 + z.2.2), (CI.c z.1 (z.2.1 - z.2.2), a z.1 z.2.1 z.2.2)))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (0 : ℝ) Real.pi) :=
    hplus.prodMk (hminus.prodMk ha')
  exact (chordPS_contDiff 8).contDiffOn.comp hphi (fun z _ => Set.mem_univ _)

/-- The "middle chord" radius `π/2 + π x/(2√2)` lies in `(0,π)` for `|x| < 1`. -/
theorem mid_r_mem (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    Real.pi / 2 + Real.pi * x / (2 * Real.sqrt 2) ∈ Set.Ioo (0 : ℝ) Real.pi := by
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
  have hsqrt2 : (1 : ℝ) < Real.sqrt 2 := Real.one_lt_sqrt_two
  have hrw : Real.pi / 2 + Real.pi * x / (2 * Real.sqrt 2)
      = Real.pi / 2 * (1 + x / Real.sqrt 2) := by
    field_simp
  rw [hrw]
  have hxabs : |x| < 1 := abs_lt.mpr ⟨hx.1, hx.2⟩
  have hu : |x / Real.sqrt 2| < 1 := by
    rw [abs_div, abs_of_pos hs2, div_lt_one hs2]
    linarith
  have h1 : -1 < x / Real.sqrt 2 := (abs_lt.mp hu).1
  have h2 : x / Real.sqrt 2 < 1 := (abs_lt.mp hu).2
  refine ⟨?_, ?_⟩
  · exact mul_pos (by positivity) (by linarith)
  · have hlt : Real.pi / 2 * (1 + x / Real.sqrt 2) < Real.pi / 2 * 2 :=
      mul_lt_mul_of_pos_left (by linarith) (by positivity)
    linarith [hlt]

theorem lagData_smooth_at_zero (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a)
    (τ₀ : ℝ) (hτ₀ : τ₀ ∈ Set.Icc (0 : ℝ) 1) (t₀ : ℝ) :
    ContDiffWithinAt ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) (τ₀, (0, t₀)) := by
  -- the "middle chord" expression that `lagPt` reduces to near `x = 0`
  set G : ℝ × (ℝ × ℝ) → Work.RPV.PS :=
    fun z => Work.RPB.chordSurf CI.c a z.1 z.2.2
      (Real.pi / 2 + Real.pi * z.2.1 / (2 * Real.sqrt 2)) with hGdef
  set F : ℝ × (ℝ × ℝ) → Work.RPV.PS :=
    fun z => Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho z.1 z.2.1 z.2.2 with hFdef
  set s : Set (ℝ × (ℝ × ℝ)) := Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ with hsdef
  set s₂ : Set (ℝ × (ℝ × ℝ)) := Set.Icc (0 : ℝ) 1 ×ˢ (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.univ)
    with hs2def
  set x₀ : ℝ × (ℝ × ℝ) := (τ₀, (0, t₀)) with hx0def
  have hx₀_mem_s₂ : x₀ ∈ s₂ := ⟨hτ₀, by norm_num, trivial⟩
  -- ## Step 1: `G` is `C⁸` on the smaller box `s₂` (where the radius stays in `(0,π)`)
  have hG₂ : ContDiffOn ℝ 8 G s₂ := by
    have htriple := chordSurf_triple_contDiffOn_mid CI a ha
    have hφ : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) =>
        ((z.1, (z.2.2, Real.pi / 2 + Real.pi * z.2.1 / (2 * Real.sqrt 2))) : ℝ × (ℝ × ℝ)))
        s₂ :=
      (by fun_prop : ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) =>
        ((z.1, (z.2.2, Real.pi / 2 + Real.pi * z.2.1 / (2 * Real.sqrt 2))) :
          ℝ × (ℝ × ℝ)))).contDiffOn
    have hmaps : Set.MapsTo (fun z : ℝ × (ℝ × ℝ) =>
        ((z.1, (z.2.2, Real.pi / 2 + Real.pi * z.2.1 / (2 * Real.sqrt 2))) : ℝ × (ℝ × ℝ)))
        s₂ (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ioo (0 : ℝ) Real.pi) := by
      intro z hz
      exact ⟨hz.1, trivial, mid_r_mem z.2.1 hz.2.1⟩
    have hcomp := htriple.comp hφ hmaps
    rw [hGdef]
    exact hcomp
  -- ## Step 2: replace `s₂` by `s` (they agree on a genuine neighbourhood of `x₀`)
  have hst : s ∩ (Set.univ ×ˢ (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.univ)) = s₂ := by
    simp only [hsdef, hs2def, Set.prod_inter_prod, Set.univ_inter, Set.inter_univ]
  have ht : (Set.univ ×ˢ (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.univ) : Set (ℝ × (ℝ × ℝ)))
      ∈ 𝓝 x₀ := by
    have hopen : IsOpen (Set.univ ×ˢ (Set.Ioo (-1 : ℝ) 1 ×ˢ Set.univ) :
        Set (ℝ × (ℝ × ℝ))) :=
      isOpen_univ.prod (isOpen_Ioo.prod isOpen_univ)
    exact hopen.mem_nhds ⟨trivial, by norm_num, trivial⟩
  have hG : ContDiffWithinAt ℝ 8 G s x₀ := by
    refine (contDiffWithinAt_inter ht).mp ?_
    rw [hst]
    exact hG₂.contDiffWithinAt hx₀_mem_s₂
  -- ## Step 3: `F = G` near `x₀` inside `s`, and both agree at `x₀`
  obtain ⟨δ, hδpos, _hδ1, hnear⟩ := lagData_nearZero CI a ha D
  have hF_eq_G : F =ᶠ[𝓝[s] x₀] G := by
    have hx₀_abs : |x₀.2.1| < δ := by rw [hx0def]; simpa using hδpos
    have hmem : {z : ℝ × (ℝ × ℝ) | |z.2.1| < δ} ∈ 𝓝[s] x₀ :=
      mem_nhdsWithin_of_mem_nhds
        ((isOpen_lt (continuous_abs.comp (continuous_fst.comp continuous_snd))
          continuous_const).mem_nhds hx₀_abs)
    filter_upwards [hmem, self_mem_nhdsWithin] with z hzδ hzs
    have hτ : z.1 ∈ Set.Icc (0 : ℝ) 1 := hzs.1
    rw [hFdef, hGdef]
    exact hnear z.1 hτ z.2.2 z.2.1 hzδ
  have hx₀_eq : F x₀ = G x₀ := by
    rw [hFdef, hGdef, hx0def]
    have h0 : |(0 : ℝ)| < δ := by simpa using hδpos
    simpa using hnear τ₀ hτ₀ t₀ 0 h0
  exact hG.congr_of_eventuallyEq hF_eq_G hx₀_eq

end Work.RPB.B5

end
