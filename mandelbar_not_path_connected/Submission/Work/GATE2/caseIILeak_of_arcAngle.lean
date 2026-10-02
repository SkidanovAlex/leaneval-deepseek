import Mathlib
import Submission.Work.GATE2.CaseII
import Submission.Work.GATE2.EXL.deviation_rayPt
import Submission.Work.GATE2.EXL.deviation_shift_eq
import Submission.Work.GATE2.EXL.deviation_shift_window
import Submission.Work.GATE2.EXL.deviation_anti_eq
import Submission.Work.GATE2.EXL.arc_front_data
import Submission.Work.GATE2.EXL.deviation_arc_back
import Submission.Work.GATE2.EXL.deviation_arc_iota
import Submission.Work.GATE2.EXL.log_tau_sub_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Work.GATE2

open LeanEval.ComplexAnalysis (Mandelbar Tantibar)

/-- **The potential of the front leg of an equipotential arc.**  If the `Ψ`-image of the arc `A`
is the ray point of level `exp p > 1`, then the Green function of its image is exactly `p`. -/
private theorem green_arc_front {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    {θ₀ p : ℝ} (A : C(unitInterval, ℂ))
    (hangle : ∀ r : unitInterval, fl.Ψ (A r) =
      Work.EL.rayPt d.hN (θ₀ + (r : ℝ) * (Work.EL.alpha1 - θ₀)) (Real.exp p))
    (hp : 0 < p) (hK : ∀ r : unitInterval, fl.Ψ (A r) ∉ Work.EL.K c) :
    ∀ r : unitInterval, Work.Bottcher.green c (fl.Ψ (A r)) = p := by
  intro r
  have hexp : (1 : ℝ) < Real.exp p := Real.one_lt_exp_iff.mpr hp
  rw [Work.GATE2.EXL.green_eq_pot d.hN d.bottcher (hK r), hangle r,
    Work.EL.pot_rayPt d.hN hexp, Real.log_exp]

/-- **The potential of the back leg.**  The equivariance `Ψ (w + 1) = F c (Ψ w)` together with
`G (F c z) = 1024 * G z` divides the potential by `1024` under the shift `w ↦ w - 1`. -/
private theorem green_arc_back {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁)
    {p : ℝ} (A : C(unitInterval, ℂ))
    (hsh : ∀ r : unitInterval, fl.Ψ (A r) = Work.EL.F c (fl.Ψ (A r - 1)))
    (hg : ∀ r : unitInterval, Work.Bottcher.green c (fl.Ψ (A r)) = p) :
    ∀ r : unitInterval, Work.Bottcher.green c (fl.Ψ (A r - 1)) = p / 1024 := by
  intro r
  have h := Work.GATE2.EXL.green_F c (fl.Ψ (A r - 1))
  rw [← hsh r] at h
  have h1 : Work.Bottcher.green c (fl.Ψ (A r - 1)) =
      Work.Bottcher.green c (fl.Ψ (A r)) / 1024 := by linarith
  rw [h1, hg r]

/-- **Total invariance of `K c` under the high return map `F c = (T_c)^{10}`.** -/
private theorem mem_K_F_iff (c z : ℂ) :
    Work.EL.F c z ∈ Work.EL.K c ↔ z ∈ Work.EL.K c := by
  rw [Work.EL.F_eq_tantibar]
  exact Work.PARIMPL.mem_K_tantibar_iterate_iff c z 10

/-- If the `F c`-image of `z` lies off `K c`, then so does `z` (total invariance of `K c`). -/
private theorem notMem_K_of_F_image {c : ℂ} {z : ℂ} (hz : Work.EL.F c z ∉ Work.EL.K c) :
    z ∉ Work.EL.K c := fun h => hz ((mem_K_F_iff c z).mpr h)

/-- If `z` lies off `K c`, then so does its image under the square root `g = (T_c)^5`. -/
private theorem notMem_K_image_five {c : ℂ} {z : ℂ} (hz : z ∉ Work.EL.K c) :
    ((Tantibar c)^[5]) z ∉ Work.EL.K c :=
  fun h => hz ((Work.PARIMPL.mem_K_tantibar_iterate_iff c z 5).mp h)

/-- **`CaseIILeak` from an equipotential arc in the angle window of `α₁`.**  The arc `A` of the
repelling coordinate runs from the real deep point `x₀` to the point `γ₁ s₁` of the `α₁`-lift,
stays in `{Re < -3/2}`, and its `Ψ`-image is the *equipotential* arc of level `exp p > 1` spanned
by the angles from `θ₀` to `α₁`, with `α₁ - θ₀ < 1/524288`.

Because the level is constant along `A` (`green_arc_front`), every remaining datum of the
exit-loop constructions is *automatic*:

* the `α₁`-deviation of the front leg is the closed form `θ(r) - α₁` (`arc_front_data`), hence
  smaller than `1/524288` in absolute value; the back leg (`deviation_arc_back`) is `1024` times
  smaller, and the reflected legs (`deviation_arc_iota`) carry the `α₂`-deviation `-32` times that;
* the four legs avoid `K c` because the front leg is a ray point and `K c` is totally invariant
  under `(T_c)^5` and `(T_c)^{10}`;
* the potential floors hold with room `p` versus `p/1024` (and `p/32` for the reflected base). -/
theorem caseIILeak_of_arcAngle {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (Lray : Work.ELRig.RayCylLift d fl)
    {θ₀ p s₁ x₀ : ℝ} (A : C(unitInterval, ℂ))
    (hA0 : A 0 = ((x₀ : ℝ) : ℂ)) (hA1 : A 1 = Lray.γ₁ s₁)
    (hAre : ∀ r : unitInterval, (A r).re < -(3 / 2 : ℝ))
    (hangle : ∀ r : unitInterval, fl.Ψ (A r) =
      Work.EL.rayPt d.hN (θ₀ + (r : ℝ) * (Work.EL.alpha1 - θ₀)) (Real.exp p))
    (hp : 0 < p) (hθ₀ : θ₀ < Work.EL.alpha1)
    (hθ₀' : Work.EL.alpha1 - θ₀ < 1 / (32 * 16384))
    (hτ1 : Lray.τ s₁ = Real.exp p)
    (hsgn : ∀ r : unitInterval, 0 < (r : ℝ) → (A r).im ≠ 0)
    (hγim : ∀ s : ℝ, (Lray.γ₁ s).im ≠ 0)
    (hγre : ∀ u ∈ Set.Icc (0 : ℝ) 1, (Lray.γ₁ (s₁ - 1 + u)).re < -(3 / 2 : ℝ))
    (hzero : ∀ r : unitInterval,
      Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r)) = 0 → r = 1)
    (hbase : Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A 1 - 1)) = 0)
    (hbase1 : Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A 1)) = 0) :
    Work.GATE2.CaseIILeak c fl.Ψ := by
  have hM : c ∈ Mandelbar := Work.FSeed.API.mem_Mandelbar d
  -- ## 1. the front leg: off `K c`, with `α₁`-deviation `< 1/524288`
  obtain ⟨hKA, hdevA⟩ := Work.GATE2.EXL.arc_front_data (d := d) fl A hangle hp hθ₀ hθ₀'
  -- ## 2. the equivariance `Ψ (A r) = F c (Ψ (A r - 1))`
  have hsh : ∀ r : unitInterval, fl.Ψ (A r) = Work.EL.F c (fl.Ψ (A r - 1)) := by
    intro r
    have h := fl.Ψ_shift (A r - 1)
    rwa [sub_add_cancel] at h
  -- ## 3. the four legs avoid `K c` (total invariance of `K c` under `(T_c)^5`, `(T_c)^{10}`)
  have hKA1 : ∀ r : unitInterval, fl.Ψ (A r - 1) ∉ Work.EL.K c := by
    intro r
    have h := hKA r
    rw [hsh r] at h
    exact notMem_K_of_F_image h
  have hKA2 : ∀ r : unitInterval, fl.Ψ (star (A r) + 1 / 2) ∉ Work.EL.K c := by
    intro r
    rw [fl.Ψ_anti (A r)]
    exact notMem_K_image_five (hKA r)
  have hKA3 : ∀ r : unitInterval, fl.Ψ (star (A r - 1) + 1 / 2) ∉ Work.EL.K c := by
    intro r
    rw [fl.Ψ_anti (A r - 1)]
    exact notMem_K_image_five (hKA1 r)
  -- ## 4. the `α₁`-deviations of the two legs (`1/16384` for the loops, `1/524288` sharp)
  have hdevFront : ∀ r : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r))| <
        1 / 16384 := fun r => lt_trans (hdevA r) (by norm_num)
  have hback := Work.GATE2.EXL.deviation_arc_back (d := d) fl A hKA hKA1 hdevFront
    hzero hbase hbase1
  have hdevBack : ∀ r : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r - 1))| <
        1 / 524288 := by
    intro r
    have h1 : Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r - 1)) =
        Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r)) / 1024 := by
      linarith [hback r]
    rw [h1, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 1024)]
    linarith [hdevA r]
  have hdevBack16384 : ∀ r : unitInterval,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha1 (fl.Ψ (A r - 1))| <
        1 / 16384 := fun r => lt_trans (hdevBack r) (by norm_num)
  -- ## 5. the reflected legs carry the `α₂`-deviation `-32` times the `α₁`-deviation
  obtain ⟨hdevι, hdevι1⟩ :=
    Work.GATE2.EXL.deviation_arc_iota (d := d) fl A hKA hKA1 hdevA hdevBack
  -- ## 6. the `γ₂`-leg of the second lift
  have hKγ₂ : ∀ u ∈ Set.Icc (0 : ℝ) 1, fl.Ψ (Lray.γ₂ (s₁ - 1 + u)) ∉ Work.EL.K c := by
    intro u hu
    rw [Lray.hΨ₂ (s₁ - 1 + u)]
    exact Work.EL.rayPt_notMem_K d.hN
      (one_lt_pow₀ (Lray.hτ1 (s₁ - 1 + u)) (by norm_num : (32 : ℕ) ≠ 0))
  have hdevγ₂ : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |Work.GATE.deviation (Work.Bottcher.varphiCrit c) Work.EL.alpha2
        (fl.Ψ (Lray.γ₂ (s₁ - 1 + u)))| < 1 / 16384 := by
    intro u hu
    rw [Work.GATE2.EXL.deviation_varphiCrit_eq_zero_iota d.hN d.bottcher hM
      (Lray.img₂ (s₁ - 1 + u))]
    norm_num
  -- ## 7. the potentials along the arc and along the two fundamental pieces
  have hgreenA : ∀ r : unitInterval, Work.Bottcher.green c (fl.Ψ (A r)) = p :=
    green_arc_front fl A hangle hp hKA
  have hgreenA1 : ∀ r : unitInterval, Work.Bottcher.green c (fl.Ψ (A r - 1)) = p / 1024 :=
    green_arc_back fl A hsh hgreenA
  have hp1024 : (0 : ℝ) < p / 1024 := by positivity
  have hp32 : (0 : ℝ) < p / 32 := by positivity
  -- ## 8. the six potential floors
  have hfloorB : ∀ r : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (A 0 - 1)) <
        Work.Bottcher.green c (fl.Ψ (A r)) := by
    intro r
    rw [hgreenA1 0, hgreenA r]
    linarith [hp1024]
  have hfloorB1 : ∀ r : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (A 0 - 1)) <
        Work.Bottcher.green c (fl.Ψ (A r - 1)) := by
    intro r
    rw [hgreenA1 0, hgreenA1 r]
    linarith [hp1024]
  have hfloorγ₁ : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (A 0 - 1)) <
        Work.Bottcher.green c (fl.Ψ (Lray.γ₁ (s₁ - 1 + u))) := by
    intro u hu
    rw [hgreenA1 0, Work.GATE2.EXL.green_lift Lray (s₁ - 1 + u)]
    have hlog1 : Real.log (Lray.τ (s₁ - 1)) = p / 1024 :=
      Work.GATE2.EXL.log_tau_sub_one Lray hτ1
    have hmono : Lray.τ (s₁ - 1) ≤ Lray.τ (s₁ - 1 + u) :=
      Lray.hτmono.monotone (by linarith [hu.1])
    have hle : Real.log (Lray.τ (s₁ - 1)) ≤ Real.log (Lray.τ (s₁ - 1 + u)) :=
      Real.log_le_log (by linarith [Lray.hτ1 (s₁ - 1)]) hmono
    rw [hlog1] at hle
    linarith [hp1024, hle]
  have hgreenS : ∀ r : unitInterval,
      Work.Bottcher.green c (fl.Ψ (star (A r) + 1 / 2)) = 32 * p := by
    intro r
    rw [fl.Ψ_anti (A r), Work.GATE2.EXL.green_iterate, hgreenA r]
    norm_num
  have hgreenS1 : ∀ r : unitInterval,
      Work.Bottcher.green c (fl.Ψ (star (A r - 1) + 1 / 2)) = p / 32 := by
    intro r
    rw [fl.Ψ_anti (A r - 1), Work.GATE2.EXL.green_iterate, hgreenA1 r]
    ring
  have hfloorS : ∀ r : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (star (A 0 - 1) + 1 / 2)) <
        Work.Bottcher.green c (fl.Ψ (star (A r) + 1 / 2)) := by
    intro r
    rw [hgreenS1 0, hgreenS r]
    linarith [hp32]
  have hfloorS1 : ∀ r : unitInterval,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (star (A 0 - 1) + 1 / 2)) <
        Work.Bottcher.green c (fl.Ψ (star (A r - 1) + 1 / 2)) := by
    intro r
    rw [hgreenS1 0, hgreenS1 r]
    linarith [hp32]
  have hfloorSγ : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      (3 / 4 : ℝ) * Work.Bottcher.green c (fl.Ψ (star (A 0 - 1) + 1 / 2)) <
        Work.Bottcher.green c (fl.Ψ (Lray.γ₂ (s₁ - 1 + u))) := by
    intro u hu
    rw [hgreenS1 0, Work.GATE2.EXL.green_lift_iota Lray (s₁ - 1 + u)]
    have hlog1 : Real.log (Lray.τ (s₁ - 1)) = p / 1024 :=
      Work.GATE2.EXL.log_tau_sub_one Lray hτ1
    have hmono : Lray.τ (s₁ - 1) ≤ Lray.τ (s₁ - 1 + u) :=
      Lray.hτmono.monotone (by linarith [hu.1])
    have hle : Real.log (Lray.τ (s₁ - 1)) ≤ Real.log (Lray.τ (s₁ - 1 + u)) :=
      Real.log_le_log (by linarith [Lray.hτ1 (s₁ - 1)]) hmono
    rw [hlog1] at hle
    linarith [hp1024, hle]
  -- ## 9. the two exit-loop families
  obtain ⟨r₁, v₁, hr₁, hE₁⟩ := Work.GATE2.EXL.exitLoop_of_arcSegment (d := d) fl Lray A
    hA0 hA1 hAre hγre hsgn hγim hKA hKA1 hdevFront hdevBack16384 hfloorB hfloorB1 hfloorγ₁
  obtain ⟨r₂, v₂, hr₂, hE₂⟩ := Work.GATE2.EXL.exitLoop_iota_of_arcSegment (d := d) fl Lray A
    hA0 hA1 hAre hγre hsgn hγim hKA2 hKA3 hKγ₂ hdevι hdevι1 hdevγ₂ hfloorS hfloorS1 hfloorSγ
  -- ## 10. the deep real leak point at `x₀`
  have hleak : fl.Ψ ((x₀ : ℝ) : ℂ) ∉ Work.EL.K c := by
    rw [← hA0]
    exact hKA 0
  have hxdeep : x₀ < -(3 / 2 : ℝ) := by
    have h := hAre 0
    rw [hA0] at h
    simpa using h
  exact ⟨x₀, Work.GATE2.deepLeak_of_leak (fl := fl) hxdeep hleak,
    ⟨r₁, hr₁, fun r₀ hr v =>
      ⟨Work.GATE2.EXL.ExitLoop.mono_r₀ (Work.GATE2.EXL.ExitLoop.congr_v hE₁.some v) hr.2⟩⟩,
    ⟨r₂, hr₂, fun r₀ hr v =>
      ⟨Work.GATE2.EXL.ExitLoop.mono_r₀ (Work.GATE2.EXL.ExitLoop.congr_v hE₂.some v) hr.2⟩⟩⟩

end Work.GATE2
