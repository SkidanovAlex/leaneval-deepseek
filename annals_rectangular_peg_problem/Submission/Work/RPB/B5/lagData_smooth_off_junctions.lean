import Mathlib
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B5.collarPt_contDiffWithinAt
import Submission.Work.RPB.B5.chartSlice_contDiffWithinAt

/-!
# B5: the assembled family `ℓ` is `C⁸` away from the three junctions

`ℓ τ (x,t) = lagPt W Γc Ac rho τ x t` is the piecewise function

* `x ≤ -√2`: the collar point `collarPt Γc Ac τ (sig x) t` (`sig x = x²/2 - 1 > 0`);
* `-√2 ≤ x ≤ 0`: the chord chart `W τ t (rho τ x t)`;
* `x > 0`: the `τ_π`-image of the reflected point, `tau π (basePt τ (-x) (t - π))`.

This file proves that `ℓ` is `C⁸` on the slab `Icc 0 1 × univ × univ` at every point whose
`x`-coordinate avoids the three junctions `-√2`, `0`, `√2`.  The three junctions are *not*
covered here (they are the subject of `lagData_junction_zero`, `lagData_junction_negSqrt2` and
their `τ_π`-transports, where the two branches only agree to a finite order and the gluing
lemmas are needed); away from them, however, `ℓ` agrees in a neighbourhood of the point with a
*single* smooth branch, so the statement is a local computation.

The two ingredients are the sibling lemmas

* `Work.RPB.B5.collarPt_contDiffWithinAt` — the collar branch is `C⁸`; this is where the
  `t`-periodicity of `(Γc, Ac)` is used (`LagData` only provides `C⁸` for `t ≥ 0`, while the
  statement is about *all* `t`; the collar branch is `Tk 1`-quasi-periodic in `t`, so shifting
  `t` into the half-space `t > 0` transfers the smoothness);
* `Work.RPB.B5.chartSlice_contDiffWithinAt` — the chart branch
  `z ↦ W z.1 z.2.2 (rho z.1 z.2.1 z.2.2)` is `C⁸`, using that `W` is smooth on the box
  `Icc 0 1 × univ × Ioo (-ρ₀) ρ₀` and that `rho` stays in the box near a point where it is
  interior.

Both the chart-branch and the collar-branch statement are on the slab `Icc 0 1 × univ × univ`,
so the `τ ∈ Icc 0 1` restriction of the target is exactly the one the data provides.  The
hypothesis `ha` is not used: no chord-phase input is needed for smoothness off the junctions.
-/

open RectangularPegProblem Manifold Complex Real
open scoped ContDiff Topology

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

theorem lagData_smooth_off_junctions (CI : Work.RPV.CurveIsotopy) (a : ℝ → ℝ → ℝ → ℝ)
    (ha : Work.RPB.IsChordPhase CI.c a) (D : Work.RPB.B5.LagData CI a)
    (τ₀ : ℝ) (hτ₀ : τ₀ ∈ Set.Icc (0 : ℝ) 1) (x₀ : ℝ)
    (hx : x₀ ≠ -Real.sqrt 2 ∧ x₀ ≠ 0 ∧ x₀ ≠ Real.sqrt 2) (t₀ : ℝ) :
    ContDiffWithinAt ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => Work.RPB.B5.lagPt D.W D.Γc D.Ac D.rho z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) (τ₀, (x₀, t₀)) := by
  set S : Set (ℝ × (ℝ × ℝ)) := Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ with hSdef
  have hpS : (τ₀, (x₀, t₀)) ∈ S := by rw [hSdef]; exact ⟨hτ₀, trivial, trivial⟩
  -- any neighbourhood of `x₀` in ℝ pulls back to a neighbourhood of the point within `S`
  have hpre : ∀ (P : ℝ → Prop), {x : ℝ | P x} ∈ 𝓝 x₀ →
      {z : ℝ × (ℝ × ℝ) | P z.2.1} ∈ 𝓝[S] (τ₀, (x₀, t₀)) := by
    intro P hP
    exact nhdsWithin_le_nhds ((continuous_snd.fst.continuousAt).preimage_mem_nhds hP)
  -- the collar branch, at an arbitrary level
  have hcollar : ∀ (σ₀ t' : ℝ), ContDiffWithinAt ℝ 8
      (fun u : ℝ × (ℝ × ℝ) => collarPt D.Γc D.Ac u.1 u.2.1 u.2.2) S (τ₀, (σ₀, t')) := by
    intro σ₀ t'
    have h := collarPt_contDiffWithinAt D.Γc D.Ac D.hΓsm D.hAsm D.hΓper D.hAper
      (τ₀ := τ₀) (σ₀ := σ₀) (t₀ := t') hτ₀
    rw [hSdef]
    exact h
  -- the collar branch with `σ = sig x`
  have hcollarX : ContDiffWithinAt ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => collarPt D.Γc D.Ac z.1 (sig z.2.1) z.2.2) S (τ₀, (x₀, t₀)) := by
    have hψ : ContDiffWithinAt ℝ 8 (fun z : ℝ × (ℝ × ℝ) => (z.1, (sig z.2.1, z.2.2)))
        S (τ₀, (x₀, t₀)) :=
      (by unfold sig; fun_prop :
        ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) =>
          (z.1, (Work.RPB.B5.sig z.2.1, z.2.2)))).contDiffWithinAt
    have hmap : Set.MapsTo (fun z : ℝ × (ℝ × ℝ) => (z.1, (sig z.2.1, z.2.2))) S S := by
      intro z hz; exact ⟨hz.1, trivial, trivial⟩
    have h := (hcollar (sig x₀) t₀).comp (τ₀, (x₀, t₀)) hψ hmap
    simpa only [Function.comp_def] using h
  -- ### the four regions
  -- `x < -√2`: the collar branch
  have caseA (hlt : x₀ < -Real.sqrt 2) : ContDiffWithinAt ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => lagPt D.W D.Γc D.Ac D.rho z.1 z.2.1 z.2.2)
      S (τ₀, (x₀, t₀)) := by
    have hev : (fun z : ℝ × (ℝ × ℝ) => lagPt D.W D.Γc D.Ac D.rho z.1 z.2.1 z.2.2)
        =ᶠ[𝓝[S] (τ₀, (x₀, t₀))]
        (fun z : ℝ × (ℝ × ℝ) => collarPt D.Γc D.Ac z.1 (sig z.2.1) z.2.2) := by
      filter_upwards [hpre (fun x => x < -Real.sqrt 2) (isOpen_Iio.mem_nhds hlt)] with z hz
      have hz0 : z.2.1 ≤ 0 := by
        have : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
        linarith
      rw [lagPt, if_pos hz0, basePt, if_pos (le_of_lt hz), collarPt]
    exact hcollarX.congr_of_eventuallyEq hev (hev.eq_of_nhdsWithin hpS)
  -- `-√2 < x < 0`: the chord chart
  have caseB (hgt : -Real.sqrt 2 < x₀) (hneg : x₀ < 0) : ContDiffWithinAt ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => lagPt D.W D.Γc D.Ac D.rho z.1 z.2.1 z.2.2)
      S (τ₀, (x₀, t₀)) := by
    have hint : D.rho τ₀ x₀ t₀ ∈ Set.Ioo (-D.ρ₀) D.ρ₀ :=
      D.hrhorng τ₀ hτ₀ x₀ ⟨le_of_lt hgt, le_of_lt hneg⟩ t₀
    have hchart := chartSlice_contDiffWithinAt CI a D hτ₀ hint
    rw [← hSdef] at hchart
    have hev : (fun z : ℝ × (ℝ × ℝ) => lagPt D.W D.Γc D.Ac D.rho z.1 z.2.1 z.2.2)
        =ᶠ[𝓝[S] (τ₀, (x₀, t₀))]
        (fun z : ℝ × (ℝ × ℝ) => D.W z.1 z.2.2 (D.rho z.1 z.2.1 z.2.2)) := by
      have hP : {x : ℝ | -Real.sqrt 2 < x ∧ x < 0} ∈ 𝓝 x₀ :=
        Filter.inter_mem (isOpen_Ioi.mem_nhds hgt) (isOpen_Iio.mem_nhds hneg)
      filter_upwards [hpre (fun x => -Real.sqrt 2 < x ∧ x < 0) hP] with z hz
      rw [lagPt, if_pos (le_of_lt hz.2), basePt, if_neg (not_le.mpr hz.1)]
    exact hchart.congr_of_eventuallyEq hev (hev.eq_of_nhdsWithin hpS)
  -- `0 < x < √2`: the chart branch of the `τ_π`-image of the reflected point
  have caseC1 (hpos : 0 < x₀) (hlt : x₀ < Real.sqrt 2) : ContDiffWithinAt ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => lagPt D.W D.Γc D.Ac D.rho z.1 z.2.1 z.2.2)
      S (τ₀, (x₀, t₀)) := by
    have hint : D.rho τ₀ (-x₀) (t₀ - Real.pi) ∈ Set.Ioo (-D.ρ₀) D.ρ₀ :=
      D.hrhorng τ₀ hτ₀ (-x₀) ⟨by linarith, by linarith⟩ (t₀ - Real.pi)
    have hchart := chartSlice_contDiffWithinAt CI a D hτ₀ hint
    rw [← hSdef] at hchart
    have hψ : ContDiffWithinAt ℝ 8 (fun z : ℝ × (ℝ × ℝ) => (z.1, (-z.2.1, z.2.2 - Real.pi)))
        S (τ₀, (x₀, t₀)) :=
      (by fun_prop :
        ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) =>
          (z.1, (-z.2.1, z.2.2 - Real.pi)))).contDiffWithinAt
    have hmap : Set.MapsTo (fun z : ℝ × (ℝ × ℝ) => (z.1, (-z.2.1, z.2.2 - Real.pi))) S S := by
      intro z hz; exact ⟨hz.1, trivial, trivial⟩
    have hcomp : ContDiffWithinAt ℝ 8
        (fun z : ℝ × (ℝ × ℝ) =>
          D.W z.1 (z.2.2 - Real.pi) (D.rho z.1 (-z.2.1) (z.2.2 - Real.pi)))
        S (τ₀, (x₀, t₀)) := by
      have h := hchart.comp (τ₀, (x₀, t₀)) hψ hmap
      simpa only [Function.comp_def] using h
    have htau : ContDiff ℝ 8 (Work.RPV.tau Real.pi) := by unfold Work.RPV.tau; fun_prop
    have hcomp2 : ContDiffWithinAt ℝ 8
        (fun z : ℝ × (ℝ × ℝ) => Work.RPV.tau Real.pi
          (D.W z.1 (z.2.2 - Real.pi) (D.rho z.1 (-z.2.1) (z.2.2 - Real.pi))))
        S (τ₀, (x₀, t₀)) :=
      (htau.contDiffWithinAt (s := Set.univ)).comp (τ₀, (x₀, t₀)) hcomp (fun z _ => trivial)
    have hev : (fun z : ℝ × (ℝ × ℝ) => lagPt D.W D.Γc D.Ac D.rho z.1 z.2.1 z.2.2)
        =ᶠ[𝓝[S] (τ₀, (x₀, t₀))]
        (fun z : ℝ × (ℝ × ℝ) => Work.RPV.tau Real.pi
          (D.W z.1 (z.2.2 - Real.pi) (D.rho z.1 (-z.2.1) (z.2.2 - Real.pi)))) := by
      have hP : {x : ℝ | 0 < x ∧ x < Real.sqrt 2} ∈ 𝓝 x₀ :=
        Filter.inter_mem (isOpen_Ioi.mem_nhds hpos) (isOpen_Iio.mem_nhds hlt)
      filter_upwards [hpre (fun x => 0 < x ∧ x < Real.sqrt 2) hP] with z hz
      rw [lagPt, if_neg (not_le.mpr hz.1), basePt,
        if_neg (not_le.mpr (by linarith [hz.2] : -Real.sqrt 2 < -z.2.1))]
    exact hcomp2.congr_of_eventuallyEq hev (hev.eq_of_nhdsWithin hpS)
  -- `√2 < x`: the collar branch of the `τ_π`-image of the reflected point
  have caseC2 (hgt : Real.sqrt 2 < x₀) : ContDiffWithinAt ℝ 8
      (fun z : ℝ × (ℝ × ℝ) => lagPt D.W D.Γc D.Ac D.rho z.1 z.2.1 z.2.2)
      S (τ₀, (x₀, t₀)) := by
    have hcol : ContDiffWithinAt ℝ 8
        (fun z : ℝ × (ℝ × ℝ) => collarPt D.Γc D.Ac z.1 (sig (-z.2.1)) (z.2.2 - Real.pi))
        S (τ₀, (x₀, t₀)) := by
      have hψ : ContDiffWithinAt ℝ 8
          (fun z : ℝ × (ℝ × ℝ) => (z.1, (sig (-z.2.1), z.2.2 - Real.pi))) S (τ₀, (x₀, t₀)) :=
        (by unfold sig; fun_prop :
          ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) =>
            (z.1, (Work.RPB.B5.sig (-z.2.1), z.2.2 - Real.pi)))).contDiffWithinAt
      have hmap : Set.MapsTo (fun z : ℝ × (ℝ × ℝ) => (z.1, (sig (-z.2.1), z.2.2 - Real.pi)))
          S S := by
        intro z hz; exact ⟨hz.1, trivial, trivial⟩
      have h := (hcollar (sig (-x₀)) (t₀ - Real.pi)).comp (τ₀, (x₀, t₀)) hψ hmap
      simpa only [Function.comp_def] using h
    have htau : ContDiff ℝ 8 (Work.RPV.tau Real.pi) := by unfold Work.RPV.tau; fun_prop
    have hcomp2 : ContDiffWithinAt ℝ 8
        (fun z : ℝ × (ℝ × ℝ) => Work.RPV.tau Real.pi
          (collarPt D.Γc D.Ac z.1 (sig (-z.2.1)) (z.2.2 - Real.pi)))
        S (τ₀, (x₀, t₀)) :=
      (htau.contDiffWithinAt (s := Set.univ)).comp (τ₀, (x₀, t₀)) hcol (fun z _ => trivial)
    have hev : (fun z : ℝ × (ℝ × ℝ) => lagPt D.W D.Γc D.Ac D.rho z.1 z.2.1 z.2.2)
        =ᶠ[𝓝[S] (τ₀, (x₀, t₀))]
        (fun z : ℝ × (ℝ × ℝ) => Work.RPV.tau Real.pi
          (collarPt D.Γc D.Ac z.1 (sig (-z.2.1)) (z.2.2 - Real.pi))) := by
      filter_upwards [hpre (fun x => Real.sqrt 2 < x) (isOpen_Ioi.mem_nhds hgt)] with z hz
      have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
      rw [lagPt, if_neg (not_le.mpr (by linarith : 0 < z.2.1)), basePt,
        if_pos (by linarith : -z.2.1 ≤ -Real.sqrt 2)]
    exact hcomp2.congr_of_eventuallyEq hev (hev.eq_of_nhdsWithin hpS)
  -- ### the case split in `x₀`
  rcases lt_trichotomy x₀ 0 with h0 | h0 | h0
  · rcases lt_trichotomy x₀ (-Real.sqrt 2) with h | h | h
    · exact caseA h
    · exact absurd h hx.1
    · exact caseB h h0
  · exact absurd h0 hx.2.1
  · rcases lt_trichotomy x₀ (Real.sqrt 2) with h | h | h
    · exact caseC1 h0 h
    · exact absurd h hx.2.2
    · exact caseC2 h

end Work.RPB.B5
