import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB25.psiP_edge_zero
import Submission.Work.FTS_StreamBdry.SB25.psiP_edge_axis
import Submission.Work.FTS_StreamBdry.SB25.glue_line_C2
import Submission.Work.FTS_StreamBdry.SB25.oddPerS_pieces
import Submission.Work.FTS_StreamBdry.SB3.psiP_c2
import Submission.Work.FTS_StreamBdry.SB2.sb2_dthDV
import Submission.Work.FTS_StreamBdry.SB2.BrNegFacts
import Submission.Work.FTS_StreamBdry.SB2.BrMirFacts
import Submission.Work.FTS_StreamBdry.SB2.SB2C2Aux
import Submission.Work.FTS_StreamBdry.SB2.OddReflectC2

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.SB2

open scoped Real Topology
open Set Filter
open Work.FTS.StreamBdryIface (oddPerS psiP)

set_option autoImplicit false

noncomputable section

/-! ## §6 The main assembly

For a `C²` function `P` on the open quadrant whose two edge traces at `θ = 0` and `θ = π/2` are
those of `psiP` (`Edge0`, `EdgePi`), the odd/`π`-reflection `oddPerS P` is `C²` on the strip
`(0,∞) × (-(π/2)-1, π/2+1)`.

The two seams `θ = 0` and `θ = π/2` are glued with `SB25.glue_line_C2` (radius `π/2`): the two
branches are `-P(-·)` resp. `-P(π-·)`, whose partials are known by `BrNegFacts`/`BrMirFacts`; the
one-sided limits at the seam are the `Edge0`/`EdgePi` data.  The remaining strip is obtained from
the `C²`-ness on `(0,π)` by the odd reflection `OddReflectC2`. -/

private theorem oddPerS_strip_c2 {P : ℝ → ℝ → ℝ}
    (hP2 : ContDiffOn ℝ 2 (Function.uncurry P) Work.Construction.Qd)
    (hPmid : ∀ w, P w (Real.pi / 2) = 0)
    (hBrNeg : ContDiffOn ℝ 2 (Function.uncurry (fun w θ => -P w (-θ)))
        (Strip (-(Real.pi / 2)) 0) ∧
      (∀ w θ, 0 < w → -(Real.pi / 2) < θ → θ < 0 →
        Work.Spaces.pz (fun w θ => -P w (-θ)) w θ = -Work.Spaces.pz P w (-θ) ∧
        Work.Spaces.pth (fun w θ => -P w (-θ)) w θ = Work.Spaces.pth P w (-θ) ∧
        Work.Spaces.pz (Work.Spaces.pz (fun w θ => -P w (-θ))) w θ
          = -Work.Spaces.pz (Work.Spaces.pz P) w (-θ) ∧
        Work.Spaces.pth (Work.Spaces.pz (fun w θ => -P w (-θ))) w θ
          = Work.Spaces.pth (Work.Spaces.pz P) w (-θ) ∧
        Work.Spaces.pz (Work.Spaces.pth (fun w θ => -P w (-θ))) w θ
          = Work.Spaces.pz (Work.Spaces.pth P) w (-θ) ∧
        Work.Spaces.pth (Work.Spaces.pth (fun w θ => -P w (-θ))) w θ
          = -Work.Spaces.pth (Work.Spaces.pth P) w (-θ)))
    (hBrMir : ContDiffOn ℝ 2 (Function.uncurry (fun w θ => -P w (Real.pi - θ)))
        (Strip (Real.pi / 2) Real.pi) ∧
      (∀ w θ, 0 < w → Real.pi / 2 < θ → θ < Real.pi →
        Work.Spaces.pz (fun w θ => -P w (Real.pi - θ)) w θ
            = -Work.Spaces.pz P w (Real.pi - θ) ∧
        Work.Spaces.pth (fun w θ => -P w (Real.pi - θ)) w θ
            = Work.Spaces.pth P w (Real.pi - θ) ∧
        Work.Spaces.pz (Work.Spaces.pz (fun w θ => -P w (Real.pi - θ))) w θ
          = -Work.Spaces.pz (Work.Spaces.pz P) w (Real.pi - θ) ∧
        Work.Spaces.pth (Work.Spaces.pz (fun w θ => -P w (Real.pi - θ))) w θ
          = Work.Spaces.pth (Work.Spaces.pz P) w (Real.pi - θ) ∧
        Work.Spaces.pz (Work.Spaces.pth (fun w θ => -P w (Real.pi - θ))) w θ
          = Work.Spaces.pz (Work.Spaces.pth P) w (Real.pi - θ) ∧
        Work.Spaces.pth (Work.Spaces.pth (fun w θ => -P w (Real.pi - θ))) w θ
          = -Work.Spaces.pth (Work.Spaces.pth P) w (Real.pi - θ)))
    (hE0 : Edge0 P) (hEP : EdgePi P) :
    ContDiffOn ℝ 2 (Function.uncurry (oddPerS P))
      (Set.Ioi 0 ×ˢ Set.Ioo (-(Real.pi / 2) - 1) (Real.pi / 2 + 1)) := by
  obtain ⟨hodd, hpos, hneg, hgt, hzero⟩ :=
    Work.FTS_StreamBdry.SB25.oddPerS_pieces P hPmid
  -- the agreement of the six partials with those of the two branches
  have hAgA := partials_eqOn_of_eqOn (U := Strip 0 (Real.pi / 2)) (f := oddPerS P) (g := P)
    (isOpen_Ioi.prod isOpen_Ioo)
    (fun p hp => hpos p.1 p.2 hp.2.1 hp.2.2.le)
  have hAgB := partials_eqOn_of_eqOn (U := Strip (-(Real.pi / 2)) 0) (f := oddPerS P)
    (g := fun w θ => -P w (-θ))
    (isOpen_Ioi.prod isOpen_Ioo)
    (fun p hp => hneg p.1 p.2 hp.2.1.le hp.2.2)
  have hAgC := partials_eqOn_of_eqOn (U := Strip (Real.pi / 2) Real.pi) (f := oddPerS P)
    (g := fun w θ => -P w (Real.pi - θ))
    (isOpen_Ioi.prod isOpen_Ioo)
    (fun p hp => hgt p.1 p.2 hp.2.1 hp.2.2)
  -- smoothness on the three open pieces
  have hA_h : ContDiffOn ℝ 2 (Function.uncurry (oddPerS P)) (Strip 0 (Real.pi / 2)) :=
    (hP2.mono strip_le_Qd).congr
      (fun p hp => hpos p.1 p.2 hp.2.1 hp.2.2.le)
  have hB_h : ContDiffOn ℝ 2 (Function.uncurry (oddPerS P)) (Strip (-(Real.pi / 2)) 0) :=
    hBrNeg.1.congr (fun p hp => hneg p.1 p.2 hp.2.1.le hp.2.2)
  have hC_h : ContDiffOn ℝ 2 (Function.uncurry (oddPerS P)) (Strip (Real.pi / 2) Real.pi) :=
    hBrMir.1.congr (fun p hp => hgt p.1 p.2 hp.2.1 hp.2.2)
  -- the punctured strips of the two gluings
  have hsetS0 : Work.FTS_StreamBdry.SB25.glueS 0 (Real.pi / 2)
      = Strip (-(Real.pi / 2)) 0 ∪ Strip 0 (Real.pi / 2) := by
    simp only [Work.FTS_StreamBdry.SB25.glueS, Strip, Set.prod_union]
    rw [show (0 : ℝ) - Real.pi / 2 = -(Real.pi / 2) from by ring,
      show (0 : ℝ) + Real.pi / 2 = Real.pi / 2 from by ring]
  have hsetS1 : Work.FTS_StreamBdry.SB25.glueS (Real.pi / 2) (Real.pi / 2)
      = Strip 0 (Real.pi / 2) ∪ Strip (Real.pi / 2) Real.pi := by
    simp only [Work.FTS_StreamBdry.SB25.glueS, Strip, Set.prod_union]
    rw [show Real.pi / 2 - Real.pi / 2 = (0 : ℝ) from by ring,
      show Real.pi / 2 + Real.pi / 2 = Real.pi from by ring]
  have hglueS0 : ContDiffOn ℝ 2 (Function.uncurry (oddPerS P))
      (Work.FTS_StreamBdry.SB25.glueS 0 (Real.pi / 2)) := by
    rw [hsetS0]
    exact contDiffOn_union_of_isOpen (isOpen_Ioi.prod isOpen_Ioo)
      (isOpen_Ioi.prod isOpen_Ioo) hB_h hA_h
  have hglueS1 : ContDiffOn ℝ 2 (Function.uncurry (oddPerS P))
      (Work.FTS_StreamBdry.SB25.glueS (Real.pi / 2) (Real.pi / 2)) := by
    rw [hsetS1]
    exact contDiffOn_union_of_isOpen (isOpen_Ioi.prod isOpen_Ioo)
      (isOpen_Ioi.prod isOpen_Ioo) hA_h hC_h
  -- continuity on the two full strips
  have hglueU0 : ContinuousOn (Function.uncurry (oddPerS P))
      (Work.FTS_StreamBdry.SB25.glueU 0 (Real.pi / 2)) := by
    rintro ⟨w, θ⟩ hp
    rw [Work.FTS_StreamBdry.SB25.mem_glueU] at hp
    obtain ⟨hw, h1, h2⟩ := hp
    rcases lt_trichotomy θ 0 with h | h | h
    · exact (hB_h.continuousOn.continuousAt
        ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds
          (show (w, θ) ∈ Strip (-(Real.pi / 2)) 0 from ⟨hw, by linarith, h⟩))).continuousWithinAt
    · subst h
      have hval : Function.uncurry (oddPerS P) (w, 0) = 0 := by
        simpa only [Function.uncurry] using hzero w
      refine (continuousAt_seam0 hw hval ?_ ?_ ?_).continuousWithinAt
      · refine Tendsto.congr' (f₁ := Function.uncurry P)
          (f₂ := Function.uncurry (oddPerS P)) ?_
          ((hE0 w hw).1.mono_left (nhdsWithin_mono _ strip_le_Qd))
        filter_upwards [self_mem_nhdsWithin] with q hq
        exact (hpos q.1 q.2 hq.2.1 hq.2.2.le).symm
      · have hmain : Tendsto (fun q : ℝ × ℝ => -(P q.1 (-q.2)))
            (𝓝[Strip (-(Real.pi / 2)) 0] (w, 0)) (𝓝 0) := by
          have h1' : Tendsto (fun q : ℝ × ℝ => P q.1 (-q.2))
              (𝓝[Strip (-(Real.pi / 2)) 0] (w, 0)) (𝓝 0) :=
            tendsto_neg_comp (hE0 w hw).1
          simpa using h1'.neg
        refine Tendsto.congr' (f₁ := fun q : ℝ × ℝ => -(P q.1 (-q.2)))
          (f₂ := Function.uncurry (oddPerS P)) ?_ hmain
        filter_upwards [self_mem_nhdsWithin] with q hq
        show -(P q.1 (-q.2)) = oddPerS P q.1 q.2
        exact (hneg q.1 q.2 hq.2.1.le hq.2.2).symm
      · refine Tendsto.congr' (f₁ := fun _ : ℝ × ℝ => (0 : ℝ))
          (f₂ := Function.uncurry (oddPerS P)) ?_ tendsto_const_nhds
        filter_upwards [self_mem_nhdsWithin] with q hq
        rw [Set.mem_prod, Set.mem_singleton_iff] at hq
        show (0 : ℝ) = oddPerS P q.1 q.2
        rw [hq.2]
        exact (hzero q.1).symm
    · exact (hA_h.continuousOn.continuousAt
        ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds
          (show (w, θ) ∈ Strip 0 (Real.pi / 2) from ⟨hw, h, by linarith⟩))).continuousWithinAt
  have hglueU1 : ContinuousOn (Function.uncurry (oddPerS P))
      (Work.FTS_StreamBdry.SB25.glueU (Real.pi / 2) (Real.pi / 2)) := by
    rintro ⟨w, θ⟩ hp
    rw [Work.FTS_StreamBdry.SB25.mem_glueU] at hp
    obtain ⟨hw, h1, h2⟩ := hp
    rcases lt_trichotomy θ (Real.pi / 2) with h | h | h
    · exact (hA_h.continuousOn.continuousAt
        ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds
          (show (w, θ) ∈ Strip 0 (Real.pi / 2) from ⟨hw, by linarith, h⟩))).continuousWithinAt
    · subst h
      refine (continuousAt_seamPi hw ?_ ?_ ?_ ?_).continuousWithinAt
      · show oddPerS P w (Real.pi / 2) = 0
        rw [hpos w (Real.pi / 2) (by linarith [Real.pi_pos]) le_rfl]
        exact hPmid w
      · have hmain : Tendsto (fun q : ℝ × ℝ => -(P q.1 (Real.pi - q.2)))
            (𝓝[Strip (Real.pi / 2) Real.pi] (w, Real.pi / 2)) (𝓝 0) := by
          have h1' : Tendsto (fun q : ℝ × ℝ => P q.1 (Real.pi - q.2))
              (𝓝[Strip (Real.pi / 2) Real.pi] (w, Real.pi / 2)) (𝓝 0) :=
            tendsto_sub_comp (hEP w hw).1
          simpa using h1'.neg
        refine Tendsto.congr' (f₁ := fun q : ℝ × ℝ => -(P q.1 (Real.pi - q.2)))
          (f₂ := Function.uncurry (oddPerS P)) ?_ hmain
        filter_upwards [self_mem_nhdsWithin] with q hq
        show -(P q.1 (Real.pi - q.2)) = oddPerS P q.1 q.2
        exact (hgt q.1 q.2 hq.2.1 hq.2.2).symm
      · refine Tendsto.congr' (f₁ := Function.uncurry P)
          (f₂ := Function.uncurry (oddPerS P)) ?_
          ((hEP w hw).1.mono_left (nhdsWithin_mono _ strip_le_Qd))
        filter_upwards [self_mem_nhdsWithin] with q hq
        exact (hpos q.1 q.2 hq.2.1 hq.2.2.le).symm
      · refine Tendsto.congr' (f₁ := fun _ : ℝ × ℝ => (0 : ℝ))
          (f₂ := Function.uncurry (oddPerS P)) ?_ tendsto_const_nhds
        filter_upwards [self_mem_nhdsWithin] with q hq
        rw [Set.mem_prod, Set.mem_singleton_iff] at hq
        show (0 : ℝ) = oddPerS P q.1 q.2
        rw [hq.2, hpos q.1 (Real.pi / 2) (by linarith [Real.pi_pos]) le_rfl]
        exact (hPmid q.1).symm
    · exact (hC_h.continuousOn.continuousAt
        ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds
          (show (w, θ) ∈ Strip (Real.pi / 2) Real.pi from ⟨hw, h, by linarith⟩))).continuousWithinAt
  -- the six limits at the two seams
  have hlim0 : ∀ D ∈ ({Work.Spaces.pz (oddPerS P), Work.Spaces.pth (oddPerS P),
      Work.Spaces.pz (Work.Spaces.pz (oddPerS P)),
      Work.Spaces.pth (Work.Spaces.pz (oddPerS P)),
      Work.Spaces.pz (Work.Spaces.pth (oddPerS P)),
      Work.Spaces.pth (Work.Spaces.pth (oddPerS P))} : Set (ℝ → ℝ → ℝ)),
      ∀ z0 : ℝ, 0 < z0 → ∃ l, Tendsto (Function.uncurry D)
        (𝓝[Work.FTS_StreamBdry.SB25.glueS 0 (Real.pi / 2)] (z0, 0)) (𝓝 l) := by
    intro D hD z0 hz0
    obtain ⟨h0P, h0pz, h0pzpz, h0pthpth, ⟨l0pth, h0pth⟩, ⟨l0mix, h0mix1, h0mix2⟩⟩ :=
      hE0 z0 hz0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hD
    rcases hD with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, tendsto_seam0 (D := Work.Spaces.pz (oddPerS P)) (DP := Work.Spaces.pz P) (σ := -1) (l := 0)
        (fun w θ hq => hAgA.1 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgB.1 (w, θ) hq, (hBrNeg.2 w θ hq.1 hq.2.1 hq.2.2).1]; ring)
        h0pz (by ring)⟩
    · exact ⟨l0pth, tendsto_seam0 (D := Work.Spaces.pth (oddPerS P)) (DP := Work.Spaces.pth P) (σ := 1) (l := l0pth)
        (fun w θ hq => hAgA.2.1 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgB.2.1 (w, θ) hq, (hBrNeg.2 w θ hq.1 hq.2.1 hq.2.2).2.1]; ring)
        h0pth (by ring)⟩
    · exact ⟨0, tendsto_seam0 (D := Work.Spaces.pz (Work.Spaces.pz (oddPerS P))) (DP := Work.Spaces.pz (Work.Spaces.pz P)) (σ := -1) (l := 0)
        (fun w θ hq => hAgA.2.2.1 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgB.2.2.1 (w, θ) hq, (hBrNeg.2 w θ hq.1 hq.2.1 hq.2.2).2.2.1]; ring)
        h0pzpz (by ring)⟩
    · exact ⟨l0mix, tendsto_seam0 (D := Work.Spaces.pth (Work.Spaces.pz (oddPerS P))) (DP := Work.Spaces.pth (Work.Spaces.pz P)) (σ := 1) (l := l0mix)
        (fun w θ hq => hAgA.2.2.2.1 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgB.2.2.2.1 (w, θ) hq, (hBrNeg.2 w θ hq.1 hq.2.1 hq.2.2).2.2.2.1]; ring)
        h0mix2 (by ring)⟩
    · exact ⟨l0mix, tendsto_seam0 (D := Work.Spaces.pz (Work.Spaces.pth (oddPerS P))) (DP := Work.Spaces.pz (Work.Spaces.pth P)) (σ := 1) (l := l0mix)
        (fun w θ hq => hAgA.2.2.2.2.1 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgB.2.2.2.2.1 (w, θ) hq, (hBrNeg.2 w θ hq.1 hq.2.1 hq.2.2).2.2.2.2.1]; ring)
        h0mix1 (by ring)⟩
    · exact ⟨0, tendsto_seam0 (D := Work.Spaces.pth (Work.Spaces.pth (oddPerS P))) (DP := Work.Spaces.pth (Work.Spaces.pth P)) (σ := -1) (l := 0)
        (fun w θ hq => hAgA.2.2.2.2.2 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgB.2.2.2.2.2 (w, θ) hq, (hBrNeg.2 w θ hq.1 hq.2.1 hq.2.2).2.2.2.2.2]; ring)
        h0pthpth (by ring)⟩
  have hlim1 : ∀ D ∈ ({Work.Spaces.pz (oddPerS P), Work.Spaces.pth (oddPerS P),
      Work.Spaces.pz (Work.Spaces.pz (oddPerS P)),
      Work.Spaces.pth (Work.Spaces.pz (oddPerS P)),
      Work.Spaces.pz (Work.Spaces.pth (oddPerS P)),
      Work.Spaces.pth (Work.Spaces.pth (oddPerS P))} : Set (ℝ → ℝ → ℝ)),
      ∀ z0 : ℝ, 0 < z0 → ∃ l, Tendsto (Function.uncurry D)
        (𝓝[Work.FTS_StreamBdry.SB25.glueS (Real.pi / 2) (Real.pi / 2)] (z0, Real.pi / 2))
        (𝓝 l) := by
    intro D hD z0 hz0
    obtain ⟨h0P, h0pz, h0pzpz, h0pthpth, ⟨l0pth, h0pth⟩, ⟨l0mix, h0mix1, h0mix2⟩⟩ :=
      hEP z0 hz0
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hD
    rcases hD with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, tendsto_seamPi (D := Work.Spaces.pz (oddPerS P)) (DP := Work.Spaces.pz P) (σ := -1) (l := 0)
        (fun w θ hq => hAgA.1 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgC.1 (w, θ) hq, (hBrMir.2 w θ hq.1 hq.2.1 hq.2.2).1]; ring)
        h0pz (by ring)⟩
    · exact ⟨l0pth, tendsto_seamPi (D := Work.Spaces.pth (oddPerS P)) (DP := Work.Spaces.pth P) (σ := 1) (l := l0pth)
        (fun w θ hq => hAgA.2.1 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgC.2.1 (w, θ) hq, (hBrMir.2 w θ hq.1 hq.2.1 hq.2.2).2.1]; ring)
        h0pth (by ring)⟩
    · exact ⟨0, tendsto_seamPi (D := Work.Spaces.pz (Work.Spaces.pz (oddPerS P))) (DP := Work.Spaces.pz (Work.Spaces.pz P)) (σ := -1) (l := 0)
        (fun w θ hq => hAgA.2.2.1 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgC.2.2.1 (w, θ) hq, (hBrMir.2 w θ hq.1 hq.2.1 hq.2.2).2.2.1]; ring)
        h0pzpz (by ring)⟩
    · exact ⟨l0mix, tendsto_seamPi (D := Work.Spaces.pth (Work.Spaces.pz (oddPerS P))) (DP := Work.Spaces.pth (Work.Spaces.pz P)) (σ := 1) (l := l0mix)
        (fun w θ hq => hAgA.2.2.2.1 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgC.2.2.2.1 (w, θ) hq, (hBrMir.2 w θ hq.1 hq.2.1 hq.2.2).2.2.2.1]; ring)
        h0mix2 (by ring)⟩
    · exact ⟨l0mix, tendsto_seamPi (D := Work.Spaces.pz (Work.Spaces.pth (oddPerS P))) (DP := Work.Spaces.pz (Work.Spaces.pth P)) (σ := 1) (l := l0mix)
        (fun w θ hq => hAgA.2.2.2.2.1 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgC.2.2.2.2.1 (w, θ) hq, (hBrMir.2 w θ hq.1 hq.2.1 hq.2.2).2.2.2.2.1]; ring)
        h0mix1 (by ring)⟩
    · exact ⟨0, tendsto_seamPi (D := Work.Spaces.pth (Work.Spaces.pth (oddPerS P))) (DP := Work.Spaces.pth (Work.Spaces.pth P)) (σ := -1) (l := 0)
        (fun w θ hq => hAgA.2.2.2.2.2 (w, θ) hq)
        (fun w θ hq => by
          rw [hAgC.2.2.2.2.2 (w, θ) hq, (hBrMir.2 w θ hq.1 hq.2.1 hq.2.2).2.2.2.2.2]; ring)
        h0pthpth (by ring)⟩
  -- the two gluings
  have hC2_0 : ContDiffOn ℝ 2 (Function.uncurry (oddPerS P))
      (Work.FTS_StreamBdry.SB25.glueU 0 (Real.pi / 2)) :=
    Work.FTS_StreamBdry.SB25.glue_line_C2 (oddPerS P) 0 (Real.pi / 2)
      (by linarith [Real.pi_pos]) hglueS0 hglueU0 hlim0
  have hC2_1 : ContDiffOn ℝ 2 (Function.uncurry (oddPerS P))
      (Work.FTS_StreamBdry.SB25.glueU (Real.pi / 2) (Real.pi / 2)) :=
    Work.FTS_StreamBdry.SB25.glue_line_C2 (oddPerS P) (Real.pi / 2) (Real.pi / 2)
      (by linarith [Real.pi_pos]) hglueS1 hglueU1 hlim1
  -- the odd reflection of the `(0,π)` strip
  have hC2_1' : ContDiffOn ℝ 2 (Function.uncurry (oddPerS P))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 Real.pi) := by
    have hset : Work.FTS_StreamBdry.SB25.glueU (Real.pi / 2) (Real.pi / 2)
        = Set.Ioi 0 ×ˢ Set.Ioo 0 Real.pi := by
      simp only [Work.FTS_StreamBdry.SB25.glueU]
      rw [show Real.pi / 2 - Real.pi / 2 = (0 : ℝ) from by ring,
        show Real.pi / 2 + Real.pi / 2 = Real.pi from by ring]
    rw [← hset]
    exact hC2_1
  have hC2_neg : ContDiffOn ℝ 2 (Function.uncurry (oddPerS P)) (Strip (-Real.pi) 0) :=
    OddReflectC2 hodd hC2_1'
  -- the cover
  have hpi : (1 : ℝ) < Real.pi / 2 := by linarith [Real.pi_gt_three]
  rintro ⟨w, θ⟩ hp
  rw [Set.mem_prod] at hp
  obtain ⟨hw, h1, h2⟩ := hp
  rcases lt_trichotomy θ 0 with h | h | h
  · exact (hC2_neg.contDiffAt
      ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds
        (show (w, θ) ∈ Strip (-Real.pi) 0 from ⟨hw, by linarith, h⟩))).contDiffWithinAt
  · subst h
    refine (hC2_0.contDiffAt ?_).contDiffWithinAt
    exact (Work.FTS_StreamBdry.SB25.isOpen_glueU 0 (Real.pi / 2)).mem_nhds (by
      rw [Work.FTS_StreamBdry.SB25.mem_glueU]
      exact ⟨hw, by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩)
  · refine (hC2_1.contDiffAt ?_).contDiffWithinAt
    exact (Work.FTS_StreamBdry.SB25.isOpen_glueU (Real.pi / 2) (Real.pi / 2)).mem_nhds (by
      rw [Work.FTS_StreamBdry.SB25.mem_glueU]
      exact ⟨hw, by linarith [hpi], by linarith [h2, Real.pi_pos, hpi]⟩)

theorem sb2_c2 {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M)
    (hF : Work.FTS.StreamBdryIface.SrcOK F L Mf)
    (hdthDV : ∃ K' : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.pth (Work.Spaces.DzIter 1
        (Work.Construction.Vop (Work.FTS.StreamBdryIface.psiP αG Ψ))) z θ| ≤ K') :
    ContDiffOn ℝ 2 (Function.uncurry
      (Work.FTS.StreamBdryIface.oddPerS (Work.FTS.StreamBdryIface.psiP αG Ψ)))
      (Set.Ioi 0 ×ˢ Set.Ioo (-(Real.pi / 2) - 1) (Real.pi / 2 + 1)) := by
  have hP2 : ContDiffOn ℝ 2 (Function.uncurry (psiP αG Ψ)) Work.Construction.Qd :=
    Work.FTS_StreamBdry.SB3.psiP_c2 hαG h3 hslot
  have hPmid : ∀ w, psiP αG Ψ w (Real.pi / 2) = 0 := by
    intro w
    rw [Work.FTS_StreamBdry.psiP_eq_Iint]
    have hs2 : Work.Construction.s2 (Real.pi / 2) = 0 := by
      rw [Work.Construction.s2_eq, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
    rw [hs2]
    ring
  have hE0 : Edge0 (psiP αG Ψ) := fun z0 hz0 =>
    Work.FTS_StreamBdry.SB25.psiP_edge_zero (αG := αG) (M := M) (L := L) (Mf := Mf)
      hαG hsol h3 hslot hF hdthDV z0 hz0
  have hEP : EdgePi (psiP αG Ψ) := fun z0 hz0 =>
    Work.FTS_StreamBdry.SB25.psiP_edge_axis (αG := αG) (M := M) (L := L) (Mf := Mf)
      hαG hsol h3 hslot hF hdthDV z0 hz0
  exact oddPerS_strip_c2 hP2 hPmid
    (BrNegFacts hP2) (BrMirFacts hP2) hE0 hEP

end

end Work.FTS_StreamBdry.SB2
