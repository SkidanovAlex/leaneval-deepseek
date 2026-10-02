import Mathlib
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.CylSides
import Submission.Work.ELRig.SideFlipChart
import Submission.Work.ELRig.chart_local_inverse
import Submission.Work.ELRig.localInverse_sphere_two

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

noncomputable section

namespace Work.ELRig

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ} {d : Work.EL.RootParabolic c}
variable {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((Tantibar c)^[5]) d.z₁}

/-- **The topological core of `local_arc_portion`.**  Let `γ : ℝ → ℂ` be continuous and
`1`-periodic up to the shift `w ↦ w + 1`, and suppose that at most two parameters give a point at
distance `ρ ∈ (0,1)` from `γ s₀` (this is the geometric content supplied by the straightening
chart).  Then the preimage of the open ball of radius `ρ` around `γ s₀` is exactly the interval
`(s₁,s₂)`, with `s₁ < s₀ < s₂` and `γ s₁`, `γ s₂` on the sphere of radius `ρ`. -/
theorem local_arc_portion_of_rays_aux {γ : ℝ → ℂ} {s₀ ρ : ℝ} (hcont : Continuous γ)
    (hper : ∀ s : ℝ, γ (s + 1) = γ s + 1) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (htwo : ∀ a b c : ℝ, dist (γ a) (γ s₀) = ρ → dist (γ b) (γ s₀) = ρ →
      dist (γ c) (γ s₀) = ρ → a = b ∨ a = c ∨ b = c) :
    ∃ s₁ s₂ : ℝ, s₁ < s₀ ∧ s₀ < s₂ ∧
      (∀ s : ℝ, dist (γ s) (γ s₀) < ρ → s ∈ Set.Icc s₁ s₂) ∧
      (∀ s ∈ Set.Icc s₁ s₂, s ≠ s₁ → s ≠ s₂ → dist (γ s) (γ s₀) < ρ) ∧
      dist (γ s₁) (γ s₀) = ρ ∧ dist (γ s₂) (γ s₀) = ρ := by
  classical
  have hcontd : Continuous fun s : ℝ => dist (γ s) (γ s₀) := hcont.dist continuous_const
  have hclosed_le : IsClosed {s : ℝ | dist (γ s) (γ s₀) ≤ ρ} :=
    isClosed_le hcontd continuous_const
  have hclosed_lt : IsOpen {s : ℝ | dist (γ s) (γ s₀) < ρ} :=
    isOpen_lt hcontd continuous_const
  -- ## the first shift at `s₀`
  have hper_p : γ (s₀ + 1) = γ s₀ + 1 := hper s₀
  have hdist_p : dist (γ (s₀ + 1)) (γ s₀) = 1 := by
    rw [hper_p, dist_eq_norm]; simp
  have hper_m : γ (s₀ - 1) = γ s₀ - 1 := by
    have h := hper (s₀ - 1)
    have h1 : s₀ - 1 + 1 = s₀ := by ring
    rw [h1] at h
    exact eq_sub_iff_add_eq.mpr h.symm
  have hdist_m : dist (γ (s₀ - 1)) (γ s₀) = 1 := by
    rw [hper_m, dist_eq_norm]; norm_num
  -- ## the set of points at distance `≥ ρ` on the right of `s₀`
  set S₂ : Set ℝ := {s : ℝ | s₀ ≤ s ∧ ρ ≤ dist (γ s) (γ s₀)} with hS₂def
  have hS₂closed : IsClosed S₂ := by
    rw [hS₂def]
    exact isClosed_Ici.inter (isClosed_le continuous_const hcontd)
  have hs₂mem₀ : s₀ + 1 ∈ S₂ := by
    rw [hS₂def]
    exact ⟨by linarith, by rw [hdist_p]; linarith⟩
  have hS₂ne : S₂.Nonempty := ⟨s₀ + 1, hs₂mem₀⟩
  have hS₂bd : BddBelow S₂ := ⟨s₀, fun s hs => by rw [hS₂def] at hs; exact hs.1⟩
  set s₂ : ℝ := sInf S₂ with hs₂def
  have hs₂mem : s₂ ∈ S₂ := hS₂closed.csInf_mem hS₂ne hS₂bd
  have hs₂ge : s₀ ≤ s₂ := by rw [hS₂def] at hs₂mem; exact hs₂mem.1
  have hs₂dist_ge : ρ ≤ dist (γ s₂) (γ s₀) := by
    rw [hS₂def] at hs₂mem; exact hs₂mem.2
  have hs₂le : s₂ ≤ s₀ + 1 := by
    rw [hs₂def]; exact csInf_le hS₂bd hs₂mem₀
  have hs₂gt : s₀ < s₂ := by
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont.continuousAt ρ hρ
    have hlow : ∀ s ∈ S₂, s₀ + δ / 2 ≤ s := by
      intro s hs
      by_contra hc
      rw [not_le] at hc
      have hsge : s₀ ≤ s := by rw [hS₂def] at hs; exact hs.1
      have hd : dist s s₀ < δ := by
        rw [Real.dist_eq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - s₀)]
        linarith
      have h1 := hδ hd
      have h2 : ρ ≤ dist (γ s) (γ s₀) := by rw [hS₂def] at hs; exact hs.2
      linarith
    have h3 := le_csInf hS₂ne hlow
    rw [← hs₂def] at h3
    linarith
  have hs₂dist_le : dist (γ s₂) (γ s₀) ≤ ρ := by
    have hsub : Set.Ioo s₀ s₂ ⊆ {s : ℝ | dist (γ s) (γ s₀) ≤ ρ} := by
      intro s hs
      change dist (γ s) (γ s₀) ≤ ρ
      by_contra hc
      rw [not_le] at hc
      have hmem : s ∈ S₂ := by
        rw [hS₂def]; exact ⟨le_of_lt hs.1, le_of_lt hc⟩
      have h4 := csInf_le hS₂bd hmem
      rw [← hs₂def] at h4
      linarith [hs.2]
    have hcl : s₂ ∈ closure (Set.Ioo s₀ s₂) := by
      rw [closure_Ioo (ne_of_lt hs₂gt)]; exact ⟨hs₂ge, le_rfl⟩
    exact (closure_minimal hsub hclosed_le) hcl
  have hs₂dist : dist (γ s₂) (γ s₀) = ρ := le_antisymm hs₂dist_le hs₂dist_ge
  -- ## the set of points at distance `≥ ρ` on the left of `s₀`
  set S₁ : Set ℝ := {s : ℝ | s ≤ s₀ ∧ ρ ≤ dist (γ s) (γ s₀)} with hS₁def
  have hS₁closed : IsClosed S₁ := by
    rw [hS₁def]
    exact isClosed_Iic.inter (isClosed_le continuous_const hcontd)
  have hs₁mem₀ : s₀ - 1 ∈ S₁ := by
    rw [hS₁def]
    exact ⟨by linarith, by rw [hdist_m]; linarith⟩
  have hS₁ne : S₁.Nonempty := ⟨s₀ - 1, hs₁mem₀⟩
  have hS₁bd : BddAbove S₁ := ⟨s₀, fun s hs => by rw [hS₁def] at hs; exact hs.1⟩
  set s₁ : ℝ := sSup S₁ with hs₁def
  have hs₁mem : s₁ ∈ S₁ := hS₁closed.csSup_mem hS₁ne hS₁bd
  have hs₁le : s₁ ≤ s₀ := by rw [hS₁def] at hs₁mem; exact hs₁mem.1
  have hs₁dist_ge : ρ ≤ dist (γ s₁) (γ s₀) := by
    rw [hS₁def] at hs₁mem; exact hs₁mem.2
  have hs₁ge : s₀ - 1 ≤ s₁ := by
    rw [hs₁def]; exact le_csSup hS₁bd hs₁mem₀
  have hs₁lt : s₁ < s₀ := by
    obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousAt_iff.mp hcont.continuousAt ρ hρ
    have hup : ∀ s ∈ S₁, s ≤ s₀ - δ / 2 := by
      intro s hs
      by_contra hc
      rw [not_le] at hc
      have hsle : s ≤ s₀ := by rw [hS₁def] at hs; exact hs.1
      have hd : dist s s₀ < δ := by
        rw [Real.dist_eq, abs_of_nonpos (by linarith : s - s₀ ≤ 0)]
        linarith
      have h1 := hδ hd
      have h2 : ρ ≤ dist (γ s) (γ s₀) := by rw [hS₁def] at hs; exact hs.2
      linarith
    have h3 := csSup_le hS₁ne hup
    rw [← hs₁def] at h3
    linarith
  have hs₁dist_le : dist (γ s₁) (γ s₀) ≤ ρ := by
    have hsub : Set.Ioo s₁ s₀ ⊆ {s : ℝ | dist (γ s) (γ s₀) ≤ ρ} := by
      intro s hs
      change dist (γ s) (γ s₀) ≤ ρ
      by_contra hc
      rw [not_le] at hc
      have hmem : s ∈ S₁ := by
        rw [hS₁def]; exact ⟨le_of_lt hs.2, le_of_lt hc⟩
      have h4 := le_csSup hS₁bd hmem
      rw [← hs₁def] at h4
      linarith [hs.1]
    have hcl : s₁ ∈ closure (Set.Ioo s₁ s₀) := by
      rw [closure_Ioo (ne_of_lt hs₁lt)]; exact ⟨le_rfl, hs₁le⟩
    exact (closure_minimal hsub hclosed_le) hcl
  have hs₁dist : dist (γ s₁) (γ s₀) = ρ := le_antisymm hs₁dist_le hs₁dist_ge
  -- ## the interval
  have hIoo : ∀ s ∈ Set.Ioo s₁ s₂, dist (γ s) (γ s₀) < ρ := by
    intro s hs
    by_contra hc
    rw [not_lt] at hc
    rcases le_total s₀ s with h | h
    · have hmem : s ∈ S₂ := by rw [hS₂def]; exact ⟨h, hc⟩
      have h4 := csInf_le hS₂bd hmem
      rw [← hs₂def] at h4
      linarith [hs.2]
    · have hmem : s ∈ S₁ := by rw [hS₁def]; exact ⟨h, hc⟩
      have h4 := le_csSup hS₁bd hmem
      rw [← hs₁def] at h4
      linarith [hs.1]
  -- ## the two sides of the ball
  have hright : ∀ s : ℝ, dist (γ s) (γ s₀) < ρ → s < s₂ := by
      intro s hs
      by_contra hc
      rw [not_lt] at hc
      have hne : s ≠ s₂ := by
        intro hh; rw [hh, hs₂dist] at hs; exact absurd hs (lt_irrefl ρ)
      have hgt : s₂ < s := lt_of_le_of_ne hc (Ne.symm hne)
      set Y : Set ℝ := {y : ℝ | y ∈ Set.Icc s₂ s ∧ ρ ≤ dist (γ y) (γ s₀)} with hY
      have hYne : Y.Nonempty :=
        ⟨s₂, by rw [hY]; exact ⟨⟨le_rfl, hc⟩, le_of_eq hs₂dist.symm⟩⟩
      have hYbd : BddAbove Y := ⟨s, fun y hy => by rw [hY] at hy; exact hy.1.2⟩
      have hYclosed : IsClosed Y := by
        rw [hY]; exact isClosed_Icc.inter (isClosed_le continuous_const hcontd)
      set b : ℝ := sSup Y with hb
      have hbmem : b ∈ Y := hYclosed.csSup_mem hYne hYbd
      have hbIcc : b ∈ Set.Icc s₂ s := (hY ▸ hbmem).1
      have hbY : ∀ y ∈ Y, y ≤ b := fun y hy => le_csSup hYbd hy
      have hblt : b < s := by
        rcases lt_or_eq_of_le hbIcc.2 with h | h
        · exact h
        · exact absurd (h ▸ (hY ▸ hbmem).2) (not_le.mpr hs)
      have hbdist_le : dist (γ b) (γ s₀) ≤ ρ := by
        have hsub : Set.Ioo b s ⊆ {y : ℝ | dist (γ y) (γ s₀) ≤ ρ} := by
          intro y hy
          change dist (γ y) (γ s₀) ≤ ρ
          have hyIcc : y ∈ Set.Icc s₂ s := ⟨le_trans hbIcc.1 hy.1.le, hy.2.le⟩
          have hyY : y ∉ Y := fun hh => absurd (hbY y hh) (not_le.mpr hy.1)
          rw [hY] at hyY
          by_contra hcon
          exact hyY ⟨hyIcc, le_of_lt (not_le.mp hcon)⟩
        have hcl : b ∈ closure (Set.Ioo b s) := by
          rw [closure_Ioo (ne_of_lt hblt)]; exact ⟨le_rfl, hblt.le⟩
        exact (closure_minimal hsub hclosed_le) hcl
      have hbT : dist (γ b) (γ s₀) = ρ := le_antisymm hbdist_le (hY ▸ hbmem).2
      rcases lt_or_eq_of_le hbIcc.1 with hbgt | hbeq
      · exact absurd (htwo s₁ s₂ b hs₁dist hs₂dist hbT)
          (by rintro (h | h | h) <;> linarith [hs₁lt, hs₂gt, hbgt])
      · have hZopen : ∀ y ∈ Set.Ioo s₂ s, dist (γ y) (γ s₀) < ρ := by
          intro y hy
          have hyIcc : y ∈ Set.Icc s₂ s := ⟨hy.1.le, hy.2.le⟩
          have hyY : y ∉ Y := by
            intro hh
            have h5 := hbY y hh
            rw [← hbeq] at h5
            exact absurd h5 (not_le.mpr hy.1)
          rw [hY] at hyY
          by_contra hcon
          exact hyY ⟨hyIcc, not_lt.mp hcon⟩
        set Z : Set ℝ := {z : ℝ | ∀ y : ℝ, s₂ < y → y < z → dist (γ y) (γ s₀) < ρ} with hZ
        have hsZ : s ∈ Z := by
          rw [hZ]; intro y hy hy2; exact hZopen y ⟨hy, hy2⟩
        have hZne : Z.Nonempty := ⟨s, hsZ⟩
        have hZbd : BddAbove Z := by
          refine ⟨s₂ + 2, fun z hz => ?_⟩
          by_contra hcon
          rw [not_le] at hcon
          have hmem := hz (s₂ + 2) (by linarith) hcon
          have hper2 : γ (s₂ + 2) = γ s₂ + 2 := by
            have h1 : γ (s₂ + 1) = γ s₂ + 1 := hper s₂
            have h2 : γ (s₂ + 1 + 1) = γ (s₂ + 1) + 1 := hper (s₂ + 1)
            have h3 : s₂ + 1 + 1 = s₂ + 2 := by ring
            rw [h3] at h2
            rw [h2, h1]; ring
          have hbd : ρ < dist (γ (s₂ + 2)) (γ s₀) := by
            rw [hper2]
            have htri : 2 - dist (γ s₂) (γ s₀) ≤ dist (γ s₂ + 2) (γ s₀) := by
              have h6 := dist_triangle (γ s₂ + 2) (γ s₀) (γ s₂)
              rw [dist_comm (γ s₀) (γ s₂)] at h6
              have hd : dist (γ s₂ + 2) (γ s₂) = 2 := by
                rw [dist_eq_norm]; norm_num
              linarith [hd]
            rw [hs₂dist] at htri
            linarith
          linarith
        set h : ℝ := sSup Z with hh
        have hhgt : s₂ < h := lt_of_lt_of_le hgt (le_csSup hZbd hsZ)
        have hsub : Set.Ioo s₂ h ⊆ {y : ℝ | dist (γ y) (γ s₀) < ρ} := by
          intro y hy
          obtain ⟨z, hzZ, hyz⟩ := (lt_csSup_iff hZbd hZne).mp hy.2
          exact hzZ y hy.1 hyz
        have hhnotmem : h ∉ {y : ℝ | dist (γ y) (γ s₀) < ρ} := by
          intro hmem
          have hopen : {y : ℝ | dist (γ y) (γ s₀) < ρ} ∈ 𝓝 h :=
            hclosed_lt.mem_nhds hmem
          obtain ⟨η, hηpos, hη⟩ := Metric.mem_nhds_iff.mp hopen
          have hmemZ : h + η / 2 ∈ Z := by
            rw [hZ]; intro y hy hy2
            rcases lt_or_ge y h with hyh | hyh
            · exact hsub ⟨hy, hyh⟩
            · exact hη (by
                rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (by linarith)]
                linarith)
          have := le_csSup hZbd hmemZ
          linarith
        have hhge : ρ ≤ dist (γ h) (γ s₀) := not_lt.mp (fun h7 => hhnotmem h7)
        have hhle : dist (γ h) (γ s₀) ≤ ρ := by
          have hcl : h ∈ closure (Set.Ioo s₂ h) := by
            rw [closure_Ioo (ne_of_lt hhgt)]; exact ⟨le_of_lt hhgt, le_rfl⟩
          refine (closure_minimal ?_ hclosed_le) hcl
          intro y hy
          have hy' : dist (γ y) (γ s₀) < ρ := hsub hy
          exact le_of_lt hy'
        have hhT : dist (γ h) (γ s₀) = ρ := le_antisymm hhle hhge
        exact absurd (htwo s₁ s₂ h hs₁dist hs₂dist hhT)
          (by rintro (h8 | h8 | h8) <;> linarith [hs₁lt, hs₂gt, hhgt])
  have hleft : ∀ s : ℝ, dist (γ s) (γ s₀) < ρ → s₁ < s := by
      intro s hs
      by_contra hc
      rw [not_lt] at hc
      have hne : s ≠ s₁ := by
        intro hh; rw [hh, hs₁dist] at hs; exact absurd hs (lt_irrefl ρ)
      have hlt : s < s₁ := lt_of_le_of_ne hc hne
      set Y : Set ℝ := {y : ℝ | y ∈ Set.Icc s s₁ ∧ ρ ≤ dist (γ y) (γ s₀)} with hY
      have hYne : Y.Nonempty :=
        ⟨s₁, by rw [hY]; exact ⟨⟨hlt.le, le_rfl⟩, le_of_eq hs₁dist.symm⟩⟩
      have hYbd : BddBelow Y := ⟨s, fun y hy => by rw [hY] at hy; exact hy.1.1⟩
      have hYclosed : IsClosed Y := by
        rw [hY]; exact isClosed_Icc.inter (isClosed_le continuous_const hcontd)
      set a : ℝ := sInf Y with ha
      have hamem : a ∈ Y := hYclosed.csInf_mem hYne hYbd
      have haIcc : a ∈ Set.Icc s s₁ := (hY ▸ hamem).1
      have haY : ∀ y ∈ Y, a ≤ y := fun y hy => csInf_le hYbd hy
      have halt : s < a := by
        rcases lt_or_eq_of_le haIcc.1 with h | h
        · exact h
        · exact absurd (h ▸ (hY ▸ hamem).2) (not_le.mpr hs)
      have hadist_le : dist (γ a) (γ s₀) ≤ ρ := by
        have hsub : Set.Ioo s a ⊆ {y : ℝ | dist (γ y) (γ s₀) ≤ ρ} := by
          intro y hy
          change dist (γ y) (γ s₀) ≤ ρ
          have hyIcc : y ∈ Set.Icc s s₁ := ⟨hy.1.le, le_trans hy.2.le haIcc.2⟩
          have hyY : y ∉ Y := fun hh => absurd (haY y hh) (not_le.mpr hy.2)
          rw [hY] at hyY
          by_contra hcon
          exact hyY ⟨hyIcc, le_of_lt (not_le.mp hcon)⟩
        have hcl : a ∈ closure (Set.Ioo s a) := by
          rw [closure_Ioo (ne_of_lt halt)]; exact ⟨le_of_lt halt, le_rfl⟩
        exact (closure_minimal hsub hclosed_le) hcl
      have haT : dist (γ a) (γ s₀) = ρ := le_antisymm hadist_le (hY ▸ hamem).2
      by_cases haeq : a = s₁
      · have hZopen : ∀ y ∈ Set.Ioo s s₁, dist (γ y) (γ s₀) < ρ := by
          intro y hy
          have hyIcc : y ∈ Set.Icc s s₁ := ⟨hy.1.le, hy.2.le⟩
          have hyY : y ∉ Y := by
            intro hh
            have h5 := haY y hh
            rw [haeq] at h5
            exact absurd h5 (not_le.mpr hy.2)
          rw [hY] at hyY
          by_contra hcon
          exact hyY ⟨hyIcc, not_lt.mp hcon⟩
        set Z : Set ℝ := {z : ℝ | ∀ y : ℝ, z < y → y < s₁ → dist (γ y) (γ s₀) < ρ} with hZ
        have hsZ : s ∈ Z := by
          rw [hZ]; intro y hy hy2; exact hZopen y ⟨hy, hy2⟩
        have hZne : Z.Nonempty := ⟨s, hsZ⟩
        have hZbd : BddBelow Z := by
          refine ⟨s₁ - 2, fun z hz => ?_⟩
          by_contra hcon
          rw [not_le] at hcon
          have hmem := hz (s₁ - 2) hcon (by linarith)
          have hper2 : γ (s₁ - 2) = γ s₁ - 2 := by
            have h1 : γ (s₁ - 1) = γ s₁ - 1 := by
              have h9 := hper (s₁ - 1)
              have h10 : s₁ - 1 + 1 = s₁ := by ring
              rw [h10] at h9
              exact eq_sub_iff_add_eq.mpr h9.symm
            have h2 : γ (s₁ - 1 - 1) = γ (s₁ - 1) - 1 := by
              have h9 := hper (s₁ - 1 - 1)
              have h10 : s₁ - 1 - 1 + 1 = s₁ - 1 := by ring
              rw [h10] at h9
              exact eq_sub_iff_add_eq.mpr h9.symm
            have h3 : s₁ - 1 - 1 = s₁ - 2 := by ring
            rw [h3] at h2
            rw [h2, h1]; ring
          have hbd : ρ < dist (γ (s₁ - 2)) (γ s₀) := by
            rw [hper2]
            have htri : 2 - dist (γ s₁) (γ s₀) ≤ dist (γ s₁ - 2) (γ s₀) := by
              have h6 := dist_triangle (γ s₁ - 2) (γ s₀) (γ s₁)
              rw [dist_comm (γ s₀) (γ s₁)] at h6
              have hd : dist (γ s₁ - 2) (γ s₁) = 2 := by
                rw [dist_eq_norm]
                have : γ s₁ - 2 - γ s₁ = -2 := by ring
                rw [this]; norm_num
              linarith [hd]
            rw [hs₁dist] at htri
            linarith
          linarith
        set k : ℝ := sInf Z with hk
        have hklt : k < s₁ := by
          have h11 : k ≤ s := csInf_le hZbd hsZ
          linarith
        have hsub : Set.Ioo k s₁ ⊆ {y : ℝ | dist (γ y) (γ s₀) < ρ} := by
          intro y hy
          obtain ⟨z, hzZ, hzy⟩ := (csInf_lt_iff hZbd hZne).mp hy.1
          exact hzZ y hzy hy.2
        have hknotmem : k ∉ {y : ℝ | dist (γ y) (γ s₀) < ρ} := by
          intro hmem
          have hopen : {y : ℝ | dist (γ y) (γ s₀) < ρ} ∈ 𝓝 k :=
            hclosed_lt.mem_nhds hmem
          obtain ⟨η, hηpos, hη⟩ := Metric.mem_nhds_iff.mp hopen
          have hmemZ : k - η / 2 ∈ Z := by
            rw [hZ]; intro y hy hy2
            rcases le_or_gt y k with hyk | hyk
            · exact hη (by
                rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith)]
                linarith)
            · exact hsub ⟨hyk, hy2⟩
          have := csInf_le hZbd hmemZ
          linarith
        have hkge : ρ ≤ dist (γ k) (γ s₀) := not_lt.mp (fun h7 => hknotmem h7)
        have hkle : dist (γ k) (γ s₀) ≤ ρ := by
          have hcl : k ∈ closure (Set.Ioo k s₁) := by
            rw [closure_Ioo (ne_of_lt hklt)]; exact ⟨le_rfl, le_of_lt hklt⟩
          refine (closure_minimal ?_ hclosed_le) hcl
          intro y hy
          have hy' : dist (γ y) (γ s₀) < ρ := hsub hy
          exact le_of_lt hy'
        have hkT : dist (γ k) (γ s₀) = ρ := le_antisymm hkle hkge
        exact absurd (htwo k s₁ s₂ hkT hs₁dist hs₂dist)
          (by rintro (h8 | h8 | h8) <;> linarith [hklt, hs₁lt, hs₂gt])
      · have halt' : a < s₁ := lt_of_le_of_ne haIcc.2 haeq
        exact absurd (htwo a s₁ s₂ haT hs₁dist hs₂dist)
          (by rintro (h8 | h8 | h8) <;> linarith [halt', hs₁lt, hs₂gt])

  refine ⟨s₁, s₂, hs₁lt, hs₂gt, ?_, ?_, hs₁dist, hs₂dist⟩
  · intro s hs
    exact ⟨le_of_lt (hleft s hs), le_of_lt (hright s hs)⟩
  · intro s hs hne₁ hne₂
    exact hIoo s ⟨lt_of_le_of_ne hs.1 (Ne.symm hne₁), lt_of_le_of_ne hs.2 hne₂⟩


/-- **The circle around a lift point meets the lift at most twice.**  For a point `s₀` whose lift
value `p = γ₁ s₀` lies in the far-left half plane there is a radius `ρ ∈ (0,1)` such that the
circle of radius `ρ` around `p` meets the lift in at most two points. -/
theorem sphere_count (L : RayCylLift d fl) {s₀ : ℝ} (hre : (L.γ₁ s₀).re < -L.R) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < 1 ∧ ∃ A B : ℂ, ∀ s : ℝ, dist (L.γ₁ s) (L.γ₁ s₀) = ρ →
      L.γ₁ s = A ∨ L.γ₁ s = B := by
  classical
  -- the straightening chart and its local inverse at `p = γ₁ s₀`
  obtain ⟨δ₁, hδ₁pos, δ₂, hδ₂pos, k, hkan, hkright, hkleft, hkderiv⟩ :=
    chart_local_inverse (c := c) d fl L hre
  have hchartp : sideFlipChart c d fl L s₀ (L.γ₁ s₀) = 1 := sideFlipChart_at_p
  have hk1 : k 1 = L.γ₁ s₀ := by
    rw [← hchartp]
    exact hkleft (L.γ₁ s₀) (Metric.mem_ball_self hδ₁pos)
  obtain ⟨ε, hεpos, hεδ, hmono, hanti, huniq⟩ :=
    localInverse_sphere_two (k := k) (p := L.γ₁ s₀) hδ₂pos hkan hk1 hkderiv
  -- the chart is continuous at `p`
  have hGcont : ContinuousAt (sideFlipChart c d fl L s₀) (L.γ₁ s₀) :=
    (analyticAt_sideFlipChart (c := c) d fl L s₀).continuousAt
  obtain ⟨ρ₁, hρ₁pos, hρ₁⟩ := Metric.continuousAt_iff.mp hGcont ε hεpos
  -- positivity at the two endpoints and the radius bound
  have hfε : (0 : ℝ) < ‖k (1 + ε) - L.γ₁ s₀‖ := by
    have h := hmono (Set.mem_Icc.mpr ⟨le_rfl, hεpos.le⟩)
      (Set.mem_Icc.mpr ⟨hεpos.le, le_rfl⟩) hεpos
    simpa [hk1] using h
  have hfmε_raw : (0 : ℝ) < ‖k (1 + (-ε)) - L.γ₁ s₀‖ := by
    have h := hanti (Set.mem_Icc.mpr ⟨by linarith, by linarith⟩)
      (Set.mem_Icc.mpr ⟨by linarith, le_rfl⟩) (by linarith : -ε < (0 : ℝ))
    simpa [hk1] using h
  have hfmε : (0 : ℝ) < ‖k (1 - ε) - L.γ₁ s₀‖ := by
    have h : (1 : ℂ) + -(↑ε) = 1 - ↑ε := by ring
    rw [← h]; exact hfmε_raw
  set m : ℝ := min (min δ₁ ρ₁) (min (min ‖k (1 + ε) - L.γ₁ s₀‖ ‖k (1 - ε) - L.γ₁ s₀‖) 1)
    with hm
  have hmpos : 0 < m := by
    rw [hm]
    exact lt_min (lt_min hδ₁pos hρ₁pos) (lt_min (lt_min hfε hfmε) one_pos)
  have hmδ₁ : m ≤ δ₁ := by
    rw [hm]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hmρ₁ : m ≤ ρ₁ := by
    rw [hm]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hmε : m ≤ ‖k (1 + ε) - L.γ₁ s₀‖ := by
    rw [hm]
    exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_left _ _))
  have hmε' : m ≤ ‖k (1 - ε) - L.γ₁ s₀‖ := by
    rw [hm]
    exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (min_le_right _ _))
  have hm1 : m ≤ 1 := by
    rw [hm]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hρpos : 0 < m / 2 := by linarith
  have hρlt1 : m / 2 < 1 := by linarith
  have hρδ₁ : m / 2 < δ₁ := by linarith
  have hρρ₁ : m / 2 < ρ₁ := by linarith
  have hρε : m / 2 < ‖k (1 + ε) - L.γ₁ s₀‖ := by linarith
  have hρε' : m / 2 < ‖k (1 - ε) - L.γ₁ s₀‖ := by linarith
  -- the two points of the circle level on the two sides of `1`
  obtain ⟨tp, ⟨htp_mem, htp_eq⟩, htp_uniq⟩ := (huniq (m / 2) hρpos hρε hρε').1
  obtain ⟨tm, ⟨htm_mem, htm_eq⟩, htm_uniq⟩ := (huniq (m / 2) hρpos hρε hρε').2
  refine ⟨m / 2, hρpos, hρlt1, k (1 + tp), k (1 + tm), fun s hs => ?_⟩
  -- a circle point of the lift: its chart value is a real level at distance `m/2` from `p`
  have hsball : L.γ₁ s ∈ Metric.ball (L.γ₁ s₀) δ₁ := by
    rw [Metric.mem_ball, hs]; exact hρδ₁
  have hkG : k (sideFlipChart c d fl L s₀ (L.γ₁ s)) = L.γ₁ s := hkleft (L.γ₁ s) hsball
  have hGreal : sideFlipChart c d fl L s₀ (L.γ₁ s) = ((L.τ s / L.τ s₀ : ℝ) : ℂ) :=
    sideFlipChart_eq_ofReal (c := c) (d := d) (fl := fl) (L := L) (s₀ := s₀) s
  set t : ℝ := L.τ s / L.τ s₀ - 1 with ht
  have hGt : sideFlipChart c d fl L s₀ (L.γ₁ s) = 1 + (t : ℂ) := by
    rw [hGreal, ht]; push_cast; ring
  have hnear : ‖sideFlipChart c d fl L s₀ (L.γ₁ s) - 1‖ < ε := by
    have h := hρ₁ (show dist (L.γ₁ s) (L.γ₁ s₀) < ρ₁ from by rw [hs]; exact hρρ₁)
    rw [hchartp, dist_eq_norm] at h
    exact h
  have htabs : |t| < ε := by
    have h : ‖(t : ℂ)‖ < ε := by rw [hGt] at hnear; simpa using hnear
    simpa using h
  have htne : t ≠ 0 := by
    intro h0
    have hG1 : sideFlipChart c d fl L s₀ (L.γ₁ s) = 1 := by rw [hGt, h0]; simp
    have hpp : L.γ₁ s = L.γ₁ s₀ := by rw [← hkG, hG1, hk1]
    rw [hpp] at hs
    simp only [dist_self] at hs
    linarith [hρpos]
  have htabs' : -ε < t ∧ t < ε := abs_lt.mp htabs
  have hft : ‖k (1 + t) - L.γ₁ s₀‖ = m / 2 := by
    have h1 : k (1 + t) = L.γ₁ s := by rw [← hkG, hGt]
    rw [h1, ← dist_eq_norm, hs]
  rcases lt_trichotomy t 0 with hlt | heq | hgt
  · right
    rw [← htm_uniq t ⟨⟨htabs'.1, hlt⟩, hft⟩]
    rw [← hkG, hGt]
  · exact absurd heq htne
  · left
    rw [← htp_uniq t ⟨⟨hgt, htabs'.2⟩, hft⟩]
    rw [← hkG, hGt]

/-- **`γ₁` is injective**: a ray point determines its level (`τ` is strictly monotone). -/
theorem gamma_inj (L : RayCylLift d fl) (s₀ : ℝ) : ∀ x y : ℝ, L.γ₁ x = L.γ₁ y → x = y := by
  intro x y hxy
  have hxv : sideFlipChart c d fl L s₀ (L.γ₁ x) = ((L.τ x / L.τ s₀ : ℝ) : ℂ) :=
    sideFlipChart_eq_ofReal (c := c) (d := d) (fl := fl) (L := L) (s₀ := s₀) x
  have hyv : sideFlipChart c d fl L s₀ (L.γ₁ y) = ((L.τ y / L.τ s₀ : ℝ) : ℂ) :=
    sideFlipChart_eq_ofReal (c := c) (d := d) (fl := fl) (L := L) (s₀ := s₀) y
  have h2 : ((L.τ x / L.τ s₀ : ℝ) : ℂ) = ((L.τ y / L.τ s₀ : ℝ) : ℂ) := by
    rw [← hxv, ← hyv, hxy]
  have h3 : L.τ x / L.τ s₀ = L.τ y / L.τ s₀ := Complex.ofReal_injective h2
  have h4 : L.τ s₀ ≠ 0 := by
    have := L.hτ1 s₀; linarith
  have h5 : L.τ x * L.τ s₀ = L.τ y * L.τ s₀ := by
    rw [div_eq_div_iff h4 h4] at h3
    exact h3
  exact L.hτmono.injective (mul_right_cancel₀ h4 h5)

/-- **The portion of the lift inside a ball around one of its points is an arc.**  For a point
`s₀` with `Re (γ₁ s₀) < -L.R` and `ρ > 0` small enough, the preimage of the ball of radius `ρ`
around `p = γ₁ s₀` is exactly an interval `(s₁,s₂)` around `s₀`, and the endpoints are mapped to
the sphere of radius `ρ`. -/
theorem local_arc_portion {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) {x₀ : ℝ} (hx : x₀ < -L.R) {s₀ : ℝ} (hs : (L.γ₁ s₀).re = x₀)
    (hcross : deriv (fun t : ℝ => (L.γ₁ t).re) s₀ ≠ 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ s₁ s₂ : ℝ, s₁ < s₀ ∧ s₀ < s₂ ∧
      (∀ s : ℝ, dist (L.γ₁ s) (L.γ₁ s₀) < ρ → s ∈ Set.Icc s₁ s₂) ∧
      (∀ s ∈ Set.Icc s₁ s₂, s ≠ s₁ → s ≠ s₂ → dist (L.γ₁ s) (L.γ₁ s₀) < ρ) ∧
      dist (L.γ₁ s₁) (L.γ₁ s₀) = ρ ∧ dist (L.γ₁ s₂) (L.γ₁ s₀) = ρ := by
  classical
  have hre : (L.γ₁ s₀).re < -L.R := by rw [hs]; exact hx
  obtain ⟨ρ, hρpos, hρ1, A, B, hAB⟩ := sphere_count L hre
  have htau : ∀ x y : ℝ, L.γ₁ x = L.γ₁ y → x = y := gamma_inj (L := L) s₀
  -- at most two parameters are mapped to the circle
  have htwo : ∀ a b c : ℝ, dist (L.γ₁ a) (L.γ₁ s₀) = ρ → dist (L.γ₁ b) (L.γ₁ s₀) = ρ →
      dist (L.γ₁ c) (L.γ₁ s₀) = ρ → a = b ∨ a = c ∨ b = c := by
    intro a b c ha hb hc
    have ea : L.γ₁ a = A ∨ L.γ₁ a = B := hAB a ha
    have eb : L.γ₁ b = A ∨ L.γ₁ b = B := hAB b hb
    have ec : L.γ₁ c = A ∨ L.γ₁ c = B := hAB c hc
    rcases ea with ea | ea <;> rcases eb with eb | eb <;> rcases ec with ec | ec
    all_goals first
      | exact Or.inl (htau a b (ea.trans eb.symm))
      | exact Or.inr (Or.inl (htau a c (ea.trans ec.symm)))
      | exact Or.inr (Or.inr (htau b c (eb.trans ec.symm)))
  -- the topological core
  have htop : ∃ s₁ s₂ : ℝ, s₁ < s₀ ∧ s₀ < s₂ ∧
      (∀ s : ℝ, dist (L.γ₁ s) (L.γ₁ s₀) < ρ → s ∈ Set.Icc s₁ s₂) ∧
      (∀ s ∈ Set.Icc s₁ s₂, s ≠ s₁ → s ≠ s₂ → dist (L.γ₁ s) (L.γ₁ s₀) < ρ) ∧
      dist (L.γ₁ s₁) (L.γ₁ s₀) = ρ ∧ dist (L.γ₁ s₂) (L.γ₁ s₀) = ρ := by
    exact local_arc_portion_of_rays_aux (γ := L.γ₁) (s₀ := s₀) (ρ := ρ)
      L.cont₁ L.per₁ hρpos hρ1 htwo
  obtain ⟨s₁, s₂, hlt₁, hlt₂, hcond1, hcond2, hdist1, hdist2⟩ := htop
  exact ⟨ρ, hρpos, s₁, s₂, hlt₁, hlt₂, hcond1, hcond2, hdist1, hdist2⟩

end Work.ELRig
