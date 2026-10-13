import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.RegPkgGal.RVocab
import Submission.Work.FTS.RegPkgGal.R7d.exp_ode_const
import Submission.Work.FTS.RegPkgGal.R7d.ode_box_existence
import Submission.Work.FTS.RegPkgGal.R7d.chain_rule_along_curve
import Submission.Work.FTS.RegPkgGal.R7d.Vth_barrier
import Submission.Work.FTS.RegPkgGal.R7d.trajectory_bounds

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open Set Filter
open scoped Topology Real

set_option maxHeartbeats 1600000

namespace Work.FTS.RegPkgGal.R7d


theorem support_strip {S a b c L : ℝ} (hS : 0 < S) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hL : 0 ≤ L)
    {F : ℝ → ℝ → ℝ → ℝ} {Vz Vθ cs : ℝ → ℝ → ℝ → ℝ}
    (hFjoint : ContDiffOn ℝ 1 (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Ioo (0:ℝ) (Real.pi / 2)) (Set.Icc (0:ℝ) S))))
    (hVjoint : ContinuousOn (fun p : ℝ × ℝ × ℝ => (Vz p.1 p.2.1 p.2.2, Vθ p.1 p.2.1 p.2.2))
      (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Icc (0:ℝ) (Real.pi / 2)) (Set.Icc (0:ℝ) S))))
    (hVlipU : ∃ K : NNReal, ∀ τ ∈ Set.Icc 0 S, LipschitzOnWith K
      (fun p : ℝ × ℝ => (Vz p.1 p.2 τ, Vθ p.1 p.2 τ))
      (Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi / 2))))
    (hcscont : ContinuousOn (fun p : ℝ × ℝ × ℝ => cs p.1 p.2.1 p.2.2)
      (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Icc (0:ℝ) (Real.pi / 2)) (Set.Icc (0:ℝ) S))))
    (hEq : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S →
      HasDerivAt (fun s => F z θ s)
        (-(Vz z θ τ * Work.Spaces.Dz (fun z θ => F z θ τ) z θ
          + Vθ z θ τ * Work.Spaces.pth (fun z θ => F z θ τ) z θ
          + cs z θ τ * F z θ τ)) τ)
    (hVz0 : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → 0 ≤ Vz z θ τ)
    (hVza : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → Vz z θ τ ≤ a)
    (hVθb : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → |Vθ z θ τ| ≤ b)
    (hVθ0 : ∀ z τ : ℝ, 0 < z → 0 < τ → τ ≤ S → Vθ z 0 τ = 0)
    (hVθπ : ∀ z τ : ℝ, 0 < z → 0 < τ → τ ≤ S → Vθ z (Real.pi / 2) τ = 0)
    (hcsc : ∀ z θ τ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 → 0 < τ → τ ≤ S → |cs z θ τ| ≤ c)
    (hInit : ∀ z θ : ℝ, L < z → 0 < θ → θ < Real.pi / 2 → F z θ 0 = 0) :
    ∀ τ ∈ Set.Icc 0 S, ∀ z θ : ℝ, L * Real.exp (a * S) < z → 0 < θ → θ < Real.pi / 2 →
      F z θ τ = 0 := by
  intro τ hτ z θ hz hθ0 hθπ
  obtain ⟨hτ0, hτS⟩ := hτ
  have hexp1 : (1:ℝ) ≤ Real.exp (a * S) := Real.one_le_exp (by positivity)
  have hzL : L < z := by nlinarith [hL, hexp1, hz]
  have hzpos : 0 < z := lt_of_le_of_lt (by nlinarith [hL, hexp1]) hz
  rcases eq_or_lt_of_le hτ0 with h0 | hpos
  · rw [← h0]
    exact hInit z θ hzL hθ0 hθπ
  obtain ⟨K, hK⟩ := hVlipU
  have hK0 : (0:ℝ) ≤ (K:ℝ) := K.2
  -- barrier bound for the angular field
  have hbar : ∀ z' θ' τ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → 0 ≤ τ' → τ' ≤ S →
      |Vθ z' θ' τ'| ≤ (K:ℝ) * θ' ∧ |Vθ z' θ' τ'| ≤ (K:ℝ) * (Real.pi / 2 - θ') :=
    Vth_barrier hS hK0 hK hVjoint hVθ0 hVθπ
  -- the a priori box of the trajectory
  set zm : ℝ := z * Real.exp (-(a * τ)) with hzm
  set θm : ℝ := θ * Real.exp (-((K:ℝ) * τ)) with hθm
  set θM : ℝ := Real.pi / 2 - (Real.pi / 2 - θ) * Real.exp (-((K:ℝ) * τ)) with hθM
  have hexpa : Real.exp (-(a * τ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [ha, le_of_lt hpos]
  have hexpK : Real.exp (-((K:ℝ) * τ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; nlinarith [hK0, le_of_lt hpos]
  have hzm_pos : 0 < zm := by rw [hzm]; positivity
  have hθm_pos : 0 < θm := by rw [hθm]; positivity
  have hθM_lt : θM < Real.pi / 2 := by
    rw [hθM]
    have h1 : 0 < (Real.pi / 2 - θ) * Real.exp (-((K:ℝ) * τ)) :=
      mul_pos (by linarith) (Real.exp_pos _)
    linarith
  have hzm_le_z : zm ≤ z := by
    rw [hzm]
    calc z * Real.exp (-(a * τ)) ≤ z * 1 :=
          mul_le_mul_of_nonneg_left hexpa (le_of_lt hzpos)
      _ = z := by ring
  have hθm_le_θ : θm ≤ θ := by
    rw [hθm]
    calc θ * Real.exp (-((K:ℝ) * τ)) ≤ θ * 1 :=
          mul_le_mul_of_nonneg_left hexpK (le_of_lt hθ0)
      _ = θ := by ring
  have hθ_le_θM : θ ≤ θM := by
    rw [hθM]
    have h1 : (Real.pi / 2 - θ) * Real.exp (-((K:ℝ) * τ)) ≤ (Real.pi / 2 - θ) * 1 :=
      mul_le_mul_of_nonneg_left hexpK (by linarith)
    linarith
  have hθm_le_θM : θm ≤ θM := le_trans hθm_le_θ hθ_le_θM
  -- the outer box
  have hzm2 : 0 < zm / 2 := by linarith
  have hθm2 : 0 < θm / 2 := by linarith
  have hθhi_lt : (θM + Real.pi / 2) / 2 < Real.pi / 2 := by linarith
  have hbox_nonempty : zm / 2 ≤ z + 1 := by linarith
  have hθbox_nonempty : θm / 2 ≤ (θM + Real.pi / 2) / 2 := by linarith
  have houter_sub : Set.Icc (zm/2) (z+1) ×ˢ Set.Icc (θm/2) ((θM + Real.pi/2)/2) ⊆
      Set.Ioi (0:ℝ) ×ˢ Set.Ioo (0:ℝ) (Real.pi/2) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
    exact Set.mem_prod.mpr
      ⟨lt_of_lt_of_le hzm2 hp1.1, lt_of_lt_of_le hθm2 hp2.1, lt_of_le_of_lt hp2.2 hθhi_lt⟩
  -- bound at fake time `0`
  have hcont0 : ContinuousOn (fun x : ℝ × ℝ => (Vz x.1 x.2 0, Vθ x.1 x.2 0))
      (Set.Icc (zm/2) (z+1) ×ˢ Set.Icc (θm/2) ((θM + Real.pi/2)/2)) := by
    have hψ : ContinuousOn (fun x : ℝ × ℝ => (x.1, x.2, (0:ℝ)))
        (Set.Icc (zm/2) (z+1) ×ˢ Set.Icc (θm/2) ((θM + Real.pi/2)/2)) := by fun_prop
    have hmap : MapsTo (fun x : ℝ × ℝ => (x.1, x.2, (0:ℝ)))
        (Set.Icc (zm/2) (z+1) ×ˢ Set.Icc (θm/2) ((θM + Real.pi/2)/2))
        (Set.Ioi (0:ℝ) ×ˢ (Set.Icc (0:ℝ) (Real.pi/2) ×ˢ Set.Icc (0:ℝ) S)) := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := Set.mem_prod.mp hx
      exact Set.mem_prod.mpr
        ⟨lt_of_lt_of_le hzm2 hx1.1,
          ⟨le_of_lt (lt_of_lt_of_le hθm2 hx2.1), le_of_lt (lt_of_le_of_lt hx2.2 hθhi_lt)⟩,
          ⟨le_rfl, le_of_lt hS⟩⟩
    simpa [Function.comp_def] using hVjoint.comp hψ hmap
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hcont0
  have hC0 : 0 ≤ C := by
    have hm : (zm/2, θm/2) ∈ Set.Icc (zm/2) (z+1) ×ˢ Set.Icc (θm/2) ((θM + Real.pi/2)/2) :=
      Set.mem_prod.mpr ⟨⟨le_rfl, hbox_nonempty⟩, ⟨le_rfl, hθbox_nonempty⟩⟩
    exact le_trans (norm_nonneg _) (hC _ hm)
  -- the constants for the existence theorem
  set Mvz : ℝ := C + a with hMvz
  set Mvθ : ℝ := C + b with hMvθ
  set Zb : ℝ := zm/2 + (z+1) with hZb
  set Lb : ℝ := Zb * Mvz + Mvθ + 1 with hLb
  set Klip : ℝ := Mvz + Zb * (K:ℝ) + (K:ℝ) + 1 with hKlip
  have hMvz0 : 0 ≤ Mvz := by rw [hMvz]; linarith
  have hMvθ0 : 0 ≤ Mvθ := by rw [hMvθ]; linarith
  have hZb0 : 0 ≤ Zb := by rw [hZb]; linarith
  have hLb0 : 0 < Lb := by rw [hLb]; nlinarith
  have hKlip0 : 0 ≤ Klip := by rw [hKlip]; nlinarith
  -- bounds on the two fields over the outer box
  have hVzb : ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ x ∈ Set.Icc (zm/2) (z+1) ×ˢ Set.Icc (θm/2) ((θM + Real.pi/2)/2),
      |Vz x.1 x.2 σ| ≤ Mvz := by
    intro σ hσ x hx
    obtain ⟨hx1, hx2⟩ := Set.mem_prod.mp hx
    have hx1' : 0 < x.1 := lt_of_lt_of_le hzm2 hx1.1
    have hx2a : 0 < x.2 := lt_of_lt_of_le hθm2 hx2.1
    have hx2b : x.2 < Real.pi / 2 := lt_of_le_of_lt hx2.2 hθhi_lt
    rcases eq_or_lt_of_le hσ.1 with hs | hs
    · rw [← hs, hMvz]
      have h2 := hC x (Set.mem_prod.mpr ⟨hx1, hx2⟩)
      rw [Prod.norm_def] at h2
      have h3 : |Vz x.1 x.2 0| ≤ max |Vz x.1 x.2 0| |Vθ x.1 x.2 0| := le_max_left _ _
      have h4 : max |Vz x.1 x.2 0| |Vθ x.1 x.2 0| ≤ C := by simpa [Real.norm_eq_abs] using h2
      linarith
    · have h1 : Vz x.1 x.2 σ ≤ a := hVza _ _ _ hx1' hx2a hx2b hs hσ.2
      have h2 : 0 ≤ Vz x.1 x.2 σ := hVz0 _ _ _ hx1' hx2a hx2b hs hσ.2
      rw [hMvz]
      rw [abs_le]
      constructor <;> linarith
  have hVθb' : ∀ σ ∈ Set.Icc (0:ℝ) S, ∀ x ∈ Set.Icc (zm/2) (z+1) ×ˢ Set.Icc (θm/2) ((θM + Real.pi/2)/2),
      |Vθ x.1 x.2 σ| ≤ Mvθ := by
    intro σ hσ x hx
    obtain ⟨hx1, hx2⟩ := Set.mem_prod.mp hx
    have hx1' : 0 < x.1 := lt_of_lt_of_le hzm2 hx1.1
    have hx2a : 0 < x.2 := lt_of_lt_of_le hθm2 hx2.1
    have hx2b : x.2 < Real.pi / 2 := lt_of_le_of_lt hx2.2 hθhi_lt
    rcases eq_or_lt_of_le hσ.1 with hs | hs
    · rw [← hs, hMvθ]
      have h2 := hC x (Set.mem_prod.mpr ⟨hx1, hx2⟩)
      rw [Prod.norm_def] at h2
      have h3 : |Vθ x.1 x.2 0| ≤ max |Vz x.1 x.2 0| |Vθ x.1 x.2 0| := le_max_right _ _
      have h4 : max |Vz x.1 x.2 0| |Vθ x.1 x.2 0| ≤ C := by simpa [Real.norm_eq_abs] using h2
      linarith
    · have h1 : |Vθ x.1 x.2 σ| ≤ b := hVθb _ _ _ hx1' hx2a hx2b hs hσ.2
      rw [hMvθ]
      linarith
  -- the data of the existence theorem
  have hx1_le_Zb : ∀ x ∈ Set.Icc (zm/2) (z+1) ×ˢ Set.Icc (θm/2) ((θM + Real.pi/2)/2),
      |x.1| ≤ Zb := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Set.mem_prod.mp hx
    rw [hZb, abs_le]
    constructor <;> linarith [hx1.1, hx1.2]
  have hlipbox : ∀ t ∈ Set.Icc (0:ℝ) τ, LipschitzOnWith ⟨Klip, hKlip0⟩
      (fun x : ℝ × ℝ => (-(x.1 * Vz x.1 x.2 (τ - t)), -(Vθ x.1 x.2 (τ - t))))
      (Set.Icc (zm/2) (z+1) ×ˢ Set.Icc (θm/2) ((θM + Real.pi/2)/2)) := by
    intro t ht
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    obtain ⟨hx1, hx2⟩ := Set.mem_prod.mp hx
    obtain ⟨hy1, hy2⟩ := Set.mem_prod.mp hy
    have hσ : τ - t ∈ Set.Icc (0:ℝ) S := ⟨by linarith [ht.2], by linarith [ht.1, hτS]⟩
    have hxmem : (x.1, x.2) ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      Set.mem_prod.mpr ⟨lt_of_lt_of_le hzm2 hx1.1, lt_of_lt_of_le hθm2 hx2.1,
        lt_of_le_of_lt hx2.2 hθhi_lt⟩
    have hymem : (y.1, y.2) ∈ Set.prod (Set.Ioi (0:ℝ)) (Set.Ioo (0:ℝ) (Real.pi/2)) :=
      Set.mem_prod.mpr ⟨lt_of_lt_of_le hzm2 hy1.1, lt_of_lt_of_le hθm2 hy2.1,
        lt_of_le_of_lt hy2.2 hθhi_lt⟩
    have hLip := hK (τ - t) hσ
    have hVθdiff : |Vθ x.1 x.2 (τ - t) - Vθ y.1 y.2 (τ - t)| ≤ (K:ℝ) * dist x y := by
      have h2 := hLip.dist_le_mul _ hxmem _ hymem
      rw [Prod.dist_eq] at h2
      have h3 : dist (Vθ x.1 x.2 (τ - t)) (Vθ y.1 y.2 (τ - t)) ≤ (K:ℝ) * dist x y :=
        le_trans (le_max_right _ _) h2
      simpa [Real.dist_eq] using h3
    have hVzdiff : |Vz x.1 x.2 (τ - t) - Vz y.1 y.2 (τ - t)| ≤ (K:ℝ) * dist x y := by
      have h2 := hLip.dist_le_mul _ hxmem _ hymem
      rw [Prod.dist_eq] at h2
      have h3 : dist (Vz x.1 x.2 (τ - t)) (Vz y.1 y.2 (τ - t)) ≤ (K:ℝ) * dist x y :=
        le_trans (le_max_left _ _) h2
      simpa [Real.dist_eq] using h3
    have hdist : |x.1 - y.1| ≤ dist x y := by
      rw [Prod.dist_eq, Real.dist_eq]
      exact le_max_left _ _
    have hsecond : dist (-(x.1 * Vz x.1 x.2 (τ - t))) (-(y.1 * Vz y.1 y.2 (τ - t)))
        ≤ Klip * dist x y := by
      have hdecomp : x.1 * Vz x.1 x.2 (τ - t) - y.1 * Vz y.1 y.2 (τ - t)
          = x.1 * (Vz x.1 x.2 (τ - t) - Vz y.1 y.2 (τ - t))
            + (x.1 - y.1) * Vz y.1 y.2 (τ - t) := by ring
      have h1 : |x.1 * Vz x.1 x.2 (τ - t) - y.1 * Vz y.1 y.2 (τ - t)|
          ≤ Zb * ((K:ℝ) * dist x y) + dist x y * Mvz := by
        calc |x.1 * Vz x.1 x.2 (τ - t) - y.1 * Vz y.1 y.2 (τ - t)|
            = |x.1 * (Vz x.1 x.2 (τ - t) - Vz y.1 y.2 (τ - t))
                + (x.1 - y.1) * Vz y.1 y.2 (τ - t)| := by rw [hdecomp]
          _ ≤ |x.1 * (Vz x.1 x.2 (τ - t) - Vz y.1 y.2 (τ - t))|
                + |(x.1 - y.1) * Vz y.1 y.2 (τ - t)| := abs_add_le _ _
          _ = |x.1| * |Vz x.1 x.2 (τ - t) - Vz y.1 y.2 (τ - t)|
                + |x.1 - y.1| * |Vz y.1 y.2 (τ - t)| := by rw [abs_mul, abs_mul]
          _ ≤ Zb * ((K:ℝ) * dist x y) + dist x y * Mvz := by
              have hA : |x.1| * |Vz x.1 x.2 (τ - t) - Vz y.1 y.2 (τ - t)|
                  ≤ Zb * ((K:ℝ) * dist x y) := by
                exact mul_le_mul (hx1_le_Zb x (Set.mem_prod.mpr ⟨hx1, hx2⟩)) hVzdiff
                  (abs_nonneg _) hZb0
              have hB : |x.1 - y.1| * |Vz y.1 y.2 (τ - t)| ≤ dist x y * Mvz := by
                exact mul_le_mul hdist (hVzb _ hσ y (Set.mem_prod.mpr ⟨hy1, hy2⟩))
                  (abs_nonneg _) dist_nonneg
              linarith
      have h2 : dist (-(x.1 * Vz x.1 x.2 (τ - t))) (-(y.1 * Vz y.1 y.2 (τ - t)))
          = |x.1 * Vz x.1 x.2 (τ - t) - y.1 * Vz y.1 y.2 (τ - t)| := by
        rw [Real.dist_eq, abs_sub_comm]
        congr 1
        ring
      rw [h2]
      have h3 : Zb * ((K:ℝ) * dist x y) + dist x y * Mvz
          = (Zb * (K:ℝ) + Mvz) * dist x y := by ring
      rw [h3] at h1
      refine le_trans h1 (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
      rw [hKlip]
      linarith [hMvz0, mul_nonneg hZb0 hK0]
    have hfirst : dist (-(Vθ x.1 x.2 (τ - t))) (-(Vθ y.1 y.2 (τ - t))) ≤ Klip * dist x y := by
      have h2 : dist (-(Vθ x.1 x.2 (τ - t))) (-(Vθ y.1 y.2 (τ - t)))
          = |Vθ x.1 x.2 (τ - t) - Vθ y.1 y.2 (τ - t)| := by
        rw [Real.dist_eq, abs_sub_comm]
        congr 1
        ring
      rw [h2]
      refine le_trans hVθdiff (mul_le_mul_of_nonneg_right ?_ dist_nonneg)
      rw [hKlip]
      linarith [hMvz0, mul_nonneg hZb0 hK0]
    rw [Prod.dist_eq]
    exact max_le hsecond hfirst
  have hbddbox : ∀ t ∈ Set.Icc (0:ℝ) τ, ∀ x ∈ Set.Icc (zm/2) (z+1) ×ˢ Set.Icc (θm/2) ((θM + Real.pi/2)/2),
      ‖(-(x.1 * Vz x.1 x.2 (τ - t)), -(Vθ x.1 x.2 (τ - t)))‖ ≤ Lb := by
    intro t ht x hx
    obtain ⟨hx1, hx2⟩ := Set.mem_prod.mp hx
    have hσ : τ - t ∈ Set.Icc (0:ℝ) S := ⟨by linarith [ht.2], by linarith [ht.1, hτS]⟩
    rw [Prod.norm_def]
    refine max_le ?_ ?_
    · rw [Real.norm_eq_abs, abs_neg, abs_mul]
      calc |x.1| * |Vz x.1 x.2 (τ - t)| ≤ Zb * Mvz :=
            mul_le_mul (hx1_le_Zb x (Set.mem_prod.mpr ⟨hx1, hx2⟩))
              (hVzb _ hσ x (Set.mem_prod.mpr ⟨hx1, hx2⟩)) (abs_nonneg _) hZb0
        _ ≤ Lb := by rw [hLb]; linarith [hMvθ0]
    · rw [Real.norm_eq_abs, abs_neg]
      calc |Vθ x.1 x.2 (τ - t)| ≤ Mvθ := hVθb' _ hσ x (Set.mem_prod.mpr ⟨hx1, hx2⟩)
        _ ≤ Lb := by rw [hLb]; nlinarith [hZb0, hMvz0]
  have htcontbox : ∀ x ∈ Set.Icc (zm/2) (z+1) ×ˢ Set.Icc (θm/2) ((θM + Real.pi/2)/2),
      ContinuousOn (fun t : ℝ => (-(x.1 * Vz x.1 x.2 (τ - t)), -(Vθ x.1 x.2 (τ - t))))
        (Set.Icc (0:ℝ) τ) := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Set.mem_prod.mp hx
    have hx1' : 0 < x.1 := lt_of_lt_of_le hzm2 hx1.1
    have hx2' : 0 < x.2 := lt_of_lt_of_le hθm2 hx2.1
    have hx2'' : x.2 < Real.pi / 2 := lt_of_le_of_lt hx2.2 hθhi_lt
    have hslice : ContinuousOn (fun s : ℝ => (Vz x.1 x.2 s, Vθ x.1 x.2 s)) (Set.Icc (0:ℝ) S) := by
      have hψ : ContinuousOn (fun s : ℝ => (x.1, x.2, s)) (Set.Icc (0:ℝ) S) := by fun_prop
      have hmap : MapsTo (fun s : ℝ => (x.1, x.2, s)) (Set.Icc (0:ℝ) S)
          (Set.Ioi (0:ℝ) ×ˢ (Set.Icc (0:ℝ) (Real.pi/2) ×ˢ Set.Icc (0:ℝ) S)) := by
        intro s hs
        exact Set.mem_prod.mpr ⟨hx1', ⟨le_of_lt hx2', le_of_lt hx2''⟩, hs⟩
      simpa [Function.comp_def] using hVjoint.comp hψ hmap
    have hsub : ContinuousOn (fun t : ℝ => τ - t) (Set.Icc (0:ℝ) τ) := by fun_prop
    have hmap2 : MapsTo (fun t : ℝ => τ - t) (Set.Icc (0:ℝ) τ) (Set.Icc (0:ℝ) S) := by
      intro t ht
      exact ⟨by linarith [ht.2], by linarith [ht.1, hτS]⟩
    have hcomp : ContinuousOn (fun t : ℝ => (Vz x.1 x.2 (τ - t), Vθ x.1 x.2 (τ - t)))
        (Set.Icc (0:ℝ) τ) := hslice.comp hsub hmap2
    have h1 : ContinuousOn (fun t : ℝ => Vz x.1 x.2 (τ - t)) (Set.Icc (0:ℝ) τ) :=
      continuous_fst.comp_continuousOn hcomp
    have h2 : ContinuousOn (fun t : ℝ => Vθ x.1 x.2 (τ - t)) (Set.Icc (0:ℝ) τ) :=
      continuous_snd.comp_continuousOn hcomp
    have h3 : ContinuousOn (fun t : ℝ => x.1 * Vz x.1 x.2 (τ - t)) (Set.Icc (0:ℝ) τ) :=
      continuousOn_const.mul h1
    exact h3.neg.prodMk h2.neg
  -- the a priori estimate
  have htrajg : ∀ T' ∈ Set.Icc (0:ℝ) τ, ∀ α : ℝ → ℝ × ℝ, α 0 = (z, θ) →
      (∀ t ∈ Set.Icc (0:ℝ) T', HasDerivWithinAt α
        (-((α t).1 * Vz (α t).1 (α t).2 (τ - t)), -(Vθ (α t).1 (α t).2 (τ - t)))
        (Set.Icc (0:ℝ) T') t) →
      ∀ t ∈ Set.Icc (0:ℝ) T', (α t).1 ∈ Set.Icc zm z ∧ (α t).2 ∈ Set.Icc θm θM := by
    intro T' hT' α hα0' hode t ht
    have hVθl : ∀ z' θ' τ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → 0 < τ' → τ' ≤ S →
        |Vθ z' θ' τ'| ≤ (K:ℝ) * θ' := fun z' θ' τ' h1 h2 h3 h4 h5 =>
      (hbar z' θ' τ' h1 h2 h3 (le_of_lt h4) h5).1
    have hVθu : ∀ z' θ' τ' : ℝ, 0 < z' → 0 < θ' → θ' < Real.pi / 2 → 0 < τ' → τ' ≤ S →
        |Vθ z' θ' τ'| ≤ (K:ℝ) * (Real.pi / 2 - θ') := fun z' θ' τ' h1 h2 h3 h4 h5 =>
      (hbar z' θ' τ' h1 h2 h3 (le_of_lt h4) h5).2
    have hb : z * Real.exp (-(a * t)) ≤ (α t).1 ∧ (α t).1 ≤ z ∧
        θ * Real.exp (-((K:ℝ) * t)) ≤ (α t).2 ∧
        (α t).2 ≤ Real.pi / 2 - (Real.pi / 2 - θ) * Real.exp (-((K:ℝ) * t)) :=
      trajectory_bounds (Vz := Vz) (Vθ := Vθ) (a := a) (K := (K:ℝ)) (S := S) (τ₀ := τ)
        (T := T') (z₀ := z) (θ₀ := θ) (α := α) hT'.1 hT'.2 hτS hzpos hθ0 hθπ ha hK0 hα0'
        hode hVz0 hVza hVθl hVθu t ht
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
    refine ⟨⟨?_, hb2⟩, ?_, ?_⟩
    · rw [hzm]
      calc z * Real.exp (-(a * τ)) ≤ z * Real.exp (-(a * t)) := by
            refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hzpos)
            have hle : a * t ≤ a * τ :=
              mul_le_mul_of_nonneg_left (le_trans ht.2 hT'.2) ha
            exact Real.exp_le_exp.mpr (neg_le_neg hle)
        _ ≤ (α t).1 := hb1
    · rw [hθm]
      calc θ * Real.exp (-((K:ℝ) * τ)) ≤ θ * Real.exp (-((K:ℝ) * t)) := by
            refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hθ0)
            have hle : (K:ℝ) * t ≤ (K:ℝ) * τ :=
              mul_le_mul_of_nonneg_left (le_trans ht.2 hT'.2) hK0
            exact Real.exp_le_exp.mpr (neg_le_neg hle)
        _ ≤ (α t).2 := hb3
    · rw [hθM]
      have hle : (K:ℝ) * t ≤ (K:ℝ) * τ :=
        mul_le_mul_of_nonneg_left (le_trans ht.2 hT'.2) hK0
      have h5 : Real.exp (-((K:ℝ) * τ)) ≤ Real.exp (-((K:ℝ) * t)) :=
        Real.exp_le_exp.mpr (neg_le_neg hle)
      have h6 : (Real.pi / 2 - θ) * Real.exp (-((K:ℝ) * τ))
          ≤ (Real.pi / 2 - θ) * Real.exp (-((K:ℝ) * t)) :=
        mul_le_mul_of_nonneg_left h5 (by linarith [hθπ])
      have h7 := sub_le_sub_left h6 (Real.pi / 2)
      linarith [hb4, h7]
  -- existence of the trajectory
  have hexists : ∃ α : ℝ → ℝ × ℝ, α 0 = (z, θ) ∧
      ∀ t ∈ Set.Icc (0:ℝ) τ, HasDerivWithinAt α
        (-((α t).1 * Vz (α t).1 (α t).2 (τ - t)), -(Vθ (α t).1 (α t).2 (τ - t)))
        (Set.Icc (0:ℝ) τ) t :=
    ode_box_existence (fun (t : ℝ) (x : ℝ × ℝ) =>
        (-(x.1 * Vz x.1 x.2 (τ - t)), -(Vθ x.1 x.2 (τ - t))))
      (z, θ) (T := τ) (L := Lb) (Klip := Klip)
      (zlo := zm) (zhi := z) (θlo := θm) (θhi := θM)
      (zlo' := zm/2) (zhi' := z+1) (θlo' := θm/2) (θhi' := (θM + Real.pi/2)/2)
      (le_of_lt hpos) hLb0 hKlip0
      ⟨⟨hzm_le_z, le_rfl⟩, hθm_le_θ, hθ_le_θM⟩
      (by linarith) (by linarith) (by linarith) (by linarith)
      hlipbox hbddbox htcontbox htrajg
  obtain ⟨α, hα0', hαode⟩ := hexists
  have hbox : ∀ t ∈ Set.Icc (0:ℝ) τ, (α t).1 ∈ Set.Icc zm z ∧ (α t).2 ∈ Set.Icc θm θM :=
    htrajg τ ⟨le_of_lt hpos, le_rfl⟩ α hα0' hαode
  -- the composite and its exponential-factor equation
  set G : ℝ → ℝ := fun s => F (α s).1 (α s).2 (τ - s) with hG
  set csG : ℝ → ℝ := fun s => cs (α s).1 (α s).2 (τ - s) with hcsG
  have hderiv : ∀ t ∈ Set.Ioo 0 τ, HasDerivAt G (csG t * G t) t := by
    intro t ht
    obtain ⟨hb1, hb2⟩ := hbox t ⟨le_of_lt ht.1, le_of_lt ht.2⟩
    have hz_t : 0 < (α t).1 := lt_of_lt_of_le hzm_pos hb1.1
    have hθ_t : 0 < (α t).2 := lt_of_lt_of_le hθm_pos hb2.1
    have hθ_t' : (α t).2 < Real.pi / 2 := lt_of_le_of_lt hb2.2 hθM_lt
    have hτt : 0 < τ - t := by linarith [ht.2]
    have hτtS : τ - t ≤ S := by linarith [ht.1, hτS]
    have hτtS' : τ - t < S := by linarith [ht.1, hτS]
    have hFd : DifferentiableAt ℝ (fun p : ℝ × ℝ × ℝ => F p.1 p.2.1 p.2.2)
        ((α t).1, (α t).2, τ - t) := by
      have hmem : ((α t).1, (α t).2, τ - t) ∈
          Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Ioo (0:ℝ) (Real.pi/2)) (Set.Icc (0:ℝ) S)) :=
        Set.mem_prod.mpr ⟨hz_t,
          Set.mem_prod.mpr ⟨⟨hθ_t, hθ_t'⟩, ⟨le_of_lt hτt, hτtS⟩⟩⟩
      have hnhds : Set.prod (Set.Ioi (0:ℝ))
          (Set.prod (Set.Ioo (0:ℝ) (Real.pi/2)) (Set.Icc (0:ℝ) S)) ∈
          𝓝 ((α t).1, (α t).2, τ - t) :=
        prod_mem_nhds (isOpen_Ioi.mem_nhds hz_t)
          (prod_mem_nhds (isOpen_Ioo.mem_nhds ⟨hθ_t, hθ_t'⟩) (Icc_mem_nhds hτt hτtS'))
      exact (hFjoint.differentiableOn (by norm_num)).differentiableAt hnhds
    have hEq' : HasDerivAt (fun s => F (α t).1 (α t).2 s)
        (-(Vz (α t).1 (α t).2 (τ - t) * Work.Spaces.Dz (fun z θ => F z θ (τ - t)) (α t).1 (α t).2
          + Vθ (α t).1 (α t).2 (τ - t) * Work.Spaces.pth (fun z θ => F z θ (τ - t)) (α t).1 (α t).2
          + cs (α t).1 (α t).2 (τ - t) * F (α t).1 (α t).2 (τ - t))) (τ - t) :=
      hEq (α t).1 (α t).2 (τ - t) hz_t hθ_t hθ_t' hτt hτtS
    have hα' : HasDerivAt α
        (-((α t).1 * Vz (α t).1 (α t).2 (τ - t)), -(Vθ (α t).1 (α t).2 (τ - t))) t :=
      (hαode t ⟨le_of_lt ht.1, le_of_lt ht.2⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    have hcr := chain_rule_along_curve (Vz := Vz) (Vθ := Vθ) (cs := cs) (α := α) (τ₀ := τ) (t := t)
      hFd hα' hEq'
    simpa [hG, hcsG] using hcr
  have hGcont : ContinuousOn G (Set.Icc (0:ℝ) τ) := by
    have hαcont : ContinuousOn α (Set.Icc (0:ℝ) τ) := fun t ht => (hαode t ht).continuousWithinAt
    have hγ : ContinuousOn (fun s : ℝ => ((α s).1, (α s).2, τ - s)) (Set.Icc (0:ℝ) τ) :=
      ((continuous_fst.comp_continuousOn hαcont).prodMk
        ((continuous_snd.comp_continuousOn hαcont).prodMk
          (continuousOn_const.sub continuousOn_id)))
    have hmap : MapsTo (fun s : ℝ => ((α s).1, (α s).2, τ - s)) (Set.Icc (0:ℝ) τ)
        (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Ioo (0:ℝ) (Real.pi/2)) (Set.Icc (0:ℝ) S))) := by
      intro s hs
      obtain ⟨hb1, hb2⟩ := hbox s hs
      have hz_s : 0 < (α s).1 := lt_of_lt_of_le hzm_pos hb1.1
      have hθ_s : 0 < (α s).2 := lt_of_lt_of_le hθm_pos hb2.1
      have hθ_s' : (α s).2 < Real.pi / 2 := lt_of_le_of_lt hb2.2 hθM_lt
      exact Set.mem_prod.mpr ⟨hz_s, Set.mem_prod.mpr ⟨⟨hθ_s, hθ_s'⟩,
        ⟨by linarith [hs.2], by linarith [hs.1, hτS]⟩⟩⟩
    have := hFjoint.continuousOn.comp hγ hmap
    simpa [hG, Function.comp_def] using this
  have hcsGcont : ContinuousOn csG (Set.Icc (0:ℝ) τ) := by
    have hαcont : ContinuousOn α (Set.Icc (0:ℝ) τ) := fun t ht => (hαode t ht).continuousWithinAt
    have hγ : ContinuousOn (fun s : ℝ => ((α s).1, (α s).2, τ - s)) (Set.Icc (0:ℝ) τ) :=
      ((continuous_fst.comp_continuousOn hαcont).prodMk
        ((continuous_snd.comp_continuousOn hαcont).prodMk
          (continuousOn_const.sub continuousOn_id)))
    have hmap : MapsTo (fun s : ℝ => ((α s).1, (α s).2, τ - s)) (Set.Icc (0:ℝ) τ)
        (Set.prod (Set.Ioi (0:ℝ)) (Set.prod (Set.Icc (0:ℝ) (Real.pi/2)) (Set.Icc (0:ℝ) S))) := by
      intro s hs
      obtain ⟨hb1, hb2⟩ := hbox s hs
      have hz_s : 0 < (α s).1 := lt_of_lt_of_le hzm_pos hb1.1
      have hθ_s : 0 < (α s).2 := lt_of_lt_of_le hθm_pos hb2.1
      have hθ_s' : (α s).2 < Real.pi / 2 := lt_of_le_of_lt hb2.2 hθM_lt
      exact Set.mem_prod.mpr ⟨hz_s, Set.mem_prod.mpr ⟨⟨le_of_lt hθ_s, le_of_lt hθ_s'⟩,
        ⟨by linarith [hs.2], by linarith [hs.1, hτS]⟩⟩⟩
    have := hcscont.comp hγ hmap
    simpa [hcsG, Function.comp_def] using this
  have hGτ : G τ = 0 := by
    obtain ⟨hb1, hb2⟩ := hbox τ ⟨le_of_lt hpos, le_rfl⟩
    have hzτ : L < (α τ).1 := by
      have h1 : z * Real.exp (-(a * τ)) ≤ (α τ).1 := hb1.1
      have h2 : L * Real.exp (a * S) * Real.exp (-(a * τ)) < z * Real.exp (-(a * τ)) :=
        mul_lt_mul_of_pos_right hz (Real.exp_pos _)
      have hexp3 : Real.exp (a * S) * Real.exp (-(a * τ)) = Real.exp (a * (S - τ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have h3 : L * Real.exp (a * S) * Real.exp (-(a * τ)) = L * Real.exp (a * (S - τ)) := by
        rw [mul_assoc, hexp3]
      have h4 : L ≤ L * Real.exp (a * (S - τ)) := by
        have h5 : (1:ℝ) ≤ Real.exp (a * (S - τ)) := Real.one_le_exp (by nlinarith [ha, hτS])
        nlinarith [hL, h5]
      linarith
    have hθτ : 0 < (α τ).2 := lt_of_lt_of_le hθm_pos hb2.1
    have hθτ' : (α τ).2 < Real.pi / 2 := lt_of_le_of_lt hb2.2 hθM_lt
    have hsub : τ - τ = 0 := by ring
    show F (α τ).1 (α τ).2 (τ - τ) = 0
    rw [hsub]
    exact hInit _ _ hzτ hθτ hθτ'
  have hfinal := exp_ode_const hpos hderiv hGcont hcsGcont hGτ
  simpa [hG, hcsG, hα0'] using hfinal

end Work.FTS.RegPkgGal.R7d
