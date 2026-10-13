import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXR1.HJ.HJDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open Filter Set
open scoped Topology

namespace Work.FTS_RegExport.RXR1

/-! ## Elementary facts about `Gs α g = gS α (tauExt g)` near `z = 0` -/

theorem Gs_eq_tauExt {α : ℝ} {g : Work.FTS.Galerkin.Fam} {z θ τ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Gs α g z θ τ = Work.FTS.FinalV2.tauExt g z θ τ := by
  have hθ' : 0 ≤ θ ∧ θ ≤ Real.pi / 2 := hθ
  simp only [Gs, Work.FTS.FinalV2.gS, if_pos hz, if_pos hθ']

theorem Gs_of_nonneg {α : ℝ} {g : Work.FTS.Galerkin.Fam} {z θ τ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) (hτ : 0 ≤ τ) :
    Gs α g z θ τ = g z θ τ := by
  rw [Gs_eq_tauExt hz hθ, Work.FTS.FinalV2.tauExt_of_nonneg g hτ]

theorem Gs_of_neg {α : ℝ} {g : Work.FTS.Galerkin.Fam} {z θ τ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) (hτ : τ < 0) :
    Gs α g z θ τ = g z θ 0 + τ * derivWithin (fun s => g z θ s) (Set.Ici 0) 0 := by
  rw [Gs_eq_tauExt hz hθ, Work.FTS.FinalV2.tauExt_of_neg g hτ]

/-- `gS α (tauExt g)` vanishes identically at the two angular endpoints. -/
theorem Gs_eq_zero_of_ends {α : ℝ} {g : Work.FTS.Galerkin.Fam}
    (hv : ∀ τ : ℝ, 0 ≤ τ → ∀ z : ℝ, 0 ≤ z → g z 0 τ = 0 ∧ g z (Real.pi / 2) τ = 0)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) (hends : θ = 0 ∨ θ = Real.pi / 2) :
    ∀ z τ : ℝ, Gs α g z θ τ = 0 := by
  intro z τ
  have key : ∀ θ₀ : ℝ, (∀ s : ℝ, 0 ≤ s → g z θ₀ s = 0) →
      derivWithin (fun s => g z θ₀ s) (Set.Ici 0) 0 = 0 := by
    intro θ₀ hzero
    have hev : (fun s => g z θ₀ s) =ᶠ[𝓝[Set.Ici 0] 0] fun _ => (0 : ℝ) :=
      eventually_nhdsWithin_of_forall fun s hs => hzero s hs
    rw [Filter.EventuallyEq.derivWithin_eq hev (hzero 0 le_rfl)]
    exact congrFun (derivWithin_const (Set.Ici 0) (0 : ℝ)) 0
  rcases hends with rfl | rfl
  · by_cases hz : 0 < z
    · rw [Gs_eq_tauExt hz hθ]
      by_cases hτ : τ < 0
      · rw [Work.FTS.FinalV2.tauExt_of_neg g hτ,
          key 0 (fun s hs => (hv s hs z hz.le).1), (hv 0 le_rfl z hz.le).1]
        ring
      · rw [Work.FTS.FinalV2.tauExt_of_nonneg g (not_lt.mp hτ)]
        exact (hv τ (not_lt.mp hτ) z hz.le).1
    · simp only [Gs, Work.FTS.FinalV2.gS, if_neg hz]
  · by_cases hz : 0 < z
    · rw [Gs_eq_tauExt hz hθ]
      by_cases hτ : τ < 0
      · rw [Work.FTS.FinalV2.tauExt_of_neg g hτ,
          key (Real.pi / 2) (fun s hs => (hv s hs z hz.le).2), (hv 0 le_rfl z hz.le).2]
        ring
      · rw [Work.FTS.FinalV2.tauExt_of_nonneg g (not_lt.mp hτ)]
        exact (hv τ (not_lt.mp hτ) z hz.le).2
    · simp only [Gs, Work.FTS.FinalV2.gS, if_neg hz]

/-! ## The `τ < 0` branch: `gS α (tauExt g) = datum + τ · RHS` -/

theorem derivWithin_g_eq {α : ℝ} {g : Work.FTS.Galerkin.Fam} {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    derivWithin (fun s => g z θ s) (Set.Ici 0) 0
      = derivWithin (fun s => Gs α g z θ s) (Set.Ici 0) 0 := by
  refine Filter.EventuallyEq.derivWithin_eq ?_ ?_
  · exact eventually_nhdsWithin_of_forall fun s hs => by
      show g z θ s = Gs α g z θ s
      rw [Gs_of_nonneg hz hθ hs]
  · show g z θ 0 = Gs α g z θ 0
    rw [Gs_of_nonneg hz hθ le_rfl]

theorem derivWithin_eq_RHS {αG S : ℝ} {G Φ : Work.FTS.Galerkin.Fam}
    (H : Work.FTS.RegPkgGal.R5Parts αG S G Φ) {θ z : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hz : 0 < z) :
    derivWithin (fun s => G z θ s) (Set.Ici 0) 0 = RHSo αG G Φ z θ := by
  have hq : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ⟩
  have h := (H.h0 z θ hz hq).hasDerivWithinAt.derivWithin (uniqueDiffWithinAt_Ici 0)
  simpa only [RHSo] using h

/-! ## The three cluster limits from three envelope bounds -/

/-- The three cluster limits, from three envelope bounds. -/
theorem hj_triple {G : ℝ → ℝ → ℝ → ℝ} {K Q NZ θ τ₀ : ℝ}
    (hbd1 : ∀ᶠ p : ℝ × ℝ in Filt τ₀, |G p.1 θ p.2| ≤ K * p.1 ^ 2 + NZ * p.1 * |p.2|)
    (hbd2 : ∀ᶠ p : ℝ × ℝ in Filt τ₀, |p.1⁻¹ * G p.1 θ p.2| ≤ K * p.1 + NZ * |p.2|)
    (hbd3 : ∀ᶠ p : ℝ × ℝ in Filt τ₀, |deriv (fun z => G z θ p.2) p.1| ≤ Q * p.1 + NZ * |p.2|)
    (ht1 : Tendsto (fun p : ℝ × ℝ => K * p.1 ^ 2 + NZ * p.1 * |p.2|) (Filt τ₀) (nhds 0))
    (ht2 : Tendsto (fun p : ℝ × ℝ => K * p.1 + NZ * |p.2|) (Filt τ₀) (nhds 0))
    (ht3 : Tendsto (fun p : ℝ × ℝ => Q * p.1 + NZ * |p.2|) (Filt τ₀) (nhds 0)) :
    (Tendsto (fun p : ℝ × ℝ => G p.1 θ p.2) (Filt τ₀) (nhds 0)) ∧
    (Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * G p.1 θ p.2) (Filt τ₀) (nhds 0)) ∧
    (Tendsto (fun p : ℝ × ℝ => deriv (fun z => G z θ p.2) p.1) (Filt τ₀) (nhds 0)) :=
  ⟨squeeze_zero_norm' hbd1 ht1, squeeze_zero_norm' hbd2 ht2, squeeze_zero_norm' hbd3 ht3⟩

/-- The `τ₀ > 0` case: only nonnegative `τ` occur eventually, so the envelopes carry no
`|τ|`-term. -/
theorem hj_triple_pos {G : ℝ → ℝ → ℝ → ℝ} {K Q S θ τ₀ : ℝ} (hτpos : 0 < τ₀)
    (hτS : τ₀ < S + 2)
    (hquadv : ∀ τ ∈ Set.Icc 0 (S + 2), ∀ z ∈ Set.Ioo (0 : ℝ) 2, |G z θ τ| ≤ K * z ^ 2)
    (hquadd : ∀ τ ∈ Set.Icc 0 (S + 2), ∀ z ∈ Set.Ioo (0 : ℝ) 2,
      |deriv (fun z' => G z' θ τ) z| ≤ Q * z) :
    (Tendsto (fun p : ℝ × ℝ => G p.1 θ p.2) (Filt τ₀) (nhds 0)) ∧
    (Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * G p.1 θ p.2) (Filt τ₀) (nhds 0)) ∧
    (Tendsto (fun p : ℝ × ℝ => deriv (fun z => G z θ p.2) p.1) (Filt τ₀) (nhds 0)) := by
  have hzpos : ∀ᶠ p : ℝ × ℝ in Filt τ₀, 0 < p.1 :=
    Filter.mem_of_superset self_mem_nhdsWithin fun p hp => hp.1
  have hlt2 : ∀ᶠ p : ℝ × ℝ in Filt τ₀, p.1 < 2 :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_fst continuous_const).mem_nhds
      (by simp only [Set.mem_setOf_eq]; norm_num))
  have hltS : ∀ᶠ p : ℝ × ℝ in Filt τ₀, p.2 < S + 2 :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_snd continuous_const).mem_nhds
      (by simpa only [Set.mem_setOf_eq] using hτS))
  have hpos : ∀ᶠ p : ℝ × ℝ in Filt τ₀, 0 < p.2 :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_const continuous_snd).mem_nhds hτpos)
  have hfst : Tendsto (fun p : ℝ × ℝ => p.1) (Filt τ₀) (nhds 0) :=
    (continuous_fst.continuousAt (x := ((0 : ℝ), τ₀))).mono_left nhdsWithin_le_nhds
  refine hj_triple (K := K) (Q := Q) (NZ := 0) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hzpos, hlt2, hltS, hpos] with p hp1 hp2 hp3 hp4
    exact le_trans (hquadv p.2 ⟨hp4.le, hp3.le⟩ p.1 ⟨hp1, hp2⟩) (by simp)
  · filter_upwards [hzpos, hlt2, hltS, hpos] with p hp1 hp2 hp3 hp4
    rw [abs_mul, abs_of_pos (inv_pos.mpr hp1)]
    calc p.1⁻¹ * |G p.1 θ p.2| ≤ p.1⁻¹ * (K * p.1 ^ 2) :=
          mul_le_mul_of_nonneg_left (hquadv p.2 ⟨hp4.le, hp3.le⟩ p.1 ⟨hp1, hp2⟩)
            (le_of_lt (inv_pos.mpr hp1))
      _ = K * p.1 := by
          have hne : p.1 ≠ 0 := ne_of_gt hp1
          field_simp
      _ ≤ K * p.1 + 0 * |p.2| := by simp
  · filter_upwards [hzpos, hlt2, hltS, hpos] with p hp1 hp2 hp3 hp4
    exact le_trans (hquadd p.2 ⟨hp4.le, hp3.le⟩ p.1 ⟨hp1, hp2⟩) (by simp)
  · have h1 : Tendsto (fun p : ℝ × ℝ => K * p.1 ^ 2) (Filt τ₀) (nhds 0) := by
      simpa using (hfst.pow 2).const_mul K
    simpa using h1
  · have h1 : Tendsto (fun p : ℝ × ℝ => K * p.1) (Filt τ₀) (nhds 0) := by
      simpa using hfst.const_mul K
    simpa using h1
  · have h1 : Tendsto (fun p : ℝ × ℝ => Q * p.1) (Filt τ₀) (nhds 0) := by
      simpa using hfst.const_mul Q
    simpa using h1

/-- The `τ₀ = 0` case: the `τ < 0` branch is live and contributes the `|τ|`-terms. -/
theorem hj_triple_zero {G : ℝ → ℝ → ℝ → ℝ} {R : ℝ → ℝ → ℝ} {gd : ℝ → ℝ} {K Q NZ S θ : ℝ}
    (hK : 0 ≤ K) (hNZ : 0 ≤ NZ) (hS2 : 0 < S + 2)
    (hdat0 : ∀ z ∈ Set.Ioo (0 : ℝ) 2, |gd z| ≤ K * z ^ 2)
    (hquadv : ∀ τ ∈ Set.Icc 0 (S + 2), ∀ z ∈ Set.Ioo (0 : ℝ) 2, |G z θ τ| ≤ K * z ^ 2)
    (hquadd : ∀ τ ∈ Set.Icc 0 (S + 2), ∀ z ∈ Set.Ioo (0 : ℝ) 2,
      |deriv (fun z' => G z' θ τ) z| ≤ Q * z)
    (hneg : ∀ z ∈ Set.Ioo (0 : ℝ) 2, ∀ τ < 0, G z θ τ = gd z + τ * R z θ)
    (hRbd : ∀ z ∈ Set.Ioo (0 : ℝ) 2, |R z θ| ≤ NZ * z)
    (hRder : ∀ z ∈ Set.Ioo (0 : ℝ) 2,
      ∃ d : ℝ, HasDerivAt (fun z' => R z' θ) d z ∧ |d| ≤ NZ)
    (hA : ∀ z ∈ Set.Ioo (0 : ℝ) 2,
      ∃ A : ℝ, HasDerivAt gd A z ∧ |A| ≤ Q * z) :
    (Tendsto (fun p : ℝ × ℝ => G p.1 θ p.2) (Filt 0) (nhds 0)) ∧
    (Tendsto (fun p : ℝ × ℝ => p.1⁻¹ * G p.1 θ p.2) (Filt 0) (nhds 0)) ∧
    (Tendsto (fun p : ℝ × ℝ => deriv (fun z => G z θ p.2) p.1) (Filt 0) (nhds 0)) := by
  have hzpos : ∀ᶠ p : ℝ × ℝ in Filt 0, 0 < p.1 :=
    Filter.mem_of_superset self_mem_nhdsWithin fun p hp => hp.1
  have hlt2 : ∀ᶠ p : ℝ × ℝ in Filt 0, p.1 < 2 :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_fst continuous_const).mem_nhds
      (by simp only [Set.mem_setOf_eq]; norm_num))
  have hltS : ∀ᶠ p : ℝ × ℝ in Filt 0, p.2 < S + 2 :=
    nhdsWithin_le_nhds ((isOpen_lt continuous_snd continuous_const).mem_nhds
      (by simpa only [Set.mem_setOf_eq] using hS2))
  have hfst : Tendsto (fun p : ℝ × ℝ => p.1) (Filt 0) (nhds 0) :=
    (continuous_fst.continuousAt (x := ((0 : ℝ), (0 : ℝ)))).mono_left nhdsWithin_le_nhds
  have hsnd0 : Tendsto (fun p : ℝ × ℝ => p.2) (Filt 0) (nhds 0) :=
    (continuous_snd.continuousAt (x := ((0 : ℝ), (0 : ℝ)))).mono_left nhdsWithin_le_nhds
  have hkey : ∀ p : ℝ × ℝ, 0 < p.1 → p.1 < 2 → p.2 < S + 2 →
      |G p.1 θ p.2| ≤ K * p.1 ^ 2 + NZ * p.1 * |p.2| := by
    intro p hp1 hp2 hp3
    rcases lt_or_ge p.2 0 with hτ | hτ
    · rw [hneg p.1 ⟨hp1, hp2⟩ p.2 hτ]
      calc |gd p.1 + p.2 * R p.1 θ| ≤ |gd p.1| + |p.2 * R p.1 θ| := abs_add_le _ _
        _ ≤ K * p.1 ^ 2 + |p.2| * (NZ * p.1) := by
            gcongr
            · exact hdat0 p.1 ⟨hp1, hp2⟩
            · rw [abs_mul]
              exact mul_le_mul_of_nonneg_left (hRbd p.1 ⟨hp1, hp2⟩) (abs_nonneg _)
        _ = K * p.1 ^ 2 + NZ * p.1 * |p.2| := by ring
    · have h := hquadv p.2 ⟨hτ, hp3.le⟩ p.1 ⟨hp1, hp2⟩
      have h2 : 0 ≤ NZ * p.1 * |p.2| := by positivity
      linarith
  refine hj_triple (K := K) (Q := Q) (NZ := NZ) ?_ ?_ ?_ ?_ ?_ ?_
  · filter_upwards [hzpos, hlt2, hltS] with p hp1 hp2 hp3
    exact hkey p hp1 hp2 hp3
  · filter_upwards [hzpos, hlt2, hltS] with p hp1 hp2 hp3
    rw [abs_mul, abs_of_pos (inv_pos.mpr hp1)]
    calc p.1⁻¹ * |G p.1 θ p.2|
        ≤ p.1⁻¹ * (K * p.1 ^ 2 + NZ * p.1 * |p.2|) :=
          mul_le_mul_of_nonneg_left (hkey p hp1 hp2 hp3) (le_of_lt (inv_pos.mpr hp1))
      _ = K * p.1 + NZ * |p.2| := by
          have hne : p.1 ≠ 0 := ne_of_gt hp1
          field_simp
  · filter_upwards [hzpos, hlt2, hltS] with p hp1 hp2 hp3
    rcases lt_or_ge p.2 0 with hτ | hτ
    · have hev : (fun z => G z θ p.2) =ᶠ[𝓝 p.1] (fun z => gd z + p.2 * R z θ) := by
        filter_upwards [isOpen_Ioo.mem_nhds ⟨hp1, hp2⟩] with z hz
        exact hneg z hz p.2 hτ
      rw [Filter.EventuallyEq.deriv_eq hev]
      obtain ⟨A, hAd, hAb⟩ := hA p.1 ⟨hp1, hp2⟩
      obtain ⟨d, hd, hdb⟩ := hRder p.1 ⟨hp1, hp2⟩
      have hsum : HasDerivAt (fun z => gd z + p.2 * R z θ) (A + p.2 * d) p.1 :=
        hAd.add (hd.const_mul p.2)
      rw [hsum.deriv]
      calc |A + p.2 * d| ≤ |A| + |p.2 * d| := abs_add_le _ _
        _ ≤ Q * p.1 + |p.2| * NZ := by
            gcongr
            rw [abs_mul]
            exact mul_le_mul_of_nonneg_left hdb (abs_nonneg _)
        _ = Q * p.1 + NZ * |p.2| := by ring
    · have h := hquadd p.2 ⟨hτ, hp3.le⟩ p.1 ⟨hp1, hp2⟩
      have h2 : 0 ≤ NZ * |p.2| := by positivity
      linarith
  · have h1 : Tendsto (fun p : ℝ × ℝ => K * p.1 ^ 2) (Filt 0) (nhds 0) := by
      simpa using (hfst.pow 2).const_mul K
    have h2 : Tendsto (fun p : ℝ × ℝ => NZ * p.1 * |p.2|) (Filt 0) (nhds 0) := by
      have h := (hfst.mul hsnd0.abs).const_mul NZ
      simpa only [mul_assoc, abs_zero, mul_zero] using h
    simpa using h1.add h2
  · have h1 : Tendsto (fun p : ℝ × ℝ => K * p.1) (Filt 0) (nhds 0) := by
      simpa using hfst.const_mul K
    have h2 : Tendsto (fun p : ℝ × ℝ => NZ * |p.2|) (Filt 0) (nhds 0) := by
      simpa using hsnd0.abs.const_mul NZ
    simpa using h1.add h2
  · have h1 : Tendsto (fun p : ℝ × ℝ => Q * p.1) (Filt 0) (nhds 0) := by
      simpa using hfst.const_mul Q
    have h2 : Tendsto (fun p : ℝ × ℝ => NZ * |p.2|) (Filt 0) (nhds 0) := by
      simpa using hsnd0.abs.const_mul NZ
    simpa using h1.add h2

end Work.FTS_RegExport.RXR1
