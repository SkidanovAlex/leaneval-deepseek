/-
# Auxiliary facts for the conjugate pair of dynamic rays of a real parameter

This module collects the elementary facts about the *conjugate* pair of dynamical rays
`(R_θ, R_{−θ})` of the tricorn `T_c` for a **real** parameter `c` and a **real** landing point,
which are used by `Work.LandLeaves.rayArg_separated_conj_ofReal`:

* the Böttcher coordinate commutes with complex conjugation (`dynPhi_conj_ofReal`), hence
  `rayPt hN (−θ) t = conj (rayPt hN θ t)` (`rayPt_conj`);
* a level point of the ray of `θ` is never real (`rayPt_notMem_range_ofReal`), whence its
  argument is never a multiple of `π` (`arg_ne_pi_mul`);
* the two turning numbers of `w` and `conj w` differ by twice the turning number of `w`
  (`arg_sub_arg_conj`);
* quantitative separation of the arguments in a *compact* range of levels
  (`rayArg_mid_separated`) and for *large* levels (`rayArg_large_separated`).

The remaining, deep, input -- the separation near the landing level `t = 1⁺` -- is the content
of `Work.LandLeaves.rayArg_near_one_separated`.
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.landsN_iff_landsAt
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.rayAccum_entry
import Submission.Work.LandLeaves.rayPt_tail_small
import Submission.Work.ParamRays.isDynBottcher_unique
import Submission.Work.ELTop.paramRay_disjoint
import Submission.Work.LandLeaves.rayPt_iterate_angDouble
import Submission.Work.LandLeaves.exists_int_arg_close

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter
open scoped Topology

namespace Work.LandLeaves

open LeanEval.ComplexAnalysis (Tantibar)

/-! ## Conjugation symmetry -/

theorem Tantibar_conj_ofReal (r : ℝ) (z : ℂ) :
    Tantibar (r : ℂ) ((starRingEnd ℂ) z) = (starRingEnd ℂ) (Tantibar (r : ℂ) z) := by
  rw [Tantibar, Tantibar, map_add, map_pow, Complex.conj_conj, Complex.conj_ofReal]

theorem escaping_conj_ofReal {r : ℝ} {z : ℂ} :
    Work.ParamRays.Escaping (r : ℂ) ((starRingEnd ℂ) z) ↔ Work.ParamRays.Escaping (r : ℂ) z := by
  have h := Work.ParamRays.escaping_conj_conj (c := (r : ℂ)) (w := z)
  rw [Complex.conj_ofReal] at h
  exact h.symm

theorem isDynBottcher_conj_ofReal {r : ℝ} {φ : ℂ → ℂ}
    (hφ : Work.ParamRays.IsDynBottcher (r : ℂ) φ) :
    Work.ParamRays.IsDynBottcher (r : ℂ) (fun z => (starRingEnd ℂ) (φ ((starRingEnd ℂ) z))) := by
  set S := Work.ParamRays.escapingSet (r : ℂ) with hS
  have hmaps : Set.MapsTo (starRingEnd ℂ) S S := fun z hz => escaping_conj_ofReal.mpr hz
  refine ⟨?_, ?_, ?_⟩
  · have h1 : ContinuousOn (fun z => φ ((starRingEnd ℂ) z)) S :=
      ContinuousOn.comp hφ.1 Complex.continuous_conj.continuousOn hmaps
    exact ContinuousOn.comp Complex.continuous_conj.continuousOn h1 (fun z _ => Set.mem_univ _)
  · intro z hz
    have hzc : Work.ParamRays.Escaping (r : ℂ) ((starRingEnd ℂ) z) := escaping_conj_ofReal.mpr hz
    show (starRingEnd ℂ) (φ ((starRingEnd ℂ) (Tantibar (r:ℂ) z)))
        = (starRingEnd ℂ) ((starRingEnd ℂ) (φ ((starRingEnd ℂ) z))) ^ 2
    rw [← Tantibar_conj_ofReal, hφ.2.1 ((starRingEnd ℂ) z) hzc]
    simp
  · intro ε hε
    obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.mp (hφ.2.2 ε hε)
    refine Filter.mem_cocompact.mpr ⟨(starRingEnd ℂ) '' K, hK.image Complex.continuous_conj, ?_⟩
    rintro z hz
    have hz' : (starRingEnd ℂ) z ∉ K := by
      intro hmem
      exact hz ⟨(starRingEnd ℂ) z, hmem, by simp⟩
    have h := hKs hz'
    simp only [Set.mem_ofPred_eq] at h ⊢
    have h2 : (starRingEnd ℂ) (φ ((starRingEnd ℂ) z)) - z
        = (starRingEnd ℂ) (φ ((starRingEnd ℂ) z) - (starRingEnd ℂ) z) := by
      rw [map_sub, Complex.conj_conj]
    rw [h2, Complex.norm_conj]
    simpa [Complex.norm_conj] using h

theorem phi_conj_ofReal {r : ℝ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher (r : ℂ) φ)
    {z : ℂ} (hz : Work.ParamRays.Escaping (r : ℂ) z) :
    φ ((starRingEnd ℂ) z) = (starRingEnd ℂ) (φ z) := by
  have h2 : Work.ParamRays.IsDynBottcher (r : ℂ)
      (fun w => (starRingEnd ℂ) (φ ((starRingEnd ℂ) w))) := isDynBottcher_conj_ofReal hφ
  have h3 := Work.ParamRays.isDynBottcher_unique hφ h2 hz
  have h4 := congrArg (starRingEnd ℂ) h3
  simpa using h4.symm

theorem mem_K_iff_not_escaping_ofReal {r : ℝ} (w : ℂ) :
    w ∈ Work.EL.K (r : ℂ) ↔ ¬ Work.ParamRays.Escaping (r : ℂ) w := by
  have h := Work.ELTop.escaping_iff_notMem_K (r : ℂ) w
  constructor
  · intro hw hesc; exact h.mp hesc hw
  · intro hw; by_contra hK; exact hw (h.mpr hK)

theorem conj_mem_K_ofReal {r : ℝ} {z : ℂ} :
    (starRingEnd ℂ) z ∈ Work.EL.K (r : ℂ) ↔ z ∈ Work.EL.K (r : ℂ) := by
  rw [mem_K_iff_not_escaping_ofReal, mem_K_iff_not_escaping_ofReal, escaping_conj_ofReal]

theorem dynPhi_conj_ofReal {r : ℝ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher (r : ℂ) φ)
    (z : ℂ) :
    Work.EL.dynPhi (r : ℂ) φ ((starRingEnd ℂ) z)
      = (starRingEnd ℂ) (Work.EL.dynPhi (r : ℂ) φ z) := by
  by_cases hz : z ∈ Work.EL.K (r : ℂ)
  · rw [Work.EL.dynPhi_of_mem (conj_mem_K_ofReal.mpr hz), Work.EL.dynPhi_of_mem hz, map_zero]
  · rw [Work.EL.dynPhi_of_notMem (fun h => hz (conj_mem_K_ofReal.mp h)),
      Work.EL.dynPhi_of_notMem hz]
    have hesc : Work.ParamRays.Escaping (r : ℂ) z := (Work.ELTop.escaping_iff_notMem_K (r:ℂ) z).mpr hz
    exact phi_conj_ofReal hφ hesc

theorem rayPoint_conj (u t : ℝ) :
    Work.Top.NakaneData.rayPoint (-u) t = (starRingEnd ℂ) (Work.Top.NakaneData.rayPoint u t) := by
  have hw : ((2 : ℂ) * (Real.pi : ℂ) * ((-u : ℝ) : ℂ) * Complex.I)
      = (starRingEnd ℂ) ((2 : ℂ) * (Real.pi : ℂ) * ((u : ℝ) : ℂ) * Complex.I) := by
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.conj_ofNat]
    push_cast
    ring
  rw [Work.Top.NakaneData.rayPoint, Work.Top.NakaneData.rayPoint, map_mul, Complex.conj_ofReal,
    ← Complex.exp_conj, hw]

/-- **For real parameters the rays of conjugate angles are mirror images.** -/
theorem rayPt_conj {r : ℝ} {φ : ℂ → ℂ} (hφ : Work.ParamRays.IsDynBottcher (r : ℂ) φ)
    {hN : Work.EL.DynB (r : ℂ) φ} {u t : ℝ} (ht : 1 < t) :
    Work.EL.rayPt hN (-u) t = (starRingEnd ℂ) (Work.EL.rayPt hN u t) := by
  have h1 : Work.EL.rayPt hN (-u) t ∉ Work.EL.K (r : ℂ) := Work.EL.rayPt_notMem_K hN ht
  have h2 : (starRingEnd ℂ) (Work.EL.rayPt hN u t) ∉ Work.EL.K (r : ℂ) := by
    intro hmem
    exact Work.EL.rayPt_notMem_K hN ht (conj_mem_K_ofReal.mp hmem)
  refine Work.Top.NakaneData.injOn_Phi hN h1 h2 ?_
  rw [Work.Top.NakaneData.Phi_rayPt hN ht, dynPhi_conj_ofReal hφ,
    Work.Top.NakaneData.Phi_rayPt hN ht, rayPoint_conj]

/-! ## The conjugate pair never meets the real axis -/

/-- **A point of a ray of a conjugate pair of angles is never real.** -/
theorem rayPt_notMem_range_ofReal {r : ℝ} {φ : ℂ → ℂ}
    (hφ : Work.ParamRays.IsDynBottcher (r : ℂ) φ) (hN : Work.EL.DynB (r : ℂ) φ)
    {θ : ℝ} (hne : ∀ m : ℤ, θ ≠ -θ + m) {t : ℝ} (ht : 1 < t) :
    Work.EL.rayPt hN θ t ∉ Set.range ((↑) : ℝ → ℂ) := by
  intro hmem
  obtain ⟨s, hs⟩ := hmem
  have hconj : (starRingEnd ℂ) (Work.EL.rayPt hN θ t) = Work.EL.rayPt hN θ t := by
    rw [← hs, Complex.conj_ofReal]
  have hdisj : Disjoint (Work.EL.paramRay hN θ) (Work.EL.paramRay hN (-θ)) := by
    refine Work.ELTop.paramRay_disjoint hN ?_
    intro k hk
    exact hne (-k) (by push_cast at hk ⊢; linarith)
  have hmem1 : Work.EL.rayPt hN θ t ∈ Work.EL.paramRay hN θ :=
    ⟨Work.EL.rayPt_notMem_K hN ht, t, ht, Work.Top.NakaneData.Phi_rayPt hN ht⟩
  have hmem2 : Work.EL.rayPt hN θ t ∈ Work.EL.paramRay hN (-θ) := by
    rw [Work.Top.NakaneData.mem_paramRay_iff]
    refine ⟨Work.EL.rayPt_notMem_K hN ht, t, ht, ?_⟩
    rw [← hconj]
    rw [dynPhi_conj_ofReal hφ]
    rw [Work.Top.NakaneData.Phi_rayPt hN ht]
    rw [← rayPoint_conj θ t]
  exact Set.disjoint_left.mp hdisj hmem1 hmem2

/-- A non-real complex number has argument different from `π * m` for every integer `m`. -/
theorem arg_ne_pi_mul {w : ℂ} (hw : w ∉ Set.range ((↑) : ℝ → ℂ)) (m : ℤ) :
    Complex.arg w ≠ (m : ℝ) * Real.pi := by
  intro h
  apply hw
  rcases lt_trichotomy m 0 with hm | hm | hm
  · exfalso
    have h1 : (m : ℝ) ≤ -1 := by exact_mod_cast (show m ≤ -1 by omega)
    have h2 : -Real.pi < (m : ℝ) * Real.pi := by rw [← h]; exact Complex.neg_pi_lt_arg w
    nlinarith [Real.pi_pos]
  · subst hm
    have h0 : Complex.arg w = 0 := by simpa using h
    refine ⟨‖w‖, ?_⟩
    have h1 := Complex.norm_mul_exp_arg_mul_I w
    rw [h0] at h1
    simp at h1
    rw [← h1]; simp
  · rcases eq_or_lt_of_le (show 1 ≤ m by omega) with hm1 | hm2
    · subst hm1
      have hpi : Complex.arg w = Real.pi := by simpa using h
      have hh := Complex.arg_eq_pi_iff.mp hpi
      refine ⟨w.re, ?_⟩
      apply Complex.ext <;> simp [hh.2]
    · exfalso
      have h2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm2
      have h3 : Complex.arg w ≤ Real.pi := Complex.arg_le_pi w
      rw [h] at h3
      nlinarith [Real.pi_pos]

theorem conj_eq_self_ofReal {y : ℂ} (hy : ∃ s : ℝ, y = (s : ℂ)) :
    (starRingEnd ℂ) y = y := by
  obtain ⟨s, rfl⟩ := hy
  simp

/-- A real complex number is the image of its real part. -/
theorem eq_ofReal_re_of_conj {y : ℂ} (hy : (starRingEnd ℂ) y = y) :
    y = ((y.re : ℝ) : ℂ) := by
  have him : y.im = 0 := by
    have h := congrArg Complex.im hy
    simp only [Complex.conj_im] at h
    linarith
  apply Complex.ext <;> simp [him]

/-- The difference of the two turning numbers of `w` and `conj w` is twice that of `w`. -/
theorem arg_sub_arg_conj {w : ℂ} (hw : w ∉ Set.range ((↑) : ℝ → ℂ)) (m : ℤ) :
    Complex.arg w / (2 * Real.pi) - Complex.arg ((starRingEnd ℂ) w) / (2 * Real.pi) - (m : ℝ)
      = Complex.arg w / Real.pi - (m : ℝ) := by
  have harg : Complex.arg w ≠ Real.pi := by
    intro hpi
    have hh := Complex.arg_eq_pi_iff.mp hpi
    refine hw ⟨w.re, ?_⟩
    apply Complex.ext <;> simp [hh.2]
  rw [Complex.arg_conj, ite_eq_right (by simpa using harg)]
  have hsub : Complex.arg w / (2 * Real.pi) - (-Complex.arg w) / (2 * Real.pi)
      = 2 * Complex.arg w / (2 * Real.pi) := by ring
  rw [hsub]
  field_simp

/-! ## A quantitative gap around a non-integer -/

/-- A real number which is not an integer has a positive distance to the integers. -/
theorem exists_gap {x : ℝ} (hx : ∀ n : ℤ, x ≠ (n : ℝ)) :
    ∃ d : ℝ, 0 < d ∧ ∀ n : ℤ, d ≤ |x - (n : ℝ)| := by
  set k : ℤ := ⌊x⌋ with hk
  have h1 : (k : ℝ) ≤ x := Int.floor_le x
  have h2 : x < (k : ℝ) + 1 := Int.lt_floor_add_one x
  have hne0 : x - (k : ℝ) ≠ 0 := by
    intro h0
    exact hx k (by linarith)
  have hpos : 0 < x - (k : ℝ) := lt_of_le_of_ne (by linarith) (Ne.symm hne0)
  refine ⟨min (x - (k : ℝ)) (1 - (x - (k : ℝ))), lt_min hpos (by linarith), fun n => ?_⟩
  rcases le_or_gt n k with hn | hn
  · have h3 : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hn
    rw [abs_of_nonneg (by linarith)]
    exact le_trans (min_le_left _ _) (by linarith)
  · have h3 : (k : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast (show k + 1 ≤ n by omega)
    rw [abs_of_nonpos (by linarith)]
    exact le_trans (min_le_right _ _) (by linarith)

end Work.LandLeaves
