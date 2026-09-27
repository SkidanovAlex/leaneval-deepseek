import Mathlib
import Submission.Work.Drive.T6GenAtD
import Submission.Work.Drive.regBaseAssembly
import Submission.Work.Drive.pairOneData_of_T6GenAt
import Submission.Work.Drive.transportT6Sharp
import Submission.Work.Drive.collarZeroInterior
import Submission.Work.Drive.ppDesignInputs
import Submission.Work.Drive.ppParity.htube_of_strip
import Submission.Work.Drive.colCollar_exists
import Submission.Work.Drive.exists_chartPert
import Submission.Work.Drive.contMDiff_chartedChain

/-!
# The per-block transport wrapper, **with the level band** of the first sweep

`Drive/blockT6Wrapper.lean` (H4) states the per-block wrapper
`Work.Drive.odd_topBdryMeet_zero_iff_of_T6GenAtDBox_meet3Hyp` with the hypotheses

    hQ, hQseam, hP₁, hP₂, hP₁seam, hP₂seam, hdisj₁, hdisj₂, hdisj₁₂, hlev : (∀ z, ‖z‖ ≤ 1 → levelOf (Q z) ≠ c₂),
    hM : Meet3Hyp (triple of clamped sweeps), hgen : T6GenAtDBox Q P₁ P₂ c₁ c₂.

This statement is **one level band and one positivity short** (see
`WALL_NODES_H3_STATUS.md` §5): the avoidances `ftY2 x ≠ 0` that `Work.Drive.htube_of_strip` consumes
come from `Work.Drive.ppMeet_face_avoidances`, whose hypotheses are exactly

* `hc₁ : 0 < c₁`, `hc₂ : 0 < c₂`,
* `hlev₁ : ∀ z, ‖z‖ ≤ 1 → c₁ < levelOf (Q z)`,
* `hlev₂ : ∀ z, ‖z‖ ≤ 1 → c₂ < levelOf (Q z)`,
* the two range disjointnesses (implied by `hdisj₁`, `hdisj₂`, since `‖sqDisk (foldBox u)‖ ≤ 1`).

`hlev` (the `≠ c₂` form) excludes `ftZ2 x = 0`; the top faces `ftY2 x = 1`, `ftZ2 x = 1` are excluded by
`hdisj₁`, `hdisj₂`; but the bottom face `ftY2 x = 0` puts the meet at level exactly `c₁` on the
collapsed plane's side, whose argument `colMap β 1 (sqDisk (foldBox u))` has norm `≤ 1`
(`Work.Drive.norm_colMap_le_one`), so it is excluded by `hlev₁` — which the current statement does not
have.  In the design `cblk = ![c/2, c/3, c/4]` sits *below* the chart disk's levels and the perturbation
*raises* the levels, so `hlev₁`/`hc₁` are free there.

The statement below is the corrected one, with the *same* conclusion.  It is stated here (rather than
edited into H4's file) because the `ChartedSpace`/`IsManifold` instances of `CappingSpace` are `local
instance`s of this namespace, and because H4 owns that file.

## The route (all pieces proved; this is assembly)

1. `obtain ⟨δc, hδc, hδcut⟩` from `hgen.1.2.2` (`Work.Drive.T6GenAt`'s third conjunct); then
   `Work.Drive.colCollar_exists δc hδc` gives `β : ℝ → ℝ` with `ContDiff β`, `0 < β`, `√t ≤ β t`,
   `δc² ≤ t → β t = √t` (i.e. `hβδ`) and **`β 1 = 1`** (the `hβ1` of `collarInterior_one`).
2. `hcore := hgen.1.1`, `hdiam := hgen.2` (up to the `T6GenAtDBox` unfolding).
3. `hregBase` from `Work.Drive.hregBase_design_chains` (`regBaseAssembly.lean`, **proved**) with
   `hD3 := hM`, its four identifications discharged by `colPlane_zero`, `clampedSweep_face_one`,
   `mk2_mk3` (the same three lines as in `hregBase_design_chains`'s own callers), and
   `hint` / `hpair` from
   * `ftS x = 0`: `Work.Drive.collarInterior_zero_of_meet3Hyp` (proved);
   * `ftS x = 1`: `Work.Drive.collarInterior_and_pairOneData_of_T6GenAt`
     (`pairOneData_of_T6GenAt.lean`, **proved** — it needs `hQ`, `hQseam`, `hβ1`, `hδc`, `hβδ`,
     `hδcut`, `hcore`, `hdiam`, `hM`, and nothing else from this list).
4. `hY`/`hZ`: `Work.Drive.ppMeet_face_avoidances` (`ppDesignInputs.lean`, **proved**) with `hc₁`,
   `hc₂`, `hlev₁`, `hlev₂`, the two range disjointnesses (from `hdisj₁`, `hdisj₂`).
5. `htube`: `Work.Drive.htube_of_strip` (**proved**) with `Ξ := chartPert`, `w` a bump which is `≠ 0`
   on `(δ, 1-δ)` and `0` outside a slightly larger strip (`Real.smoothTransition`), `K := unitBox 8`.
6. `hfin`, `hbase` from `hgen.1.1`'s `GoodLoopChain` (`hfin` is its finiteness clause and `hbase` its
   interiority clause at `x 1 = 1`); `hfind` from `Work.Drive.hfind_of_T6GenAt`; `ht5` from
   `Work.Drive.odd_ncard_diamMeet_iff_coreSideCount_clampedSweep` (proved) applied to `hgen.2`.
7. Conclude with
   `Work.Drive.odd_topBdryMeet_zero_iff_coreSideCount_mul_of_design_intrinsic_nf`
   (`transportT6Sharp.lean`, **proved**).
-/

namespace Work.Drive

open Manifold Set Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The per-block transport wrapper, with the level band of the first sweep** (the corrected
`hlev₁`/`hc₁` version of `Work.Drive.odd_topBdryMeet_zero_iff_of_T6GenAtDBox_meet3Hyp`). -/
theorem blockT6Wrapper_of_T6GenAtD
    (Q : ℂ → CappingSpace)
    (P₁ P₂ : EuclideanSpace ℝ (Fin 2) → CappingSpace) (c₀ c₁ c₂ : ℝ)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hQ : ContMDiff (𝓘(ℝ, ℂ)) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) Q)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hP₁ : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P₁)
    (hP₂ : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) P₂)
    (hP₁seam : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P₁ y = P₁ (seamInv2 y))
    (hP₂seam : ∀ y : EuclideanSpace ℝ (Fin 2), onSeam2 y → P₂ y = P₂ (seamInv2 y))
    (hdisj₁ : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 → Q z ≠ P₁ y)
    (hdisj₂ : ∀ (z : ℂ) (y : EuclideanSpace ℝ (Fin 2)), ‖z‖ ≤ 1 → Q z ≠ P₂ y)
    (hdisj₁₂ : ∀ y y' : EuclideanSpace ℝ (Fin 2), P₁ y ≠ P₂ y')
    (hlev₁ : ∀ z : ℂ, ‖z‖ ≤ 1 → c₁ < levelOf (Q z))
    (hlev₂ : ∀ z : ℂ, ‖z‖ ≤ 1 → c₂ < levelOf (Q z))
    (hM : Meet3Hyp CappingSpace
      (fun k => clampedSweep (![c₀, c₁, c₂] k) (fun r => 1 - r)
        (![diskPlane Q, P₁, P₂] k)))
    (hgen : T6GenAtDBox Q P₁ P₂ c₁ c₂) :
    Odd (topBdryMeet CappingSpace
        (fun k => clampedSweep (![c₀, c₁, c₂] k) (fun r => 1 - r)
          (![diskPlane Q, P₁, P₂] k)) 0).ncard ↔
      Odd (coreSideCount Q c₁ P₁) ∧ Odd (coreSideCount Q c₂ P₂) := by
  -- ## 0. the collar function of the radial collapse
  obtain ⟨δc, hδcpos, hδcut⟩ := hgen.1.2.2
  obtain ⟨β, hβsm, hβpos, hβsqrt, hβδ, hβ1⟩ := colCollar_exists δc hδcpos
  -- ## 1. the identifications at `s = 0`
  have hE0 : ∀ u : EuclideanSpace ℝ (Fin 2), colPlane β Q 0 u
      = clampedSweep (![c₀, c₁, c₂] 0) (fun t => 1 - t)
        (![diskPlane Q, P₁, P₂] 0) (mk3 u 1) := by
    intro u
    show colPlane β Q 0 u = clampedSweep (![c₀, c₁, c₂] 0) (fun t => 1 - t)
      (![diskPlane Q, P₁, P₂] 0) (mk3 u 1)
    rw [colPlane_zero, Matrix.cons_val_zero,
      clampedSweep_face_one _ _ _ (by norm_num) _ (by simp [mk3])]
    exact congrArg (diskPlane Q) (mk2_mk3 u 1).symm
  have hE'0 : ∀ u : EuclideanSpace ℝ (Fin 2), diskPlane Q u
      = clampedSweep (![c₀, c₁, c₂] 0) (fun t => 1 - t)
        (![diskPlane Q, P₁, P₂] 0) (mk3 u 1) := by
    intro u
    show (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u) 0 u
      = clampedSweep (![c₀, c₁, c₂] 0) (fun t => 1 - t)
        (![diskPlane Q, P₁, P₂] 0) (mk3 u 1)
    rw [Matrix.cons_val_zero,
      clampedSweep_face_one _ _ _ (by norm_num) _ (by simp [mk3])]
    exact congrArg (diskPlane Q) (mk2_mk3 u 1).symm
  -- ## 2. the two design data at the collar
  have hD3 : Meet3Hyp CappingSpace
      (fun k => clampedSweep (![c₀, c₁, c₂] k) (fun t => 1 - t)
        (![diskPlane Q, P₁, P₂] k)) := hM
  have hC1 : ∀ x ∈ ppMeet (colPlane β Q)
      (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
      (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂),
      ftS x = 1 → CollarInterior x ∧
        PairOneData (colPlane β Q) (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
          (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂) x :=
    collarInterior_and_pairOneData_of_T6GenAt β Q P₁ P₂ c₀ c₁ c₂ (by simpa using hQ) hQseam hβ1
      (le_of_lt hδcpos) hβδ hδcut hgen.1.1 hgen.1.2.1 hM
  have hint : ∀ x ∈ ppMeet (colPlane β Q)
      (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
      (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂),
      (ftS x = 0 ∨ ftS x = 1) → CollarInterior x := by
    intro x hx h
    rcases h with h0 | h1
    · exact collarInterior_zero_of_meet3Hyp (M := CappingSpace) (D := fun k =>
        clampedSweep (![c₀, c₁, c₂] k) (fun t => 1 - t) (![diskPlane Q, P₁, P₂] k))
        hD3 hE0 hE'0 (fun y => rfl) (fun z => rfl) hx h0
    · exact (hC1 x hx h1).1
  have hpair : ∀ x ∈ ppMeet (colPlane β Q)
      (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
      (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂),
      ftS x = 1 → PairOneData (colPlane β Q)
        (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
        (clampedSweep c₁ (fun t => 1 - t) P₁) (clampedSweep c₂ (fun t => 1 - t) P₂) x := by
    intro x hx h1
    exact (hC1 x hx h1).2
  -- ## 3. the smoothness of the four chains
  have hrawE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
      (Function.uncurry (colPlane β Q)) :=
    contMDiff_colPlane hβsm hβpos hQ
  have hrawE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
      (Function.uncurry (fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)) := by
    have hsnd : ContMDiff (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2))) (𝓡 2) Ctop
        (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => p.2) :=
      contMDiff_iff_contDiff.mpr
        (contDiff_snd (𝕜 := ℝ) (E := ℝ) (F := EuclideanSpace ℝ (Fin 2)))
    show ContMDiff (𝓘(ℝ, ℝ × EuclideanSpace ℝ (Fin 2))) (𝓡 4) Ctop
      (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => diskPlane Q p.2)
    exact (contMDiff_diskPlane hQ).comp hsnd
  have hrawV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
      (clampedSweep c₁ (fun t => 1 - t) P₁) :=
    contMDiff_clampedSweep c₁ (fun t => 1 - t) P₁ (by fun_prop) hP₁
  have hrawW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) Ctop
      (clampedSweep c₂ (fun t => 1 - t) P₂) :=
    contMDiff_clampedSweep c₂ (fun t => 1 - t) P₂ (by fun_prop) hP₂
  -- ## 4. the collar radius and the regularity beyond it
  obtain ⟨δ, hδpos, hδhalf, hregBase⟩ :=
    hregBase_design_chains β Q P₁ P₂ c₀ c₁ c₂ hrawE hrawE' hrawV hrawW hD3 hint hpair
  -- ## 5. the weight supported on the open strip
  set w : ℝ → ℝ := fun s =>
    Real.smoothTransition ((s - δ) / (1 - 2 * δ)) *
      Real.smoothTransition ((1 - δ - s) / (1 - 2 * δ)) with hwdef
  have hden : 0 < 1 - 2 * δ := by linarith
  have hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w := by
    rw [hwdef]
    have hw1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun s : ℝ => (s - δ) / (1 - 2 * δ)) :=
      (contDiff_id.sub contDiff_const).div_const _
    have hw2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun s : ℝ => ((1 : ℝ) - δ - s) / (1 - 2 * δ)) :=
      (contDiff_const.sub contDiff_id).div_const _
    exact (Real.smoothTransition.contDiff (n := ⊤)).comp hw1 |>.mul
      ((Real.smoothTransition.contDiff (n := ⊤)).comp hw2)
  have hwleft : ∀ s : ℝ, s ≤ δ → w s = 0 := by
    intro s hs
    simp only [hwdef]
    have h1 : (s - δ) / (1 - 2 * δ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le
    rw [Real.smoothTransition.zero_of_nonpos h1, zero_mul]
  have hwright : ∀ s : ℝ, 1 - δ ≤ s → w s = 0 := by
    intro s hs
    simp only [hwdef]
    have h1 : (1 - δ - s) / (1 - 2 * δ) ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le
    rw [Real.smoothTransition.zero_of_nonpos h1, mul_zero]
  have hwstrip : ∀ s : ℝ, δ < s → s < 1 - δ → w s ≠ 0 := by
    intro s h1 h2 h0
    simp only [hwdef] at h0
    have ha : 0 < (s - δ) / (1 - 2 * δ) := div_pos (by linarith) hden
    have hb : 0 < (1 - δ - s) / (1 - 2 * δ) := div_pos (by linarith) hden
    have hpa := Real.smoothTransition.pos_of_pos ha
    have hpb := Real.smoothTransition.pos_of_pos hb
    nlinarith [mul_pos hpa hpb]
  have hw0 : w 0 = 0 := hwleft 0 (le_of_lt hδpos)
  have hw1 : w 1 = 0 := hwright 1 (by linarith)
  -- ## 6. the level-face avoidances
  have hdisj₁' : Disjoint (Set.range (diskPlane Q)) (Set.range P₁) := by
    rw [Set.disjoint_left]
    intro p hp1 hp2
    obtain ⟨z, rfl⟩ := hp1
    obtain ⟨y, hy⟩ := hp2
    exact hdisj₁ (sqDisk (foldBox z)) y (norm_sqDisk_le_one (foldBox z) (foldBox_mem_unitBox z)) hy.symm
  have hdisj₂' : Disjoint (Set.range (diskPlane Q)) (Set.range P₂) := by
    rw [Set.disjoint_left]
    intro p hp1 hp2
    obtain ⟨z, rfl⟩ := hp1
    obtain ⟨y, hy⟩ := hp2
    exact hdisj₂ (sqDisk (foldBox z)) y (norm_sqDisk_le_one (foldBox z) (foldBox_mem_unitBox z)) hy.symm
  obtain ⟨hY, hZ⟩ := ppMeet_face_avoidances hβpos hβsqrt Q P₁ P₂ c₁ c₂
    hc₁ hc₂ hlev₁ hlev₂ hdisj₁' hdisj₂'
  -- ## 7. the perturbation family and the tube package
  have hΞ : ChartPert Q 4 (fun s p => chartPert s p) :=
    ⟨chartPert_zero, contMDiff_chartPert,
      fun t p => surjective_mfderiv_chartPert p contMDiff_chartPert t⟩
  have htube := ppParity.htube_of_strip (M := CappingSpace) (E := colPlane β Q)
    (E' := fun (_ : ℝ) (u : EuclideanSpace ℝ (Fin 2)) => diskPlane Q u)
    (V := clampedSweep c₁ (fun t => 1 - t) P₁) (W := clampedSweep c₂ (fun t => 1 - t) P₂)
    (fun s p => chartPert s p) hΞ.1 hΞ.2.1 hΞ.2.2 w hw (le_of_lt hδpos) hrawE hrawE' hrawV hrawW
    hwstrip hwleft hwright hregBase hY hZ (Submission.Drive.unitBox 8)
  -- ## 8. the bundle inputs
  have hfin : (coreMeet Q c₁ P₁).Finite := hgen.1.1.1
  have hbase : ∀ y ∈ Submission.Drive.unitBox 2,
      coreLoop Q 1 ≠ clampedSweep c₁ (fun t => 1 - t) P₁ y := by
    intro y hy heq
    have hmem : (1, y) ∈ coreMeet Q c₁ P₁ := ⟨Set.right_mem_Icc.mpr zero_le_one, hy, heq⟩
    exact absurd (hgen.1.1.2.1 (1, y) hmem).1.2 (lt_irrefl (1 : ℝ))
  have hfind : ∀ q ∈ coreMeet Q c₁ P₁,
      (diamMeet Q q.1 (clampedSweep c₂ (fun t => 1 - t) P₂)).Finite := hfind_of_T6GenAt hgen.1
  have ht5 : ∀ q ∈ coreMeet Q c₁ P₁,
      Odd (diamMeet Q q.1 (clampedSweep c₂ (fun t => 1 - t) P₂)).ncard ↔
        Odd (coreSideCount Q c₂ P₂) :=
    fun q hq => odd_ncard_diamMeet_iff_coreSideCount_clampedSweep Q q.1 c₂ P₂ hQ hQseam hP₂ hP₂seam
      hc₂ hdisj₂ (fun z hz => ne_of_gt (hlev₂ z hz)) (hgen.2 q hq)
  -- ## 9. the intrinsic transport
  exact odd_topBdryMeet_zero_iff_coreSideCount_mul_of_design_intrinsic_nf β Q
    (fun s p => chartPert s p) hΞ w (Submission.Drive.unitBox 8) (isCompact_unitBox 8)
    P₁ P₂ c₀ c₁ c₂ hw (fun x hx _ _ => hx) hwleft hwright hw0 hw1 hrawE hrawE' hrawV hrawW
    (fun s u hu => colPlane_seamInv2 hβ1 s hQseam hu)
    (fun s u hu => diskPlane_seamInv2 hQseam hu)
    (fun y hy => (clampedSweep_seamInv c₁ (fun t => 1 - t) P₁ hP₁seam y hy).symm)
    (fun z hz => (clampedSweep_seamInv c₂ (fun t => 1 - t) P₂ hP₂seam z hz).symm)
    hregBase 1 one_pos htube hQseam (le_of_lt hδcpos) hβδ hδcut hfin hfind hbase ht5

end

end Work.Drive
