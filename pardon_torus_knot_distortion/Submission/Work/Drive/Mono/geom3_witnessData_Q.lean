import Mathlib
import Submission.Work.Drive.Mono.g3OneEvDefs
import Submission.Work.Drive.Mono.g3WitnessDefs
import Submission.Work.Drive.Mono.noGraze_witness_arcs_Q
import Submission.Work.Drive.Mono.geom3_witnessData
import Submission.Work.Drive.Mono.Geom3Defs

namespace Work.Drive.Mono

/-!
**The `Q`-provenance witness of the single-level `Geom3Data` producer.**

This is `Work.Drive.Mono.geom3_witnessData` (`Submission/Work/Drive/Mono/geom3_witnessData.lean`,
PROVED) with three edits, all of them in its SS5 (the perturbation of the tilt direction); SS6-SS12
and all the other clauses are unchanged:

* the tilt direction `V` is **drawn from the prescribed countable dense family `Q`** of
  `HeightGood` height directions, in the form `V = orthDir (shiftVσ σ 1) (unitDir ng)`,
  `n = unitDir ng` with `ng ∈ Q`, via `Work.Drive.Mono.noGraze_witness_arcs_Q`;
* the perturbation `wdg_axis_perturb` of `geom3_witnessData` is dropped (its `εv` is set to `0`),
  and the adapted basis is the *prescribed* one `(af ng, bf ng)` (hypothesis `hframe`);
* the axis clause `haxis` and `V ≠ shiftVσ σ 1` are derived from the non-vanishing-coordinate
  hypothesis `hQnv` via `wdg_ne_smul_single` / `wdg_ne_shiftVσ`;
* one conjunct is ADDED to the bundle: the **flat sliver**, the last conjunct of
  `Work.Drive.Mono.WitnessData3`.
-/

open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set Filter
open scoped ENNReal _root_.Topology RealInnerProductSpace

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

/-! ## Elementary estimates for the tilt direction -/

/-- **The two slab heights differ by the inner product with the difference of the directions.** -/
private lemma wdg_slab_diff (v v' x c : R3) :
    inner ℝ v x - inner ℝ v c
      = (inner ℝ v' x - inner ℝ v' c) + inner ℝ (v - v') (x - c) := by
  rw [← inner_sub_right, ← inner_sub_right, ← inner_add_left]
  congr 1
  abel

/-- **The two slab heights differ by at most `εv * R` on a ball of radius `R`.** -/
private lemma wdg_slab_le {v v' x c : R3} {εv R u : ℝ} (h : ‖v' - v‖ ≤ εv)
    (hx : ‖x - c‖ ≤ R) :
    |inner ℝ v x - (inner ℝ v c + u)| ≤ |inner ℝ v' x - (inner ℝ v' c + u)| + εv * R := by
  have hkey : inner ℝ v x - (inner ℝ v c + u)
      = (inner ℝ v' x - (inner ℝ v' c + u)) + inner ℝ (v - v') (x - c) := by
    have h1 : inner ℝ (v - v') (x - c) = inner ℝ v (x - c) - inner ℝ v' (x - c) :=
      inner_sub_left _ _ _
    have h2 : inner ℝ v (x - c) = inner ℝ v x - inner ℝ v c := inner_sub_right _ _ _
    have h3 : inner ℝ v' (x - c) = inner ℝ v' x - inner ℝ v' c := inner_sub_right _ _ _
    rw [h1, h2, h3]
    ring
  rw [hkey]
  refine le_trans (abs_add_le _ _) ?_
  have hεv0 : 0 ≤ εv := le_trans (norm_nonneg _) h
  refine add_le_add le_rfl ?_
  calc |inner ℝ (v - v') (x - c)| ≤ ‖v - v'‖ * ‖x - c‖ := abs_real_inner_le_norm _ _
    _ = ‖v' - v‖ * ‖x - c‖ := by rw [norm_sub_rev]
    _ ≤ εv * R := mul_le_mul h hx (norm_nonneg _) hεv0

/-- **The tilted slab functional differs from the flat one by the inner product with `v - e`.** -/
private lemma wdg_slabFn_sub (σ : Equiv.Perm (Fin 3)) (u : ℝ) {e v x c : R3}
    (hex : inner ℝ e x = x (σ 2)) (hec : inner ℝ e c = c (σ 2)) :
    Work.Drive.Final.slabFn c u v x - (x (σ 2) - (c (σ 2) + u))
      = inner ℝ (v - e) (x - c) := by
  have h3 := wdg_slab_diff v e x c
  rw [hex, hec] at h3
  simp only [Work.Drive.Final.slabFn]
  have hgoal : (inner ℝ v x - (inner ℝ v c + u)) - (x (σ 2) - (c (σ 2) + u))
      = (inner ℝ v x - inner ℝ v c) - (x (σ 2) - c (σ 2)) := by ring
  rw [hgoal, h3]
  ring

/-- **A vector with two non-zero coordinates is parallel to no coordinate axis.** -/
private theorem wdg_ne_smul_single {v : R3} {j j' : Fin 3} (hjj : j ≠ j')
    (hj : v j ≠ 0) (hj' : v j' ≠ 0) :
    ∀ i : Fin 3, ∀ a : ℝ, EuclideanSpace.single i (1 : ℝ) ≠ a • v := by
  intro i a hcon
  have hsingle : ∀ m : Fin 3, (EuclideanSpace.single i (1 : ℝ)) m = if m = i then 1 else 0 := by
    intro m; rw [PiLp.single_apply]
  have hai : a * v i = 1 := by
    have h2 := congrArg (fun x : R3 => x i) hcon.symm
    rw [hsingle i, if_pos rfl] at h2
    simpa [PiLp.smul_apply, smul_eq_mul] using h2
  have ha0 : a ≠ 0 := fun h0 => by rw [h0, zero_mul] at hai; norm_num at hai
  have hzero : ∀ m : Fin 3, m ≠ i → v m = 0 := by
    intro m hm
    have h2 := congrArg (fun x : R3 => x m) hcon.symm
    rw [hsingle m, if_neg hm] at h2
    have h3 : a * v m = 0 := by simpa [PiLp.smul_apply, smul_eq_mul] using h2.symm
    exact (mul_eq_zero.mp h3).resolve_left ha0
  rcases eq_or_ne j i with hji | hji
  · exact hj' (hzero j' (fun hc => hjj (by rw [hji, hc])))
  · exact hj (hzero j hji)

/-- **A vector with two non-zero coordinates is not the standard axis vector `e_{σ 2}`.** -/
private theorem wdg_ne_shiftVσ {v : R3} {σ : Equiv.Perm (Fin 3)} {j j' : Fin 3}
    (hjj : j ≠ j') (hj : v j ≠ 0) (hj' : v j' ≠ 0) : v ≠ Work.BoxShrink.shiftVσ σ 1 := by
  intro hcon
  have hsingle : ∀ m : Fin 3, (Work.BoxShrink.shiftVσ σ 1) m = if m = σ 2 then 1 else 0 := by
    intro m; rw [Work.BoxShrink.shiftVσ_apply]
  have hzero : ∀ m : Fin 3, m ≠ σ 2 → v m = 0 := by
    intro m hm
    have h2 := congrArg (fun x : R3 => x m) hcon
    rw [hsingle m, if_neg hm] at h2
    exact h2
  rcases eq_or_ne j (σ 2) with h1 | h1
  · exact hj' (hzero j' (fun hc => hjj (by rw [h1, hc])))
  · exact hj (hzero j h1)

/-! ## The witness stage of the single-level `Geom3Data` producer, from the countable family `Q` -/

theorem geom3_witnessData_Q
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot) {r s u : ℝ}
    (hr : 0 < r) (hrs : r < s) (hs : s < (1 + Submission.eps) * r)
    (hu : |u| < Submission.eps * r)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (hcut : Work.Drive.Mono.CutTransverse K s c σ u)
    (hFC : Work.Drive.Mono.FaceCrossReg ψ c σ s u)
    (hFB : Work.Drive.Mono.FaceNoBend ψ c σ s u)
    {εg δg : ℝ} (hεg : 0 < εg) (hδg : 0 < δg)
    (hnograz : ∀ v : LeanEval.KnotTheory.PardonDistortion.R3, ‖v‖ = 1 →
      ‖v - Work.BoxShrink.shiftVσ σ 1‖ < εg →
      ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
        deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 →
        δg ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)|)
    (hnobend : ∀ t : ℝ, K.curve t ∈ closure (Submission.PBox s c σ) →
      (K.curve t) (σ 2) = c (σ 2) + u →
      Work.Drive.Mono.vertVel K (Work.BoxShrink.shiftVσ σ 1) t = 0 →
      Work.Drive.Mono.vertAcc K (Work.BoxShrink.shiftVσ σ 1) t = 0)
    {mE : ℝ} (hmE : 0 < mE)
    (hhedge : ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      |z (σ 0) - c (σ 0)| = Submission.boxSide 0 * s →
      |z (σ 1) - c (σ 1)| = Submission.boxSide 1 * s →
      mE ≤ |z (σ 2) - (c (σ 2) + u)|)
    (Q : Set LeanEval.KnotTheory.PardonDistortion.R3) (hQc : Q.Countable)
    (hQH : ∀ ng ∈ Q, Work.Drive.Mono.Band.HeightGood ψ ng)
    (hQd : ∀ U : Set LeanEval.KnotTheory.PardonDistortion.R3, IsOpen U → U.Nonempty →
      (U ∩ Q).Nonempty)
    (hQnv : ∀ ng ∈ Q, ∀ j : Fin 3,
      (Work.Drive.Mono.orthDir (Work.BoxShrink.shiftVσ σ 1)
        (Work.Drive.Mono.unitDir ng)) j ≠ 0)
    (af bf : LeanEval.KnotTheory.PardonDistortion.R3 →
      LeanEval.KnotTheory.PardonDistortion.R3)
    (hframe : ∀ ng ∈ Q,
      Work.Drive.Mono.G3Frame (Work.BoxShrink.shiftVσ σ 1) ng (af ng) (bf ng)) :
    ∃ (V n a₀ b₀ : LeanEval.KnotTheory.PardonDistortion.R3) (ρ A B : ℝ) (N : ℕ)
      (γ : Fin N → ℝ → LeanEval.KnotTheory.PardonDistortion.R3) (η m : ℝ)
      (ng : LeanEval.KnotTheory.PardonDistortion.R3),
      ng ∈ Q ∧ n = Work.Drive.Mono.unitDir ng ∧
      V = Work.Drive.Mono.orthDir (Work.BoxShrink.shiftVσ σ 1) n ∧
      a₀ = af ng ∧ b₀ = bf ng ∧
      Work.Drive.Mono.WitnessData3 ψ K s u c σ V n a₀ b₀ ρ A B N γ η m δg mE := by
  classical
  set e : R3 := Work.BoxShrink.shiftVσ σ 1 with hedef
  have he_inner : ∀ y : R3, inner ℝ e y = y (σ 2) := fun y => by
    rw [hedef]; exact Work.Drive.Mono.inner_shiftVσ_one σ y
  have he_norm : ‖e‖ = 1 := by rw [hedef]; exact Work.Drive.Mono.norm_shiftVσ_one σ
  -- ## 0. elementary data
  have hs0 : 0 < s := lt_trans hr hrs
  have hs0le : 0 ≤ s := le_of_lt hs0
  have heps0 : (0 : ℝ) < Submission.eps := Submission.eps_pos
  have hu2 : |u| < Submission.boxSide 2 * s := by
    have h1 : Submission.eps * r < Submission.eps * s := mul_lt_mul_of_pos_left hrs heps0
    have he2 : Submission.eps = 2 / 13 := rfl
    have h2 : Submission.eps * s < s := by rw [he2]; nlinarith [hs0]
    have h4 : s ≤ Submission.boxSide 2 * s := by
      have h5 : (1 : ℝ) ≤ Submission.boxSide 2 := Submission.one_le_boxSide 2
      nlinarith [hs0]
    linarith
  have hbs2m2 : 0 < (Submission.boxSide 2 * s - |u|) / 2 := by linarith [hu2]
  -- ## 1. the trace arcs of the box sphere at the cutting level `u`
  obtain ⟨N, γ, η, m, hη0, hm0, hγ, hγh, hbranch, hcover⟩ :=
    Work.Drive.Mono.gammaArcs_exist ψ hs0 c σ hu2 hFC
  have hbend : ∀ k, deriv (γ k) 0 = Work.BoxShrink.shiftVσ σ 1 →
      deriv (deriv (γ k)) 0 = 0 := by
    intro k hk
    obtain ⟨i, hi, ε, hε, β, hβ, hγβ⟩ := hbranch k
    exact Work.Drive.Mono.gammaArc_noBend ψ c σ hFC hFB hη0 hi hε hβ hγβ
      (fun t ht => hγh k t ht) hk
  -- ## 2. the coordinate identity `⟪e, γ'⟫ = 1` on the interior of the parameter interval
  have hcoord_all : ∀ k (t : ℝ), t ∈ Set.Ioo (-η) η → (deriv (γ k) t) (σ 2) = 1 := by
    intro k t ht
    have hIcc : Set.Icc (-η) η ∈ 𝓝 t :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ht) (fun r hr => ⟨le_of_lt hr.1, le_of_lt hr.2⟩)
    have hdiff : DifferentiableAt ℝ (γ k) t :=
      ((hγ k).contDiffAt hIcc).differentiableAt (by norm_num)
    have h1 : deriv (fun r : ℝ => (γ k r) (σ 2)) t = (deriv (γ k) t) (σ 2) := by
      have h2 : (fun r : ℝ => (γ k r) (σ 2)) = fun r : ℝ => inner ℝ (unitCoord σ 2) (γ k r) := by
        funext r; rw [inner_unitCoord]
      rw [h2, deriv_inner_apply ℝ (differentiableAt_const _) hdiff, inner_unitCoord]
      simp
    rw [← h1]
    have hEv : (fun r : ℝ => (γ k r) (σ 2)) =ᶠ[𝓝 t] fun r : ℝ => c (σ 2) + u + r := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with r hr
      exact hγh k r ⟨le_of_lt hr.1, le_of_lt hr.2⟩
    rw [Filter.EventuallyEq.deriv_eq hEv]
    simp
  -- ## 3. the numerical constants
  obtain ⟨MA1, MA2, MA4, hMA10, hMA20, hMA40, hMAspec⟩ := Work.Drive.Mono.arcFamilyBounds hη0 hγ
  set R1 : ℝ := 5 / 2 * s with hR1def
  have hR1pos : 0 < R1 := by rw [hR1def]; linarith
  set θ' : ℝ :=
    min (min (min (1 / 32) (εg / 3)) (min (1 / (16 * (MA1 + 1))) (δg / (2 * (R1 + 1)))))
      (min (min ((mE / 2) / (2 * (R1 + 1))) (((Submission.boxSide 2 * s - |u|) / 2) / (2 * (R1 + 1))))
        (min ((m / 2) / (2 * (R1 + 1))) ((η / 8) / (2 * (R1 + 1))))) with hθ'def
  have hθ'0 : 0 < θ' := by
    rw [hθ'def]; simp only [lt_min_iff]
    exact ⟨⟨⟨by norm_num, by linarith⟩, ⟨by positivity, by positivity⟩⟩,
      ⟨⟨by positivity, by positivity⟩, ⟨by positivity, by positivity⟩⟩⟩
  have hθ'1 : θ' ≤ 1 / 32 := by rw [hθ'def]; simp
  have hθ'2 : θ' ≤ εg / 3 := by rw [hθ'def]; simp
  have hθ'3 : θ' ≤ 1 / (16 * (MA1 + 1)) := by rw [hθ'def]; simp
  have hθ'4 : θ' ≤ δg / (2 * (R1 + 1)) := by rw [hθ'def]; simp
  have hθ'5 : θ' ≤ (mE / 2) / (2 * (R1 + 1)) := by rw [hθ'def]; simp
  have hθ'6 : θ' ≤ ((Submission.boxSide 2 * s - |u|) / 2) / (2 * (R1 + 1)) := by
    rw [hθ'def]; simp
  have hθ'7 : θ' ≤ (m / 2) / (2 * (R1 + 1)) := by rw [hθ'def]; simp
  have hθ'8 : θ' ≤ (η / 8) / (2 * (R1 + 1)) := by rw [hθ'def]; simp
  -- ## 4. the merged no-grazing witness for the arcs, drawn from `Q`
  obtain ⟨v, n, hw, ρw, hv1, hn1, hvn, hgood, hθ'v, hvεg4, hhw0, hρw0, hhwsize,
    hcl1, hcl2, hcl3, hcl4, harcℓ, harcv, hng⟩ :=
    Work.Drive.Mono.noGraze_witness_arcs_Q ψ K hr hrs hu c σ hcut hεg hδg hθ'0 hnograz hnobend
      hη0 hγ hγh hbend Q hQc hQH hQd
  rw [← hedef] at hθ'v hvεg4 hhwsize hng
  rw [← hR1def] at hhwsize
  obtain ⟨ng, hngQ, hnng, hvng⟩ := hng
  have hvεg : ‖v - e‖ < εg := by linarith [hvεg4, hεg]
  -- ## 5. the prescribed frame, and the axis clause from the non-vanishing coordinates
  have hvj : ∀ j : Fin 3, v j ≠ 0 := by
    intro j
    rw [hvng, hnng]
    exact hQnv ng hngQ j
  have hvne : v ≠ e :=
    wdg_ne_shiftVσ (σ := σ) (j := 0) (j' := 1) (by decide) (hvj 0) (hvj 1)
  have haxis' : ∀ (i : Fin 3) (a : ℝ), EuclideanSpace.single (σ i) (1 : ℝ) ≠ a • v :=
    fun i a => wdg_ne_smul_single (j := 0) (j' := 1) (by decide) (hvj 0) (hvj 1) (σ i) a
  obtain ⟨hfr1, hfr2, hfr3, hfr4, hfr5, hfr6, hfr7, hfr8, hfr9⟩ := hframe ng hngQ
  have hva0 : inner ℝ v (af ng) = 0 := by rw [hvng, hnng]; exact hfr7
  have hvb0 : inner ℝ v (bf ng) = 0 := by rw [hvng, hnng]; exact hfr8
  have hn_frame : n = (Real.sqrt 2)⁻¹ • (af ng + bf ng) := by rw [hnng]; exact hfr9
  -- ## 6. the half-width window `(A, B)`
  set A : ℝ := ‖v - e‖ * R1 with hAdef
  have hApos : 0 < A := by
    rw [hAdef]
    exact mul_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hvne)) hR1pos
  have hA_le : A ≤ θ' * R1 := by
    rw [hAdef]
    exact mul_le_mul_of_nonneg_right hθ'v (le_of_lt hR1pos)
  have key : ∀ c0 : ℝ, 0 < c0 → θ' ≤ c0 / (2 * (R1 + 1)) → θ' * R1 < c0 := by
    intro c0 hc0 hc
    have h1 : θ' * R1 ≤ (c0 / (2 * (R1 + 1))) * R1 :=
      mul_le_mul_of_nonneg_right hc (le_of_lt hR1pos)
    have h4 : (c0 / (2 * (R1 + 1))) * R1 * 2 < c0 := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
        div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (R1 + 1))]
      nlinarith [hc0, hR1pos]
    linarith [h1, h4]
  have hA_δg : A < δg := lt_of_le_of_lt hA_le (key δg hδg hθ'4)
  have hA_mE : A < mE / 2 := lt_of_le_of_lt hA_le (key (mE / 2) (by linarith) hθ'5)
  have hA_bs : A < (Submission.boxSide 2 * s - |u|) / 2 :=
    lt_of_le_of_lt hA_le (key ((Submission.boxSide 2 * s - |u|) / 2) hbs2m2 hθ'6)
  have hA_m : A < m / 2 := lt_of_le_of_lt hA_le (key (m / 2) (by linarith) hθ'7)
  have hA_η : A < η / 8 := lt_of_le_of_lt hA_le (key (η / 8) (by linarith) hθ'8)
  have hv_e18 : ‖v - Work.BoxShrink.shiftVσ σ 1‖ ≤ 1 / 8 := by
    rw [← hedef]
    linarith [hθ'v, hθ'1]
  have hA_win : A < Work.Drive.Mono.boxWidth s σ v - |u| := by
    have h := Work.Drive.Mono.Band.window_nondegenerate s hs0 σ hv_e18 hrs hu
    rw [← hedef] at h
    rw [hAdef, hR1def]
    exact h
  have hA_hwhw : 2 * A < hw := by rw [hAdef]; exact hhwsize
  have hA_hw : A < hw := by linarith [hApos, hA_hwhw]
  set B : ℝ := min hw
      (min (Work.Drive.Mono.boxWidth s σ v - |u|)
        (min δg (min (mE / 2)
          (min ((Submission.boxSide 2 * s - |u|) / 2) (min (m / 2) (η / 8))))))
    with hBdef
  have hB_hw : B ≤ hw := by rw [hBdef]; exact min_le_left _ _
  have hB_win : B ≤ Work.Drive.Mono.boxWidth s σ v - |u| := by rw [hBdef]; simp
  have hB_δg : B ≤ δg := by rw [hBdef]; simp
  have hB_mE : B ≤ mE / 2 := by rw [hBdef]; simp
  have hB_bs : B ≤ (Submission.boxSide 2 * s - |u|) / 2 := by rw [hBdef]; simp
  have hB_m : B ≤ m / 2 := by rw [hBdef]; simp
  have hB_η : B ≤ η / 8 := by rw [hBdef]; simp
  have hAB : A < B := by
    rw [hBdef]
    exact lt_min hA_hw (lt_min hA_win (lt_min hA_δg (lt_min hA_mE (lt_min hA_bs
      (lt_min hA_m hA_η)))))
  -- ## 9. the no-grazing clauses at the tilt `v`
  have hcl1' : ∀ h ∈ Set.Ioo A B, ∀ t : ℝ, Submission.boxNorm c σ (K.curve t) = s →
      h ≤ |Work.Drive.Final.slabFn c u v (K.curve t)| := by
    intro h hh t hbs
    have h2 : h < hw := lt_of_lt_of_le hh.2 hB_hw
    have h1 := hcl1 t hbs
    simp only [Work.Drive.Final.slabFn]
    linarith
  have hcl2' : ∀ h ∈ Set.Ioo A B, ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 →
      h ≤ |Work.Drive.Final.slabFn c u v (K.curve t)| := by
    intro h hh t htmem hd
    have h2 : h < hw := lt_of_lt_of_le hh.2 hB_hw
    have h1 := hcl2 t htmem hd
    simp only [Work.Drive.Final.slabFn]
    linarith
  have hcl3' : ∀ h ∈ Set.Ioo A B, ∀ nn : R3, ‖nn‖ = 1 → ‖nn - n‖ < ρw →
      ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |Work.Drive.Final.slabFn c u v (K.curve t)| ≤ h →
      deriv (fun r : ℝ => inner ℝ nn (K.curve r)) t ≠ 0 := by
    intro h hh nn hnn1 hnnn t htmem hle
    have h2 : h < hw := lt_of_lt_of_le hh.2 hB_hw
    have hle' : |inner ℝ v (K.curve t) - (inner ℝ v c + u)| ≤ h := by
      simpa only [Work.Drive.Final.slabFn] using hle
    exact hcl3 nn hnn1 hnnn t htmem (by linarith)
  have hcl4' : ∀ h ∈ Set.Ioo A B, ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |Work.Drive.Final.slabFn c u v (K.curve t)| = h →
      deriv (fun r : ℝ => inner ℝ v (K.curve r)) t ≠ 0 := by
    intro h hh t htmem heq hd
    have h1 := hnograz v hv1 hvεg t htmem hd
    have h2 : h < δg := lt_of_lt_of_le hh.2 hB_δg
    have h3 : |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h := by
      simpa only [Work.Drive.Final.slabFn] using heq
    linarith
  -- ## 10. the cover by the arcs
  have hcover' : ∀ h ∈ Set.Ioo A B, ∀ z : R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → Submission.boxNorm c σ z = s →
      |Work.Drive.Final.slabFn c u v z| ≤ h →
      (∀ j : Fin 3, j ≠ 2 → ∀ j' : Fin 3, j' ≠ 2 → j ≠ j' →
        ¬ (|z (σ j) - c (σ j)| = Submission.boxSide j * s ∧
           |z (σ j') - c (σ j')| = Submission.boxSide j' * s)) →
      ∃ k, ∃ t ∈ Set.Ioo (-η) η, z = γ k t ∧ |t| ≤ 2 * h := by
    intro h hh z hz hzn hslab hnoext
    have hx : ‖z - c‖ ≤ R1 := by
      rw [hR1def]
      exact Work.Drive.Mono.norm_sub_le_of_mem_closure_PBox hs0le
        (Work.Drive.Mono.mem_closure_PBox_of_boxNorm_le hs0 c σ (le_of_eq hzn))
    have hdiff : |z (σ 2) - (c (σ 2) + u)|
        ≤ |Work.Drive.Final.slabFn c u v z| + ‖v - e‖ * R1 := by
      have h1 := wdg_slab_le (v := e) (v' := v) (x := z) (c := c) (εv := ‖v - e‖) (R := R1)
        (u := u) (le_refl _) hx
      simp only [he_inner] at h1
      simpa only [Work.Drive.Final.slabFn] using h1
    have hslab' : |Work.Drive.Final.slabFn c u v z| ≤ h := hslab
    have hA' : ‖v - e‖ * R1 < h := by rw [← hAdef]; exact hh.1
    have hle2h : |z (σ 2) - (c (σ 2) + u)| ≤ 2 * h := by linarith [hdiff, hslab', hA']
    have hflat : |z (σ 2) - (c (σ 2) + u)| < m := by
      have h2 : h < m / 2 := lt_of_lt_of_le hh.2 hB_m
      linarith
    obtain ⟨k, t, htIoo, hzt⟩ := hcover z hz hzn hflat hnoext
    refine ⟨k, t, htIoo, hzt, ?_⟩
    have hzt' : z (σ 2) = c (σ 2) + u + t := by
      rw [hzt]; exact hγh k t ⟨le_of_lt htIoo.1, le_of_lt htIoo.2⟩
    have ht_eq : |t| = |z (σ 2) - (c (σ 2) + u)| := by
      rw [hzt', show c (σ 2) + u + t - (c (σ 2) + u) = t by ring]
    rw [ht_eq]
    exact hle2h
  -- ## 11. the arc clauses
  have harc_nn : ∀ h ∈ Set.Ioo A B, ∀ k, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h →
      ∀ nn : R3, ‖nn‖ = 1 → ‖nn - n‖ < ρw → inner ℝ nn (deriv (γ k) t) ≠ 0 := by
    intro h hh k t htIoo ht2h nn hnn1 hnnn
    have h1 : |t| ≤ 2 * hw := by
      have h2 : h < hw := lt_of_lt_of_le hh.2 hB_hw
      linarith
    exact harcℓ k t htIoo h1 nn hnn1 hnnn
  have harc_slope : ∀ h ∈ Set.Ioo A B, ∀ k, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h →
      (1 / 2 : ℝ) ≤ inner ℝ v (deriv (γ k) t) := by
    intro h hh k t htIoo ht2h
    have htη : |t| ≤ η / 2 := by
      have h1 : 2 * h < η / 4 := by
        have h2 : h < η / 8 := lt_of_lt_of_le hh.2 hB_η
        linarith
      linarith
    have hM1 : ‖deriv (γ k) t‖ ≤ MA1 := (hMAspec k t htIoo htη).1
    have hcoord : inner ℝ e (deriv (γ k) t) = 1 := by
      rw [he_inner]
      exact hcoord_all k t htIoo
    have hsplit : inner ℝ v (deriv (γ k) t)
        = inner ℝ e (deriv (γ k) t) + inner ℝ (v - e) (deriv (γ k) t) := by
      rw [← inner_add_left]; congr 1; abel
    have hbd : |inner ℝ (v - e) (deriv (γ k) t)| ≤ ‖v - e‖ * MA1 :=
      le_trans (abs_real_inner_le_norm _ _) (mul_le_mul_of_nonneg_left hM1 (norm_nonneg _))
    have hsmallM : ‖v - e‖ * MA1 ≤ 1 / 4 := by
      have h1 : ‖v - e‖ * MA1 ≤ θ' * MA1 :=
        mul_le_mul_of_nonneg_right hθ'v (le_of_lt hMA10)
      have h3 : θ' * MA1 ≤ (1 / (16 * (MA1 + 1))) * MA1 :=
        mul_le_mul_of_nonneg_right hθ'3 (le_of_lt hMA10)
      have h4 : (1 / (16 * (MA1 + 1))) * MA1 ≤ 1 / 16 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [hMA10]
      linarith
    rw [hsplit, hcoord]
    have h5 := (abs_le.mp hbd).1
    linarith
  -- ## 12. the flat sliver at the fixed cutting level `u`
  set m₀ : ℝ := min (hw - A) δg with hm₀def
  have hA_lt_hwA : A < hw - A := by linarith [hA_hwhw]
  have hm₀_gt : A < m₀ := by
    rw [hm₀def]
    exact lt_min hA_lt_hwA hA_δg
  have hm₀_le_hwA : m₀ ≤ hw - A := min_le_left _ _
  have hm₀_le_δg : m₀ ≤ δg := min_le_right _ _
  set ε₀ : ℝ := (A + m₀) / 2 with hε₀def
  have hε₀pos : 0 < ε₀ := by rw [hε₀def]; linarith [hApos, hm₀_gt]
  have hA_lt_ε₀ : A < ε₀ := by rw [hε₀def]; linarith [hm₀_gt]
  have hε₀_lt_m₀ : ε₀ < m₀ := by rw [hε₀def]; linarith [hm₀_gt]
  have hε₀_le_hwA : ε₀ ≤ hw - A := le_trans (le_of_lt hε₀_lt_m₀) hm₀_le_hwA
  have hε₀_le_δg : ε₀ ≤ δg := le_trans (le_of_lt hε₀_lt_m₀) hm₀_le_δg
  have hε₀_le_hwA' : ε₀ ≤ hw - ‖v - e‖ * R1 := by rw [← hAdef]; exact hε₀_le_hwA
  have hsliver1 : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |Work.Drive.Final.slabFn c u v (K.curve t) - ((K.curve t) (σ 2) - (c (σ 2) + u))| < ε₀ := by
    intro t ht
    have hx : ‖K.curve t - c‖ ≤ R1 := by
      rw [hR1def]; exact Work.Drive.Mono.norm_sub_le_of_mem_PBox hs0le ht
    have hkey := wdg_slabFn_sub (σ := σ) (u := u) (e := e) (v := v) (x := K.curve t) (c := c)
      (he_inner _) (he_inner _)
    rw [hkey]
    calc |inner ℝ (v - e) (K.curve t - c)| ≤ ‖v - e‖ * ‖K.curve t - c‖ :=
          abs_real_inner_le_norm _ _
      _ ≤ ‖v - e‖ * R1 := mul_le_mul_of_nonneg_left hx (norm_nonneg _)
      _ = A := by rw [hAdef]
      _ < ε₀ := hA_lt_ε₀
  have hsliver2 : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      deriv (fun r : ℝ => (K.curve r) (σ 2)) t = 0 →
      ε₀ ≤ |(K.curve t) (σ 2) - (c (σ 2) + u)| := by
    intro t ht hd
    have hd' : deriv (fun r : ℝ => inner ℝ e (K.curve r)) t = 0 := by
      have hfun : (fun r : ℝ => inner ℝ e (K.curve r)) = fun r : ℝ => (K.curve r) (σ 2) := by
        funext r; exact he_inner _
      rw [hfun]; exact hd
    have h1 := hnograz e he_norm (by simp only [sub_self, norm_zero]; exact hεg) t ht hd'
    simp only [he_inner] at h1
    linarith [hε₀_le_δg]
  have hsliver3 : ∀ t : ℝ, Submission.boxNorm c σ (K.curve t) = s →
      ε₀ ≤ |(K.curve t) (σ 2) - (c (σ 2) + u)| := by
    intro t hbs
    have hx : ‖K.curve t - c‖ ≤ R1 := by
      rw [hR1def]
      exact Work.Drive.Mono.norm_sub_le_of_mem_closure_PBox hs0le
        (Work.Drive.Mono.mem_closure_PBox_of_boxNorm_le hs0 c σ (le_of_eq hbs))
    have h1 := hcl1 t hbs
    have h2 := wdg_slab_le (v := v) (v' := e) (x := K.curve t) (c := c) (εv := ‖v - e‖)
      (R := R1) (u := u) (le_of_eq (norm_sub_rev e v)) hx
    simp only [he_inner] at h2
    have h3 : hw - ‖v - e‖ * R1 ≤ |(K.curve t) (σ 2) - (c (σ 2) + u)| := by linarith
    linarith [h3, hε₀_le_hwA']
  have hsliver4 : ∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |(K.curve t) (σ 2) - (c (σ 2) + u)| < ε₀ →
      deriv (fun r : ℝ => inner ℝ v (K.curve r)) t ≠ 0 := by
    intro t ht hlt hd
    have h1 := hcl2 t ht hd
    have hx : ‖K.curve t - c‖ ≤ R1 := by
      rw [hR1def]; exact Work.Drive.Mono.norm_sub_le_of_mem_PBox hs0le ht
    have h2 := wdg_slab_le (v := v) (v' := e) (x := K.curve t) (c := c) (εv := ‖v - e‖)
      (R := R1) (u := u) (le_of_eq (norm_sub_rev e v)) hx
    simp only [he_inner] at h2
    have h4 : ε₀ + ‖v - e‖ * R1 ≤ hw := by linarith [hε₀_le_hwA']
    linarith [h1, h2, hlt, h4]
  have hsliver : ∃ ε₀ : ℝ, 0 < ε₀ ∧
      (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
        |Work.Drive.Final.slabFn c u v (K.curve t) - ((K.curve t) (σ 2) - (c (σ 2) + u))| < ε₀) ∧
      (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
        deriv (fun r : ℝ => (K.curve r) (σ 2)) t = 0 →
        ε₀ ≤ |(K.curve t) (σ 2) - (c (σ 2) + u)|) ∧
      (∀ t : ℝ, Submission.boxNorm c σ (K.curve t) = s →
        ε₀ ≤ |(K.curve t) (σ 2) - (c (σ 2) + u)|) ∧
      (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
        |(K.curve t) (σ 2) - (c (σ 2) + u)| < ε₀ →
        deriv (fun r : ℝ => inner ℝ v (K.curve r)) t ≠ 0) :=
    ⟨ε₀, hε₀pos, hsliver1, hsliver2, hsliver3, hsliver4⟩
  -- ## 13. the datum
  refine ⟨v, n, af ng, bf ng, ρw, A, B, N, γ, η, m, ng, hngQ, hnng, ?_, rfl, rfl, ?_⟩
  · exact hvng
  · rw [Work.Drive.Mono.WitnessData3]
    refine ⟨hv1, haxis', hv_e18, hn1, hvn, hgood, hfr4, hfr5, hfr6, hva0, hvb0, hn_frame,
      hρw0, hApos, hAB, ?_, hB_win, hB_δg, hB_mE, hB_bs, hcl1', hcl2', hcl3', hcl4',
      hη0, hm0, hB_m, hγ, hγh, hbranch, hcover', harc_nn, harc_slope, hsliver⟩
    rw [hAdef, hR1def, hedef]

end

end Work.Drive.Mono
