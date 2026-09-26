import Mathlib
import Submission.Work.Drive.Mono.gammaArcs_exist
import Submission.Work.Drive.Mono.BoxGenE
import Submission.Work.Drive.Mono.arcHeightAux
import Submission.Work.Drive.Mono.arcHeightBranch

/-!
# The intrinsic data of the box-trace arcs near the cutting plane
-/

namespace Work.Drive.Mono
open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace
open scoped _root_.Topology

noncomputable section

private lemma beta_zero_cross (ψ : Submission.Diffeo) {s u : ℝ} (c : R3)
    (σ : Equiv.Perm (Fin 3)) {i : Fin 3} {ev : ℝ} {η : ℝ} {γ : ℝ → R3} {β : ℝ → ℝ × ℝ}
    (hη : 0 < η)
    (hβγ : ∀ t ∈ Set.Icc (-η) η, Work.BoxShrink.Pinch.par ψ (β t) = γ t ∧
      (γ t) (σ i) = c (σ i) + ev * Submission.boxSide i * s)
    (hγh : ∀ t ∈ Set.Icc (-η) η, (γ t) (σ 2) = c (σ 2) + u + t) :
    facePairMap ψ σ i (β 0) =
      (c (σ i) + ev * Submission.boxSide i * s, c (σ 2) + u) := by
  have h0 : (0:ℝ) ∈ Set.Icc (-η) η := ⟨by linarith, by linarith⟩
  rw [Prod.ext_iff]
  refine ⟨?_, ?_⟩
  · show (Work.BoxShrink.Pinch.par ψ (β 0)) (σ i) = _
    rw [(hβγ 0 h0).1]
    exact (hβγ 0 h0).2
  · show (Work.BoxShrink.Pinch.par ψ (β 0)) (σ 2) = _
    rw [(hβγ 0 h0).1, hγh 0 h0]
    ring

theorem arcHeightKernel (ψ : Submission.Diffeo) {s u : ℝ} (hs : 0 < s)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (hX : Work.Drive.Mono.FaceCrossReg ψ c σ s u)
    (hFB : Work.Drive.Mono.FaceNoBend ψ c σ s u) :
    ∃ (D : Finset LeanEval.KnotTheory.PardonDistortion.R3) (arcE arcM arcL arcQ : ℝ),
      (∀ d ∈ D, inner ℝ (Work.BoxShrink.shiftVσ σ 1) d = 0) ∧
      0 < arcE ∧ 0 < arcM ∧ 0 < arcL ∧ 0 < arcQ ∧
      (∀ (γ : ℝ → LeanEval.KnotTheory.PardonDistortion.R3) (η : ℝ) (i : Fin 3) (ev : ℝ)
          (β : ℝ → ℝ × ℝ),
        0 < η → i ≠ 2 → (ev = 1 ∨ ev = -1) →
        ContDiffOn ℝ 3 γ (Set.Icc (-η) η) →
        (∀ t ∈ Set.Icc (-η) η, (γ t) (σ 2) = c (σ 2) + u + t) →
        ContDiffOn ℝ 3 β (Set.Icc (-η) η) →
        (∀ t ∈ Set.Icc (-η) η, Work.BoxShrink.Pinch.par ψ (β t) = γ t ∧
          (γ t) (σ i) = c (σ i) + ev * Submission.boxSide i * s) →
        (∃ d ∈ D, deriv γ 0 - Work.BoxShrink.shiftVσ σ 1 = d) ∧
        (∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ arcE →
          ‖deriv γ t‖ ≤ arcM ∧ ‖deriv γ t - deriv γ 0‖ ≤ arcL * |t| ∧
          (deriv γ 0 = Work.BoxShrink.shiftVσ σ 1 →
            ‖deriv γ t - deriv γ 0‖ ≤ arcQ * t ^ 2))) := by
  classical
  let e : R3 := Work.BoxShrink.shiftVσ σ 1
  let B : Finset (FaceBranch ψ s u c σ) := branchFinset ψ s u c σ hX
  by_cases hB : B.Nonempty
  · have hbranch : ∀ bb : FaceBranch ψ s u c σ, ∃ (ρ M L Q : ℝ), bb ∈ B →
        (0 < ρ ∧ 0 < M ∧ 0 < L ∧ 0 < Q ∧
        ρ ≤ (arcDatum ψ s u c σ bb.i bb.ε bb.p).2.2 ∧
        (∀ t ∈ Set.Icc (-ρ) ρ,
          faceVertDet ψ σ bb.i 2 ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 t) ≠ 0) ∧
        (∀ t ∈ Set.Ioo (-ρ) ρ,
          ‖deriv (fun τ => Work.BoxShrink.Pinch.par ψ
            ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 τ)) t‖ ≤ M) ∧
        (∀ t ∈ Set.Ioo (-ρ) ρ,
          ‖deriv (fun τ => Work.BoxShrink.Pinch.par ψ
             ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 τ)) t -
           deriv (fun τ => Work.BoxShrink.Pinch.par ψ
             ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 τ)) 0‖ ≤ L * |t|) ∧
        (deriv (fun τ => Work.BoxShrink.Pinch.par ψ
             ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 τ)) 0 = e →
          ∀ t ∈ Set.Ioo (-ρ) ρ,
            ‖deriv (fun τ => Work.BoxShrink.Pinch.par ψ
               ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 τ)) t -
             deriv (fun τ => Work.BoxShrink.Pinch.par ψ
               ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 τ)) 0‖ ≤ Q * t ^ 2)) := by
      intro bb
      by_cases hbb : bb ∈ B
      · obtain ⟨ρ, M, L, Q, hP⟩ :=
          branchEstimates ψ c σ hX hFB bb.i bb.hi bb.ε bb.hε bb.p bb.hcross
        exact ⟨ρ, M, L, Q, fun _ => hP⟩
      · exact ⟨1, 1, 1, 1, fun h => absurd h hbb⟩
    choose ρc Mc Lc Qc hh using hbranch
    have hcoord2 : ∀ bb ∈ B, (deriv (fun τ => Work.BoxShrink.Pinch.par ψ
        ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 τ)) 0) (σ 2) = 1 := by
      intro bb _
      set q : ℝ → ℝ × ℝ := (arcDatum ψ s u c σ bb.i bb.ε bb.p).1 with hq
      set θ : ℝ := (arcDatum ψ s u c σ bb.i bb.ε bb.p).2.2 with hθ
      have hspec := arcDatum_spec ψ s u c σ bb.i bb.ε bb.p bb.hi bb.hε bb.hcross
        (hX bb.i bb.hi bb.ε bb.hε bb.p (congrArg Prod.fst bb.hcross)
          (congrArg Prod.snd bb.hcross))
      have hθpos : 0 < θ := by rw [hθ]; exact hspec.1
      have hq3 : ContDiffOn ℝ 3 q (Set.Icc (-θ) θ) := by rw [hq, hθ]; exact hspec.2.2.2.1
      have hH : ∀ t ∈ Set.Icc (-θ) θ,
          (Work.BoxShrink.Pinch.par ψ (q t)) (σ 2) = c (σ 2) + u + t := by
        intro t ht
        have ht' : t ∈ Set.Icc (-(arcDatum ψ s u c σ bb.i bb.ε bb.p).2.2)
            (arcDatum ψ s u c σ bb.i bb.ε bb.p).2.2 := by rw [hθ] at ht; exact ht
        exact congrArg Prod.snd (hspec.2.2.2.2.2.1 t ht')
      have hev : (fun t => (Work.BoxShrink.Pinch.par ψ (q t)) (σ 2)) =ᶠ[𝓝 (0:ℝ)]
          (fun t => c (σ 2) + u + t) :=
        Filter.eventually_of_mem (Icc_mem_nhds (by linarith) (by linarith)) (fun t ht => hH t ht)
      have h1 : deriv (fun t => (Work.BoxShrink.Pinch.par ψ (q t)) (σ 2)) 0 = 1 := by
        rw [Filter.EventuallyEq.deriv_eq hev]
        exact ((hasDerivAt_id (0:ℝ)).const_add (c (σ 2) + u)).deriv
      have h2 : deriv (fun t => (Work.BoxShrink.Pinch.par ψ (q t)) (σ 2)) 0 =
          (deriv (fun τ => Work.BoxShrink.Pinch.par ψ (q τ)) 0) (σ 2) := by
        have hd : DifferentiableAt ℝ (fun τ => Work.BoxShrink.Pinch.par ψ (q τ)) 0 :=
          ((Work.BoxShrink.Pinch.par_contDiff ψ).differentiable (by simp)).differentiableAt.comp 0
            ((hq3.contDiffAt (Icc_mem_nhds (by linarith) (by linarith))).differentiableAt
              (by norm_num))
        have h := deriv_clm_comp (coordCLM σ 2) (fun τ => Work.BoxShrink.Pinch.par ψ (q τ)) 0 hd
        simpa using h
      rw [← h2]
      exact h1
    set arcE : ℝ := (B.inf' hB ρc) / 2 with harcE
    set arcM : ℝ := B.sup' hB Mc with harcM
    set arcL : ℝ := B.sup' hB Lc with harcL
    set arcQ : ℝ := B.sup' hB Qc with harcQ
    set D : Finset R3 := B.image (fun bb => deriv (fun τ => Work.BoxShrink.Pinch.par ψ
      ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 τ)) 0 - e) with hD
    refine ⟨D, arcE, arcM, arcL, arcQ, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro d hd
      rw [hD] at hd
      obtain ⟨bb, hbb, rfl⟩ := Finset.mem_image.mp hd
      rw [inner_sub_right, inner_shiftVσ_one', inner_shiftVσ_one_self]
      have h := hcoord2 bb hbb
      linarith
    · rw [harcE]
      have h : 0 < B.inf' hB ρc := (Finset.lt_inf'_iff hB).mpr (fun i hi => (hh i hi).1)
      linarith
    · rw [harcM]
      refine (Finset.lt_sup'_iff hB).mpr ?_
      obtain ⟨b, hb⟩ := hB
      exact ⟨b, hb, (hh b hb).2.1⟩
    · rw [harcL]
      refine (Finset.lt_sup'_iff hB).mpr ?_
      obtain ⟨b, hb⟩ := hB
      exact ⟨b, hb, (hh b hb).2.2.1⟩
    · rw [harcQ]
      refine (Finset.lt_sup'_iff hB).mpr ?_
      obtain ⟨b, hb⟩ := hB
      exact ⟨b, hb, (hh b hb).2.2.2.1⟩
    · intro γ η i ev β hη hi hεv hγ3 hγh hβ3 hβγ
      have hp_cross := beta_zero_cross ψ c σ hη hβγ hγh
      obtain ⟨bb, hbbB, hbi, hbe, k, l, hpbb⟩ := exists_branch_of_cross ψ c σ hX hi hεv hp_cross
      set cc : ℝ × ℝ := ((k : ℝ) * (2 * Real.pi), (l : ℝ) * (2 * Real.pi)) with hcc
      have hspec := arcDatum_spec ψ s u c σ bb.i bb.ε bb.p bb.hi bb.hε bb.hcross
        (hX bb.i bb.hi bb.ε bb.hε bb.p (congrArg Prod.fst bb.hcross)
          (congrArg Prod.snd bb.hcross))
      have hθpos : 0 < (arcDatum ψ s u c σ bb.i bb.ε bb.p).2.2 := hspec.1
      have hq3 : ContDiffOn ℝ 3 (arcDatum ψ s u c σ bb.i bb.ε bb.p).1
          (Set.Icc (-(arcDatum ψ s u c σ bb.i bb.ε bb.p).2.2)
            (arcDatum ψ s u c σ bb.i bb.ε bb.p).2.2) := hspec.2.2.2.1
      have hq0 : (arcDatum ψ s u c σ bb.i bb.ε bb.p).1 0 = bb.p := hspec.2.2.2.2.1
      have hqcross := hspec.2.2.2.2.2.1
      have hρθ : ρc bb ≤ (arcDatum ψ s u c σ bb.i bb.ε bb.p).2.2 := (hh bb hbbB).2.2.2.2.1
      set arcE' : ℝ := min (ρc bb) η with harcE'
      have harcE'pos : 0 < arcE' := by rw [harcE']; exact lt_min (hh bb hbbB).1 hη
      have harcE'ρ : arcE' ≤ ρc bb := min_le_left _ _
      have harcE'η : arcE' ≤ η := min_le_right _ _
      have hKθ : Set.Icc (-arcE') arcE' ⊆
          Set.Icc (-(arcDatum ψ s u c σ bb.i bb.ε bb.p).2.2)
            (arcDatum ψ s u c σ bb.i bb.ε bb.p).2.2 := fun t ht =>
        ⟨by linarith [ht.1, harcE'ρ, hρθ], by linarith [ht.2, harcE'ρ, hρθ]⟩
      have hKη : Set.Icc (-arcE') arcE' ⊆ Set.Icc (-η) η := fun t ht =>
        ⟨by linarith [ht.1, harcE'η], by linarith [ht.2, harcE'η]⟩
      have hagree : ∀ t ∈ Set.Icc (-arcE') arcE',
          (arcDatum ψ s u c σ bb.i bb.ε bb.p).1 t + cc = β t := by
        refine eqOnOfFDerivInvertible (facePairMap ψ σ i)
          (fun x => (facePairMap_contDiff ψ σ i).hasStrictFDerivAt (by norm_num))
          isPreconnected_Icc ⟨by linarith, by linarith⟩ ?_ ?_ ?_ ?_ ?_
        · exact (hq3.mono hKθ).continuousOn.add continuousOn_const
        · exact hβ3.continuousOn.mono hKη
        · rw [hq0, ← hpbb]
        · intro t ht
          have hmemρ : t ∈ Set.Icc (-(ρc bb)) (ρc bb) :=
            ⟨by linarith [ht.1, harcE'ρ], by linarith [ht.2, harcE'ρ]⟩
          have hdet : faceVertDet ψ σ i 2 ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 t) ≠ 0 := by
            have h := (hh bb hbbB).2.2.2.2.2.1 t hmemρ
            simpa [hbi] using h
          have hqcc : (arcDatum ψ s u c σ bb.i bb.ε bb.p).1 t + cc =
              (((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 t).1 + (k : ℝ) * (2 * Real.pi),
                ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 t).2 + (l : ℝ) * (2 * Real.pi)) := by
            rw [hcc]; rfl
          rw [hqcc, fderiv_facePairMap_period ψ σ i ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 t) k l]
          exact isInvertible_facePairMap_of_faceVertDet_ne_zero ψ σ i _ hdet
        · intro t ht
          have hmemη : t ∈ Set.Icc (-η) η := hKη ht
          have hqcc : (arcDatum ψ s u c σ bb.i bb.ε bb.p).1 t + cc =
              (((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 t).1 + (k : ℝ) * (2 * Real.pi),
                ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 t).2 + (l : ℝ) * (2 * Real.pi)) := by
            rw [hcc]; rfl
          rw [hqcc, facePairMap_period ψ σ i ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 t) k l]
          have h1 : facePairMap ψ σ i ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 t) =
              (c (σ i) + ev * Submission.boxSide i * s, c (σ 2) + u + t) := by
            have h := hqcross t (hKθ ht)
            simpa [hbi, hbe] using h
          have h2 : facePairMap ψ σ i (β t) =
              (c (σ i) + ev * Submission.boxSide i * s, c (σ 2) + u + t) := by
            rw [Prod.ext_iff]
            refine ⟨?_, ?_⟩
            · show (Work.BoxShrink.Pinch.par ψ (β t)) (σ i) = _
              rw [(hβγ t hmemη).1]
              exact (hβγ t hmemη).2
            · show (Work.BoxShrink.Pinch.par ψ (β t)) (σ 2) = _
              rw [(hβγ t hmemη).1]
              exact hγh t hmemη
          rw [h1, h2]
      have hγμ : ∀ t ∈ Set.Icc (-arcE') arcE',
          γ t = Work.BoxShrink.Pinch.par ψ ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 t) := by
        intro t ht
        rw [← (hβγ t (hKη ht)).1, ← hagree t ht, hcc]
        exact Work.BoxShrink.Pinch.par_period ψ ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 t) k l
      have hderiv_eq : deriv γ 0 = deriv (fun τ => Work.BoxShrink.Pinch.par ψ
          ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 τ)) 0 := by
        have hev : γ =ᶠ[𝓝 (0:ℝ)] (fun τ => Work.BoxShrink.Pinch.par ψ
            ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 τ)) :=
          Filter.eventually_of_mem (Icc_mem_nhds (by linarith) (by linarith))
            (fun t ht => hγμ t ht)
        exact Filter.EventuallyEq.deriv_eq hev
      refine ⟨?_, fun t ht hle => ?_⟩
      · refine ⟨deriv (fun τ => Work.BoxShrink.Pinch.par ψ
            ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 τ)) 0 - e, ?_, ?_⟩
        · rw [hD]
          exact Finset.mem_image.mpr ⟨bb, hbbB, rfl⟩
        · rw [← hderiv_eq]
      · have hlt : |t| < arcE' := by
          refine lt_min ?_ ?_
          · have h1 : B.inf' hB ρc ≤ ρc bb := Finset.inf'_le ρc hbbB
            have h2 : 0 < B.inf' hB ρc := (Finset.lt_inf'_iff hB).mpr (fun i hi => (hh i hi).1)
            rw [harcE] at hle
            linarith
          · rw [abs_lt]
            exact ⟨ht.1, ht.2⟩
        have hmemK : t ∈ Set.Ioo (-arcE') arcE' := by
          rw [abs_lt] at hlt
          exact ⟨hlt.1, hlt.2⟩
        have htρ : t ∈ Set.Ioo (-(ρc bb)) (ρc bb) :=
          ⟨by linarith [hmemK.1, harcE'ρ], by linarith [hmemK.2, harcE'ρ]⟩
        have hdt : deriv γ t = deriv (fun τ => Work.BoxShrink.Pinch.par ψ
            ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 τ)) t := by
          have hev : γ =ᶠ[𝓝 t] (fun τ => Work.BoxShrink.Pinch.par ψ
              ((arcDatum ψ s u c σ bb.i bb.ε bb.p).1 τ)) :=
            Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hmemK)
              (fun s hs => hγμ s ⟨le_of_lt hs.1, le_of_lt hs.2⟩)
          exact Filter.EventuallyEq.deriv_eq hev
        have hMc : Mc bb ≤ arcM := by rw [harcM]; exact Finset.le_sup' Mc hbbB
        have hLc : Lc bb ≤ arcL := by rw [harcL]; exact Finset.le_sup' Lc hbbB
        have hQc : Qc bb ≤ arcQ := by rw [harcQ]; exact Finset.le_sup' Qc hbbB
        refine ⟨?_, ?_, ?_⟩
        · rw [hdt]
          exact le_trans ((hh bb hbbB).2.2.2.2.2.2.1 t htρ) hMc
        · rw [hdt, hderiv_eq]
          exact le_trans ((hh bb hbbB).2.2.2.2.2.2.2.1 t htρ)
            (mul_le_mul_of_nonneg_right hLc (abs_nonneg t))
        · intro hd0
          rw [hdt, hderiv_eq]
          refine le_trans ((hh bb hbbB).2.2.2.2.2.2.2.2 ?_ t htρ)
            (mul_le_mul_of_nonneg_right hQc (sq_nonneg t))
          rw [← hderiv_eq]
          exact hd0
  · -- `B` empty: there is no admissible arc
    refine ⟨∅, 1, 1, 1, 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · norm_num
    · norm_num
    · norm_num
    · norm_num
    · intro γ η i ev β hη hi hεv hγ3 hγh hβ3 hβγ
      obtain ⟨bb, hbbB, k, l, hpbb⟩ := exists_branch_of_cross ψ c σ hX hi hεv
        (beta_zero_cross ψ c σ hη hβγ hγh)
      exact absurd ⟨bb, hbbB⟩ hB

end
end Work.Drive.Mono
