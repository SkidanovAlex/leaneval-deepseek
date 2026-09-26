import Submission.Work.Drive.Mono.arcHeightAux
import Submission.Work.Drive.Mono.gammaArc_noBend
import Submission.Work.Drive.Mono.derivCoordModel
import Submission.Work.Drive.Mono.eqOnOfFDerivInvertible
import Submission.Work.Drive.Mono.quadBoundDerivZero

namespace Work.Drive.Mono
open LeanEval.KnotTheory.PardonDistortion MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace
open scoped _root_.Topology

noncomputable section

theorem branchEstimates (ψ : Submission.Diffeo) {s u : ℝ} (c : R3) (σ : Equiv.Perm (Fin 3))
    (hX : FaceCrossReg ψ c σ s u) (hFB : FaceNoBend ψ c σ s u)
    (i : Fin 3) (hi : i ≠ 2) (ε : ℝ) (hε : ε = 1 ∨ ε = -1) (p : ℝ × ℝ)
    (hp : facePairMap ψ σ i p = (c (σ i) + ε * Submission.boxSide i * s, c (σ 2) + u)) :
    ∃ (ρ M L Q : ℝ), 0 < ρ ∧ 0 < M ∧ 0 < L ∧ 0 < Q ∧
      ρ ≤ (arcDatum ψ s u c σ i ε p).2.2 ∧
      (∀ t ∈ Set.Icc (-ρ) ρ, faceVertDet ψ σ i 2 ((arcDatum ψ s u c σ i ε p).1 t) ≠ 0) ∧
      (∀ t ∈ Set.Ioo (-ρ) ρ,
        ‖deriv (fun τ => Work.BoxShrink.Pinch.par ψ ((arcDatum ψ s u c σ i ε p).1 τ)) t‖ ≤ M) ∧
      (∀ t ∈ Set.Ioo (-ρ) ρ,
        ‖deriv (fun τ => Work.BoxShrink.Pinch.par ψ ((arcDatum ψ s u c σ i ε p).1 τ)) t -
         deriv (fun τ => Work.BoxShrink.Pinch.par ψ ((arcDatum ψ s u c σ i ε p).1 τ)) 0‖
          ≤ L * |t|) ∧
      (deriv (fun τ => Work.BoxShrink.Pinch.par ψ ((arcDatum ψ s u c σ i ε p).1 τ)) 0 =
          Work.BoxShrink.shiftVσ σ 1 →
        ∀ t ∈ Set.Ioo (-ρ) ρ,
          ‖deriv (fun τ => Work.BoxShrink.Pinch.par ψ ((arcDatum ψ s u c σ i ε p).1 τ)) t -
           deriv (fun τ => Work.BoxShrink.Pinch.par ψ ((arcDatum ψ s u c σ i ε p).1 τ)) 0‖
            ≤ Q * t ^ 2) := by
  classical
  set q : ℝ → ℝ × ℝ := (arcDatum ψ s u c σ i ε p).1 with hq
  set θ : ℝ := (arcDatum ψ s u c σ i ε p).2.2 with hθ
  set μ : ℝ → R3 := fun t => Work.BoxShrink.Pinch.par ψ (q t) with hμ
  have hinv0 : (fderiv ℝ (facePairMap ψ σ i) p).IsInvertible :=
    hX i hi ε hε p (congrArg Prod.fst hp) (congrArg Prod.snd hp)
  have hspec := arcDatum_spec ψ s u c σ i ε p hi hε hp hinv0
  obtain ⟨hθpos0, hUmem, hUopen, hq3, hq0, hqcross, hqinv⟩ := hspec
  have hθpos : 0 < θ := by rw [hθ]; exact hθpos0
  have hq3' : ContDiffOn ℝ 3 q (Set.Icc (-θ) θ) := by rw [hq, hθ]; exact hq3
  have hq0' : q 0 = p := by rw [hq]; exact hq0
  have hqcross' : ∀ t ∈ Set.Icc (-θ) θ, facePairMap ψ σ i (q t) =
      (c (σ i) + ε * Submission.boxSide i * s, c (σ 2) + u + t) := by
    intro t ht
    rw [hθ] at ht
    exact hqcross t ht
  -- coordinate identities
  have hcoordi : ∀ t ∈ Set.Icc (-θ) θ, coordFun ψ σ i (q t) =
      c (σ i) + ε * Submission.boxSide i * s := fun t ht =>
    congrArg Prod.fst (hqcross' t ht)
  have hcoord2 : ∀ t ∈ Set.Icc (-θ) θ, coordFun ψ σ 2 (q t) = c (σ 2) + u + t := fun t ht =>
    congrArg Prod.snd (hqcross' t ht)
  -- differentiability of mu
  have hμ3 : ContDiffOn ℝ 3 μ (Set.Icc (-θ) θ) :=
    ContDiff.fun_comp_contDiffOn
      ((Work.BoxShrink.Pinch.par_contDiff ψ).of_le (by decide)) hq3'
  -- the determinant is nonzero near 0
  have hdet0 : faceVertDet ψ σ i 2 p ≠ 0 :=
    faceVertDet_two_ne_zero_of_invertible ψ σ i hinv0
  have hq_contAt0 : ContinuousAt q 0 :=
    hq3'.continuousOn.continuousAt (Icc_mem_nhds (by linarith) (by linarith))
  have hcontdet : ContinuousAt (fun t => faceVertDet ψ σ i 2 (q t)) 0 :=
    ((continuous_faceVertDet ψ σ i 2).continuousAt).comp hq_contAt0
  have hev : ∀ᶠ t in 𝓝 (0:ℝ), faceVertDet ψ σ i 2 (q t) ≠ 0 := by
    refine hcontdet.eventually_ne ?_
    rw [hq0']; exact hdet0
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhds_iff.mp hev
  set ρ : ℝ := min (δ/2) (θ/2) with hρ
  have hρpos : 0 < ρ := lt_min (by linarith) (by linarith)
  have hρθ : ρ ≤ θ := by
    rw [hρ]; linarith [min_le_right (δ/2) (θ/2), hθpos]
  have hρlt : ρ < θ := by
    rw [hρ]; linarith [min_le_right (δ/2) (θ/2), hθpos]
  have hρdet : ∀ t ∈ Set.Icc (-ρ) ρ, faceVertDet ψ σ i 2 (q t) ≠ 0 := by
    intro t ht
    refine hδsub ?_
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    have h1 : |t| ≤ ρ := abs_le.mpr ⟨ht.1, ht.2⟩
    rw [hρ] at h1
    linarith [min_le_left (δ/2) (θ/2), hδpos]
  -- local differentiability facts
  have h0mem : (0:ℝ) ∈ Set.Icc (-ρ) ρ := ⟨by linarith, by linarith⟩
  have hmemθ : ∀ t ∈ Set.Icc (-ρ) ρ, Set.Icc (-θ) θ ∈ 𝓝 t := by
    intro t ht
    exact Icc_mem_nhds (by linarith [ht.1, hρlt]) (by linarith [ht.2, hρlt])
  have hderivAt2 : ∀ t ∈ Set.Icc (-ρ) ρ, ContDiffAt ℝ 2 (deriv μ) t := fun t ht =>
    (hμ3.contDiffAt (hmemθ t ht)).derivWithin (by norm_num)
  have hderivAt1 : ∀ t ∈ Set.Icc (-ρ) ρ, ContDiffAt ℝ 1 (deriv (deriv μ)) t := fun t ht =>
    (hderivAt2 t ht).derivWithin (by norm_num)
  have hcd2 : ContDiffOn ℝ 2 (deriv μ) (Set.Icc (-ρ) ρ) := fun t ht =>
    (hderivAt2 t ht).contDiffWithinAt
  have hcont2 : ContinuousOn (deriv μ) (Set.Icc (-ρ) ρ) := hcd2.continuousOn
  obtain ⟨M0, hM0⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont2
  set M : ℝ := max M0 1 with hM
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hMbound : ∀ t ∈ Set.Ioo (-ρ) ρ, ‖deriv μ t‖ ≤ M := fun t ht =>
    le_trans (hM0 t ⟨le_of_lt ht.1, le_of_lt ht.2⟩) (le_max_left _ _)
  -- the Lipschitz bound
  have hcont1 : ContinuousOn (deriv (deriv μ)) (Set.Icc (-ρ) ρ) := fun t ht =>
    ((hderivAt1 t ht).continuousAt).continuousWithinAt
  obtain ⟨L0, hL0⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont1
  set L : ℝ := max L0 1 with hL
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hLbound0 : ∀ x ∈ Set.Icc (-ρ) ρ, ‖deriv (deriv μ) x‖ ≤ L := fun x hx =>
    le_trans (hL0 x hx) (le_max_left _ _)
  have hLbound : ∀ t ∈ Set.Ioo (-ρ) ρ, ‖deriv μ t - deriv μ 0‖ ≤ L * |t| := by
    intro t ht
    by_cases ht0 : 0 ≤ t
    · have hsub : Set.Icc (0:ℝ) ρ ⊆ Set.Icc (-ρ) ρ := fun x hx =>
        ⟨by linarith [hx.1], hx.2⟩
      have h1 := norm_image_sub_le_of_norm_deriv_le_segment'
        (f := deriv μ) (f' := deriv (deriv μ)) (C := L) (a := 0) (b := ρ)
        (fun x hx => ((hderivAt2 x (hsub hx)).differentiableAt (by norm_num)).hasDerivAt
          |>.hasDerivWithinAt.mono hsub)
        (fun x hx => hLbound0 x (hsub ⟨hx.1, le_of_lt hx.2⟩))
        t ⟨ht0, le_of_lt ht.2⟩
      rw [sub_zero] at h1
      calc ‖deriv μ t - deriv μ 0‖ ≤ L * t := h1
        _ = L * |t| := by rw [abs_of_nonneg ht0]
    · have ht0' : t < 0 := lt_of_not_ge ht0
      have hsub : Set.Icc t 0 ⊆ Set.Icc (-ρ) ρ := fun x hx =>
        ⟨by linarith [hx.1, ht.1], by linarith [hx.2, hρpos]⟩
      have h1 := norm_image_sub_le_of_norm_deriv_le_segment'
        (f := deriv μ) (f' := deriv (deriv μ)) (C := L) (a := t) (b := 0)
        (fun x hx => ((hderivAt2 x (hsub hx)).differentiableAt (by norm_num)).hasDerivAt
          |>.hasDerivWithinAt.mono hsub)
        (fun x hx => hLbound0 x (hsub ⟨hx.1, le_of_lt hx.2⟩))
        0 ⟨le_of_lt ht0', le_refl 0⟩
      calc ‖deriv μ t - deriv μ 0‖ = ‖deriv μ 0 - deriv μ t‖ := by rw [norm_sub_rev]
        _ ≤ L * (0 - t) := h1
        _ = L * |t| := by rw [abs_of_neg ht0']; ring
  -- the quadratic bound
  have hquad : deriv μ 0 = Work.BoxShrink.shiftVσ σ 1 → ∃ Q : ℝ, 0 < Q ∧
      ∀ t ∈ Set.Ioo (-ρ) ρ, ‖deriv μ t - deriv μ 0‖ ≤ Q * t ^ 2 := by
    intro hd0
    have hnb : deriv (deriv μ) 0 = 0 :=
      gammaArc_noBend ψ c σ hX hFB hθpos (γ := μ) hi hε (β := q) hq3'
        (fun t ht => ⟨rfl, hcoordi t ht⟩) (fun t ht => hcoord2 t ht) hd0
    have hcoordk : ∀ k : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ioo (-ρ) ρ,
        |(deriv μ t) (σ k) - (deriv μ 0) (σ k)| ≤ C * t ^ 2 := by
      intro k
      set F : ℝ → ℝ := fun t => coordCLM σ k (deriv μ t) - coordCLM σ k (deriv μ 0) with hF
      have hF2 : ContDiffOn ℝ 2 F (Set.Icc (-ρ) ρ) := by
        have h1 : ContDiffOn ℝ 2 (fun t => coordCLM σ k (deriv μ t)) (Set.Icc (-ρ) ρ) := by
          fun_prop
        exact h1.sub contDiffOn_const
      have hF0 : F 0 = 0 := by rw [hF]; exact sub_self _
      have hF1 : deriv F 0 = 0 := by
        have hFG : F = fun t => coordCLM σ k (deriv μ t) + (- coordCLM σ k (deriv μ 0)) := by
          funext t; exact sub_eq_add_neg _ _
        rw [hFG, deriv_add_const]
        rw [deriv_clm_comp (coordCLM σ k) (deriv μ) 0
          ((hderivAt2 0 h0mem).differentiableAt (by norm_num))]
        rw [hnb]
        simp
      obtain ⟨C, hC0, hC⟩ := quadBoundDerivZero hρpos hF2 hF0 hF1
      exact ⟨C, hC0, fun t ht => by simpa [hF] using hC t ht⟩
    choose Ck hCk0 hCk using hcoordk
    have hsum : (0:ℝ) ≤ ∑ k : Fin 3, Ck k := Finset.sum_nonneg (fun k _ => hCk0 k)
    refine ⟨(∑ k : Fin 3, Ck k) + 1, by linarith, ?_⟩
    intro t ht
    have h1 : ‖deriv μ t - deriv μ 0‖ ≤
        ∑ k : Fin 3, |(deriv μ t) (σ k) - (deriv μ 0) (σ k)| := by
      have h := norm_le_sum_abs_coord σ (deriv μ t - deriv μ 0)
      simpa [Pi.sub_apply] using h
    have h2 : ∑ k : Fin 3, |(deriv μ t) (σ k) - (deriv μ 0) (σ k)|
        ≤ ∑ k : Fin 3, Ck k * t ^ 2 :=
      Finset.sum_le_sum (fun k _ => hCk k t ht)
    have h3 : (∑ k : Fin 3, Ck k * t ^ 2) = (∑ k : Fin 3, Ck k) * t ^ 2 := by
      rw [Finset.sum_mul]
    have h4 : (∑ k : Fin 3, Ck k) * t ^ 2 ≤ ((∑ k : Fin 3, Ck k) + 1) * t ^ 2 := by
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg t)
      linarith
    linarith [h1, h2, h3.trans_le h4]
  have hQexists : ∃ Q : ℝ, 0 < Q ∧ ∀ t ∈ Set.Ioo (-ρ) ρ,
      (deriv μ 0 = Work.BoxShrink.shiftVσ σ 1 →
        ‖deriv μ t - deriv μ 0‖ ≤ Q * t ^ 2) := by
    by_cases hd0 : deriv μ 0 = Work.BoxShrink.shiftVσ σ 1
    · obtain ⟨Q, hQpos, hQb⟩ := hquad hd0
      exact ⟨Q, hQpos, fun t ht _ => hQb t ht⟩
    · exact ⟨1, one_pos, fun t ht h => absurd h hd0⟩
  obtain ⟨Q, hQpos, hQbound⟩ := hQexists
  exact ⟨ρ, M, L, Q, hρpos, hMpos, hLpos, hQpos, hρθ, hρdet, hMbound, hLbound,
    fun hd0 t ht => hQbound t ht hd0⟩


/-- **A crossing point of a face with the cutting plane lies on a branch**, up to a period. -/
theorem exists_branch_of_cross (ψ : Submission.Diffeo) {s u : ℝ} (c : R3)
    (σ : Equiv.Perm (Fin 3)) (hX : FaceCrossReg ψ c σ s u)
    {i : Fin 3} {ev : ℝ} {p : ℝ × ℝ} (hi : i ≠ 2) (hεv : ev = 1 ∨ ev = -1)
    (hp : facePairMap ψ σ i p =
      (c (σ i) + ev * Submission.boxSide i * s, c (σ 2) + u)) :
    ∃ bb ∈ branchFinset ψ s u c σ hX, bb.i = i ∧ bb.ε = ev ∧ ∃ k l : ℤ,
      p = bb.p + ((k : ℝ) * (2 * Real.pi), (l : ℝ) * (2 * Real.pi)) := by
  classical
  obtain ⟨p', hp'fund, k, l, hp'1, hp'2⟩ := exists_mem_arcFundBox_add_period p
  have hp'_cross : facePairMap ψ σ i p' =
      (c (σ i) + ev * Submission.boxSide i * s, c (σ 2) + u) := by
    have hper := facePairMap_period ψ σ i p' k l
    rw [← hper]
    have hpp : ((p'.1 + (k:ℝ)*(2*Real.pi), p'.2 + (l:ℝ)*(2*Real.pi)) : ℝ × ℝ) = p := by
      rw [Prod.ext_iff]; exact ⟨hp'1, hp'2⟩
    rw [hpp]
    exact hp
  refine ⟨⟨i, ev, p', hi, hεv, hp'fund, hp'_cross⟩, mem_branchFinset hi hεv
    (mem_crossSet.mpr ⟨hp'fund, hp'_cross⟩), rfl, rfl, k, l, ?_⟩
  show p = (p'.1 + (k:ℝ)*(2*Real.pi), p'.2 + (l:ℝ)*(2*Real.pi))
  rw [Prod.ext_iff]
  exact ⟨hp'1.symm, hp'2.symm⟩


end
end Work.Drive.Mono
