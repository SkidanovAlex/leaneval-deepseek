import Mathlib
import Submission.Work.WilE7.FrontierCS.Defs
import Submission.Work.WilE7.FrontierCS.grid_cover
import Submission.Work.WilE7.FrontierCS.isOpen_fst_image_sliceSet
import Submission.Work.WilE7.FrontierCS.exists_complement
import Submission.Work.WilE7.FrontierCS.mem_closure_preimage
import Submission.Work.WilE7.FrontierCS.exists_open_subset_of_finite_closed_cover
import Submission.Work.WilE7.FrontierCS.exists_mem_iInter_of_dense_in_open

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open scoped Topology

namespace Work.WilE7.FrontierCS

/-- The slice chart `sliceChart γ B Λ` of an entire germ `γ` is entire. -/
lemma analyticOnNhd_sliceChart {N d j : ℕ} {γ : (Fin d → ℝ) → (Fin N → ℝ)}
    (hγ : AnalyticOnNhd ℝ γ Set.univ) (B : (Fin j → ℝ) →L[ℝ] (Fin N → ℝ))
    (Λ : Matrix (Fin d) (Fin j) ℝ) :
    AnalyticOnNhd ℝ (sliceChart γ B Λ) Set.univ := by
  have h1 : AnalyticOnNhd ℝ
      (fun p : (Fin d → ℝ) × (Fin j → ℝ) => γ (p.1 + Λ.mulVec p.2)) Set.univ :=
    hγ.comp (((ContinuousLinearMap.fst ℝ (Fin d → ℝ) (Fin j → ℝ)) +
      (matCLM Λ).comp (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (Fin j → ℝ))).analyticOnNhd
        Set.univ) (fun x _ => Set.mem_univ _)
  have h2 : AnalyticOnNhd ℝ
      (fun p : (Fin d → ℝ) × (Fin j → ℝ) => B p.2) Set.univ :=
    (B.comp (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (Fin j → ℝ))).analyticOnNhd Set.univ
  have heq : sliceChart γ B Λ =
      (fun p : (Fin d → ℝ) × (Fin j → ℝ) => γ (p.1 + Λ.mulVec p.2)) +
      (fun p : (Fin d → ℝ) × (Fin j → ℝ) => B p.2) := rfl
  rw [heq]; exact h1.add h2

/-- `sliceChart γ B Λ (τ, 0) = γ τ`. -/
lemma sliceChart_zero {N d j : ℕ} (γ : (Fin d → ℝ) → (Fin N → ℝ))
    (B : (Fin j → ℝ) →L[ℝ] (Fin N → ℝ)) (Λ : Matrix (Fin d) (Fin j) ℝ) (τ : Fin d → ℝ) :
    sliceChart γ B Λ (τ, (0 : Fin j → ℝ)) = γ τ := by
  simp [sliceChart]

theorem slice_reduction {N d j : ℕ} (hdj : d + j = N) (hj : 0 < j) {G : (Fin N → ℝ) → (Fin j → ℝ)}
    (hG : AnalyticOnNhd ℝ G Set.univ) {W : Set (Fin N → ℝ)}
    (hWZ : ∀ w ∈ W, G w = 0)
    (hWopen : ∀ w ∈ W, ∃ U ∈ nhds w, ∀ z ∈ U, G z = 0 → z ∈ W)
    (hWrk : ∀ w ∈ W, (fderiv ℝ G w).range = ⊤)
    {γ : (Fin d → ℝ) → (Fin N → ℝ)} (hγ : AnalyticOnNhd ℝ γ Set.univ)
    (hγinj : Function.Injective (fderiv ℝ γ (0 : Fin d → ℝ)))
    (hγW : Filter.Eventually (fun s => γ s ∈ closure W \ W) (nhds (0 : Fin d → ℝ))) :
    ∃ g : (Fin j → ℝ) → (Fin j → ℝ), AnalyticOnNhd ℝ g Set.univ ∧
      (0 : Fin j → ℝ) ∈ closure {e | e ≠ 0 ∧ g e = 0 ∧ (fderiv ℝ g e).range = ⊤} := by
  -- N3: a linear complement `B` to the injective `fderiv γ 0`.
  obtain ⟨B, hB⟩ := exists_complement hdj (fderiv ℝ γ 0) hγinj
  -- `γ` eventually lands in `closure W`.
  have hγC : ∀ᶠ s in nhds (0 : Fin d → ℝ), γ s ∈ closure W :=
    hγW.mono (fun s hs => hs.1)
  -- N5: grid cover.
  have hgrid := grid_cover hG hWrk hγ hB hγC
  obtain ⟨εg, hεg, hεgball⟩ := Metric.mem_nhds_iff.mp hgrid
  obtain ⟨ε0, hε0, hε0ball⟩ := Metric.mem_nhds_iff.mp hγW
  -- The (finitely many) closed sets of `τ`s on which one grid slope works.
  set C : (Fin d → Fin j → Bool) → Set (Fin d → ℝ) :=
    fun b => {τ | (τ, (0 : Fin j → ℝ)) ∈
      closure (sliceSet G W (sliceChart γ B (gridMat b)))} with hC
  have hCclosed : ∀ b, IsClosed (C b) := by
    intro b
    have hbc : C b = {τ : Fin d → ℝ | (τ, (0 : Fin j → ℝ)) ∈
        closure (sliceSet G W (sliceChart γ B (gridMat b)))} := by rw [hC]
    rw [hbc]
    exact isClosed_closure.preimage (continuous_id.prodMk continuous_const)
  have hcov : Metric.ball (0 : Fin d → ℝ) (min εg ε0) ⊆ ⋃ b, C b := by
    intro τ hτ
    have hτg : τ ∈ Metric.ball (0 : Fin d → ℝ) εg :=
      Metric.ball_subset_ball (min_le_left _ _) hτ
    obtain ⟨b, hb⟩ := hεgball hτg
    refine Set.mem_iUnion.mpr ⟨b, ?_⟩
    show τ ∈ C b
    rw [hC]
    exact hb
  -- N7a: one slope works on a nonempty open set `V'`.
  obtain ⟨b, V', hV'open, hV'ne, hV'sub, hV'C⟩ :=
    exists_open_subset_of_finite_closed_cover
      (Metric.isOpen_ball (x := (0 : Fin d → ℝ)) (ε := min εg ε0))
      ⟨0, Metric.mem_ball_self (lt_min hεg hε0)⟩ C hCclosed hcov
  have hV'good : ∀ τ ∈ V', γ τ ∈ closure W \ W := fun τ hτ =>
    hε0ball (Metric.ball_subset_ball (min_le_right _ _) (hV'sub hτ))
  -- The chosen slice chart.
  set ψ : (Fin d → ℝ) × (Fin j → ℝ) → (Fin N → ℝ) := sliceChart γ B (gridMat b) with hψ
  have hψan : AnalyticOnNhd ℝ ψ Set.univ := by
    rw [hψ]; exact analyticOnNhd_sliceChart hγ B (gridMat b)
  have hV'Cb : ∀ τ ∈ V', (τ, (0 : Fin j → ℝ)) ∈ closure (sliceSet G W ψ) := by
    intro τ hτ
    have h1 : (τ, (0 : Fin j → ℝ)) ∈ closure (sliceSet G W (sliceChart γ B (gridMat b))) := by
      have h := hV'C hτ
      rwa [hC] at h
    rw [hψ]
    exact h1
  -- N6: the slices cut by a shrinking tube have open `fst`-image.
  set O : ℕ → Set (Fin d → ℝ) := fun k => Prod.fst ''
    ({p : (Fin d → ℝ) × (Fin j → ℝ) | ‖p.2‖ < 1 / ((k : ℝ) + 1)} ∩ sliceSet G W ψ) with hO
  have hOopen : ∀ k, IsOpen (O k) := by
    intro k
    have hUopen : IsOpen {p : (Fin d → ℝ) × (Fin j → ℝ) | ‖p.2‖ < 1 / ((k : ℝ) + 1)} :=
      isOpen_lt (continuous_norm.comp continuous_snd) continuous_const
    have hmain := isOpen_fst_image_sliceSet (d := d) hj hG hWZ hWopen hψan hUopen
    rw [hO]
    exact hmain
  -- `O k` is dense in `V'`.
  have hdense : ∀ k, V' ⊆ closure (O k) := by
    intro k τ hτ
    have hcl : (τ, (0 : Fin j → ℝ)) ∈ closure (sliceSet G W ψ) := hV'Cb τ hτ
    have hUopen : IsOpen {p : (Fin d → ℝ) × (Fin j → ℝ) | ‖p.2‖ < 1 / ((k : ℝ) + 1)} :=
      isOpen_lt (continuous_norm.comp continuous_snd) continuous_const
    have hmem : (τ, (0 : Fin j → ℝ)) ∈ closure
        ({p : (Fin d → ℝ) × (Fin j → ℝ) | ‖p.2‖ < 1 / ((k : ℝ) + 1)}
          ∩ sliceSet G W ψ) := by
      rw [mem_closure_iff_nhds]
      intro U hU
      have hUn : U ∩ {p : (Fin d → ℝ) × (Fin j → ℝ) | ‖p.2‖ < 1 / ((k : ℝ) + 1)} ∈
          nhds (τ, (0 : Fin j → ℝ)) :=
        Filter.inter_mem hU (hUopen.mem_nhds (by
          simp only [Set.mem_ofPred_eq, norm_zero]; positivity))
      obtain ⟨q, hq⟩ := (mem_closure_iff_nhds.mp hcl)
        (U ∩ {p : (Fin d → ℝ) × (Fin j → ℝ) | ‖p.2‖ < 1 / ((k : ℝ) + 1)}) hUn
      exact ⟨q, hq.1.1, hq.1.2, hq.2⟩
    have himg := image_closure_subset_closure_image (f := Prod.fst) continuous_fst
      (s := ({p : (Fin d → ℝ) × (Fin j → ℝ) | ‖p.2‖ < 1 / ((k : ℝ) + 1)}
        ∩ sliceSet G W ψ))
    have hmem' : τ ∈ closure (Prod.fst ''
        ({p : (Fin d → ℝ) × (Fin j → ℝ) | ‖p.2‖ < 1 / ((k : ℝ) + 1)}
          ∩ sliceSet G W ψ)) :=
      himg ⟨(τ, (0 : Fin j → ℝ)), hmem, rfl⟩
    rw [hO]
    exact hmem'
  -- N7b: Baire.
  obtain ⟨τ₀, hτ₀V, hτ₀O⟩ :=
    exists_mem_iInter_of_dense_in_open hV'open hV'ne O hOopen hdense
  -- The points `e k` with `(τ₀, e k) ∈ sliceSet` and `‖e k‖ < 1/(k+1)`.
  have hchoice : ∀ k : ℕ, ∃ e : Fin j → ℝ,
      (τ₀, e) ∈ ({p : (Fin d → ℝ) × (Fin j → ℝ) | ‖p.2‖ < 1 / ((k : ℝ) + 1)}
        ∩ sliceSet G W ψ) := by
    intro k
    have hmemk : τ₀ ∈ Prod.fst ''
        ({p : (Fin d → ℝ) × (Fin j → ℝ) | ‖p.2‖ < 1 / ((k : ℝ) + 1)} ∩ sliceSet G W ψ) :=
      hτ₀O k
    rw [Set.mem_image] at hmemk
    obtain ⟨p, hp, hp1⟩ := hmemk
    refine ⟨p.2, ?_⟩
    have hpe : (τ₀, p.2) = p := by rw [← hp1]
    rw [hpe]; exact hp
  choose e he using hchoice
  have he_slice : ∀ k, (τ₀, e k) ∈ sliceSet G W ψ := fun k => (he k).2
  have he_small : ∀ k, ‖e k‖ < 1 / ((k : ℝ) + 1) := fun k => (he k).1
  have he_ne : ∀ k, e k ≠ 0 := by
    intro k hk
    have hmemW : ψ (τ₀, e k) ∈ W := (he_slice k).1
    rw [hk] at hmemW
    have hψ0 : ψ (τ₀, (0 : Fin j → ℝ)) = γ τ₀ := by rw [hψ]; exact sliceChart_zero γ B (gridMat b) τ₀
    rw [hψ0] at hmemW
    exact (hV'good τ₀ hτ₀V).2 hmemW
  -- The resulting entire square system `g`.
  set g : (Fin j → ℝ) → (Fin j → ℝ) := fun e => G (ψ (τ₀, e)) with hg_def
  refine ⟨g, ?_, ?_⟩
  · -- analyticity of `g`
    have hψG : AnalyticOnNhd ℝ (fun p : (Fin d → ℝ) × (Fin j → ℝ) => G (ψ p)) Set.univ :=
      hG.comp hψan (fun x _ => Set.mem_univ _)
    have hpair : AnalyticOnNhd ℝ (fun e : Fin j → ℝ => (τ₀, e)) Set.univ :=
      fun x _ => analyticAt_const.prod analyticAt_id
    have hcomp := hψG.comp hpair (fun x _ => Set.mem_univ _)
    have hgoal : g = ((fun p : (Fin d → ℝ) × (Fin j → ℝ) => G (ψ p)) ∘
        (fun e : Fin j → ℝ => (τ₀, e))) := rfl
    rw [hgoal]; exact hcomp
  · -- the nondegenerate zeros `e k` accumulate at `0`
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨k, hk⟩ := exists_nat_gt (1 / ε)
    have hk' : (1 : ℝ) < ε * (k : ℝ) := by rw [div_lt_iff₀ hε] at hk; linarith
    refine ⟨e k, ⟨he_ne k, ?_, ?_⟩, ?_⟩
    · show g (e k) = 0
      rw [hg_def]
      exact hWZ (ψ (τ₀, e k)) (he_slice k).1
    · show (fderiv ℝ g (e k)).range = ⊤
      have h2 := (he_slice k).2
      simpa [hg_def] using h2
    · rw [dist_comm, dist_eq_norm, sub_zero]
      have h1 : 1 / ((k : ℝ) + 1) < ε := by
        rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (k : ℝ) + 1)]
        nlinarith [hk', hε]
      exact lt_of_lt_of_le (he_small k) h1.le

end Work.WilE7.FrontierCS
