import Mathlib
import Submission.Work.Drive.Mono.Band.HeightGoodDefs
import Submission.Work.Drive.EpsForm.critTrackExists
import Submission.Work.Drive.EpsForm.critBranchLocal
import Submission.Work.Drive.EpsForm.goodHeight_exists
import Submission.Work.Drive.Mono.Band.no_crit_off_isCompact
import Submission.Work.Drive.Mono.Band.continuous_fderiv_fderiv_snd
import Submission.Work.Drive.Mono.Band.branch_lattice_shift

open scoped _root_.Topology

namespace Work.Drive.Mono.Band

open LeanEval.KnotTheory.PardonDistortion

noncomputable section

/-- **The set of good height directions is open.**

`HeightGood ψ n` (see `Work.Drive.Mono.Band.HeightGoodDefs`) says that the height
`heightIn ψ n = fun q => ⟪n, par ψ q⟫` has injective Hessian at every critical point and that two
critical points with the same value have the same image on the surface.

The proof has two halves.

* *Nondegeneracy.*  A degenerate critical point can be moved into the fundamental square
  `[0,2π] × [0,2π]` without changing the criticality, the value or the Hessian
  (`Work.Drive.EpsForm.exists_fundBox_of_crit` in `goodHeight_exists.lean`), so if `n_k → n₀` all
  had degenerate critical points, a subsequence of the (compact) fundamental-square witnesses would
  converge to one for `n₀`, contradicting `HeightGood ψ n₀`.  (The Hessian of `heightIn ψ n` at `p`
  is continuous in `(n,p)`, and injectivity of a linear map is an open condition.)

* *Injectivity of the values.*  This half needs the *uniqueness of the critical point of a Morse
  height near a nondegenerate critical point*: `Work.Drive.EpsForm.critBranchLocal`
  (`Submission/Work/Drive/EpsForm/critBranchLocal.lean`) applied at `n₀` to the (finite) set `X` of
  critical points of `heightIn ψ n₀` in the fundamental square gives radii `ε, δ > 0` and branches
  `y x n` such that, for `‖n - n₀‖ < δ`, `y x n` is *the only* critical point of `heightIn ψ n`
  within distance `ε` of `x`, with `y x n₀ = x`.

  Suppose then that `n₀` is good but `n_k → n₀` are all bad: there are critical `p_k, p'_k`
  (movable into the fundamental square, keeping value and image) with equal values and
  `par ψ p_k ≠ par ψ p'_k`.  Pass to a subsequence with `p_k → p*`, `p'_k → p'*`; both are critical
  for `n₀` with equal value, so `par ψ p* = par ψ p'*`, i.e. `p'* = p* + c` with `c` in the
  `2π`-lattice (`Work.Drive.EpsForm.par_eq_iff`).  For large `k` the point `p'_k - c` is a critical
  point of `heightIn ψ n_k` at distance `< ε` from `p*`, and so is `p_k` (of which `p_k = y p* n_k`
  by uniqueness); hence `p'_k - c = p_k`, so `par ψ p'_k = par ψ p_k`, a contradiction. -/
theorem heightGood_open (ψ : Submission.Diffeo) {n₀ : LeanEval.KnotTheory.PardonDistortion.R3}
    (h : Work.Drive.Mono.Band.HeightGood ψ n₀) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ n : LeanEval.KnotTheory.PardonDistortion.R3,
      ‖n - n₀‖ < ρ → Work.Drive.Mono.Band.HeightGood ψ n := by
  classical
  unfold Work.Drive.Mono.Band.HeightGood at h
  -- ## 1. the critical points of the base height inside the fundamental square
  have hndH : ∀ p : ℝ × ℝ, fderiv ℝ (heightIn ψ n₀) p = 0 →
      Function.Injective (fderiv ℝ (fderiv ℝ (heightIn ψ n₀)) p) := h.1
  have hvalH : ∀ p p' : ℝ × ℝ, fderiv ℝ (heightIn ψ n₀) p = 0 →
      fderiv ℝ (heightIn ψ n₀) p' = 0 → heightIn ψ n₀ p = heightIn ψ n₀ p' →
      Work.BoxShrink.Pinch.par ψ p = Work.BoxShrink.Pinch.par ψ p' := h.2
  have hfin : ({p : ℝ × ℝ | fderiv ℝ (heightIn ψ n₀) p = 0} ∩
      Work.Drive.EpsForm.fundBox).Finite := by
    simpa only [Work.Drive.EpsForm.fundBox, heightIn_eq_heightOf] using
      (Work.Drive.EpsForm.finite_critSet_box (Work.Drive.EpsForm.heightOf_contDiff_two ψ n₀)
        (fun p hp => hndH p hp))
  obtain ⟨X, memX⟩ : ∃ X : Finset (ℝ × ℝ), ∀ p : ℝ × ℝ,
      p ∈ X ↔ fderiv ℝ (heightIn ψ n₀) p = 0 ∧ p ∈ Work.Drive.EpsForm.fundBox :=
    ⟨hfin.toFinset, fun p => by
      rw [Set.Finite.mem_toFinset]
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]⟩
  -- ## 2. branches of the critical points, unique near their base point
  obtain ⟨y, ε, δb, hε, hδb, hy0, hydiff, hycrit, hyuniq⟩ :=
    Work.Drive.EpsForm.critBranchLocal ψ n₀ X (fun x hx => by
      obtain ⟨h1, _⟩ := (memX x).mp hx
      exact ⟨h1, hndH x h1⟩)
  have hycrit' : ∀ x ∈ X, ∀ n : R3, ‖n - n₀‖ < δb →
      fderiv ℝ (heightIn ψ n) (y x n) = 0 := hycrit
  have hyuniq' : ∀ x ∈ X, ∀ n : R3, ‖n - n₀‖ < δb → ∀ p : ℝ × ℝ, ‖p - x‖ < ε →
      fderiv ℝ (heightIn ψ n) p = 0 → p = y x n := hyuniq
  have hcont : ∀ x ∈ X, ContinuousAt (y x) n₀ := fun x hx =>
    (hydiff x hx n₀ (by simpa using hδb)).continuousAt
  have hpaircont : ∀ x ∈ X, ContinuousAt (fun n : R3 => (n, y x n)) n₀ := fun x hx =>
    continuousAt_id.prodMk_nhds (hcont x hx)
  -- ## 3. the branches stay inside their balls
  have hclose_ev : ∀ᶠ n in 𝓝 n₀, ∀ x ∈ X, ‖y x n - x‖ < ε := by
    refine Work.Drive.EpsForm.eventually_forall_mem_finset (fun x hx => ?_)
    have h1 : ∀ᶠ n in 𝓝 n₀, y x n ∈ Metric.ball (y x n₀) ε :=
      (hcont x hx).eventually (Metric.ball_mem_nhds (y x n₀) hε)
    filter_upwards [h1] with n hn
    rw [hy0 x hx] at hn
    rwa [Metric.mem_ball, dist_eq_norm] at hn
  obtain ⟨δ₁, hδ₁, hclose_ball⟩ := Metric.mem_nhds_iff.mp hclose_ev
  have hclose : ∀ n : R3, ‖n - n₀‖ < δ₁ → ∀ x ∈ X, ‖y x n - x‖ < ε := by
    intro n hn x hx
    exact hclose_ball (by rw [Metric.mem_ball, dist_eq_norm]; exact hn) x hx
  -- ## 4. the Hessian is nondegenerate at the branch points
  have hHfun_cd : ContDiff ℝ 2
      (fun v : R3 × (ℝ × ℝ) => inner ℝ v.1 (Work.BoxShrink.Pinch.par ψ v.2)) := by
    have h1 : ContDiff ℝ 2 (fun v : R3 × (ℝ × ℝ) => (innerSL ℝ) v.1) :=
      (ContinuousLinearMap.contDiff (innerSL ℝ)).comp contDiff_fst
    have h2 : ContDiff ℝ 2 (fun v : R3 × (ℝ × ℝ) => Work.BoxShrink.Pinch.par ψ v.2) :=
      ((Work.BoxShrink.Pinch.par_contDiff ψ).of_le
        (WithTop.coe_le_coe.mpr le_top)).comp contDiff_snd
    exact h1.clm_apply h2
  have hHessCont : Continuous (fun v : R3 × (ℝ × ℝ) =>
      fderiv ℝ (fderiv ℝ (heightIn ψ v.1)) v.2) :=
    continuous_fderiv_fderiv_snd hHfun_cd
  have hndX : ∀ x ∈ X, Function.Injective (fderiv ℝ (fderiv ℝ (heightIn ψ n₀)) x) :=
    fun x hx => hndH x ((memX x).mp hx).1
  have hhess_ev : ∀ᶠ n in 𝓝 n₀, ∀ x ∈ X,
      Function.Injective (fderiv ℝ (fderiv ℝ (heightIn ψ n)) (y x n)) := by
    refine Work.Drive.EpsForm.eventually_forall_mem_finset (fun x hx => ?_)
    have hopen : IsOpen {v : R3 × (ℝ × ℝ) |
        (fderiv ℝ (fderiv ℝ (heightIn ψ v.1)) v.2).IsInvertible} :=
      hHessCont.isOpen_preimage _ Work.Embedding.isOpen_isInvertible
    have hmem : (n₀, x) ∈ {v : R3 × (ℝ × ℝ) |
        (fderiv ℝ (fderiv ℝ (heightIn ψ v.1)) v.2).IsInvertible} :=
      Work.Drive.EpsForm.hessian_isInvertible _ (hndX x hx)
    have hmem' : (fun n : R3 => (n, y x n)) n₀ ∈ {v : R3 × (ℝ × ℝ) |
        (fderiv ℝ (fderiv ℝ (heightIn ψ v.1)) v.2).IsInvertible} := by
      show (n₀, y x n₀) ∈ _
      rw [hy0 x hx]
      exact hmem
    filter_upwards [(hpaircont x hx).eventually (hopen.mem_nhds hmem')] with n hn
    exact hn.injective
  obtain ⟨δ₂, hδ₂, hhess⟩ := Metric.mem_nhds_iff.mp hhess_ev
  have hhess' : ∀ n : R3, ‖n - n₀‖ < δ₂ → ∀ x ∈ X,
      Function.Injective (fderiv ℝ (fderiv ℝ (heightIn ψ n)) (y x n)) := by
    intro n hn x hx
    exact hhess (by rw [Metric.mem_ball, dist_eq_norm]; exact hn) x hx
  -- ## 5. every critical point of a nearby height inside the square is near a base critical point
  have hcover_lemma := Work.Drive.Mono.Band.no_crit_off_isCompact ψ n₀
    (K := Work.Drive.EpsForm.fundBox) Work.Drive.EpsForm.isCompact_fundBox X
    (fun p hp hcrit => (memX p).mpr ⟨by simpa only [heightIn_eq_heightOf] using hcrit, hp⟩) hε
  obtain ⟨U, hUopen, hUn₀, hU⟩ := hcover_lemma
  obtain ⟨δ₃, hδ₃, hδ₃U⟩ := Metric.mem_nhds_iff.mp (hUopen.mem_nhds hUn₀)
  have hcover : ∀ n : R3, ‖n - n₀‖ < δ₃ → ∀ p ∈ Work.Drive.EpsForm.fundBox,
      fderiv ℝ (heightIn ψ n) p = 0 → ∃ x ∈ X, ‖p - x‖ < ε := by
    intro n hn p hp hcrit
    exact hU n (hδ₃U (by rw [Metric.mem_ball, dist_eq_norm]; exact hn)) p hp hcrit
  -- ## 6. the critical values of the branches are separated (or the images coincide)
  have hvalcont : ∀ x ∈ X, ContinuousAt (fun n : R3 => heightIn ψ n (y x n)) n₀ := by
    intro x hx
    have hJ : Continuous (fun v : R3 × (ℝ × ℝ) => heightIn ψ v.1 v.2) := hHfun_cd.continuous
    have hpt : ContinuousAt (fun v : R3 × (ℝ × ℝ) => heightIn ψ v.1 v.2)
        (n₀, y x n₀) := hJ.continuousAt
    exact ContinuousAt.comp₂ (x := n₀)
      (f := fun v : R3 × (ℝ × ℝ) => heightIn ψ v.1 v.2)
      (g := fun n : R3 => n) (h := y x) hpt continuousAt_id (hcont x hx)
  have hpair_ev : ∀ x ∈ X, ∀ x' ∈ X, ∀ᶠ n in 𝓝 n₀,
      heightIn ψ n (y x n) = heightIn ψ n (y x' n) →
        Work.BoxShrink.Pinch.par ψ (y x n) = Work.BoxShrink.Pinch.par ψ (y x' n) := by
    intro x hx x' hx'
    by_cases hbase : heightIn ψ n₀ x = heightIn ψ n₀ x'
    · -- the base points have the same value, hence the same image: lattice translates
      have hpar0 : Work.BoxShrink.Pinch.par ψ x = Work.BoxShrink.Pinch.par ψ x' :=
        hvalH x x' ((memX x).mp hx).1 ((memX x').mp hx').1 hbase
      obtain ⟨k, m, hk, hm⟩ := (Work.Drive.EpsForm.par_eq_iff ψ x x').mp hpar0
      have hshift : x' = x + (((-k : ℤ) : ℝ) * (2 * Real.pi), ((-m : ℤ) : ℝ) * (2 * Real.pi)) := by
        have h1 : x'.1 = x.1 + ((-k : ℤ) : ℝ) * (2 * Real.pi) := by push_cast; linarith
        have h2 : x'.2 = x.2 + ((-m : ℤ) : ℝ) * (2 * Real.pi) := by push_cast; linarith
        exact Prod.ext h1 h2
      have hcrit₁ : ∀ x ∈ X, ∀ n : R3, ‖n - n₀‖ < min δb δ₁ →
          fderiv ℝ (heightIn ψ n) (y x n) = 0 :=
        fun x hx n hn => hycrit' x hx n (lt_of_lt_of_le hn (min_le_left _ _))
      have huniq₁ : ∀ x ∈ X, ∀ n : R3, ‖n - n₀‖ < min δb δ₁ → ∀ p : ℝ × ℝ, ‖p - x‖ < ε →
          fderiv ℝ (heightIn ψ n) p = 0 → p = y x n :=
        fun x hx n hn => hyuniq' x hx n (lt_of_lt_of_le hn (min_le_left _ _))
      have hclose₁ : ∀ x ∈ X, ∀ n : R3, ‖n - n₀‖ < min δb δ₁ → ‖y x n - x‖ < ε :=
        fun x hx n hn => hclose n (lt_of_lt_of_le hn (min_le_right _ _)) x hx
      have hbs := branch_lattice_shift ψ n₀ X y ε (min δb δ₁) hy0 hcrit₁ huniq₁ hclose₁
        hx hx' (-k) (-m) hshift
      filter_upwards [Metric.ball_mem_nhds n₀ (lt_min hδb hδ₁)] with n hn _
      have h1 : y x' n = y x n + (((-k : ℤ) : ℝ) * (2 * Real.pi), ((-m : ℤ) : ℝ) * (2 * Real.pi)) :=
        hbs n (by simpa [Metric.mem_ball, dist_eq_norm] using hn)
      rw [h1, Work.Drive.EpsForm.par_add_shift ψ (-k) (-m) (y x n)]
    · -- the base values differ, so by continuity they stay different
      have hne : ∀ᶠ n in 𝓝 n₀, heightIn ψ n (y x n) ≠ heightIn ψ n (y x' n) := by
        have hlim : ContinuousAt (fun n : R3 => heightIn ψ n (y x n) - heightIn ψ n (y x' n)) n₀ :=
          (hvalcont x hx).sub (hvalcont x' hx')
        have h0 : heightIn ψ n₀ (y x n₀) - heightIn ψ n₀ (y x' n₀) ≠ 0 := by
          rw [hy0 x hx, hy0 x' hx']
          exact sub_ne_zero.mpr hbase
        refine (hlim.eventually_ne h0).mono (fun n hn => ?_)
        exact sub_ne_zero.mp hn
      filter_upwards [hne] with n hn heq
      exact absurd heq hn
  have hpair_all : ∀ᶠ n in 𝓝 n₀, ∀ x ∈ X, ∀ x' ∈ X,
      heightIn ψ n (y x n) = heightIn ψ n (y x' n) →
        Work.BoxShrink.Pinch.par ψ (y x n) = Work.BoxShrink.Pinch.par ψ (y x' n) := by
    refine Work.Drive.EpsForm.eventually_forall_mem_finset (fun x hx => ?_)
    refine Work.Drive.EpsForm.eventually_forall_mem_finset (fun x' hx' => hpair_ev x hx x' hx')
  obtain ⟨δ₄, hδ₄, hpair⟩ := Metric.mem_nhds_iff.mp hpair_all
  have hpair' : ∀ n : R3, ‖n - n₀‖ < δ₄ → ∀ x ∈ X, ∀ x' ∈ X,
      heightIn ψ n (y x n) = heightIn ψ n (y x' n) →
        Work.BoxShrink.Pinch.par ψ (y x n) = Work.BoxShrink.Pinch.par ψ (y x' n) := by
    intro n hn x hx x' hx'
    exact hpair (by rw [Metric.mem_ball, dist_eq_norm]; exact hn) x hx x' hx'
  -- ## 7. the radii
  set ρ : ℝ := min δb (min δ₁ (min δ₂ (min δ₃ δ₄))) with hρdef
  have hρpos : 0 < ρ := by
    rw [hρdef]
    exact lt_min hδb (lt_min hδ₁ (lt_min hδ₂ (lt_min hδ₃ hδ₄)))
  refine ⟨ρ, hρpos, ?_⟩
  intro n hn
  have hρb : ρ ≤ δb := by rw [hρdef]; exact min_le_left _ _
  have hρ1 : ρ ≤ δ₁ := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hρ2 : ρ ≤ δ₂ := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hρ3 : ρ ≤ δ₃ := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hρ4 : ρ ≤ δ₄ := by
    rw [hρdef]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hnb : ‖n - n₀‖ < δb := lt_of_lt_of_le hn hρb
  have hn1 : ‖n - n₀‖ < δ₁ := lt_of_lt_of_le hn hρ1
  have hn2 : ‖n - n₀‖ < δ₂ := lt_of_lt_of_le hn hρ2
  have hn3 : ‖n - n₀‖ < δ₃ := lt_of_lt_of_le hn hρ3
  have hn4 : ‖n - n₀‖ < δ₄ := lt_of_lt_of_le hn hρ4
  refine ⟨?_, ?_⟩
  · -- nondegeneracy of the critical points
    intro p hp
    obtain ⟨p', hp'box, hp'crit, _, hp'hess, _⟩ :=
      Work.Drive.EpsForm.exists_fundBox_of_crit ψ n (by simpa only [heightIn_eq_heightOf] using hp)
    obtain ⟨x, hxX, hxε⟩ := hcover n hn3 p' hp'box hp'crit
    have hp'eq : p' = y x n := hyuniq' x hxX n hnb p' hxε hp'crit
    have hp'hess' : fderiv ℝ (fderiv ℝ (heightIn ψ n)) p'
        = fderiv ℝ (fderiv ℝ (heightIn ψ n)) p := by
      simpa only [heightIn_eq_heightOf] using hp'hess
    have hinj := hhess' n hn2 x hxX
    rw [← hp'eq] at hinj
    rw [hp'hess'] at hinj
    exact hinj
  · -- injectivity of the critical values
    intro p p' hp hp' hval
    obtain ⟨p₁, hp₁box, hp₁crit, hp₁val, -, hp₁par⟩ :=
      Work.Drive.EpsForm.exists_fundBox_of_crit ψ n (by simpa only [heightIn_eq_heightOf] using hp)
    obtain ⟨p₂, hp₂box, hp₂crit, hp₂val, -, hp₂par⟩ :=
      Work.Drive.EpsForm.exists_fundBox_of_crit ψ n (by simpa only [heightIn_eq_heightOf] using hp')
    have hp₁val' : heightIn ψ n p₁ = heightIn ψ n p := hp₁val
    have hp₂val' : heightIn ψ n p₂ = heightIn ψ n p' := hp₂val
    obtain ⟨x, hxX, hxε⟩ := hcover n hn3 p₁ hp₁box hp₁crit
    have hp₁eq : p₁ = y x n := hyuniq' x hxX n hnb p₁ hxε hp₁crit
    obtain ⟨x', hx'X, hx'ε⟩ := hcover n hn3 p₂ hp₂box hp₂crit
    have hp₂eq : p₂ = y x' n := hyuniq' x' hx'X n hnb p₂ hx'ε hp₂crit
    have hvaleq : heightIn ψ n (y x n) = heightIn ψ n (y x' n) := by
      rw [← hp₁eq, ← hp₂eq, hp₁val', hp₂val']
      exact hval
    have himg : Work.BoxShrink.Pinch.par ψ (y x n) = Work.BoxShrink.Pinch.par ψ (y x' n) :=
      hpair' n hn4 x hxX x' hx'X hvaleq
    rw [← hp₁par, ← hp₂par, hp₁eq, hp₂eq]
    exact himg

end

end Work.Drive.Mono.Band
