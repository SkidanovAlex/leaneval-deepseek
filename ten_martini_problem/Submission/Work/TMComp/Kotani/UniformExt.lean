import Mathlib
import Submission.Work.TMComp.Kotani.GlueDefs
import Submission.Work.TMComp.Kotani.ExtOnShift
import Submission.Work.TMComp.Kotani.AnalyticLimit

/-!
# Uniformity of the local continuation in the phase

From the pointwise local continuation hypothesis (`hloc`) we deduce that for every real `E₀` in
the interval there is a *radius* `r > 0` such that `mfun α lam · x` continues to the ball
`B(E₀,r)` for **every** phase `x`.

The proof is a Baire category argument: the sets `Z(r) = {x | ExtOn α lam E₀ r x}` are closed
(the pointwise limit of extensions of `mfun α lam · xₙ` with `xₙ → x` is again an extension,
by the Vitali-type lemma `exists_analyticOnNhd_of_tendsto_offreal` applied to the Cayley
transform), and they are invariant under the dense translation group `ℤ + αℤ` and under the
reflection `x ↦ α - x`.
-/

open MeasureTheory Filter Topology Set
open scoped Topology
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Kotani

open Work.TMContract

theorem continuousOn_mfun' (α lam : ℝ) :
    ContinuousOn (fun p : ℂ × ℝ => mfun α lam p.1 p.2) {p : ℂ × ℝ | 0 < p.1.im} :=
  (mfun_props α lam).2.2.2.2.1

/-- Continuity of `mfun` in the phase at fixed energy in the upper half plane. -/
theorem continuous_mfun_fst (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) :
    Continuous (fun x : ℝ => mfun α lam E x) := by
  have h : ContinuousOn (fun p : ℂ × ℝ => mfun α lam p.1 p.2) {p : ℂ × ℝ | 0 < p.1.im} :=
    (mfun_props α lam).2.2.2.2.1
  have h1 : Continuous fun x : ℝ => (E, x) := continuous_const.prodMk continuous_id
  exact (h.comp_continuous h1 fun x => hE).congr fun x => rfl

/-- Convergence of `mfun` in the phase at a fixed energy in the upper half plane. -/
theorem tendsto_mfun (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) {u : ℕ → ℝ} {x₀ : ℝ}
    (h : Tendsto u atTop (𝓝 x₀)) :
    Tendsto (fun n => mfun α lam E (u n)) atTop (𝓝 (mfun α lam E x₀)) :=
  ((continuous_mfun_fst α lam hE).tendsto x₀).comp h

/-- Continuity of the reflected section in the phase. -/
theorem continuous_sig_fst (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) :
    Continuous (fun x : ℝ => 1 / star (mfun α lam E (α - x))) := by
  have hc : Continuous fun x : ℝ => mfun α lam E (α - x) :=
    (continuous_mfun_fst α lam hE).comp (continuous_const.sub continuous_id)
  exact (hc.star.inv₀ fun x => star_ne_zero.mpr
    (ne_of_apply_ne Complex.im (ne_of_gt (mfun_im_pos' α lam hE (α - x))))).congr fun x => by
      simp [one_div]

/-- Convergence of the reflected section in the phase. -/
theorem tendsto_sig (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) {u : ℕ → ℝ} {x₀ : ℝ}
    (h : Tendsto u atTop (𝓝 x₀)) :
    Tendsto (fun n => 1 / star (mfun α lam E (α - u n))) atTop
      (𝓝 (1 / star (mfun α lam E (α - x₀)))) :=
  ((continuous_sig_fst α lam hE).tendsto x₀).comp h

/-- The Cayley transform of an `ExtOn`-witness is analytic. -/
theorem analyticOnNhd_cayley_comp {E₀ r : ℝ} {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (Metric.ball (E₀ : ℂ) r))
    (hpos : ∀ z ∈ Metric.ball (E₀ : ℂ) r, 0 < (f z).im) :
    AnalyticOnNhd ℂ (fun z => cayley (f z)) (Metric.ball (E₀ : ℂ) r) := by
  have h1 : AnalyticOnNhd ℂ (fun z => f z - Complex.I) (Metric.ball (E₀ : ℂ) r) :=
    hf.sub analyticOnNhd_const
  have h2 : AnalyticOnNhd ℂ (fun z => f z + Complex.I) (Metric.ball (E₀ : ℂ) r) :=
    hf.add analyticOnNhd_const
  have hden : ∀ z ∈ Metric.ball (E₀ : ℂ) r, f z + Complex.I ≠ 0 := by
    intro z hz hc
    have h := congrArg Complex.im hc
    simp at h
    have := hpos z hz
    linarith
  refine (AnalyticOnNhd.div h1 h2 hden).congr Metric.isOpen_ball ?_
  intro z hz
  simp [cayley]

/-- The inverse Cayley transform of an analytic function of modulus `< 1` is analytic. -/
theorem analyticOnNhd_cayleyInv_comp {E₀ r : ℝ} {G : ℂ → ℂ}
    (hG : AnalyticOnNhd ℂ G (Metric.ball (E₀ : ℂ) r))
    (hlt : ∀ z ∈ Metric.ball (E₀ : ℂ) r, ‖G z‖ < 1) :
    AnalyticOnNhd ℂ (fun z => cayleyInv (G z)) (Metric.ball (E₀ : ℂ) r) := by
  have hnum : AnalyticOnNhd ℂ (fun z => Complex.I * (1 + G z)) (Metric.ball (E₀ : ℂ) r) :=
    analyticOnNhd_const.mul (analyticOnNhd_const.add hG)
  have hden : AnalyticOnNhd ℂ (fun z => 1 - G z) (Metric.ball (E₀ : ℂ) r) :=
    analyticOnNhd_const.sub hG
  have hne : ∀ z ∈ Metric.ball (E₀ : ℂ) r, (1 : ℂ) - G z ≠ 0 := by
    intro z hz hc
    have h1 : G z = 1 := by linear_combination -hc
    have h2 := hlt z hz
    rw [h1] at h2
    simp at h2
  refine (AnalyticOnNhd.div hnum hden hne).congr Metric.isOpen_ball ?_
  intro z hz
  simp [cayleyInv]

/-- `ExtOn` is monotone in the radius. -/
theorem extOn_mono {α lam E₀ r r' x : ℝ} (h : r' ≤ r) (hf : ExtOn α lam E₀ r x) :
    ExtOn α lam E₀ r' x := by
  obtain ⟨f, han, hup, hdown, hpos⟩ := hf
  have hsub : Metric.ball (E₀ : ℂ) r' ⊆ Metric.ball (E₀ : ℂ) r := by
    intro z hz
    rw [Metric.mem_ball] at hz ⊢
    linarith
  exact ⟨f, han.mono hsub, fun z hz hzim => hup z (hsub hz) hzim,
    fun z hz hzim => hdown z (hsub hz) hzim, fun z hz => hpos z (hsub hz)⟩

/-- `cayley` is continuous where its denominator does not vanish. -/
theorem continuousAt_cayley {w : ℂ} (hw : w ≠ -Complex.I) : ContinuousAt cayley w := by
  have h : cayley = fun z : ℂ => (z - Complex.I) / (z + Complex.I) := rfl
  rw [h]
  refine ContinuousAt.div (continuousAt_id.sub continuousAt_const)
    (continuousAt_id.add continuousAt_const) ?_
  exact fun h => hw (by linear_combination h)

/-- **Uniformity in the phase.**  If `mfun α lam · x` continues analytically across every
`E₀ ∈ (a,b)` for every phase `x`, then at every `E₀ ∈ (a,b)` there is a radius `r > 0` which
works for all phases. -/
theorem uniform_ext (α lam a b : ℝ) (hα : Irrational α) (hE : a < b)
    (hloc : ∀ E₀ ∈ Set.Ioo a b, ∀ x : ℝ, ∃ f : ℂ → ℂ,
      AnalyticAt ℂ f (E₀ : ℂ) ∧
      (∀ᶠ E in nhds (E₀ : ℂ), 0 < E.im → f E = mfun α lam E x) ∧
      (∀ᶠ E in nhds (E₀ : ℂ), E.im < 0 →
        f E = 1 / star (mfun α lam (star E) (α - x))) ∧
      (∀ᶠ E in nhds (E₀ : ℂ), 0 < (f E).im)) :
    ∀ E₀ ∈ Set.Ioo a b, ∃ r : ℝ, 0 < r ∧ ∀ x : ℝ, ExtOn α lam E₀ r x := by
  intro E₀ hE₀
  -- (1) `ExtOn` holds for some radius, for every phase
  have hbasic : ∀ x : ℝ, ∃ s : ℝ, 0 < s ∧ ExtOn α lam E₀ s x := by
    intro x
    obtain ⟨f, han, hup, hdown, hpos⟩ := hloc E₀ hE₀ x
    obtain ⟨s₁, hs₁, hb₁⟩ := Metric.mem_nhds_iff.mp hup
    obtain ⟨s₂, hs₂, hb₂⟩ := Metric.mem_nhds_iff.mp hdown
    obtain ⟨s₃, hs₃, hb₃⟩ := Metric.mem_nhds_iff.mp hpos
    obtain ⟨s₄, hs₄, han4⟩ := han.exists_ball_analyticOnNhd
    set s : ℝ := min (min s₁ s₂) (min s₃ s₄) / 2 with hsdef
    have hpos_min : 0 < min (min s₁ s₂) (min s₃ s₄) :=
      lt_min (lt_min hs₁ hs₂) (lt_min hs₃ hs₄)
    have hspos : 0 < s := by rw [hsdef]; positivity
    have hs1 : s ≤ s₁ := le_trans (by rw [hsdef]; linarith) (le_trans (min_le_left _ _) (min_le_left _ _))
    have hs2 : s ≤ s₂ := le_trans (by rw [hsdef]; linarith) (le_trans (min_le_left _ _) (min_le_right _ _))
    have hs3 : s ≤ s₃ := le_trans (by rw [hsdef]; linarith) (le_trans (min_le_right _ _) (min_le_left _ _))
    have hs4 : s ≤ s₄ := le_trans (by rw [hsdef]; linarith) (le_trans (min_le_right _ _) (min_le_right _ _))
    refine ⟨s, hspos, f, ?_, ?_, ?_, ?_⟩
    · refine han4.mono fun z hz => ?_
      rw [Metric.mem_ball] at hz ⊢
      linarith
    · intro z hz hzim
      exact hb₁ (by rw [Metric.mem_ball] at hz ⊢; linarith) hzim
    · intro z hz hzim
      exact hb₂ (by rw [Metric.mem_ball] at hz ⊢; linarith) hzim
    · intro z hz
      exact hb₃ (by rw [Metric.mem_ball] at hz ⊢; linarith)
  -- (2) the sets `Z r` are closed
  -- (2) `Z r` is closed: the limit of extensions is an extension
  have hclosed : ∀ r : ℝ, 0 < r → IsClosed {x : ℝ | ExtOn α lam E₀ r x} := by
    intro r hr
    have key : ∀ u : ℕ → ℝ, (∀ n, ExtOn α lam E₀ r (u n)) → ∀ x₀ : ℝ,
        Tendsto u atTop (𝓝 x₀) → ExtOn α lam E₀ r x₀ := by
      intro u hu x₀ hutend
      have hw : ∀ n, ∃ f : ℂ → ℂ, AnalyticOnNhd ℂ f (Metric.ball (E₀ : ℂ) r) ∧
          (∀ z ∈ Metric.ball (E₀ : ℂ) r, 0 < z.im → f z = mfun α lam z (u n)) ∧
          (∀ z ∈ Metric.ball (E₀ : ℂ) r, z.im < 0 →
            f z = 1 / star (mfun α lam (star z) (α - u n))) ∧
          (∀ z ∈ Metric.ball (E₀ : ℂ) r, 0 < (f z).im) := fun n => hu n
      choose f hfan hfup hfdown hfpos using hw
      have hF : ∀ n, AnalyticOnNhd ℂ (fun z => cayley (f n z)) (Metric.ball (E₀ : ℂ) r) :=
        fun n => analyticOnNhd_cayley_comp (hfan n) (hfpos n)
      have hbg : ∀ n z, z ∈ Metric.ball (E₀ : ℂ) r → ‖cayley (f n z)‖ ≤ 1 :=
        fun n z hz => le_of_lt (norm_cayley_lt_one (hfpos n z hz))
      set g : ℂ → ℂ := fun z => if 0 < z.im then cayley (mfun α lam z x₀)
        else if z.im < 0 then cayley (1 / star (mfun α lam (star z) (α - x₀))) else 0 with hgdef
      have hgpos : ∀ z, 0 < z.im → g z = cayley (mfun α lam z x₀) := by
        intro z hz
        simp only [hgdef]
        rw [if_pos hz]
      have hgneg : ∀ z, z.im < 0 →
          g z = cayley (1 / star (mfun α lam (star z) (α - x₀))) := by
        intro z hz
        simp only [hgdef]
        rw [if_neg (not_lt.mpr (le_of_lt hz)), if_pos hz]
      have hconv : ∀ z ∈ Metric.ball (E₀ : ℂ) r, z.im ≠ 0 →
          Tendsto (fun n => cayley (f n z)) atTop (𝓝 (g z)) := by
        intro z hz hzim
        rcases lt_or_gt_of_ne hzim with hlt | hgt
        · have hcan : ContinuousAt cayley (1 / star (mfun α lam (star z) (α - x₀))) := by
            refine continuousAt_cayley ?_
            intro hc
            have him := inv_star_im_pos (mfun_im_pos' α lam (star_im_neg hlt) (α - x₀))
            rw [hc] at him
            simp at him
            exact absurd him (by norm_num)
          have h2 := hcan.tendsto.comp (tendsto_sig α lam (star_im_neg hlt) hutend)
          rw [hgneg z hlt]
          refine h2.congr' (Eventually.of_forall fun n => ?_)
          simp only [Function.comp_apply]
          rw [hfdown n z hz hlt]
        · have hcan : ContinuousAt cayley (mfun α lam z x₀) := by
            refine continuousAt_cayley ?_
            intro hc
            have him := mfun_im_pos' α lam hgt x₀
            rw [hc] at him
            simp at him
            exact absurd him (by norm_num)
          have h2 := hcan.tendsto.comp (tendsto_mfun α lam hgt hutend)
          rw [hgpos z hgt]
          refine h2.congr' (Eventually.of_forall fun n => ?_)
          simp only [Function.comp_apply]
          rw [hfup n z hz hgt]
      obtain ⟨G, hGan, hGval, hGunif, hGpt⟩ :=
        exists_analyticOnNhd_of_tendsto_offreal (E₀ : ℂ) r hr hF hbg hconv
      have hGle : ∀ z ∈ Metric.ball (E₀ : ℂ) r, ‖G z‖ ≤ 1 :=
        fun z hz => le_of_tendsto' (hGpt z hz).norm fun n => hbg n z hz
      have hGlt : ∀ z ∈ Metric.ball (E₀ : ℂ) r, ‖G z‖ < 1 := by
        intro z hz
        rcases lt_trichotomy (‖G z‖) 1 with hlt | heq | hgt
        · exact hlt
        · exfalso
          have hmax : IsMaxOn (fun w => ‖G w‖) (Metric.ball (E₀ : ℂ) r) z := by
            intro w hw
            show ‖G w‖ ≤ ‖G z‖
            rw [heq]
            exact hGle w hw
          have heqon := Complex.norm_eqOn_of_isPreconnected_of_isMaxOn
            Metric.isPreconnected_ball Metric.isOpen_ball hGan.differentiableOn hz hmax
          set z₂ : ℂ := (E₀ : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I with hz₂def
          have hz₂im : 0 < z₂.im := by
            rw [hz₂def]
            simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
              Complex.I_re, Complex.I_im, mul_one, zero_add]
            positivity
          have hz₂mem : z₂ ∈ Metric.ball (E₀ : ℂ) r := by
            rw [Metric.mem_ball, dist_eq_norm, hz₂def,
              show (E₀ : ℂ) + ((r / 2 : ℝ) : ℂ) * Complex.I - (E₀ : ℂ)
                = ((r / 2 : ℝ) : ℂ) * Complex.I by ring,
              norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos (by positivity)]
            linarith
          have h1 : ‖G z₂‖ = ‖G z‖ := heqon hz₂mem
          have h2 : ‖G z₂‖ < 1 := by
            rw [hGval z₂ hz₂mem (ne_of_gt hz₂im), hgpos z₂ hz₂im]
            exact norm_cayley_lt_one (mfun_im_pos' α lam hz₂im x₀)
          rw [h1, heq] at h2
          exact lt_irrefl 1 h2
        · exact absurd hgt (not_lt.mpr (hGle z hz))
      have hf_an : AnalyticOnNhd ℂ (fun z => cayleyInv (G z)) (Metric.ball (E₀ : ℂ) r) :=
        analyticOnNhd_cayleyInv_comp hGan hGlt
      refine ⟨fun z => cayleyInv (G z), hf_an, ?_, ?_, ?_⟩
      · intro z hz hzim
        dsimp only
        rw [hGval z hz (ne_of_gt hzim), hgpos z hzim,
          cayleyInv_cayley (mfun_im_pos' α lam hzim x₀)]
      · intro z hz hzim
        dsimp only
        rw [hGval z hz (ne_of_lt hzim), hgneg z hzim,
          cayleyInv_cayley (inv_star_im_pos (mfun_im_pos' α lam (star_im_neg hzim) (α - x₀)))]
      · intro z hz
        dsimp only
        exact im_cayleyInv_pos (hGlt z hz)
    exact IsSeqClosed.isClosed fun u x₀ hu hutend => key u hu x₀ hutend
  -- (3) Baire category: some `Z r` has an interior point, and by invariance it is everything
  have hinv : ∀ (r : ℝ) (γ : ℝ), γ ∈ AddSubgroup.closure ({α, 1} : Set ℝ) →
      ∀ x : ℝ, (ExtOn α lam E₀ r (x + γ) ↔ ExtOn α lam E₀ r x) := by
    intro r γ hγ
    refine AddSubgroup.closure_induction (p := fun g _ => ∀ x : ℝ,
      (ExtOn α lam E₀ r (x + g) ↔ ExtOn α lam E₀ r x)) ?_ ?_ ?_ ?_ hγ
    · intro y hy x
      rcases hy with rfl | rfl
      · exact extOn_add_alpha _ _
      · exact extOn_add_one _ _
    · intro x
      simp
    · intro y z hy hz hyC hzC x
      rw [show x + (y + z) = (x + y) + z by ring, hzC, hyC]
    · intro y hy hyC x
      have h := hyC (x + -y)
      rw [show (x + -y) + y = x by ring] at h
      exact h.symm
  have hGamma_dense : Dense ((AddSubgroup.closure ({α, 1} : Set ℝ)) : Set ℝ) := by
    rw [dense_addSubgroupClosure_pair_iff]
    simpa using hα
  have hcover : (⋃ n : ℕ, {x : ℝ | ExtOn α lam E₀ (1 / ((n : ℝ) + 1)) x}) = Set.univ := by
    ext x
    simp only [mem_iUnion, mem_setOf_eq, mem_univ, iff_true]
    obtain ⟨s, hs, hsx⟩ := hbasic x
    obtain ⟨n, hn⟩ : ∃ n : ℕ, 1 / s ≤ (n : ℝ) := ⟨Nat.ceil (1 / s), Nat.le_ceil _⟩
    refine ⟨n, extOn_mono ?_ hsx⟩
    rw [div_le_iff₀ (by positivity)]
    have h1 : 1 / s ≤ (n : ℝ) + 1 := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 (le_of_lt hs)
    have h3 : s * (1 / s) = 1 := by field_simp
    rw [h3] at h2
    exact h2
  obtain ⟨N, hN⟩ := nonempty_interior_of_iUnion_of_closed
    (f := fun n : ℕ => {x : ℝ | ExtOn α lam E₀ (1 / ((n : ℝ) + 1)) x})
    (fun n => hclosed _ (by positivity)) hcover
  set R : ℝ := 1 / ((N : ℝ) + 1) with hRdef
  have hR : 0 < R := by rw [hRdef]; positivity
  have hZclosed : IsClosed {x : ℝ | ExtOn α lam E₀ R x} := hclosed R hR
  obtain ⟨x₀, hx₀⟩ := hN
  have hx₀Z : x₀ ∈ {x : ℝ | ExtOn α lam E₀ R x} := interior_subset hx₀
  have hdense : Dense {x : ℝ | ExtOn α lam E₀ R x} := by
    rw [Metric.dense_iff]
    intro y δ hδ
    have hmem : (y - x₀) ∈ closure ((AddSubgroup.closure ({α, 1} : Set ℝ)) : Set ℝ) :=
      hGamma_dense.closure_eq ▸ mem_univ (y - x₀)
    obtain ⟨γ, hγ, hγdist⟩ := Metric.mem_closure_iff.mp hmem δ hδ
    refine ⟨x₀ + γ, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_comm]
      have h1 : dist y (x₀ + γ) = dist (y - x₀) γ := by
        rw [dist_eq_norm, dist_eq_norm]
        congr 1
        ring
      rw [h1]
      exact hγdist
    · exact (hinv R γ hγ x₀).mpr hx₀Z
  have hZU : {x : ℝ | ExtOn α lam E₀ R x} = Set.univ := by
    rw [← hZclosed.closure_eq, hdense.closure_eq]
  exact ⟨R, hR, fun x => by
    show x ∈ {x : ℝ | ExtOn α lam E₀ R x}
    rw [hZU]
    exact mem_univ x⟩

end Work.TMComp.Kotani
