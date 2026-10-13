/-
  WilC4aCS.CaseB: the induction step when the defining function `F` is not identically zero near the
  origin.  Simultaneous real Weierstrass preparation (`RealWeierstrass`) turns the basic semianalytic
  set into sign conditions on monic polynomials whose coefficients are analytic functions of the
  first `n` coordinates; Tarski-Seidenberg (`TS1`) projects the polynomial sign table to a
  semialgebraic set in coefficient space; a DNF disjunct gives a basic semianalytic set `W ⊆ R^n`
  with the origin in its closure, `CurveSel n` gives a base arc `γ'` in `W`, and `ArcLift` lifts the
  last coordinate analytically over `γ' ∘ (·^N)`.
-/
import Submission.Work.WilC4aCS.Defs
import Submission.Work.WilC4aCS.Helpers
import Submission.Work.WilC4aCS.Setup
import Submission.Work.WilC4aCS.wpoly_eq_Qeval
import Submission.Work.WilC4aCS.SAcoef_set
import Submission.Work.WilC4aCS.posSign_spec
import Submission.Work.WilC4aCS.mpoly_coefFun
import Submission.Work.WilC4aCS.analyticAt_base_funs
import Submission.Work.WilC4aCS.analyticAt_snoc
import Submission.Work.WilC4aCS.Yw_iff
import Submission.Work.WilC4aCS.Base_eq_BasicSA
import Submission.Work.WilC4aCS.exists_basic_closure
import Submission.Work.WilC4aCS.YwL_eq_BasicSA
import Submission.Work.WilC4aCS.L_mem_of_Yw

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators
open WilkiesConjecture WilkiesDesign WilkiesDesign.CG

namespace Work.WilC4aCS

open WilkiesDesign.CG.C4a
open WilkiesDesign.E

/-- `Basic`-sets are contained in the `SA`-set whose disjunction they belong to. -/
lemma BSet_subset {D : ℕ} {Y : E.SA D} {B : Basic D 0} (hB : B ∈ Y.basics) :
    BSet B ⊆ Y.set := fun _ hv => ⟨B, hB, hv⟩

/-- `Fin.snoc` of the two zero vectors is zero. -/
lemma snoc_zero_zero (n : ℕ) :
    (Fin.snoc (0 : Fin n → ℝ) (0 : ℝ) : Fin (n + 1) → ℝ) = 0 := by
  funext i
  exact Fin.lastCases (by simp) (fun _ => by simp) i

/-- Evaluation of `Qpoly` at `Fin.snoc A z`, in the `ev0` form. -/
lemma ev0_snoc_Qpoly {K : ℕ} (d : Fin K → ℕ) (A : Fin (∑ i, d i) → ℝ) (z : ℝ) (i : Fin K) :
    ev0 (Fin.snoc A z) (Qpoly d i) = Qeval d A z i :=
  eval_Qpoly d A z i

/-! ## The `F ≢ 0` case of the induction step -/

theorem caseB_step {n l : ℕ} (F : (Fin (n + 1) → ℝ) → ℝ)
    (g : Fin l → (Fin (n + 1) → ℝ) → ℝ) (hF : AnalyticAt ℝ F 0)
    (hg : ∀ j, AnalyticAt ℝ (g j) 0) (hF0 : F 0 = 0) (hg0 : ∀ j, g j 0 = 0)
    (hFnz : ¬ (F =ᶠ[𝓝 0] 0)) (hgnz : ∀ j, ¬ (g j =ᶠ[𝓝 0] 0))
    (hcl : (0 : Fin (n + 1) → ℝ) ∈ closure (BasicSA F g))
    (ih : CurveSel n) (hW : RealWeierstrass) (hA : ArcLift) (hT : TS1) :
    ∃ γ : ℝ → (Fin (n + 1) → ℝ), AnalyticAt ℝ γ 0 ∧ γ 0 = 0 ∧
      ∃ ε > (0 : ℝ), ∀ s ∈ Set.Ioo (0 : ℝ) ε, γ s ∈ BasicSA F g := by
  obtain ⟨W⟩ := wsetup_exists F g hF hg hF0 hg0 hFnz hgnz hW
  -- the sign vector for the lifted inequalities
  let τ : Fin l → ℝ := fun j => posSign (W.u (Fin.succ j) 0)
  have hτ : ∀ j, SignType.sign (τ j) = SignType.sign (W.u (Fin.succ j) 0) := fun j =>
    (posSign_spec (W.hu0 (Fin.succ j))).2.1
  -- Tarski-Seidenberg
  obtain ⟨Y, hYset⟩ := hT (∑ i : Fin (l + 1), W.d i) (SAcoef l W.d τ)
  -- a uniform continuity bound for `L.symm` at the origin
  have hcont_symm : ∀ ε > (0 : ℝ), ∃ η > (0 : ℝ), ∀ x : Fin (n + 1) → ℝ,
      ‖x‖ < η → ‖W.L.symm x‖ < ε := by
    intro ε hε
    obtain ⟨η, hη, hη'⟩ := (Metric.continuousAt_iff.mp W.L.symm.continuous.continuousAt) ε hε
    refine ⟨η, hη, fun x hx => ?_⟩
    have h1 : dist (W.L.symm x) (W.L.symm 0) < ε := hη' (by simpa [dist_eq_norm] using hx)
    simpa [dist_eq_norm, map_zero] using h1
  -- the origin is still in the closure of the Weierstrass side
  have hYwcl : (0 : Fin (n + 1) → ℝ) ∈ closure (Yw W.d W.a τ) := by
    have hLcl : (0 : Fin (n + 1) → ℝ) ∈ closure (YwL W.L W.d W.a τ) := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨η, hη, hη'⟩ := hcont_symm W.δ W.hδ
      obtain ⟨x, hx, hxε⟩ := Metric.mem_closure_iff.mp hcl (min ε η) (lt_min hε hη)
      refine ⟨x, ?_, ?_⟩
      · refine (YwL_eq_BasicSA F g (combineFam F g) rfl (fun j => rfl) W.L W.d W.a W.u W.δ
          W.hid W.hu W.hus τ hτ x ?_).mpr hx
        exact hη' x (by simpa [dist_eq_norm] using lt_of_lt_of_le hxε (min_le_right _ _))
      · exact lt_of_lt_of_le hxε (min_le_left _ _)
    rw [Metric.mem_closure_iff] at hLcl ⊢
    intro ε hε
    obtain ⟨η, hη, hη'⟩ := hcont_symm ε hε
    obtain ⟨y, hy, hyη⟩ := hLcl η hη
    refine ⟨W.L.symm y, hy, ?_⟩
    simpa [dist_eq_norm] using hη' y (by simpa [dist_eq_norm] using hyη)
  -- DNF: one basic piece still has the origin in its closure
  obtain ⟨B, hBmem, hBcl⟩ := exists_basic_closure W.d W.a τ Y hYset hYwcl
  -- rewrite it as a basic semianalytic set in `R^n`
  let F' : (Fin n → ℝ) → ℝ :=
    fun x' => ∑ f ∈ B.eqs.toFinset, (ev0 (coefFun W.d W.a x') f) ^ 2
  let g' : Fin B.pos.length → (Fin n → ℝ) → ℝ :=
    fun j x' => ev0 (coefFun W.d W.a x') (B.pos.get j)
  have hBase : Base W.d W.a B = BasicSA F' g' := Base_eq_BasicSA W.d W.a B
  have hAnal' : AnalyticAt ℝ F' 0 ∧ ∀ j, AnalyticAt ℝ (g' j) 0 :=
    analyticAt_base_funs W.d W.a (fun i j => W.han i j) B
  have hγ'cl : (0 : Fin n → ℝ) ∈ closure (BasicSA F' g') := by
    rw [← hBase]
    exact hBcl
  obtain ⟨γ', hγ'an, hγ'0, ε', hε', hγ'mem⟩ :=
    curveSelAt0_of_curveSel ih B.pos.length F' g' hAnal'.1 hAnal'.2 hγ'cl
  -- the lifted family and its sign vector
  let c : ∀ i : Fin (l + 1), Fin (W.d i) → ℝ → ℝ := fun i j s => W.a i j (γ' s)
  let σ : Fin (l + 1) → SignType :=
    fun i => Fin.cases 0 (fun j => SignType.sign (W.u (Fin.succ j) 0)) i
  have hσ0 : σ 0 = 0 := rfl
  have hσs : ∀ j : Fin l, σ (Fin.succ j) = SignType.sign (W.u (Fin.succ j) 0) := fun j => rfl
  have hAnal_c : ∀ (i : Fin (l + 1)) (j : Fin (W.d i)), AnalyticAt ℝ (c i j) 0 := by
    intro i j
    exact (W.han i j).comp_of_eq hγ'an hγ'0
  -- every small positive parameter admits a lift
  have hArc : ∃ s0 > (0 : ℝ), ∀ s ∈ Set.Ioo (0 : ℝ) s0, ∃ z : ℝ, ∀ i : Fin (l + 1),
      SignType.sign (mpoly (c i) s z) = σ i := by
    refine ⟨ε', hε', fun s hs => ?_⟩
    have hmem : γ' s ∈ Base W.d W.a B := by
      rw [hBase]
      exact hγ'mem s hs
    have hY : coefFun W.d W.a (γ' s) ∈ Y.set := BSet_subset hBmem hmem
    rw [hYset] at hY
    obtain ⟨z, hz⟩ := hY
    have hz' := hz
    rw [SAcoef_set l W.d τ] at hz'
    have hbr : ∀ i : Fin (l + 1),
        mpoly (c i) s z = Qeval W.d (coefFun W.d W.a (γ' s)) z i := by
      intro i
      rw [show mpoly (c i) s z = mpoly (fun (j : Fin (W.d i)) (_ : ℝ) => W.a i j (γ' s)) s z
        from rfl]
      exact mpoly_coefFun W.d W.a γ' s z i
    have key0 : SignType.sign (Qeval W.d (coefFun W.d W.a (γ' s)) z 0) = σ 0 := by
      rw [hσ0, sign_eq_zero_iff]
      have h := hz'.1
      rw [ev0_snoc_Qpoly W.d (coefFun W.d W.a (γ' s)) z 0] at h
      exact h
    have keys : ∀ j : Fin l,
        SignType.sign (Qeval W.d (coefFun W.d W.a (γ' s)) z (Fin.succ j)) = σ (Fin.succ j) := by
      intro j
      rw [hσs j]
      refine ((posSign_spec (W.hu0 (Fin.succ j))).2.2
        (Qeval W.d (coefFun W.d W.a (γ' s)) z (Fin.succ j))).mp ?_
      have h := hz'.2 j
      rw [ev0_snoc_Qpoly W.d (coefFun W.d W.a (γ' s)) z (Fin.succ j)] at h
      exact h
    have hall : ∀ i : Fin (l + 1),
        SignType.sign (Qeval W.d (coefFun W.d W.a (γ' s)) z i) = σ i :=
      Fin.cases key0 (fun j => keys j)
    exact ⟨z, fun i => by rw [hbr i]; exact hall i⟩
  obtain ⟨N, ζ, hN, hζan, r₀, hr₀, hζsign⟩ := hA (l + 1) W.d c σ hAnal_c hArc
  have hzN : ((id : ℝ → ℝ) ^ N) 0 = 0 := by
    show (0 : ℝ) ^ N = 0
    exact zero_pow (ne_of_gt hN)
  have hγ'N : AnalyticAt ℝ (fun r => γ' (r ^ N)) 0 :=
    hγ'an.comp_of_eq (analyticAt_id.pow N) hzN
  have hγ'0N : (fun r : ℝ => γ' (r ^ N)) 0 = 0 := by
    show γ' (0 ^ N) = 0
    rw [zero_pow (ne_of_gt hN), hγ'0]
  -- the lifted arc starts at the origin
  have hζ0 : ζ 0 = 0 := by
    have hzero : ∀ r ∈ Set.Ioo (0 : ℝ) r₀, mpoly (c 0) (r ^ N) (ζ r) = 0 := by
      intro r hr
      have h := hζsign r hr 0
      rw [hσ0] at h
      exact sign_eq_zero_iff.mp h
    have hΦan : AnalyticAt ℝ (fun r => mpoly (c 0) (r ^ N) (ζ r)) 0 := by
      have hfun : (fun r => mpoly (c 0) (r ^ N) (ζ r))
          = fun r => ζ r ^ (W.d 0) + ∑ j : Fin (W.d 0),
              W.a 0 j (γ' (r ^ N)) * ζ r ^ (j : ℕ) := by
        funext r
        rfl
      rw [hfun]
      have hsum : AnalyticAt ℝ (fun r => ∑ j : Fin (W.d 0),
          W.a 0 j (γ' (r ^ N)) * ζ r ^ (j : ℕ)) 0 := by
        rw [show (fun r : ℝ => ∑ j : Fin (W.d 0), W.a 0 j (γ' (r ^ N)) * ζ r ^ (j : ℕ))
            = ∑ j : Fin (W.d 0), (fun r : ℝ => W.a 0 j (γ' (r ^ N)) * ζ r ^ (j : ℕ)) from by
          funext r
          rw [Finset.sum_apply]]
        exact Finset.analyticAt_sum Finset.univ (fun j _ =>
          ((W.han 0 j).comp_of_eq hγ'N hγ'0N).mul (hζan.pow _))
      exact (hζan.pow _).add hsum
    have hcont : Tendsto (fun r => mpoly (c 0) (r ^ N) (ζ r)) (𝓝 (0 : ℝ))
        (𝓝 (mpoly (c 0) ((0 : ℝ) ^ N) (ζ 0))) := hΦan.continuousAt.tendsto
    have hlim0 : Tendsto (fun k : ℕ => mpoly (c 0) ((1 / (k + 1 : ℝ)) ^ N) (ζ (1 / (k + 1 : ℝ))))
        atTop (𝓝 (mpoly (c 0) ((0 : ℝ) ^ N) (ζ 0))) :=
      hcont.comp tendsto_one_div_add_atTop_nhds_zero_nat
    have hev1 : ∀ᶠ k : ℕ in atTop, (1 / (k + 1 : ℝ)) < r₀ :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (Iio_mem_nhds hr₀)
    have hev0 : ∀ᶠ k : ℕ in atTop,
        mpoly (c 0) ((1 / (k + 1 : ℝ)) ^ N) (ζ (1 / (k + 1 : ℝ))) = 0 := by
      filter_upwards [hev1] with k hk
      exact hzero _ ⟨by positivity, hk⟩
    have hlim1 : Tendsto (fun k : ℕ => mpoly (c 0) ((1 / (k + 1 : ℝ)) ^ N) (ζ (1 / (k + 1 : ℝ))))
        atTop (𝓝 0) :=
      Tendsto.congr' (hev0.mono fun k hk => hk.symm) tendsto_const_nhds
    have huniq : (0 : ℝ) = mpoly (c 0) ((0 : ℝ) ^ N) (ζ 0) := tendsto_nhds_unique hlim1 hlim0
    have hval : mpoly (c 0) ((0 : ℝ) ^ N) (ζ 0) = ζ 0 ^ (W.d 0) := by
      have hN0 : N ≠ 0 := ne_of_gt hN
      have hmp : mpoly (c 0) ((0 : ℝ) ^ N) (ζ 0)
          = ζ 0 ^ (W.d 0) + ∑ j : Fin (W.d 0), c 0 j ((0 : ℝ) ^ N) * ζ 0 ^ (j : ℕ) := rfl
      rw [hmp]
      have hcz : ∀ j : Fin (W.d 0), c 0 j ((0 : ℝ) ^ N) = 0 := by
        intro j
        show W.a 0 j (γ' ((0 : ℝ) ^ N)) = 0
        rw [zero_pow hN0, hγ'0, W.han0 0 j]
      rw [Finset.sum_eq_zero (fun j _ => by rw [hcz j, zero_mul]), add_zero]
    rw [hval] at huniq
    exact eq_zero_of_pow_eq_zero huniq.symm
  -- the final arc
  refine ⟨fun r => W.L (Fin.snoc (γ' (r ^ N)) (ζ r)), ?_, ?_, ?_⟩
  · have h2 : AnalyticAt ℝ (fun r => (Fin.snoc (γ' (r ^ N)) (ζ r) : Fin (n + 1) → ℝ)) 0 :=
      analyticAt_snoc hγ'N hζan
    exact AnalyticAt.comp
      (ContinuousLinearEquiv.analyticAt W.L (Fin.snoc (γ' (0 ^ N)) (ζ 0))) h2
  · have h0 : (Fin.snoc (γ' (0 ^ N)) (ζ 0) : Fin (n + 1) → ℝ) = 0 := by
      rw [zero_pow (ne_of_gt hN), hγ'0, hζ0]
      exact snoc_zero_zero n
    show W.L (Fin.snoc (γ' (0 ^ N)) (ζ 0)) = 0
    rw [h0, map_zero]
  · have hsnoc : AnalyticAt ℝ (fun r => (Fin.snoc (γ' (r ^ N)) (ζ r) : Fin (n + 1) → ℝ)) 0 :=
      analyticAt_snoc hγ'N hζan
    have hsmall : ∀ᶠ r in 𝓝 (0 : ℝ),
        ‖(Fin.snoc (γ' (r ^ N)) (ζ r) : Fin (n + 1) → ℝ)‖ < W.δ := by
      have h20 : (fun r => (Fin.snoc (γ' (r ^ N)) (ζ r) : Fin (n + 1) → ℝ)) 0 = 0 := by
        have h0 : (Fin.snoc (γ' (0 ^ N)) (ζ 0) : Fin (n + 1) → ℝ) = 0 := by
          rw [zero_pow (ne_of_gt hN), hγ'0, hζ0]
          exact snoc_zero_zero n
        simpa using h0
      have hb : ∀ᶠ r in 𝓝 (0 : ℝ),
          (fun r => (Fin.snoc (γ' (r ^ N)) (ζ r) : Fin (n + 1) → ℝ)) r ∈ Metric.ball 0 W.δ :=
        hsnoc.continuousAt.tendsto.eventually_mem
          (by simpa [h20] using Metric.ball_mem_nhds (0 : Fin (n + 1) → ℝ) W.hδ)
      filter_upwards [hb] with r hr
      simpa [Metric.mem_ball, dist_eq_norm] using hr
    obtain ⟨δ₀, hδ₀, hδ₀'⟩ := Metric.eventually_nhds_iff.mp hsmall
    refine ⟨min r₀ δ₀, lt_min hr₀ hδ₀, fun r hr => ?_⟩
    have hr' : r ∈ Set.Ioo (0 : ℝ) r₀ := ⟨hr.1, lt_of_lt_of_le hr.2 (min_le_left _ _)⟩
    have hδ' : ‖(Fin.snoc (γ' (r ^ N)) (ζ r) : Fin (n + 1) → ℝ)‖ < W.δ := by
      refine hδ₀' ?_
      rw [dist_eq_norm, Real.norm_eq_abs, sub_zero, abs_of_pos hr.1]
      exact lt_of_lt_of_le hr.2 (min_le_right _ _)
    have hyw : (Fin.snoc (γ' (r ^ N)) (ζ r) : Fin (n + 1) → ℝ) ∈ Yw W.d W.a τ := by
      rw [Yw_iff]
      have hInit : Fin.init (Fin.snoc (γ' (r ^ N)) (ζ r) : Fin (n + 1) → ℝ) = γ' (r ^ N) :=
        Fin.init_snoc _ _
      have hLast : (Fin.snoc (γ' (r ^ N)) (ζ r) : Fin (n + 1) → ℝ) (Fin.last n) = ζ r :=
        Fin.snoc_last _ _
      rw [hInit, hLast]
      have hbr : ∀ i : Fin (l + 1),
          mpoly (c i) (r ^ N) (ζ r) = Qeval W.d (coefFun W.d W.a (γ' (r ^ N))) (ζ r) i := by
        intro i
        rw [show mpoly (c i) (r ^ N) (ζ r)
          = mpoly (fun (j : Fin (W.d i)) (_ : ℝ) => W.a i j (γ' (r ^ N))) (r ^ N) (ζ r) from rfl]
        exact mpoly_coefFun W.d W.a γ' (r ^ N) (ζ r) i
      constructor
      · have h := hζsign r hr' 0
        rw [hσ0] at h
        rw [hbr 0] at h
        rw [sign_eq_zero_iff] at h
        exact h
      · intro j
        have h := hζsign r hr' (Fin.succ j)
        rw [hσs j] at h
        rw [hbr (Fin.succ j)] at h
        exact ((posSign_spec (W.hu0 (Fin.succ j))).2.2
          (Qeval W.d (coefFun W.d W.a (γ' (r ^ N))) (ζ r) (Fin.succ j))).mpr h
    exact L_mem_of_Yw F g (combineFam F g) rfl (fun j => rfl) W.L W.d W.a W.u W.δ
      W.hid W.hu W.hus τ hτ hδ' hyw

end Work.WilC4aCS
