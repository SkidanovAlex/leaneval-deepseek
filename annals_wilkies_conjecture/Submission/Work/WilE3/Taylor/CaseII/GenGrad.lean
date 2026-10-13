import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.eaEval_analytic
import Submission.Work.WilE3.Taylor.Grad.PolarDefs
import Submission.Work.WilE3.Taylor.Grad.hinge
import Submission.Work.WilE3.Taylor.Grad.sumSqGrad_le_norm_fderiv_sq
import Submission.Work.Taylor.Grad.grad_eaEval
import Submission.Work.WilE3.Taylor.CaseII.Defs
import Submission.Work.WilE3.Taylor.CaseII.GenGradAux
import Submission.Work.WilE3.Taylor.CaseII.exists_pos_of_ae_prod
import Submission.Work.WilE3.Taylor.CaseII.badArc_fixedBall
import Submission.Work.WilE3.Taylor.CaseII.pertSys_det_ne
import Submission.Work.WilE3.Taylor.CaseII.sphSys_det_ne

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / CaseII: **node T5** of the replacement route
  (design `sources/wilkiesE3caseII/wilkies_e3_caseII.md`, §3): the effective gradient inequality
  (Gabrielov 1995, Theorem 3.3)

  `∀ F ∃ K ∀ Φ (Φ y = 0), ∃ κ < 1, c > 0, 1/(1-κ) ≤ K.eval (atomDeg Φ), c |Φ|^κ ≤ ‖∇Φ‖` near `y`,

  proved from `Work.WilE3.MultiplicityBound` **without** the arc crux `ArcCrux`: the bad arcs are
  placed on the *nondegenerate* square systems `pertSys`/`sphSys` (the perturbed squared gradient
  `G·exp⟨v, x - y⟩` at a generic `v` and a fixed radius `δ`), where the generalised Case A count
  `CaseII.Gen.squareSystem_deficit` (node T2′) applies.  The mathematical core is
  `CaseII.badArc_contradiction`; this module supplies the measure theory (choosing `v`, `δ`),
  the Lagrange arc (node T3, `badArc_fixedBall`), the nondegeneracy of the systems (node T4,
  `pertSys_det_ne`/`sphSys_det_ne`) and the sign bookkeeping.

  This statement is *verbatim* the conclusion of the hinge
  `Work.WilE3.Taylor.Grad.ea_grad_of_arcCrux`, so that the latter can be replaced by it in
  `Work.WilE3.Taylor.ea_grad_of_multiplicity` (and, through it, in the target
  `Work.WilE3.Taylor.hasLoj_of_multiplicity`).
-/

set_option autoImplicit false
noncomputable section
open Classical Topology Filter MeasureTheory
open scoped Topology
open WilkiesDesign.E

namespace Work.WilE3.Taylor.CaseII

variable {k r : ℕ}

/-- **The effective gradient inequality for EA functions** (Gabrielov 1995, Theorem 3.3), from
`MultiplicityBound`, by the replacement route (nodes T2′–T5 of
`sources/wilkiesE3caseII/wilkies_e3_caseII.md`, §3).  Statement identical to
`Work.WilE3.Taylor.ea_grad_of_multiplicity`. -/
theorem ea_grad_of_multiplicity' (hMB : Work.WilE3.MultiplicityBound) :
    ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (Φ : EAPoly k r)
        (y : Fin k → ℝ), k + r ≤ F → eaEval c Φ y = 0 →
        ∃ (κ cst : ℝ), 0 ≤ κ ∧ κ < 1 ∧ 0 < cst ∧
          1 / (1 - κ) ≤ ((K.eval (atomDeg Φ) : ℕ) : ℝ) ∧
          (∀ᶠ x in 𝓝 y, cst * |eaEval c Φ x| ^ κ ≤
            ‖fderiv ℝ (fun z : Fin k → ℝ => eaEval c Φ z) x‖) := by
  intro F
  obtain ⟨K₀, hT2raw⟩ := Gen.squareSystem_deficit hMB F
  refine ⟨K₀ + 2, ?_⟩
  intro k r c Φ y hkr hΦy
  rcases k with _ | k
  · -- ## the degenerate case `k = 0`: the space is a point and `Φ y = 0`
    refine ⟨1 / 2, 1, by norm_num, by norm_num, one_pos, ?_, ?_⟩
    · have hev : (((K₀ + 2).eval (atomDeg Φ) : ℕ) : ℝ)
          = ((K₀.eval (atomDeg Φ) : ℕ) : ℝ) + 2 := by
        rw [Grad.eval_add_two]
        push_cast
        ring
      rw [hev]
      have h2 : (1 : ℝ) / (1 - 1 / 2) = 2 := by norm_num
      rw [h2]
      have h3 : (0 : ℝ) ≤ ((K₀.eval (atomDeg Φ) : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    · filter_upwards with x
      have hxy : x = y := Subsingleton.elim x y
      have hA0 : |eaEval c Φ y| = 0 := by rw [hΦy]; exact abs_zero
      rw [hxy, hA0, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), one_mul]
      exact norm_nonneg _
  · -- ## the main case
    set p : ℕ := K₀.eval (atomDeg Φ) + 1 with hp
    set q : ℕ := K₀.eval (atomDeg Φ) + 2 with hq
    set κ : ℝ := (p : ℝ) / (q : ℝ) with hκdef
    have hq_pos : 0 < q := by rw [hq]; omega
    have hp_lt_q : p < q := by rw [hp, hq]; omega
    have hκ_pos : 0 < κ := by rw [hκdef]; positivity
    have hκ_nonneg : 0 ≤ κ := le_of_lt hκ_pos
    have hκ_lt_one : κ < 1 := by
      rw [hκdef, div_lt_one (by positivity : (0 : ℝ) < (q : ℝ))]
      exact_mod_cast hp_lt_q
    have hκ_bound : 1 / (1 - κ) ≤ (((K₀ + 2).eval (atomDeg Φ) : ℕ) : ℝ) := by
      have h1 : 1 - κ = 1 / (q : ℝ) := by
        rw [hκdef]
        field_simp
        have hqp : q = p + 1 := by omega
        rw [hqp]
        push_cast
        ring
      rw [h1, one_div_one_div]
      have hnat : ((K₀ + 2).eval (atomDeg Φ) : ℕ) = K₀.eval (atomDeg Φ) + 2 := by
        rw [Grad.eval_add_two]
      rw [hnat, ← hq]
    refine ⟨κ, 1, hκ_nonneg, hκ_lt_one, one_pos, hκ_bound, ?_⟩
    by_contra hbadEv
    -- ## Step 1: points at which the gradient inequality fails
    have hbad_pts : ∀ n : ℕ, ∃ x : Fin (k + 1) → ℝ, dist x y < 1 / (n + 1) ∧
        ‖fderiv ℝ (fun z : Fin (k + 1) → ℝ => eaEval c Φ z) x‖ < |eaEval c Φ x| ^ κ := by
      intro n
      by_contra hcon
      push_neg at hcon
      refine hbadEv ?_
      filter_upwards [Metric.ball_mem_nhds y (by positivity : (0 : ℝ) < 1 / (n + 1))]
        with x hx
      have hxd : dist x y < 1 / (n + 1) := by simpa [Metric.mem_ball] using hx
      have hle : |eaEval c Φ x| ^ κ
          ≤ ‖fderiv ℝ (fun z : Fin (k + 1) → ℝ => eaEval c Φ z) x‖ := hcon x hxd
      simpa using hle
    choose x hx using hbad_pts
    -- ## Step 2: the sum-of-squares bad inequality at every bad point
    have hxsq : ∀ n : ℕ, (∑ i : Fin (k + 1), (eaEval c (eaD c i Φ) (x n)) ^ 2) ^ q
        < |eaEval c Φ (x n)| ^ (2 * p) := by
      intro n
      have h1 : (∑ i : Fin (k + 1),
            (Work.WilE3.Taylor.grad (fun z : Fin (k + 1) → ℝ => eaEval c Φ z) (x n) i) ^ 2)
          ≤ ‖fderiv ℝ (fun z : Fin (k + 1) → ℝ => eaEval c Φ z) (x n)‖ ^ 2 :=
        Work.WilE3.Taylor.Grad.sumSqGrad_le_norm_fderiv_sq
          (Work.WilE3.eaEval_analytic c Φ (x n))
      have h2 : (∑ i : Fin (k + 1), (eaEval c (eaD c i Φ) (x n)) ^ 2)
          ≤ ‖fderiv ℝ (fun z : Fin (k + 1) → ℝ => eaEval c Φ z) (x n)‖ ^ 2 := by
        simpa only [Grad.grad_eq_eaD] using h1
      have h3 : ‖fderiv ℝ (fun z : Fin (k + 1) → ℝ => eaEval c Φ z) (x n)‖ ^ 2
          < (|eaEval c Φ (x n)| ^ κ) ^ 2 :=
        pow_lt_pow_left₀ (hx n).2 (norm_nonneg _) (by norm_num)
      have h4 : (∑ i : Fin (k + 1), (eaEval c (eaD c i Φ) (x n)) ^ 2) ^ q
          < ((|eaEval c Φ (x n)| ^ κ) ^ 2) ^ q :=
        pow_lt_pow_left₀ (lt_of_le_of_lt h2 h3)
          (Finset.sum_nonneg fun i _ => sq_nonneg _) (by omega)
      have h5 : ((|eaEval c Φ (x n)| ^ κ) ^ 2) ^ q = |eaEval c Φ (x n)| ^ (2 * p) := by
        have hκq : κ * ((2 * q : ℕ) : ℝ) = ((2 * p : ℕ) : ℝ) := by
          rw [hκdef]
          have hqne : (q : ℝ) ≠ 0 := by positivity
          field_simp
          push_cast
          ring
        calc ((|eaEval c Φ (x n)| ^ κ) ^ 2) ^ q
            = (|eaEval c Φ (x n)| ^ κ) ^ ((2 * q : ℕ) : ℝ) := by
              rw [← pow_mul, Real.rpow_natCast]
          _ = |eaEval c Φ (x n)| ^ (κ * ((2 * q : ℕ) : ℝ)) :=
              (Real.rpow_mul (abs_nonneg (eaEval c Φ (x n))) κ _).symm
          _ = |eaEval c Φ (x n)| ^ ((2 * p : ℕ) : ℝ) := by rw [hκq]
          _ = |eaEval c Φ (x n)| ^ (2 * p) := Real.rpow_natCast _ _
      rw [h5] at h4
      exact h4
    -- ## Step 3: a definite sign for the bad points
    have hsign : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ᶠ n in atTop, 0 < σ * eaEval c Φ (x n) := by
      by_cases h : ∃ᶠ n in atTop, 0 < eaEval c Φ (x n)
      · exact ⟨1, Or.inl rfl, by simpa using h⟩
      · push_neg at h
        refine ⟨-1, Or.inr rfl, ?_⟩
        by_contra h2
        push_neg at h2
        have h3 : ∀ᶠ n in atTop, eaEval c Φ (x n) = 0 := by
          filter_upwards [h, h2] with n hn1 hn2
          linarith
        obtain ⟨n, hn⟩ := h3.exists
        have hbn := (hx n).2
        rw [hn, abs_zero, Real.zero_rpow hκ_pos.ne'] at hbn
        exact absurd hbn (not_lt_of_ge (norm_nonneg _))
    obtain ⟨σ, hσ, hσfreq⟩ := hsign
    -- ## Step 4: the signed polynomial `Ψ = C σ * Φ` and its bad sequence
    set Ψ : EAPoly (k + 1) r := MvPolynomial.C σ * Φ with hΨdef
    have hΨeval : ∀ z : Fin (k + 1) → ℝ, eaEval c Ψ z = σ * eaEval c Φ z := by
      intro z; rw [hΨdef, Grad.eaEval_C_mul]
    have hΨy : eaEval c Ψ y = 0 := by rw [hΨeval, hΦy, mul_zero]
    have hσ2 : σ ^ 2 = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
    have hQa : atomDeg Ψ ≤ atomDeg Φ := by
      rw [hΨdef]; exact Grad.atomDeg_C_mul_le σ Φ
    have hbadΨ : ∀ ρ : ℝ, 0 < ρ → ∃ z : Fin (k + 1) → ℝ, dist z y < ρ ∧ 0 < eaEval c Ψ z ∧
        (∑ l : Fin (k + 1), (eaEval c (eaD c l Ψ) (z)) ^ 2) ^ q
          < (eaEval c Ψ z) ^ (2 * p) := by
      intro ρ hρ
      have hρn : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ρ :=
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (eventually_lt_nhds hρ)
      obtain ⟨n, hnσ, hnρ⟩ := (hσfreq.and_eventually hρn).exists
      have hnρ' : (1 : ℝ) / (n + 1) < ρ := by push_cast; exact hnρ
      refine ⟨x n, lt_trans (hx n).1 hnρ', ?_, ?_⟩
      · rw [hΨeval]; exact hnσ
      · have hleft : (∑ l : Fin (k + 1), (eaEval c (eaD c l Ψ) (x n)) ^ 2)
            = (∑ i : Fin (k + 1), (eaEval c (eaD c i Φ) (x n)) ^ 2) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [hΨdef, Grad.eaD_C_mul, Grad.eaEval_C_mul, mul_pow, hσ2, one_mul]
        have hright : (eaEval c Ψ (x n)) ^ (2 * p) = |eaEval c Φ (x n)| ^ (2 * p) := by
          rw [hΨeval, mul_pow]
          have hσpow : σ ^ (2 * p) = 1 := by rw [pow_mul, hσ2, one_pow]
          rw [hσpow, one_mul, pow_mul, pow_mul, sq_abs]
        rw [hleft, hright]
        exact hxsq n
    -- ## Step 5: node T2′ specialized to the fixed format
    have hT2 : ∀ (c : EAChain (k + 1) r) (Q : EAPoly (k + 1) r) (y : Fin (k + 1) → ℝ)
        (γ : ℝ → Fin (k + 1) → ℝ) (P : Fin (k + 1) → EAPoly (k + 1) r) (m a : ℕ)
        (i₀ : Fin (k + 1)),
        P i₀ = Q → (∀ i, atomDeg (P i) ≤ 3 * atomDeg Q + 3) → k + 1 + r ≤ F →
        AnalyticAt ℝ γ 0 → γ 0 = y → 0 < a → 0 < m →
        analyticOrderAt (fun t : ℝ => γ t - y) 0 = a →
        analyticOrderAt (fun t : ℝ => eaEval c Q (γ t)) 0 = m →
        (∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i : Fin (k + 1), i ≠ i₀ →
          eaEval c (P i) (γ t) = 0) →
        (¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          (Matrix.of fun i j => eaEval c (eaD c j (P i)) (γ t)).det = 0) →
        ∃ (i : Fin (k + 1)) (n : ℕ),
          analyticOrderAt (fun t : ℝ => eaEval c (eaD c i Q) (γ t)) 0 = n ∧
            (K₀.eval (atomDeg Q) + 1) * n ≤ K₀.eval (atomDeg Q) * m :=
      fun c Q y γ P m a i₀ => hT2raw (k + 1) r c Q y γ P m a i₀
    -- ## Step 5: generic perturbation parameters `(v, d)`
    have hIntΦ : ∀ᵐ v : Fin (k + 1) → ℝ, ∀ (i₀ : Fin (k + 1)) (γ : ℝ → Fin (k + 1) → ℝ),
        AnalyticAt ℝ γ 0 → eaEval c Φ (γ 0) = 0 → IntHyp c Φ v i₀ γ →
        ¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), sysDet c (pertSys c Φ v i₀) (γ t) = 0 :=
      Filter.eventually_all.mpr fun i₀ => pertSys_det_ne c Φ i₀
    have hIntN : ∀ᵐ v : Fin (k + 1) → ℝ, ∀ (i₀ : Fin (k + 1)) (γ : ℝ → Fin (k + 1) → ℝ),
        AnalyticAt ℝ γ 0 → eaEval c (MvPolynomial.C (-1) * Φ) (γ 0) = 0 →
        IntHyp c (MvPolynomial.C (-1) * Φ) v i₀ γ →
        ¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          sysDet c (pertSys c (MvPolynomial.C (-1) * Φ) v i₀) (γ t) = 0 :=
      Filter.eventually_all.mpr fun i₀ => pertSys_det_ne c (MvPolynomial.C (-1) * Φ) i₀
    have hBdΦ : ∀ᵐ vd : (Fin (k + 1) → ℝ) × ℝ, ∀ (i₀ j₀ : Fin (k + 1)), i₀ ≠ j₀ →
        ∀ (γ : ℝ → Fin (k + 1) → ℝ), AnalyticAt ℝ γ 0 → eaEval c Φ (γ 0) = 0 →
        BdHyp c Φ vd.1 y vd.2 i₀ j₀ γ →
        ¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          sysDet c (sphSys c Φ vd.1 y vd.2 i₀ j₀) (γ t) = 0 := by
      refine Filter.eventually_all.mpr fun i₀ => Filter.eventually_all.mpr fun j₀ => ?_
      by_cases hij : i₀ = j₀
      · filter_upwards with vd hne
        exact False.elim (absurd hij hne)
      · have h := sphSys_det_ne c Φ y i₀ j₀ hij
        filter_upwards [h] with vd hv _
        exact hv
    have hBdN : ∀ᵐ vd : (Fin (k + 1) → ℝ) × ℝ, ∀ (i₀ j₀ : Fin (k + 1)), i₀ ≠ j₀ →
        ∀ (γ : ℝ → Fin (k + 1) → ℝ), AnalyticAt ℝ γ 0 →
        eaEval c (MvPolynomial.C (-1) * Φ) (γ 0) = 0 →
        BdHyp c (MvPolynomial.C (-1) * Φ) vd.1 y vd.2 i₀ j₀ γ →
        ¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
          sysDet c (sphSys c (MvPolynomial.C (-1) * Φ) vd.1 y vd.2 i₀ j₀) (γ t) = 0 := by
      refine Filter.eventually_all.mpr fun i₀ => Filter.eventually_all.mpr fun j₀ => ?_
      by_cases hij : i₀ = j₀
      · filter_upwards with vd hne
        exact False.elim (absurd hij hne)
      · have h := sphSys_det_ne c (MvPolynomial.C (-1) * Φ) y i₀ j₀ hij
        filter_upwards [h] with vd hv _
        exact hv
    have hgood : ∀ᵐ vd : (Fin (k + 1) → ℝ) × ℝ,
        (∀ (i₀ : Fin (k + 1)) (γ : ℝ → Fin (k + 1) → ℝ), AnalyticAt ℝ γ 0 →
          eaEval c Φ (γ 0) = 0 → IntHyp c Φ vd.1 i₀ γ →
          ¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            sysDet c (pertSys c Φ vd.1 i₀) (γ t) = 0) ∧
        (∀ (i₀ : Fin (k + 1)) (γ : ℝ → Fin (k + 1) → ℝ), AnalyticAt ℝ γ 0 →
          eaEval c (MvPolynomial.C (-1) * Φ) (γ 0) = 0 →
          IntHyp c (MvPolynomial.C (-1) * Φ) vd.1 i₀ γ →
          ¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            sysDet c (pertSys c (MvPolynomial.C (-1) * Φ) vd.1 i₀) (γ t) = 0) ∧
        (∀ (i₀ j₀ : Fin (k + 1)), i₀ ≠ j₀ → ∀ (γ : ℝ → Fin (k + 1) → ℝ), AnalyticAt ℝ γ 0 →
          eaEval c Φ (γ 0) = 0 → BdHyp c Φ vd.1 y vd.2 i₀ j₀ γ →
          ¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            sysDet c (sphSys c Φ vd.1 y vd.2 i₀ j₀) (γ t) = 0) ∧
        (∀ (i₀ j₀ : Fin (k + 1)), i₀ ≠ j₀ → ∀ (γ : ℝ → Fin (k + 1) → ℝ), AnalyticAt ℝ γ 0 →
          eaEval c (MvPolynomial.C (-1) * Φ) (γ 0) = 0 →
          BdHyp c (MvPolynomial.C (-1) * Φ) vd.1 y vd.2 i₀ j₀ γ →
          ¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            sysDet c (sphSys c (MvPolynomial.C (-1) * Φ) vd.1 y vd.2 i₀ j₀) (γ t) = 0) := by
      have h1 := (MeasureTheory.Measure.quasiMeasurePreserving_fst
        (μ := (volume : Measure (Fin (k + 1) → ℝ)))
        (ν := (volume : Measure ℝ))).ae hIntΦ
      have h2 := (MeasureTheory.Measure.quasiMeasurePreserving_fst
        (μ := (volume : Measure (Fin (k + 1) → ℝ)))
        (ν := (volume : Measure ℝ))).ae hIntN
      filter_upwards [h1, h2, hBdΦ, hBdN] with vd a b cc d
      exact ⟨a, b, cc, d⟩
    obtain ⟨v, d, hd, hgood⟩ := exists_pos_of_ae_prod hgood
    obtain ⟨hIntΦv, hIntNv, hBdΦv, hBdNv⟩ := hgood
    set δ : ℝ := Real.sqrt d with hδdef
    have hδ : 0 < δ := Real.sqrt_pos.mpr hd
    have hδsq : δ ^ 2 = d := Real.sq_sqrt hd.le
    -- ## Step 6: the bad arc (node T3)
    obtain ⟨y', γ, C, hC, hγan, hγ0, hΨy', harc, hcase⟩ :=
      badArc_fixedBall c Ψ y (Nat.succ_pos k) hp_lt_q hbadΨ hΨy v δ hδ
    have hcase' : (∃ i₀ : Fin (k + 1), ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        eaEval c (eaD c i₀ Ψ) (γ t) ≠ 0 ∧
        ∀ i : Fin (k + 1), i ≠ i₀ → eaEval c (pertMinor c Ψ v i₀ i) (γ t) = 0) ∨
      (∃ i₀ j₀ : Fin (k + 1), i₀ ≠ j₀ ∧ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        eaEval c (sphereP y d) (γ t) = 0 ∧
        (eaEval c (eaD c i₀ Ψ) (γ t) * (γ t j₀ - y j₀)
          - eaEval c (eaD c j₀ Ψ) (γ t) * (γ t i₀ - y i₀)) ≠ 0 ∧
        ∀ l : Fin (k + 1), l ≠ i₀ → l ≠ j₀ →
          eaEval c (pertMinor3 c Ψ v y i₀ j₀ l) (γ t) = 0) := by
      rcases hcase with h | h
      · exact Or.inl h
      · refine Or.inr ?_
        obtain ⟨i₀, j₀, hij, hh⟩ := h
        refine ⟨i₀, j₀, hij, ?_⟩
        rw [hδsq] at hh
        exact hh
    -- ## Step 7: the contradiction in the two sign cases
    rcases hσ with hσ1 | hσm1
    · -- ## the sign `σ = 1`, i.e. `Ψ = Φ`
      have hΨΦ : Ψ = Φ := by rw [hΨdef, hσ1]; simp
      have hT4i : ∀ (i₀ : Fin (k + 1)) (γ' : ℝ → Fin (k + 1) → ℝ), AnalyticAt ℝ γ' 0 →
          eaEval c Ψ (γ' 0) = 0 → IntHyp c Ψ v i₀ γ' →
          ¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), sysDet c (pertSys c Ψ v i₀) (γ' t) = 0 := by
        intro i₀ γ' ha h0 hh
        rw [hΨΦ] at h0 hh ⊢
        exact hIntΦv i₀ γ' ha h0 hh
      have hT4b : ∀ (i₀ j₀ : Fin (k + 1)), i₀ ≠ j₀ → ∀ (γ' : ℝ → Fin (k + 1) → ℝ),
          AnalyticAt ℝ γ' 0 → eaEval c Ψ (γ' 0) = 0 → BdHyp c Ψ v y d i₀ j₀ γ' →
          ¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            sysDet c (sphSys c Ψ v y d i₀ j₀) (γ' t) = 0 := by
        intro i₀ j₀ hij γ' ha h0 hh
        rw [hΨΦ] at h0 hh ⊢
        exact hBdΦv i₀ j₀ hij γ' ha h0 hh
      exact badArc_contradiction F hkr K₀ hT2 c Φ Ψ hQa p q hp hq y v d hT4i hT4b
        y' γ C hC hγan hγ0 hΨy' harc hcase'
    · -- ## the sign `σ = -1`, i.e. `Ψ = C (-1) * Φ`
      have hΨΦ : Ψ = MvPolynomial.C (-1) * Φ := by rw [hΨdef, hσm1]
      have hT4i : ∀ (i₀ : Fin (k + 1)) (γ' : ℝ → Fin (k + 1) → ℝ), AnalyticAt ℝ γ' 0 →
          eaEval c Ψ (γ' 0) = 0 → IntHyp c Ψ v i₀ γ' →
          ¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), sysDet c (pertSys c Ψ v i₀) (γ' t) = 0 := by
        intro i₀ γ' ha h0 hh
        rw [hΨΦ] at h0 hh ⊢
        exact hIntNv i₀ γ' ha h0 hh
      have hT4b : ∀ (i₀ j₀ : Fin (k + 1)), i₀ ≠ j₀ → ∀ (γ' : ℝ → Fin (k + 1) → ℝ),
          AnalyticAt ℝ γ' 0 → eaEval c Ψ (γ' 0) = 0 → BdHyp c Ψ v y d i₀ j₀ γ' →
          ¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
            sysDet c (sphSys c Ψ v y d i₀ j₀) (γ' t) = 0 := by
        intro i₀ j₀ hij γ' ha h0 hh
        rw [hΨΦ] at h0 hh ⊢
        exact hBdNv i₀ j₀ hij γ' ha h0 hh
      exact badArc_contradiction F hkr K₀ hT2 c Φ Ψ hQa p q hp hq y v d hT4i hT4b
        y' γ C hC hγan hγ0 hΨy' harc hcase'

end Work.WilE3.Taylor.CaseII
