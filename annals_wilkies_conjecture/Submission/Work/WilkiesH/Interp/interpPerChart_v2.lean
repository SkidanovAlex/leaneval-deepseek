import Mathlib
import Submission.Work.WilkiesH.Count.Interface
import Submission.Work.WilkiesH.Defs
import Submission.Work.WilkiesH.Basic
import Submission.Work.WilkiesH.Interp.V2Defs
import Submission.Work.WilkiesH.Interp.exists_params_v2
import Submission.Work.WilkiesH.Interp.v2_box_poly
import Submission.Work.WilkiesH.Interp.exists_convexBoxCover_openCube
import Submission.Work.WilkiesH.Interp.norm_iteratedFDeriv_comp_proj_le
import Submission.Work.WilkiesH.Interp.degreeHeightLE_comp_embedding

/-!
# The interpolation step (`v2` route): `InterpPerChart` from the Siegel box polynomials

This file assembles `Work.WilkiesH.InterpPerChart S F n` (BNZ Prop. 6.1, the per-chart
interpolation step) from

* `Work.WilkiesH.Interp.exists_params_v2` — for every chart dimension `μ ≤ n` a single
  polynomial `q_μ` bounding the parameters `b`, `⌈1/ρ⌉^μ · d`, `b+1` and `log (1/ε)`, with
  `above μ b d Q ρ ε < liou μ d Q g H`;
* `Work.WilkiesH.Interp.v2_box_poly` — the Siegel–Wilkie polynomial on one small box
  (Siegel's lemma + Taylor + Lipschitz + Liouville).

The chart `φ : openCube μ → X` is covered by `≤ ⌈1/ρ⌉^μ` convex boxes of diameter `ρ`
(`Interp.exists_convexBoxCover_openCube`); on each box we take the polynomial of
`v2_box_poly` and multiply the box polynomials together.  The product has degree
`≤ ⌈1/ρ⌉^μ · d` and vanishes at `x ∘ e` for every point of `degreeHeightLE X g H` within `ε`
of the chart.  The domination of the single polynomial `q` over all the per-`μ` polynomials
`q_μ` is `eval_le_sum_sq_add_one` (`q := ∑_ν (q_ν² + 1)`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilkiesH.Interp

open WilkiesDesign WilkiesConjecture

/-! ## Elementary topological facts about the open cube -/

theorem convex_openCube (μ : ℕ) : Convex ℝ (openCube μ) := by
  intro x hx y hy a b ha hb hab i
  have key := convex_Ioo (0 : ℝ) 1 (hx i) (hy i) ha hb hab
  simpa [Pi.add_apply, Pi.smul_apply] using key

theorem isOpen_openCube_v2 (μ : ℕ) : IsOpen (openCube μ) := by
  have h : openCube μ = ⋂ i : Fin μ, {t : Fin μ → ℝ | t i ∈ Set.Ioo (0 : ℝ) 1} := by
    ext t; simp [openCube]
  rw [h]
  exact isOpen_iInter_of_finite fun i => isOpen_Ioo.preimage (continuous_apply i)

/-! ## Dominating a family of parameter polynomials -/

/-- `y ≤ y ^ 2 + 1` in the form needed: a parameter polynomial is dominated by the sum of
the squares-plus-one of a finite family containing it. -/
theorem eval_le_sum_sq_add_one {k : ℕ} (q : Fin k → MvPolynomial (Fin 3) ℝ) (x : Fin 3 → ℝ)
    (j : Fin k) :
    (q j).eval x ≤ (∑ i, ((q i) ^ 2 + (1 : MvPolynomial (Fin 3) ℝ))).eval x := by
  rw [MvPolynomial.eval_sum]
  have h1 : (q j).eval x ≤ ((q j) ^ 2 + (1 : MvPolynomial (Fin 3) ℝ)).eval x := by
    have he : ((q j) ^ 2 + (1 : MvPolynomial (Fin 3) ℝ)).eval x
        = ((q j).eval x) ^ 2 + 1 := by
      rw [map_add, map_pow, map_one]
    rw [he]
    nlinarith [sq_nonneg ((q j).eval x - 1 / 2)]
  have h2 : ((q j) ^ 2 + (1 : MvPolynomial (Fin 3) ℝ)).eval x
      ≤ ∑ i, ((q i) ^ 2 + (1 : MvPolynomial (Fin 3) ℝ)).eval x :=
    Finset.single_le_sum (f := fun i => ((q i) ^ 2 + (1 : MvPolynomial (Fin 3) ℝ)).eval x)
      (fun i _ => by
        rw [map_add, map_pow, map_one]
        positivity)
      (Finset.mem_univ j)
  linarith

/-- The map of an integral polynomial into `ℝ` does not increase the total degree. -/
lemma totalDegree_map_le_int {n : ℕ} (P : MvPolynomial (Fin n) ℤ) :
    (P.map (Int.castRingHom ℝ)).totalDegree ≤ P.totalDegree := by
  classical
  rw [MvPolynomial.totalDegree, MvPolynomial.totalDegree, Finset.sup_le_iff]
  intro m hm
  exact Finset.le_sup (f := fun m : Fin n →₀ ℕ => m.sum fun _ e => e) (by
    rw [MvPolynomial.mem_support_iff] at hm ⊢
    intro h
    exact hm (by rw [MvPolynomial.coeff_map, h, map_zero]))

/-! ## Numerical consequences of `above < liou` -/

/-- **The radius is at most one.**  Useful consequence of the strict inequality
`above < liou`: the first term of `above` is `√(monoCount) · ρ ^ b` and `liou ≤ 1`, so
`ρ ^ b < 1` and hence `ρ ≤ 1` (for `ρ ≥ 0`, `ε ≥ 0` and `b ≥ 1`). -/
theorem rho_le_one_of_above_lt_liou {μ b d Q g H : ℕ} {ρ ε : ℝ}
    (hb : 1 ≤ b) (hQ : 1 ≤ Q) (hH : 1 ≤ H) (hρ0 : 0 ≤ ρ) (hε0 : 0 ≤ ε)
    (h : above μ b d Q ρ ε < liou μ d Q g H) : ρ ≤ 1 := by
  have hN1 : (1 : ℝ) ≤ ((Work.WilkiesH.monoCount (μ + 1) d : ℕ) : ℝ) := by
    have h1 : 1 ≤ Work.WilkiesH.monoCount (μ + 1) d :=
      Fintype.card_pos_iff.mpr ⟨⟨fun _ => 0, by simp⟩⟩
    exact_mod_cast h1
  -- `liou ≤ 1`
  have hliou1 : liou μ d Q g H ≤ 1 := by
    rw [liou, one_div]
    refine inv_le_one_of_one_le₀ ?_
    refine one_le_pow₀ ?_
    have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
    have hH1 : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH
    have hp : (1 : ℝ) ≤ (H : ℝ) ^ (((μ + 1) + 1) * d * g) := one_le_pow₀ hH1
    have hNQ : (1 : ℝ) ≤ ((Work.WilkiesH.monoCount (μ + 1) d : ℕ) : ℝ) * (Q : ℝ) := by
      have h := mul_le_mul hN1 hQ1 (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity : (0 : ℝ) ≤ ((Work.WilkiesH.monoCount (μ + 1) d : ℕ) : ℝ))
      simpa using h
    have h := mul_le_mul hNQ hp (by norm_num : (0 : ℝ) ≤ 1)
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) hNQ)
    simpa using h
  -- `1 ≤ ∑_j (√μ)^{3j} d^j / j!`
  have hsum1 : (1 : ℝ) ≤ ∑ j ∈ Finset.range (b + 1),
      ((Real.sqrt (μ : ℝ)) ^ (3 * j) * (d : ℝ) ^ j) / (((j.factorial : ℕ) : ℝ)) := by
    have h0mem : (0 : ℕ) ∈ Finset.range (b + 1) := Finset.mem_range.mpr (by omega)
    have h0val : ((Real.sqrt (μ : ℝ)) ^ (3 * 0) * (d : ℝ) ^ 0)
        / ((((0 : ℕ).factorial : ℕ) : ℝ)) = 1 := by norm_num
    have hnonneg : ∀ j ∈ Finset.range (b + 1),
        0 ≤ ((Real.sqrt (μ : ℝ)) ^ (3 * j) * (d : ℝ) ^ j) / (((j.factorial : ℕ) : ℝ)) := by
      intro j _
      have hf : (0 : ℝ) < (((j.factorial : ℕ) : ℝ)) := by positivity
      have : 0 ≤ (Real.sqrt (μ : ℝ)) ^ (3 * j) * (d : ℝ) ^ j := by positivity
      exact div_nonneg this hf.le
    calc (1 : ℝ)
        = ((Real.sqrt (μ : ℝ)) ^ (3 * 0) * (d : ℝ) ^ 0) / ((((0 : ℕ).factorial : ℕ) : ℝ)) :=
          h0val.symm
      _ ≤ ∑ j ∈ Finset.range (b + 1),
            ((Real.sqrt (μ : ℝ)) ^ (3 * j) * (d : ℝ) ^ j) / (((j.factorial : ℕ) : ℝ)) :=
          Finset.single_le_sum (f := fun j => ((Real.sqrt (μ : ℝ)) ^ (3 * j) * (d : ℝ) ^ j)
            / (((j.factorial : ℕ) : ℝ))) (fun j hj => hnonneg j hj) h0mem
  -- `√(monoCount) · ρ ^ b ≤ above`
  have habove : Real.sqrt ((Work.WilkiesH.monoCount (μ + 1) d : ℕ) : ℝ) * ρ ^ b
      ≤ above μ b d Q ρ ε := by
    rw [above]
    have hρb : 0 ≤ ρ ^ b := pow_nonneg hρ0 b
    have hs : 0 ≤ Real.sqrt ((Work.WilkiesH.monoCount (μ + 1) d : ℕ) : ℝ) := Real.sqrt_nonneg _
    have h1 : Real.sqrt ((Work.WilkiesH.monoCount (μ + 1) d : ℕ) : ℝ) * ρ ^ b
        ≤ Real.sqrt ((Work.WilkiesH.monoCount (μ + 1) d : ℕ) : ℝ) * ρ ^ b
          * (∑ j ∈ Finset.range (b + 1),
              ((Real.sqrt (μ : ℝ)) ^ (3 * j) * (d : ℝ) ^ j) / (((j.factorial : ℕ) : ℝ))) := by
      have h2 : Real.sqrt ((Work.WilkiesH.monoCount (μ + 1) d : ℕ) : ℝ) * ρ ^ b * 1
          ≤ Real.sqrt ((Work.WilkiesH.monoCount (μ + 1) d : ℕ) : ℝ) * ρ ^ b
            * (∑ j ∈ Finset.range (b + 1),
                ((Real.sqrt (μ : ℝ)) ^ (3 * j) * (d : ℝ) ^ j) / (((j.factorial : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hsum1 (mul_nonneg hs hρb)
      simpa using h2
    have h2 : 0 ≤ ((Work.WilkiesH.monoCount (μ + 1) d : ℕ) : ℝ) * (Q : ℝ)
        * ((d : ℝ) + 1) ^ (b + 1) * ((Real.sqrt (μ : ℝ) * ρ) ^ (b + 1))
        / (((((b + 1).factorial : ℕ) : ℝ))) := by positivity
    have h3 : 0 ≤ ((Work.WilkiesH.monoCount (μ + 1) d : ℕ) : ℝ) * (Q : ℝ) * (d : ℝ)
        * ((μ : ℝ) + 1) * ε :=
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity))
        (by positivity)) (by positivity)) hε0
    linarith
  have h2 : Real.sqrt ((Work.WilkiesH.monoCount (μ + 1) d : ℕ) : ℝ) * ρ ^ b < 1 :=
    lt_of_lt_of_le (lt_of_le_of_lt habove h) hliou1
  have h3 : ρ ^ b < 1 := by
    have hsqrt1 : (1 : ℝ) ≤ Real.sqrt ((Work.WilkiesH.monoCount (μ + 1) d : ℕ) : ℝ) :=
      Real.one_le_sqrt.mpr hN1
    have hpos : 0 < Real.sqrt ((Work.WilkiesH.monoCount (μ + 1) d : ℕ) : ℝ) :=
      lt_of_lt_of_le zero_lt_one hsqrt1
    nlinarith [h2, pow_nonneg hρ0 b, hsqrt1]
  by_contra hc
  push_neg at hc
  have h4 : 1 < ρ ^ b :=
    lt_of_lt_of_le hc (by
      calc ρ = ρ ^ 1 := (pow_one ρ).symm
        _ ≤ ρ ^ b := pow_le_pow_right₀ (le_of_lt hc) hb)
  linarith

/-! ## The interpolation step -/

/-- **Area (I): the interpolation step (BNZ Prop. 6.1), `v2` route.**
`Work.WilkiesH.InterpPerChart S F n` via the Siegel box polynomials
(`Interp.siegel_poly_exists_v2` + `Interp.v2_box_poly`) instead of the interpolation
determinant. -/
theorem interpPerChart_v2 {S : WilkiesDesign.SOMin} (F n : ℕ)
    (hG : WilkiesDesign.AlgLemma S F n) : Work.WilkiesH.InterpPerChart S F n := by
  classical
  choose q hq using fun ν : Fin (n + 1) => exists_params_v2 (ν : ℕ)
  refine ⟨∑ ν : Fin (n + 1), ((q ν) ^ 2 + (1 : MvPolynomial (Fin 3) ℝ)), ?_⟩
  intro D μ X hμn hX hXcube hdim g H
  have hμlt : μ < n + 1 := Nat.lt_succ_of_le hμn
  obtain ⟨b, d, ρ, ε, Q, hb, hd, hQ, hρ, hε0, hε1, hsqr, hcard, hineq, hbq, hb1q, hdq, hεq⟩ :=
    hq ⟨μ, hμlt⟩ D g (max H 1) (le_max_right H 1)
  have hlogmax : Real.log (((max H 1 : ℕ)) : ℝ) = Real.log (H : ℝ) := by
    rcases Nat.eq_zero_or_pos H with h0 | h1
    · subst h0; norm_num
    · rw [Nat.max_eq_left h1]
  have hdom : ∀ x : Fin 3 → ℝ, (q ⟨μ, hμlt⟩).eval x
      ≤ (∑ ν : Fin (n + 1), ((q ν) ^ 2 + (1 : MvPolynomial (Fin 3) ℝ))).eval x :=
    fun x => eval_le_sum_sq_add_one q x ⟨μ, hμlt⟩
  refine ⟨(Nat.ceil (1 / ρ)) ^ μ * d, b + 1, ε, hε0, hε1, ?_, ?_, ?_, ?_⟩
  · -- the degree bound
    have h := hdq
    rw [hlogmax] at h
    exact le_trans h (hdom ![(D : ℝ), (g : ℝ), Real.log H])
  · -- the smoothness bound
    have h := hb1q
    rw [hlogmax] at h
    exact le_trans h (hdom ![(D : ℝ), (g : ℝ), Real.log H])
  · -- the bound on `log (1/ε)`
    have h := hεq
    rw [hlogmax] at h
    exact le_trans h (hdom ![(D : ℝ), (g : ℝ), Real.log H])
  · -- the polynomial for each chart and each embedding
    intro φ hφmem hφdiff hφjet e
    have hρ1 : ρ ≤ 1 := rho_le_one_of_above_lt_liou (μ := μ) (d := d) (Q := Q) (g := g)
      (H := max H 1) (ρ := ρ) (ε := ε) hb hQ (le_max_right H 1) hρ.le hε0.le hineq
    have hopen : IsOpen (openCube μ) := isOpen_openCube_v2 μ
    have hconv : Convex ℝ (openCube μ) := convex_openCube μ
    have hφat : ∀ t ∈ openCube μ, ContDiffAt ℝ (b + 1) φ t := fun t ht =>
      hφdiff.contDiffAt (hopen.mem_nhds ht)
    -- the restricted chart `Ψ = π_e ∘ φ`
    set Ψ : (Fin μ → ℝ) → (Fin (μ + 1) → ℝ) := fun t i => φ t (e i) with hΨ
    have hΨval : ∀ t ∈ openCube μ, ∀ i, |Ψ t i| ≤ 1 := by
      intro t ht i
      have h1 : (φ t) (e i) ∈ Set.Icc (0 : ℝ) 1 := hXcube (hφmem t ht) (e i)
      have h2 : Ψ t i = φ t (e i) := rfl
      rw [h2]
      exact abs_le.mpr ⟨by linarith [h1.1], h1.2⟩
    have hΨsmooth : ContDiffOn ℝ (b + 1 : ℕ) Ψ (openCube μ) := by
      let L : (Fin n → ℝ) →L[ℝ] (Fin (μ + 1) → ℝ) :=
        LinearMap.mkContinuous
          { toFun := fun v i => v (e i)
            map_add' := fun v w => by funext i; simp
            map_smul' := fun c v => by funext i; simp }
          1 (fun v => by
            rw [one_mul]
            exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => norm_le_pi_norm v (e i))
      have key : ContDiffOn ℝ (b + 1 : ℕ) (fun u : Fin μ → ℝ => L (φ u)) (openCube μ) :=
        L.contDiff.comp_contDiffOn hφdiff
      have hfun : Ψ = fun u : Fin μ → ℝ => L (φ u) := by
        funext u i
        rfl
      rw [hfun]
      exact key
    have hΨjet : ∀ k, k ≤ b + 1 → ∀ t ∈ openCube μ, ‖iteratedFDeriv ℝ k Ψ t‖ ≤ 1 := by
      intro k hk t ht
      have h1 := norm_iteratedFDeriv_comp_proj_le e φ hk t (hφat t ht)
      have h2 := hφjet k hk t ht
      exact h1.trans h2
    -- the cover of the chart domain by boxes of diameter `ρ`
    obtain ⟨C, hCconv, hCsub, hCne, hCdiam, hCcover, hCcard⟩ :=
      exists_convexBoxCover_openCube μ hρ
    -- one Siegel polynomial per box, pushed forward to a real polynomial
    have hbox : ∀ c ∈ C, ∃ P : MvPolynomial (Fin (μ + 1)) ℝ, P ≠ 0 ∧ P.totalDegree ≤ d ∧
        ∀ y : Fin (μ + 1) → ℝ, (∀ i, |y i| ≤ 1) →
          y ∈ WilkiesConjecture.degreeHeightLE Set.univ g (max H 1) →
          (∃ t ∈ c, dist (Ψ t) y < ε) →
          MvPolynomial.eval y P = 0 := by
      intro c hc
      obtain ⟨s₀, hs₀⟩ := hCne c hc
      have hdiam : ∀ t ∈ c, ‖t - s₀‖ ≤ ρ := by
        intro t ht
        rw [pi_norm_le_iff_of_nonneg hρ.le]
        intro l
        simpa [Pi.sub_apply] using hCdiam c hc t ht s₀ hs₀ l
      obtain ⟨P, hPne, hPdeg, hPcoef, hPvanish⟩ :=
        v2_box_poly (μ := μ) (b := b) (d := d) (Q := Q) (ρ := ρ) (ε := ε) (g := g)
          (H := max H 1) hb hd hQ (le_max_right H 1) hρ hρ1 hsqr hcard
          (hCconv c hc) (hCsub c hc) hs₀ hdiam hΨsmooth hΨjet hΨval hineq
      refine ⟨P.map (Int.castRingHom ℝ), ?_, ?_, ?_⟩
      · intro h
        exact hPne (MvPolynomial.map_injective (Int.castRingHom ℝ) Int.cast_injective
          (by rw [h, map_zero (MvPolynomial.map (Int.castRingHom ℝ))]))
      · exact (totalDegree_map_le_int P).trans hPdeg
      · intro y hy1 hy hnear
        exact hPvanish y hy1 hy hnear
    -- the product over the boxes
    let Ps : {c : Set (Fin μ → ℝ) // c ∈ C} → MvPolynomial (Fin (μ + 1)) ℝ :=
      fun c => (hbox c.1 c.2).choose
    have hPsne : ∀ c, Ps c ≠ 0 := fun c => (hbox c.1 c.2).choose_spec.1
    have hPsdeg : ∀ c, (Ps c).totalDegree ≤ d := fun c => (hbox c.1 c.2).choose_spec.2.1
    have hPsvanish : ∀ c, ∀ y : Fin (μ + 1) → ℝ, (∀ i, |y i| ≤ 1) →
        y ∈ WilkiesConjecture.degreeHeightLE Set.univ g (max H 1) →
        (∃ t ∈ c.1, dist (Ψ t) y < ε) → MvPolynomial.eval y (Ps c) = 0 :=
      fun c => (hbox c.1 c.2).choose_spec.2.2
    refine ⟨∏ c, Ps c, ?_, ?_, ?_⟩
    · exact Finset.prod_ne_zero_iff.mpr fun c _ => hPsne c
    · -- the total degree of the product
      have hdeg : (∏ c, Ps c).totalDegree ≤ C.card * d := by
        refine (MvPolynomial.totalDegree_finsetProd Finset.univ Ps).trans ?_
        calc (∑ c : {c : Set (Fin μ → ℝ) // c ∈ C}, (Ps c).totalDegree)
            ≤ ∑ _c : {c : Set (Fin μ → ℝ) // c ∈ C}, d :=
              Finset.sum_le_sum fun c _ => hPsdeg c
          _ = C.card * d := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
      have hCd : C.card * d ≤ (Nat.ceil (1 / ρ)) ^ μ * d :=
        Nat.mul_le_mul_right d hCcard
      exact (le_trans hdeg hCd)
    · -- the vanishing at the required points
      intro x hx hnear
      obtain ⟨hxX, hint, hdegx, hheightx⟩ := hx
      obtain ⟨t, ht, hdist⟩ := hnear
      obtain ⟨c, hcC, htc⟩ := hCcover t ht
      have hy1 : ∀ i, |(fun i : Fin (μ + 1) => x (e i)) i| ≤ 1 := by
        intro i
        have h1 : x (e i) ∈ Set.Icc (0 : ℝ) 1 := hXcube hxX (e i)
        exact abs_le.mpr ⟨by linarith [h1.1], h1.2⟩
      have hy : (fun i : Fin (μ + 1) => x (e i))
          ∈ WilkiesConjecture.degreeHeightLE Set.univ g (max H 1) := by
        obtain ⟨hint', hfin', hheight'⟩ := degreeHeightLE_comp_embedding e X g H ⟨hxX, hint, hdegx, hheightx⟩
        exact ⟨Set.mem_univ _, hint', hfin', hheight'.trans (by exact_mod_cast le_max_left H 1)⟩
      have hdist' : dist (Ψ t) (fun i : Fin (μ + 1) => x (e i)) < ε := by
        refine lt_of_le_of_lt ?_ hdist
        rw [dist_pi_le_iff dist_nonneg]
        intro i
        exact dist_le_pi_dist (φ t) x (e i)
      have h1 : MvPolynomial.eval (fun i : Fin (μ + 1) => x (e i)) (Ps ⟨c, hcC⟩) = 0 :=
        hPsvanish ⟨c, hcC⟩ (fun i => x (e i)) hy1 hy ⟨t, htc, hdist'⟩
      rw [MvPolynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ _) h1

end Work.WilkiesH.Interp
