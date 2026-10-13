/-
  WilG4cW / `StepStageOfAxesW` — BNZ §5.4: the production of `StepStageW` from the frozen axes
  and the corrected Corollary 5.5 `Work.WilG4a.F1AffineW`.

  This is a copy of `Submission/Work/WilG4c/StepStageOfAxes.lean` with

  * `h1 : ∀ q, F1Affine S q` replaced by the corrected `h1 : ∀ q, F1AffineW S q`;
  * the chart output read through `H1ChartW` instead of `H1Chart` (the per-chart conditions
    `0 < β l` replaced by `ChartInW`, i.e. `β ≥ 0` plus the image clause);
  * the multi-curve data produced by `Work.WilG4cW.CurveDataPullCW` instead of
    `Work.WilkG4c.CurveDataPullC`.

  The change in the per-chart conditions shows up only in the "chart conditions" block: for the
  shrunk chart `(α₀ + β₀ c, β₀/4)` one must also prove the image clause
  `α l + β l · t ∈ I` for `t ∈ I` — it follows from the image clause of the *unshrunk* chart at
  the point `c + t/4 ∈ I` (using `0 ≤ c ≤ 3/4`).
-/
import Mathlib
import Submission.Work.WilG4a.F1AffineW
import Submission.Work.WilG4c.StepStageAux
import Submission.Work.WilG4c.countPolySubst
import Submission.Work.WilG4cW.StepH1OutW
import Submission.Work.WilG4cW.StepStageW
import Submission.Work.WilG4cW.CurveDataPullCW

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

theorem StepStage_of_axesW (S : SOMin) (hcd : SOMin.SharpCD S) (hder : SOMin.SharpDeriv S)
    (p n : ℕ) (hn : 1 ≤ n) (h1 : ∀ q, Work.WilG4a.F1AffineW S q)
    (hchoice : Work.WilkG4c.ChoiceHyp S) (hbdd : Work.WilkG4c.BddDxHyp S) :
    StepStageW S p n := by
  classical
  obtain ⟨Afc, Cfc, hFPCshr⟩ := shrunkChart_graph_mem S p
  intro F0
  obtain ⟨Ac, Bc, hCurveA⟩ := Work.WilG4c.CurveFamAlphaListPureSliced S hcd hder hchoice p n F0
  obtain ⟨At, Bt, hTupG⟩ := tupleFamBig_graph_mem S hcd hder p n Ac Bc F0
  obtain ⟨a₀, b₀, c₀, hH1raw⟩ := h1 p (F0 + At)
  obtain ⟨ccount, hccount⟩ := Work.WilG4c.countPolySubst n Bt c₀
  let b₁ : MvPolynomial (Fin 2) ℕ :=
    MvPolynomial.bind₁ (R := ℕ) ![Bt, MvPolynomial.X 1 + MvPolynomial.C 1] b₀
  let bstage : MvPolynomial (Fin 2) ℕ :=
    MvPolynomial.C Cfc * (MvPolynomial.C 2 * b₁ + MvPolynomial.C 2) + MvPolynomial.C Cfc
  refine ⟨2 * a₀ + Afc, bstage, MvPolynomial.C 16 * ccount, ?_⟩
  intro D r k ε hr hε hε1 Λ F hP hΩ hval
  -- ## the choice data
  let γ0 : (i : Fin k) → (L : List (Fin (n + 1))) → L.length ≤ r →
      (Fin p → ℝ) → ℝ → (Fin n → ℝ) :=
    fun i L hL => Classical.choose (hCurveA D r Set.univ (F i) (hΩ i) L hL)
  let γs : (i : Fin k) → (Fin p → ℝ) → (L : List (Fin (n + 1))) → ℝ → (Fin n → ℝ) :=
    fun i l L => if h : L.length ≤ r then γ0 i L h l else fun _ => 1 / 2
  have hcspec : ∀ (i : Fin k) (l : Fin p → ℝ), Work.WilkG4c.ChoiceOut (F i l) r (γs i l) := by
    intro i l L hL
    show Work.WilkG4c.ChoiceOutAt (F i l) L (γs i l L)
    have hγL : γs i l L = γ0 i L hL l := by
      dsimp only [γs]
      exact dite_eq_left hL
    rw [hγL]
    exact fun x hx => (Classical.choose_spec (hCurveA D r Set.univ (F i) (hΩ i) L hL)).2
      l (Set.mem_univ l) x hx
  -- ## the tuple-indexed choice data
  let γsIdx : (i : Fin k) → MIdx n r → (Fin p → ℝ) → ℝ → (Fin n → ℝ) :=
    fun i m l x => γs i l (LcOf m) x
  -- ## the fibre-sup finiteness data
  let Bbad : (i : Fin k) → (Fin p → ℝ) → Finset ℝ := fun i l =>
    Classical.choose (Work.WilG4c.hBdd_of_member S hder hbdd (F i) (hΩ i)
      (fun l x hx m hm y hy => hP.1 i l x hx m hm y hy) l)
  have hb : ∀ (i : Fin k) (l : Fin p → ℝ), Work.WilkG4c.FibreBdd (F i l) r (Bbad i l) :=
    fun i l => Classical.choose_spec (Work.WilG4c.hBdd_of_member S hder hbdd (F i) (hΩ i)
      (fun l x hx m hm y hy => hP.1 i l x hx m hm y hy) l)
  -- ## `F1AffineW` applied to the padded tuple
  have hTupGraf : ∀ j : Fin (tupleSizeBig k n r),
      famGraph (tupleFamBig F γsIdx j) ∈ S.Ω (F0 + At) (MvPolynomial.eval ![D, r] Bt)
        (p + 1 + 1) := by
    intro j
    refine Work.WilG1.Omega.mono (hTupG D r k F γsIdx ?_ hΩ j) le_add_self le_rfl
    intro i m ι
    have h := (Classical.choose_spec (hCurveA D r Set.univ (F i) (hΩ i) (LcOf m)
      (LcOf_length_le m))).1 ι
    have hγe : γsIdx i m = γ0 i (LcOf m) (LcOf_length_le m) := by
      funext l x
      dsimp only [γsIdx, γs]
      rw [dite_eq_left (LcOf_length_le m)]
    rw [hγe]
    exact h
  obtain ⟨Φ₀, hΦ₀card, hΦ₀ok, hΦ₀cov⟩ :=
    hH1raw (MvPolynomial.eval ![D, r] Bt) (r + 1) (tupleSizeBig k n r) (ε / 2)
      (by linarith) (by linarith) Set.univ (tupleFamBig F γsIdx) hTupGraf
      (fun j l _ t ht => tupleFamBig_val (F := F) (γs := γsIdx) (r := r) hP.1 j l t ht)
  -- ## the `H1ChartW` output
  have hH1 : ∀ cb ∈ Φ₀, H1ChartW F γsIdx cb.1 cb.2 :=
    h1Chart_of_f1affine_bigW (Φ₀ := Φ₀) (F := F) (γs := γsIdx) (k := k) (r := r)
      (fun cb hcb l => (hΦ₀ok cb hcb).2.2 l (Set.mem_univ l))
  -- ## the shrunk charts
  refine ⟨shrunkCharts Φ₀, ?_, ?_, ?_, ?_⟩
  · -- the cardinality bound
    have h1card : ((shrunkCharts Φ₀).card : ℝ) ≤ 16 * (Φ₀.card : ℝ) := by
      have := shrunkCharts_card Φ₀
      rw [mul_comm]
      exact_mod_cast this
    have h3card : MvPolynomial.eval ![((MvPolynomial.eval ![D, r] Bt : ℕ) : ℝ),
        ((r + 1 : ℕ) : ℝ), ((tupleSizeBig k n r : ℕ) : ℝ), -Real.log (ε / 2)] c₀
        = MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] ccount := by
      rw [hccount D r k (-Real.log ε)]
      rw [show ((tupleSizeBig k n r : ℕ) : ℝ)
          = ((k * ((r + 1) ^ (n + 1) * (n + (r + 1) ^ n)) : ℕ) : ℝ) from by
        simp only [tupleSizeBig]]
      rw [show -Real.log (ε / 2) = -Real.log ε + Real.log 2 from by
        rw [Real.log_div (ne_of_gt hε) (by norm_num), neg_sub]
        ring]
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_C, ← h3card]
    linarith [h1card, hΦ₀card]
  · -- the chart conditions (`ChartInW` of the shrunk chart)
    intro cb hcb
    obtain ⟨cb₀, hcb₀, hmem⟩ := Finset.mem_biUnion.mp hcb
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hmem
    obtain ⟨hgc1, hgc2, hcond⟩ := hΦ₀ok cb₀ hcb₀
    have hc0 : (0 : ℝ) ≤ (j : ℝ) / 20 := by positivity
    have hc34 : (j : ℝ) / 20 ≤ 3 / 4 := by
      have hj16 : j < 16 := Finset.mem_range.mp hj
      have hle : (j : ℝ) ≤ 15 := by exact_mod_cast (by omega : j ≤ 15)
      linarith
    have hb1 : MvPolynomial.eval ![D, r] b₁
        = MvPolynomial.eval ![MvPolynomial.eval ![D, r] Bt, r + 1] b₀ := by
      dsimp only [b₁]
      rw [eval_bind₁_fin2_shift]
    have hbstage : MvPolynomial.eval ![D, r] bstage
        = Cfc * (2 * MvPolynomial.eval ![D, r] b₁ + 2) + Cfc := by
      simp only [bstage, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C]
    have hgc1' : graphOf cb₀.1 ∈ S.Ω a₀ (MvPolynomial.eval ![D, r] b₁) (p + 1) := by
      rw [hb1]; exact hgc1
    have hgc2' : graphOf cb₀.2 ∈ S.Ω a₀ (MvPolynomial.eval ![D, r] b₁) (p + 1) := by
      rw [hb1]; exact hgc2
    obtain ⟨hs1, hs2⟩ := hFPCshr D r a₀ b₁ cb₀.1 cb₀.2 ((j : ℝ) / 20) hgc1' hgc2'
    rw [← hbstage] at hs1 hs2
    refine ⟨hs1, hs2, ?_⟩
    intro l
    have h := hcond l (Set.mem_univ l)
    rw [shrunkCoeff]
    simp only [Prod.fst, Prod.snd]
    refine ⟨by linarith [h.1], by nlinarith [h.1, h.2.1, hc0],
      by nlinarith [h.2.1, h.2.2.1, h.1, hc0, hc34], ?_⟩
    -- the image clause of the shrunk chart
    intro t ht
    have hu : (j : ℝ) / 20 + t / 4 ∈ I :=
      ⟨by linarith [hc0, ht.1], by linarith [hc34, ht.2]⟩
    have hsplit : (cb₀.1 l + cb₀.2 l * ((j : ℝ) / 20)) + cb₀.2 l / 4 * t
        = cb₀.1 l + cb₀.2 l * ((j : ℝ) / 20 + t / 4) := by ring
    rw [hsplit]
    exact h.2.2.2.1 ((j : ℝ) / 20 + t / 4) hu
  · -- the cover
    refine shrunkCharts_cover Φ₀ Λ (ε / 2) (fun l _ x hx => ?_)
    obtain ⟨αβ, hαβ, _, t, ht, hlt⟩ := hΦ₀cov l (Set.mem_univ l) x hx
    exact ⟨αβ, hαβ, t, ht, hlt⟩
  · -- `CurveData` for each shrunk pullback
    intro cb hcb
    obtain ⟨cb₀, hcb₀, hmem⟩ := Finset.mem_biUnion.mp hcb
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hmem
    have hc0 : (0 : ℝ) ≤ (j : ℝ) / 20 := by positivity
    have hc34 : (j : ℝ) / 20 ≤ 3 / 4 := by
      have hj16 : j < 16 := Finset.mem_range.mp hj
      have hle : (j : ℝ) ≤ 15 := by exact_mod_cast (by omega : j ≤ 15)
      linarith
    exact Work.WilG4cW.CurveDataPullCW (k := k) (p := p) (n := n) (r := r) hr F γs hcspec Bbad hb
      ((j : ℝ) / 20) hc0 hc34 cb₀.1 cb₀.2 (hH1 cb₀ hcb₀) hP.1

end Work.WilkG4c
