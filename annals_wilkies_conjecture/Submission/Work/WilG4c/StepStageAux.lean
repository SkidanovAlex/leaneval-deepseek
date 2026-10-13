/-
  WilG4c / `StepStageOfAxes` — BNZ §5.4: the production of `StepStage` from the frozen axes.

  This is the last assembly of `Work.WilkG4c.StepHigher`.  From

  * the sliced choice lemma (`CurveFamAlphaListPureSliced`),
  * `F1Affine` (`h1`), `ChoiceHyp` (`hchoice`) and `BddDxHyp` (`hbdd`),

  it produces `StepStage S p n`: for every family `F` satisfying `PYLip` with `Ω`-bounded graphs
  and values in `(0,1)` on `Λ`, a finite family `Φ₁` of affine `x`-charts covering `I` up to
  `ε/2`, whose coordinate graphs are `Ω`-bounded, and each of whose pullbacks carries the
  multi-curve data `CurveData` of the estimate.

  The construction is the one of `StepHigherPlan.md` §15/§16:

  1. the sliced choice lemma, applied to every list `L` of length `≤ r`, gives the curves `γs`;
  2. the tuple of BNZ §5.4 — the clamped curves and the sliced surrogates — is padded to the
     explicit member count `tupleSizeBig k n r` and `F1Affine` is applied to it with `Λ := univ`,
     order `r+1` and parameter `ε/2` (`H1Chart` per chart);
  3. each chart `(α₀,β₀)` is shrunk and shifted sixteen times: `(α₀ + β₀·c₀, β₀/4)` with
     `c₀ ∈ {j/20 : j < 16}` (`Work.WilG4c.shiftCover16`), which absorbs the factor `4` of the
     surrogate and keeps the `ε/2`-cover;
  4. `Work.WilG4c.CurveDataPullC` supplies `CurveData` for each shrunk pullback.
-/
import Mathlib
import Submission.Work.WilG4c.StepHigherStageDefs
import Submission.Work.WilG4c.StepTupleBig
import Submission.Work.WilG4c.StepH1Out
import Submission.Work.WilG4c.StepChoiceOut
import Submission.Work.WilG4c.CurveFamAlphaListPureSliced
import Submission.Work.WilG4c.hBdd_of_member
import Submission.Work.WilG4c.FamGraphPolyComb
import Submission.Work.WilG4c.shiftCover16
import Submission.Work.WilG4c.countPolySubst
import Submission.Work.WilG4c.StepHigherMain

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-! ## 1. Substituting `X 0 ↦ Bt`, `X 1 ↦ X 1 + 1` -/

/-- Substituting `X 0 ↦ Bt` and `X 1 ↦ X 1 + 1` into a `Fin 2`-polynomial turns the evaluation
point `![D,r]` into `![eval ![D,r] Bt, r+1]`. -/
theorem eval_bind₁_fin2_shift (Bt b : MvPolynomial (Fin 2) ℕ) (D r : ℕ) :
    MvPolynomial.eval ![D, r]
        (MvPolynomial.bind₁ (R := ℕ) ![Bt, MvPolynomial.X 1 + MvPolynomial.C 1] b)
      = MvPolynomial.eval ![MvPolynomial.eval ![D, r] Bt, r + 1] b := by
  rw [Work.WilG4a.eval_bind₁_fin2]
  rw [show (fun i : Fin 2 => MvPolynomial.eval ![D, r]
        (![Bt, MvPolynomial.X 1 + MvPolynomial.C 1] i))
      = ![MvPolynomial.eval ![D, r] Bt, r + 1] from by
    funext i
    fin_cases i <;> simp]

/-! ## 2. The shrunk charts -/

/-- The family of shrunk charts of a chart family: `(α,β)` is replaced by the sixteen charts
`(α + β·c₀, β/4)`, `c₀ ∈ {j/20 : j < 16}`. -/
def shrunkCharts {p : ℕ} (Φ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ))) :
    Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ)) :=
  Φ.biUnion (fun cb => (Finset.range 16).image
    (fun j : ℕ => shrunkCoeff cb.1 cb.2 ((j : ℝ) / 20)))

/-- The shrunk chart family has at most `16` times as many charts. -/
theorem shrunkCharts_card {p : ℕ} (Φ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ))) :
    (shrunkCharts Φ).card ≤ Φ.card * 16 := by
  have hinner : ∀ a ∈ Φ, (Finset.image (fun j : ℕ => shrunkCoeff a.1 a.2 ((j : ℝ) / 20))
      (Finset.range 16)).card ≤ 16 := by
    intro a _
    refine le_trans Finset.card_image_le ?_
    simp
  refine le_trans (Finset.card_biUnion_le ..) ?_
  calc (∑ a ∈ Φ, (Finset.image (fun j : ℕ => shrunkCoeff a.1 a.2 ((j : ℝ) / 20))
          (Finset.range 16)).card)
      ≤ ∑ _a ∈ Φ, 16 := Finset.sum_le_sum hinner
    _ = Φ.card * 16 := by rw [Finset.sum_const, smul_eq_mul]

/-- The shrunk chart family still covers `I` up to `ε`. -/
theorem shrunkCharts_cover {p : ℕ} (Φ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ)))
    (Λ : Set (Fin p → ℝ)) (ε : ℝ)
    (hcov : ∀ l ∈ Λ, ∀ x ∈ I, ∃ cb ∈ Φ, ∃ t ∈ I, |cb.1 l + cb.2 l * t - x| < ε) :
    ∀ l ∈ Λ, ∀ x ∈ I, ∃ cb ∈ shrunkCharts Φ, ∃ t ∈ I, |cb.1 l + cb.2 l * t - x| < ε := by
  intro l hl x hx
  obtain ⟨cb, hcb, t, ht, hlt⟩ := hcov l hl x hx
  obtain ⟨c, hc, hct, htc, hc34⟩ := Work.WilG4c.shiftCover16 t ht.1 ht.2
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hc
  refine ⟨shrunkCoeff cb.1 cb.2 ((j : ℝ) / 20), ?_, 4 * (t - (j : ℝ) / 20),
    ⟨by linarith, by linarith⟩, ?_⟩
  · exact Finset.mem_biUnion.mpr ⟨cb, hcb, Finset.mem_image.mpr ⟨j, hj, rfl⟩⟩
  · rw [shrunkCoeff]
    simp only [Prod.snd]
    have : cb.1 l + cb.2 l * ((j : ℝ) / 20) + (cb.2 l / 4) * (4 * (t - (j : ℝ) / 20))
        = cb.1 l + cb.2 l * t := by ring
    rw [this]
    exact hlt

/-- The graph of a shrunk chart coordinate `α + β·c` (resp. `β/4`) is `Ω`-bounded, with format
`2 a₀ + A` and degree `C (2 D₀ + 2) + C` when the graphs of `α` and `β` are `Ω`-bounded with
format `a₀` and degree `D₀`. -/
theorem shrunkChart_graph_mem (S : SOMin) (p : ℕ) :
    ∃ (A C : ℕ), ∀ (D r a₀ : ℕ) (b₀ : MvPolynomial (Fin 2) ℕ)
      (α β : (Fin p → ℝ) → ℝ) (c : ℝ),
      graphOf α ∈ S.Ω a₀ (MvPolynomial.eval ![D, r] b₀) (p + 1) →
      graphOf β ∈ S.Ω a₀ (MvPolynomial.eval ![D, r] b₀) (p + 1) →
      graphOf (shrunkCoeff α β c).1 ∈
        S.Ω (2 * a₀ + A) (C * (2 * MvPolynomial.eval ![D, r] b₀ + 2) + C) (p + 1) ∧
      graphOf (shrunkCoeff α β c).2 ∈
        S.Ω (2 * a₀ + A) (C * (2 * MvPolynomial.eval ![D, r] b₀ + 2) + C) (p + 1) := by
  obtain ⟨A, C, hFPC⟩ := Work.WilG4c.FamGraphPolyComb S p 2
  refine ⟨A, C, ?_⟩
  intro D r a₀ b₀ α β c hα hβ
  set E : ℕ := MvPolynomial.eval ![D, r] b₀ with hE
  have hH : ∀ i : Fin 2, graphOf (![α, β] i) ∈ S.Ω (![a₀, a₀] i) (![E, E] i) (p + 1) := by
    intro i
    fin_cases i
    · simpa using hα
    · simpa [hE] using hβ
  have hsum1 : (∑ i : Fin 2, ![a₀, a₀] i) = 2 * a₀ := by simp [Fin.sum_univ_two]; omega
  have hsum2 : (∑ i : Fin 2, ![E, E] i) = 2 * E := by simp [Fin.sum_univ_two]; omega
  -- the first coordinate `α + β * c`
  have hP1 : (MvPolynomial.X (0 : Fin 2) + MvPolynomial.C c * MvPolynomial.X (1 : Fin 2)
      : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 2 := by
    refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
    have ha : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 2 :=
      le_trans (le_of_eq (MvPolynomial.totalDegree_X (R := ℝ) _)) (by norm_num)
    have hb : (MvPolynomial.C c * MvPolynomial.X (1 : Fin 2)
        : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 2 := by
      refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
      have h1 : (MvPolynomial.C c : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 :=
        le_trans (le_of_eq (MvPolynomial.totalDegree_C c)) (by norm_num)
      have h2 : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 :=
        le_of_eq (MvPolynomial.totalDegree_X (R := ℝ) _)
      exact Nat.add_le_add h1 h2
    exact max_le ha hb
  have hfun1 : (fun x : Fin p → ℝ =>
      MvPolynomial.eval (fun i => ![α, β] i x)
        (MvPolynomial.X (0 : Fin 2) + MvPolynomial.C c * MvPolynomial.X (1 : Fin 2)))
      = (shrunkCoeff α β c).1 := by
    funext x
    simp [shrunkCoeff, MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X,
      MvPolynomial.eval_C]
    ring
  have h1 := hFPC ![a₀, a₀] ![E, E] ![α, β]
    (MvPolynomial.X (0 : Fin 2) + MvPolynomial.C c * MvPolynomial.X (1 : Fin 2)) hH
  rw [hsum1, hsum2, hfun1] at h1
  have h2 : (MvPolynomial.C ((1 : ℝ) / 4) * MvPolynomial.X (1 : Fin 2)
      : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 2 := by
    refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
    have h1' : (MvPolynomial.C ((1 : ℝ) / 4) : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 :=
      le_trans (le_of_eq (MvPolynomial.totalDegree_C _)) (by norm_num)
    have h2' : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) ℝ).totalDegree ≤ 1 :=
      le_of_eq (MvPolynomial.totalDegree_X (R := ℝ) _)
    exact Nat.add_le_add h1' h2'
  have hfun2 : (fun x : Fin p → ℝ =>
      MvPolynomial.eval (fun i => ![α, β] i x)
        (MvPolynomial.C ((1 : ℝ) / 4) * MvPolynomial.X (1 : Fin 2)))
      = (shrunkCoeff α β c).2 := by
    funext x
    simp only [shrunkCoeff, Prod.snd, MvPolynomial.eval_mul, MvPolynomial.eval_X,
      MvPolynomial.eval_C, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
    ring
  have h3 := hFPC ![a₀, a₀] ![E, E] ![α, β]
    (MvPolynomial.C ((1 : ℝ) / 4) * MvPolynomial.X (1 : Fin 2)) hH
  rw [hsum1, hsum2, hfun2] at h3
  refine ⟨Work.WilG1.Omega.mono h1 le_rfl ?_, Work.WilG1.Omega.mono h3 le_rfl ?_⟩
  · exact Nat.add_le_add_right (Nat.mul_le_mul_left C (Nat.add_le_add_left hP1 _)) C
  · exact Nat.add_le_add_right (Nat.mul_le_mul_left C (Nat.add_le_add_left h2 _)) C

end Work.WilkG4c
