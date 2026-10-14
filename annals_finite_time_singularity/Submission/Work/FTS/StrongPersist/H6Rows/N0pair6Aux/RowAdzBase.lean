import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.dzSelfA2d
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.t5bPiecePtwIntegrable
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.TransportS.Slots
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.Spaces.sq_mul_div_rpow
import Submission.Work.Spaces.uncurry_partial_c1

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.N0pair6Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

noncomputable section

/-- The product measure `(dz dθ)` restricted to the self-similar domain `Iz × Iθ`. -/
noncomputable abbrev pqm : MeasureTheory.Measure (ℝ × ℝ) :=
  (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
    (MeasureTheory.volume.restrict Work.Spaces.Iθ)

/-- The `(i,j)`-slot of the Leibniz expansion of `D_z^bD_θ^a(A·D_z f)` paired against
`D_z^bD_θ^a f` and the leaf weight `ρ`. -/
def rowA_piece (f A ρ : ℝ → ℝ → ℝ) (a b i j : ℕ) (p : ℝ × ℝ) : ℝ :=
  ρ p.1 p.2 * Work.Spaces.mixed j i A p.1 p.2 * Work.Spaces.mixed (b - j + 1) (a - i) f p.1 p.2
    * Work.Spaces.mixed b a f p.1 p.2


/-- `sin(2θ) > 0` on the open interval. -/
theorem rowA_sin_two_pos {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- `sin(2θ)^{-η} ≤ sin(2θ)^{-γ}` on the open interval. -/
theorem rowA_sin_rpow_eta_le_gam {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) ≤
      (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) :=
  Work.FTS.H2.rpow_eta_le_gam hα ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩

/-- The angular weight `sin(2θ)^{-q}` is a.e. strongly measurable for `volume|Iθ`. -/
theorem rowA_sin_rpow_aemeasurable (q : ℝ) :
    AEMeasurable (fun θ : ℝ => Real.sin (2 * θ) ^ (-q))
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hsin2 : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (π / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hpos : ∀ θ ∈ Set.Ioo 0 (π / 2), Real.sin (2 * θ) ≠ 0 :=
    fun θ hθ => ne_of_gt (rowA_sin_two_pos hθ)
  have h1 : AEMeasurable (fun θ : ℝ => Real.sin (2 * θ) ^ (-q))
      (MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2))) :=
    (hsin2.rpow_const (fun θ hθ => Or.inl (hpos θ hθ))).aemeasurable measurableSet_Ioo
  rw [show (MeasureTheory.volume.restrict Work.Spaces.Iθ)
      = MeasureTheory.volume.restrict (Set.Ioo 0 (π / 2)) from
    (Measure.restrict_congr_set (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)
      (a := (0:ℝ)) (b := π / 2))).symm]
  exact h1

/-- **Decomposition of a leaf weight.**  Each leaf weight of the slot `a` factors as `w²·σ` with
an angular factor `σ` that is positive, a.e. measurable, and dominated by the slot exponent. -/
theorem rowA_leaf_decomp {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {a : ℕ} {ρ : ℝ → ℝ → ℝ}
    (hρ : Work.FTS.TransportS.IsLeafW α a ρ) :
    ∃ σ : ℝ → ℝ, (∀ z θ : ℝ, ρ z θ = (Work.Spaces.w z) ^ 2 * σ θ) ∧
      (∀ θ ∈ Set.Ioo 0 (π / 2), 0 < σ θ) ∧
      AEMeasurable σ (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∀ θ ∈ Set.Ioo 0 (π / 2),
        σ θ ≤ (Real.sin (2 * θ)) ^
          (-(if a = 0 then Work.Spaces.eta else Work.Spaces.gam α))) := by
  rcases hρ with h | h | ⟨ha, h⟩
  · subst h
    refine ⟨fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)),
      fun z θ => rfl, ?_, ?_, ?_⟩
    · intro θ hθ; exact Real.rpow_pos_of_pos (rowA_sin_two_pos hθ) _
    · exact rowA_sin_rpow_aemeasurable _
    · intro θ hθ
      by_cases ha0 : a = 0
      · rw [if_pos ha0]
      · rw [if_neg ha0]
        exact rowA_sin_rpow_eta_le_gam hα hθ
  · subst h
    refine ⟨fun _ => 1, fun z θ => by simp only [Work.FTS.TransportS.leafOne, mul_one],
      fun θ hθ => one_pos, ?_, ?_⟩
    · exact aestronglyMeasurable_const.aemeasurable
    · intro θ hθ
      by_cases ha0 : a = 0
      · rw [if_pos ha0]
        simpa using Work.FTS.TransportS.one_le_rpow_neg Work.Spaces.eta_nonneg hθ
      · rw [if_neg ha0]
        have hg : 0 ≤ Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
        simpa using Work.FTS.TransportS.one_le_rpow_neg hg hθ
  · subst h
    have ha0 : a ≠ 0 := by omega
    refine ⟨fun θ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)),
      fun z θ => rfl, ?_, ?_, ?_⟩
    · intro θ hθ; exact Real.rpow_pos_of_pos (rowA_sin_two_pos hθ) _
    · exact rowA_sin_rpow_aemeasurable _
    · intro θ hθ; rw [if_neg ha0]

/-- `x·(|g|·|h|) ≤ (x·(g²+h²))/2` for `x ≥ 0`. -/
theorem rowA_mul_abs_le {x g h : ℝ} (hx : 0 ≤ x) :
    x * (|g| * |h|) ≤ (x * (g ^ 2 + h ^ 2)) / 2 := by
  have h1 : |g| * |h| ≤ (g ^ 2 + h ^ 2) / 2 := Work.Spaces.abs_mul_abs_le_half_add_sq g h
  calc x * (|g| * |h|) ≤ x * ((g ^ 2 + h ^ 2) / 2) := mul_le_mul_of_nonneg_left h1 hx
    _ = (x * (g ^ 2 + h ^ 2)) / 2 := by ring

/-- The slot is continuous on the open quadrant. -/
theorem rowA_piece_continuousOn {f A ρ : ℝ → ℝ → ℝ} {a b i j : ℕ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hAso : Work.FTS.EllipticEst.SmoothOpen A)
    (hρc : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) Work.FTS.EllipticEst.Q0) :
    ContinuousOn (rowA_piece f A ρ a b i j) Work.FTS.EllipticEst.Q0 := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2 * Work.Spaces.mixed j i A p.1 p.2
      * Work.Spaces.mixed (b - j + 1) (a - i) f p.1 p.2
      * Work.Spaces.mixed b a f p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    ((hρc.mul ((hAso.mixed j i).continuousOn)).mul
      ((hso.mixed (b - j + 1) (a - i)).continuousOn)).mul ((hso.mixed b a).continuousOn)
  exact h1.congr (fun p _ => rfl)

/-- **The a.e. Leibniz expansion of the paired integrand.** -/
theorem rowA_piece_expansion {a b : ℕ} {f A : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen f) (hAso : Work.FTS.EllipticEst.SmoothOpen A) :
    (fun p : ℝ × ℝ => ρ p.1 p.2
        * Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) p.1 p.2
        * Work.Spaces.mixed b a f p.1 p.2)
      =ᵐ[pqm]
      (fun p : ℝ × ℝ => ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          ((a.choose i : ℝ) * (b.choose j : ℝ)) * rowA_piece f A ρ a b i j p) := by
  refine Work.FTS.StrongPersist.H6Pair6Aux.ae_prod_Ioo (p := fun z θ =>
    ρ z θ * Work.Spaces.mixed b a (fun z θ => A z θ * Work.Spaces.Dz f z θ) z θ
        * Work.Spaces.mixed b a f z θ
      = ∑ i ∈ Finset.range (a + 1), ∑ j ∈ Finset.range (b + 1),
          ((a.choose i : ℝ) * (b.choose j : ℝ)) * rowA_piece f A ρ a b i j (z, θ))
    (fun θ hθ z hz => ?_)
  rw [Work.FTS.TransportS.mixed_mul_Dz_open b a A f hAso hso z θ hz hθ.1 hθ.2]
  simp only [rowA_piece]
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  ring

/-- **The `ℋ^k`-integrand of a member of `ℋ^k` is product integrable**, and its product integral
is `HkSq`. -/
theorem rowA_HkIntegrand_prodIntegrable {α : ℝ} {k : ℕ} {F : ℝ → ℝ → ℝ}
    (hso : Work.FTS.EllipticEst.SmoothOpen F) (hmem : Work.Spaces.HkMem α k F) :
    MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2) pqm ∧
      ∫ p, Work.Spaces.HkIntegrand α k F p.1 p.2 ∂pqm = Work.Spaces.HkSq α k F := by
  have hnn : ∀ z θ : ℝ, 0 ≤ Work.Spaces.HkIntegrand α k F z θ :=
    fun z θ => Work.Spaces.HkIntegrand_nonneg α k F z θ
  have hAE : AEStronglyMeasurable (Function.uncurry
      (fun z θ => Work.Spaces.HkIntegrand α k F z θ)) pqm :=
    Work.Spaces.aesm_of_continuousOn_Qd _ (hso.continuousOn_HkIntegrand α k)
  have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => Work.Spaces.HkIntegrand α k F z θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    (MeasureTheory.ae_restrict_mem measurableSet_Ici).mono fun z hz => hmem.1 z hz
  exact Work.Spaces.integrable_prod_of_iterated hnn hAE hslice hmem.2

end

end Work.FTS.StrongPersist.H6Rows.N0pair6Aux
