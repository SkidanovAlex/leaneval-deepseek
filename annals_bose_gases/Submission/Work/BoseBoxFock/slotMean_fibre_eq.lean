import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.PB3Defs
import Submission.Work.BoseBoxFock.aPCPairAlg
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotMean_fibre_eq` — the slot mean commutes with a fibre (slot-`j`) operator

The corpus's box slot mean `aPC ℓ i` averages a state over the `i`-th slot.  The operation
appearing on the `Q₂`-row, and more generally in every "one-particle operator in the slot `j`
sandwiched between two configurations" computation, is

    `(K)_{j} Ψ x = ∫ u, K u * Ψ (x[j ↦ u])`,

i.e. the second quantisation of the one-body operator with a state-independent kernel `K`,
acting in the slot `j`.  Since `i ≠ j`, the `i`-average and the `j`-fibre integral live in two
*independent* slots of the configuration: the two operations commute.  This is the identity

    `aPC ℓ i ((K)_{j} Ψ) = (K)_{j} (aPC ℓ i Ψ)     (i ≠ j)`,

and the whole content is the interchange of the two fibre integrals, i.e. Fubini for the
two-variable integrand `(y, u) ↦ K u * Ψ (x[j ↦ u][i ↦ y])` over `Λ × Λ`, together with the
pointwise `Function.update_comm` reindexing `x[i ↦ y][j ↦ u] = x[j ↦ u][i ↦ y]`.

Because `aPC` averages over FS's box `Λ(ℓ) = acube ℓ` (a finite-measure set) while the `u`-fibre
integral runs over all of `ℝ³`, the Fubini interchange needs a *support* hypothesis: the kernel
`K` vanishes off `Λ(ℓ)`.  That is exactly the situation for the corpus's pinned modes, whose
representatives `pinQ v μ N k` are supported in the box (`pinQ_eq_zero_of_notMem_acube`, proved
below from `corpusBox`'s localisation function `χ_Λ`).

Everything here is complete; the analytic inputs are the unconditional identity
`MeasureTheory.integral_const_mul`, the Fubini theorem
`MeasureTheory.integral_integral_swap` (applied to a bounded integrand on the finite-measure
product of the two boxes), and the support lemma.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 1. The pinned modes vanish off the box -/

/-- **The pinned mode `pinQ` is supported in FS's box `Λ(ℓ)`.**  Both summands of
`qVec = e^{ikx}χ_Λ − χ̂(kℓ)θ` are supported in the box: the first through the localisation
function `χ_Λ` (`BoxData.chiLam_supp`), the second through `θ = 1_Λ`. -/
theorem pinQ_eq_zero_of_notMem_acube {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {N : ℕ}
    (k : Lab N) {u : EuclideanSpace ℝ (Fin 3)}
    (hu : u ∉ Submission.BoseGases.acube (ellH v μ)) : pinQ v μ N k u = 0 := by
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have hchi : Work.BoseK15.corpusBox.chiLam (ellH v μ) u = 0 := by
    by_contra hh
    have hmem : u ∈ Work.BoseK15.corpusBox.boxL (ellH v μ) :=
      Work.BoseB4.BoxData.chiLam_supp Work.BoseK15.corpusBox hℓ
        (Function.mem_support.mpr hh)
    rw [boxL_eq_acube hℓ] at hmem
    exact hu hmem
  have hth : Work.BoseK15.corpusBox.thetaFun (ellH v μ) u = 0 := by
    apply thetaFun_eq_zero_of_notMem
    rwa [boxL_eq_acube hℓ]
  rw [pinQ, Work.BoseB4.BoxData.qVec_apply, Work.BoseB4.BoxData.modeVec_apply, hchi, hth]
  simp

/-! ## 2. The slot mean commutes with a box-supported fibre operator -/

/-- **The slot mean `aPC ℓ i` commutes with the slot-`j` fibre operator of a box-supported
kernel `K`** (`i ≠ j`):

    `aPC ℓ i (fun y => ∫ u, K u * Ψ (y[j ↦ u])) x
       = ∫ u, K u * (aPC ℓ i Ψ) (x[j ↦ u])`.

The two slots are independent, so the `i`-average (over `Λ(ℓ)`) and the `j`-fibre integral
interchange: this is `MeasureTheory.integral_integral_swap` for the jointly measurable, bounded
integrand `(y, u) ↦ K u * Ψ (x[j ↦ u][i ↦ y])`, after the pointwise reindexing
`x[i ↦ y][j ↦ u] = x[j ↦ u][i ↦ y]` (`Function.update_comm`, `i ≠ j`).  The support hypothesis
`supp K ⊆ Λ(ℓ)` makes both integrals run over the same finite-measure box, which is what makes
the joint integrand integrable (it is bounded on a finite measure space). -/
theorem aPC_fibre_swap {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i j : Fin n) (hij : i ≠ j)
    {K : EuclideanSpace ℝ (Fin 3) → ℂ} (hKm : Measurable K)
    (hKb : ∃ C : ℝ, ∀ u, ‖K u‖ ≤ C)
    (hKsupp : Function.support K ⊆ Submission.BoseGases.acube ℓ)
    {Θ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ} (hΘm : Measurable Θ)
    (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C) (x : Fin n → EuclideanSpace ℝ (Fin 3)) :
    aPC ℓ i (fun y => ∫ u : EuclideanSpace ℝ (Fin 3), K u * Θ (Function.update y j u)) x
      = ∫ u : EuclideanSpace ℝ (Fin 3), K u * (aPC ℓ i Θ) (Function.update x j u) := by
  classical
  obtain ⟨Ck, hCk⟩ := hKb
  obtain ⟨C, hC⟩ := hΘb
  obtain ⟨C', hC'0, hC'⟩ : ∃ C' : ℝ, 0 ≤ C' ∧ ∀ y, ‖Θ y‖ ≤ C' :=
    ⟨max C 0, le_max_right _ _, fun y => le_trans (hC y) (le_max_left _ _)⟩
  set S : Set E3 := Submission.BoseGases.acube ℓ with hSdef
  have hSmeas : MeasurableSet S := by
    rw [hSdef]; exact Submission.BoseGases.acube_measurable ℓ
  have hSfin : (volume : Measure E3) S < ⊤ := by
    rw [hSdef, Submission.BoseGases.acube_volume ℓ hℓ.le]; exact ENNReal.ofReal_lt_top
  haveI : IsFiniteMeasure ((volume : Measure E3).restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hSfin⟩
  have hKzero : ∀ u ∉ S, K u = 0 := by
    intro u hu
    by_contra h
    exact hu (by rw [hSdef]; exact hKsupp (Function.mem_support.mpr h))
  -- the joint integrand is measurable on the product of the two boxes
  have hUpd : Measurable (fun p : E3 × E3 => Function.update (Function.update x j p.2) i p.1) := by
    measurability
  have hFint : Integrable
      (fun p : E3 × E3 => K p.2 * Θ (Function.update (Function.update x j p.2) i p.1))
      (((volume : Measure E3).restrict S).prod ((volume : Measure E3).restrict S)) := by
    refine Integrable.of_bound ((hKm.comp measurable_snd).mul (hΘm.comp hUpd)).aestronglyMeasurable
      (Ck * C') ?_
    filter_upwards with p
    rw [norm_mul]
    exact mul_le_mul (hCk p.2) (hC' _) (norm_nonneg _)
      (le_trans (norm_nonneg _) (hCk p.2))
  have hFub : (∫ y in S, ∫ u in S, K u * Θ (Function.update (Function.update x j u) i y))
      = ∫ u in S, ∫ y in S, K u * Θ (Function.update (Function.update x j u) i y) :=
    MeasureTheory.integral_integral_swap hFint
  -- unfold the slot mean on both sides
  simp only [aPC]
  rw [← hSdef]
  -- the `Λ`-average of the `j`-fibre integral, with the two slots interchanged
  trans ((1 / ℓ ^ 3 : ℝ) : ℂ)
      * ∫ y in S, ∫ u in S, K u * Θ (Function.update (Function.update x j u) i y)
  · congr 1
    refine setIntegral_congr_fun hSmeas (fun y _ => ?_)
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S)
      (f := fun u => K u * Θ (Function.update (Function.update x i y) j u))
      (fun u hu => by rw [hKzero u hu, zero_mul])]
    refine setIntegral_congr_fun hSmeas (fun u _ => ?_)
    rw [Function.update_comm hij y u x]
  -- Fubini
  trans ((1 / ℓ ^ 3 : ℝ) : ℂ)
      * ∫ u in S, ∫ y in S, K u * Θ (Function.update (Function.update x j u) i y)
  · rw [hFub]
  -- pull out the normalisation `ℓ⁻³`
  trans ∫ u in S, ((1 / ℓ ^ 3 : ℝ) : ℂ)
      * ∫ y in S, K u * Θ (Function.update (Function.update x j u) i y)
  · rw [MeasureTheory.integral_const_mul]
  -- pull the `u`-independent factor `K u` out of the `y`-integral
  trans ∫ u in S, K u * (((1 / ℓ ^ 3 : ℝ) : ℂ)
      * ∫ y in S, Θ (Function.update (Function.update x j u) i y))
  · refine setIntegral_congr_fun hSmeas (fun u _ => ?_)
    rw [MeasureTheory.integral_const_mul]; ring
  -- extend the `u`-integral back to all of `ℝ³` (the integrand vanishes off the box)
  · exact setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun u hu => by rw [hKzero u hu, zero_mul])

/-! ## 3. The target -/

theorem slotMean_fibre_eq {n N : ℕ} {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ}
    (i j : Fin n) (hij : i ≠ j) (k : Work.BoseBoxFock.Lab N)
    {Θ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ}
    (hΘm : Measurable Θ) (hΘb : ∃ C : ℝ, ∀ x, ‖Θ x‖ ≤ C)
    (x : Fin n → EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.aPC (Work.BoseBoxFock.ellH v μ) i
        (fun y => ∫ u : EuclideanSpace ℝ (Fin 3),
          (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u) * Θ (Function.update y j u)) x
      = ∫ u : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (Work.BoseBoxFock.pinQ v μ N k u)
          * (Work.BoseBoxFock.aPC (Work.BoseBoxFock.ellH v μ) i Θ)
              (Function.update x j u) := by
  have hKsupp : Function.support (fun u : E3 => (starRingEnd ℂ) (pinQ v μ N k u)) ⊆
      Submission.BoseGases.acube (ellH v μ) := by
    intro u hu
    by_contra h
    have h0 : pinQ v μ N k u = 0 := pinQ_eq_zero_of_notMem_acube k h
    have h1 : (starRingEnd ℂ) (pinQ v μ N k u) = 0 := by rw [h0, map_zero]
    exact hu h1
  have hKm : Measurable (fun u : E3 => (starRingEnd ℂ) (pinQ v μ N k u)) :=
    Complex.continuous_conj.measurable.comp (pinQ_measurable v μ N k)
  have hKb : ∃ C : ℝ, ∀ u : E3, ‖(starRingEnd ℂ) (pinQ v μ N k u)‖ ≤ C := by
    obtain ⟨Ck, -, hbound⟩ := pinQ_bdd v μ N k
    exact ⟨Ck, fun u => by rw [Complex.norm_conj]; exact hbound u⟩
  exact aPC_fibre_swap (ellH_pos v μ) i j hij hKm hKb hKsupp hΘm hΘb x

end Work.BoseBoxFock
