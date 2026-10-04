import Mathlib
import Submission.Work.Diff.STE.Lead.Gal.GardDef
import Submission.Work.Diff.STE.B3.BPairDefs
import Submission.Work.Diff.STE.Lead.MatJetDefs
import Submission.Work.Diff.STE.Lead.matA_jets
import Submission.Work.Diff.STE.B3.R_contDiff_of_chartData
import Submission.Work.Diff.STE.flat.compact_iteratedFDeriv_bound
import Submission.Work.Diff.STE.flat.jetP_iteratedFDeriv_bound
import Submission.Work.Diff.STE.B3.CSq_period_le_integral_deriv
import Submission.Work.Diff.STE.exists_bound_pdRList
import Submission.Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The static jet bound of the localised components (`GardJet`)

`Work.Diff.STE.Lead.Gal.GardJet D k K` asks for a constant `CJ` with

`‖∂^m (D.Rper j h a b) z‖ ≤ CJ * (1 + K)^(k+1)`

for every section `h` whose chart-matrix jets of order `≤ k+1` are bounded by `K` on the `2σ`-balls,
every chart `j`, every pair of frame indices `a b`, every `m ≤ k+1`, every multi-index of directions
and every point `z` of the flat space.

This file proves `GardJet D k K` for every `K > 0`, in a self-contained way.  The mathematical
content is threefold, all *soft* (the constant `CJ` may be anything depending only on the Layer B3
data `D` and on `k`):

* **The support of `D.R j h a b` lies in the `σ j`-ball.**  Indeed `D.R = ψ_j · √dens_j · mat_j`,
  so `D.R j h a b z ≠ 0` forces `ψ_j z ≠ 0`, and on the support of `ψ_j` the chart is genuine and
  `‖z‖ < σ j` (`Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero`, used in `support_R_subset_ball`).
  In particular the jet hypothesis on the `2σ j`-ball *covers the whole support* of the component.
* **The jets of a product** (`pdVec_mul_le`).  `D.R j h a b = matA D j · D.mat j h a b` is the
  product of the *fixed* smooth weight `matA D j = ψ_j √dens_j` (`exists_weight_jets` gives the
  uniform jet bound `W` for it) and the chart matrix.  The chart matrix is only smooth on a
  neighbourhood of the `σ j`-ball, so it is replaced by a globally smooth function agreeing with it
  near the ball: `exists_bumpMat` multiplies it by a bump supported in the open `2σ j`-ball, where
  the chart is genuine (`D.htarget`).  The Leibniz rule for iterated derivatives is then applied to
  the two globally smooth factors; it is obtained from Mathlib's `norm_iteratedFDeriv_mul_le` and the
  two dictionary lemmas `Comp.pdVec_eq_iteratedFDeriv` and
  `flat.norm_iteratedFDeriv_le_sum_pdVec`.
* **The periodisation** (`per_jets_le`).  `D.Rper j h a b` is the periodisation of the complexified
  component; the periodisation is transported by an integer lattice vector (`periodic1_add_iVec`,
  which is `Work.Diff.STE.eb_periodic1_add_intVec` read off the real and imaginary parts) into the
  half-open cube `[0,1)^n`, where it is the finite sum of the `2^n` translates with directions in
  `{-1,0}^n` (`Work.Diff.STE.csqp_periodization_eq_sum_boxIdx`); every summand is either `0` or
  evaluated where the ball bound applies.

The two auxiliary statements were also handed out as sibling tasks
(`Work.Diff.STE.Lead.Gal.per_pdVec_bound` and `...pdVec_mul_bound`, with a slightly different
constant in the second); the proofs below are self-contained and do not depend on them.
-/

namespace Work.Diff.STE.Lead.Gal

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## 1. Smoothness of the chart matrix on the chart target -/

/-- **The chart matrix of a section with smooth chart data is smooth on the chart target.**  This is
the hypothesis `ContDiffOn ℝ ⊤ (D.matChart i h a b) (extChartAt I (D.x₀ i)).target` of
`Work.Diff.STE.B3Data.R_contDiff`, derived from `Work.Diff.STE.D.ChartData h` (the smoothness of the
matrix of `h` in the *coordinate* frame) and the global smoothness of the frame fields `D.e i a`. -/
lemma matChart_contDiffOn_chartData
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (D.matChart i h a b) (extChartAt I (D.x₀ i)).target := by
  have hsec : ∀ x : M, ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) (⊤ : ℕ∞)
      (fun x : M => Bundle.TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x (h x)) x :=
    fun x => Work.Diff.STE.B3.section_contMDiffAt_of_chartData (I := I) (M := M) hh x
  have hmat : ContMDiffOn I 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
      (fun x : M => h x (D.e i a x) (D.e i b x)) Set.univ := by
    intro x _
    have hψ := (hsec x).contMDiffWithinAt (s := Set.univ)
    have hv : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (⊤ : ℕ∞) (T% (D.e i a)) Set.univ x :=
      (D.hesm i a).contMDiffAt.contMDiffWithinAt
    have hw : ContMDiffWithinAt I (I.prod 𝓘(ℝ, E)) (⊤ : ℕ∞) (T% (D.e i b)) Set.univ x :=
      (D.hesm i b).contMDiffAt.contMDiffWithinAt
    have hres := hψ.clm_bundle_apply₂ (F₁ := E) (F₂ := E) hv hw
    simp only [contMDiffWithinAt_totalSpace] at hres
    exact hres.2
  have hcomp : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) (⊤ : ℕ∞)
      (fun y : E => h ((extChartAt I (D.x₀ i)).symm y)
        (D.e i a ((extChartAt I (D.x₀ i)).symm y))
        (D.e i b ((extChartAt I (D.x₀ i)).symm y))) (extChartAt I (D.x₀ i)).target :=
    hmat.comp (contMDiffOn_extChartAt_symm (I := I) (x := D.x₀ i) (n := (⊤ : ℕ∞)))
      (fun y _ => Set.mem_univ _)
  have h' := hcomp.contDiffOn
  change ContDiffOn ℝ (⊤ : ℕ∞) (fun y => h ((extChartAt I (D.x₀ i)).symm y)
    (D.e i a ((extChartAt I (D.x₀ i)).symm y))
    (D.e i b ((extChartAt I (D.x₀ i)).symm y))) (extChartAt I (D.x₀ i)).target
  exact h'

/-- **The chart matrix is smooth at every point whose flat coordinate lies in the chart target.** -/
lemma mat_contDiffAt_of_target
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target) :
    ContDiffAt ℝ (⊤ : ℕ∞) (D.mat i h a b) z := by
  have hsm := matChart_contDiffOn_chartData (I := I) (M := M) D h hh i a b
  have h1 : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun z : Fin (Module.finrank ℝ E) → ℝ => D.matChart i h a b
        (flatToE (I := I) (D.x₀ i) z)) z :=
    (hsm.contDiffAt ((isOpen_extChartAt_target (I := I) (D.x₀ i)).mem_nhds hz)).comp z
      ((Work.Diff.STE.contDiff_flatToE (I := I) (x₀ := D.x₀ i)).contDiffAt)
  simpa only [Work.Diff.STE.B3Data.mat_eq] using h1

/-! ## 2. A globally smooth function agreeing with the chart matrix near the `σ`-ball

The chart matrix `D.mat i h a b` is smooth on the preimage of the chart target, which contains the
closed `2σ i`-ball, but is in general not smooth outside it.  Multiplying by a bump function `ρ`
with `ρ = 1` near the closed `σ`-ball and support inside the open `2σ i`-ball produces a globally
`C^∞` function agreeing with the chart matrix near the `σ`-ball, to which the global Leibniz rule for
iterated partial derivatives applies. -/

/-- **A globally smooth extension of the chart matrix near the `σ i`-ball.** -/
lemma exists_bumpMat
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    ∃ Mhat : (Fin (Module.finrank ℝ E) → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) Mhat ∧
      ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ D.σ i →
        Mhat =ᶠ[nhds z] D.mat i h a b := by
  classical
  have hσ := D.hσ i
  let ρ : ContDiffBump (0 : Fin (Module.finrank ℝ E) → ℝ) :=
    ⟨(3 / 2) * D.σ i, 2 * D.σ i, by linarith, by linarith⟩
  have hρrIn : ρ.rIn = (3 / 2) * D.σ i := rfl
  have hρrOut : ρ.rOut = 2 * D.σ i := rfl
  refine ⟨fun z => ρ z * D.mat i h a b z, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport (⇑ρ)
    · have hzle : ‖z‖ ≤ 2 * D.σ i := by
        have h' : z ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ i) := by
          rw [← hρrOut, ← ρ.tsupport_eq]; exact hz
        rwa [Metric.mem_closedBall, dist_zero_right] at h'
      have hzt := D.htarget i z hzle
      exact ((ρ.contDiff (n := ⊤)).contDiffAt).mul
        (mat_contDiffAt_of_target (I := I) (M := M) D h hh i a b hzt)
    · have hnear : ∀ᶠ y in nhds z, y ∉ tsupport (⇑ρ) :=
        (isClosed_tsupport (⇑ρ)).isOpen_compl.mem_nhds hz
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hnear] with y hy
      rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
  · intro z hz
    have hball : ∀ᶠ y in nhds z,
        y ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) ((3 / 2) * D.σ i) := by
      refine Filter.eventually_iff_exists_mem.mpr
        ⟨Metric.ball z (D.σ i / 2), Metric.ball_mem_nhds z (by linarith), fun y hy => ?_⟩
      rw [Metric.mem_ball, dist_eq_norm] at hy
      rw [Metric.mem_closedBall, dist_zero_right]
      refine le_of_lt ?_
      calc ‖y‖ = ‖(y - z) + z‖ := by ring_nf
        _ ≤ ‖y - z‖ + ‖z‖ := norm_add_le _ _
        _ < D.σ i / 2 + D.σ i := by linarith
        _ = (3 / 2) * D.σ i := by ring
    filter_upwards [hball] with y hy
    have hy' : y ∈ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) ρ.rIn := by
      rwa [hρrIn]
    rw [ρ.one_of_mem_closedBall hy', one_mul]

/-! ## 3. Jet bounds for the weight `matA D i` -/

/-- **Uniform jet bound for the localised weights.**  There is `W ≥ 0` with
`‖∂^m_l (matA D i) z‖ ≤ W` for every chart `i`, every `m ≤ N`, every multi-index `l` and every `z`
in the closed `σ i`-ball (complexified, so that the bound applies to the complex-valued components).
This is the compactness bound `Work.Diff.STE.flat.compact_iteratedFDeriv_bound` for the globally
smooth weight (`Work.Diff.STE.Lead.matA_contDiff`), converted to the partial-derivative vectors by
`Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv`. -/
lemma exists_weight_jets (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (N : ℕ) :
    ∃ W : ℝ, 0 ≤ W ∧
      ∀ (i : ι₀) (j : ℕ), j ≤ N →
        ∀ (l : Fin j → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
          ‖z‖ ≤ D.σ i →
          ‖Work.Diff.STE.pdVec j l
            (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((Work.Diff.STE.Lead.matA (I := I) (M := M) D i y : ℝ) : ℂ)) z‖ ≤ W := by
  classical
  have hper : ∀ i : ι₀, ∃ Wi : ℝ, 0 ≤ Wi ∧
      ∀ (j : ℕ), j ≤ N →
        ∀ (l : Fin j → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
          ‖z‖ ≤ D.σ i →
          ‖Work.Diff.STE.pdVec j l
            (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((Work.Diff.STE.Lead.matA (I := I) (M := M) D i y : ℝ) : ℂ)) z‖ ≤ Wi := by
    intro i
    set F : (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
      fun y => ((Work.Diff.STE.Lead.matA (I := I) (M := M) D i y : ℝ) : ℂ) with hF
    have hFsm : ContDiff ℝ (⊤ : ℕ∞) F :=
      Complex.ofRealCLM.contDiff.comp (Work.Diff.STE.Lead.matA_contDiff (I := I) (M := M) D i)
    obtain ⟨Wi, hWi0, hWi⟩ := Work.Diff.STE.flat.compact_iteratedFDeriv_bound F isOpen_univ
      hFsm.contDiffOn (isCompact_closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i))
      (subset_univ _) N
    refine ⟨Wi, hWi0, fun j hj l z hz => ?_⟩
    rw [Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv j F hFsm z l]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    have hprod : ∏ t : Fin j,
        ‖(Pi.single (l t) (1 : ℝ) : Fin (Module.finrank ℝ E) → ℝ)‖ = 1 := by
      simp [Pi.norm_single]
    rw [hprod, mul_one]
    exact hWi z (by rwa [Metric.mem_closedBall, dist_zero_right]) j hj
  choose Wf hWf0 hWf using hper
  refine ⟨∑ i : ι₀, Wf i, Finset.sum_nonneg (fun i _ => hWf0 i), ?_⟩
  intro i j hj l z hz
  exact (hWf i j hj l z hz).trans
    (Finset.single_le_sum (fun i _ => hWf0 i) (Finset.mem_univ i))

/-! ## 3b. The two elementary jet estimates

* `pdVec_mul_le`: the Leibniz bound for the iterated partial derivatives of a product, at a single
  point, from the jet bounds of the two factors at that point.  It is obtained from Mathlib's
  `norm_iteratedFDeriv_mul_le` together with the two dictionary lemmas
  `Comp.pdVec_eq_iteratedFDeriv` (`pdVec` is the iterated derivative evaluated on the basis tuple)
  and `flat.norm_iteratedFDeriv_le_sum_pdVec` (`‖D^m f‖ ≤ Σ_l ‖∂^l f‖`).
* `per_jets_le`: the jets of the periodisation of a compactly supported smooth function are bounded
  by the jets of the summand on the support; the periodisation is reduced to a lattice translate
  (`periodic1_add_iVec`) lying in the half-open cube `[0,1)^n`, where it is the finite sum of the
  `2^n` translates of the summand with directions in `{-1,0}^n`
  (`csqp_periodization_eq_sum_boxIdx`). -/

/-- **Product bound for the iterated partial derivatives at a point.** -/
lemma pdVec_mul_le {n N : ℕ} {z : Fin n → ℝ} {F G : (Fin n → ℝ) → ℂ} {A B : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hFz : ∀ (j : ℕ), j ≤ N → ∀ γ : Fin j → Fin n, ‖Work.Diff.STE.pdVec j γ F z‖ ≤ A)
    (hGz : ∀ (j : ℕ), j ≤ N → ∀ γ : Fin j → Fin n, ‖Work.Diff.STE.pdVec j γ G z‖ ≤ B) :
    ∀ (j : ℕ), j ≤ N → ∀ γ : Fin j → Fin n,
      ‖Work.Diff.STE.pdVec j γ (fun y => F y * G y) z‖
        ≤ ((2 : ℝ) ^ N * ((n : ℝ) + 1) ^ N * ((N : ℝ) + 1)) * (A * B) := by
  intro j hj γ
  have hFG : ContDiff ℝ (⊤ : ℕ∞) (fun y => F y * G y) := hF.mul hG
  -- the partial derivative vector is the iterated derivative evaluated on the basis tuple
  have h1 : ‖Work.Diff.STE.pdVec j γ (fun y => F y * G y) z‖
      ≤ ‖iteratedFDeriv ℝ j (fun y => F y * G y) z‖ := by
    rw [Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv j _ hFG z γ]
    refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
    have hprod : ∏ t : Fin j, ‖(Pi.single (γ t) (1 : ℝ) : Fin n → ℝ)‖ = 1 := by
      simp [Pi.norm_single]
    rw [hprod, mul_one]
  -- jet bounds of the factors in terms of the operator norms of their iterated derivatives
  have key : ∀ {H : (Fin n → ℝ) → ℂ} {C : ℝ}, ContDiff ℝ (⊤ : ℕ∞) H → 0 ≤ C →
      (∀ (j' : ℕ), j' ≤ N → ∀ γ' : Fin j' → Fin n,
        ‖Work.Diff.STE.pdVec j' γ' H z‖ ≤ C) →
      ∀ i : ℕ, i ≤ j → ‖iteratedFDeriv ℝ i H z‖ ≤ ((n : ℝ) + 1) ^ i * C := by
    intro H C hH hC0 hHz i hi
    refine (Work.Diff.STE.flat.norm_iteratedFDeriv_le_sum_pdVec i H hH z).trans ?_
    calc ∑ l : Fin i → Fin n, ‖Work.Diff.STE.pdVec i l H z‖
        ≤ ∑ _l : Fin i → Fin n, C := Finset.sum_le_sum (fun l _ => hHz i (hi.trans hj) l)
      _ = (n : ℝ) ^ i * C := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fun]
          simp [Nat.cast_pow]
      _ ≤ ((n : ℝ) + 1) ^ i * C :=
          mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) i) hC0
  -- the Leibniz bound for the product
  have h2 : ‖iteratedFDeriv ℝ j (fun y => F y * G y) z‖
      ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i F z‖
          * ‖iteratedFDeriv ℝ (j - i) G z‖ :=
    norm_iteratedFDeriv_mul_le hF hG z (WithTop.coe_le_coe.mpr le_top)
  -- termwise replacement of the jet norms by the assumed bounds
  have h3 : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i F z‖
        * ‖iteratedFDeriv ℝ (j - i) G z‖
      ≤ ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (((n : ℝ) + 1) ^ i * A)
          * (((n : ℝ) + 1) ^ (j - i) * B) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i ≤ j := Finset.mem_range_succ_iff.mp hi
    have h2' := key hF hA hFz i hi'
    have h3' := key hG hB hGz (j - i) (Nat.sub_le j i)
    have h2'' : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ i * A := by positivity
    have hc : (0 : ℝ) ≤ (j.choose i : ℝ) := Nat.cast_nonneg _
    exact mul_le_mul (mul_le_mul_of_nonneg_left h2' hc) h3' (norm_nonneg _) (mul_nonneg hc h2'')
  -- the term is a constant multiple of `(n+1)^j (A B)`
  have h4 : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * (((n : ℝ) + 1) ^ i * A)
        * (((n : ℝ) + 1) ^ (j - i) * B)
      = ∑ i ∈ Finset.range (j + 1),
          (j.choose i : ℝ) * (((n : ℝ) + 1) ^ j * (A * B)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ j := Finset.mem_range_succ_iff.mp hi
    have hpow : ((n : ℝ) + 1) ^ i * ((n : ℝ) + 1) ^ (j - i) = ((n : ℝ) + 1) ^ j := by
      rw [← pow_add, Nat.add_sub_of_le hi']
    rw [← hpow]
    ring
  have h5 : ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * (((n : ℝ) + 1) ^ j * (A * B))
      = (2 : ℝ) ^ j * (((n : ℝ) + 1) ^ j * (A * B)) := by
    rw [← Finset.sum_mul]
    congr 1
    rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
    norm_num
  -- final comparison of the constants
  have h6 : (2 : ℝ) ^ j * (((n : ℝ) + 1) ^ j * (A * B))
      ≤ ((2 : ℝ) ^ N * ((n : ℝ) + 1) ^ N * ((N : ℝ) + 1)) * (A * B) := by
    have hAB : 0 ≤ A * B := mul_nonneg hA hB
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n; linarith
    have hnj : ((n : ℝ) + 1) ^ j ≤ ((n : ℝ) + 1) ^ N := pow_le_pow_right₀ hn1 hj
    have h2j : (2 : ℝ) ^ j ≤ (2 : ℝ) ^ N := pow_le_pow_right₀ (by norm_num) hj
    have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) N; linarith
    have h7 : (2 : ℝ) ^ j * (((n : ℝ) + 1) ^ j * (A * B))
        ≤ (2 : ℝ) ^ N * (((n : ℝ) + 1) ^ N * (A * B)) :=
      mul_le_mul h2j (mul_le_mul_of_nonneg_right hnj hAB) (by positivity) (by positivity)
    have h8 : (2 : ℝ) ^ N * (((n : ℝ) + 1) ^ N * (A * B))
        ≤ (2 : ℝ) ^ N * (((n : ℝ) + 1) ^ N * (A * B)) * ((N : ℝ) + 1) :=
      le_mul_of_one_le_right (by positivity) hN1
    calc (2 : ℝ) ^ j * (((n : ℝ) + 1) ^ j * (A * B))
        ≤ (2 : ℝ) ^ N * (((n : ℝ) + 1) ^ N * (A * B)) := h7
      _ ≤ (2 : ℝ) ^ N * (((n : ℝ) + 1) ^ N * (A * B)) * ((N : ℝ) + 1) := h8
      _ = ((2 : ℝ) ^ N * ((n : ℝ) + 1) ^ N * ((N : ℝ) + 1)) * (A * B) := by ring
  exact h1.trans (h2.trans (h3.trans ((h4.trans h5).le.trans h6)))

/-- The zero function has vanishing iterated partial derivatives. -/
lemma pdVec_zero_fun {n : ℕ} (j : ℕ) (γ : Fin j → Fin n) :
    Work.Diff.STE.pdVec j γ (fun _ : Fin n → ℝ => (0 : ℂ))
      = fun _ : Fin n → ℝ => (0 : ℂ) := by
  induction j with
  | zero => simp [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]
  | succ j ih =>
      have hstep : Work.Diff.STE.pdVec (j + 1) γ (fun _ : Fin n → ℝ => (0 : ℂ))
          = Work.Diff.STE.pd (γ 0)
              (Work.Diff.STE.pdVec j (Fin.tail γ) (fun _ : Fin n → ℝ => (0 : ℂ))) := by
        have h : List.ofFn γ = γ 0 :: List.ofFn (Fin.tail γ) := by
          conv_lhs => rw [← Fin.cons_self_tail γ]
          rw [List.ofFn_cons]
        simp only [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]
        rw [h, List.foldr_cons]
      rw [hstep, ih]
      funext x
      simp [Work.Diff.STE.pd, fderiv_const]

/-- **Jets of a function vanishing near a point vanish.** -/
lemma pdVec_eq_zero_of_notMem_tsupport {n : ℕ} {f : (Fin n → ℝ) → ℂ} {y : Fin n → ℝ}
    (hy : y ∉ tsupport f) (j : ℕ) (γ : Fin j → Fin n) :
    Work.Diff.STE.pdVec j γ f y = 0 := by
  have hev : f =ᶠ[nhds y] (fun _ : Fin n → ℝ => (0 : ℂ)) := by
    have hc : (tsupport f)ᶜ ∈ nhds y := (isClosed_tsupport f).isOpen_compl.mem_nhds hy
    filter_upwards [hc] with y' hy'
    exact image_eq_zero_of_notMem_tsupport hy'
  rw [Work.Diff.STE.csqp_pdVec_congr (l := γ) hev, pdVec_zero_fun j γ]

/-- **Shifting by an integer vector does not change a `1`-periodic complex-valued function.** -/
lemma periodic1_add_iVec {n : ℕ} {f : (Fin n → ℝ) → ℂ} (hper : Periodic1 f)
    (m : Fin n → ℤ) (x : Fin n → ℝ) : f (x + Work.Diff.STE.iVec m) = f x := by
  have hv : ∀ i : Fin n, ∃ k : ℤ, (Work.Diff.STE.iVec m) i = (k : ℝ) := fun i => ⟨m i, rfl⟩
  have hre : Periodic1 (fun y : Fin n → ℝ => (f y).re) := fun i y => congrArg Complex.re (hper i y)
  have him : Periodic1 (fun y : Fin n → ℝ => (f y).im) := fun i y => congrArg Complex.im (hper i y)
  have h1 := Work.Diff.STE.eb_periodic1_add_intVec (f := fun y : Fin n → ℝ => (f y).re)
    hre (Work.Diff.STE.iVec m) hv x
  have h2 := Work.Diff.STE.eb_periodic1_add_intVec (f := fun y : Fin n → ℝ => (f y).im)
    him (Work.Diff.STE.iVec m) hv x
  exact Complex.ext (by simpa using h1) (by simpa using h2)

/-- **Jets of the periodisation.**  For a smooth `f` supported in the `σ`-ball with jets of order
`≤ N` bounded by `B` on the closed `σ`-ball, all jets of order `≤ N` of the periodisation of `f`
are bounded by `2^n * B` everywhere. -/
lemma per_jets_le {n N : ℕ} {σ B : ℝ} (hσ0 : 0 ≤ σ) (hσ : σ ≤ 1 / 8) (hB0 : 0 ≤ B)
    {f : (Fin n → ℝ) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hsupp : Function.support f ⊆ Metric.ball (0 : Fin n → ℝ) σ)
    (hB : ∀ (j : ℕ), j ≤ N → ∀ (γ : Fin j → Fin n) (w : Fin n → ℝ), ‖w‖ ≤ σ →
      ‖Work.Diff.STE.pdVec j γ f w‖ ≤ B) :
    ∀ (j : ℕ), j ≤ N → ∀ (γ : Fin j → Fin n) (z : Fin n → ℝ),
      ‖Work.Diff.STE.pdVec j γ
        (fun z : Fin n → ℝ => ∑' m : Fin n → ℤ, f (z + Work.Diff.STE.iVec m)) z‖
      ≤ (2 : ℝ) ^ n * B := by
  intro j hj γ z
  set P : (Fin n → ℝ) → ℂ := fun z => ∑' m : Fin n → ℤ, f (z + Work.Diff.STE.iVec m) with hP
  have hPper : Periodic1 P := Work.Diff.STE.periodization_periodic f
  -- the half-open cube is contained in the open cube, where `f` lives
  have hsupp' : Function.support f ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) := by
    intro y hy
    rw [Set.mem_pi]
    intro i _
    have h1 : ‖y‖ < σ := by
      have := hsupp hy
      rwa [Metric.mem_ball, dist_zero_right] at this
    have h2 : |y i| ≤ ‖y‖ := norm_le_pi_norm y i
    rw [Set.mem_Ioo]
    constructor <;> linarith [abs_lt.mp (lt_of_le_of_lt h2 h1)]
  -- shift to the half-open cube
  set z' : Fin n → ℝ := fun i => Int.fract (z i) with hz'def
  set m : Fin n → ℤ := fun i => ⌊z i⌋ with hmdef
  have hz' : ∀ i, 0 ≤ z' i ∧ z' i < 1 :=
    fun i => ⟨Int.fract_nonneg (z i), Int.fract_lt_one (z i)⟩
  have hzm : z' + Work.Diff.STE.iVec m = z := by
    funext i
    simp only [hz'def, hmdef, Pi.add_apply, Work.Diff.STE.iVec_apply]
    exact Int.fract_add_floor (z i)
  have hshift : Work.Diff.STE.pdVec j γ P z = Work.Diff.STE.pdVec j γ P z' := by
    rw [← hzm, ← Work.Diff.STE.csqp_pdVec_comp_add_right γ P (Work.Diff.STE.iVec m) z']
    congr 1
    funext y
    exact periodic1_add_iVec hPper m y
  rw [hshift]
  -- on a neighbourhood of `z'` the periodisation is the finite sum over `{-1,0}^n`
  have hbox : P =ᶠ[nhds z']
      (fun y : Fin n → ℝ => ∑ k ∈ Work.Diff.STE.csqp_boxIdx (Fin n),
        f (y + Work.Diff.STE.iVec k)) := by
    refine Filter.eventually_iff_exists_mem.mpr
      ⟨Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 4 : ℝ)) (5 / 4)), ?_, ?_⟩
    · refine (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo).mem_nhds ?_
      rw [Set.mem_pi]
      intro i _
      exact ⟨by linarith [(hz' i).1], by linarith [(hz' i).2]⟩
    · intro y hy
      exact Work.Diff.STE.csqp_periodization_eq_sum_boxIdx hsupp'
        (fun i => Set.mem_pi.mp hy i (Set.mem_univ i))
  have hsum : Work.Diff.STE.pdVec j γ (fun y : Fin n → ℝ => ∑ k ∈ Work.Diff.STE.csqp_boxIdx (Fin n),
        f (y + Work.Diff.STE.iVec k)) z'
      = ∑ k ∈ Work.Diff.STE.csqp_boxIdx (Fin n), Work.Diff.STE.pdVec j γ f (z' + Work.Diff.STE.iVec k) := by
    rw [Work.Diff.STE.csqp_pdVec_finset_sum]
    · exact Finset.sum_congr rfl
        (fun k _ => Work.Diff.STE.csqp_pdVec_comp_add_right γ f (Work.Diff.STE.iVec k) z')
    · intro k _
      exact hf.comp (contDiff_id.add contDiff_const)
  -- the topological support of `f` lies in the closed `σ`-ball
  have hts : tsupport f ⊆ Metric.closedBall (0 : Fin n → ℝ) σ :=
    closure_minimal (fun y hy => Metric.ball_subset_closedBall (hsupp hy)) isClosed_closedBall
  have hterm : ∀ k ∈ Work.Diff.STE.csqp_boxIdx (Fin n),
      ‖Work.Diff.STE.pdVec j γ f (z' + Work.Diff.STE.iVec k)‖ ≤ B := by
    intro k _
    by_cases hk : ‖z' + Work.Diff.STE.iVec k‖ ≤ σ
    · exact hB j hj γ _ hk
    · have hy' : z' + Work.Diff.STE.iVec k ∉ tsupport f := fun hc => hk (by
        have hmem := hts hc
        rwa [Metric.mem_closedBall, dist_zero_right] at hmem)
      rw [pdVec_eq_zero_of_notMem_tsupport hy' j γ]
      simpa using hB0
  calc ‖Work.Diff.STE.pdVec j γ P z'‖
      = ‖∑ k ∈ Work.Diff.STE.csqp_boxIdx (Fin n), Work.Diff.STE.pdVec j γ f (z' + Work.Diff.STE.iVec k)‖ := by
        rw [Work.Diff.STE.csqp_pdVec_congr (l := γ) hbox, hsum]
    _ ≤ ∑ k ∈ Work.Diff.STE.csqp_boxIdx (Fin n),
          ‖Work.Diff.STE.pdVec j γ f (z' + Work.Diff.STE.iVec k)‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Work.Diff.STE.csqp_boxIdx (Fin n), B := Finset.sum_le_sum hterm
    _ = (2 : ℝ) ^ n * B := by
        rw [Finset.sum_const, Work.Diff.STE.csqp_card_boxIdx, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-! ## 4. The support of the localised component -/

/-- **The support of the localised component lies in the open `σ i`-ball.** -/
lemma support_R_subset_ball
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀) (a b : Fin (Module.finrank ℝ E)) :
    Function.support (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      ((D.R i h a b z : ℝ) : ℂ)) ⊆ Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ i) := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right]
  have hR : D.R i h a b z ≠ 0 := by
    intro h0
    exact hz (by simp [h0])
  have hA : Work.Diff.STE.Lead.matA (I := I) (M := M) D i z ≠ 0 := by
    intro h0
    exact hR (by rw [Work.Diff.STE.Lead.R_eq_matA_mul_mat, h0, zero_mul])
  have hψ : D.psi i z ≠ 0 := by
    intro h0
    exact hA (by rw [Work.Diff.STE.Lead.matA, h0, zero_mul])
  exact Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero (I := I) (M := M) D hψ

/-! ## 5. The jet bound of the localised component on the `σ`-ball -/

/-- **The jets of the localised component on the `σ i`-ball.**  Here `K` bounds the jets of the
chart matrices on the `2σ`-balls (the hypothesis `hjet` of `GardJet`) and `W` the jets of the
weights `matA D i` on the `σ`-balls (`exists_weight_jets`).  The chart matrix is replaced, near the
ball, by the globally smooth bump multiple `exists_bumpMat`, to which the product bound
`pdVec_mul_le` applies. -/
lemma jets_component_le
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hh : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (N : ℕ) (W K : ℝ)
    (hW0 : 0 ≤ W) (hK0 : 0 ≤ K)
    (hW : ∀ (i : ι₀) (j : ℕ), j ≤ N →
      ∀ (l : Fin j → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
        ‖z‖ ≤ D.σ i →
        ‖Work.Diff.STE.pdVec j l
          (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((Work.Diff.STE.Lead.matA (I := I) (M := M) D i y : ℝ) : ℂ)) z‖ ≤ W)
    (hjet : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (j : ℕ), j ≤ N →
      ∀ (l : Fin j → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
        ‖z‖ ≤ 2 * D.σ i →
        ‖Work.Diff.STE.pdVec j l
          (fun y : Fin (Module.finrank ℝ E) → ℝ => ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K) :
    ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (m : ℕ), m ≤ N →
      ∀ (β : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
        ‖z‖ ≤ D.σ i →
        ‖Work.Diff.STE.pdVec m β
          (fun y : Fin (Module.finrank ℝ E) → ℝ => ((D.R i h a b y : ℝ) : ℂ)) z‖
          ≤ ((2 : ℝ) ^ N * ((Module.finrank ℝ E : ℝ) + 1) ^ N * ((N : ℝ) + 1)) * (W * K) := by
  intro i a b m hm β z hz
  obtain ⟨Mhat, hMsm, hMeq⟩ := exists_bumpMat (I := I) (M := M) D h hh i a b
  have hMhat : Mhat =ᶠ[nhds z] D.mat i h a b := hMeq z hz
  set F : (Fin (Module.finrank ℝ E) → ℝ) → ℂ :=
    fun y => ((Work.Diff.STE.Lead.matA (I := I) (M := M) D i y : ℝ) : ℂ) with hF
  set G : (Fin (Module.finrank ℝ E) → ℝ) → ℂ := fun y => ((Mhat y : ℝ) : ℂ) with hG
  have hFsm : ContDiff ℝ (⊤ : ℕ∞) F :=
    Complex.ofRealCLM.contDiff.comp (Work.Diff.STE.Lead.matA_contDiff (I := I) (M := M) D i)
  have hGsm : ContDiff ℝ (⊤ : ℕ∞) G := Complex.ofRealCLM.contDiff.comp hMsm
  have hGz : ∀ (j' : ℕ), j' ≤ N → ∀ γ : Fin j' → Fin (Module.finrank ℝ E),
      ‖Work.Diff.STE.pdVec j' γ G z‖ ≤ K := by
    intro j' hj' γ
    have hev : G =ᶠ[nhds z]
        (fun y : Fin (Module.finrank ℝ E) → ℝ => ((D.mat i h a b y : ℝ) : ℂ)) := by
      filter_upwards [hMhat] with y hy
      simp only [hG, hy]
    rw [Work.Diff.STE.csqp_pdVec_congr (l := γ) hev]
    exact hjet i a b j' hj' γ z (by have := D.hσ i; linarith)
  have hFz : ∀ (j' : ℕ), j' ≤ N → ∀ γ : Fin j' → Fin (Module.finrank ℝ E),
      ‖Work.Diff.STE.pdVec j' γ F z‖ ≤ W := fun j' hj' γ => hW i j' hj' γ z hz
  have hb := pdVec_mul_le (F := F) (G := G) (A := W) (B := K) hW0 hK0 hFsm hGsm hFz hGz m hm β
  have hfun : (fun y : Fin (Module.finrank ℝ E) → ℝ => ((D.R i h a b y : ℝ) : ℂ))
      =ᶠ[nhds z] (fun y => F y * G y) := by
    filter_upwards [hMhat] with y hy
    simp only [hF, hG]
    rw [Work.Diff.STE.Lead.R_eq_matA_mul_mat, ← hy, Complex.ofReal_mul]
  rw [Work.Diff.STE.csqp_pdVec_congr (l := β) hfun]
  exact hb

/-! ## 6. The assembly of `GardJet`

Combining the jet bound of the component on the `σ j`-ball (`jets_component_le`) with the
periodisation bound (`per_jets_le`) gives `GardJet D k K` for every `K > 0`. -/

end

end Work.Diff.STE.Lead.Gal

namespace Work.Diff.STE.Lead.Gal

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

theorem gardJet_holds
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) :
    ∀ K : ℝ, 0 < K → Work.Diff.STE.Lead.Gal.GardJet (I := I) (M := M) D k K := by
  intro K hK
  classical
  obtain ⟨W, hW0, hW⟩ := exists_weight_jets (I := I) (M := M) D (k + 1)
  set PC : ℝ := (2 : ℝ) ^ (k + 1) * ((Module.finrank ℝ E : ℝ) + 1) ^ (k + 1)
    * (((k + 1 : ℕ) : ℝ) + 1) with hPCdef
  have hPC0 : 0 ≤ PC := by rw [hPCdef]; positivity
  refine ⟨(2 : ℝ) ^ Module.finrank ℝ E * PC * W, by positivity, ?_⟩
  intro h hsmooth hjet j a b m hm β z
  have hcomp := jets_component_le (I := I) (M := M) D h hsmooth (k + 1) W K hW0 hK.le hW hjet
  have hσ8 : D.σ j ≤ 1 / 8 := by have := D.hσ2 j; linarith
  have hRsm : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Fin (Module.finrank ℝ E) → ℝ => ((D.R j h a b y : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp
      (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hsmooth j a b)
  have hB0 : 0 ≤ PC * (W * K) := by positivity
  have hsupp := support_R_subset_ball (I := I) (M := M) D h j a b
  have hper := per_jets_le (n := Module.finrank ℝ E) (N := k + 1) (σ := D.σ j)
    (B := PC * (W * K)) (le_of_lt (D.hσ j)) hσ8 hB0
    hRsm hsupp (fun m' hm' γ w hw => hcomp j a b m' hm' γ w hw) m hm β z
  have hK1 : K + 1 ≤ (1 + K) ^ (k + 1) := by
    have h1 : (1 : ℝ) ≤ 1 + K := by linarith
    simpa [add_comm, pow_one] using
      (pow_le_pow_right₀ h1 (show 1 ≤ k + 1 by omega) : (1 + K) ^ 1 ≤ (1 + K) ^ (k + 1))
  have hc : 0 ≤ (2 : ℝ) ^ Module.finrank ℝ E * PC * W := by positivity
  calc ‖Work.Diff.STE.pdVec m β (D.Rper j h a b) z‖
      = ‖Work.Diff.STE.pdVec m β (fun z : Fin (Module.finrank ℝ E) → ℝ =>
          ∑' m' : Fin (Module.finrank ℝ E) → ℤ,
            ((D.R j h a b (z + Work.Diff.STE.iVec m') : ℝ) : ℂ)) z‖ := rfl
    _ ≤ (2 : ℝ) ^ Module.finrank ℝ E * (PC * (W * K)) := hper
    _ = (2 : ℝ) ^ Module.finrank ℝ E * PC * W * K := by ring
    _ ≤ (2 : ℝ) ^ Module.finrank ℝ E * PC * W * (1 + K) ^ (k + 1) :=
        mul_le_mul_of_nonneg_left (le_trans (by linarith : K ≤ K + 1) hK1) hc

end

end Work.Diff.STE.Lead.Gal
