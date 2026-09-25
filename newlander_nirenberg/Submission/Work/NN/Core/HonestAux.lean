/-
# Auxiliary lemmas for the honest `∂̄`-solvability statements

This file collects the localisation toolkit shared by `Work.NN.Core.dbarHonestOne` and
`Work.NN.Core.dbarHonestTwo`: the general Hölder-norm congruence, the globalisation of the
rescaled datum `Work.NN.Ratio.dataOf` when the datum is only `C^m` *on the polydisc*, and the
localised closedness of that datum.
-/
import Mathlib
import Submission.Work.NN.Ratio.Setup
import Submission.Work.NN.Ratio.Scale
import Submission.Work.NN.Ratio.PullBack
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc

noncomputable section

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

namespace Work.NN.Core

open Work.CR.Flat

/-! ## Congruence of the Hölder norms -/

/-- The `C^{k,α}`-norm only depends on the values on the (open) set `Ω`. -/
theorem holderNorm_congr_gen {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {k : ℕ} {α : ℝ} {Ω : Set X} {f g : X → ℂ} (h : ∀ x ∈ Ω, f x = g x) :
    holderNorm k α f Ω = holderNorm k α g Ω := by
  rw [holderNorm, holderNorm]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  · rw [iterDerivNorm, iterDerivNorm]
    refine iSup_congr fun x => iSup_congr fun hx => ?_
    rw [iteratedFDerivWithin_congr (fun y hy => (h y hy).symm) hx i]
  · rw [holderSeminorm, holderSeminorm]
    refine iSup_congr fun x => iSup_congr fun hx => iSup_congr fun y => iSup_congr fun hy => ?_
    congr 1
    rw [iteratedFDerivWithin_congr (fun z hz => (h z hz).symm) hx i,
      iteratedFDerivWithin_congr (fun z hz => (h z hz).symm) hy i]

/-! ## The polydisc cutoff is one on a neighbourhood of the inner polydisc -/

/-- The polydisc cutoff equals `1` on a whole neighbourhood of any point of the open polydisc
`polydisc 0 A`. -/
lemma polydiscCut_eventuallyEq_one {n : ℕ} {A B : Fin n → ℝ} (hA : ∀ j, 0 ≤ A j)
    (hB : ∀ j, A j < B j) {z : Fin n → ℂ} (hz : z ∈ polydisc 0 A) :
    Work.NN.Ratio.polydiscCut A B =ᶠ[𝓝 z] (fun _ => (1 : ℂ)) := by
  filter_upwards [(isOpen_polydisc (0 : Fin n → ℂ) A).mem_nhds hz] with y hy
  exact Work.NN.Ratio.polydiscCut_eq_one hA hB (fun j => le_of_lt (by simpa using hy j))

/-- On the open polydisc `polydisc 0 A` multiplication by the cutoff `polydiscCut A B` does not
change the function. -/
lemma polydiscCut_mul_eqOn {n : ℕ} {A B : Fin n → ℝ} (hA : ∀ j, 0 ≤ A j)
    (hB : ∀ j, A j < B j) {g : (Fin n → ℂ) → ℂ} :
    ∀ z ∈ polydisc (0 : Fin n → ℂ) A, Work.NN.Ratio.polydiscCut A B z * g z = g z := by
  intro z hz
  rw [Work.NN.Ratio.polydiscCut_eq_one hA hB (fun j => le_of_lt (by simpa using hz j)), one_mul]

/-- On the open polydisc `polydisc 0 A` multiplication by the cutoff `polydiscCut A B` does not
change the `∂̄`-derivative. -/
lemma dbarCoord_polydiscCut_mul_eq {n : ℕ} {A B : Fin n → ℝ} (hA : ∀ j, 0 ≤ A j)
    (hB : ∀ j, A j < B j) {g : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ} (hz : z ∈ polydisc 0 A)
    (l : Fin n) :
    dbarCoord l (fun y => Work.NN.Ratio.polydiscCut A B y * g y) z = dbarCoord l g z := by
  refine Work.NN.Ratio.dbarCoord_congr_eventually l ?_
  filter_upwards [polydiscCut_eventuallyEq_one hA hB hz] with y hy
  rw [hy, one_mul]

/-! ## Globalisation of the rescaled datum -/

/-- The rescaled datum `dataOf η ρ f j` is *globally* `C^m` as soon as `f j` is `C^m` on the
polydisc `polydisc 0 ρ`: the physical cutoff `polCut η ρ` is supported in the polydisc
`polydisc 0 (cutOut η ρ) ⊂ polydisc 0 ρ`, so the product with `f ∘ Φ` is globally smooth
`Work.NN.Ratio.contDiff_mul_of_tsupport_subset`. -/
theorem contDiff_dataOfHonest {n : ℕ} {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {m : ℕ} {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiffOn ℝ (↑m) (f j) (polydisc 0 ρ)) (j : Fin n) :
    ContDiff ℝ (↑m) (Work.NN.Ratio.dataOf η ρ f j) := by
  have hSpos : ∀ l, 0 < Work.NN.Ratio.scale η ρ l := fun l => Work.NN.Ratio.scale_pos h0 h1 hρ l
  set U : Set (Fin n → ℂ) := polydisc 0 (fun l => ρ l / Work.NN.Ratio.scale η ρ l)
  have hUopen : IsOpen U := isOpen_polydisc _ _
  set χ : (Fin n → ℂ) → ℂ :=
    fun y => Work.NN.Ratio.polydiscCut (Work.NN.Ratio.cutIn η ρ) (Work.NN.Ratio.cutOut η ρ)
      (Work.NN.Ratio.Phi (Work.NN.Ratio.scale η ρ) y)
  set F : (Fin n → ℂ) → ℂ := fun y => f j (Work.NN.Ratio.Phi (Work.NN.Ratio.scale η ρ) y)
  have hχsm : ContDiff ℝ (↑(⊤ : ℕ∞)) χ :=
    (Work.NN.Ratio.contDiff_polydiscCut _ _).comp (Work.NN.Ratio.contDiff_Phi _)
  have hmaps : MapsTo (Work.NN.Ratio.Phi (Work.NN.Ratio.scale η ρ)) U (polydisc 0 ρ) := by
    intro y hy l
    show ‖Work.NN.Ratio.Phi (Work.NN.Ratio.scale η ρ) y l - 0‖ < ρ l
    rw [sub_zero]
    show ‖(Work.NN.Ratio.scale η ρ l : ℂ) * y l‖ < ρ l
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hSpos l).le]
    have h2 : ‖y l‖ * Work.NN.Ratio.scale η ρ l < ρ l := by
      have h3 := hy l
      simp only [Pi.zero_apply, sub_zero] at h3
      rwa [lt_div_iff₀ (hSpos l)] at h3
    rw [mul_comm]
    exact h2
  have hFon : ContDiffOn ℝ (↑m) F U :=
    (hf j).comp (((Work.NN.Ratio.contDiff_Phi _).of_le (Work.NN.Ratio.le_infty m)).contDiffOn) hmaps
  have hPhiNorm : ∀ (y : Fin n → ℂ) (l : Fin n),
      ‖Work.NN.Ratio.Phi (Work.NN.Ratio.scale η ρ) y l‖ =
        Work.NN.Ratio.scale η ρ l * ‖y l‖ := by
    intro y l
    show ‖(Work.NN.Ratio.scale η ρ l : ℂ) * y l‖ = _
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hSpos l).le]
  have hsupp : tsupport χ ⊆ U := by
    have hcl : IsClosed {y : Fin n → ℂ | ∀ j,
        ‖y j‖ ≤ Work.NN.Ratio.cutOut η ρ j / Work.NN.Ratio.scale η ρ j} := by
      have hset : {y : Fin n → ℂ | ∀ j,
          ‖y j‖ ≤ Work.NN.Ratio.cutOut η ρ j / Work.NN.Ratio.scale η ρ j}
          = ⋂ j, {y : Fin n → ℂ | ‖y j‖ ≤ Work.NN.Ratio.cutOut η ρ j / Work.NN.Ratio.scale η ρ j} := by
        ext y; simp
      rw [hset]
      exact isClosed_iInter fun j => isClosed_le (continuous_norm.comp (continuous_apply j))
        continuous_const
    have hsub : Function.support χ ⊆ {y : Fin n → ℂ | ∀ j,
        ‖y j‖ ≤ Work.NN.Ratio.cutOut η ρ j / Work.NN.Ratio.scale η ρ j} := by
      intro y hy j
      have h1 : ‖Work.NN.Ratio.Phi (Work.NN.Ratio.scale η ρ) y j‖ < Work.NN.Ratio.cutOut η ρ j :=
        Work.NN.Ratio.polydiscCut_ne_zero_imp (fun i => Work.NN.Ratio.cutIn_nonneg h0 h1 hρ i)
          (fun i => Work.NN.Ratio.cutIn_lt_cutOut h0 h1 hρ i) hy j
      rw [hPhiNorm y j] at h1
      refine le_of_lt ((lt_div_iff₀ (hSpos j)).mpr ?_)
      rw [mul_comm]
      exact h1
    have hmono : closure (Function.support χ) ⊆ {y : Fin n → ℂ | ∀ j,
        ‖y j‖ ≤ Work.NN.Ratio.cutOut η ρ j / Work.NN.Ratio.scale η ρ j} :=
      closure_minimal hsub hcl
    intro y hy
    have hy' := hmono hy
    intro j
    have h2 := hy' j
    simp only [Pi.zero_apply, sub_zero]
    exact lt_of_le_of_lt h2
      (div_lt_div_of_pos_right (Work.NN.Ratio.cutOut_lt_rho h0 h1 hρ j) (hSpos j))
  have hmul : ContDiff ℝ (↑m) (fun y => χ y * F y) :=
    Work.NN.Ratio.contDiff_mul_of_tsupport_subset hχsm hUopen hsupp hFon
  have heq : Work.NN.Ratio.dataOf η ρ f j =
      fun y => (Work.NN.Ratio.scale η ρ j : ℂ) * (χ y * F y) := by
    funext y
    rw [Work.NN.Ratio.dataOf_apply]
    rfl
  rw [heq]
  exact contDiff_const.mul hmul

/-- Closedness of the rescaled datum on the tracking polydisc, from closedness of `f` *on the
polydisc* `polydisc 0 ρ` only: the dilation `Φ` maps the tracking polydisc into `polydisc 0 ρ`,
so only the closedness of `f` there is ever used. -/
theorem dataOf_closedOn {n : ℕ} {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiffOn ℝ 1 (f j) (polydisc 0 ρ))
    (hcl : ∀ j l z, z ∈ polydisc 0 ρ → dbarCoord j (f l) z = dbarCoord l (f j) z) :
    ∀ j l (y : Fin n → ℂ), y ∈ polydisc 0 (fun _ => Work.NN.Ratio.thrT η) →
      dbarCoord l (Work.NN.Ratio.dataOf η ρ f j) y
        = dbarCoord j (Work.NN.Ratio.dataOf η ρ f l) y := by
  intro j l y hy
  have hmem := Work.NN.Ratio.phi_mem_polydisc h0 h1 hρ hy
  have hdj : DifferentiableAt ℝ (f j) (Work.NN.Ratio.Phi (Work.NN.Ratio.scale η ρ) y) :=
    ((hf j).contDiffAt ((isOpen_polydisc (0 : Fin n → ℂ) ρ).mem_nhds hmem)).differentiableAt
      (by simp)
  have hdl : DifferentiableAt ℝ (f l) (Work.NN.Ratio.Phi (Work.NN.Ratio.scale η ρ) y) :=
    ((hf l).contDiffAt ((isOpen_polydisc (0 : Fin n → ℂ) ρ).mem_nhds hmem)).differentiableAt
      (by simp)
  rw [Work.NN.Ratio.dbarCoord_congr_eventually l (Work.NN.Ratio.dataOf_eventuallyEq h0 h1 hρ f j hy),
    Work.NN.Ratio.dbarCoord_congr_eventually j (Work.NN.Ratio.dataOf_eventuallyEq h0 h1 hρ f l hy),
    Work.NN.Ratio.dbarCoord_smul_Phi (Work.NN.Ratio.scale η ρ) l (Work.NN.Ratio.scale η ρ j : ℂ) hdj,
    Work.NN.Ratio.dbarCoord_smul_Phi (Work.NN.Ratio.scale η ρ) j (Work.NN.Ratio.scale η ρ l : ℂ) hdl,
    (hcl l j (Work.NN.Ratio.Phi (Work.NN.Ratio.scale η ρ) y) hmem).symm]
  ring


/-- Multiplication of a datum by the physical cutoff `polCut η ρ` turns a datum which is only
`C^m` on `polydisc 0 ρ` into a globally `C^m` datum.  (The cutoff is supported in
`polydisc 0 (cutOut η ρ)` with `cutOut η ρ < ρ`, so
`Work.NN.Ratio.contDiff_mul_of_tsupport_subset` applies.) -/
theorem contDiff_cutMul_polCut {n : ℕ} {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1 / 2)
    {ρ : Fin n → ℝ} (hρ : ∀ j, 0 < ρ j) {m : ℕ} {f : Fin n → (Fin n → ℂ) → ℂ}
    (hf : ∀ j, ContDiffOn ℝ (↑m) (f j) (polydisc 0 ρ)) (j : Fin n) :
    ContDiff ℝ (↑m) (Work.NN.Ratio.cutMul (Work.NN.Ratio.polCut η ρ) f j) := by
  have hsupp : tsupport (Work.NN.Ratio.polydiscCut (Work.NN.Ratio.cutIn η ρ)
      (Work.NN.Ratio.cutOut η ρ)) ⊆ polydisc 0 ρ := by
    refine subset_trans (Work.NN.Ratio.tsupport_polydiscCut_subset
      (fun i => Work.NN.Ratio.cutIn_nonneg h0 h1 hρ i)
      (fun i => Work.NN.Ratio.cutIn_lt_cutOut h0 h1 hρ i)) ?_
    intro z hz k
    simp only [Pi.zero_apply, sub_zero]
    exact lt_of_le_of_lt (hz k) (Work.NN.Ratio.cutOut_lt_rho h0 h1 hρ k)
  have h := Work.NN.Ratio.contDiff_mul_of_tsupport_subset
    (χ := Work.NN.Ratio.polydiscCut (Work.NN.Ratio.cutIn η ρ) (Work.NN.Ratio.cutOut η ρ))
    (f := f j) (Work.NN.Ratio.contDiff_polydiscCut _ _) (isOpen_polydisc 0 ρ) hsupp (hf j)
  show ContDiff ℝ (↑m) ((Work.NN.Ratio.cutMul (Work.NN.Ratio.polydiscCut (Work.NN.Ratio.cutIn η ρ)
      (Work.NN.Ratio.cutOut η ρ))) f j)
  have heq : (Work.NN.Ratio.cutMul (Work.NN.Ratio.polydiscCut (Work.NN.Ratio.cutIn η ρ)
      (Work.NN.Ratio.cutOut η ρ))) f j
      = fun z => Work.NN.Ratio.polydiscCut (Work.NN.Ratio.cutIn η ρ)
          (Work.NN.Ratio.cutOut η ρ) z * f j z := by
    funext z
    rw [Work.NN.Ratio.cutMul_apply]
  rw [heq]
  exact h

end Work.NN.Core
