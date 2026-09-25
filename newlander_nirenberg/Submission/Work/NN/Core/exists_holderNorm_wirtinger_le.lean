/-
Copyright: none.  Part of the `Newlander–Nirenberg` formalisation project.

# The Wirtinger derivatives lower the Hölder order

For an open set `Ω ⊆ ℂⁿ` and `f : ℂⁿ → ℂ` of class `C^{k+1}`, the coordinate Wirtinger
derivatives `∂̄_j f` and `∂_j f` are "one derivative down": their `C^{k,α}` norms are
bounded by the `C^{k+1,α}` norm of `f`, with a constant independent of `f` and `j`.

Both operators are compositions of the real differential `fderiv ℝ f` with a *fixed*
continuous linear map on `(ℂⁿ →L[ℝ] ℂ)` (of norm `≤ 1`):

  `∂̄_j f = dbarCoordPhi j ∘ fderiv ℝ f`,  `∂_j f = dCoordLin j ∘ fderiv ℝ f`.

The `C^{k,α}` norm of such a composition is controlled by the `C^{k,α}` norm of
`fderiv ℝ f` (`comp_linear_le`), and the iterated derivatives of `fderiv ℝ f` are
exactly the iterated derivatives of `f` shifted by one (`iDN_fderivWithin`/`hSN_fderivWithin`).
-/
import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comm
import Submission.Work.CR.Flat.Polydisc.dbarCoord_norm_le_holderNorm
import Submission.Work.CR.Flat.Holder.Bilinear
import Submission.Work.CR.Flat.Holder.comp_linear_le

namespace Work.NN.Core

open scoped NNReal ENNReal Topology
open Set

open Work.CR.Flat (holderNorm iterDerivNorm holderSeminorm dbarCoord dCoord)
open Work.CR.Flat.Holder (iDN hSN iDN_congr hSN_congr iDN_fderivWithin hSN_fderivWithin
  comp_linear_le iDN_complex_eq hSN_complex_eq)
open Work.CR.Flat.Polydisc (dbarCoordPhi norm_dbarCombination_le dbarCoord_eq_comp)

noncomputable section

/-! ### `holderNorm` depends only on the values on the domain -/

lemma holderNorm_congr {n : ℕ} {k : ℕ} {α : ℝ} {f g : (Fin n → ℂ) → ℂ} {Ω : Set (Fin n → ℂ)}
    (h : ∀ x ∈ Ω, f x = g x) : holderNorm k α f Ω = holderNorm k α g Ω := by
  unfold Work.CR.Flat.holderNorm
  exact Finset.sum_congr rfl fun i _ => by
    have h1 : iterDerivNorm i f Ω = iterDerivNorm i g Ω := iDN_congr h
    have h2 : holderSeminorm i α f Ω = holderSeminorm i α g Ω := hSN_congr h
    rw [h1, h2]

/-! ### The `(1,0)`-operator as a fixed linear map on the real differential -/

/-- The continuous linear map `L ↦ (1/2)(L e_j - i·L(i·e_j))` on `(ℂⁿ →L[ℝ] ℂ)`;
composing it with `fderiv ℝ f` gives `∂_j f`. -/
def dCoordLin {n : ℕ} (j : Fin n) : ((Fin n → ℂ) →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ (1/2 : ℂ)).comp
    (ContinuousLinearMap.apply ℝ ℂ (Pi.single j 1)
      - (ContinuousLinearMap.mul ℝ ℂ Complex.I).comp
          (ContinuousLinearMap.apply ℝ ℂ (Pi.single j Complex.I)))

lemma dCoordLin_apply {n : ℕ} (j : Fin n) (D : (Fin n → ℂ) →L[ℝ] ℂ) :
    dCoordLin j D = (1/2 : ℂ) * (D (Pi.single j 1) - Complex.I * D (Pi.single j Complex.I)) := by
  simp only [dCoordLin, ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.mul_apply']

lemma dCoord_eq_comp {n : ℕ} (j : Fin n) (u : (Fin n → ℂ) → ℂ) :
    dCoord j u = dCoordLin j ∘ (fderiv ℝ u) := by
  funext x
  simp only [dCoordLin, Function.comp_apply, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, Work.CR.Flat.dCoord, ContinuousLinearMap.mul_apply']

/-- `‖dCoordLin j‖ ≤ 1`: the triangle inequality applied to the two evaluations of `D`
along the unit vectors `e_j`, `i e_j`. -/
lemma norm_dCoordLin_le {n : ℕ} (j : Fin n) : ‖dCoordLin j‖ ≤ 1 := by
  rw [ContinuousLinearMap.opNorm_le_iff (by norm_num : (0:ℝ) ≤ 1)]
  intro D
  rw [one_mul, dCoordLin_apply]
  have hv1 : ‖(Pi.single j (1 : ℂ) : Fin n → ℂ)‖ = 1 := by rw [Pi.norm_single]; norm_num
  have hv2 : ‖(Pi.single j (Complex.I : ℂ) : Fin n → ℂ)‖ = 1 := by rw [Pi.norm_single]; simp
  have h1 : ‖D (Pi.single j (1 : ℂ))‖ ≤ ‖D‖ := by
    have := D.le_opNorm (Pi.single j (1 : ℂ)); rwa [hv1, mul_one] at this
  have h2 : ‖D (Pi.single j (Complex.I : ℂ))‖ ≤ ‖D‖ := by
    have := D.le_opNorm (Pi.single j (Complex.I : ℂ)); rwa [hv2, mul_one] at this
  calc ‖(1/2 : ℂ) * (D (Pi.single j 1) - Complex.I * D (Pi.single j Complex.I))‖
      = (1/2) * ‖D (Pi.single j 1) - Complex.I * D (Pi.single j Complex.I)‖ := by
        rw [norm_mul]; norm_num
    _ ≤ (1/2) * (‖D (Pi.single j 1)‖ + ‖Complex.I * D (Pi.single j Complex.I)‖) := by
        have h := norm_sub_le (D (Pi.single j 1)) (Complex.I * D (Pi.single j Complex.I))
        have h1' : (0:ℝ) ≤ ‖D (Pi.single j (1:ℂ))‖ := norm_nonneg _
        have h2' : (0:ℝ) ≤ ‖Complex.I * D (Pi.single j Complex.I)‖ := norm_nonneg _
        linarith
    _ = (1/2) * (‖D (Pi.single j 1)‖ + ‖D (Pi.single j Complex.I)‖) := by
        rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ (1/2) * (‖D‖ + ‖D‖) := by linarith
    _ = ‖D‖ := by ring

/-- `‖dbarCoordPhi j‖ ≤ 1`. -/
lemma norm_dbarCoordPhi_le {n : ℕ} (j : Fin n) : ‖dbarCoordPhi j‖ ≤ 1 := by
  rw [ContinuousLinearMap.opNorm_le_iff (by norm_num : (0:ℝ) ≤ 1)]
  intro D
  have hD : dbarCoordPhi j D
      = (1/2 : ℂ) * (D (Pi.single j 1) + Complex.I * D (Pi.single j Complex.I)) := by
    simp only [Work.CR.Flat.Polydisc.dbarCoordPhi, ContinuousLinearMap.comp_apply, add_apply,
      ContinuousLinearMap.apply_apply, ContinuousLinearMap.mul_apply']
  rw [one_mul, hD]
  exact norm_dbarCombination_le j D

/-! ### The main estimate -/

/-- If `Φ` is a continuous linear map of norm `≤ 1` on the space of real-linear maps
`ℂⁿ → ℂ`, then the `C^{k,α}` norm of `Φ ∘ fderiv ℝ f` is bounded by the `C^{k+1,α}` norm
of `f`. -/
lemma holderNorm_comp_fderiv_le {n : ℕ} (k : ℕ) (α : ℝ) {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    {f : (Fin n → ℂ) → ℂ} (hf : ContDiffOn ℝ (k + 1) f Ω)
    (Φ : ((Fin n → ℂ) →L[ℝ] ℂ) →L[ℝ] ℂ) (hΦ : ‖Φ‖ ≤ 1) :
    holderNorm k α (Φ ∘ fderiv ℝ f) Ω ≤ holderNorm (k + 1) α f Ω := by
  have hΩu : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  have hm : ((k:ℕ):WithTop ℕ∞) + 1 ≤ (((k+1:ℕ)):WithTop ℕ∞) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
  have hfdiff : ContDiffOn ℝ (k:ℕ∞) (fun z => fderiv ℝ f z) Ω :=
    hf.fderiv_of_isOpen hΩ hm
  have hterm : ∀ i ∈ Finset.range (k+1),
      iterDerivNorm i (Φ ∘ fderiv ℝ f) Ω + holderSeminorm i α (Φ ∘ fderiv ℝ f) Ω
        ≤ iterDerivNorm (i+1) f Ω + holderSeminorm (i+1) α f Ω := by
    intro i hi
    rw [Finset.mem_range] at hi
    have hik : i ≤ k := by omega
    have hφi : ContDiffOn ℝ (i:ℕ∞) (fun z => fderiv ℝ f z) Ω :=
      hfdiff.of_le (WithTop.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hik))
    have hcomp := comp_linear_le Φ i α hφi hΩu
    have hIdn : iterDerivNorm i (Φ ∘ fderiv ℝ f) Ω ≤ iterDerivNorm (i+1) f Ω := by
      calc iterDerivNorm i (Φ ∘ fderiv ℝ f) Ω
          = iDN i (Φ ∘ fderiv ℝ f) Ω := (iDN_complex_eq i _ Ω).symm
        _ ≤ ENNReal.ofReal ‖Φ‖ * iDN i (fun z => fderiv ℝ f z) Ω := hcomp.1
        _ = ENNReal.ofReal ‖Φ‖ * iDN i (fun z => fderivWithin ℝ f Ω z) Ω := by
              rw [iDN_congr (fun z hz => (fderivWithin_of_isOpen hΩ hz).symm)]
        _ = ENNReal.ofReal ‖Φ‖ * iDN (i+1) f Ω := by rw [iDN_fderivWithin i f Ω hΩu]
        _ = ENNReal.ofReal ‖Φ‖ * iterDerivNorm (i+1) f Ω := by rw [iDN_complex_eq]
        _ ≤ 1 * iterDerivNorm (i+1) f Ω :=
              mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_one.mpr hΦ) bot_le
        _ = iterDerivNorm (i+1) f Ω := one_mul _
    have hHsn : holderSeminorm i α (Φ ∘ fderiv ℝ f) Ω ≤ holderSeminorm (i+1) α f Ω := by
      calc holderSeminorm i α (Φ ∘ fderiv ℝ f) Ω
          = hSN i α (Φ ∘ fderiv ℝ f) Ω := (hSN_complex_eq i α _ Ω).symm
        _ ≤ ENNReal.ofReal ‖Φ‖ * hSN i α (fun z => fderiv ℝ f z) Ω := hcomp.2
        _ = ENNReal.ofReal ‖Φ‖ * hSN i α (fun z => fderivWithin ℝ f Ω z) Ω := by
              rw [hSN_congr (fun z hz => (fderivWithin_of_isOpen hΩ hz).symm)]
        _ = ENNReal.ofReal ‖Φ‖ * hSN (i+1) α f Ω := by rw [hSN_fderivWithin i α f Ω hΩu]
        _ = ENNReal.ofReal ‖Φ‖ * holderSeminorm (i+1) α f Ω := by rw [hSN_complex_eq]
        _ ≤ 1 * holderSeminorm (i+1) α f Ω :=
              mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_one.mpr hΦ) bot_le
        _ = holderSeminorm (i+1) α f Ω := one_mul _
    exact add_le_add hIdn hHsn
  calc holderNorm k α (Φ ∘ fderiv ℝ f) Ω
      = ∑ i ∈ Finset.range (k+1), (iterDerivNorm i (Φ ∘ fderiv ℝ f) Ω
          + holderSeminorm i α (Φ ∘ fderiv ℝ f) Ω) := rfl
    _ ≤ ∑ i ∈ Finset.range (k+1), (iterDerivNorm (i+1) f Ω + holderSeminorm (i+1) α f Ω) :=
        Finset.sum_le_sum hterm
    _ ≤ holderNorm (k + 1) α f Ω := by
        rw [Work.CR.Flat.holderNorm]
        conv_rhs => rw [Finset.sum_range_succ']
        exact le_add_right le_rfl

/-- **The Wirtinger derivatives lower the Hölder order.**  For a `C^{k+1}` function on an open set
`Ω` and every coordinate `j`, the `C^{k,α}` norms of `∂̄_j f` and of `∂_j f` are bounded by the
`C^{k+1,α}` norm of `f`, with a constant depending only on `k, Ω`. -/
theorem exists_holderNorm_wirtinger_le {n : ℕ} (k : ℕ) {α : ℝ} {Ω : Set (Fin n → ℂ)}
    (hΩ : IsOpen Ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : (Fin n → ℂ) → ℂ, ContDiffOn ℝ (k + 1) f Ω → ∀ j : Fin n,
      Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dbarCoord j f z) Ω
          ≤ ENNReal.ofReal C * Work.CR.Flat.holderNorm (k + 1) α f Ω ∧
        Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dCoord j f z) Ω
          ≤ ENNReal.ofReal C * Work.CR.Flat.holderNorm (k + 1) α f Ω := by
  refine ⟨1, one_pos, ?_⟩
  intro f hf j
  have hdb_eq : holderNorm k α (fun z => dbarCoord j f z) Ω
      = holderNorm k α (dbarCoordPhi j ∘ fderiv ℝ f) Ω :=
    holderNorm_congr fun z _ => congrFun (dbarCoord_eq_comp j f) z
  have hdc_eq : holderNorm k α (fun z => dCoord j f z) Ω
      = holderNorm k α (dCoordLin j ∘ fderiv ℝ f) Ω :=
    holderNorm_congr fun z _ => congrFun (dCoord_eq_comp j f) z
  refine ⟨?_, ?_⟩
  · rw [hdb_eq, ENNReal.ofReal_one, one_mul]
    exact holderNorm_comp_fderiv_le k α hΩ hf (dbarCoordPhi j) (norm_dbarCoordPhi_le j)
  · rw [hdc_eq, ENNReal.ofReal_one, one_mul]
    exact holderNorm_comp_fderiv_le k α hΩ hf (dCoordLin j) (norm_dCoordLin_le j)

end

end Work.NN.Core
