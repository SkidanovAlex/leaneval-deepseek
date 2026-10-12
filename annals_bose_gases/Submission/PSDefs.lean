import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.SubaddVol
import Submission.Superadd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Shared infrastructure for the product trial states (see `Submission.ProductState`):
the `X 1 ≃ ℝ³` bridge, the one-particle lift, the two-block product states, and
their numerator/denominator decompositions.  This module contains no `sorry`.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real
open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## The `X 1 ≃ ℝ³` bridge -/

/-- Evaluation at the single element of `Fin 1`, as a measure-preserving equivalence. -/
noncomputable def oneEval : X 1 ≃ᵐ ℝ³ := MeasurableEquiv.funUnique (Fin 1) ℝ³

lemma oneEval_apply (w : X 1) : oneEval w = w 0 := rfl

lemma oneEval_measurePreserving : MeasurePreserving oneEval (volume : Measure (X 1))
    (volume : Measure ℝ³) := volume_preserving_funUnique (Fin 1) ℝ³

lemma oneEval_contDiff : ContDiff ℝ ∞ (fun w : X 1 => (w 0 : ℝ³)) := by fun_prop

lemma oneEval_continuous : Continuous (fun w : X 1 => (w 0 : ℝ³)) := by fun_prop

/-- The box of one particle is the preimage of the cube. -/
lemma box1_preimage {L : ℝ} : oneEval ⁻¹' (cube L) = box 1 L := by
  ext w
  simp [oneEval, box, cube]

/-- The support of the lifted function `w ↦ φ (w 0)` is inside the one-particle box. -/
lemma tsupport_oneLift {φ : ℝ³ → ℝ} {L : ℝ} (hφts : tsupport φ ⊆ interior (cube L)) :
    tsupport (fun w : X 1 => φ (w 0)) ⊆ interior (box 1 L) := by
  have hcl : tsupport (fun w : X 1 => φ (w 0)) ⊆ (fun w : X 1 => (w 0 : ℝ³)) ⁻¹' (tsupport φ) := by
    simpa [tsupport, Function.support] using
      (oneEval_continuous.closure_preimage_subset (Function.support φ))
  have hpre : (fun w : X 1 => (w 0 : ℝ³)) ⁻¹' (interior (cube L)) ⊆ interior (box 1 L) := by
    refine interior_maximal ?_ (isOpen_interior.preimage oneEval_continuous)
    intro x hx
    have hx1 : x ∈ oneEval ⁻¹' (cube L) := by
      simpa [oneEval_apply] using (Set.preimage_mono interior_subset hx)
    simpa [box1_preimage] using hx1
  exact hcl.trans ((Set.preimage_mono hφts).trans hpre)

/-- Integrals over the one-particle box of functions of `w 0` equal integrals over the cube. -/
lemma integral_box1 {L : ℝ} (f : ℝ³ → ℝ) :
    (∫ w in box 1 L, f (w 0)) = ∫ y in cube L, f y := by
  rw [← box1_preimage]
  have hmp := oneEval_measurePreserving.restrict_preimage_emb oneEval.measurableEmbedding (cube L)
  have h := hmp.integral_comp oneEval.measurableEmbedding (fun y : ℝ³ => f y)
  simpa [oneEval] using h

/-! ## Smoothness facts for the one-particle data -/

/-- The Laplacian of a `C^∞` function on `ℝ³` is continuous. -/
lemma laplacian_contDiff {φ : ℝ³ → ℝ} (hφc : ContDiff ℝ ∞ φ) :
    Continuous (fun x : ℝ³ => Δ φ x) := by
  have hφ2 : ContDiff ℝ 2 φ := by
    have h : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := WithTop.coe_le_coe.mpr (by exact (le_top : (2 : ℕ∞) ≤ ⊤))
    exact hφc.of_le h
  have hEq : (fun x : ℝ³ => Δ φ x) =
      fun x => ∑ k : Fin 3,
        (fderiv ℝ (fun z : ℝ³ => fderiv ℝ φ z (euclBasis3 k)) x) (euclBasis3 k) := by
    funext x
    rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f := φ) euclBasis3]
    apply Finset.sum_congr rfl
    intro k hk
    exact bridgeSecondDirIteratedFDeriv (f := φ) hφ2
  rw [hEq]
  refine continuous_finsetSum (s := Finset.univ) (f := fun k x =>
    (fderiv ℝ (fun z : ℝ³ => fderiv ℝ φ z (euclBasis3 k)) x) (euclBasis3 k)) ?_
  intro k hk
  let u : ℝ³ := euclBasis3 k
  have hf1 : ContDiff ℝ ∞ (fderiv ℝ φ) := ContDiff.fderiv_right (m := ∞) hφc (by simp)
  have heval : ContDiff ℝ ∞ (fun (L : ℝ³ →L[ℝ] ℝ) => L u) := by
    exact ((ContinuousLinearMap.apply (𝕜 := ℝ) (Fₗ := ℝ) u : (ℝ³ →L[ℝ] ℝ) →L[ℝ] ℝ).contDiff)
  have h0 : ContDiff ℝ ∞ (fun z : ℝ³ => fderiv ℝ φ z u) := by
    simpa [Function.comp_def] using heval.comp hf1
  have hd : ContDiff ℝ ∞ (fderiv ℝ (fun z : ℝ³ => fderiv ℝ φ z u)) :=
    ContDiff.fderiv_right (m := ∞) h0 (by simp)
  have hfinal : ContDiff ℝ ∞ (fun x : ℝ³ => (fderiv ℝ (fun z : ℝ³ => fderiv ℝ φ z u) x) u) := by
    simpa [Function.comp_def] using heval.comp hd
  simpa [u] using hfinal.continuous

/-- The lift `w ↦ φ (w 0)` has partial Laplacian `(Δφ) ∘ eval`. -/
lemma partialLaplacian_oneLift {φ : ℝ³ → ℝ} (w : X 1) :
    partialLaplacian (0 : Fin 1) (fun z : X 1 => φ (z 0)) w = Δ φ (w 0) := by
  unfold partialLaplacian
  simp

/-! ## The one-particle trial state from `φ` -/

/-- The one-particle state `z ↦ φ (z 0)`, admissible in the box of side `L`. -/
noncomputable def oneState {L : ℝ} {φ : ℝ³ → ℝ} (hφc : ContDiff ℝ ∞ φ)
    (hφts : tsupport φ ⊆ interior (cube L)) (hφnorm : (∫ x : ℝ³, (φ x)^2) = 1) :
    CInfty0Box 1 L where
  toFun := fun z => φ (z 0)
  contDiff := (hφc.comp oneEval_contDiff).contDiffOn
  support := tsupport_oneLift (φ := φ) hφts
  nezero := by
    intro hz
    have hφ0 : ∀ x : ℝ³, φ x = 0 := by
      intro x
      simpa using (congrFun hz (fun _ : Fin 1 => x))
    have hnorm0 : (∫ x : ℝ³, (φ x)^2) = 0 := by
      simp [hφ0]
    linarith

lemma oneState_coe {L : ℝ} {φ : ℝ³ → ℝ} (hφc : ContDiff ℝ ∞ φ)
    (hφts : tsupport φ ⊆ interior (cube L)) (hφnorm : (∫ x : ℝ³, (φ x)^2) = 1) :
    ((oneState (φ := φ) hφc hφts hφnorm : CInfty0Box 1 L) : X 1 → ℝ) =
      fun z => φ (z 0) := by
  rfl

/-- The one-particle state is normalized: `∫ φ₁² = 1`. -/
lemma oneState_den {L : ℝ} {φ : ℝ³ → ℝ} (hφc : ContDiff ℝ ∞ φ)
    (hφts : tsupport φ ⊆ interior (cube L)) (hφnorm : (∫ x : ℝ³, (φ x)^2) = 1) :
    (∫ w in box 1 L, ((oneState (φ := φ) hφc hφts hφnorm : X 1 → ℝ) w)^2) = 1 := by
  have h1 : (∫ w in box 1 L, ((oneState (φ := φ) hφc hφts hφnorm : X 1 → ℝ) w)^2)
      = ∫ y in cube L, (φ y)^2 := by
    change (∫ w in box 1 L, φ (w 0) ^ 2) = ∫ y in cube L, (φ y)^2
    exact integral_box1 (L := L) (f := fun y => (φ y)^2)
  have h2 : (∫ y in cube L, (φ y)^2) = ∫ x : ℝ³, (φ x)^2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hx0 : x ∉ interior (cube L) := by
      intro hi; exact hx (interior_subset hi)
    have hx2 : x ∉ tsupport φ := by
      intro ht; exact hx0 (hφts ht)
    have hφx0 : φ x = 0 := image_eq_zero_of_notMem_tsupport (f := φ) hx2
    simp [hφx0]
  rw [h1, h2, hφnorm]

/-- The square of the one-particle state is bounded by `sp`. -/
lemma oneState_sq_le {L : ℝ} {φ : ℝ³ → ℝ} {sp : ℝ} (hφc : ContDiff ℝ ∞ φ)
    (hφts : tsupport φ ⊆ interior (cube L)) (hφnorm : (∫ x : ℝ³, (φ x)^2) = 1)
    (hφsq : ∀ x : ℝ³, (φ x)^2 ≤ sp) (w : X 1) :
    (((oneState (φ := φ) hφc hφts hφnorm : X 1 → ℝ) w)^2) ≤ sp := by
  simpa [oneState] using hφsq (w 0)

/-! ## Two-block product states -/

/-- Product of two states in the same box, as an admissible state. -/
lemma psProdState_mem {N1 N2 : ℕ} {L : ℝ} (Φ1 : CInfty0Box N1 L) (Φ2 : CInfty0Box N2 L) :
    ∃ Φ : CInfty0Box (N1+N2) L,
      ((Φ : X (N1+N2) → ℝ) = prodState N1 N2 (Φ1 : X N1 → ℝ) (Φ2 : X N2 → ℝ)) := by
  let f1 : X N1 → ℝ := (Φ1 : X N1 → ℝ)
  let f2 : X N2 → ℝ := (Φ2 : X N2 → ℝ)
  have hg : ContDiff ℝ ∞ (prodState N1 N2 f1 f2) := by
    unfold prodState
    have h1 : ContDiff ℝ ∞ (fun x : X (N1+N2) => f1 (firstBlock N1 N2 x)) :=
      (psi_contDiff Φ1).comp (fstCLM N1 N2).contDiff
    have h2 : ContDiff ℝ ∞ (fun x : X (N1+N2) => f2 (lastBlock N1 N2 x)) :=
      (psi_contDiff Φ2).comp (lstCLM N1 N2).contDiff
    exact ContDiff.mul h1 h2
  have hs1 : Function.support (prodState N1 N2 f1 f2) ⊆ (firstBlock N1 N2) ⁻¹' (Function.support f1) := by
    intro x hx
    change f1 (firstBlock N1 N2 x) ≠ 0
    intro hz
    apply hx
    simp [prodState, hz]
  have hs2 : Function.support (prodState N1 N2 f1 f2) ⊆ (lastBlock N1 N2) ⁻¹' (Function.support f2) := by
    intro x hx
    change f2 (lastBlock N1 N2 x) ≠ 0
    intro hz
    apply hx
    simp [prodState, hz]
  have hts1 : tsupport (prodState N1 N2 f1 f2) ⊆ (firstBlock N1 N2) ⁻¹' (tsupport f1) := by
    exact (closure_mono hs1).trans ((firstBlock_continuous N1 N2).closure_preimage_subset (Function.support f1))
  have hts2 : tsupport (prodState N1 N2 f1 f2) ⊆ (lastBlock N1 N2) ⁻¹' (tsupport f2) := by
    exact (closure_mono hs2).trans ((lastBlock_continuous N1 N2).closure_preimage_subset (Function.support f2))
  have hO : {x : X (N1+N2) | firstBlock N1 N2 x ∈ interior (box N1 L) ∧
        lastBlock N1 N2 x ∈ interior (box N2 L)} ⊆ interior (box (N1+N2) L) := by
    refine interior_maximal ?_ ?_
    · intro x hx
      exact (mem_box_split N1 N2 L x).mpr ⟨interior_subset hx.1, interior_subset hx.2⟩
    · exact (isOpen_interior.preimage (firstBlock_continuous N1 N2)).inter
        (isOpen_interior.preimage (lastBlock_continuous N1 N2))
  have hsupp : tsupport (prodState N1 N2 f1 f2) ⊆ interior (box (N1+N2) L) := by
    intro x hx
    apply hO
    constructor
    · exact (Set.preimage_mono Φ1.support) (hts1 hx)
    · exact (Set.preimage_mono Φ2.support) (hts2 hx)
  refine ⟨⟨prodState N1 N2 f1 f2, hg.contDiffOn, hsupp, ?_⟩, rfl⟩
  have hne1 : ∃ u0 : X N1, f1 u0 ≠ 0 := by
    by_contra h
    have hz : f1 = 0 := by
      funext u
      by_contra hu
      exact h ⟨u, hu⟩
    exact Φ1.nezero (by simpa [f1] using hz)
  have hne2 : ∃ w0 : X N2, f2 w0 ≠ 0 := by
    by_contra h
    have hz : f2 = 0 := by
      funext w
      by_contra hw
      exact h ⟨w, hw⟩
    exact Φ2.nezero (by simpa [f2] using hz)
  rcases hne1 with ⟨u0, hu0⟩
  rcases hne2 with ⟨w0, hw0⟩
  let x0 : X (N1+N2) := mergeBlock N1 N2 (u0, w0)
  have hx : prodState N1 N2 f1 f2 x0 ≠ 0 := by
    have hfb : firstBlock N1 N2 x0 = u0 := by simp [x0, mergeBlock_first]
    have hlb : lastBlock N1 N2 x0 = w0 := by simp [x0, mergeBlock_last]
    simpa [prodState, hfb, hlb] using (mul_ne_zero hu0 hw0)
  intro hzero
  exact hx (congrFun hzero x0)

/-- The product state of two states in the same box. -/
noncomputable def psProdState {N1 N2 : ℕ} {L : ℝ} (Φ1 : CInfty0Box N1 L)
    (Φ2 : CInfty0Box N2 L) : CInfty0Box (N1+N2) L :=
  Classical.choose (psProdState_mem Φ1 Φ2)

lemma psProdState_coe {N1 N2 : ℕ} {L : ℝ} (Φ1 : CInfty0Box N1 L) (Φ2 : CInfty0Box N2 L) :
    ((psProdState Φ1 Φ2 : CInfty0Box (N1+N2) L) : X (N1+N2) → ℝ) =
      prodState N1 N2 (Φ1 : X N1 → ℝ) (Φ2 : X N2 → ℝ) := by
  exact Classical.choose_spec (psProdState_mem Φ1 Φ2)

/-- The denominator (square of the L² norm on the box) of a state. -/
noncomputable def psDen (N : ℕ) (L : ℝ) (Φ : CInfty0Box N L) : ℝ :=
  ∫ x in box N L, ((Φ : X N → ℝ) x)^2

/-- The numerator of the Rayleigh quotient of a state. -/
noncomputable def psNum (N : ℕ) (L : ℝ) (v : ℝ³ → ℝ) (Φ : CInfty0Box N L) : ℝ :=
  ∫ x in box N L, (Φ : X N → ℝ) x * 𝓗 N v (Φ : X N → ℝ) x

/-- The integrated cross interaction of a two-block product state. -/
noncomputable def psCross {N1 N2 : ℕ} (L : ℝ) (v : ℝ³ → ℝ) (P : X (N1+N2) → ℝ) : ℝ :=
  ∫ x in box (N1+N2) L, (P x)^2 * crossSum N1 N2 v (firstBlock N1 N2 x) (lastBlock N1 N2 x)

/-- `boxQuot` is the ratio of the numerator by the denominator. -/
lemma boxQuot_eq_ps {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (Φ : CInfty0Box N L) :
    boxQuot N L v Φ = psNum N L v Φ / psDen N L Φ := by
  have hden : (√ (∫ x in box N L, (Φ : X N → ℝ) x * (Φ : X N → ℝ) x)) ^ 2 = psDen N L Φ := by
    unfold psDen
    have hge : 0 ≤ (∫ x in box N L, (Φ : X N → ℝ) x * (Φ : X N → ℝ) x) :=
      integral_nonneg (fun x => mul_self_nonneg _)
    calc
      (√ (∫ x in box N L, (Φ : X N → ℝ) x * (Φ : X N → ℝ) x)) ^ 2
          = (∫ x in box N L, (Φ : X N → ℝ) x * (Φ : X N → ℝ) x) := Real.sq_sqrt hge
      _ = ∫ x in box N L, ((Φ : X N → ℝ) x)^2 := by
            apply integral_congr_ae
            filter_upwards with x
            rw [pow_two]
  unfold boxQuot psNum
  rw [hden]

/-- The denominator of a product state is the product of the denominators. -/
lemma psDen_prod {N1 N2 : ℕ} {L : ℝ} (Φ1 : CInfty0Box N1 L) (Φ2 : CInfty0Box N2 L) :
    psDen (N1+N2) L (psProdState Φ1 Φ2) = psDen N1 L Φ1 * psDen N2 L Φ2 := by
  unfold psDen
  rw [psProdState_coe]
  have hpt : (fun x : X (N1+N2) => (prodState N1 N2 (Φ1 : X N1 → ℝ) (Φ2 : X N2 → ℝ) x)^2) =
      fun x => (fun u : X N1 => ((Φ1 : X N1 → ℝ) u)^2) (firstBlock N1 N2 x) *
        (fun w : X N2 => ((Φ2 : X N2 → ℝ) w)^2) (lastBlock N1 N2 x) := by
    funext x
    simp [prodState]
    ring
  rw [hpt]
  exact boxIntegral_prod_fun L (fun u : X N1 => ((Φ1 : X N1 → ℝ) u)^2)
    (fun w : X N2 => ((Φ2 : X N2 → ℝ) w)^2)

/-- The numerator of a product state splits into block numerators plus the cross term. -/
lemma psNum_prod {N1 N2 : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv1 : MemLp v 1)
    (Φ1 : CInfty0Box N1 L) (Φ2 : CInfty0Box N2 L) :
    psNum (N1+N2) L v (psProdState Φ1 Φ2) =
      psNum N1 L v Φ1 * psDen N2 L Φ2 + psDen N1 L Φ1 * psNum N2 L v Φ2 +
        psCross (L := L) v (psProdState Φ1 Φ2) := by
  let f1 : X N1 → ℝ := (Φ1 : X N1 → ℝ)
  let f2 : X N2 → ℝ := (Φ2 : X N2 → ℝ)
  let Ψ : CInfty0Box (N1+N2) L := psProdState Φ1 Φ2
  let P : X (N1+N2) → ℝ := prodState N1 N2 f1 f2
  have hP : (Ψ : X (N1+N2) → ℝ) = P := by
    simp [Ψ, P, f1, f2, psProdState_coe]
  have h2c1 : ContDiff ℝ 2 f1 := psi_contDiff_two Φ1
  have h2c2 : ContDiff ℝ 2 f2 := psi_contDiff_two Φ2
  let D1 : ℝ := ∫ u in box N1 L, f1 u * f1 u
  let D2 : ℝ := ∫ w in box N2 L, f2 w * f2 w
  let K1 : ℝ := kineticEnergy N1 L Φ1
  let K2 : ℝ := kineticEnergy N2 L Φ2
  let I1 : ℝ := interactionEnergy N1 L v Φ1
  let I2 : ℝ := interactionEnergy N2 L v Φ2
  have hsum1 : (∑ i1 : Fin N1, ∫ x in box (N1+N2) L,
          P x * (-(partialLaplacian (Fin.castAdd N2 i1) P x))) = K1 * D2 := by
    calc
      (∑ i1 : Fin N1, ∫ x in box (N1+N2) L,
          P x * (-(partialLaplacian (Fin.castAdd N2 i1) P x)))
          = ∑ i1 : Fin N1,
              (∫ u in box N1 L, f1 u * (-(partialLaplacian i1 f1 u))) * D2 := by
            apply Finset.sum_congr rfl
            intro i1 hi1
            have ht := kinetic_term_first (N1 := N1) (N2 := N2) (L := L) (f1 := f1) (f2 := f2) h2c1 i1
            dsimp [D2]
            simpa [P, f1, f2, prodState] using ht
      _ = (∑ i1 : Fin N1, ∫ u in box N1 L, f1 u * (-(partialLaplacian i1 f1 u))) * D2 := by
            rw [Finset.sum_mul]
      _ = K1 * D2 := by
            dsimp [K1]
            unfold kineticEnergy
            rfl
  have hsum2 : (∑ j2 : Fin N2, ∫ x in box (N1+N2) L,
          P x * (-(partialLaplacian (Fin.natAdd N1 j2) P x))) = D1 * K2 := by
    calc
      (∑ j2 : Fin N2, ∫ x in box (N1+N2) L,
          P x * (-(partialLaplacian (Fin.natAdd N1 j2) P x)))
          = ∑ j2 : Fin N2,
              D1 * (∫ w in box N2 L, f2 w * (-(partialLaplacian j2 f2 w))) := by
            apply Finset.sum_congr rfl
            intro j2 hj2
            have ht := kinetic_term_last (N1 := N1) (N2 := N2) (L := L) (f1 := f1) (f2 := f2) h2c2 j2
            dsimp [D1]
            simpa [P, f1, f2, prodState] using ht
      _ = D1 * (∑ j2 : Fin N2, ∫ w in box N2 L, f2 w * (-(partialLaplacian j2 f2 w))) := by
            rw [Finset.mul_sum]
      _ = D1 * K2 := by
            dsimp [K2]
            unfold kineticEnergy
            rfl
  have hK3 : kineticEnergy (N1+N2) L Ψ = K1 * D2 + D1 * K2 := by
    calc
      kineticEnergy (N1+N2) L Ψ
          = ∑ i : Fin (N1+N2), ∫ x in box (N1+N2) L,
              (Ψ : X (N1+N2) → ℝ) x * (-(partialLaplacian i (Ψ : X (N1+N2) → ℝ) x)) := rfl
      _ = ∑ i : Fin (N1+N2), ∫ x in box (N1+N2) L,
              P x * (-(partialLaplacian i P x)) := by
            simp [hP]
      _ = (∑ i1 : Fin N1, ∫ x in box (N1+N2) L,
              P x * (-(partialLaplacian (Fin.castAdd N2 i1) P x))) +
          (∑ j2 : Fin N2, ∫ x in box (N1+N2) L,
              P x * (-(partialLaplacian (Fin.natAdd N1 j2) P x))) := by
            rw [Fin.sum_univ_add]
      _ = K1 * D2 + D1 * K2 := by rw [hsum1, hsum2]
  have hint1 : IntegrableOn (fun u : X N1 => (f1 u)^2 * pairSum N1 v u) (box N1 L) volume := by
    convert (integrableOn_intIntegrand (N := N1) hL (v := v) hv1 Φ1) using 1
    funext u
    simp [f1, intIntegrand, pairSum]
  have hden1c : IntegrableOn (fun u : X N1 => (f1 u)^2) (box N1 L) volume := by
    have hc : Continuous (fun u : X N1 => (f1 u)^2) := (psi_contDiff Φ1).continuous.pow 2
    exact ContinuousOn.integrableOn_compact (box_compact hL) hc.continuousOn
  have hint2 : IntegrableOn (fun w : X N2 => (f2 w)^2 * pairSum N2 v w) (box N2 L) volume := by
    convert (integrableOn_intIntegrand (N := N2) hL (v := v) hv1 Φ2) using 1
    funext w
    simp [f2, intIntegrand, pairSum]
  have hden2c : IntegrableOn (fun w : X N2 => (f2 w)^2) (box N2 L) volume := by
    have hc : Continuous (fun w : X N2 => (f2 w)^2) := (psi_contDiff Φ2).continuous.pow 2
    exact ContinuousOn.integrableOn_compact (box_compact hL) hc.continuousOn
  have hP1 : IntegrableOn (fun x : X (N1+N2) =>
        (P x)^2 * pairSum N1 v (firstBlock N1 N2 x)) (box (N1+N2) L) volume := by
    have hprod := integrableOn_prod_box (N1 := N1) (N2 := N2) L
      (a := fun u : X N1 => (f1 u)^2 * pairSum N1 v u) (b := fun w : X N2 => (f2 w)^2)
      hint1 hden2c
    convert hprod using 1
    · funext x
      simp [P, f1, f2, prodState]
      ring
  have hP2 : IntegrableOn (fun x : X (N1+N2) =>
        (P x)^2 * pairSum N2 v (lastBlock N1 N2 x)) (box (N1+N2) L) volume := by
    have hprod := integrableOn_prod_box (N1 := N1) (N2 := N2) L
      (a := fun u : X N1 => (f1 u)^2) (b := fun w : X N2 => (f2 w)^2 * pairSum N2 v w)
      hden1c hint2
    convert hprod using 1
    · funext x
      simp [P, f1, f2, prodState]
      ring
  have hT : IntegrableOn (fun x : X (N1+N2) =>
        (P x)^2 * pairSum (N1+N2) v x) (box (N1+N2) L) volume := by
    convert (integrableOn_intIntegrand (N := N1+N2) hL (v := v) hv1 Ψ) using 1
    funext x
    simp [P, f1, f2, psProdState_coe, Ψ, pairSum, intIntegrand]
  have hP3 : IntegrableOn (fun x : X (N1+N2) =>
        (P x)^2 * crossSum N1 N2 v (firstBlock N1 N2 x) (lastBlock N1 N2 x))
      (box (N1+N2) L) volume := by
    have hA3eq : (fun x : X (N1+N2) =>
          (P x)^2 * crossSum N1 N2 v (firstBlock N1 N2 x) (lastBlock N1 N2 x)) =
        (fun x : X (N1+N2) =>
          (P x)^2 * pairSum (N1+N2) v x - (P x)^2 * pairSum N1 v (firstBlock N1 N2 x) -
            (P x)^2 * pairSum N2 v (lastBlock N1 N2 x)) := by
      funext x
      rw [pairSum_block_split]
      ring
    rw [hA3eq]
    exact IntegrableOn.sub (IntegrableOn.sub hT hP1) hP2
  have hI1val : I1 = (∫ u in box N1 L, (f1 u)^2 * pairSum N1 v u) := by
    calc
      I1 = ∫ u in box N1 L, intIntegrand N1 L v Φ1 u := by
            dsimp [I1]
            rw [boxInt_intIntegrand N1 L v Φ1]
      _ = ∫ u in box N1 L, (f1 u)^2 * pairSum N1 v u := by
            apply integral_congr_ae
            filter_upwards with u
            simp [f1, intIntegrand, pairSum]
  have hI2val : I2 = (∫ w in box N2 L, (f2 w)^2 * pairSum N2 v w) := by
    calc
      I2 = ∫ w in box N2 L, intIntegrand N2 L v Φ2 w := by
            dsimp [I2]
            rw [boxInt_intIntegrand N2 L v Φ2]
      _ = ∫ w in box N2 L, (f2 w)^2 * pairSum N2 v w := by
            apply integral_congr_ae
            filter_upwards with w
            simp [f2, intIntegrand, pairSum]
  have hvalP1 : (∫ x in box (N1+N2) L,
        (P x)^2 * pairSum N1 v (firstBlock N1 N2 x)) = I1 * D2 := by
    calc
      (∫ x in box (N1+N2) L, (P x)^2 * pairSum N1 v (firstBlock N1 N2 x))
          = ∫ x in box (N1+N2) L,
              ((f1 (firstBlock N1 N2 x))^2 * pairSum N1 v (firstBlock N1 N2 x)) *
                ((f2 (lastBlock N1 N2 x))^2) := by
            apply integral_congr_ae
            filter_upwards with x
            simp [P, f1, f2, prodState]
            ring
      _ = (∫ u in box N1 L, (f1 u)^2 * pairSum N1 v u) * (∫ w in box N2 L, (f2 w)^2) := by
            exact boxIntegral_prod_fun L (fun u : X N1 => (f1 u)^2 * pairSum N1 v u)
              (fun w : X N2 => (f2 w)^2)
      _ = I1 * D2 := by
            rw [hI1val]
            dsimp [D2]
            apply congrArg (fun t : ℝ => I1 * t)
            apply integral_congr_ae
            filter_upwards with w
            rw [pow_two]
  have hvalP2 : (∫ x in box (N1+N2) L,
        (P x)^2 * pairSum N2 v (lastBlock N1 N2 x)) = D1 * I2 := by
    calc
      (∫ x in box (N1+N2) L, (P x)^2 * pairSum N2 v (lastBlock N1 N2 x))
          = ∫ x in box (N1+N2) L,
              ((f1 (firstBlock N1 N2 x))^2) *
                ((f2 (lastBlock N1 N2 x))^2 * pairSum N2 v (lastBlock N1 N2 x)) := by
            apply integral_congr_ae
            filter_upwards with x
            simp [P, f1, f2, prodState]
            ring
      _ = (∫ u in box N1 L, (f1 u)^2) * (∫ w in box N2 L, (f2 w)^2 * pairSum N2 v w) := by
            exact boxIntegral_prod_fun L (fun u : X N1 => (f1 u)^2)
              (fun w : X N2 => (f2 w)^2 * pairSum N2 v w)
      _ = D1 * I2 := by
            rw [hI2val]
            dsimp [D1]
            congr 1
            · apply integral_congr_ae
              filter_upwards with u
              rw [pow_two]
  have hI3 : interactionEnergy (N1+N2) L v Ψ =
      I1 * D2 + D1 * I2 + psCross (L := L) v (psProdState Φ1 Φ2) := by
    have h12 : IntegrableOn (fun x : X (N1+N2) =>
        (P x)^2 * pairSum N1 v (firstBlock N1 N2 x) +
          (P x)^2 * pairSum N2 v (lastBlock N1 N2 x)) (box (N1+N2) L) volume :=
      IntegrableOn.add hP1 hP2
    calc
      interactionEnergy (N1+N2) L v Ψ
          = ∫ x in box (N1+N2) L, (P x)^2 * pairSum (N1+N2) v x := by
            unfold interactionEnergy
            rw [hP]
            rfl
      _ = ∫ x in box (N1+N2) L,
            ((P x)^2 * pairSum N1 v (firstBlock N1 N2 x) +
              (P x)^2 * pairSum N2 v (lastBlock N1 N2 x)) +
              (P x)^2 * crossSum N1 N2 v (firstBlock N1 N2 x) (lastBlock N1 N2 x) := by
            apply integral_congr_ae
            filter_upwards with x
            rw [pairSum_block_split]
            ring
      _ = (∫ x in box (N1+N2) L,
            ((P x)^2 * pairSum N1 v (firstBlock N1 N2 x) +
              (P x)^2 * pairSum N2 v (lastBlock N1 N2 x))) +
          (∫ x in box (N1+N2) L,
            (P x)^2 * crossSum N1 N2 v (firstBlock N1 N2 x) (lastBlock N1 N2 x)) := by
            exact integral_add (μ := volume.restrict (box (N1+N2) L)) h12 hP3
      _ = (∫ x in box (N1+N2) L,
            (P x)^2 * pairSum N1 v (firstBlock N1 N2 x)) +
          (∫ x in box (N1+N2) L,
            (P x)^2 * pairSum N2 v (lastBlock N1 N2 x)) +
          (∫ x in box (N1+N2) L,
            (P x)^2 * crossSum N1 N2 v (firstBlock N1 N2 x) (lastBlock N1 N2 x)) := by
            rw [integral_add (μ := volume.restrict (box (N1+N2) L)) hP1 hP2]
      _ = I1 * D2 + D1 * I2 + psCross (L := L) v (psProdState Φ1 Φ2) := by
            rw [hvalP1, hvalP2]
            congr 1
            unfold psCross
            simp [P, f1, f2, psProdState_coe]
  have hnum3 : psNum (N1+N2) L v Ψ = K1 * D2 + D1 * K2 + (I1 * D2 + D1 * I2) + psCross (L := L) v Ψ := by
    calc
      psNum (N1+N2) L v Ψ
          = kineticEnergy (N1+N2) L Ψ + interactionEnergy (N1+N2) L v Ψ := by
            simpa [psNum, hP] using (energy_decomposition_admissible (N1+N2) hL (v := v) hv1 Ψ)
      _ = (K1 * D2 + D1 * K2) + (I1 * D2 + D1 * I2 + psCross (L := L) v Ψ) := by
            rw [hK3, hI3]
      _ = K1 * D2 + D1 * K2 + (I1 * D2 + D1 * I2) + psCross (L := L) v Ψ := by ring
  have hnum1 : psNum N1 L v Φ1 = K1 + I1 := by
    simpa [psNum, f1] using (energy_decomposition_admissible N1 hL (v := v) hv1 Φ1)
  have hnum2 : psNum N2 L v Φ2 = K2 + I2 := by
    simpa [psNum, f2] using (energy_decomposition_admissible N2 hL (v := v) hv1 Φ2)
  have hD1 : psDen N1 L Φ1 = D1 := by
    dsimp [D1, psDen, f1]
    apply integral_congr_ae
    filter_upwards with u
    rw [pow_two]
  have hD2 : psDen N2 L Φ2 = D2 := by
    dsimp [D2, psDen, f2]
    apply integral_congr_ae
    filter_upwards with w
    rw [pow_two]
  calc
    psNum (N1+N2) L v (psProdState Φ1 Φ2) = K1 * D2 + D1 * K2 + (I1 * D2 + D1 * I2) + psCross (L := L) v Ψ := by
          simpa [Ψ] using hnum3
    _ = (K1 + I1) * D2 + D1 * (K2 + I2) + psCross (L := L) v Ψ := by ring
    _ = psNum N1 L v Φ1 * psDen N2 L Φ2 + psDen N1 L Φ1 * psNum N2 L v Φ2 +
          psCross (L := L) v (psProdState Φ1 Φ2) := by
          rw [hnum1, hnum2, hD1, hD2]

/-- The one-particle numerator is bounded in absolute value by `∫|φ Δ φ|`. -/
lemma psNum_one_abs_le {L : ℝ} {v : ℝ³ → ℝ} {φ : ℝ³ → ℝ}
    (hφc : ContDiff ℝ ∞ φ) (hφts : tsupport φ ⊆ interior (cube L))
    (hφnorm : (∫ x : ℝ³, (φ x)^2) = 1) :
    |psNum 1 L v (oneState (φ := φ) hφc hφts hφnorm)| ≤
      ∫ x : ℝ³, |φ x * Δ φ x| := by
  let Φ1 : CInfty0Box 1 L := oneState (φ := φ) hφc hφts hφnorm
  have hH : ∀ w : X 1, 𝓗 1 v (Φ1 : X 1 → ℝ) w = -(Δ φ (w 0)) := by
    intro w
    unfold _root_.BoseGases.𝓗
    rw [Fin.sum_univ_one]
    simp [Φ1, oneState, partialLaplacian_oneLift]
    apply Finset.sum_eq_zero
    intro x hx
    exfalso
    simp at hx
    have hx1 : (x.1 : ℕ) < 1 := x.1.isLt
    have hx2 : (x.2 : ℕ) < 1 := x.2.isLt
    omega
  have hnum1 : psNum 1 L v Φ1 = ∫ w in box 1 L, φ (w 0) * (-(Δ φ (w 0))) := by
    calc
      psNum 1 L v Φ1 = ∫ w in box 1 L, (Φ1 : X 1 → ℝ) w * 𝓗 1 v (Φ1 : X 1 → ℝ) w := rfl
      _ = ∫ w in box 1 L, φ (w 0) * (-(Δ φ (w 0))) := by
            apply integral_congr_ae
            filter_upwards with w
            rw [hH]
            simp [Φ1, oneState]
  have hnum2 : (∫ w in box 1 L, φ (w 0) * (-(Δ φ (w 0))))
      = ∫ y in cube L, φ y * (-(Δ φ y)) := by
    simpa using (integral_box1 (L := L) (f := fun y => φ y * (-(Δ φ y))))
  have hnum3 : (∫ y in cube L, φ y * (-(Δ φ y))) = ∫ x : ℝ³, φ x * (-(Δ φ x)) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hx0 : x ∉ interior (cube L) := by
      intro hi; exact hx (interior_subset hi)
    have hx2 : x ∉ tsupport φ := by
      intro ht; exact hx0 (hφts ht)
    have hφx0 : φ x = 0 := image_eq_zero_of_notMem_tsupport (f := φ) hx2
    simp [hφx0]
  calc
    |psNum 1 L v (oneState (φ := φ) hφc hφts hφnorm)|
        = |∫ x : ℝ³, φ x * (-(Δ φ x))| := by
          rw [hnum1, hnum2, hnum3]
    _ ≤ ∫ x : ℝ³, |φ x * (-(Δ φ x))| := by
          simpa using (abs_integral_le_integral_abs (f := fun x : ℝ³ => φ x * (-(Δ φ x))))
    _ = ∫ x : ℝ³, |φ x * Δ φ x| := by
          apply integral_congr_ae
          filter_upwards with x
          simp [abs_mul, abs_neg]

end BoseGases

end Submission
