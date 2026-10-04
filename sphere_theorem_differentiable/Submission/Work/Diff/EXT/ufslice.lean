import Mathlib
import Submission.Work.Diff.EXT.jets_eq_of_t_derivs_eq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Slices and iterated Fréchet derivatives

Two facts identifying partial derivatives of a smooth `w : ℝ × E → Z` with components of its
full iterated Fréchet derivative:

* `tder_eq_jet` : the `k`-th time derivative equals the `k`-th full jet evaluated on the tuple
  `((1,0), …, (1,0))` (time slots last);
* `sjet_apply` : the `m`-th partial jet in the space variable is the full jet composed with the
  inclusion of `E` into `ℝ × E`.

They are used to bound the mixed partials of `w` by the norms of its full jets.
-/

namespace Work.Diff.EXT

open Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]

/-- Evaluation of a continuous multilinear map at a fixed tuple, as a continuous linear map. -/
noncomputable def evalCM {ι : Type*} [Fintype ι] (G : Type*) [NormedAddCommGroup G]
    [NormedSpace ℝ G] {X : ι → Type*} [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℝ (X i)]
    (u : (i : ι) → X i) : ContinuousMultilinearMap ℝ X G →L[ℝ] G :=
  ContinuousMultilinearMap.apply ℝ X G u

@[simp] lemma evalCM_apply {ι : Type*} [Fintype ι] (G : Type*) [NormedAddCommGroup G]
    [NormedSpace ℝ G] {X : ι → Type*} [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℝ (X i)]
    (u : (i : ι) → X i) (T : ContinuousMultilinearMap ℝ X G) : evalCM G u T = T u := rfl

/-- The tuple `((1,0), …, (1,0))` of `k` copies of the time vector of `ℝ × E`. -/
def oneTup (E : Type*) [NormedAddCommGroup E] (k : ℕ) : Fin k → ℝ × E := fun _ => ((1 : ℝ), 0)


/-- **The time derivatives are components of the full jet.** -/
theorem tder_eq_jet {V : Set (ℝ × E)} (hV : IsOpen V) {w : ℝ × E → Z}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w V) {p : ℝ × E} (hp : p ∈ V) (k : ℕ) :
    iteratedDeriv k (fun s : ℝ => w (s, p.2)) p.1
      = (iteratedFDeriv ℝ k w p) (oneTup E k) := by
  suffices H : ∀ q : ℝ × E, q ∈ V → iteratedDeriv k (fun s : ℝ => w (s, q.2)) q.1
      = (iteratedFDeriv ℝ k w q) (oneTup E k) from H p hp
  induction k with
  | zero =>
    intro q hq
    simp
  | succ k ih =>
    intro q hq
    rw [iteratedDeriv_succ]
    have hcw : ContDiffAt ℝ (⊤ : ℕ∞) w q := hw.contDiffAt (hV.mem_nhds hq)
    have hmem : ∀ᶠ s in 𝓝 q.1, (s, q.2) ∈ V :=
      (hV.preimage (continuous_id.prodMk continuous_const)).mem_nhds hq
    have hev : (fun s : ℝ => iteratedDeriv k (fun σ : ℝ => w (σ, q.2)) s)
        =ᶠ[𝓝 q.1] (fun s : ℝ => (iteratedFDeriv ℝ k w (s, q.2)) (oneTup E k)) :=
      hmem.mono fun s hs => ih (s, q.2) hs
    rw [hev.deriv_eq]
    -- the derivative of the sliced jet
    have hjet : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℝ × E => iteratedFDeriv ℝ k w z) q :=
      hcw.iteratedFDeriv_right (by simp)
    have hdiff : DifferentiableAt ℝ (fun z : ℝ × E =>
        (iteratedFDeriv ℝ k w z) (oneTup E k)) q :=
      (hjet.continuousLinearMap_comp (evalCM Z (oneTup E k))).differentiableAt (by simp)
    have hchain : fderiv ℝ (fun z : ℝ × E => (iteratedFDeriv ℝ k w z) (oneTup E k)) q
        = (evalCM Z (oneTup E k)).comp
            (fderiv ℝ (fun z : ℝ × E => iteratedFDeriv ℝ k w z) q) := by
      have := (ContinuousLinearMap.hasFDerivAt (evalCM Z (oneTup E k))).comp q
        ((hjet.differentiableAt (by simp)).hasFDerivAt)
      exact this.fderiv
    rw [show deriv (fun s : ℝ => (iteratedFDeriv ℝ k w (s, q.2)) (oneTup E k)) q.1
        = fderiv ℝ (fun z : ℝ × E => (iteratedFDeriv ℝ k w z) (oneTup E k)) q (1, 0) from
      (jets_eq_fderiv_fst_apply _ hdiff).symm, hchain]
    simp only [ContinuousLinearMap.comp_apply, evalCM_apply]
    rw [iteratedFDeriv_succ_apply_left]
    change ((fderiv ℝ (iteratedFDeriv ℝ k w) q) (1, 0)) (oneTup E k)
      = ((fderiv ℝ (iteratedFDeriv ℝ k w) q) (1, 0)) (Fin.tail (oneTup E (k + 1)))
    congr 1


/-- The partial jet of `w` in the space variable, as a component of the full jet. -/
theorem sjet_apply {V : Set (ℝ × E)} (hV : IsOpen V) {w : ℝ × E → Z}
    (hw : ContDiffOn ℝ (⊤ : ℕ∞) w V) {p : ℝ × E} (hp : p ∈ V) (m : ℕ) (v : Fin m → E) :
    (iteratedFDeriv ℝ m (fun y' : E => w (p.1, y')) p.2) v
      = (iteratedFDeriv ℝ m w p) (fun i => ((0 : ℝ), v i)) := by
  have aux : ∀ m : ℕ, ∀ q : ℝ × E, q ∈ V → ∀ v : Fin m → E,
      (iteratedFDeriv ℝ m (fun y' : E => w (q.1, y')) q.2) v
        = (iteratedFDeriv ℝ m w q) (fun i => ((0 : ℝ), v i)) := by
    intro m
    induction m with
    | zero =>
      intro q hq v
      simp
    | succ m ih =>
      intro q hq v
      have hcw : ContDiffAt ℝ (⊤ : ℕ∞) w q := hw.contDiffAt (hV.mem_nhds hq)
      have hjet : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℝ × E => iteratedFDeriv ℝ m w z) q :=
        hcw.iteratedFDeriv_right (by simp)
      set CL : ContinuousMultilinearMap ℝ (fun _ : Fin m => ℝ × E) Z →L[ℝ]
          ContinuousMultilinearMap ℝ (fun _ : Fin m => E) Z :=
        ContinuousMultilinearMap.compContinuousLinearMapL
          (fun _ : Fin m => ContinuousLinearMap.inr ℝ ℝ E) with hCL
      have hCL_apply : ∀ (T : ContinuousMultilinearMap ℝ (fun _ : Fin m => ℝ × E) Z)
          (u : Fin m → E), CL T u = T (fun i => ((0 : ℝ), u i)) := by
        intro T u
        rw [hCL]
        exact ContinuousMultilinearMap.compContinuousLinearMap_apply T
          (fun _ => ContinuousLinearMap.inr ℝ ℝ E) u
      have hslice_eq : (fun y' : E => iteratedFDeriv ℝ m (fun y'' : E => w (q.1, y'')) y')
          =ᶠ[𝓝 q.2] (fun y' : E => CL (iteratedFDeriv ℝ m w (q.1, y'))) := by
        have hmem : ∀ᶠ y' in 𝓝 q.2, (q.1, y') ∈ V :=
          (hV.preimage (continuous_const.prodMk continuous_id)).mem_nhds hq
        filter_upwards [hmem] with y' hy'
        ext u
        rw [hCL_apply]
        exact ih (q.1, y') hy' u
      have hslice_diff : DifferentiableAt ℝ (fun y' : E => iteratedFDeriv ℝ m w (q.1, y')) q.2 :=
        (hjet.differentiableAt (by simp)).comp q.2
          (hasFDerivAt_prodMk_right (𝕜 := ℝ) q.1 q.2).differentiableAt
      have hfdslice : fderiv ℝ (fun y' : E => iteratedFDeriv ℝ m w (q.1, y')) q.2
          = (fderiv ℝ (fun z : ℝ × E => iteratedFDeriv ℝ m w z) q).comp
              (ContinuousLinearMap.inr ℝ ℝ E) :=
        jets_eq_slice_snd_fderiv (fun z : ℝ × E => iteratedFDeriv ℝ m w z)
          (hjet.differentiableAt (by simp))
      have hfd : fderiv ℝ (fun y' : E => iteratedFDeriv ℝ m (fun y'' : E => w (q.1, y'')) y') q.2
          = CL.comp (fderiv ℝ (fun y' : E => iteratedFDeriv ℝ m w (q.1, y')) q.2) := by
        rw [hslice_eq.fderiv_eq]
        exact ((ContinuousLinearMap.hasFDerivAt CL).comp q.2
          hslice_diff.hasFDerivAt).fderiv
      rw [iteratedFDeriv_succ_apply_left, iteratedFDeriv_succ_apply_left, hfd]
      simp only [ContinuousLinearMap.comp_apply]
      rw [hCL_apply, hfdslice]
      have htail : (Fin.tail (fun i : Fin (m + 1) => ((0 : ℝ), v i)))
          = (fun i : Fin m => ((0 : ℝ), v i.succ)) := by
        funext i
        simp [Fin.tail]
      rw [htail]
      rfl
  exact aux m p hp v


end Work.Diff.EXT
