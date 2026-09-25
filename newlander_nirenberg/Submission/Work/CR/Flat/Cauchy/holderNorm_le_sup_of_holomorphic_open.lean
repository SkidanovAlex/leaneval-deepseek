import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Cauchy
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comm
import Submission.Work.CR.Flat.Cauchy.exists_dbar_solution_polydisc
import Submission.Work.CR.Flat.Cauchy.fderiv_eq_dzC_add_dbarC
import Submission.Work.CR.Flat.Holder.holderNorm_le_wirtinger_coord

noncomputable section

open scoped NNReal ENNReal Topology
open Filter Metric
open Set MeasureTheory

namespace Work.CR.Flat.Cauchy

open Work.CR.Flat
open Work.CR.Flat (polydisc mem_polydisc polydisc_mono dbarCoord dCoord slice)
open Work.CR.Flat.Holder

/-! ## Complex differentiability from the vanishing of `∂̄` -/

/-- If `f : ℂ → ℂ` is real-differentiable at `z` and `∂̄f z = 0`, then `f` is complex
differentiable at `z`. -/
lemma differentiableAt_complex_of_dbarC {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (h : Work.CR.Flat.dbarC f z = 0) : DifferentiableAt ℂ f z := by
  rw [differentiableAt_iff_restrictScalars ℝ hf]
  refine ⟨ContinuousLinearMap.toSpanSingleton ℂ (Work.CR.Flat.dzC f z), ?_⟩
  ext v
  change (ContinuousLinearMap.toSpanSingleton ℂ (Work.CR.Flat.dzC f z)) v = (fderiv ℝ f z) v
  rw [ContinuousLinearMap.toSpanSingleton_apply]
  have hh := fderiv_eq_dzC_add_dbarC f z v hf
  rw [h, zero_mul, add_zero] at hh
  rw [hh, smul_eq_mul]; ring


/-! ## Mixed commutation of the flat Wirtinger operators -/

/-- The continuous linear map `L ↦ (1/2)(L e_j - i·L(i·e_j))`; composing with `fderiv ℝ u`
gives `dCoord j u`. -/
noncomputable def dCoordPhi {n : ℕ} (j : Fin n) : ((Fin n → ℂ) →L[ℝ] ℂ) →L[ℝ] ℂ :=
  (ContinuousLinearMap.mul ℝ ℂ (1/2 : ℂ)).comp
    (ContinuousLinearMap.apply ℝ ℂ (Pi.single j 1)
      - (ContinuousLinearMap.mul ℝ ℂ Complex.I).comp
          (ContinuousLinearMap.apply ℝ ℂ (Pi.single j Complex.I)))

lemma dCoord_eq_comp {n : ℕ} (j : Fin n) (u : (Fin n → ℂ) → ℂ) :
    dCoord j u = dCoordPhi j ∘ (fderiv ℝ u) := by
  funext x
  simp only [dCoordPhi, Function.comp_apply, sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, dCoord, ContinuousLinearMap.mul_apply']

/-- The derivative of `dCoord j u` at `z`, in terms of the second derivative of `u`. -/
lemma fderiv_dCoord {n : ℕ} (j : Fin n) (u : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hu : ContDiffAt ℝ 2 u z) (v : Fin n → ℂ) :
    fderiv ℝ (dCoord j u) z v
      = (1/2 : ℂ) * (((fderiv ℝ (fderiv ℝ u) z) v) (Pi.single j 1)
          - Complex.I * (((fderiv ℝ (fderiv ℝ u) z) v) (Pi.single j Complex.I))) := by
  have hdu : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [dCoord_eq_comp j u, fderiv_comp z (dCoordPhi j).differentiableAt hdu,
    ContinuousLinearMap.fderiv]
  simp only [dCoordPhi, ContinuousLinearMap.comp_apply, sub_apply,
    ContinuousLinearMap.apply_apply, ContinuousLinearMap.mul_apply']

/-- Mixed commutation: `∂̄_k ∂_j u = ∂_j ∂̄_k u` for `u` twice real-differentiable. -/
theorem dbarCoord_dCoord_comm {n : ℕ} (j k : Fin n) (u : (Fin n → ℂ) → ℂ) (z : Fin n → ℂ)
    (hu : ContDiffAt ℝ 2 u z) :
    dbarCoord k (dCoord j u) z = dCoord j (dbarCoord k u) z := by
  have hsymm : ∀ a b : Fin n → ℂ,
      ((fderiv ℝ (fderiv ℝ u) z) a) b = ((fderiv ℝ (fderiv ℝ u) z) b) a :=
    fun a b => (hu.isSymmSndFDerivAt (by simp)).eq a b
  change (1/2 : ℂ) * (fderiv ℝ (dCoord j u) z (Pi.single k 1)
        + Complex.I * fderiv ℝ (dCoord j u) z (Pi.single k Complex.I))
      = (1/2 : ℂ) * (fderiv ℝ (dbarCoord k u) z (Pi.single j 1)
        - Complex.I * fderiv ℝ (dbarCoord k u) z (Pi.single j Complex.I))
  rw [fderiv_dCoord j u z hu (Pi.single k 1),
      fderiv_dCoord j u z hu (Pi.single k Complex.I),
      Work.CR.Flat.Polydisc.fderiv_dbarCoord k u z hu (Pi.single j 1),
      Work.CR.Flat.Polydisc.fderiv_dbarCoord k u z hu (Pi.single j Complex.I),
      hsymm (Pi.single k 1) (Pi.single j 1),
      hsymm (Pi.single k 1) (Pi.single j Complex.I),
      hsymm (Pi.single k Complex.I) (Pi.single j 1),
      hsymm (Pi.single k Complex.I) (Pi.single j Complex.I)]
  ring

/-! ## The slice of a function of several variables -/

/-- The `j`-th slice map `t ↦ Function.update y j t` is affine with derivative `Pi.single j`. -/
lemma hasFDerivAt_update {n : ℕ} (j : Fin n) (y : Fin n → ℂ) (w : ℂ) :
    HasFDerivAt (fun t : ℂ => Function.update y j t)
      (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j) w := by
  have hfun : (fun t : ℂ => Function.update y j t)
      = fun t : ℂ => Function.update y j 0
          + (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j) t := by
    funext t
    rw [ContinuousLinearMap.single_apply]
    ext i
    by_cases h : i = j <;> simp [h]
  rw [hfun]
  exact (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j)
    (x := w)).const_add (Function.update y j 0)

/-- The real differential of the `j`-th slice at an arbitrary point. -/
lemma fderiv_slice {n : ℕ} (j : Fin n) {g : (Fin n → ℂ) → ℂ} {y : Fin n → ℂ} {w : ℂ}
    (hg : DifferentiableAt ℝ g (Function.update y j w)) :
    fderiv ℝ (fun t : ℂ => g (Function.update y j t)) w
      = (fderiv ℝ g (Function.update y j w)).comp
          (ContinuousLinearMap.single ℝ (fun _ : Fin n => ℂ) j) :=
  (hg.hasFDerivAt.comp w (hasFDerivAt_update j y w)).fderiv

/-- Real differentiability of a slice at an arbitrary point. -/
lemma differentiableAt_slice {n : ℕ} (j : Fin n) {g : (Fin n → ℂ) → ℂ} {y : Fin n → ℂ} {w : ℂ}
    (hg : DifferentiableAt ℝ g (Function.update y j w)) :
    DifferentiableAt ℝ (fun t : ℂ => g (Function.update y j t)) w :=
  (hg.hasFDerivAt.comp w (hasFDerivAt_update j y w)).differentiableAt

/-- The `(0,1)`-derivative of the `j`-th slice is the `j`-th `(0,1)`-derivative of `g`. -/
lemma dbarC_slice {n : ℕ} (j : Fin n) {g : (Fin n → ℂ) → ℂ} {y : Fin n → ℂ} {w : ℂ}
    (hg : DifferentiableAt ℝ g (Function.update y j w)) :
    Work.CR.Flat.dbarC (fun t : ℂ => g (Function.update y j t)) w
      = dbarCoord j g (Function.update y j w) :=
  dbarSolution_dbarC_update_eq_dbarCoord j hg

/-- A slice at a point where `∂̄` vanishes is complex differentiable. -/
lemma differentiableAt_complex_slice {n : ℕ} (j : Fin n) {g : (Fin n → ℂ) → ℂ} {y : Fin n → ℂ}
    {w : ℂ} (hg : DifferentiableAt ℝ g (Function.update y j w))
    (h : dbarCoord j g (Function.update y j w) = 0) :
    DifferentiableAt ℂ (fun t : ℂ => g (Function.update y j t)) w :=
  differentiableAt_complex_of_dbarC (differentiableAt_slice j hg)
    (by rw [dbarC_slice j hg]; exact h)

/-- The complex derivative of a slice is the `j`-th `(1,0)`-derivative of `g`. -/
lemma deriv_slice_eq_dCoord {n : ℕ} (j : Fin n) {g : (Fin n → ℂ) → ℂ} {y : Fin n → ℂ} {w : ℂ}
    (hg : DifferentiableAt ℝ g (Function.update y j w))
    (h : dbarCoord j g (Function.update y j w) = 0) :
    deriv (fun t : ℂ => g (Function.update y j t)) w = dCoord j g (Function.update y j w) := by
  have hcd := differentiableAt_complex_slice j hg h
  have h1 : deriv (fun t : ℂ => g (Function.update y j t)) w
      = fderiv ℝ (fun t : ℂ => g (Function.update y j t)) w 1 := by
    rw [show deriv (fun t : ℂ => g (Function.update y j t)) w
        = (fderiv ℂ (fun t : ℂ => g (Function.update y j t)) w) 1 from rfl]
    calc (fderiv ℂ (fun t : ℂ => g (Function.update y j t)) w) 1
        = ((fderiv ℂ (fun t : ℂ => g (Function.update y j t)) w).restrictScalars ℝ) 1 := rfl
      _ = (fderiv ℝ (fun t : ℂ => g (Function.update y j t)) w) 1 := by
          rw [hcd.fderiv_restrictScalars ℝ]
  rw [h1, fderiv_slice j hg]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.single_apply]
  rw [Work.CR.Flat.Holder.fderiv_single_eq g (Function.update y j w) j 1, h]
  simp

/-! ## Smoothness of the Wirtinger derivatives on an open set -/

/-- `∂_j u` is `C^K` on an open set when `u` is `C^{K+1}`. -/
lemma contDiffOn_dCoord' {n : ℕ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω) {K : ℕ}
    {u : (Fin n → ℂ) → ℂ} (hu : ContDiffOn ℝ (((K+1:ℕ)):WithTop ℕ∞) u Ω) (j : Fin n) :
    ContDiffOn ℝ ((K:ℕ):WithTop ℕ∞) (fun z => dCoord j u z) Ω := by
  have hm : ((K:ℕ):WithTop ℕ∞) + 1 ≤ (((K+1:ℕ)):WithTop ℕ∞) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
  have hfd : ContDiffOn ℝ ((K:ℕ):WithTop ℕ∞) (fun z => fderiv ℝ u z) Ω :=
    hu.fderiv_of_isOpen hΩ hm
  have h1 : ContDiffOn ℝ ((K:ℕ):WithTop ℕ∞)
      (fun z => fderiv ℝ u z (Pi.single j (1:ℂ))) Ω := by
    change ContDiffOn ℝ ((K:ℕ):WithTop ℕ∞)
      (fun z => (ContinuousLinearMap.apply ℝ ℂ (Pi.single j (1:ℂ))) (fderiv ℝ u z)) Ω
    exact (ContinuousLinearMap.apply ℝ ℂ (Pi.single j (1:ℂ))).contDiff.comp_contDiffOn hfd
  have h2 : ContDiffOn ℝ ((K:ℕ):WithTop ℕ∞)
      (fun z => fderiv ℝ u z (Pi.single j Complex.I)) Ω := by
    change ContDiffOn ℝ ((K:ℕ):WithTop ℕ∞)
      (fun z => (ContinuousLinearMap.apply ℝ ℂ (Pi.single j Complex.I)) (fderiv ℝ u z)) Ω
    exact (ContinuousLinearMap.apply ℝ ℂ (Pi.single j Complex.I)).contDiff.comp_contDiffOn hfd
  have h3 : ContDiffOn ℝ ((K:ℕ):WithTop ℕ∞)
      (fun z => Complex.I * fderiv ℝ u z (Pi.single j Complex.I)) Ω :=
    contDiffOn_const.mul h2
  have h4 : ContDiffOn ℝ ((K:ℕ):WithTop ℕ∞) (fun z => fderiv ℝ u z (Pi.single j (1:ℂ))
      - Complex.I * fderiv ℝ u z (Pi.single j Complex.I)) Ω := h1.sub h3
  have h5 : ContDiffOn ℝ ((K:ℕ):WithTop ℕ∞) (fun z => (1/2:ℂ) * (fderiv ℝ u z (Pi.single j (1:ℂ))
      - Complex.I * fderiv ℝ u z (Pi.single j Complex.I))) Ω := contDiffOn_const.mul h4
  simpa [dCoord] using h5

/-- `∂̄_j u` is `C^K` on an open set when `u` is `C^{K+1}`. -/
lemma contDiffOn_dbarCoord' {n : ℕ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω) {K : ℕ}
    {u : (Fin n → ℂ) → ℂ} (hu : ContDiffOn ℝ (((K+1:ℕ)):WithTop ℕ∞) u Ω) (j : Fin n) :
    ContDiffOn ℝ ((K:ℕ):WithTop ℕ∞) (fun z => dbarCoord j u z) Ω := by
  have hm : ((K:ℕ):WithTop ℕ∞) + 1 ≤ (((K+1:ℕ)):WithTop ℕ∞) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
  have hfd : ContDiffOn ℝ ((K:ℕ):WithTop ℕ∞) (fun z => fderiv ℝ u z) Ω :=
    hu.fderiv_of_isOpen hΩ hm
  have h1 : ContDiffOn ℝ ((K:ℕ):WithTop ℕ∞)
      (fun z => fderiv ℝ u z (Pi.single j (1:ℂ))) Ω := by
    change ContDiffOn ℝ ((K:ℕ):WithTop ℕ∞)
      (fun z => (ContinuousLinearMap.apply ℝ ℂ (Pi.single j (1:ℂ))) (fderiv ℝ u z)) Ω
    exact (ContinuousLinearMap.apply ℝ ℂ (Pi.single j (1:ℂ))).contDiff.comp_contDiffOn hfd
  have h2 : ContDiffOn ℝ ((K:ℕ):WithTop ℕ∞)
      (fun z => fderiv ℝ u z (Pi.single j Complex.I)) Ω := by
    change ContDiffOn ℝ ((K:ℕ):WithTop ℕ∞)
      (fun z => (ContinuousLinearMap.apply ℝ ℂ (Pi.single j Complex.I)) (fderiv ℝ u z)) Ω
    exact (ContinuousLinearMap.apply ℝ ℂ (Pi.single j Complex.I)).contDiff.comp_contDiffOn hfd
  have h3 : ContDiffOn ℝ ((K:ℕ):WithTop ℕ∞)
      (fun z => Complex.I * fderiv ℝ u z (Pi.single j Complex.I)) Ω :=
    contDiffOn_const.mul h2
  have h4 : ContDiffOn ℝ ((K:ℕ):WithTop ℕ∞) (fun z => fderiv ℝ u z (Pi.single j (1:ℂ))
      + Complex.I * fderiv ℝ u z (Pi.single j Complex.I)) Ω := h1.add h3
  have h5 : ContDiffOn ℝ ((K:ℕ):WithTop ℕ∞) (fun z => (1/2:ℂ) * (fderiv ℝ u z (Pi.single j (1:ℂ))
      + Complex.I * fderiv ℝ u z (Pi.single j Complex.I))) Ω := contDiffOn_const.mul h4
  simpa [dbarCoord] using h5

/-! ## Iterated Wirtinger derivatives -/

/-- The iterated `(1,0)`-coordinate derivative of `g`, indexed by a vector of coordinates:
`dcoordVec m v g z = ∂_{v 0} ∂_{v 1} … ∂_{v (m-1)} g z`. -/
def dcoordVec {n : ℕ} : (m : ℕ) → (Fin m → Fin n) → ((Fin n → ℂ) → ℂ) → ((Fin n → ℂ) → ℂ)
  | 0, _, g => g
  | m+1, v, g => fun z => dCoord (v 0) (dcoordVec m (fun i => v i.succ) g) z

@[simp] lemma dcoordVec_zero {n : ℕ} (v : Fin 0 → Fin n) (g : (Fin n → ℂ) → ℂ) :
    dcoordVec 0 v g = g := rfl

lemma dcoordVec_succ {n : ℕ} (m : ℕ) (v : Fin (m+1) → Fin n) (g : (Fin n → ℂ) → ℂ) :
    dcoordVec (m+1) v g
      = fun z => dCoord (v 0) (dcoordVec m (fun i => v i.succ) g) z := rfl

/-- `dcoordVec` preserves `C^N`-smoothness, losing one order per derivative. -/
lemma contDiffOn_dcoordVec {n : ℕ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω) (m : ℕ)
    (v : Fin m → Fin n) (N : ℕ) {g : (Fin n → ℂ) → ℂ}
    (hg : ContDiffOn ℝ (((N + m : ℕ)) : WithTop ℕ∞) g Ω) :
    ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞) (dcoordVec m v g) Ω := by
  induction m generalizing N with
  | zero => simpa using hg
  | succ m ih =>
      have hg' : ContDiffOn ℝ (((N + 1 + m : ℕ)) : WithTop ℕ∞) g Ω := by
        rw [show N + (m + 1) = N + 1 + m from by omega] at hg
        exact hg
      have h1 := ih (fun i => v i.succ) (N+1) hg'
      have h2 : ContDiffOn ℝ ((N : ℕ) : WithTop ℕ∞)
          (fun z => dCoord (v 0) (dcoordVec m (fun i => v i.succ) g) z) Ω :=
        contDiffOn_dCoord' hΩ h1 (v 0)
      rw [dcoordVec_succ]
      exact h2

/-- If `f` vanishes near `z` then its real differential vanishes at `z`. -/
lemma fderiv_eq_zero_of_eventuallyEq_zero {n : ℕ} {f : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ}
    (h : f =ᶠ[𝓝 z] 0) : fderiv ℝ f z = 0 := by
  have h1 : HasFDerivAt f (0 : (Fin n → ℂ) →L[ℝ] ℂ) z :=
    (hasFDerivAt_const (0 : ℂ) z).congr_of_eventuallyEq h
  simpa using h1.fderiv

lemma dCoord_eq_zero_of_eventuallyEq_zero {n : ℕ} (j : Fin n) {f : (Fin n → ℂ) → ℂ}
    {z : Fin n → ℂ} (h : f =ᶠ[𝓝 z] 0) : dCoord j f z = 0 := by
  rw [dCoord, fderiv_eq_zero_of_eventuallyEq_zero h]
  simp

lemma dbarCoord_eq_zero_of_eventuallyEq_zero {n : ℕ} (j : Fin n) {f : (Fin n → ℂ) → ℂ}
    {z : Fin n → ℂ} (h : f =ᶠ[𝓝 z] 0) : dbarCoord j f z = 0 := by
  rw [dbarCoord, fderiv_eq_zero_of_eventuallyEq_zero h]
  simp

/-- If `h` is holomorphic and `C^κ` on the open set `Ω`, then every iterated
`(1,0)`-derivative `dcoordVec m v h` with `m + 1 ≤ κ` is again holomorphic on `Ω`. -/
lemma dbarCoord_dcoordVec_eq_zero {n : ℕ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω) {κ : ℕ}
    {h : (Fin n → ℂ) → ℂ} (hh : ∀ j z, z ∈ Ω → dbarCoord j h z = 0)
    (hsmooth : ContDiffOn ℝ ((κ : ℕ) : WithTop ℕ∞) h Ω) :
    ∀ (m : ℕ) (v : Fin m → Fin n) (j : Fin n) (z : Fin n → ℂ), z ∈ Ω → m + 1 ≤ κ →
      dbarCoord j (dcoordVec m v h) z = 0 := by
  intro m
  induction m with
  | zero => intro v j z hz _; simpa using hh j z hz
  | succ m ih =>
      intro v j z hz hm
      have hm' : m + 1 ≤ κ := by omega
      have hsmooth2 : ContDiffOn ℝ ((2 + m : ℕ) : WithTop ℕ∞) h Ω :=
        hsmooth.of_le (by exact_mod_cast (by omega : 2 + m ≤ κ))
      have hg : ContDiffOn ℝ (2 : WithTop ℕ∞) (dcoordVec m (fun i => v i.succ) h) Ω :=
        contDiffOn_dcoordVec hΩ m (fun i => v i.succ) 2 hsmooth2
      have hgAt : ContDiffAt ℝ 2 (dcoordVec m (fun i => v i.succ) h) z :=
        hg.contDiffAt (hΩ.mem_nhds hz)
      have hinner : ∀ j' y, y ∈ Ω → dbarCoord j' (dcoordVec m (fun i => v i.succ) h) y = 0 :=
        fun j' y hy => ih (fun i => v i.succ) j' y hy hm'
      rw [dcoordVec_succ]
      show dbarCoord j (dCoord (v 0) (dcoordVec m (fun i => v i.succ) h)) z = 0
      rw [dbarCoord_dCoord_comm (v 0) j _ z hgAt]
      exact dCoord_eq_zero_of_eventuallyEq_zero (v 0)
        (by filter_upwards [hΩ.mem_nhds hz] with y hy; exact hinner j y hy)

/-! ## Nested interpolating polydiscs -/

/-- The multi-radius obtained by linear interpolation between `ρi` and `ρo`: at `m = 0` it is
`ρo`, at `m = N` it is `ρi`. -/
noncomputable def interpR {n : ℕ} (ρi ρo : Fin n → ℝ) (N m : ℕ) : Fin n → ℝ :=
  fun j => ρi j + (ρo j - ρi j) * (1 - (m : ℝ) / (N : ℝ))

@[simp] lemma interpR_zero {n : ℕ} (ρi ρo : Fin n → ℝ) (N : ℕ) :
    interpR ρi ρo N 0 = ρo := by
  funext j
  simp only [interpR, Nat.cast_zero, zero_div, sub_zero, mul_one]
  ring

lemma interpR_self {n : ℕ} {ρi ρo : Fin n → ℝ} {N : ℕ} (hN : (N:ℝ) ≠ 0) :
    interpR ρi ρo N N = ρi := by
  funext j
  simp only [interpR, div_self hN, sub_self, mul_zero, add_zero]

lemma interpR_diff {n : ℕ} (ρi ρo : Fin n → ℝ) (N m : ℕ) (j : Fin n) :
    interpR ρi ρo N m j - interpR ρi ρo N (m+1) j
      = (ρo j - ρi j) * (1 / (N:ℝ)) := by
  simp only [interpR]
  push_cast
  ring

lemma interpR_le {n : ℕ} {ρi ρo : Fin n → ℝ} (hmono : ∀ j, ρi j < ρo j) (N m : ℕ) (j : Fin n) :
    interpR ρi ρo N m j ≤ ρo j := by
  simp only [interpR]
  have h1 : (0:ℝ) ≤ (m:ℝ)/(N:ℝ) := by positivity
  have h2 : (0:ℝ) < ρo j - ρi j := by linarith [hmono j]
  nlinarith [mul_nonneg (le_of_lt h2) h1]

lemma interpR_anti {n : ℕ} {ρi ρo : Fin n → ℝ} (hmono : ∀ j, ρi j < ρo j) (N m : ℕ) :
    interpR ρi ρo N (m+1) ≤ interpR ρi ρo N m := by
  intro j
  have h2 : (0:ℝ) < ρo j - ρi j := by linarith [hmono j]
  have hdiff : interpR ρi ρo N m j - interpR ρi ρo N (m+1) j = (ρo j - ρi j) * (1/(N:ℝ)) :=
    interpR_diff ρi ρo N m j
  have h3 : (0:ℝ) ≤ (ρo j - ρi j) * (1/(N:ℝ)) := mul_nonneg (le_of_lt h2) (by positivity)
  linarith [hdiff, h3]

lemma interpR_mono {n : ℕ} {ρi ρo : Fin n → ℝ} (hmono : ∀ j, ρi j < ρo j) (N : ℕ) :
    ∀ {m m' : ℕ}, m ≤ m' → interpR ρi ρo N m' ≤ interpR ρi ρo N m := by
  intro m m' h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => simp
  | succ d ih =>
      rw [show m + (d + 1) = (m + d) + 1 from by omega]
      exact le_trans (interpR_anti hmono N (m+d)) ih

/-- Membership in a polydisc after slicing. -/
lemma mem_polydisc_update {n : ℕ} {c : Fin n → ℂ} {ρ : Fin n → ℝ} {z : Fin n → ℂ} {j : Fin n}
    {R : ℝ} (hzj : ‖z j - c j‖ + R < ρ j) (hzk : ∀ k, k ≠ j → ‖z k - c k‖ < ρ k)
    {w : ℂ} (hw : ‖w - z j‖ ≤ R) :
    Function.update z j w ∈ polydisc c ρ := by
  intro i
  by_cases hi : i = j
  · subst hi
    rw [Function.update_self]
    have hsplit : w - c i = (w - z i) + (z i - c i) := by ring
    calc ‖w - c i‖ = ‖(w - z i) + (z i - c i)‖ := by rw [hsplit]
      _ ≤ ‖w - z i‖ + ‖z i - c i‖ := norm_add_le _ _
      _ ≤ R + ‖z i - c i‖ := by linarith
      _ < ρ i := by linarith [hzj]
  · rw [Function.update_of_ne hi]
    exact hzk i hi

/-- **One-variable Cauchy estimate on a slice.** -/
lemma norm_dCoord_le_of_slice_bound {n : ℕ} {c : Fin n → ℂ} {ρ : Fin n → ℝ} {j : Fin n}
    {g : (Fin n → ℂ) → ℂ} {C R : ℝ} (hR : 0 < R)
    (hcd : ∀ y ∈ polydisc c ρ, DifferentiableAt ℝ g y)
    (hhol : ∀ y ∈ polydisc c ρ, dbarCoord j g y = 0)
    (hbnd : ∀ y ∈ polydisc c ρ, ‖g y‖ ≤ C)
    {z : Fin n → ℂ} (hzj : ‖z j - c j‖ + R < ρ j) (hzk : ∀ k, k ≠ j → ‖z k - c k‖ < ρ k) :
    ‖dCoord j g z‖ ≤ C / R := by
  set F : ℂ → ℂ := fun w => g (Function.update z j w) with hF
  have hz : z ∈ polydisc c ρ := by
    intro i
    by_cases hi : i = j
    · subst hi; linarith [hzj, hR]
    · exact hzk i hi
  have hderiv : deriv F (z j) = dCoord j g z := by
    rw [hF]
    have hg' : DifferentiableAt ℝ g (Function.update z j (z j)) := by
      rw [Function.update_eq_self]; exact hcd z hz
    have h' : dbarCoord j g (Function.update z j (z j)) = 0 := by
      rw [Function.update_eq_self]; exact hhol z hz
    simpa only [Function.update_eq_self] using deriv_slice_eq_dCoord j hg' h'
  have hmain : ‖deriv F (z j)‖ ≤ C / R := by
    refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := z j) (R := R) (f := F)
      (C := C) hR ?_ ?_
    · apply DifferentiableOn.diffContOnCl
      have hdcl : DifferentiableOn ℂ F (Metric.closedBall (z j) R) := by
        intro w hw
        rw [hF]
        have hmem : Function.update z j w ∈ polydisc c ρ :=
          mem_polydisc_update hzj hzk (by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hw)
        exact (differentiableAt_complex_slice j (hcd _ hmem) (hhol _ hmem)).differentiableWithinAt
      exact hdcl.mono closure_ball_subset_closedBall
    · intro w hw
      rw [hF]
      have hnorm : ‖w - z j‖ = R := by
        have := Metric.mem_sphere.mp hw
        rwa [dist_eq_norm] at this
      exact hbnd _ (mem_polydisc_update hzj hzk (le_of_eq hnorm))
  rwa [hderiv] at hmain

/-- The explicit sup-norm constant used for the iterated Wirtinger derivatives. -/
noncomputable def supC {n : ℕ} (ρi ρo : Fin n → ℝ) (k : ℕ) : ℝ :=
  (((k + 1 : ℕ)) : ℝ) * (∑ j : Fin n, 1 / (ρo j - ρi j)) + 1

lemma supC_pos {n : ℕ} {ρi ρo : Fin n → ℝ} (hmono : ∀ j, ρi j < ρo j) (k : ℕ) :
    0 < supC ρi ρo k := by
  rw [supC]
  have h : 0 ≤ ∑ j : Fin n, 1 / (ρo j - ρi j) :=
    Finset.sum_nonneg (fun j _ => le_of_lt (one_div_pos.mpr (by linarith [hmono j])))
  have h2 : (0:ℝ) ≤ (((k+1:ℕ)) : ℝ) := by positivity
  nlinarith

lemma supC_ge1 {n : ℕ} {ρi ρo : Fin n → ℝ} (hmono : ∀ j, ρi j < ρo j) (k : ℕ) :
    1 ≤ supC ρi ρo k := by
  rw [supC]
  have h : 0 ≤ ∑ j : Fin n, 1 / (ρo j - ρi j) :=
    Finset.sum_nonneg (fun j _ => le_of_lt (one_div_pos.mpr (by linarith [hmono j])))
  have h2 : (0:ℝ) ≤ (((k+1:ℕ)) : ℝ) := by positivity
  nlinarith

lemma supC_bound {n : ℕ} {ρi ρo : Fin n → ℝ} (hmono : ∀ j, ρi j < ρo j) (k : ℕ)
    (j : Fin n) : ((k+1:ℕ):ℝ) / (ρo j - ρi j) ≤ supC ρi ρo k := by
  rw [supC]
  have h1 : 1/(ρo j - ρi j) ≤ ∑ i : Fin n, 1/(ρo i - ρi i) :=
    Finset.single_le_sum (f := fun i : Fin n => 1/(ρo i - ρi i))
      (fun i _ => le_of_lt (one_div_pos.mpr (by linarith [hmono i]))) (Finset.mem_univ j)
  have h2 : ((k+1:ℕ):ℝ) * (1/(ρo j - ρi j)) ≤ ((k+1:ℕ):ℝ) * (∑ i : Fin n, 1/(ρo i - ρi i)) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  have h3 : ((k+1:ℕ):ℝ) * (1/(ρo j - ρi j)) = ((k+1:ℕ):ℝ)/(ρo j - ρi j) := by
    rw [one_div, div_eq_mul_inv]
  calc ((k+1:ℕ):ℝ) / (ρo j - ρi j) = ((k+1:ℕ):ℝ) * (1/(ρo j - ρi j)) := by rw [mul_one_div]
    _ ≤ ((k+1:ℕ):ℝ) * (∑ i : Fin n, 1/(ρo i - ρi i)) := h2
    _ ≤ ((k+1:ℕ):ℝ) * (∑ i : Fin n, 1/(ρo i - ρi i)) + 1 := le_add_of_nonneg_right zero_le_one

/-- **Sup bounds for all iterated `(1,0)`-derivatives.**  If `h` is holomorphic and bounded by `S`
on `P(ρo)` and `C^{k+1}` there, then on the inner polydisc `P(ρi)` every iterated derivative of
order `m ≤ k+1` is bounded by `Λ^{k+1} · S` for every `Λ ≥ (k+1)/(ρo j - ρi j)`, `Λ ≥ 1`. -/
theorem dcoordVec_sup_bound {n : ℕ} {c : Fin n → ℂ} {ρi ρo : Fin n → ℝ}
    (hmono : ∀ j, ρi j < ρo j) {k : ℕ} {h : (Fin n → ℂ) → ℂ} {S : ℝ} (hS : 0 ≤ S)
    {Λ : ℝ} (hΛpos : 0 < Λ) (hΛge1 : 1 ≤ Λ)
    (hΛbound : ∀ j, ((k+1:ℕ):ℝ) / (ρo j - ρi j) ≤ Λ)
    (hsmooth : ContDiffOn ℝ (((k+1 : ℕ)) : WithTop ℕ∞) h (polydisc c ρo))
    (hhol : ∀ j z, z ∈ polydisc c ρo → dbarCoord j h z = 0)
    (hbnd : ∀ z ∈ polydisc c ρo, ‖h z‖ ≤ S) :
    ∀ (m : ℕ) (v : Fin m → Fin n) (z : Fin n → ℂ),
      m ≤ k + 1 → z ∈ polydisc c ρi → ‖dcoordVec m v h z‖ ≤ Λ^(k+1) * S := by
  let N : ℕ := k + 1
  have hNpos : 0 < N := by omega
  have hNRpos : (0:ℝ) < N := by exact_mod_cast hNpos
  have hNne : (N:ℝ) ≠ 0 := ne_of_gt hNRpos
  have key : ∀ m, m ≤ k+1 → ∀ (v : Fin m → Fin n) (z : Fin n → ℂ),
      z ∈ polydisc c (interpR ρi ρo N m) → ‖dcoordVec m v h z‖ ≤ Λ^m * S := by
    intro m
    induction m with
    | zero =>
        intro _ v z hz
        rw [show interpR ρi ρo N 0 = ρo from interpR_zero ρi ρo N] at hz
        simpa using hbnd z hz
    | succ m ih =>
        intro hm v z hz
        have hmk : m ≤ k := by omega
        set g : (Fin n → ℂ) → ℂ := dcoordVec m (fun i => v i.succ) h with hgdef
        set R : ℝ := (ρo (v 0) - ρi (v 0)) * (1 / (N:ℝ)) with hRdef
        have hRpos : 0 < R := by
          rw [hRdef]
          have : (0:ℝ) < ρo (v 0) - ρi (v 0) := by linarith [hmono (v 0)]
          positivity
        have hsub : polydisc c (interpR ρi ρo N m) ⊆ polydisc c ρo :=
          polydisc_mono (interpR_le hmono N m)
        have hg_hol : ∀ y ∈ polydisc c ρo, dbarCoord (v 0) g y = 0 := by
          intro y hy
          rw [hgdef]
          exact dbarCoord_dcoordVec_eq_zero (isOpen_polydisc c ρo) (κ := k+1) hhol hsmooth
            m (fun i => v i.succ) (v 0) y hy (by omega)
        have hg_smooth : ContDiffOn ℝ (((k+1-m : ℕ)) : WithTop ℕ∞) g (polydisc c ρo) := by
          rw [hgdef]
          refine contDiffOn_dcoordVec (isOpen_polydisc c ρo) m (fun i => v i.succ) (k+1-m) ?_
          rw [show (k+1-m) + m = k+1 from by omega]
          exact hsmooth
        have hg_diff : ∀ y ∈ polydisc c ρo, DifferentiableAt ℝ g y := by
          intro y hy
          have hne : (((k+1-m : ℕ)) : WithTop ℕ∞) ≠ 0 := by
            exact_mod_cast (show (k+1-m : ℕ) ≠ 0 by omega)
          exact (hg_smooth.differentiableOn hne).differentiableAt
            ((isOpen_polydisc c ρo).mem_nhds hy)
        have hg_bnd : ∀ y ∈ polydisc c (interpR ρi ρo N m), ‖g y‖ ≤ Λ^m * S := by
          intro y hy
          rw [hgdef]
          exact ih (by omega) (fun i => v i.succ) y hy
        have hz0 : ‖z (v 0) - c (v 0)‖ < interpR ρi ρo N (m+1) (v 0) := hz (v 0)
        have hdiff : interpR ρi ρo N m (v 0) - interpR ρi ρo N (m+1) (v 0) = R := by
          rw [hRdef]; exact interpR_diff ρi ρo N m (v 0)
        have hmnt : ‖z (v 0) - c (v 0)‖ + R < interpR ρi ρo N m (v 0) := by linarith [hz0, hdiff]
        have hother : ∀ kk, kk ≠ v 0 → ‖z kk - c kk‖ < interpR ρi ρo N m kk := by
          intro kk hkk
          exact lt_of_lt_of_le (hz kk) (interpR_anti hmono N m kk)
        have hcauchy : ‖dCoord (v 0) g z‖ ≤ (Λ^m * S) / R :=
          norm_dCoord_le_of_slice_bound hRpos
            (fun y hy => hg_diff y (hsub hy))
            (fun y hy => hg_hol y (hsub hy))
            (fun y hy => hg_bnd y hy) hmnt hother
        have hstep : (Λ^m * S) / R ≤ Λ^(m+1) * S := by
          rw [hRdef, div_eq_mul_inv]
          have hinv : ((ρo (v 0) - ρi (v 0)) * (1/(N:ℝ)))⁻¹ ≤ Λ := by
            rw [mul_one_div, inv_div]
            exact hΛbound (v 0)
          calc Λ^m * S * ((ρo (v 0) - ρi (v 0)) * (1/(N:ℝ)))⁻¹
              ≤ Λ^m * S * Λ := mul_le_mul_of_nonneg_left hinv (by positivity)
            _ = Λ^(m+1) * S := by rw [pow_succ]; ring
        rw [dcoordVec_succ, ← hgdef]
        calc ‖dCoord (v 0) g z‖ ≤ (Λ^m * S) / R := hcauchy
          _ ≤ Λ^(m+1) * S := hstep
  intro m v z hm hz
  have hmN : m ≤ N := hm
  have hz' : z ∈ polydisc c (interpR ρi ρo N m) := by
    have h1 : polydisc c (interpR ρi ρo N N) = polydisc c ρi := by
      rw [interpR_self (ρi := ρi) (ρo := ρo) (N := N) hNne]
    rw [← h1] at hz
    exact polydisc_mono (interpR_mono hmono N hmN) hz
  calc ‖dcoordVec m v h z‖ ≤ Λ^m * S := key m hm v z hz'
    _ ≤ Λ^N * S := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hΛge1 hmN) hS

/-! ## The Cauchy formula for the derivative at a non-central point -/

/-- **Cauchy integral formula for the derivative at an arbitrary interior point.**  If `f` is
holomorphic on the open disc `ball c R` and continuous on its closure, then for every `w` in the
disc, `∮ (z - w)^{-2} f z = 2πi · f'(w)`. -/
lemma deriv_eq_smul_circleIntegral {R : ℝ} {c w : ℂ} {f : ℂ → ℂ}
    (hc : DiffContOnCl ℂ f (Metric.ball c R)) (hw : w ∈ Metric.ball c R) :
    (∮ z in C(c, R), (z - w) ^ (-2 : ℤ) • f z)
      = (2 * (Real.pi : ℂ) * Complex.I) • deriv f w := by
  have hR : 0 < R := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.mp hw)
  have hci : CircleIntegrable f c R :=
    (hc.continuousOn_ball.mono sphere_subset_closedBall).circleIntegrable hR.le
  have hderiv : HasDerivAt (fun t : ℂ => ∮ z in C(c, R), (z - t)⁻¹ • f z)
      (∮ z in C(c, R), (z - w) ^ (-2 : ℤ) • f z) w :=
    Complex.hasDerivAt_circleIntegral_sub_inv_smul hci (by
      rw [Metric.mem_sphere, abs_of_pos hR]
      exact ne_of_lt (Metric.mem_ball.mp hw))
  have hev : (fun t : ℂ => ∮ z in C(c, R), (z - t)⁻¹ • f z)
      =ᶠ[𝓝 w] (fun t : ℂ => (2 * (Real.pi : ℂ) * Complex.I) • f t) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hw] with t ht
    exact hc.circleIntegral_sub_inv_smul ht
  have hf2 : HasDerivAt (fun t : ℂ => (2 * (Real.pi : ℂ) * Complex.I) • f t)
      ((2 * (Real.pi : ℂ) * Complex.I) • deriv f w) w := by
    have hfd : DifferentiableAt ℂ f w := hc.differentiableAt Metric.isOpen_ball hw
    exact hfd.hasDerivAt.const_smul (2 * (Real.pi : ℂ) * Complex.I)
  rw [← hderiv.deriv, hev.deriv_eq, hf2.deriv]

/-! ## Convexity of polydiscs, slices and norm estimates -/

lemma convex_polydisc {n : ℕ} (c : Fin n → ℂ) (ρ : Fin n → ℝ) : Convex ℝ (polydisc c ρ) := by
  have h : polydisc c ρ = ⋂ j : Fin n, {z : Fin n → ℂ | z j ∈ Metric.ball (c j) (ρ j)} := by
    ext z
    simp only [mem_polydisc, Set.mem_iInter, Set.mem_setOf_eq, Metric.mem_ball, dist_eq_norm]
  rw [h]
  exact convex_iInter fun j =>
    (convex_ball (c j) (ρ j)).linear_preimage
      (ContinuousLinearMap.proj (φ := fun _ : Fin n => ℂ) j).toLinearMap

lemma dcoordVec_cons {n : ℕ} (m : ℕ) (j : Fin n) (v : Fin m → Fin n)
    (g : (Fin n → ℂ) → ℂ) :
    dcoordVec (m+1) (Fin.cons j v) g = fun z => dCoord j (dcoordVec m v g) z := by
  rw [dcoordVec_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- The slice of a holomorphic function is `DiffContOnCl` on a disc centred at `c j`. -/
lemma diffContOnCl_slice {n : ℕ} {c : Fin n → ℂ} {ρ : Fin n → ℝ} {g : (Fin n → ℂ) → ℂ}
    {j : Fin n} {z : Fin n → ℂ} {R : ℝ}
    (hcd : ∀ y ∈ polydisc c ρ, DifferentiableAt ℝ g y)
    (hhol : ∀ y ∈ polydisc c ρ, dbarCoord j g y = 0)
    (hR : R < ρ j) (hzk : ∀ k, k ≠ j → ‖z k - c k‖ < ρ k) :
    DiffContOnCl ℂ (fun t : ℂ => g (Function.update z j t)) (Metric.ball (c j) R) := by
  apply DifferentiableOn.diffContOnCl
  have hdcl : DifferentiableOn ℂ (fun t : ℂ => g (Function.update z j t))
      (Metric.closedBall (c j) R) := by
    intro w hw
    have hmem : Function.update z j w ∈ polydisc c ρ := by
      intro k
      by_cases hk : k = j
      · subst hk
        rw [Function.update_self]
        have := Metric.mem_closedBall.mp hw
        rw [dist_eq_norm] at this
        linarith
      · rw [Function.update_of_ne hk]; exact hzk k hk
    exact (differentiableAt_complex_slice j (hcd _ hmem) (hhol _ hmem)).differentiableWithinAt
  exact hdcl.mono closure_ball_subset_closedBall

/-- The Cauchy formula for the derivative, solved for the derivative. -/
lemma two_pi_I_inv_smul_circleIntegral_deriv {R : ℝ} {c w : ℂ} {f : ℂ → ℂ}
    (hc : DiffContOnCl ℂ f (Metric.ball c R)) (hw : w ∈ Metric.ball c R) :
    ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) • (∮ z in C(c, R), (z - w) ^ (-2 : ℤ) • f z)
      = deriv f w := by
  rw [deriv_eq_smul_circleIntegral hc hw, inv_smul_smul₀]
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

lemma norm_update_sub_le {n : ℕ} (j : Fin n) (x y : Fin n → ℂ) (ζ : ℂ) :
    ‖Function.update x j ζ - Function.update y j ζ‖ ≤ ‖x - y‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => ?_
  by_cases hi : i = j
  · subst hi
    simp only [Pi.sub_apply, Function.update_self, sub_self, norm_zero]
    exact norm_nonneg _
  · simp only [Pi.sub_apply, Function.update_of_ne hi]
    exact norm_le_pi_norm (x - y) i

lemma zpow_neg_two_eq (a : ℂ) : a ^ (-2 : ℤ) = ((a⁻¹)^2) := by
  rw [show (-2 : ℤ) = -((2:ℕ):ℤ) by norm_num, zpow_neg, inv_pow]
  norm_num

lemma norm_zpow_neg_two_le {a : ℂ} {g : ℝ} (hg : 0 < g) (h : g ≤ ‖a‖) :
    ‖a ^ (-2 : ℤ)‖ ≤ (g^2)⁻¹ := by
  have h1 : ‖a ^ (-2 : ℤ)‖ = (‖a‖^2)⁻¹ := by
    rw [zpow_neg_two_eq a, norm_pow, norm_inv, ← inv_pow]
  rw [h1, inv_le_inv₀ (pow_pos (lt_of_lt_of_le hg h) 2) (pow_pos hg 2)]
  exact pow_le_pow_left₀ hg.le h 2

lemma norm_zpow_neg_two_sub_le {a b : ℂ} {g : ℝ} (hg : 0 < g) (ha : g ≤ ‖a‖)
    (hb : g ≤ ‖b‖) :
    ‖a ^ (-2 : ℤ) - b ^ (-2 : ℤ)‖ ≤ 2 * ‖a - b‖ / g^3 := by
  have ha0 : a ≠ 0 := fun h => by rw [h, norm_zero] at ha; linarith
  have hb0 : b ≠ 0 := fun h => by rw [h, norm_zero] at hb; linarith
  rw [zpow_neg_two_eq a, zpow_neg_two_eq b]
  have e1 : ((a⁻¹)^2 - (b⁻¹)^2) = (a⁻¹ - b⁻¹) * (a⁻¹ + b⁻¹) := by ring
  rw [e1, norm_mul]
  have hdiff : ‖a⁻¹ - b⁻¹‖ ≤ ‖a - b‖ / g^2 := by
    have h1 : a⁻¹ - b⁻¹ = (b - a) * (a * b)⁻¹ := by
      rw [mul_inv, sub_mul,
        show b * (a⁻¹ * b⁻¹) = a⁻¹ * (b * b⁻¹) by ring,
        show a * (a⁻¹ * b⁻¹) = (a * a⁻¹) * b⁻¹ by ring,
        mul_inv_cancel₀ hb0, mul_inv_cancel₀ ha0]
      ring
    rw [h1, norm_mul, norm_inv, norm_mul, norm_sub_rev b a, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact inv_anti₀ (pow_pos hg 2) (by rw [sq]; exact mul_le_mul ha hb hg.le (norm_nonneg _))
  have hsum : ‖a⁻¹ + b⁻¹‖ ≤ 2 / g := by
    calc ‖a⁻¹ + b⁻¹‖ ≤ ‖a⁻¹‖ + ‖b⁻¹‖ := norm_add_le _ _
      _ = ‖a‖⁻¹ + ‖b‖⁻¹ := by rw [norm_inv, norm_inv]
      _ ≤ g⁻¹ + g⁻¹ := add_le_add (inv_anti₀ hg ha) (inv_anti₀ hg hb)
      _ = 2 / g := by ring
  calc ‖a⁻¹ - b⁻¹‖ * ‖a⁻¹ + b⁻¹‖
      ≤ (‖a - b‖ / g^2) * (2 / g) :=
        mul_le_mul hdiff hsum (norm_nonneg _) (by positivity)
    _ = 2 * ‖a - b‖ / g^3 := by ring

/-- Continuity of the Cauchy kernel times a slice, on a circle. -/
lemma continuousOn_zpow_mul_slice {n : ℕ} {c : Fin n → ℂ} {ρ : Fin n → ℝ}
    {g : (Fin n → ℂ) → ℂ} {j : Fin n} {z : Fin n → ℂ} {R : ℝ}
    (hg : ContinuousOn g (polydisc c ρ))
    (hR : R < ρ j) (hzk : ∀ k, k ≠ j → ‖z k - c k‖ < ρ k) (hzj : ‖z j - c j‖ < R) :
    ContinuousOn (fun ζ : ℂ => (ζ - z j) ^ (-2 : ℤ) * g (Function.update z j ζ))
      (Metric.sphere (c j) R) := by
  have hmem : ∀ ζ ∈ Metric.sphere (c j) R, Function.update z j ζ ∈ polydisc c ρ := by
    intro ζ hζ
    intro k
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self]
      have h1 : ‖ζ - c k‖ = R := by
        have := Metric.mem_sphere.mp hζ
        rwa [dist_eq_norm] at this
      rw [h1]; exact hR
    · rw [Function.update_of_ne hk]; exact hzk k hk
  have hcont_update : Continuous (fun ζ : ℂ => Function.update z j ζ) :=
    continuous_iff_continuousAt.mpr (fun ζ => (hasFDerivAt_update j z ζ).continuousAt)
  have h1 : ContinuousOn (fun ζ : ℂ => g (Function.update z j ζ)) (Metric.sphere (c j) R) :=
    hg.comp hcont_update.continuousOn hmem
  have h2 : ContinuousOn (fun ζ : ℂ => (ζ - z j) ^ (-2 : ℤ)) (Metric.sphere (c j) R) := by
    rw [show (fun ζ : ℂ => (ζ - z j) ^ (-2 : ℤ))
        = fun ζ : ℂ => ((ζ - z j)⁻¹)^2 from funext (fun ζ => zpow_neg_two_eq (ζ - z j))]
    refine ContinuousOn.pow ?_ 2
    refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) ?_
    intro ζ hζ
    have hζ' : ‖ζ - c j‖ = R := by
      have := Metric.mem_sphere.mp hζ
      rwa [dist_eq_norm] at this
    have hpos : 0 < R - ‖z j - c j‖ := by linarith
    intro hzero
    have : ‖ζ - z j‖ = 0 := by rw [hzero, norm_zero]
    have h2 : ‖ζ - c j‖ ≤ ‖ζ - z j‖ + ‖z j - c j‖ := by
      calc ‖ζ - c j‖ = ‖(ζ - z j) + (z j - c j)‖ := by congr 1; ring
        _ ≤ ‖ζ - z j‖ + ‖z j - c j‖ := norm_add_le _ _
    rw [hζ'] at h2
    linarith
  exact h2.mul h1

/-- Continuity of a slice. -/
lemma continuousOn_slice {n : ℕ} {c : Fin n → ℂ} {ρ : Fin n → ℝ} {g : (Fin n → ℂ) → ℂ}
    {j : Fin n} {z : Fin n → ℂ} {R : ℝ}
    (hg : ContinuousOn g (polydisc c ρ))
    (hR : R < ρ j) (hzk : ∀ k, k ≠ j → ‖z k - c k‖ < ρ k) :
    ContinuousOn (fun ζ : ℂ => g (Function.update z j ζ)) (Metric.sphere (c j) R) := by
  have hmem : ∀ ζ ∈ Metric.sphere (c j) R, Function.update z j ζ ∈ polydisc c ρ := by
    intro ζ hζ k
    by_cases hk : k = j
    · subst hk
      rw [Function.update_self]
      have h1 : ‖ζ - c k‖ = R := by
        have := Metric.mem_sphere.mp hζ
        rwa [dist_eq_norm] at this
      rw [h1]; exact hR
    · rw [Function.update_of_ne hk]; exact hzk k hk
  have hcont_update : Continuous (fun ζ : ℂ => Function.update z j ζ) :=
    continuous_iff_continuousAt.mpr (fun ζ => (hasFDerivAt_update j z ζ).continuousAt)
  exact hg.comp hcont_update.continuousOn hmem

/-! ## Lipschitz bounds for the iterated Wirtinger derivatives -/

/-- The explicit Lipschitz constant for the iterated Wirtinger derivatives. -/
noncomputable def lipC {n : ℕ} (ρi ρo : Fin n → ℝ) (k : ℕ) : ℝ :=
  let ρm : Fin n → ℝ := fun j => (ρi j + ρo j) / 2
  let sm : Fin n → ℝ := fun j => (ρi j + ρm j) / 2
  let Kc : ℝ := (∑ j : Fin n, |sm j * ((n:ℝ) / (sm j - ρi j)^2
      + 2 / (sm j - ρi j)^3)|) + 1
  |max ((n:ℝ) * (supC ρi ρo k)^(k+1)) ((supC ρm ρo k)^(k+1) * Kc)| + 1

lemma lipC_pos {n : ℕ} (ρi ρo : Fin n → ℝ) (k : ℕ) : 0 < lipC ρi ρo k := by
  rw [lipC]; positivity

theorem dcoordVec_lipschitz {n : ℕ} {c : Fin n → ℂ} {ρi ρo : Fin n → ℝ}
    (hmono : ∀ j, ρi j < ρo j) {k : ℕ} {h : (Fin n → ℂ) → ℂ} {S : ℝ} (hS : 0 ≤ S)
    (hsmooth : ContDiffOn ℝ (((k+1 : ℕ)) : WithTop ℕ∞) h (polydisc c ρo))
    (hhol : ∀ j z, z ∈ polydisc c ρo → dbarCoord j h z = 0)
    (hbnd : ∀ z ∈ polydisc c ρo, ‖h z‖ ≤ S) :
    ∀ (m : ℕ) (v : Fin m → Fin n) (x : Fin n → ℂ) (y : Fin n → ℂ),
      m ≤ k + 1 → x ∈ polydisc c ρi → y ∈ polydisc c ρi →
      ‖dcoordVec m v h x - dcoordVec m v h y‖ ≤ lipC ρi ρo k * S * ‖x - y‖ := by
  have hM0 : ∀ m v z, m ≤ k+1 → z ∈ polydisc c ρi →
      ‖dcoordVec m v h z‖ ≤ ((supC ρi ρo k)^(k+1)) * S :=
    dcoordVec_sup_bound hmono hS (supC_pos hmono k) (supC_ge1 hmono k) (supC_bound hmono k)
      hsmooth hhol hbnd
  set ρm : Fin n → ℝ := fun j => (ρi j + ρo j)/2 with hρm
  have hmono_m : ∀ j, ρm j < ρo j := by intro j; rw [hρm]; linarith [hmono j]
  have hρm_gt : ∀ j, ρi j < ρm j := by intro j; rw [hρm]; linarith [hmono j]
  have hM1 : ∀ m v z, m ≤ k+1 → z ∈ polydisc c ρm →
      ‖dcoordVec m v h z‖ ≤ ((supC ρm ρo k)^(k+1)) * S :=
    dcoordVec_sup_bound hmono_m hS (supC_pos hmono_m k) (supC_ge1 hmono_m k)
      (supC_bound hmono_m k) hsmooth hhol hbnd
  have hM0nn : (0:ℝ) ≤ ((supC ρi ρo k)^(k+1)) := pow_nonneg (supC_pos hmono k).le (k+1)
  have hM1nn : (0:ℝ) ≤ ((supC ρm ρo k)^(k+1)) := pow_nonneg (supC_pos hmono_m k).le (k+1)
  set sm : Fin n → ℝ := fun j => (ρi j + ρm j)/2 with hsm
  have hsm_gt : ∀ j, ρi j < sm j := by intro j; rw [hsm]; linarith [hρm_gt j]
  have hsm_lt : ∀ j, sm j < ρm j := by intro j; rw [hsm]; linarith [hρm_gt j]
  have hgap : ∀ j, 0 < sm j - ρi j := fun j => by linarith [hsm_gt j]
  set Kc : ℝ := (∑ j : Fin n, |sm j * ((n:ℝ) / (sm j - ρi j)^2 + 2 / (sm j - ρi j)^3)|) + 1 with hKc
  have hKc_ge : ∀ j : Fin n, sm j * ((n:ℝ) / (sm j - ρi j)^2 + 2 / (sm j - ρi j)^3) ≤ Kc := by
    intro j
    have hsum : |sm j * ((n:ℝ) / (sm j - ρi j)^2 + 2 / (sm j - ρi j)^3)|
        ≤ ∑ i : Fin n, |sm i * ((n:ℝ) / (sm i - ρi i)^2 + 2 / (sm i - ρi i)^3)| :=
      Finset.single_le_sum (f := fun i : Fin n => |sm i * ((n:ℝ) / (sm i - ρi i)^2 + 2 / (sm i - ρi i)^3)|) (fun i _ => abs_nonneg _) (Finset.mem_univ j)
    calc sm j * ((n:ℝ) / (sm j - ρi j)^2 + 2 / (sm j - ρi j)^3)
        ≤ |sm j * ((n:ℝ) / (sm j - ρi j)^2 + 2 / (sm j - ρi j)^3)| := le_abs_self _
      _ ≤ ∑ i : Fin n, |sm i * ((n:ℝ) / (sm i - ρi i)^2 + 2 / (sm i - ρi i)^3)| := hsum
      _ ≤ Kc := by rw [hKc]; linarith
  intro m v x y hm hx hy
  -- easy case m ≤ k
  have easy : m ≤ k → ‖dcoordVec m v h x - dcoordVec m v h y‖
      ≤ ((n:ℝ) * ((supC ρi ρo k)^(k+1))) * S * ‖x - y‖ := by
    intro hmk
    have hg_smooth : ContDiffOn ℝ (((k+1-m : ℕ)):WithTop ℕ∞) (dcoordVec m v h) (polydisc c ρo) := by
      refine contDiffOn_dcoordVec (isOpen_polydisc c ρo) m v (k+1-m) ?_
      rw [show (k+1-m) + m = k+1 from by omega]
      exact hsmooth
    have hne : (((k+1-m : ℕ)) : WithTop ℕ∞) ≠ 0 := by
      exact_mod_cast (show (k+1-m : ℕ) ≠ 0 by omega)
    have hg_diff_o : ∀ z ∈ polydisc c ρo, DifferentiableAt ℝ (dcoordVec m v h) z :=
      fun z hz => (hg_smooth.differentiableOn hne).differentiableAt ((isOpen_polydisc c ρo).mem_nhds hz)
    have hsub : polydisc c ρi ⊆ polydisc c ρo := polydisc_mono (fun j => le_of_lt (hmono j))
    have hg_diff : ∀ z ∈ polydisc c ρi, DifferentiableAt ℝ (dcoordVec m v h) z :=
      fun z hz => hg_diff_o z (hsub hz)
    have hnorm : ∀ z ∈ polydisc c ρi, ‖fderiv ℝ (dcoordVec m v h) z‖ ≤ (n:ℝ) * ((supC ρi ρo k)^(k+1)) * S := by
      intro z hz
      have hzρo : z ∈ polydisc c ρo := hsub hz
      rw [Work.CR.Flat.Holder.fderiv_eq_sum_PhiN_PsiN]
      have hzero : ∀ j' : Fin n, dbarCoord j' (dcoordVec m v h) z = 0 := fun j' =>
        dbarCoord_dcoordVec_eq_zero (isOpen_polydisc c ρo) (κ := k+1) hhol hsmooth m v j' z hzρo (by omega)
      simp only [hzero, map_zero, add_zero]
      calc ‖∑ j' : Fin n, Work.CR.Flat.Holder.PhiN j' (dCoord j' (dcoordVec m v h) z)‖
          ≤ ∑ j' : Fin n, ‖Work.CR.Flat.Holder.PhiN j' (dCoord j' (dcoordVec m v h) z)‖ :=
            norm_sum_le _ _
        _ ≤ ∑ j' : Fin n, (1:ℝ) * ‖dCoord j' (dcoordVec m v h) z‖ := by
            refine Finset.sum_le_sum fun j' _ => ?_
            calc ‖Work.CR.Flat.Holder.PhiN j' (dCoord j' (dcoordVec m v h) z)‖
                ≤ ‖Work.CR.Flat.Holder.PhiN j'‖ * ‖dCoord j' (dcoordVec m v h) z‖ :=
                  ContinuousLinearMap.le_opNorm _ _
              _ ≤ 1 * ‖dCoord j' (dcoordVec m v h) z‖ :=
                  mul_le_mul_of_nonneg_right (Work.CR.Flat.Holder.norm_PhiN_le j') (norm_nonneg _)
        _ = ∑ j' : Fin n, ‖dcoordVec (m+1) (Fin.cons j' v) h z‖ := by
            refine Finset.sum_congr rfl fun j' _ => ?_
            rw [one_mul, dcoordVec_cons m j' v h]
        _ ≤ ∑ j' : Fin n, ((supC ρi ρo k)^(k+1)) * S :=
            Finset.sum_le_sum fun j' _ => hM0 (m+1) (Fin.cons j' v) z (by omega) hz
        _ = (n:ℝ) * (((supC ρi ρo k)^(k+1)) * S) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = (n:ℝ) * ((supC ρi ρo k)^(k+1)) * S := by ring
    exact Convex.norm_image_sub_le_of_norm_fderiv_le hg_diff hnorm (convex_polydisc c ρi) hy hx
  rcases lt_or_eq_of_le (by omega : m ≤ k+1) with hmk | hmk
  · -- m ≤ k
    calc ‖dcoordVec m v h x - dcoordVec m v h y‖ ≤ ((n:ℝ) * ((supC ρi ρo k)^(k+1))) * S * ‖x - y‖ := easy (by omega)
      _ ≤ (max ((n:ℝ) * ((supC ρi ρo k)^(k+1))) (((supC ρm ρo k)^(k+1)) * Kc) + 1) * S * ‖x - y‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hS) (norm_nonneg _)
          exact (le_trans (le_max_left _ _) (le_add_of_nonneg_right zero_le_one))
      _ ≤ lipC ρi ρo k * S * ‖x - y‖ := by
          have h2 : lipC ρi ρo k
              = |max ((n:ℝ) * (supC ρi ρo k)^(k+1)) ((supC ρm ρo k)^(k+1) * Kc)| + 1 := by
            simp only [lipC, hρm, hsm, hKc]
          rw [h2]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith [le_abs_self (max ((n:ℝ) * (supC ρi ρo k)^(k+1))
              ((supC ρm ρo k)^(k+1) * Kc))]) hS) (norm_nonneg _)
  · -- m = k+1
    subst hmk
    set j : Fin n := v 0 with hj
    set g' : (Fin n → ℂ) → ℂ := dcoordVec k (fun i => v i.succ) h with hg'def
    have hg'_smooth : ContDiffOn ℝ (((k+1-k : ℕ)):WithTop ℕ∞) g' (polydisc c ρo) := by
      rw [hg'def]
      refine contDiffOn_dcoordVec (isOpen_polydisc c ρo) k (fun i => v i.succ) (k+1-k) ?_
      rw [show (k+1-k) + k = k+1 from by omega]
      exact hsmooth
    have hne' : (((k+1-k : ℕ)) : WithTop ℕ∞) ≠ 0 := by
      exact_mod_cast (show (k+1-k : ℕ) ≠ 0 by omega)
    have hgd : ∀ z ∈ polydisc c ρo, DifferentiableAt ℝ g' z :=
      fun z hz => (hg'_smooth.differentiableOn hne').differentiableAt ((isOpen_polydisc c ρo).mem_nhds hz)
    have hgh : ∀ j' z, z ∈ polydisc c ρo → dbarCoord j' g' z = 0 := by
      intro j' z hz
      rw [hg'def]
      exact dbarCoord_dcoordVec_eq_zero (isOpen_polydisc c ρo) (κ := k+1) hhol hsmooth
        k (fun i => v i.succ) j' z hz (by omega)
    have hgc : ContinuousOn g' (polydisc c ρo) := hg'_smooth.continuousOn
    have hρm_sub : polydisc c ρm ⊆ polydisc c ρo := polydisc_mono (fun j => le_of_lt (hmono_m j))
    have hgdm : ∀ z ∈ polydisc c ρm, DifferentiableAt ℝ g' z := fun z hz => hgd z (hρm_sub hz)
    have hnorm_m : ∀ z ∈ polydisc c ρm, ‖fderiv ℝ g' z‖ ≤ (n:ℝ) * ((supC ρm ρo k)^(k+1)) * S := by
      intro z hz
      have hzρo : z ∈ polydisc c ρo := hρm_sub hz
      rw [Work.CR.Flat.Holder.fderiv_eq_sum_PhiN_PsiN]
      have hzero : ∀ j' : Fin n, dbarCoord j' g' z = 0 := fun j' => hgh j' z hzρo
      simp only [hzero, map_zero, add_zero]
      calc ‖∑ j' : Fin n, Work.CR.Flat.Holder.PhiN j' (dCoord j' g' z)‖
          ≤ ∑ j' : Fin n, ‖Work.CR.Flat.Holder.PhiN j' (dCoord j' g' z)‖ := norm_sum_le _ _
        _ ≤ ∑ j' : Fin n, (1:ℝ) * ‖dCoord j' g' z‖ := by
            refine Finset.sum_le_sum fun j' _ => ?_
            calc ‖Work.CR.Flat.Holder.PhiN j' (dCoord j' g' z)‖
                ≤ ‖Work.CR.Flat.Holder.PhiN j'‖ * ‖dCoord j' g' z‖ :=
                  ContinuousLinearMap.le_opNorm _ _
              _ ≤ 1 * ‖dCoord j' g' z‖ := mul_le_mul_of_nonneg_right
                  (Work.CR.Flat.Holder.norm_PhiN_le j') (norm_nonneg _)
        _ = ∑ j' : Fin n, ‖dcoordVec (k+1) (Fin.cons j' (fun i => v i.succ)) h z‖ := by
            refine Finset.sum_congr rfl fun j' _ => ?_
            rw [one_mul, hg'def, dcoordVec_cons k j' (fun i => v i.succ) h]
        _ ≤ ∑ j' : Fin n, ((supC ρm ρo k)^(k+1)) * S := Finset.sum_le_sum fun j' _ => hM1 (k+1) _ z (by omega) hz
        _ = (n:ℝ) * (((supC ρm ρo k)^(k+1)) * S) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = (n:ℝ) * ((supC ρm ρo k)^(k+1)) * S := by ring
    have hglip : ∀ x' ∈ polydisc c ρm, ∀ y' ∈ polydisc c ρm,
        ‖g' x' - g' y'‖ ≤ ((n:ℝ) * ((supC ρm ρo k)^(k+1)) * S) * ‖x' - y'‖ := fun x' hx' y' hy' =>
      Convex.norm_image_sub_le_of_norm_fderiv_le hgdm hnorm_m (convex_polydisc c ρm) hy' hx'
    have hgsup : ∀ z ∈ polydisc c ρm, ‖g' z‖ ≤ ((supC ρm ρo k)^(k+1)) * S :=
      fun z hz => hM1 k (fun i => v i.succ) z (by omega) hz
    have hxρo : x ∈ polydisc c ρo := polydisc_mono (fun i => le_of_lt (hmono i)) hx
    have hyρo : y ∈ polydisc c ρo := polydisc_mono (fun i => le_of_lt (hmono i)) hy
    have hx_other : ∀ kk, kk ≠ j → ‖x kk - c kk‖ < ρo kk := fun kk _ => hxρo kk
    have hy_other : ∀ kk, kk ≠ j → ‖y kk - c kk‖ < ρo kk := fun kk _ => hyρo kk
    have hsm_lt_ρo : sm j < ρo j := lt_trans (hsm_lt j) (hmono_m j)
    have hx_norm : ‖x j - c j‖ < sm j := lt_trans (hx j) (hsm_gt j)
    have hy_norm : ‖y j - c j‖ < sm j := lt_trans (hy j) (hsm_gt j)
    have hx_ball : x j ∈ Metric.ball (c j) (sm j) := by rw [Metric.mem_ball, dist_eq_norm]; exact hx_norm
    have hy_ball : y j ∈ Metric.ball (c j) (sm j) := by rw [Metric.mem_ball, dist_eq_norm]; exact hy_norm
    have hslicex := diffContOnCl_slice (ρ := ρo) hgd (fun z hz => hgh j z hz) hsm_lt_ρo hx_other
    have hslicey := diffContOnCl_slice (ρ := ρo) hgd (fun z hz => hgh j z hz) hsm_lt_ρo hy_other
    have hderivx : dCoord j g' x = deriv (fun t : ℂ => g' (Function.update x j t)) (x j) := by
      have hg2 : DifferentiableAt ℝ g' (Function.update x j (x j)) := by
        rw [Function.update_eq_self]; exact hgd x hxρo
      have hh2 : dbarCoord j g' (Function.update x j (x j)) = 0 := by
        rw [Function.update_eq_self]; exact hgh j x hxρo
      have h1 := deriv_slice_eq_dCoord j hg2 hh2
      rw [Function.update_eq_self] at h1
      exact h1.symm
    have hderivy : dCoord j g' y = deriv (fun t : ℂ => g' (Function.update y j t)) (y j) := by
      have hg2 : DifferentiableAt ℝ g' (Function.update y j (y j)) := by
        rw [Function.update_eq_self]; exact hgd y hyρo
      have hh2 : dbarCoord j g' (Function.update y j (y j)) = 0 := by
        rw [Function.update_eq_self]; exact hgh j y hyρo
      have h1 := deriv_slice_eq_dCoord j hg2 hh2
      rw [Function.update_eq_self] at h1
      exact h1.symm
    have hreprx : dcoordVec (k+1) v h x
        = ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
            (∮ ζ in C(c j, sm j), (ζ - x j) ^ (-2 : ℤ) • (g' (Function.update x j ζ))) := by
      have h1g : dcoordVec (k+1) v h x = dCoord j g' x := by
        rw [dcoordVec_succ, ← hj, ← hg'def]
      rw [h1g, hderivx]
      exact (two_pi_I_inv_smul_circleIntegral_deriv hslicex hx_ball).symm
    have hrepry : dcoordVec (k+1) v h y
        = ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
            (∮ ζ in C(c j, sm j), (ζ - y j) ^ (-2 : ℤ) • (g' (Function.update y j ζ))) := by
      have h1g : dcoordVec (k+1) v h y = dCoord j g' y := by
        rw [dcoordVec_succ, ← hj, ← hg'def]
      rw [h1g, hderivy]
      exact (two_pi_I_inv_smul_circleIntegral_deriv hslicey hy_ball).symm
    have hmemx : ∀ ζ ∈ Metric.sphere (c j) (sm j), Function.update x j ζ ∈ polydisc c ρm := by
      intro ζ hζ i
      by_cases hi : i = j
      · rw [hi, Function.update_self]
        have h1 : ‖ζ - c j‖ = sm j := by
          have := Metric.mem_sphere.mp hζ; rwa [dist_eq_norm] at this
        rw [h1]; exact hsm_lt j
      · rw [Function.update_of_ne hi]
        exact lt_of_lt_of_le (hx i) (le_of_lt (hρm_gt i))
    have hmemy : ∀ ζ ∈ Metric.sphere (c j) (sm j), Function.update y j ζ ∈ polydisc c ρm := by
      intro ζ hζ i
      by_cases hi : i = j
      · rw [hi, Function.update_self]
        have h1 : ‖ζ - c j‖ = sm j := by
          have := Metric.mem_sphere.mp hζ; rwa [dist_eq_norm] at this
        rw [h1]; exact hsm_lt j
      · rw [Function.update_of_ne hi]
        exact lt_of_lt_of_le (hy i) (le_of_lt (hρm_gt i))
    have hbound : ∀ ζ ∈ Metric.sphere (c j) (sm j),
        ‖(ζ - x j) ^ (-2 : ℤ) • g' (Function.update x j ζ)
          - (ζ - y j) ^ (-2 : ℤ) • g' (Function.update y j ζ)‖
        ≤ (((supC ρm ρo k)^(k+1)) * S * ((n:ℝ) / (sm j - ρi j)^2 + 2 / (sm j - ρi j)^3)) * ‖x - y‖ := by
      intro ζ hζ
      have hζ' : ‖ζ - c j‖ = sm j := by
        have := Metric.mem_sphere.mp hζ; rwa [dist_eq_norm] at this
      have hxa : sm j - ρi j ≤ ‖ζ - x j‖ := by
        have h1 : ‖ζ - c j‖ ≤ ‖ζ - x j‖ + ‖x j - c j‖ := by
          calc ‖ζ - c j‖ = ‖(ζ - x j) + (x j - c j)‖ := by congr 1; ring
            _ ≤ _ := norm_add_le _ _
        rw [hζ'] at h1; linarith [hx j]
      have hya : sm j - ρi j ≤ ‖ζ - y j‖ := by
        have h1 : ‖ζ - c j‖ ≤ ‖ζ - y j‖ + ‖y j - c j‖ := by
          calc ‖ζ - c j‖ = ‖(ζ - y j) + (y j - c j)‖ := by congr 1; ring
            _ ≤ _ := norm_add_le _ _
        rw [hζ'] at h1; linarith [hy j]
      have hgapj := hgap j
      have e1 : (ζ - x j) ^ (-2 : ℤ) • g' (Function.update x j ζ)
          - (ζ - y j) ^ (-2 : ℤ) • g' (Function.update y j ζ)
          = (ζ - x j) ^ (-2 : ℤ) * (g' (Function.update x j ζ) - g' (Function.update y j ζ))
            + ((ζ - x j) ^ (-2 : ℤ) - (ζ - y j) ^ (-2 : ℤ)) * g' (Function.update y j ζ) := by
        rw [sub_mul, mul_sub]; ring
      rw [e1]
      have hA : ‖(ζ - x j) ^ (-2 : ℤ) * (g' (Function.update x j ζ) - g' (Function.update y j ζ))‖
          ≤ ((sm j - ρi j)^2)⁻¹ * ((n:ℝ) * ((supC ρm ρo k)^(k+1)) * S * ‖x - y‖) := by
        rw [norm_mul]
        refine mul_le_mul (norm_zpow_neg_two_le hgapj hxa) ?_ (norm_nonneg _) (by positivity)
        calc ‖g' (Function.update x j ζ) - g' (Function.update y j ζ)‖
            ≤ (n:ℝ) * ((supC ρm ρo k)^(k+1)) * S * ‖Function.update x j ζ - Function.update y j ζ‖ :=
              hglip _ (hmemx ζ hζ) _ (hmemy ζ hζ)
          _ ≤ (n:ℝ) * ((supC ρm ρo k)^(k+1)) * S * ‖x - y‖ :=
              mul_le_mul_of_nonneg_left (norm_update_sub_le j x y ζ) (mul_nonneg (mul_nonneg (by positivity) hM1nn) hS)
      have hB : ‖((ζ - x j) ^ (-2 : ℤ) - (ζ - y j) ^ (-2 : ℤ)) * g' (Function.update y j ζ)‖
          ≤ (2 * ‖x - y‖ / (sm j - ρi j)^3) * (((supC ρm ρo k)^(k+1)) * S) := by
        rw [norm_mul]
        refine mul_le_mul ?_ (hgsup _ (hmemy ζ hζ)) (norm_nonneg _) (by positivity)
        calc ‖(ζ - x j) ^ (-2 : ℤ) - (ζ - y j) ^ (-2 : ℤ)‖
            ≤ 2 * ‖(ζ - x j) - (ζ - y j)‖ / (sm j - ρi j)^3 := norm_zpow_neg_two_sub_le hgapj hxa hya
          _ = 2 * ‖x j - y j‖ / (sm j - ρi j)^3 := by
              rw [show (ζ - x j) - (ζ - y j) = -(x j - y j) by ring, norm_neg]
          _ ≤ 2 * ‖x - y‖ / (sm j - ρi j)^3 := by
              gcongr
              calc ‖x j - y j‖ = ‖(x - y) j‖ := by rw [Pi.sub_apply]
                _ ≤ ‖x - y‖ := norm_le_pi_norm (x - y) j
      calc ‖(ζ - x j) ^ (-2 : ℤ) * (g' (Function.update x j ζ) - g' (Function.update y j ζ))
            + ((ζ - x j) ^ (-2 : ℤ) - (ζ - y j) ^ (-2 : ℤ)) * g' (Function.update y j ζ)‖
          ≤ ‖(ζ - x j) ^ (-2 : ℤ) * (g' (Function.update x j ζ) - g' (Function.update y j ζ))‖
            + ‖((ζ - x j) ^ (-2 : ℤ) - (ζ - y j) ^ (-2 : ℤ)) * g' (Function.update y j ζ)‖ :=
            norm_add_le _ _
        _ ≤ ((sm j - ρi j)^2)⁻¹ * ((n:ℝ) * ((supC ρm ρo k)^(k+1)) * S * ‖x - y‖)
            + (2 * ‖x - y‖ / (sm j - ρi j)^3) * (((supC ρm ρo k)^(k+1)) * S) := add_le_add hA hB
        _ = (((supC ρm ρo k)^(k+1)) * S * ((n:ℝ) / (sm j - ρi j)^2 + 2 / (sm j - ρi j)^3)) * ‖x - y‖ := by
            rw [div_eq_mul_inv, div_eq_mul_inv,
              show ((sm j - ρi j)^3)⁻¹ = ((sm j - ρi j)^2)⁻¹ * (sm j - ρi j)⁻¹ by
                rw [show (sm j - ρi j)^3 = (sm j - ρi j)^2 * (sm j - ρi j) by ring, mul_inv]]
            field_simp
    have hsmnn : 0 ≤ sm j := by
      have : 0 < ρi j := lt_of_le_of_lt (norm_nonneg _) (hx j)
      linarith [hsm_gt j]
    have hKxi : CircleIntegrable
        (fun ζ : ℂ => (ζ - x j) ^ (-2 : ℤ) • (g' (Function.update x j ζ))) (c j) (sm j) :=
      (continuousOn_zpow_mul_slice hgc hsm_lt_ρo hx_other
        (by rw [← dist_eq_norm] at hx_norm ⊢; exact hx_norm)).circleIntegrable hsmnn
    have hKyi : CircleIntegrable
        (fun ζ : ℂ => (ζ - y j) ^ (-2 : ℤ) • (g' (Function.update y j ζ))) (c j) (sm j) :=
      (continuousOn_zpow_mul_slice hgc hsm_lt_ρo hy_other
        (by rw [← dist_eq_norm] at hy_norm ⊢; exact hy_norm)).circleIntegrable hsmnn
    have hcomb : dcoordVec (k+1) v h x - dcoordVec (k+1) v h y
        = ((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
            (∮ ζ in C(c j, sm j), ((ζ - x j) ^ (-2 : ℤ) • (g' (Function.update x j ζ))
              - (ζ - y j) ^ (-2 : ℤ) • (g' (Function.update y j ζ)))) := by
      rw [hreprx, hrepry, ← smul_sub, ← circleIntegral.integral_sub hKxi hKyi]
    rw [hcomb]
    calc ‖((2 * (Real.pi : ℂ) * Complex.I)⁻¹) •
            (∮ ζ in C(c j, sm j), ((ζ - x j) ^ (-2 : ℤ) • (g' (Function.update x j ζ))
              - (ζ - y j) ^ (-2 : ℤ) • (g' (Function.update y j ζ))))‖
        ≤ sm j * ((((supC ρm ρo k)^(k+1)) * S * ((n:ℝ) / (sm j - ρi j)^2 + 2 / (sm j - ρi j)^3)) * ‖x - y‖) :=
          circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hsmnn
            (fun ζ hζ => hbound ζ hζ)
      _ = ((supC ρm ρo k)^(k+1)) * S * (sm j * ((n:ℝ) / (sm j - ρi j)^2 + 2 / (sm j - ρi j)^3)) * ‖x - y‖ := by ring
      _ ≤ ((supC ρm ρo k)^(k+1)) * S * Kc * ‖x - y‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact mul_le_mul_of_nonneg_left (hKc_ge j) (mul_nonneg (pow_pos (supC_pos hmono_m k) (k+1)).le hS)
      _ ≤ (max ((n:ℝ) * ((supC ρi ρo k)^(k+1))) (((supC ρm ρo k)^(k+1)) * Kc) + 1) * S * ‖x - y‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          rw [show ((supC ρm ρo k)^(k+1)) * S * Kc = ((supC ρm ρo k)^(k+1)) * Kc * S by ring]
          exact mul_le_mul_of_nonneg_right
            (le_trans (le_max_right _ _) (le_add_of_nonneg_right zero_le_one)) hS
      _ ≤ lipC ρi ρo k * S * ‖x - y‖ := by
          have h2 : lipC ρi ρo k
              = |max ((n:ℝ) * (supC ρi ρo k)^(k+1)) ((supC ρm ρo k)^(k+1) * Kc)| + 1 := by
            simp only [lipC, hρm, hsm, hKc]
          rw [h2]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (by linarith [le_abs_self (max ((n:ℝ) * (supC ρi ρo k)^(k+1))
              ((supC ρm ρo k)^(k+1) * Kc))]) hS) (norm_nonneg _)


private lemma iterDerivNorm_le_wirtinger_o {n : ℕ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    (k : ℕ) (α : ℝ) {u : (Fin n → ℂ) → ℂ} (hu : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) u Ω)
    {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k + 1) :
    iterDerivNorm i u Ω ≤ ∑ j : Fin n, (holderNorm k α (fun z => dCoord j u z) Ω
        + holderNorm k α (fun z => dbarCoord j u z) Ω) := by
  have hΩu : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  have hpred : i - 1 ≤ k := by omega
  have hsucc : i - 1 + 1 = i := by omega
  have hdz : ∀ j : Fin n, ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => dCoord j u z) Ω := fun j =>
    (contDiffOn_dCoord' hΩ hu j).of_le (WithTop.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hpred))
  have hdb : ∀ j : Fin n, ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => dbarCoord j u z) Ω := fun j =>
    (contDiffOn_dbarCoord' hΩ hu j).of_le (WithTop.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hpred))
  have hg : ∀ j : Fin n, ContDiffOn ℝ (((i-1):ℕ):ℕ∞)
      (fun z => PhiN j (dCoord j u z) + PsiN j (dbarCoord j u z)) Ω := fun j =>
    ((PhiN j).contDiff.comp_contDiffOn (hdz j)).add
      ((PsiN j).contDiff.comp_contDiffOn (hdb j))
  have hperj : ∀ j : Fin n,
      iDN (i - 1) (fun z => PhiN j (dCoord j u z) + PsiN j (dbarCoord j u z)) Ω
        ≤ holderNorm k α (fun z => dCoord j u z) Ω
          + holderNorm k α (fun z => dbarCoord j u z) Ω := by
    intro j
    have hφ : ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => PhiN j (dCoord j u z)) Ω :=
      (PhiN j).contDiff.comp_contDiffOn (hdz j)
    have hψ : ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => PsiN j (dbarCoord j u z)) Ω :=
      (PsiN j).contDiff.comp_contDiffOn (hdb j)
    calc iDN (i - 1) (fun z => PhiN j (dCoord j u z) + PsiN j (dbarCoord j u z)) Ω
        ≤ iDN (i - 1) (fun z => PhiN j (dCoord j u z)) Ω
          + iDN (i - 1) (fun z => PsiN j (dbarCoord j u z)) Ω :=
          iDN_add_le (i - 1) hφ hψ hΩu
      _ ≤ ENNReal.ofReal ‖PhiN j‖ * iDN (i - 1) (fun z => dCoord j u z) Ω
          + ENNReal.ofReal ‖PsiN j‖ * iDN (i - 1) (fun z => dbarCoord j u z) Ω :=
          add_le_add (comp_linear_le (PhiN j) (i - 1) α (hdz j) hΩu).1
            (comp_linear_le (PsiN j) (i - 1) α (hdb j) hΩu).1
      _ ≤ iDN (i - 1) (fun z => dCoord j u z) Ω
          + iDN (i - 1) (fun z => dbarCoord j u z) Ω := by
          refine add_le_add ?_ ?_
          · calc ENNReal.ofReal ‖PhiN j‖ * iDN (i - 1) (fun z => dCoord j u z) Ω
                ≤ 1 * iDN (i - 1) (fun z => dCoord j u z) Ω :=
                  mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_one.mpr (norm_PhiN_le j)) bot_le
              _ = iDN (i - 1) (fun z => dCoord j u z) Ω := one_mul _
          · calc ENNReal.ofReal ‖PsiN j‖ * iDN (i - 1) (fun z => dbarCoord j u z) Ω
                ≤ 1 * iDN (i - 1) (fun z => dbarCoord j u z) Ω :=
                  mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_one.mpr (norm_PsiN_le j)) bot_le
              _ = iDN (i - 1) (fun z => dbarCoord j u z) Ω := one_mul _
      _ ≤ holderNorm k α (fun z => dCoord j u z) Ω
          + holderNorm k α (fun z => dbarCoord j u z) Ω :=
          add_le_add (iterDerivNorm_le_holderNorm k α _ Ω hpred)
            (iterDerivNorm_le_holderNorm k α _ Ω hpred)
  calc iterDerivNorm i u Ω
      = iDN i u Ω := rfl
    _ = iDN ((i-1)+1) u Ω := by rw [hsucc]
    _ = iDN (i-1) (fun z => fderivWithin ℝ u Ω z) Ω := (iDN_fderivWithin (i-1) u Ω hΩu).symm
    _ = iDN (i-1)
          (fun z => ∑ j : Fin n, (PhiN j (dCoord j u z) + PsiN j (dbarCoord j u z))) Ω :=
        iDN_congr (fun z hz => by
          rw [fderivWithin_of_isOpen hΩ hz, fderiv_eq_sum_PhiN_PsiN])
    _ ≤ ∑ j : Fin n,
          iDN (i-1) (fun z => PhiN j (dCoord j u z) + PsiN j (dbarCoord j u z)) Ω :=
        iDN_sum_le Finset.univ (i-1) (fun j _ => hg j) hΩu
    _ ≤ ∑ j : Fin n, (holderNorm k α (fun z => dCoord j u z) Ω
          + holderNorm k α (fun z => dbarCoord j u z) Ω) :=
        Finset.sum_le_sum (fun j _ => hperj j)

/-- Bound on the Hölder seminorms of the derivatives of `u` of order `1 ≤ i ≤ k+1`. -/
private lemma holderSeminorm_le_wirtinger_o {n : ℕ} {Ω : Set (Fin n → ℂ)} (hΩ : IsOpen Ω)
    (k : ℕ) (α : ℝ) {u : (Fin n → ℂ) → ℂ} (hu : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) u Ω)
    {i : ℕ} (hi1 : 1 ≤ i) (hik : i ≤ k + 1) :
    holderSeminorm i α u Ω ≤ ∑ j : Fin n, (holderNorm k α (fun z => dCoord j u z) Ω
        + holderNorm k α (fun z => dbarCoord j u z) Ω) := by
  have hΩu : UniqueDiffOn ℝ Ω := hΩ.uniqueDiffOn
  have hpred : i - 1 ≤ k := by omega
  have hsucc : i - 1 + 1 = i := by omega
  have hdz : ∀ j : Fin n, ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => dCoord j u z) Ω := fun j =>
    (contDiffOn_dCoord' hΩ hu j).of_le (WithTop.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hpred))
  have hdb : ∀ j : Fin n, ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => dbarCoord j u z) Ω := fun j =>
    (contDiffOn_dbarCoord' hΩ hu j).of_le (WithTop.coe_le_coe.mpr (ENat.natCast_le_natCast.mpr hpred))
  have hg : ∀ j : Fin n, ContDiffOn ℝ (((i-1):ℕ):ℕ∞)
      (fun z => PhiN j (dCoord j u z) + PsiN j (dbarCoord j u z)) Ω := fun j =>
    ((PhiN j).contDiff.comp_contDiffOn (hdz j)).add
      ((PsiN j).contDiff.comp_contDiffOn (hdb j))
  have hperj : ∀ j : Fin n,
      hSN (i - 1) α (fun z => PhiN j (dCoord j u z) + PsiN j (dbarCoord j u z)) Ω
        ≤ holderNorm k α (fun z => dCoord j u z) Ω
          + holderNorm k α (fun z => dbarCoord j u z) Ω := by
    intro j
    have hφ : ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => PhiN j (dCoord j u z)) Ω :=
      (PhiN j).contDiff.comp_contDiffOn (hdz j)
    have hψ : ContDiffOn ℝ (((i-1):ℕ):ℕ∞) (fun z => PsiN j (dbarCoord j u z)) Ω :=
      (PsiN j).contDiff.comp_contDiffOn (hdb j)
    calc hSN (i - 1) α (fun z => PhiN j (dCoord j u z) + PsiN j (dbarCoord j u z)) Ω
        ≤ hSN (i - 1) α (fun z => PhiN j (dCoord j u z)) Ω
          + hSN (i - 1) α (fun z => PsiN j (dbarCoord j u z)) Ω :=
          hSN_add_le (i - 1) α hφ hψ hΩu
      _ ≤ ENNReal.ofReal ‖PhiN j‖ * hSN (i - 1) α (fun z => dCoord j u z) Ω
          + ENNReal.ofReal ‖PsiN j‖ * hSN (i - 1) α (fun z => dbarCoord j u z) Ω :=
          add_le_add (comp_linear_le (PhiN j) (i - 1) α (hdz j) hΩu).2
            (comp_linear_le (PsiN j) (i - 1) α (hdb j) hΩu).2
      _ ≤ hSN (i - 1) α (fun z => dCoord j u z) Ω
          + hSN (i - 1) α (fun z => dbarCoord j u z) Ω := by
          refine add_le_add ?_ ?_
          · calc ENNReal.ofReal ‖PhiN j‖ * hSN (i - 1) α (fun z => dCoord j u z) Ω
                ≤ 1 * hSN (i - 1) α (fun z => dCoord j u z) Ω :=
                  mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_one.mpr (norm_PhiN_le j)) bot_le
              _ = hSN (i - 1) α (fun z => dCoord j u z) Ω := one_mul _
          · calc ENNReal.ofReal ‖PsiN j‖ * hSN (i - 1) α (fun z => dbarCoord j u z) Ω
                ≤ 1 * hSN (i - 1) α (fun z => dbarCoord j u z) Ω :=
                  mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_one.mpr (norm_PsiN_le j)) bot_le
              _ = hSN (i - 1) α (fun z => dbarCoord j u z) Ω := one_mul _
      _ ≤ holderNorm k α (fun z => dCoord j u z) Ω
          + holderNorm k α (fun z => dbarCoord j u z) Ω :=
          add_le_add (holderSeminorm_le_holderNorm k α _ Ω hpred)
            (holderSeminorm_le_holderNorm k α _ Ω hpred)
  calc holderSeminorm i α u Ω
      = hSN i α u Ω := rfl
    _ = hSN ((i-1)+1) α u Ω := by rw [hsucc]
    _ = hSN (i-1) α (fun z => fderivWithin ℝ u Ω z) Ω := (hSN_fderivWithin (i-1) α u Ω hΩu).symm
    _ = hSN (i-1) α
          (fun z => ∑ j : Fin n, (PhiN j (dCoord j u z) + PsiN j (dbarCoord j u z))) Ω :=
        hSN_congr (fun z hz => by
          rw [fderivWithin_of_isOpen hΩ hz, fderiv_eq_sum_PhiN_PsiN])
    _ ≤ ∑ j : Fin n,
          hSN (i-1) α (fun z => PhiN j (dCoord j u z) + PsiN j (dbarCoord j u z)) Ω :=
        hSN_sum_le Finset.univ (i-1) α (fun j _ => hg j) hΩu
    _ ≤ ∑ j : Fin n, (holderNorm k α (fun z => dCoord j u z) Ω
          + holderNorm k α (fun z => dbarCoord j u z) Ω) :=
        Finset.sum_le_sum (fun j _ => hperj j)


theorem holderNorm_le_wirtinger_coord_open' {n : ℕ} {α : ℝ} (k : ℕ) {Ω : Set (Fin n → ℂ)}
    (hΩ : IsOpen Ω) (u : (Fin n → ℂ) → ℂ)
    (hu : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) u Ω) :
    Work.CR.Flat.holderNorm (k + 1) α u Ω
      ≤ ENNReal.ofReal (2 * (k + 2)) * (Work.CR.Flat.holderNorm 0 α u Ω
          + ∑ j : Fin n, (Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dCoord j u z) Ω
              + Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dbarCoord j u z) Ω)) := by
  set A := Work.CR.Flat.holderNorm 0 α u Ω with hA
  set B := ∑ j : Fin n, (Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dCoord j u z) Ω
      + Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dbarCoord j u z) Ω) with hB
  have hterm : ∀ i ∈ Finset.range ((k+1)+1),
      iterDerivNorm i u Ω + holderSeminorm i α u Ω ≤ 2 * (A + B) := by
    intro i hi
    rw [Finset.mem_range] at hi
    obtain h0 | hpos := Nat.eq_zero_or_pos i
    · subst h0
      have h1 : iterDerivNorm 0 u Ω ≤ A := iterDerivNorm_le_holderNorm 0 α u Ω le_rfl
      have h2 : holderSeminorm 0 α u Ω ≤ A := holderSeminorm_le_holderNorm 0 α u Ω le_rfl
      calc iterDerivNorm 0 u Ω + holderSeminorm 0 α u Ω ≤ A + A := add_le_add h1 h2
        _ = 2 * A := (two_mul A).symm
        _ ≤ 2 * (A + B) := by gcongr; exact le_add_right le_rfl
    · have hi1 : 1 ≤ i := hpos
      have hik : i ≤ k + 1 := by omega
      have h1 := iterDerivNorm_le_wirtinger_o hΩ k α hu hi1 hik
      have h2 := holderSeminorm_le_wirtinger_o hΩ k α hu hi1 hik
      calc iterDerivNorm i u Ω + holderSeminorm i α u Ω ≤ B + B := add_le_add h1 h2
        _ = 2 * B := (two_mul B).symm
        _ ≤ 2 * (A + B) := by gcongr; exact le_add_left le_rfl
  calc Work.CR.Flat.holderNorm (k + 1) α u Ω
      = ∑ i ∈ Finset.range ((k+1)+1), (iterDerivNorm i u Ω + holderSeminorm i α u Ω) := rfl
    _ ≤ ∑ i ∈ Finset.range ((k+1)+1), (2 * (A + B)) := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (2 * (k + 2)) * (A + B) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        rw [← mul_assoc]
        rw [show (2:ℝ≥0∞) = ((2:ℕ):ℝ≥0∞) from by norm_num, ← Nat.cast_mul]
        rw [show ENNReal.ofReal (2 * (k+2) : ℝ) = ((2*(k+2):ℕ) : ℝ≥0∞) from by
          rw [show (2*(k+2):ℝ) = ((2*(k+2):ℕ):ℝ) from by norm_num, ENNReal.ofReal_natCast]]
        congr 1
        ring_nf



/-- The standard bijection `(v, j) ↦ Fin.cons j v`. -/
def finConsEquiv {m n : ℕ} : (Fin m → Fin n) × Fin n ≃ (Fin (m+1) → Fin n) where
  toFun p := Fin.cons p.2 p.1
  invFun w := (fun i => w i.succ, w 0)
  left_inv p := by
    obtain ⟨v, j⟩ := p
    simp only [Prod.mk.injEq]
    exact ⟨funext fun i => by simp [Fin.cons_succ], by simp [Fin.cons_zero]⟩
  right_inv w := by
    funext i
    by_cases hi : i = 0
    · subst hi; simp [Fin.cons_zero]
    · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.mpr hi
      simp [Fin.cons_succ]

/-! ## Assembly -/

/-- The `C^{k,α}`-norm on an open set vanishes identically for a function that vanishes there. -/
lemma holderNorm_eq_zero_of_eqOn_zero {n : ℕ} {Ω : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → ℂ}
    (h : ∀ z ∈ Ω, f z = 0) (k : ℕ) (α : ℝ) : holderNorm k α f Ω = 0 := by
  have hiter : ∀ i, iterDerivNorm i f Ω = 0 := by
    intro i
    refine le_antisymm ?_ bot_le
    refine iSup₂_le fun z hz => ?_
    have hc : iteratedFDerivWithin ℝ i f Ω z
        = iteratedFDerivWithin ℝ i (0 : (Fin n → ℂ) → ℂ) Ω z :=
      iteratedFDerivWithin_congr (f₁ := f) (f := (0 : (Fin n → ℂ) → ℂ)) (fun y hy => h y hy) hz i
    rw [hc, iteratedFDerivWithin_zero]
    simp
  have hsemi : ∀ i, holderSeminorm i α f Ω = 0 := by
    intro i
    refine le_antisymm ?_ bot_le
    refine iSup₂_le fun z hz => iSup₂_le fun y hy => iSup_le fun _ => ?_
    have hc : iteratedFDerivWithin ℝ i f Ω z
        = iteratedFDerivWithin ℝ i (0 : (Fin n → ℂ) → ℂ) Ω z :=
      iteratedFDerivWithin_congr (f₁ := f) (f := (0 : (Fin n → ℂ) → ℂ)) (fun y hy => h y hy) hz i
    have hc' : iteratedFDerivWithin ℝ i f Ω y
        = iteratedFDerivWithin ℝ i (0 : (Fin n → ℂ) → ℂ) Ω y :=
      iteratedFDerivWithin_congr (f₁ := f) (f := (0 : (Fin n → ℂ) → ℂ)) (fun y hy => h y hy) hy i
    rw [hc, hc', iteratedFDerivWithin_zero]
    simp
  rw [holderNorm]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [hiter i, hsemi i, add_zero]

/-- The diameter of a polydisc is bounded by an explicit constant. -/
lemma diam_bound {n : ℕ} {c : Fin n → ℂ} {ρi : Fin n → ℝ} {x y : Fin n → ℂ}
    (hx : x ∈ polydisc c ρi) (hy : y ∈ polydisc c ρi) :
    ‖x - y‖ ≤ 2 * (∑ j : Fin n, |ρi j|) + 1 := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun j => ?_
  rw [Pi.sub_apply]
  have h1 : 0 < ρi j := lt_of_le_of_lt (norm_nonneg _) (hx j)
  have h2 : ‖x j - y j‖ < 2 * ρi j := by
    calc ‖x j - y j‖ = ‖(x j - c j) - (y j - c j)‖ := by congr 1; ring
      _ ≤ ‖x j - c j‖ + ‖y j - c j‖ := norm_sub_le _ _
      _ < ρi j + ρi j := add_lt_add (hx j) (hy j)
      _ = 2 * ρi j := by ring
  have h3 : ρi j ≤ ∑ i : Fin n, |ρi i| := by
    rw [← abs_of_pos h1]
    exact Finset.single_le_sum (f := fun i : Fin n => |ρi i|) (fun i _ => abs_nonneg _)
      (Finset.mem_univ j)
  have h4 : (0:ℝ) ≤ ∑ i : Fin n, |ρi i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  linarith

/-- The order-`0` Hölder seminorm is controlled by a Lipschitz constant and the diameter. -/
lemma holderSeminorm_zero_le {n : ℕ} {Ω : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → ℂ} {L D : ℝ}
    {α : ℝ} (hL : 0 ≤ L) (hD : 0 ≤ D) (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (hlip : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖f x - f y‖ ≤ L * ‖x - y‖)
    (hdiam : ∀ x ∈ Ω, ∀ y ∈ Ω, ‖x - y‖ ≤ D) :
    holderSeminorm 0 α f Ω ≤ ENNReal.ofReal (L * (1 + D)) := by
  refine iSup₂_le fun x hx => iSup₂_le fun y hy => iSup_le fun hxy => ?_
  have hdist : ‖iteratedFDerivWithin ℝ 0 f Ω x - iteratedFDerivWithin ℝ 0 f Ω y‖
      = ‖f x - f y‖ := by
    rw [← dist_eq_norm, dist_iteratedFDerivWithin_zero, dist_eq_norm]
  rw [hdist]
  refine ENNReal.ofReal_le_ofReal ?_
  have hxy0 : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have h1 : ‖f x - f y‖ ≤ L * ‖x - y‖ := hlip x hx y hy
  have h2 : ‖x - y‖ ≤ D := hdiam x hx y hy
  have h3 : ‖x - y‖ ^ (1 - α) ≤ 1 + D := by
    by_cases hle : ‖x - y‖ ≤ 1
    · calc ‖x - y‖ ^ (1 - α) ≤ 1 ^ (1 - α) :=
            Real.rpow_le_rpow (norm_nonneg _) hle (by linarith)
        _ = 1 := Real.one_rpow _
        _ ≤ 1 + D := by linarith
    · push_neg at hle
      calc ‖x - y‖ ^ (1 - α) ≤ ‖x - y‖ ^ (1:ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hle.le (by linarith)
        _ = ‖x - y‖ := Real.rpow_one _
        _ ≤ 1 + D := by linarith
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hxy0 α)]
  calc ‖f x - f y‖ ≤ L * ‖x - y‖ := h1
    _ = L * (‖x - y‖ ^ α * ‖x - y‖ ^ (1 - α)) := by
        rw [← Real.rpow_add hxy0, show α + (1 - α) = 1 by ring, Real.rpow_one]
    _ ≤ L * (‖x - y‖ ^ α * (1 + D)) := by gcongr
    _ = L * (1 + D) * ‖x - y‖ ^ α := by ring

/-- `iterDerivNorm 0` is bounded by an explicit constant. -/
lemma iterDerivNorm_zero_le {n : ℕ} {Ω : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → ℂ} {X : ℝ}
    (h : ∀ z ∈ Ω, ‖f z‖ ≤ X) : iterDerivNorm 0 f Ω ≤ ENNReal.ofReal X := by
  rw [iterDerivNorm_zero]
  refine iSup₂_le fun z hz => ENNReal.ofReal_le_ofReal (h z hz)

/-- The `C^{k,α}` norm of `h` on the inner polydisc is controlled by any boundedness constant of
`h` on the outer polydisc, with a constant that is uniform in `h` and the bound. -/
theorem holderNorm_le_sup_of_holomorphic_bound {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ}
    {ρi ρo : Fin n → ℝ} (hmono : ∀ j, ρi j < ρo j) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (h : (Fin n → ℂ) → ℂ) (B : ℝ), 0 ≤ B →
      ContDiffOn ℝ (((k+1 : ℕ)) : WithTop ℕ∞) h (polydisc c ρo) →
      (∀ j, ∀ z ∈ polydisc c ρo, dbarCoord j h z = 0) →
      (∀ z ∈ polydisc c ρo, ‖h z‖ ≤ B) →
      holderNorm (k+1) α h (polydisc c ρi) ≤ ENNReal.ofReal (C * B) := by
  set Diam : ℝ := 2 * (∑ j : Fin n, |ρi j|) + 1 with hDiam
  have hDiam_pos : 0 < Diam := by
    rw [hDiam]
    have hsum : (0:ℝ) ≤ ∑ j : Fin n, |ρi j| := Finset.sum_nonneg fun j _ => abs_nonneg _
    linarith
  set Pf : ℝ := (supC ρi ρo k)^(k+1) + lipC ρi ρo k * (1 + Diam) with hPf
  have hPf_pos : 0 < Pf := by
    rw [hPf]
    have h1 := pow_pos (supC_pos hmono k) (k+1)
    have h2 := mul_pos (lipC_pos ρi ρo k) (by linarith : (0:ℝ) < 1 + Diam)
    linarith
  refine ⟨(2*(k+2))^(k+2) * (k+2) * (n:ℝ)^(k+1) * Pf, ?_, ?_⟩
  · have h1 : (0:ℝ) < (2*(k+2))^(k+2) := pow_pos (by positivity) _
    have h2 : (0:ℝ) < ((k:ℝ)+2) := by positivity
    have h3 : (0:ℝ) < (n:ℝ)^(k+1) := pow_pos (by exact_mod_cast hn) _
    exact mul_pos (mul_pos (mul_pos h1 h2) h3) hPf_pos
  intro h B hB hsmooth hhol hbnd
  have hsub : polydisc c ρi ⊆ polydisc c ρo := polydisc_mono (fun j => le_of_lt (hmono j))
  have hsup : ∀ (m : ℕ) (v : Fin m → Fin n) (z : Fin n → ℂ),
      m ≤ k+1 → z ∈ polydisc c ρi → ‖dcoordVec m v h z‖ ≤ (supC ρi ρo k)^(k+1) * B :=
    dcoordVec_sup_bound hmono hB (supC_pos hmono k) (supC_ge1 hmono k) (supC_bound hmono k)
      hsmooth hhol hbnd
  have hlip : ∀ (m : ℕ) (v : Fin m → Fin n) (x : Fin n → ℂ) (y : Fin n → ℂ),
      m ≤ k+1 → x ∈ polydisc c ρi → y ∈ polydisc c ρi →
      ‖dcoordVec m v h x - dcoordVec m v h y‖ ≤ lipC ρi ρo k * B * ‖x - y‖ :=
    dcoordVec_lipschitz hmono hB hsmooth hhol hbnd
  have hper : ∀ (m : ℕ) (v : Fin m → Fin n), m ≤ k+1 →
      holderNorm 0 α (dcoordVec m v h) (polydisc c ρi) ≤ ENNReal.ofReal (Pf * B) := by
    intro m v hm
    have h1 : iterDerivNorm 0 (dcoordVec m v h) (polydisc c ρi)
        ≤ ENNReal.ofReal (((supC ρi ρo k)^(k+1)) * B) :=
      iterDerivNorm_zero_le fun z hz => hsup m v z hm hz
    have h2 : holderSeminorm 0 α (dcoordVec m v h) (polydisc c ρi)
        ≤ ENNReal.ofReal (lipC ρi ρo k * B * (1 + Diam)) :=
      holderSeminorm_zero_le (mul_nonneg (le_of_lt (lipC_pos ρi ρo k)) hB)
        (le_of_lt hDiam_pos) hα hα1
        (fun x hx y hy => by simpa only [mul_assoc] using hlip m v x y hm hx hy)
        (fun x hx y hy => diam_bound hx hy)
    rw [holderNorm, Finset.sum_range_one]
    refine le_trans (add_le_add h1 h2) (le_of_eq ?_)
    rw [← ENNReal.ofReal_add
      (mul_nonneg (pow_nonneg (supC_pos hmono k).le (k+1)) hB)
      (mul_nonneg (mul_nonneg (lipC_pos ρi ρo k).le hB) (by linarith))]
    congr 1
    rw [hPf]; ring
  set G : ℕ → ℝ≥0∞ := (fun m =>
    ∑ v : Fin m → Fin n, holderNorm (k+1-m) α (dcoordVec m v h) (polydisc c ρi)) with hGdef
  set E : ℕ → ℝ≥0∞ := (fun m =>
    ∑ v : Fin m → Fin n, holderNorm 0 α (dcoordVec m v h) (polydisc c ρi)) with hEdef
  set M : ℝ≥0∞ := ENNReal.ofReal (((n:ℝ)^(k+1)) * Pf * B) with hMdef
  have hE : ∀ m ≤ k+1, E m ≤ M := by
    intro m hm
    have hsum : E m ≤ ((Fintype.card (Fin m → Fin n) : ℕ) : ℝ≥0∞) * ENNReal.ofReal (Pf * B) := by
      rw [hEdef]
      calc ∑ v : Fin m → Fin n, holderNorm 0 α (dcoordVec m v h) (polydisc c ρi)
          ≤ ∑ _v : Fin m → Fin n, ENNReal.ofReal (Pf * B) :=
            Finset.sum_le_sum fun v _ => hper m v hm
        _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : ((Fintype.card (Fin m → Fin n) : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((n:ℝ)^m) := by
      rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow,
        ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (Nat.cast_nonneg n)]
    rw [hcard] at hsum
    refine le_trans hsum ?_
    have hle : ((n:ℝ)^m) ≤ (n:ℝ)^(k+1) := pow_le_pow_right₀ (by exact_mod_cast hn) hm
    rw [hMdef]
    calc ENNReal.ofReal ((n:ℝ)^m) * ENNReal.ofReal (Pf * B)
        ≤ ENNReal.ofReal ((n:ℝ)^(k+1)) * ENNReal.ofReal (Pf * B) :=
          mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hle) bot_le
      _ = ENNReal.ofReal (((n:ℝ)^(k+1)) * Pf * B) := by
          rw [← ENNReal.ofReal_mul (by positivity), mul_assoc]
  have hdc : ∀ (m : ℕ) (j : Fin n) (v : Fin m → Fin n),
      (fun z => dCoord j (dcoordVec m v h) z) = dcoordVec (m+1) (Fin.cons j v) h :=
    fun m j v => (dcoordVec_cons m j v h).symm
  have hG_E : ∀ m ≤ k, G m ≤ ENNReal.ofReal (2*(k+2)) * (E m + G (m+1)) := by
    intro m hmk
    have hperv : ∀ v : Fin m → Fin n,
        holderNorm (k+1-m) α (dcoordVec m v h) (polydisc c ρi)
          ≤ ENNReal.ofReal (2*(k+2)) * (holderNorm 0 α (dcoordVec m v h) (polydisc c ρi)
              + ∑ j : Fin n, (holderNorm (k-m) α (fun z => dCoord j (dcoordVec m v h) z) (polydisc c ρi)
                  + holderNorm (k-m) α (fun z => dbarCoord j (dcoordVec m v h) z) (polydisc c ρi))) := by
      intro v
      have hs : ContDiffOn ℝ (((k-m+1 : ℕ)) : WithTop ℕ∞) (dcoordVec m v h) (polydisc c ρi) := by
        have h0 : ContDiffOn ℝ (((k+1-m : ℕ)) : WithTop ℕ∞) (dcoordVec m v h) (polydisc c ρo) := by
          refine contDiffOn_dcoordVec (isOpen_polydisc c ρo) m v (k+1-m) ?_
          rw [show (k+1-m) + m = k+1 from by omega]
          exact hsmooth
        have h0' := h0.mono hsub
        rwa [show k+1-m = k-m+1 from by omega] at h0'
      have h := holderNorm_le_wirtinger_coord_open' (α := α) (k-m) (isOpen_polydisc c ρi)
        (dcoordVec m v h) hs
      rw [show (k-m)+1 = k+1-m from by omega] at h
      refine le_trans h (mul_le_mul (ENNReal.ofReal_le_ofReal ?_) le_rfl bot_le bot_le)
      push_cast
      have hs' : ((k-m:ℕ):ℝ) ≤ (k:ℝ) := by exact_mod_cast Nat.sub_le k m
      linarith
    have hsum : G m ≤ ∑ v : Fin m → Fin n,
        ENNReal.ofReal (2*(k+2)) * (holderNorm 0 α (dcoordVec m v h) (polydisc c ρi)
            + ∑ j : Fin n, (holderNorm (k-m) α (fun z => dCoord j (dcoordVec m v h) z) (polydisc c ρi)
                + holderNorm (k-m) α (fun z => dbarCoord j (dcoordVec m v h) z) (polydisc c ρi))) := by
      rw [hGdef]
      exact Finset.sum_le_sum fun v _ => hperv v
    have hzero : ∀ (j : Fin n) (v : Fin m → Fin n),
        holderNorm (k-m) α (fun z => dbarCoord j (dcoordVec m v h) z) (polydisc c ρi) = 0 := by
      intro j v
      refine holderNorm_eq_zero_of_eqOn_zero (fun z hz => ?_) (k-m) α
      exact dbarCoord_dcoordVec_eq_zero (isOpen_polydisc c ρo) (κ := k+1) hhol hsmooth
        m v j z (hsub hz) (by omega)
    have hstep : (∑ v : Fin m → Fin n, ∑ j : Fin n,
          (holderNorm (k-m) α (fun z => dCoord j (dcoordVec m v h) z) (polydisc c ρi)
              + holderNorm (k-m) α (fun z => dbarCoord j (dcoordVec m v h) z) (polydisc c ρi)))
        ≤ G (m+1) := by
      have hz : (∑ v : Fin m → Fin n, ∑ j : Fin n,
            holderNorm (k-m) α (fun z => dbarCoord j (dcoordVec m v h) z) (polydisc c ρi)) = 0 :=
        Finset.sum_eq_zero fun v _ => Finset.sum_eq_zero fun j _ => hzero j v
      have hf : (∑ v : Fin m → Fin n, ∑ j : Fin n,
            holderNorm (k-m) α (fun z => dCoord j (dcoordVec m v h) z) (polydisc c ρi))
          = ∑ w : Fin (m+1) → Fin n,
              holderNorm (k+1-(m+1)) α (dcoordVec (m+1) w h) (polydisc c ρi) := by
        rw [← Finset.sum_product (s := Finset.univ) (t := Finset.univ)
              (f := fun p : (Fin m → Fin n) × Fin n =>
                holderNorm (k-m) α (fun z => dCoord p.2 (dcoordVec m p.1 h) z) (polydisc c ρi))]
        exact Fintype.sum_equiv (finConsEquiv (m := m) (n := n))
          (fun p : (Fin m → Fin n) × Fin n =>
            holderNorm (k-m) α (fun z => dCoord p.2 (dcoordVec m p.1 h) z) (polydisc c ρi))
          (fun w => holderNorm (k+1-(m+1)) α (dcoordVec (m+1) w h) (polydisc c ρi))
          (fun p => by
            change holderNorm (k-m) α (fun z => dCoord p.2 (dcoordVec m p.1 h) z) (polydisc c ρi)
              = holderNorm (k+1-(m+1)) α (dcoordVec (m+1) (Fin.cons p.2 p.1) h) (polydisc c ρi)
            rw [show k-m = k+1-(m+1) from by omega, dcoordVec_cons m p.2 p.1 h])
      simp only [Finset.sum_add_distrib]
      rw [hz, add_zero, hf]
    have hsum2 : (∑ v : Fin m → Fin n,
        ENNReal.ofReal (2*(k+2)) * (holderNorm 0 α (dcoordVec m v h) (polydisc c ρi)
            + ∑ j : Fin n, (holderNorm (k-m) α (fun z => dCoord j (dcoordVec m v h) z) (polydisc c ρi)
                + holderNorm (k-m) α (fun z => dbarCoord j (dcoordVec m v h) z) (polydisc c ρi))))
        ≤ ENNReal.ofReal (2*(k+2)) * (E m + G (m+1)) := by
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ bot_le
      rw [Finset.sum_add_distrib]
      refine add_le_add ?_ hstep
      rw [hEdef]
    exact le_trans hsum hsum2
  have hG0 : G 0 = holderNorm (k+1) α h (polydisc c ρi) := by
    simp only [hGdef]
    rw [Fintype.sum_unique]
    simp only [dcoordVec_zero, tsub_zero]
  have honeK : (1:ℝ≥0∞) ≤ (ENNReal.ofReal (2*(k+2)) : ℝ≥0∞) := by
    rw [ENNReal.one_le_ofReal]
    have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith
  have hkey : ∀ d, d ≤ k+1 → G (k+1-d)
      ≤ (∑ t ∈ Finset.range (d+1), (ENNReal.ofReal (2*(k+2)))^(t+1)) * M := by
    intro d
    induction d with
    | zero =>
        intro _
        rw [Nat.sub_zero]
        have h1 : G (k+1) = E (k+1) := by
          rw [hGdef, hEdef]
          simp only [tsub_self]
        rw [h1, Finset.sum_range_one, pow_one]
        exact le_trans (hE (k+1) le_rfl) (le_mul_of_one_le_left' honeK)
    | succ d ih =>
        intro hd
        have hdk : k - d ≤ k := by omega
        rw [show k+1-(d+1) = k-d from by omega]
        have h2 := hG_E (k-d) hdk
        have hih : G (k-d+1) ≤ (∑ t ∈ Finset.range (d+1),
            (ENNReal.ofReal (2*(k+2)))^(t+1)) * M := by
          have := ih (by omega)
          rwa [show k+1-d = k-d+1 from by omega] at this
        have hid2 : ENNReal.ofReal (2*(k+2))
              * (1 + ∑ t ∈ Finset.range (d+1), (ENNReal.ofReal (2*(k+2)))^(t+1))
            = ∑ t ∈ Finset.range (d+1+1), (ENNReal.ofReal (2*(k+2)))^(t+1) := by
          have hS : (∑ t ∈ Finset.range (d+1),
                ENNReal.ofReal (2*(k+2)) * (ENNReal.ofReal (2*(k+2)))^(t+1))
              = ∑ t ∈ Finset.range (d+1), (ENNReal.ofReal (2*(k+2)))^(t+1+1) :=
            Finset.sum_congr rfl fun t _ => by rw [← pow_succ']
          have hT : (∑ t ∈ Finset.range (d+1+1), (ENNReal.ofReal (2*(k+2)))^(t+1))
              = (∑ t ∈ Finset.range (d+1), (ENNReal.ofReal (2*(k+2)))^(t+1+1))
                + ENNReal.ofReal (2*(k+2)) := by
            simpa using (Finset.sum_range_succ'
              (fun t => (ENNReal.ofReal (2*(k+2)))^(t+1)) (d+1))
          rw [hT, mul_add, mul_one, Finset.mul_sum, hS]
          exact add_comm _ _
        have hid1 : ENNReal.ofReal (2*(k+2))
              * (M + (∑ t ∈ Finset.range (d+1), (ENNReal.ofReal (2*(k+2)))^(t+1)) * M)
            = (ENNReal.ofReal (2*(k+2))
              * (1 + ∑ t ∈ Finset.range (d+1), (ENNReal.ofReal (2*(k+2)))^(t+1))) * M := by
          ring
        calc G (k-d)
            ≤ ENNReal.ofReal (2*(k+2)) * (E (k-d) + G (k-d+1)) := h2
          _ ≤ ENNReal.ofReal (2*(k+2))
                * (M + (∑ t ∈ Finset.range (d+1), (ENNReal.ofReal (2*(k+2)))^(t+1)) * M) :=
              mul_le_mul_of_nonneg_left (add_le_add (hE (k-d) (by omega)) hih) bot_le
          _ = (ENNReal.ofReal (2*(k+2))
                * (1 + ∑ t ∈ Finset.range (d+1), (ENNReal.ofReal (2*(k+2)))^(t+1))) * M := hid1
          _ = (∑ t ∈ Finset.range (d+1+1), (ENNReal.ofReal (2*(k+2)))^(t+1)) * M := by
              rw [hid2]
  have hmain : G 0 ≤ (∑ t ∈ Finset.range (k+2),
      (ENNReal.ofReal (2*(k+2)))^(t+1)) * M := by
    have h := hkey (k+1) le_rfl
    rwa [show k + 1 - (k+1) = 0 from by omega] at h
  have hfinal : (∑ t ∈ Finset.range (k+2), (ENNReal.ofReal (2*(k+2)))^(t+1)) * M
      ≤ ENNReal.ofReal (((2*(k+2))^(k+2) * (k+2) * (n:ℝ)^(k+1) * Pf) * B) := by
    rw [hMdef]
    have h1 : ∑ t ∈ Finset.range (k+2), (ENNReal.ofReal (2*(k+2)))^(t+1)
        ≤ ENNReal.ofReal (((k+2 : ℝ)) * (2*(k+2) : ℝ)^(k+2)) := by
      have h2 : ∑ t ∈ Finset.range (k+2), (ENNReal.ofReal (2*(k+2)))^(t+1)
          = ENNReal.ofReal (∑ t ∈ Finset.range (k+2), (2*(k+2) : ℝ)^(t+1)) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun t _ => by positivity)]
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ 2*(k+2))]
      rw [h2]
      refine ENNReal.ofReal_le_ofReal ?_
      calc ∑ t ∈ Finset.range (k+2), (2*(k+2) : ℝ)^(t+1)
          ≤ ∑ _t ∈ Finset.range (k+2), (2*(k+2) : ℝ)^(k+2) := by
            refine Finset.sum_le_sum fun t ht => ?_
            rw [Finset.mem_range] at ht
            exact pow_le_pow_right₀
              (show (1:ℝ) ≤ 2*(k+2) by have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k; linarith)
              (by omega)
        _ = ((k+2 : ℝ)) * (2*(k+2) : ℝ)^(k+2) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            push_cast; ring
    calc (∑ t ∈ Finset.range (k+2), (ENNReal.ofReal (2*(k+2)))^(t+1))
            * ENNReal.ofReal (((n:ℝ)^(k+1)) * Pf * B)
        ≤ ENNReal.ofReal (((k+2 : ℝ)) * (2*(k+2) : ℝ)^(k+2))
            * ENNReal.ofReal (((n:ℝ)^(k+1)) * Pf * B) :=
          mul_le_mul_of_nonneg_right h1 bot_le
      _ = ENNReal.ofReal (((2*(k+2))^(k+2) * (k+2) * (n:ℝ)^(k+1) * Pf) * B) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  exact le_trans (le_of_eq hG0.symm) (le_trans hmain hfinal)

/-! ## The localised interior Cauchy estimate -/

theorem holderNorm_le_sup_of_holomorphic_open {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ}
    {ρi ρo : Fin n → ℝ} (hmono : ∀ j, ρi j < ρo j) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : (Fin n → ℂ) → ℂ,
      ContDiffOn ℝ ((k + 1 : ℕ) : ℕ∞) h (Work.CR.Flat.polydisc c ρo) →
      (∀ j, ∀ z ∈ Work.CR.Flat.polydisc c ρo, Work.CR.Flat.dbarCoord j h z = 0) →
      Work.CR.Flat.holderNorm (k + 1) α h (Work.CR.Flat.polydisc c ρi)
        ≤ ENNReal.ofReal C *
          (⨆ z ∈ Work.CR.Flat.polydisc c ρo, ENNReal.ofReal ‖h z‖) := by
  obtain ⟨C, hCpos, hC⟩ := holderNorm_le_sup_of_holomorphic_bound (n := n) hn hmono hα hα1 k
  refine ⟨C, hCpos, ?_⟩
  intro h hsmooth hhol
  set S : ℝ≥0∞ := ⨆ z ∈ polydisc c ρo, ENNReal.ofReal ‖h z‖ with hS
  rcases eq_or_ne S ⊤ with hStop | hSne
  · have hmul : (ENNReal.ofReal C * S : ℝ≥0∞) = ⊤ := by
      rw [hStop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hCpos).ne']
    rw [hmul]
    exact le_top
  · have hBnn : 0 ≤ S.toReal := ENNReal.toReal_nonneg
    have hSb : ENNReal.ofReal S.toReal = S := ENNReal.ofReal_toReal hSne
    have hbnd : ∀ z ∈ polydisc c ρo, ‖h z‖ ≤ S.toReal := by
      intro z hz
      have h1 : ENNReal.ofReal ‖h z‖ ≤ S := by
        rw [hS]
        exact le_iSup_of_le z (le_iSup_of_le hz le_rfl)
      rw [← hSb] at h1
      exact (ENNReal.ofReal_le_ofReal_iff hBnn).mp h1
    have hbound := hC h S.toReal hBnn hsmooth hhol hbnd
    rw [ENNReal.ofReal_mul (le_of_lt hCpos), hSb] at hbound
    exact hbound

end Work.CR.Flat.Cauchy
