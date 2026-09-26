import Mathlib
import Submission.Work.Drive.qwDefs
import Submission.Work.Drive.tangencyBadSet
import Submission.Commons.Analysis.CrossProduct.cross3_contDiff
import Submission.Commons.Analysis.CrossProduct.cross3_eq_zero_iff_smul
import Submission.CollinearityMap
import Submission.Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv

/-!
# The rank of the augmented derivative at a window with vanishing chord–tangent defect

This module proves `Work.Drive.rank_triplet_Xa`, the rank lemma consumed by the
quadrisecant-isolation genericity argument of `Work.Drive.qwDefs` (the map `qPsi2`).

Let `r` be a smooth knot, `c` a coefficient and `τ = (a,z,w,b)` a window at which the four points
`r a, r z, r w, r b` are collinear with `qV = β • qU`, `qS = γ • qU` and `β ≠ γ`, and suppose that
the coefficient directions realize every prescribed quadruple of values at the four window
parameters (`hsurj`).  Assume the chord–tangent defect at `a` vanishes (`qXa = 0`), the velocity at
`a` is nonzero and the curvature there does not vanish.  Then the derivative of
`p ↦ (triplet r p, qXa r p)` has rank at least `5`.

The proof exhibits five independent tangent directions:

* the *coefficient* directions: since the four point-evaluations at the window parameters are
  jointly surjective (`valLin4`, `hsurj`), a linear section `g` of that evaluation map
  (`LinearMap.exists_rightInverse_of_surjective`) prescribes independently the coefficient
  derivatives of `qU`, `qV` and `qS`.  Writing `x := dV - β dU`, `y := dS - γ dU`,
  `z := β dS - γ dV`, the derivative of `triplet` is
  `(qU × x, qU × y, qU × z)` (see `fderiv_triplet_coeff`), so the two slot directions
  `slotDir g 2` and `slotDir g 3` produce entries whose first two components are `qU × w.1` and
  `qU × w.2.1`.  This is exactly the four-dimensional image
  `{(x,y,z) ∈ (qU^⊥)³ : z = β y - γ x}`.
* the *window* direction `e_a` (`qEa`): at `qXa = 0` the velocity at `a` is a nonzero multiple of
  `qU`, so the `a`-partial of `triplet` vanishes (`fderiv_triplet_tauA`), while the partial of
  `qXa` is `(acceleration at a) × qU ≠ 0` (`fderiv_qXa_tauA`, `cross3_acc_ne_zero`).

The two families are independent because the first two components of the image of the triplet
recover the two `K'`-coordinates, where `K'` is a complement of the kernel `ℝ qU` of `u ↦ qU × u`.

Helper lemmas of the file (all `sorry`-free): the value functional `valLin4` and its slots, the
sections `slotDir`, the linear maps `crossUL`, the smoothness of the pieces
(`contDiff_qU/_qV/_qS/_triplet/_qXa`), the shift derivatives of `pertV`/`pertVelV`, and the
component formulas for the coefficient and window partials of `triplet` and `qXa`.
-/

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant

noncomputable section

/-! ## The value functional on the four window parameters -/

/-- The linear map evaluating a coefficient vector at the four window parameters. -/
def valLin4 (τ : QP) : Coeff →ₗ[ℝ] (Fin 4 → Space) :=
  LinearMap.pi (fun i : Fin 4 => linSum (fun j : Fin 9 => trigBasis j (qtp τ i)))

lemma valLin4_apply (τ : QP) (dc : Coeff) (i : Fin 4) :
    valLin4 τ dc i = (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))) dc :=
  LinearMap.pi_apply _ _ _

/-- The four point-evaluations are jointly surjective, hence so is `valLin4`. -/
lemma valLin4_surjective {τ : QP}
    (hsurj : Function.Surjective fun dc : Coeff => fun i : Fin 4 =>
      (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))) dc) :
    Function.Surjective (valLin4 τ) := fun v => hsurj v

lemma valLin4_zero (τ : QP) (dc : Coeff) :
    valLin4 τ dc 0 = (linSum (fun j : Fin 9 => trigBasis j (qA τ))) dc := by
  rw [valLin4_apply]; simp

lemma valLin4_one (τ : QP) (dc : Coeff) :
    valLin4 τ dc 1 = (linSum (fun j : Fin 9 => trigBasis j (qZ τ))) dc := by
  rw [valLin4_apply]; simp

lemma valLin4_two (τ : QP) (dc : Coeff) :
    valLin4 τ dc 2 = (linSum (fun j : Fin 9 => trigBasis j (qW τ))) dc := by
  rw [valLin4_apply]; simp

lemma valLin4_three (τ : QP) (dc : Coeff) :
    valLin4 τ dc 3 = (linSum (fun j : Fin 9 => trigBasis j (qB τ))) dc := by
  rw [valLin4_apply]; simp

/-! ## The slot directions -/

/-- The `i`-th coordinate slot `Space → (Fin 4 → Space)`. -/
def slotLin (i : Fin 4) : Space →ₗ[ℝ] (Fin 4 → Space) :=
  LinearMap.single ℝ (fun _ : Fin 4 => Space) i

/-- The coefficient direction realizing the value `p` in the `i`-th window slot, and `0` in the
other three. -/
def slotDir (g : (Fin 4 → Space) →ₗ[ℝ] Coeff) (i : Fin 4) : Space →ₗ[ℝ] Coeff :=
  g.comp (slotLin i)

lemma slotDir_apply (g : (Fin 4 → Space) →ₗ[ℝ] Coeff) (i : Fin 4) (p : Space) :
    slotDir g i p = g (slotLin i p) := rfl

lemma valLin4_slotDir {τ : QP} {g : (Fin 4 → Space) →ₗ[ℝ] Coeff}
    (hg : (valLin4 τ).comp g = LinearMap.id) (i : Fin 4) (p : Space) :
    valLin4 τ (slotDir g i p) = Pi.single i p := by
  rw [slotDir_apply, ← LinearMap.comp_apply, hg, LinearMap.id_apply, slotLin,
    LinearMap.single_apply]

lemma linSum_qA_slot2 (τ : QP) {g : (Fin 4 → Space) →ₗ[ℝ] Coeff}
    (hg : (valLin4 τ).comp g = LinearMap.id) (p : Space) :
    (linSum (fun j : Fin 9 => trigBasis j (qA τ))) (slotDir g 2 p) = 0 := by
  rw [← valLin4_zero τ (slotDir g 2 p), valLin4_slotDir hg,
    Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 2)]

lemma linSum_qZ_slot2 (τ : QP) {g : (Fin 4 → Space) →ₗ[ℝ] Coeff}
    (hg : (valLin4 τ).comp g = LinearMap.id) (p : Space) :
    (linSum (fun j : Fin 9 => trigBasis j (qZ τ))) (slotDir g 2 p) = 0 := by
  rw [← valLin4_one τ (slotDir g 2 p), valLin4_slotDir hg,
    Pi.single_eq_of_ne (by decide : (1 : Fin 4) ≠ 2)]

lemma linSum_qW_slot2 (τ : QP) {g : (Fin 4 → Space) →ₗ[ℝ] Coeff}
    (hg : (valLin4 τ).comp g = LinearMap.id) (p : Space) :
    (linSum (fun j : Fin 9 => trigBasis j (qW τ))) (slotDir g 2 p) = p := by
  rw [← valLin4_two τ (slotDir g 2 p), valLin4_slotDir hg, Pi.single_eq_same]

lemma linSum_qB_slot2 (τ : QP) {g : (Fin 4 → Space) →ₗ[ℝ] Coeff}
    (hg : (valLin4 τ).comp g = LinearMap.id) (p : Space) :
    (linSum (fun j : Fin 9 => trigBasis j (qB τ))) (slotDir g 2 p) = 0 := by
  rw [← valLin4_three τ (slotDir g 2 p), valLin4_slotDir hg,
    Pi.single_eq_of_ne (by decide : (3 : Fin 4) ≠ 2)]

lemma linSum_qA_slot3 (τ : QP) {g : (Fin 4 → Space) →ₗ[ℝ] Coeff}
    (hg : (valLin4 τ).comp g = LinearMap.id) (p : Space) :
    (linSum (fun j : Fin 9 => trigBasis j (qA τ))) (slotDir g 3 p) = 0 := by
  rw [← valLin4_zero τ (slotDir g 3 p), valLin4_slotDir hg,
    Pi.single_eq_of_ne (by decide : (0 : Fin 4) ≠ 3)]

lemma linSum_qZ_slot3 (τ : QP) {g : (Fin 4 → Space) →ₗ[ℝ] Coeff}
    (hg : (valLin4 τ).comp g = LinearMap.id) (p : Space) :
    (linSum (fun j : Fin 9 => trigBasis j (qZ τ))) (slotDir g 3 p) = 0 := by
  rw [← valLin4_one τ (slotDir g 3 p), valLin4_slotDir hg,
    Pi.single_eq_of_ne (by decide : (1 : Fin 4) ≠ 3)]

lemma linSum_qW_slot3 (τ : QP) {g : (Fin 4 → Space) →ₗ[ℝ] Coeff}
    (hg : (valLin4 τ).comp g = LinearMap.id) (p : Space) :
    (linSum (fun j : Fin 9 => trigBasis j (qW τ))) (slotDir g 3 p) = 0 := by
  rw [← valLin4_two τ (slotDir g 3 p), valLin4_slotDir hg,
    Pi.single_eq_of_ne (by decide : (2 : Fin 4) ≠ 3)]

lemma linSum_qB_slot3 (τ : QP) {g : (Fin 4 → Space) →ₗ[ℝ] Coeff}
    (hg : (valLin4 τ).comp g = LinearMap.id) (p : Space) :
    (linSum (fun j : Fin 9 => trigBasis j (qB τ))) (slotDir g 3 p) = p := by
  rw [← valLin4_three τ (slotDir g 3 p), valLin4_slotDir hg, Pi.single_eq_same]

/-! ## The cross-product map `u ↦ U × u` and its rank -/

/-- The linear map `u ↦ U × u`. -/
def crossUL (U : Space) : Space →ₗ[ℝ] Space where
  toFun := fun u => cross3 U u
  map_add' := fun u v => cross3_add_right U u v
  map_smul' := fun c u => cross3_smul_right c U u

lemma crossUL_apply (U u : Space) : crossUL U u = cross3 U u := rfl

lemma ker_crossUL {U : Space} (hU : U ≠ 0) :
    LinearMap.ker (crossUL U) = Submodule.span ℝ ({U} : Set Space) := by
  ext u
  simp only [LinearMap.mem_ker, crossUL_apply, Submodule.mem_span_singleton]
  rw [cross3_eq_zero_iff_smul_local U u]
  constructor
  · rintro (h | ⟨t, ht⟩)
    · exact absurd h hU
    · exact ⟨t, ht.symm⟩
  · rintro ⟨t, ht⟩
    exact Or.inr ⟨t, ht.symm⟩

lemma finrank_ker_crossUL {U : Space} (hU : U ≠ 0) :
    Module.finrank ℝ (LinearMap.ker (crossUL U)) = 1 := by
  rw [ker_crossUL hU]
  exact finrank_span_singleton hU

lemma finrank_range_crossUL {U : Space} (hU : U ≠ 0) :
    Module.finrank ℝ (LinearMap.range (crossUL U)) = 2 := by
  have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
  have h2 := LinearMap.finrank_range_add_finrank_ker (crossUL U)
  rw [finrank_ker_crossUL hU, hdim] at h2
  omega

/-- If the velocity `T` at the first point is parallel to the chord `U` (and both are nonzero),
then the acceleration `A` is not parallel to `U`: `A × U ≠ 0`. -/
lemma cross3_acc_ne_zero {T U A : Space} (hT : T ≠ 0) (hU : U ≠ 0)
    (hTU : cross3 T U = 0) (hTA : cross3 T A ≠ 0) : cross3 A U ≠ 0 := by
  rw [cross3_eq_zero_iff_smul_local T U] at hTU
  rcases hTU with h | ⟨t, ht⟩
  · exact absurd h hT
  · have ht0 : t ≠ 0 := by
      intro h0
      rw [h0, zero_smul] at ht
      exact hU ht
    intro hc
    rw [ht, cross3_smul_right, cross3_anticomm T A] at hc
    rcases smul_eq_zero.mp hc with h1 | h2
    · exact ht0 h1
    · exact hTA (neg_eq_zero.mp h2)

/-! ## Smoothness of the pieces -/

lemma contDiff_cross3_pair :
    ContDiff ℝ ⊤ (fun p : Space × Space => cross3 p.1 p.2) :=
  Commons.Analysis.CrossProduct.cross3_contDiff

lemma contDiff_pertV_slice {r : ℝ → Space} (hr : IsSmoothKnot r) (c : Coeff) :
    ContDiff ℝ ⊤ (pertV r c) := by
  have hfun : pertV r c = (fun t : ℝ => r t + perturbCorr (eCoeff c) t) := rfl
  rw [hfun]
  exact hr.smooth.add (contDiff_perturbCorr (eCoeff c))

lemma deriv_pertV_eq {r : ℝ → Space} (hr : IsSmoothKnot r) (c : Coeff) :
    deriv (pertV r c) = pertVelV r c :=
  deriv_perturb hr.smooth (eCoeff c)

lemma contDiff_pertVelV_slice {r : ℝ → Space} (hr : IsSmoothKnot r) (c : Coeff) :
    ContDiff ℝ ⊤ (pertVelV r c) := by
  rw [← deriv_pertV_eq hr c]
  exact (contDiff_pertV_slice hr c).deriv' (n := ⊤)

lemma contDiff_qU {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ContDiff ℝ ⊤ (fun p : Coeff × QP => qU r p) := by
  have h1 : ContDiff ℝ ⊤ (fun p : Coeff × QP => pertV r p.1 (qZ p.2)) :=
    (contDiff_pertV_joint hr.smooth).comp
      (contDiff_fst.prodMk (contDiff_qZ.comp contDiff_snd))
  have h2 : ContDiff ℝ ⊤ (fun p : Coeff × QP => pertV r p.1 (qA p.2)) :=
    (contDiff_pertV_joint hr.smooth).comp
      (contDiff_fst.prodMk (contDiff_qA.comp contDiff_snd))
  have h3 : (fun p : Coeff × QP => qU r p)
      = fun p : Coeff × QP => pertV r p.1 (qZ p.2) - pertV r p.1 (qA p.2) := by
    funext p; simp [qU, qPZ, qPA]
  rw [h3]
  exact h1.sub h2

lemma contDiff_qV {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ContDiff ℝ ⊤ (fun p : Coeff × QP => qV r p) := by
  have h1 : ContDiff ℝ ⊤ (fun p : Coeff × QP => pertV r p.1 (qW p.2)) :=
    (contDiff_pertV_joint hr.smooth).comp
      (contDiff_fst.prodMk (contDiff_qW.comp contDiff_snd))
  have h2 : ContDiff ℝ ⊤ (fun p : Coeff × QP => pertV r p.1 (qA p.2)) :=
    (contDiff_pertV_joint hr.smooth).comp
      (contDiff_fst.prodMk (contDiff_qA.comp contDiff_snd))
  have h3 : (fun p : Coeff × QP => qV r p)
      = fun p : Coeff × QP => pertV r p.1 (qW p.2) - pertV r p.1 (qA p.2) := by
    funext p; simp [qV, qPW, qPA]
  rw [h3]
  exact h1.sub h2

lemma contDiff_qS {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ContDiff ℝ ⊤ (fun p : Coeff × QP => qS r p) := by
  have h1 : ContDiff ℝ ⊤ (fun p : Coeff × QP => pertV r p.1 (qB p.2)) :=
    (contDiff_pertV_joint hr.smooth).comp
      (contDiff_fst.prodMk (contDiff_qB.comp contDiff_snd))
  have h2 : ContDiff ℝ ⊤ (fun p : Coeff × QP => pertV r p.1 (qA p.2)) :=
    (contDiff_pertV_joint hr.smooth).comp
      (contDiff_fst.prodMk (contDiff_qA.comp contDiff_snd))
  have h3 : (fun p : Coeff × QP => qS r p)
      = fun p : Coeff × QP => pertV r p.1 (qB p.2) - pertV r p.1 (qA p.2) := by
    funext p; simp [qS, qPB, qPA]
  rw [h3]
  exact h1.sub h2

lemma contDiff_triplet {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ContDiff ℝ ⊤ (fun p : Coeff × QP => triplet r p) := by
  have hc := contDiff_cross3_pair
  have hUV : ContDiff ℝ ⊤ (fun p : Coeff × QP => (qU r p, qV r p)) :=
    (contDiff_qU hr).prodMk (contDiff_qV hr)
  have hUS : ContDiff ℝ ⊤ (fun p : Coeff × QP => (qU r p, qS r p)) :=
    (contDiff_qU hr).prodMk (contDiff_qS hr)
  have hVS : ContDiff ℝ ⊤ (fun p : Coeff × QP => (qV r p, qS r p)) :=
    (contDiff_qV hr).prodMk (contDiff_qS hr)
  have h := (hc.comp hUV).prodMk ((hc.comp hUS).prodMk (hc.comp hVS))
  simpa [triplet, Function.comp_def] using h

lemma contDiff_qXa {r : ℝ → Space} (hr : IsSmoothKnot r) :
    ContDiff ℝ ⊤ (fun p : Coeff × QP => qXa r p) := by
  have h1 : ContDiff ℝ ⊤ (fun p : Coeff × QP => pertVelV r p.1 (qA p.2)) :=
    (contDiff_pertVelV_joint hr.smooth).comp
      (contDiff_fst.prodMk (contDiff_qA.comp contDiff_snd))
  have h := (contDiff_cross3_pair.comp (h1.prodMk (contDiff_qU hr)))
  simpa [qXa, Function.comp_def] using h

/-! ## The window-parameter direction `e_a` and the coordinate shifts -/

/-- The unit vector of the `a`-coordinate of the window space. -/
def qEa : QP := qPar 1 0 0 0

@[simp] lemma qA_qEa : qA qEa = 1 := by simp [qEa]
@[simp] lemma qZ_qEa : qZ qEa = 0 := by simp [qEa]
@[simp] lemma qW_qEa : qW qEa = 0 := by simp [qEa]
@[simp] lemma qB_qEa : qB qEa = 0 := by simp [qEa]

lemma qA_add (τ σ : QP) : qA (τ + σ) = qA τ + qA σ := by
  rw [qA_eq]; exact map_add _ _ _
lemma qA_smul (s : ℝ) (τ : QP) : qA (s • τ) = s * qA τ := by
  rw [qA_eq]; exact map_smul _ _ _
lemma qZ_add (τ σ : QP) : qZ (τ + σ) = qZ τ + qZ σ := by
  rw [qZ_eq]; exact map_add _ _ _
lemma qZ_smul (s : ℝ) (τ : QP) : qZ (s • τ) = s * qZ τ := by
  rw [qZ_eq]; exact map_smul _ _ _
lemma qW_add (τ σ : QP) : qW (τ + σ) = qW τ + qW σ := by
  rw [qW_eq]; exact map_add _ _ _
lemma qW_smul (s : ℝ) (τ : QP) : qW (s • τ) = s * qW τ := by
  rw [qW_eq]; exact map_smul _ _ _
lemma qB_add (τ σ : QP) : qB (τ + σ) = qB τ + qB σ := by
  rw [qB_eq]; exact map_add _ _ _
lemma qB_smul (s : ℝ) (τ : QP) : qB (s • τ) = s * qB τ := by
  rw [qB_eq]; exact map_smul _ _ _

/-- Adding a multiple of a slot direction in the coefficient variable. -/
lemma prod_add_smul_left (x : Coeff × QP) (s : ℝ) (dc : Coeff) :
    x + s • ((dc, (0 : QP)) : Coeff × QP) = (x.1 + s • dc, x.2) := by
  ext <;> simp

/-- Adding a multiple of the window direction. -/
lemma prod_add_smul_tau (x : Coeff × QP) (s : ℝ) :
    x + s • (((0 : Coeff), qEa) : Coeff × QP) = (x.1, x.2 + s • qEa) := by
  ext <;> simp

lemma qA_add_smul_qEa (τ : QP) (s : ℝ) : qA (τ + s • qEa) = qA τ + s := by
  rw [qA_add, qA_smul, qA_qEa, mul_one]
lemma qZ_add_smul_qEa (τ : QP) (s : ℝ) : qZ (τ + s • qEa) = qZ τ := by
  rw [qZ_add, qZ_smul, qZ_qEa, mul_zero, add_zero]
lemma qW_add_smul_qEa (τ : QP) (s : ℝ) : qW (τ + s • qEa) = qW τ := by
  rw [qW_add, qW_smul, qW_qEa, mul_zero, add_zero]
lemma qB_add_smul_qEa (τ : QP) (s : ℝ) : qB (τ + s • qEa) = qB τ := by
  rw [qB_add, qB_smul, qB_qEa, mul_zero, add_zero]

/-! ## Shift derivatives of the perturbed curve -/

lemma hasDerivAt_pertV_shift {r : ℝ → Space} (hr : IsSmoothKnot r) (c : Coeff) (a : ℝ) :
    HasDerivAt (fun s : ℝ => pertV r c (a + s)) (pertVelV r c a) 0 := by
  have hd : DifferentiableAt ℝ (pertV r c) a :=
    ((contDiff_pertV_slice hr c).differentiable (by simp)).differentiableAt
  have hd' : HasDerivAt (pertV r c) (deriv (pertV r c) a) (a + 0) := by
    rw [add_zero]; exact hd.hasDerivAt
  have h := hd'.comp_const_add a 0
  rw [deriv_pertV_eq hr c] at h
  simpa using h

lemma hasDerivAt_pertVelV_shift {r : ℝ → Space} (hr : IsSmoothKnot r) (c : Coeff) (a : ℝ) :
    HasDerivAt (fun s : ℝ => pertVelV r c (a + s)) (deriv (pertVelV r c) a) 0 := by
  have hd : DifferentiableAt ℝ (pertVelV r c) a :=
    ((contDiff_pertVelV_slice hr c).differentiable (by simp)).differentiableAt
  have hd' : HasDerivAt (pertVelV r c) (deriv (pertVelV r c) a) (a + 0) := by
    rw [add_zero]; exact hd.hasDerivAt
  have h := hd'.comp_const_add a 0
  simpa using h

/-! ## The window-parameter derivative of the triplet -/

lemma hasDerivAt_qU_tauA (r : ℝ → Space) (hr : IsSmoothKnot r) (c : Coeff) (τ : QP) :
    HasDerivAt (fun s : ℝ => qU r (c, τ + s • qEa)) (-(pertVelV r c (qA τ))) 0 := by
  have hconst : HasDerivAt (fun _ : ℝ => pertV r c (qZ τ)) (0 : Space) 0 :=
    hasDerivAt_const 0 _
  have hshift := hasDerivAt_pertV_shift hr c (qA τ)
  have hmain : HasDerivAt (fun s : ℝ => pertV r c (qZ τ) - pertV r c (qA τ + s))
      (0 - pertVelV r c (qA τ)) 0 := hconst.sub hshift
  rw [show (0 : Space) - pertVelV r c (qA τ) = -(pertVelV r c (qA τ)) by simp] at hmain
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards with s
  simp [qU, qPZ, qPA, qZ_add_smul_qEa, qA_add_smul_qEa]

lemma hasDerivAt_qV_tauA (r : ℝ → Space) (hr : IsSmoothKnot r) (c : Coeff) (τ : QP) :
    HasDerivAt (fun s : ℝ => qV r (c, τ + s • qEa)) (-(pertVelV r c (qA τ))) 0 := by
  have hconst : HasDerivAt (fun _ : ℝ => pertV r c (qW τ)) (0 : Space) 0 :=
    hasDerivAt_const 0 _
  have hshift := hasDerivAt_pertV_shift hr c (qA τ)
  have hmain : HasDerivAt (fun s : ℝ => pertV r c (qW τ) - pertV r c (qA τ + s))
      (0 - pertVelV r c (qA τ)) 0 := hconst.sub hshift
  rw [show (0 : Space) - pertVelV r c (qA τ) = -(pertVelV r c (qA τ)) by simp] at hmain
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards with s
  simp [qV, qPW, qPA, qW_add_smul_qEa, qA_add_smul_qEa]

lemma hasDerivAt_qS_tauA (r : ℝ → Space) (hr : IsSmoothKnot r) (c : Coeff) (τ : QP) :
    HasDerivAt (fun s : ℝ => qS r (c, τ + s • qEa)) (-(pertVelV r c (qA τ))) 0 := by
  have hconst : HasDerivAt (fun _ : ℝ => pertV r c (qB τ)) (0 : Space) 0 :=
    hasDerivAt_const 0 _
  have hshift := hasDerivAt_pertV_shift hr c (qA τ)
  have hmain : HasDerivAt (fun s : ℝ => pertV r c (qB τ) - pertV r c (qA τ + s))
      (0 - pertVelV r c (qA τ)) 0 := hconst.sub hshift
  rw [show (0 : Space) - pertVelV r c (qA τ) = -(pertVelV r c (qA τ)) by simp] at hmain
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards with s
  simp [qS, qPB, qPA, qB_add_smul_qEa, qA_add_smul_qEa]

/-- The zero of a triple, written as an explicit triple. -/
lemma zero_triple : (((0 : Space), (0 : Space), (0 : Space)) : Space × Space × Space) = 0 := rfl

/-- The `a`-direction derivative of the triplet vanishes when the velocity at `a` is parallel to
the chord `qU`. -/
lemma triplet_tau_a_zero {T U V S : Space} {β γ : ℝ} (hUV : V = β • U) (hUS : S = γ • U)
    (hTU : cross3 T U = 0) :
    (cross3 (-T) V + cross3 U (-T), cross3 (-T) S + cross3 U (-T),
      cross3 (-T) S + cross3 V (-T))
      = (((0 : Space), (0 : Space), (0 : Space)) : Space × Space × Space) := by
  have hd : cross3 U T = -cross3 T U := cross3_anticomm T U
  have e1 : cross3 (-T) V + cross3 U (-T) = (0 : Space) := by
    rw [hUV, cross3_neg_left, cross3_smul_right, cross3_neg_right, hd, hTU]
    simp
  have e2 : cross3 (-T) S + cross3 U (-T) = (0 : Space) := by
    rw [hUS, cross3_neg_left, cross3_smul_right, cross3_neg_right, hd, hTU]
    simp
  have e3 : cross3 (-T) S + cross3 V (-T) = (0 : Space) := by
    rw [hUS, hUV, cross3_neg_left, cross3_neg_right, cross3_smul_left, cross3_smul_right,
      hd, hTU]
    simp
  rw [e1, e2, e3]

lemma hasDerivAt_triplet_tauA {r : ℝ → Space} (hr : IsSmoothKnot r) {c : Coeff} {τ : QP}
    {β γ : ℝ} (hv : qV r (c, τ) = β • qU r (c, τ)) (hs : qS r (c, τ) = γ • qU r (c, τ))
    (hXa : qXa r (c, τ) = 0) :
    HasDerivAt (fun s : ℝ => triplet r (c, τ + s • qEa)) 0 0 := by
  have hU := hasDerivAt_qU_tauA r hr c τ
  have hV := hasDerivAt_qV_tauA r hr c τ
  have hS := hasDerivAt_qS_tauA r hr c τ
  have hprod := (hasDerivAt_cross3_curves _ _ hU hV).prodMk
    ((hasDerivAt_cross3_curves _ _ hU hS).prodMk (hasDerivAt_cross3_curves _ _ hV hS))
  have hXa' : cross3 (pertVelV r c (qA τ)) (qU r (c, τ)) = 0 := hXa
  have hqu : qU r (c, τ + (0 : ℝ) • qEa) = qU r (c, τ) := by simp
  have hqv : qV r (c, τ + (0 : ℝ) • qEa) = qV r (c, τ) := by simp
  have hqs : qS r (c, τ + (0 : ℝ) • qEa) = qS r (c, τ) := by simp
  have hval : (cross3 (-(pertVelV r c (qA τ))) (qV r (c, τ + (0 : ℝ) • qEa))
        + cross3 (qU r (c, τ + (0 : ℝ) • qEa)) (-(pertVelV r c (qA τ))),
      cross3 (-(pertVelV r c (qA τ))) (qS r (c, τ + (0 : ℝ) • qEa))
        + cross3 (qU r (c, τ + (0 : ℝ) • qEa)) (-(pertVelV r c (qA τ))),
      cross3 (-(pertVelV r c (qA τ))) (qS r (c, τ + (0 : ℝ) • qEa))
        + cross3 (qV r (c, τ + (0 : ℝ) • qEa)) (-(pertVelV r c (qA τ))))
      = (0 : Space × Space × Space) := by
    rw [hqu, hqv, hqs]
    rw [triplet_tau_a_zero hv hs hXa', zero_triple]
  rw [hval] at hprod
  refine hprod.congr_of_eventuallyEq ?_
  filter_upwards with s
  simp [triplet]

lemma fderiv_triplet_tauA {r : ℝ → Space} (hr : IsSmoothKnot r) {c : Coeff} {τ : QP}
    {β γ : ℝ} (hv : qV r (c, τ) = β • qU r (c, τ)) (hs : qS r (c, τ) = γ • qU r (c, τ))
    (hXa : qXa r (c, τ) = 0) :
    (fderiv ℝ (fun p : Coeff × QP => triplet r p) (c, τ)) (0, qEa) = 0 := by
  have hdiff : DifferentiableAt ℝ (fun p : Coeff × QP => triplet r p) (c, τ) :=
    ((contDiff_triplet hr).differentiable (by simp)).differentiableAt
  have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := fun p : Coeff × QP => triplet r p) (p := (c, τ)) (e := ((0 : Coeff), qEa)) hdiff
  refine h1.unique ?_
  have h2 : HasDerivAt
      (fun s : ℝ => (fun p : Coeff × QP => triplet r p)
        ((c, τ) + s • (((0 : Coeff), qEa) : Coeff × QP))) 0 0 := by
    refine (hasDerivAt_triplet_tauA hr hv hs hXa).congr_of_eventuallyEq ?_
    filter_upwards with s
    rw [prod_add_smul_tau]
  exact h2

lemma fderiv_triplet_tauA_smul {r : ℝ → Space} (hr : IsSmoothKnot r) {c : Coeff} {τ : QP}
    {β γ : ℝ} (hv : qV r (c, τ) = β • qU r (c, τ)) (hs : qS r (c, τ) = γ • qU r (c, τ))
    (hXa : qXa r (c, τ) = 0) (s : ℝ) :
    (fderiv ℝ (fun p : Coeff × QP => triplet r p) (c, τ)) (0, s • qEa) = 0 := by
  rw [show (((0 : Coeff), s • qEa) : Coeff × QP) = s • (((0 : Coeff), qEa) : Coeff × QP) by
        ext <;> simp,
    map_smul, fderiv_triplet_tauA hr hv hs hXa, smul_zero]

/-! ## The window-parameter derivative of `qXa` -/

lemma hasDerivAt_qXa_tauA (r : ℝ → Space) (hr : IsSmoothKnot r) (c : Coeff) (τ : QP) :
    HasDerivAt (fun s : ℝ => qXa r (c, τ + s • qEa))
      (cross3 (deriv (pertVelV r c) (qA τ)) (qU r (c, τ))) 0 := by
  have hfun : (fun s : ℝ => qXa r (c, τ + s • qEa))
      = fun s : ℝ => cross3 (pertVelV r c (qA τ + s)) (qU r (c, τ + s • qEa)) := by
    funext s
    simp [qXa, qA_add_smul_qEa]
  rw [hfun]
  have h1 := hasDerivAt_pertVelV_shift hr c (qA τ)
  have h2 := hasDerivAt_qU_tauA r hr c τ
  have h3 := hasDerivAt_cross3_curves _ _ h1 h2
  refine h3.congr_deriv ?_
  simp [cross3_neg_right, cross3_self]

lemma fderiv_qXa_tauA (r : ℝ → Space) (hr : IsSmoothKnot r) (c : Coeff) (τ : QP) :
    (fderiv ℝ (fun p : Coeff × QP => qXa r p) (c, τ)) (0, qEa)
      = cross3 (deriv (pertVelV r c) (qA τ)) (qU r (c, τ)) := by
  have hdiff : DifferentiableAt ℝ (fun p : Coeff × QP => qXa r p) (c, τ) :=
    ((contDiff_qXa hr).differentiable (by simp)).differentiableAt
  have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := fun p : Coeff × QP => qXa r p) (p := (c, τ)) (e := ((0 : Coeff), qEa)) hdiff
  refine h1.unique ?_
  have h2 : HasDerivAt
      (fun s : ℝ => (fun p : Coeff × QP => qXa r p)
        ((c, τ) + s • (((0 : Coeff), qEa) : Coeff × QP)))
      (cross3 (deriv (pertVelV r c) (qA τ)) (qU r (c, τ))) 0 := by
    refine (hasDerivAt_qXa_tauA r hr c τ).congr_of_eventuallyEq ?_
    filter_upwards with s
    simp
  exact h2

lemma fderiv_qXa_tauA_smul (r : ℝ → Space) (hr : IsSmoothKnot r) (c : Coeff) (τ : QP)
    (s : ℝ) :
    (fderiv ℝ (fun p : Coeff × QP => qXa r p) (c, τ)) (0, s • qEa)
      = s • cross3 (deriv (pertVelV r c) (qA τ)) (qU r (c, τ)) := by
  rw [show (((0 : Coeff), s • qEa) : Coeff × QP) = s • (((0 : Coeff), qEa) : Coeff × QP) by
        ext <;> simp,
    map_smul, fderiv_qXa_tauA r hr c τ]

/-! ## The coefficient-line derivative of the triplet -/

lemma hasDerivAt_pertV_line (r : ℝ → Space) (t : ℝ) (c dc : Coeff) :
    HasDerivAt (fun s : ℝ => pertV r (c + s • dc) t)
      ((linSum (fun j : Fin 9 => trigBasis j t)) dc) 0 := by
  have hdiff : DifferentiableAt ℝ (fun c : Coeff => pertV r c t) c :=
    (hasFDerivAt_pertV_slice r t c).differentiableAt
  have h := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := fun c : Coeff => pertV r c t) (p := c) (e := dc) hdiff
  rwa [(hasFDerivAt_pertV_slice r t c).fderiv] at h

lemma hasDerivAt_qU_coeff (r : ℝ → Space) (x : Coeff × QP) (dc : Coeff) :
    HasDerivAt (fun s : ℝ => qU r (x.1 + s • dc, x.2))
      ((linSum (fun j : Fin 9 => trigBasis j (qZ x.2))) dc -
        (linSum (fun j : Fin 9 => trigBasis j (qA x.2))) dc) 0 := by
  have h1 := hasDerivAt_pertV_line r (qZ x.2) x.1 dc
  have h2 := hasDerivAt_pertV_line r (qA x.2) x.1 dc
  refine (h1.sub h2).congr_of_eventuallyEq ?_
  filter_upwards with s
  simp [qU, qPZ, qPA]

lemma hasDerivAt_qV_coeff (r : ℝ → Space) (x : Coeff × QP) (dc : Coeff) :
    HasDerivAt (fun s : ℝ => qV r (x.1 + s • dc, x.2))
      ((linSum (fun j : Fin 9 => trigBasis j (qW x.2))) dc -
        (linSum (fun j : Fin 9 => trigBasis j (qA x.2))) dc) 0 := by
  have h1 := hasDerivAt_pertV_line r (qW x.2) x.1 dc
  have h2 := hasDerivAt_pertV_line r (qA x.2) x.1 dc
  refine (h1.sub h2).congr_of_eventuallyEq ?_
  filter_upwards with s
  simp [qV, qPW, qPA]

lemma hasDerivAt_qS_coeff (r : ℝ → Space) (x : Coeff × QP) (dc : Coeff) :
    HasDerivAt (fun s : ℝ => qS r (x.1 + s • dc, x.2))
      ((linSum (fun j : Fin 9 => trigBasis j (qB x.2))) dc -
        (linSum (fun j : Fin 9 => trigBasis j (qA x.2))) dc) 0 := by
  have h1 := hasDerivAt_pertV_line r (qB x.2) x.1 dc
  have h2 := hasDerivAt_pertV_line r (qA x.2) x.1 dc
  refine (h1.sub h2).congr_of_eventuallyEq ?_
  filter_upwards with s
  simp [qS, qPB, qPA]

/-- The coefficient-line derivative of the triplet, as an explicit triple. -/
def tripletCoeffDeriv (r : ℝ → Space) (x : Coeff × QP) (dc : Coeff) : Space × Space × Space :=
  (cross3 ((linSum (fun j : Fin 9 => trigBasis j (qZ x.2))) dc -
        (linSum (fun j : Fin 9 => trigBasis j (qA x.2))) dc) (qV r x)
      + cross3 (qU r x) ((linSum (fun j : Fin 9 => trigBasis j (qW x.2))) dc -
        (linSum (fun j : Fin 9 => trigBasis j (qA x.2))) dc),
    cross3 ((linSum (fun j : Fin 9 => trigBasis j (qZ x.2))) dc -
        (linSum (fun j : Fin 9 => trigBasis j (qA x.2))) dc) (qS r x)
      + cross3 (qU r x) ((linSum (fun j : Fin 9 => trigBasis j (qB x.2))) dc -
        (linSum (fun j : Fin 9 => trigBasis j (qA x.2))) dc),
    cross3 ((linSum (fun j : Fin 9 => trigBasis j (qW x.2))) dc -
        (linSum (fun j : Fin 9 => trigBasis j (qA x.2))) dc) (qS r x)
      + cross3 (qV r x) ((linSum (fun j : Fin 9 => trigBasis j (qB x.2))) dc -
        (linSum (fun j : Fin 9 => trigBasis j (qA x.2))) dc))

lemma hasDerivAt_triplet_coeff (r : ℝ → Space) (x : Coeff × QP) (dc : Coeff) :
    HasDerivAt (fun s : ℝ => triplet r (x.1 + s • dc, x.2)) (tripletCoeffDeriv r x dc) 0 := by
  have hU := hasDerivAt_qU_coeff r x dc
  have hV := hasDerivAt_qV_coeff r x dc
  have hS := hasDerivAt_qS_coeff r x dc
  have hprod := (hasDerivAt_cross3_curves _ _ hU hV).prodMk
    ((hasDerivAt_cross3_curves _ _ hU hS).prodMk (hasDerivAt_cross3_curves _ _ hV hS))
  have hcurve : (fun s : ℝ => triplet r (x.1 + s • dc, x.2))
      = fun s : ℝ => (cross3 (qU r (x.1 + s • dc, x.2)) (qV r (x.1 + s • dc, x.2)),
          cross3 (qU r (x.1 + s • dc, x.2)) (qS r (x.1 + s • dc, x.2)),
          cross3 (qV r (x.1 + s • dc, x.2)) (qS r (x.1 + s • dc, x.2))) := by
    funext s
    simp [triplet]
  rw [hcurve]
  simpa [tripletCoeffDeriv] using hprod

lemma fderiv_triplet_coeff {r : ℝ → Space} (hr : IsSmoothKnot r) (x : Coeff × QP)
    (dc : Coeff) :
    (fderiv ℝ (fun p : Coeff × QP => triplet r p) x) (dc, 0)
      = tripletCoeffDeriv r x dc := by
  have hdiff : DifferentiableAt ℝ (fun p : Coeff × QP => triplet r p) x :=
    ((contDiff_triplet hr).differentiable (by simp)).differentiableAt
  have h1 := Commons.Analysis.Calculus.FDeriv.fderiv_along_axis_eq_deriv
    (H := fun p : Coeff × QP => triplet r p) (p := x) (e := (dc, (0 : QP))) hdiff
  refine h1.unique ?_
  have h2 : HasDerivAt
      (fun s : ℝ => (fun p : Coeff × QP => triplet r p) (x + s • ((dc, (0 : QP)) : Coeff × QP)))
      (tripletCoeffDeriv r x dc) 0 := by
    refine (hasDerivAt_triplet_coeff r x dc).congr_of_eventuallyEq ?_
    filter_upwards with s
    rw [prod_add_smul_left]
  exact h2

/-! ## The two components of the coefficient-line derivative that we use -/

lemma fderiv_triplet_dirV_fst {r : ℝ → Space} (hr : IsSmoothKnot r) (x : Coeff × QP)
    {g : (Fin 4 → Space) →ₗ[ℝ] Coeff} (hg : (valLin4 x.2).comp g = LinearMap.id) (p : Space) :
    ((fderiv ℝ (fun q : Coeff × QP => triplet r q) x) (slotDir g 2 p, (0 : QP))).1
      = crossUL (qU r x) p := by
  rw [fderiv_triplet_coeff hr x (slotDir g 2 p), tripletCoeffDeriv]
  simp only [linSum_qA_slot2 x.2 hg p, linSum_qZ_slot2 x.2 hg p, linSum_qW_slot2 x.2 hg p,
    linSum_qB_slot2 x.2 hg p, sub_zero, sub_self, cross3_zero_left, cross3_zero_right,
    zero_add, add_zero]
  rfl

lemma fderiv_triplet_dirV_snd {r : ℝ → Space} (hr : IsSmoothKnot r) (x : Coeff × QP)
    {g : (Fin 4 → Space) →ₗ[ℝ] Coeff} (hg : (valLin4 x.2).comp g = LinearMap.id) (p : Space) :
    ((fderiv ℝ (fun q : Coeff × QP => triplet r q) x) (slotDir g 2 p, (0 : QP))).2.1 = 0 := by
  rw [fderiv_triplet_coeff hr x (slotDir g 2 p), tripletCoeffDeriv]
  simp only [linSum_qA_slot2 x.2 hg p, linSum_qZ_slot2 x.2 hg p, linSum_qW_slot2 x.2 hg p,
    linSum_qB_slot2 x.2 hg p, sub_zero, sub_self, cross3_zero_left, cross3_zero_right,
    zero_add, add_zero]

lemma fderiv_triplet_dirS_fst {r : ℝ → Space} (hr : IsSmoothKnot r) (x : Coeff × QP)
    {g : (Fin 4 → Space) →ₗ[ℝ] Coeff} (hg : (valLin4 x.2).comp g = LinearMap.id) (p : Space) :
    ((fderiv ℝ (fun q : Coeff × QP => triplet r q) x) (slotDir g 3 p, (0 : QP))).1 = 0 := by
  rw [fderiv_triplet_coeff hr x (slotDir g 3 p), tripletCoeffDeriv]
  simp only [linSum_qA_slot3 x.2 hg p, linSum_qZ_slot3 x.2 hg p, linSum_qW_slot3 x.2 hg p,
    linSum_qB_slot3 x.2 hg p, sub_zero, sub_self, cross3_zero_left, cross3_zero_right,
    zero_add, add_zero]

lemma fderiv_triplet_dirS_snd {r : ℝ → Space} (hr : IsSmoothKnot r) (x : Coeff × QP)
    {g : (Fin 4 → Space) →ₗ[ℝ] Coeff} (hg : (valLin4 x.2).comp g = LinearMap.id) (p : Space) :
    ((fderiv ℝ (fun q : Coeff × QP => triplet r q) x) (slotDir g 3 p, (0 : QP))).2.1
      = crossUL (qU r x) p := by
  rw [fderiv_triplet_coeff hr x (slotDir g 3 p), tripletCoeffDeriv]
  simp only [linSum_qA_slot3 x.2 hg p, linSum_qZ_slot3 x.2 hg p, linSum_qW_slot3 x.2 hg p,
    linSum_qB_slot3 x.2 hg p, sub_zero, sub_self, cross3_zero_left, cross3_zero_right,
    zero_add, add_zero]
  rfl

open Work.Drive LeanEval.KnotTheory.Quadrisecant in
/-- **The rank of the augmented derivative at a window with vanishing chord–tangent defect.**

Let `r` be a smooth knot, `c` a coefficient and `τ` a window at which the four points
`r a, r z, r w, r b` are collinear with chord coordinates `β ≠ γ`
(`qV = β • qU`, `qS = γ • qU`, `qU ≠ 0`), such that the coefficient directions realize every
prescribed four-tuple of values at the four window parameters (`hsurj`), and such that the
chord–tangent defect `qXa = (velocity at a) × qU` vanishes.  Assume moreover that the velocity at
`a` is non-zero and the curvature at `a` does not vanish.  Then the derivative of the augmented map
`p ↦ (triplet r p, qXa r p)` has rank at least `5`.

Mathematical content (this was verified by hand by two reviewers): the image of the derivative of
`triplet` is exactly the four-dimensional space
`V = {(x, y, z) ∈ (qU^⊥)³ : z = β y - γ x}`; at `qXa = 0` the `a`-parameter partial of the triplet
is zero, so the parameter direction `e_a` lies in the kernel of the triplet derivative, while the
derivative of `qXa` in that direction is `(acceleration at a) × qU`, which is non-zero because the
velocity at `a` is a non-zero multiple of `qU` and the curvature there does not vanish. -/
theorem rank_triplet_Xa {r : ℝ → Space} (hr : IsSmoothKnot r) {c : Coeff} {τ : QP} {β γ : ℝ}
    (hU : qU r (c, τ) ≠ 0)
    (hv : qV r (c, τ) = β • qU r (c, τ))
    (hs : qS r (c, τ) = γ • qU r (c, τ))
    (hbγ : β ≠ γ)
    (hsurj : Function.Surjective fun dc : Coeff => fun i : Fin 4 =>
      (linSum (fun j : Fin 9 => trigBasis j (qtp τ i))) dc)
    (hXa : qXa r (c, τ) = 0)
    (hreg : pertVelV r c (qA τ) ≠ 0)
    (hnoinfl : cross3 (pertVelV r c (qA τ)) (deriv (pertVelV r c) (qA τ)) ≠ 0) :
    5 ≤ Module.finrank ℝ
      (LinearMap.range
        ((fderiv ℝ (fun p : Coeff × QP => (triplet r p, qXa r p)) (c, τ)).toLinearMap)) := by
  classical
  set Uq : Space := qU r (c, τ) with hUq
  set Tv : Space := pertVelV r c (qA τ) with hTv
  set Ac : Space := deriv (pertVelV r c) (qA τ) with hAc
  have hUq' : Uq ≠ 0 := by rw [hUq]; exact hU
  have hTv' : Tv ≠ 0 := by rw [hTv]; exact hreg
  have hTU : cross3 Tv Uq = 0 := by rw [hTv, hUq]; exact hXa
  have hTA : cross3 Tv Ac ≠ 0 := by rw [hTv, hAc]; exact hnoinfl
  have hAU : cross3 Ac Uq ≠ 0 := cross3_acc_ne_zero hTv' hUq' hTU hTA
  -- the linear section of the four-point value functional
  obtain ⟨g, hg⟩ := LinearMap.exists_rightInverse_of_surjective (valLin4 τ)
    (LinearMap.range_eq_top.mpr (valLin4_surjective hsurj))
  -- the slot directions
  set dirV : Space →ₗ[ℝ] Coeff := slotDir g 2 with hdirV
  set dirS : Space →ₗ[ℝ] Coeff := slotDir g 3 with hdirS
  -- a complement of the kernel of `u ↦ Uq × u`
  obtain ⟨K', hK'⟩ := Submodule.exists_isCompl (LinearMap.ker (crossUL Uq))
  have hK'2 : Module.finrank ℝ K' = 2 := by
    have hker : Module.finrank ℝ (LinearMap.ker (crossUL Uq)) = 1 := finrank_ker_crossUL hUq'
    have hsup : LinearMap.ker (crossUL Uq) ⊔ K' = ⊤ := codisjoint_iff.mp hK'.codisjoint
    have hinf : LinearMap.ker (crossUL Uq) ⊓ K' = ⊥ := disjoint_iff.mp hK'.disjoint
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (crossUL Uq)) K'
    rw [hsup, hinf, hker, finrank_top, finrank_bot] at h1
    have hdim : Module.finrank ℝ Space = 3 := by simp [Space]
    rw [hdim] at h1
    omega
  have hK'inj : ∀ p : K', crossUL Uq (p : Space) = 0 → p = 0 := by
    intro p hp
    have hmem : (p : Space) ∈ LinearMap.ker (crossUL Uq) ⊓ K' := ⟨hp, p.2⟩
    rw [disjoint_iff.mp hK'.disjoint] at hmem
    exact Subtype.ext ((Submodule.mem_bot ℝ).mp hmem)
  -- the augmented map, its derivative, and the decomposition of the latter
  set F : Coeff × QP → (Space × Space × Space) × Space :=
    fun p => (triplet r p, qXa r p) with hF
  set D : (Coeff × QP) →ₗ[ℝ] ((Space × Space × Space) × Space) :=
    (fderiv ℝ F (c, τ)).toLinearMap with hD
  have hTdiff : DifferentiableAt ℝ (fun p : Coeff × QP => triplet r p) (c, τ) :=
    ((contDiff_triplet hr).differentiable (by simp)).differentiableAt
  have hQdiff : DifferentiableAt ℝ (fun p : Coeff × QP => qXa r p) (c, τ) :=
    ((contDiff_qXa hr).differentiable (by simp)).differentiableAt
  have hfF : fderiv ℝ F (c, τ)
      = (fderiv ℝ (fun p : Coeff × QP => triplet r p) (c, τ)).prod
        (fderiv ℝ (fun p : Coeff × QP => qXa r p) (c, τ)) := by
    rw [hF]
    exact hTdiff.fderiv_prodMk hQdiff
  have hDprod : D = (fderiv ℝ (fun p : Coeff × QP => triplet r p) (c, τ)).toLinearMap.prod
      (fderiv ℝ (fun p : Coeff × QP => qXa r p) (c, τ)).toLinearMap := by
    rw [hD, hfF]
    rfl
  have hfst : ∀ v : Coeff × QP, (D v).1
      = (fderiv ℝ (fun p : Coeff × QP => triplet r p) (c, τ)) v := by
    intro v
    rw [hDprod]
    rfl
  have hsnd : ∀ v : Coeff × QP, (D v).2
      = (fderiv ℝ (fun p : Coeff × QP => qXa r p) (c, τ)) v := by
    intro v
    rw [hDprod]
    rfl
  -- the component formulas
  have hD1 : ∀ p : Space, (D ((dirV p), (0 : QP))).1.1 = crossUL Uq p := by
    intro p
    rw [hfst, hdirV, hUq]
    exact fderiv_triplet_dirV_fst hr (c, τ) hg p
  have hD2 : ∀ p : Space, (D ((dirV p), (0 : QP))).1.2.1 = 0 := by
    intro p
    rw [hfst, hdirV]
    exact fderiv_triplet_dirV_snd hr (c, τ) hg p
  have hD3 : ∀ p : Space, (D ((dirS p), (0 : QP))).1.1 = 0 := by
    intro p
    rw [hfst, hdirS]
    exact fderiv_triplet_dirS_fst hr (c, τ) hg p
  have hD4 : ∀ p : Space, (D ((dirS p), (0 : QP))).1.2.1 = crossUL Uq p := by
    intro p
    rw [hfst, hdirS, hUq]
    exact fderiv_triplet_dirS_snd hr (c, τ) hg p
  have hD5 : ∀ s : ℝ, D (((0 : Coeff), s • qEa) : Coeff × QP)
      = ((((0 : Space), (0 : Space), (0 : Space)) : Space × Space × Space), s • cross3 Ac Uq) := by
    intro s
    refine Prod.ext ?_ ?_
    · show (D (((0 : Coeff), s • qEa) : Coeff × QP)).1 = (0 : Space × Space × Space)
      rw [hfst, fderiv_triplet_tauA_smul hr hv hs hXa s]
    · show (D (((0 : Coeff), s • qEa) : Coeff × QP)).2 = s • cross3 Ac Uq
      rw [hsnd, fderiv_qXa_tauA_smul r hr c τ s, ← hAc, ← hUq]
  -- the linear map into the range of `D`
  let fst₁ : K' × K' × ℝ →ₗ[ℝ] K' := LinearMap.fst ℝ K' (K' × ℝ)
  let snd₁ : K' × K' × ℝ →ₗ[ℝ] (K' × ℝ) := LinearMap.snd ℝ K' (K' × ℝ)
  let fst₂ : K' × ℝ →ₗ[ℝ] K' := LinearMap.fst ℝ K' ℝ
  let snd₂ : K' × ℝ →ₗ[ℝ] ℝ := LinearMap.snd ℝ K' ℝ
  let phi : K' × K' × ℝ →ₗ[ℝ] Coeff × QP :=
    ((dirV.comp K'.subtype).comp fst₁ + (dirS.comp K'.subtype).comp (fst₂.comp snd₁)).prod
      ((LinearMap.toSpanSingleton ℝ QP qEa).comp (snd₂.comp snd₁))
  have hphi : ∀ w : K' × K' × ℝ, phi w
      = (dirV (w.1 : Space) + dirS (w.2.1 : Space), w.2.2 • qEa) := by
    intro w
    simp [phi, fst₁, snd₁, fst₂, snd₂, LinearMap.toSpanSingleton]
  have hcomp1 : ∀ w : K' × K' × ℝ, (D (phi w)).1.1 = crossUL Uq (w.1 : Space) := by
    intro w
    have hsp : phi w = ((dirV (w.1 : Space), (0 : QP)) + (dirS (w.2.1 : Space), (0 : QP))
        + (((0 : Coeff), w.2.2 • qEa) : Coeff × QP)) := by
      rw [hphi]
      ext <;> simp
    have hzero : (D (((0 : Coeff), w.2.2 • qEa) : Coeff × QP)).1.1 = 0 := by
      rw [hD5 w.2.2]
    rw [hsp, map_add, map_add]
    simp only [Prod.fst_add]
    rw [hD1, hD3, hzero]
    try simp
  have hcomp2 : ∀ w : K' × K' × ℝ, (D (phi w)).1.2.1 = crossUL Uq (w.2.1 : Space) := by
    intro w
    have hsp : phi w = ((dirV (w.1 : Space), (0 : QP)) + (dirS (w.2.1 : Space), (0 : QP))
        + (((0 : Coeff), w.2.2 • qEa) : Coeff × QP)) := by
      rw [hphi]
      ext <;> simp
    have hzero : (D (((0 : Coeff), w.2.2 • qEa) : Coeff × QP)).1.2.1 = 0 := by
      rw [hD5 w.2.2]
    rw [hsp, map_add, map_add]
    simp only [Prod.fst_add, Prod.snd_add]
    rw [hD2, hD4, hzero]
    try simp
  -- the kernel of `Φ` is trivial
  have hker : ∀ w : K' × K' × ℝ, (D.comp phi) w = 0 → w = 0 := by
    intro w hw
    have hDw : D (phi w) = 0 := hw
    have hw1 : w.1 = 0 := by
      refine hK'inj w.1 ?_
      have h1 : (D (phi w)).1.1 = 0 := by rw [hDw]; rfl
      rw [hcomp1 w] at h1
      exact h1
    have hw2 : w.2.1 = 0 := by
      refine hK'inj w.2.1 ?_
      have h1 : (D (phi w)).1.2.1 = 0 := by rw [hDw]; rfl
      rw [hcomp2 w] at h1
      exact h1
    have hw3 : w.2.2 = 0 := by
      have hphiz : phi w = (((0 : Coeff), w.2.2 • qEa) : Coeff × QP) := by
        rw [hphi, hw1, hw2]
        simp
      have h4 : (D (((0 : Coeff), w.2.2 • qEa) : Coeff × QP)).2 = 0 := by
        rw [← hphiz, hDw]; rfl
      rw [hD5 w.2.2] at h4
      have h4' : w.2.2 • cross3 Ac Uq = 0 := by simpa using h4
      rcases smul_eq_zero.mp h4' with h | h
      · exact h
      · exact absurd h hAU
    exact Prod.ext hw1 (Prod.ext hw2 hw3)
  have hinj : Function.Injective (D.comp phi) := by
    intro u v huv
    have h0 : (D.comp phi) (u - v) = 0 := by rw [map_sub, huv, sub_self]
    exact sub_eq_zero.mp (hker (u - v) h0)
  have hfin : Module.finrank ℝ (K' × K' × ℝ) = 5 := by
    rw [Module.finrank_prod, Module.finrank_prod, hK'2, Module.finrank_self]
  have hrank : Module.finrank ℝ (LinearMap.range (D.comp phi))
      = Module.finrank ℝ (K' × K' × ℝ) := by
    have h := LinearMap.finrank_range_add_finrank_ker (D.comp phi)
    rw [LinearMap.ker_eq_bot.mpr hinj, finrank_bot, add_zero] at h
    exact h
  have hmono : Module.finrank ℝ (LinearMap.range (D.comp phi))
      ≤ Module.finrank ℝ (LinearMap.range D) :=
    Submodule.finrank_mono (LinearMap.range_comp_le_range phi D)
  rw [← hfin, ← hrank]
  exact hmono


end

end Work.Drive
