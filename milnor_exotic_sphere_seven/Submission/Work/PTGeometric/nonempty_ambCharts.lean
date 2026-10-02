import Mathlib
import Submission.Work.PTGeometric.AmbientPerturbation
import Submission.Work.PTGeometric.ell_apply_frame_eq
import Submission.Work.PTGeometric.existsCoordInjOnGr
import Submission.Work.PTGeometric.isInvertible_comp_adjoint_iff
import Submission.Work.PTGeometric.contMDiff_smul_of_contMDiffOn_of_tsupport_subset

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The chart family of a projection-valued map over a compact source

`Work.PTGeometric.AmbCharts n k M P m` records the data of a finite family of "Grassmannian charts"
for a projection-valued map `P : M → End(ℝⁿ)`: linear coordinates `ell l : ℝⁿ → ℝᵏ` which are
injective on the moving planes `im (P x)` over the chart `U l`, together with `ell l`-adapted smooth
frames of those planes.

This file proves `nonempty_ambCharts`: such a family always exists for a compact source `M`.  No
Hausdorff assumption on `M` is needed (the statement does not have one), so the proof does not use a
partition of unity: the cut-off used to globalise the local frames is built from the *norm of the
coordinate Gram operator*, the smoothness input being the identity
`‖A‖² ≤ ∑ i, ‖A (single i 1)‖²` for an endomorphism `A` of `ℝᵏ`.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.unusedVariables false

open scoped Manifold ContDiff
open Function Set Topology

namespace Work.PTGeometric

noncomputable section

variable {n k : ℕ}

/-! ### Elementary facts about `Amb`, `Gr` and `EuclideanSpace` -/

/-- The finrank of `ℝᵐ` (written as `Amb m = EuclideanSpace ℝ (Fin m)`). -/
theorem finrank_Amb (m : ℕ) : Module.finrank ℝ (Amb m) = m := by
  simp [finrank_euclideanSpace]

/-- **The rank of a member of the Grassmannian.**  An orthogonal projection in `Gr n k` (i.e. a
self-adjoint idempotent whose trace is `k`) has `k`-dimensional range. -/
theorem finrank_range_eq_of_mem_Gr {Q : Amb n →L[ℝ] Amb n} (hQ : Q ∈ Gr n k) :
    Module.finrank ℝ (LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n)) = k := by
  have hcomp : ∀ x : Amb n, Q (Q x) = Q x := by
    intro x
    have h : (Q * Q : Amb n →L[ℝ] Amb n) x = Q x := by rw [hQ.2.1]
    simpa using h
  have hQidem_lin : (Q : Amb n →ₗ[ℝ] Amb n) * (Q : Amb n →ₗ[ℝ] Amb n)
      = (Q : Amb n →ₗ[ℝ] Amb n) := by
    refine LinearMap.ext fun y => ?_
    rw [Module.End.mul_eq_comp, LinearMap.comp_apply]
    exact hcomp y
  have hproj : LinearMap.IsProj (LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n))
      (Q : Amb n →ₗ[ℝ] Amb n) :=
    (LinearMap.isProj_range_iff_isIdempotentElem (Q : Amb n →ₗ[ℝ] Amb n)).mpr hQidem_lin
  have h1 : LinearMap.trace ℝ (Amb n) (Q : Amb n →ₗ[ℝ] Amb n)
      = (Module.finrank ℝ (LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n)) : ℝ) := hproj.trace
  have h2 : LinearMap.trace ℝ (Amb n) (Q : Amb n →ₗ[ℝ] Amb n) = (k : ℝ) := hQ.2.2
  have h3 : (Module.finrank ℝ (LinearMap.range (Q : Amb n →ₗ[ℝ] Amb n)) : ℝ) = (k : ℝ) := by
    rw [← h1, h2]
  exact Nat.cast_injective h3

/-- The standard-basis expansion of a vector of `ℝᵏ`. -/
theorem sum_smul_single (t : Amb k) :
    (Finset.univ.sum fun j : Fin k => t j • EuclideanSpace.single j (1 : ℝ)) = t := by
  have h := (EuclideanSpace.basisFun (Fin k) ℝ).sum_repr t
  simpa [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using h

/-- **The operator norm of an endomorphism of `ℝᵏ` is bounded by the `ℓ²`-norm of its values on the
standard basis.**  This is the `k`-dimensional instance of the equivalence of norms on
`End(ℝᵏ)`; it is what lets us detect invertibility of `G x y` from a *smooth* quantity
(`∑ i, ‖(G x y - G x x) eᵢ‖²`, which is a sum of squares of inner products). -/
theorem opNorm_sq_le_sum_norm_sq (A : Amb k →L[ℝ] Amb k) :
    ‖A‖ ^ 2 ≤ ∑ i : Fin k, ‖A (EuclideanSpace.single i (1 : ℝ))‖ ^ 2 := by
  set hsq : ℝ := ∑ i : Fin k, ‖A (EuclideanSpace.single i (1:ℝ))‖^2 with hsqdef
  have hsqnn : 0 ≤ hsq := Finset.sum_nonneg fun i _ => sq_nonneg _
  have key : ∀ v : Amb k, ‖A v‖ ≤ Real.sqrt hsq * ‖v‖ := by
    intro v
    have hAv : A v = ∑ i : Fin k, v.ofLp i • A (EuclideanSpace.single i (1:ℝ)) := by
      conv_lhs => rw [← sum_smul_single v]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
    have h1 : ‖A v‖ ≤ ∑ i : Fin k, |v.ofLp i| * ‖A (EuclideanSpace.single i (1:ℝ))‖ := by
      rw [hAv]
      calc ‖∑ i : Fin k, v.ofLp i • A (EuclideanSpace.single i (1:ℝ))‖
          ≤ ∑ i : Fin k, ‖v.ofLp i • A (EuclideanSpace.single i (1:ℝ))‖ := norm_sum_le _ _
        _ = ∑ i : Fin k, |v.ofLp i| * ‖A (EuclideanSpace.single i (1:ℝ))‖ :=
            Finset.sum_congr rfl fun i _ => by rw [norm_smul, Real.norm_eq_abs]
    have h2 : (∑ i : Fin k, |v.ofLp i| * ‖A (EuclideanSpace.single i (1:ℝ))‖)^2
        ≤ (∑ i : Fin k, (v.ofLp i)^2) * hsq := by
      have h3 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin k))
        (fun i => |v.ofLp i|) (fun i => ‖A (EuclideanSpace.single i (1:ℝ))‖)
      simp only [sq_abs] at h3
      rw [hsqdef]
      simpa using h3
    have h4 : (∑ i : Fin k, (v.ofLp i)^2) = ‖v‖^2 := by
      rw [EuclideanSpace.norm_sq_eq]
      exact Finset.sum_congr rfl fun i _ => by rw [Real.norm_eq_abs, sq_abs]
    have h5 : ‖A v‖^2 ≤ (Real.sqrt hsq * ‖v‖)^2 := by
      have h6 := pow_le_pow_left₀ (norm_nonneg (A v)) h1 2
      calc ‖A v‖^2 ≤ (∑ i : Fin k, |v.ofLp i| * ‖A (EuclideanSpace.single i (1:ℝ))‖)^2 := h6
        _ ≤ (∑ i : Fin k, (v.ofLp i)^2) * hsq := h2
        _ = ‖v‖^2 * hsq := by rw [h4]
        _ = (Real.sqrt hsq * ‖v‖)^2 := by rw [mul_pow, Real.sq_sqrt hsqnn]; ring
    calc ‖A v‖ = Real.sqrt (‖A v‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((Real.sqrt hsq * ‖v‖)^2) := Real.sqrt_le_sqrt h5
      _ = Real.sqrt hsq * ‖v‖ := Real.sqrt_sq (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
  have hA : ‖A‖ ≤ Real.sqrt hsq := ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) key
  calc ‖A‖^2 ≤ (Real.sqrt hsq)^2 := pow_le_pow_left₀ (norm_nonneg A) hA 2
    _ = hsq := Real.sq_sqrt hsqnn

/-- **The `ℓ`-adapted frame identity, summed.**  This is `ell_apply_frame_eq` together with the
standard-basis expansion: applying `ℓ` to the `ℓ`-adapted frame vector
`∑ j, t j • Q (ℓ† (Λ⁻¹ (single j 1)))` of the plane returns `t`. -/
theorem ell_frame_sum {Q : Amb n →L[ℝ] Amb n} (hQ : Q ∈ Gr n k)
    (ℓ : Amb n →L[ℝ] Amb k) (hinj : ∀ z : Amb n, Q z = z → ℓ z = 0 → z = 0) (t : Amb k) :
    ℓ ((Finset.univ : Finset (Fin k)).sum fun j =>
        t j • Q (ℓ.adjoint ((ℓ.comp (Q.comp ℓ.adjoint)).inverse
          (EuclideanSpace.single j (1 : ℝ))))) = t := by
  rw [map_sum]
  rw [Finset.sum_congr rfl (fun j _ => by
    rw [map_smul, ell_apply_frame_eq ℓ Q hQ hinj])]
  exact sum_smul_single t

/-! ### Invertibility criteria -/

/-- An endomorphism of `ℝᵏ` whose `ℓ²`-distance to an invertible one is below
`(2 ‖A⁻¹‖ + 1)⁻¹` is again invertible.  (The constant is chosen in this harmless form so that it is
positive for *every* `A`, including in the degenerate case where `ℝᵏ` is a single point.) -/
theorem isInvertible_of_norm_sub_le {A B : Amb k →L[ℝ] Amb k} (hA : A.IsInvertible)
    (h : ‖B - A‖ ≤ (2 * ‖A.inverse‖ + 1)⁻¹) : B.IsInvertible := by
  by_cases h0 : A.inverse = 0
  · have hA0 : A = 0 := by
      have hinv := hA.inverse_inverse
      rw [h0, ContinuousLinearMap.inverse_zero] at hinv
      exact hinv.symm
    have hsub : Subsingleton (Amb k) := by
      have hAi : (0 : Amb k →L[ℝ] Amb k).IsInvertible := hA0 ▸ hA
      exact (ContinuousLinearMap.isInvertible_zero_iff.mp hAi).1
    have hB0 : B = 0 := by
      refine ContinuousLinearMap.ext fun x => ?_
      exact hsub.allEq _ _
    rw [hB0]
    exact ContinuousLinearMap.isInvertible_zero_iff.mpr ⟨hsub, hsub⟩
  · have hpos : 0 < ‖A.inverse‖ := norm_pos_iff.mpr h0
    obtain ⟨e, rfl⟩ := hA
    have hlt : ‖B - ↑(ContinuousLinearEquiv.toUnit e)‖
        < ‖(↑(ContinuousLinearEquiv.toUnit e)⁻¹ : Amb k →L[ℝ] Amb k)‖⁻¹ := by
      have hcoe : (↑(ContinuousLinearEquiv.toUnit e) : Amb k →L[ℝ] Amb k) = ↑e := rfl
      have hcoe' : (↑(ContinuousLinearEquiv.toUnit e)⁻¹ : Amb k →L[ℝ] Amb k)
          = (↑e : Amb k →L[ℝ] Amb k).inverse := by
        rw [show (↑(ContinuousLinearEquiv.toUnit e)⁻¹ : Amb k →L[ℝ] Amb k) = e.symm from rfl,
          ContinuousLinearMap.inverse_equiv]
      rw [hcoe, hcoe']
      refine lt_of_le_of_lt h ?_
      rw [inv_lt_inv₀ (by linarith) hpos]
      linarith
    exact ⟨ContinuousLinearEquiv.ofUnit (Units.ofNearby (ContinuousLinearEquiv.toUnit e) B hlt),
      rfl⟩

/-- Units in the endomorphism ring of `ℝᵏ` are exactly the invertible maps. -/
theorem isUnit_iff_isInvertible (A : Amb k →L[ℝ] Amb k) : IsUnit A ↔ A.IsInvertible := by
  constructor
  · intro h
    exact ⟨ContinuousLinearEquiv.ofUnit h.unit, h.unit_spec⟩
  · rintro ⟨e, rfl⟩
    exact ⟨ContinuousLinearEquiv.toUnit e, rfl⟩

/-- The set of invertible endomorphisms of `ℝᵏ` is open (no Hausdorff assumption needed: this is
`Units.isOpen` transported along `isUnit_iff_isInvertible`). -/
theorem isOpen_setOf_isInvertible : IsOpen {A : Amb k →L[ℝ] Amb k | A.IsInvertible} := by
  have h : {A : Amb k →L[ℝ] Amb k | A.IsInvertible} = {A | IsUnit A} := by
    ext A; exact (isUnit_iff_isInvertible A).symm
  rw [h]
  exact Units.isOpen

/-- **The inverse family is smooth on the invertibility locus.** -/
theorem contMDiffOn_inverse {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    (Λ : M → Amb k →L[ℝ] Amb k)
    (hΛ : ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Amb k →L[ℝ] Amb k) ∞ Λ) :
    ContMDiffOn (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Amb k →L[ℝ] Amb k) ∞
      (fun y => (Λ y).inverse) {y | (Λ y).IsInvertible} := by
  intro y hy
  have hinv : ContMDiffAt 𝓘(ℝ, Amb k →L[ℝ] Amb k) 𝓘(ℝ, Amb k →L[ℝ] Amb k) ∞
      ContinuousLinearMap.inverse (Λ y) :=
    (contMDiffAt_iff_contDiffAt).mpr (hy.contDiffAt_map_inverse)
  exact (hinv.comp y (hΛ.contMDiffAt (x := y))).contMDiffWithinAt

/-! ### The chart family of a projection-valued map -/

/-- **The chart family of a projection-valued map.**  Every `C^∞` map `P : M → End(ℝⁿ)` on a compact
source whose values are orthogonal projections of rank `k` (`P x ∈ Gr n k`) admits a finite family of
Grassmannian charts with `ℓ`-adapted frames **covering the source**, i.e. an `AmbCharts n k M P m` for
some `m`.

For each `x` we choose a linear coordinate `ℓ x : ℝⁿ → ℝᵏ` injective on the plane `im (P x)`
(`existsCoordInjOnGr`) and consider the *smooth* family of endomorphisms
`G x y = ℓ x ∘ P y ∘ (ℓ x)†` of `ℝᵏ`.  At `y = x` this is invertible
(`isInvertible_comp_adjoint_iff`), and it stays invertible as long as the *smooth* quantity
`sq x y = ∑ i, ‖(G x y - G x x) eᵢ‖²` stays small, because `‖A‖² ≤ ∑ i, ‖A eᵢ‖²`
(`opNorm_sq_sum_norm_sq`).  Hence `{y | sq x y < (rad x / 2)²}` is an open neighbourhood of `x` on
which `G x ·` is invertible and on which the smooth cut-off
`χ x y = smoothTransition (((rad x)² - sq x y) / ((rad x)² - (rad x/2)²))` equals `1`, while its
topological support lies inside the invertibility locus.  Multiplying the local frame by this
cut-off (which is supported where the inverse family is smooth, `contMDiffOn_inverse`, so that the
product is globally smooth by `contMDiff_smul_of_contMDiffOn_of_tsupport_subset`) makes the frames
globally smooth.  Compactness of `M` turns the family of these neighbourhoods into a finite cover. -/
theorem nonempty_ambCharts {n k : ℕ} (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace ((8 + k) + 1)) M]
    [IsManifold (𝓡∂ ((8 + k) + 1)) ((⊤ : ℕ∞) : WithTop ℕ∞) M] [CompactSpace M]
    {P : M → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)}
    (hP : ContMDiff (𝓡∂ ((8 + k) + 1))
      (𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) P)
    (hproj : ∀ x, P x ∈ Work.PTGeometric.Gr n k) :
    ∃ m : ℕ, Nonempty (Work.PTGeometric.AmbCharts n k M P m) := by
  classical
  -- Step 1: a linear coordinate for every point
  choose ℓ hℓ using fun x => existsCoordInjOnGr (P x) (hproj x)
  -- Step 2: the smooth family of endomorphisms `G x y = ℓ x ∘ P y ∘ (ℓ x)†`
  let G : M → M → (Amb k →L[ℝ] Amb k) := fun x y => (ℓ x).comp ((P y).comp (ℓ x).adjoint)
  have hG : ∀ x, ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Amb k →L[ℝ] Amb k) ∞ (G x) := by
    intro x
    have h1 : ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Amb k →L[ℝ] Amb n) ∞
        (fun y => (P y).comp (ℓ x).adjoint) :=
      hP.clm_comp (contMDiff_const (c := (ℓ x).adjoint))
    exact (contMDiff_const (c := ℓ x)).clm_comp h1
  have hGxx : ∀ x, (G x x).IsInvertible := fun x =>
    (isInvertible_comp_adjoint_iff (ℓ x) (P x) (hproj x)).mpr (fun z hz h0 => hℓ x z hz h0)
  have hpidem : ∀ y (w : Amb n), P y (P y w) = P y w := by
    intro y w
    have h : (P y * P y : Amb n →L[ℝ] Amb n) w = P y w := by rw [(hproj y).2.1]
    simpa using h
  -- Step 3: the smooth "smallness" function `sq`
  let sq : M → M → ℝ := fun x y =>
    ∑ i : Fin k, ‖G x y (EuclideanSpace.single i (1 : ℝ))
      - G x x (EuclideanSpace.single i (1 : ℝ))‖ ^ 2
  have hsq : ∀ x, ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, ℝ) ∞ (sq x) := by
    intro x
    refine ContMDiff.sum fun i _ => ?_
    have h1 : ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Amb k) ∞
        (fun y => G x y (EuclideanSpace.single i (1 : ℝ))
          - G x x (EuclideanSpace.single i (1 : ℝ))) :=
      (((hG x).clm_apply contMDiff_const)).sub contMDiff_const
    exact (contDiff_norm_sq (𝕜 := ℝ) (E := Amb k)).contMDiff.comp h1
  -- Step 4: the radius and the neighbourhoods
  let rad : M → ℝ := fun x => (2 * ‖(G x x).inverse‖ + 1)⁻¹
  have hrad_pos : ∀ x, 0 < rad x := fun x => inv_pos.mpr (by positivity)
  have hrad_nonneg : ∀ x, 0 ≤ rad x := fun x => (hrad_pos x).le
  let U : M → Set M := fun x => {y | sq x y < (rad x / 2) ^ 2}
  have hU_open : ∀ x, IsOpen (U x) :=
    fun x => isOpen_lt (hsq x).continuous continuous_const
  have hU_mem : ∀ x, x ∈ U x := by
    intro x
    have hzero : sq x x = 0 := by
      simp only [sq]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [sub_self, norm_zero]
      ring
    show sq x x < (rad x / 2) ^ 2
    rw [hzero]
    exact pow_pos (by linarith [hrad_pos x]) 2
  -- the norm bound: a small `sq` gives a small operator norm of `G x y - G x x`
  have hbound : ∀ x y : M, sq x y ≤ (rad x) ^ 2 → ‖G x y - G x x‖ ≤ rad x := by
    intro x y hy
    have h1 := opNorm_sq_le_sum_norm_sq (G x y - G x x)
    have h2 : (∑ i : Fin k, ‖(G x y - G x x) (EuclideanSpace.single i (1 : ℝ))‖ ^ 2)
        = sq x y := by
      simp only [sq]
      exact Finset.sum_congr rfl fun i _ => by rw [sub_apply]
    rw [h2] at h1
    have h3 : ‖G x y - G x x‖ ^ 2 ≤ (rad x) ^ 2 := le_trans h1 hy
    calc ‖G x y - G x x‖ = Real.sqrt (‖G x y - G x x‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ Real.sqrt ((rad x) ^ 2) := Real.sqrt_le_sqrt h3
      _ = rad x := Real.sqrt_sq (hrad_nonneg x)
  have hU_sub : ∀ x, U x ⊆ {y | (G x y).IsInvertible} := by
    intro x y hy
    have hy' : sq x y < (rad x / 2) ^ 2 := hy
    exact isInvertible_of_norm_sub_le (hGxx x)
      (hbound x y (le_trans hy'.le (by nlinarith [hrad_nonneg x])))
  -- Step 5: finitely many of the neighbourhoods cover `M`
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hU_open
    (fun y _ => mem_iUnion.mpr ⟨y, hU_mem y⟩)
  let xl : Fin t.card → M := fun l => ((t.equivFin.symm l : ↥t) : M)
  have hcov : ∀ y : M, ∃ l : Fin t.card, y ∈ U (xl l) := by
    intro y
    have h1 : y ∈ ⋃ x ∈ t, U x := ht (mem_univ y)
    simp only [mem_iUnion] at h1
    obtain ⟨x, hxt, hxU⟩ := h1
    refine ⟨t.equivFin ⟨x, hxt⟩, ?_⟩
    have hxl : xl (t.equivFin ⟨x, hxt⟩) = x := by simp [xl]
    rwa [hxl]
  -- Step 6: the cut-off functions
  let chi : M → M → ℝ := fun x y =>
    Real.smoothTransition (((rad x) ^ 2 - sq x y) / ((rad x) ^ 2 - (rad x / 2) ^ 2))
  have hchi_smooth : ∀ x, ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, ℝ) ∞ (chi x) := by
    intro x
    exact (Real.smoothTransition.contDiff (n := ⊤)).contMDiff.comp
      (((contMDiff_const (c := (rad x) ^ 2)).sub (hsq x)).div_const _)
  have hchi_one : ∀ x y, y ∈ U x → chi x y = 1 := by
    intro x y hy
    have hD : 0 < (rad x) ^ 2 - (rad x / 2) ^ 2 := by nlinarith [hrad_pos x]
    have hy' : sq x y < (rad x / 2) ^ 2 := hy
    refine Real.smoothTransition.one_of_one_le ?_
    rw [le_div_iff₀ hD]
    nlinarith [hy'.le]
  have hchi_tsupp : ∀ x, tsupport (chi x) ⊆ {y | (G x y).IsInvertible} := by
    intro x
    have hsupp : Function.support (chi x) ⊆ {y : M | sq x y ≤ (rad x) ^ 2} := by
      intro y hy
      by_contra hcon
      have hlt : (rad x) ^ 2 < sq x y := not_le.mp hcon
      have hD : 0 < (rad x) ^ 2 - (rad x / 2) ^ 2 := by nlinarith [hrad_pos x]
      have hz : ((rad x) ^ 2 - sq x y) / ((rad x) ^ 2 - (rad x / 2) ^ 2) < 0 :=
        div_neg_of_neg_of_pos (by linarith) hD
      exact hy (by
        simp only [chi]
        exact Real.smoothTransition.zero_of_nonpos hz.le)
    have hclosed : IsClosed {y : M | sq x y ≤ (rad x) ^ 2} :=
      isClosed_le (hsq x).continuous continuous_const
    have h1 : closure (Function.support (chi x)) ⊆ {y : M | sq x y ≤ (rad x) ^ 2} :=
      closure_minimal hsupp hclosed
    intro y hy
    exact isInvertible_of_norm_sub_le (hGxx x) (hbound x y (h1 hy))
  -- Step 7: the frames
  have hinj_of_inv : ∀ x y : M, y ∈ U x → ∀ z : Amb n, P y z = z → ℓ x z = 0 → z = 0 := by
    intro x y hy z hz h0
    exact (isInvertible_comp_adjoint_iff (ℓ x) (P y) (hproj y)).mp (hU_sub x hy) z hz h0
  let efun : Fin t.card → Fin k → M → Amb n := fun l j y =>
    chi (xl l) y • P y ((ℓ (xl l)).adjoint
      ((G (xl l) y).inverse (EuclideanSpace.single j (1 : ℝ))))
  have hefun_smooth : ∀ l j, ContMDiff (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Amb n) ∞ (efun l j) := by
    intro l j
    have h4 : ContMDiffOn (𝓡∂ ((8 + k) + 1)) 𝓘(ℝ, Amb n) ∞
        (fun y => P y ((ℓ (xl l)).adjoint
          ((G (xl l) y).inverse (EuclideanSpace.single j (1 : ℝ)))))
        {y | (G (xl l) y).IsInvertible} :=
      hP.contMDiffOn.clm_apply
        ((contMDiffOn_const (c := (ℓ (xl l)).adjoint)).clm_apply
          ((contMDiffOn_inverse (G (xl l)) (hG (xl l))).clm_apply contMDiffOn_const))
    have hWopen : IsOpen {y : M | (G (xl l) y).IsInvertible} :=
      isOpen_setOf_isInvertible.preimage (hG (xl l)).continuous
    exact contMDiff_smul_of_contMDiffOn_of_tsupport_subset hWopen
      (hchi_smooth (xl l)) h4 (hchi_tsupp (xl l))
  -- Step 8: assemble
  refine ⟨t.card, ?_⟩
  refine ⟨?_⟩
  exact
  { ell := fun l => ℓ (xl l),
    U := fun l => U (xl l),
    e := efun,
    isOpen_U := fun l => hU_open (xl l),
    covers := fun y => hcov y,
    contMDiff_e := fun l j => hefun_smooth l j,
    ell_inj := fun l y hy z hz h0 => hinj_of_inv (xl l) y hy z hz h0,
    mem_e := by
      intro l j y hy
      show P y (efun l j y) = efun l j y
      simp only [efun]
      rw [map_smul, hpidem y],
    ell_frame := by
      intro l y hy s
      have hchi1 : chi (xl l) y = 1 := hchi_one (xl l) y hy
      have hkey : ∀ j : Fin k, efun l j y = P y ((ℓ (xl l)).adjoint
          ((G (xl l) y).inverse (EuclideanSpace.single j (1 : ℝ)))) := by
        intro j
        simp only [efun, hchi1, one_smul]
      simp only [hkey]
      exact ell_frame_sum (hproj y) (ℓ (xl l)) (hinj_of_inv (xl l) y hy) s }

end

end Work.PTGeometric
