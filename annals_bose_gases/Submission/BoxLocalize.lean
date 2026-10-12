import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Submission.CellGrid
import Submission.ManyBodyIMS
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Box-level localization: partition of unity on the cube, integrated over the box

`Submission.ManyBodyIMS` proved the many-body IMS identity under a *global*
partition-of-unity assumption `Σ_j (χ_j y)² = 1` for all `y : ℝ³`.  The cell
cutoffs of `Submission.CellGrid` satisfy the partition identity only on the
cube `[0, m·ℓ]³`.  This module proves the variant needed in applications: the
partition identity is assumed only on the (open) cube `cubeOp L`, and the IMS
identity is asserted at configurations whose localised particle lies in the
cube — which is exactly the situation for a Dirichlet state in `box N (m·ℓ)`
(with the open-cube assumption satisfied since `cellCut`'s partition holds on
the closed cube, hence on the open cube).

  * `cubeOp` / `cubeCl` — the open/closed coordinate cubes of side `L`;
  * `pu_fderiv_sum_zero_cube` — the cross-term cancellation from a partition
    identity on the open cube (a neighbourhood of the point, since the cube is
    open);
  * `ims_pointwise_cube` — the pointwise many-body IMS identity for a state
    whose localised particle is inside the cube;
  * `ims_box_identity` — the integrated identity over `box N L` for Dirichlet
    states (integrands vanish on the boundary, where the particle coordinate
    leaves the open cube);
  * **`boxLocalize_kinetic_le`** — the box-level localization bound: for a
    Dirichlet state `Ψ` in `box N (m·ℓ)` and the `m³`-cell cutoffs `cellCut ℓ m`,
    localising particle `i` costs at most `(6A²/ℓ²)·‖Ψ‖²`:
        Σ_c Σ_k ∫ (∂_{ik}(χ_c(x_i)·Ψ))² ≤ Σ_k ∫ (∂_{ik}Ψ)² + (6A²/ℓ²)·∫ Ψ².
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

local notation "⟪" f ", " g "⟫_["N "," L"]" => ∫ x in box N L, f x * g x

/-- The open coordinate cube `(0,L)³`. -/
def cubeOp (L : ℝ) : Set ℝ³ := {y : ℝ³ | ∀ k : Fin 3, y k ∈ Set.Ioo 0 L}

/-- The closed coordinate cube `[0,L]³`. -/
def cubeCl (L : ℝ) : Set ℝ³ := {y : ℝ³ | ∀ k : Fin 3, y k ∈ Set.Icc 0 L}

/-- The open cube is contained in the closed one. -/
lemma cubeOp_subset_cubeCl (L : ℝ) : cubeOp L ⊆ cubeCl L := by
  intro y hy k
  exact Set.Ioo_subset_Icc_self (hy k)

/-- The open cube is an open set. -/
lemma cubeOp_isOpen (L : ℝ) : IsOpen (cubeOp L) := by
  unfold cubeOp
  rw [show {y : ℝ³ | ∀ k : Fin 3, y k ∈ Set.Ioo 0 L} =
      (⋂ k : Fin 3, (fun y : ℝ³ => y k) ⁻¹' (Set.Ioo 0 L)) by
        ext y; simp]
  exact isOpen_iInter_of_finite (fun k => IsOpen.preimage (by fun_prop : Continuous fun y : ℝ³ => y k) isOpen_Ioo)

/-- The open cube is a neighbourhood of each of its points. -/
lemma cubeOp_mem_nhds {L : ℝ} {x : ℝ³} (hx : x ∈ cubeOp L) : cubeOp L ∈ 𝓝 x :=
  (cubeOp_isOpen L).mem_nhds hx

/-- A function which is eventually zero at a point has zero fderiv there. -/
lemma fderiv_zero_of_eventually_eq_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {p : E → ℝ} {x : E} (hp : p =ᶠ[𝓝 x] 0) : fderiv ℝ p x = 0 := by
  have h : HasFDerivAt p (0 : E →L[ℝ] ℝ) x := by
    exact (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq hp
  exact h.fderiv

/-- A point of `box N L` whose `i`-th particle leaves the open cube is not an
interior point of the box. -/
lemma box_out_interior {N : ℕ} {L : ℝ} (hL : 0 < L) (i : Fin N) {x : X N}
    (hxi : x i ∉ cubeOp L) : x ∉ interior (box N L) := by
  intro hxint
  apply hxi
  intro k
  exact kc_interior_box_coord hL hxint i k

/-- A Dirichlet state is eventually zero at configurations whose localised
particle leaves the open cube. -/
lemma psi_eventually_zero_of_coord_out {N : ℕ} {L : ℝ} (hL : 0 < L)
    (Ψ : CInfty0Box N L) (i : Fin N) {x : X N} (hxi : x i ∉ cubeOp L) :
    (Ψ : X N → ℝ) =ᶠ[𝓝 x] 0 := by
  have hxni : x ∉ interior (box N L) := box_out_interior hL i hxi
  have hts : x ∉ tsupport (Ψ : X N → ℝ) := by
    intro hmem
    exact hxni (Ψ.support hmem)
  exact notMem_tsupport_iff_eventuallyEq.mp hts

/-- Cross-term cancellation from a partition identity on the *open* cube: at a
point of the open cube (where the identity holds on a whole neighbourhood) one
has `Σ_j χ_j(x)·∂ₖχ_j(x) = 0`. -/
lemma pu_fderiv_sum_zero_cube {ι : Type*} [Fintype ι] {χ : ι → ℝ³ → ℝ}
    (hχ : ∀ j : ι, ContDiff ℝ 1 (χ j)) {L : ℝ} {x : ℝ³} (hx : x ∈ cubeOp L)
    (k : Fin 3) (hpu : ∀ y : ℝ³, y ∈ cubeOp L → ∑ j : ι, (χ j y) ^ 2 = 1) :
    ∑ j : ι, (χ j x) * (fderiv ℝ (χ j) x (kcStdBasis k)) = 0 := by
  let w : ℝ³ := kcStdBasis k
  have hdiff : ∀ j : ι, DifferentiableAt ℝ (χ j) x := fun j =>
    (hχ j).differentiable (by norm_num) x
  have hdiff_sq : ∀ j : ι, DifferentiableAt ℝ (fun y : ℝ³ => (χ j y) ^ 2) x := fun j =>
    (hdiff j).pow 2
  have hpow_j : ∀ j : ι, fderiv ℝ (fun y : ℝ³ => (χ j y) ^ 2) x w =
      2 * (χ j x) * (fderiv ℝ (χ j) x w) := by
    intro j
    have hEq : (fun y : ℝ³ => (χ j y) ^ 2) = fun y : ℝ³ => (χ j y) * (χ j y) := by
      funext y
      rw [pow_two]
    calc
      fderiv ℝ (fun y : ℝ³ => (χ j y) ^ 2) x w
          = fderiv ℝ (fun y : ℝ³ => (χ j y) * (χ j y)) x w := by
            rw [hEq]
      _ = (χ j x • fderiv ℝ (χ j) x + χ j x • fderiv ℝ (χ j) x) w := by
            change (fderiv ℝ (χ j * χ j) x) w =
              (χ j x • fderiv ℝ (χ j) x + χ j x • fderiv ℝ (χ j) x) w
            rw [fderiv_mul (hdiff j) (hdiff j)]
      _ = χ j x * (fderiv ℝ (χ j) x w) + χ j x * (fderiv ℝ (χ j) x w) := by simp
      _ = 2 * (χ j x) * (fderiv ℝ (χ j) x w) := by ring
  let φ : ℝ³ → ℝ := fun y => ∑ j : ι, (χ j y) ^ 2
  have hφeq : φ =ᶠ[𝓝 x] (fun _ : ℝ³ => 1) := by
    filter_upwards [cubeOp_mem_nhds hx] with y hy
    dsimp [φ]
    exact hpu y hy
  have hφfd : fderiv ℝ φ x = 0 := by
    have hc : HasFDerivAt (fun _ : ℝ³ => (1 : ℝ)) (0 : ℝ³ →L[ℝ] ℝ) x := hasFDerivAt_const 1 x
    have hc' : HasFDerivAt φ (0 : ℝ³ →L[ℝ] ℝ) x := hc.congr_of_eventuallyEq hφeq
    exact hc'.fderiv
  have h0 : fderiv ℝ φ x w = 0 := by
    rw [hφfd]
    simp
  have hfdsum : fderiv ℝ φ x = ∑ j : ι, fderiv ℝ (fun y : ℝ³ => (χ j y) ^ 2) x := by
    dsimp [φ]
    rw [fderiv_fun_sum (u := Finset.univ) (A := fun j : ι => fun y : ℝ³ => (χ j y) ^ 2)
      (by intro j hj; exact hdiff_sq j)]
  have happ : fderiv ℝ φ x w = (∑ j : ι, fderiv ℝ (fun y : ℝ³ => (χ j y) ^ 2) x) w := by
    rw [hfdsum]
  have htot : (∑ j : ι, fderiv ℝ (fun y : ℝ³ => (χ j y) ^ 2) x w) = 0 := by
    calc
      (∑ j : ι, fderiv ℝ (fun y : ℝ³ => (χ j y) ^ 2) x w)
          = (∑ j : ι, fderiv ℝ (fun y : ℝ³ => (χ j y) ^ 2) x) w := by
            rw [← sum_apply]
      _ = fderiv ℝ φ x w := happ.symm
      _ = 0 := h0
  have hrew : (∑ j : ι, fderiv ℝ (fun y : ℝ³ => (χ j y) ^ 2) x w) =
      ∑ j : ι, 2 * (χ j x) * (fderiv ℝ (χ j) x w) := by
    refine Finset.sum_congr rfl (fun j hj => hpow_j j)
  have htot2 : (∑ j : ι, 2 * (χ j x) * (fderiv ℝ (χ j) x w)) = 0 := by
    rw [← hrew]
    exact htot
  have hfac : (∑ j : ι, 2 * (χ j x) * (fderiv ℝ (χ j) x w)) =
      2 * (∑ j : ι, (χ j x) * (fderiv ℝ (χ j) x w)) := by
    calc
      (∑ j : ι, 2 * (χ j x) * (fderiv ℝ (χ j) x w))
          = ∑ j : ι, 2 * ((χ j x) * (fderiv ℝ (χ j) x w)) := by
            refine Finset.sum_congr rfl (fun j hj => by ring)
      _ = 2 * (∑ j : ι, (χ j x) * (fderiv ℝ (χ j) x w)) := by
            rw [← Finset.mul_sum]
  have h2 : 2 * (∑ j : ι, (χ j x) * (fderiv ℝ (χ j) x w)) = 0 := by
    rw [← hfac]
    exact htot2
  have hT : (∑ j : ι, (χ j x) * (fderiv ℝ (χ j) x w)) = 0 := by
    nlinarith
  simpa [w] using hT

/-- algebraic IMS square-sum identity (local copy of the private lemma of
`Submission.ManyBodyIMS`) -/
private lemma ims_sq_sum_identity_local {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (b : ι → κ → ℝ) (c : κ → ℝ) (m : ℝ)
    (ha : (∑ j : ι, (a j)^2) = 1) (hb : ∀ k : κ, (∑ j : ι, a j * b j k) = 0) :
    (∑ j : ι, ∑ k : κ, (a j * c k + b j k * m)^2) =
      (∑ k : κ, (c k)^2) + (m^2) * (∑ j : ι, ∑ k : κ, (b j k)^2) := by
  have h1 : (∑ j : ι, ∑ k : κ, (a j)^2 * (c k)^2) = ∑ k : κ, (c k)^2 := by
    calc
      (∑ j : ι, ∑ k : κ, (a j)^2 * (c k)^2)
          = ∑ j : ι, (a j)^2 * (∑ k : κ, (c k)^2) := by
            refine Finset.sum_congr rfl (fun j hj => ?_)
            rw [Finset.mul_sum]
      _ = (∑ j : ι, (a j)^2) * (∑ k : κ, (c k)^2) := by rw [Finset.sum_mul]
      _ = 1 * (∑ k : κ, (c k)^2) := by rw [ha]
      _ = (∑ k : κ, (c k)^2) := by ring
  have h2 : (∑ j : ι, ∑ k : κ, 2 * (a j * c k) * (b j k * m)) = 0 := by
    calc
      (∑ j : ι, ∑ k : κ, 2 * (a j * c k) * (b j k * m))
          = ∑ k : κ, ∑ j : ι, 2 * (a j * c k) * (b j k * m) := by rw [Finset.sum_comm]
      _ = ∑ k : κ, (2 * m * c k) * (∑ j : ι, a j * b j k) := by
            refine Finset.sum_congr rfl (fun k hk => ?_)
            calc
              (∑ j : ι, 2 * (a j * c k) * (b j k * m))
                  = ∑ j : ι, (2 * m * c k) * (a j * b j k) := by
                    refine Finset.sum_congr rfl (fun j hj => by ring)
              _ = (2 * m * c k) * (∑ j : ι, a j * b j k) := by rw [← Finset.mul_sum]
      _ = ∑ k : κ, (2 * m * c k) * 0 := by
            refine Finset.sum_congr rfl (fun k hk => ?_)
            rw [hb k]
      _ = 0 := by simp
  have h3 : (∑ j : ι, ∑ k : κ, (b j k)^2 * m^2) =
      m^2 * (∑ j : ι, ∑ k : κ, (b j k)^2) := by
    calc
      (∑ j : ι, ∑ k : κ, (b j k)^2 * m^2)
          = ∑ j : ι, (∑ k : κ, (b j k)^2) * m^2 := by
            refine Finset.sum_congr rfl (fun j hj => ?_)
            rw [← Finset.sum_mul]
      _ = (∑ j : ι, ∑ k : κ, (b j k)^2) * m^2 := by rw [← Finset.sum_mul]
      _ = m^2 * (∑ j : ι, ∑ k : κ, (b j k)^2) := by ring
  have hexp : (∑ j : ι, ∑ k : κ, (a j * c k + b j k * m)^2) =
      (∑ j : ι, ∑ k : κ, ((a j)^2 * (c k)^2 + 2 * (a j * c k) * (b j k * m) + (b j k)^2 * m^2)) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    refine Finset.sum_congr rfl (fun k hk => ?_)
    ring
  rw [hexp]
  have hsplit : (∑ j : ι, ∑ k : κ, ((a j)^2 * (c k)^2 + 2 * (a j * c k) * (b j k * m) + (b j k)^2 * m^2)) =
      (∑ j : ι, ∑ k : κ, (a j)^2 * (c k)^2) +
      (∑ j : ι, ∑ k : κ, 2 * (a j * c k) * (b j k * m)) +
      (∑ j : ι, ∑ k : κ, (b j k)^2 * m^2) := by
    simp [Finset.sum_add_distrib, add_assoc]
  rw [hsplit, h1, h2, h3]
  ring

/-- The pointwise many-body IMS identity with the partition identity assumed
only on the cube, at configurations whose localised particle lies inside the
cube. -/
lemma ims_pointwise_cube {N : ℕ} {ι : Type*} [Fintype ι] (i : Fin N) {L : ℝ}
    {f : X N → ℝ} (hf : ContDiff ℝ 1 f) {x : X N} (hx : (x i) ∈ cubeOp L)
    (χ : ι → ℝ³ → ℝ) (hχ : ∀ j : ι, ContDiff ℝ 1 (χ j))
    (hpu : ∀ y : ℝ³, y ∈ cubeOp L → ∑ j : ι, (χ j y) ^ 2 = 1) :
    (∑ j : ι, ∑ k : Fin 3,
        (fderiv ℝ (fun y : X N => χ j (y i) * f y) x (kcDir N i k)) ^ 2) =
      (∑ k : Fin 3, (fderiv ℝ f x (kcDir N i k)) ^ 2) +
        ((f x) ^ 2) * (∑ j : ι, ∑ k : Fin 3,
          (fderiv ℝ (χ j) (x i) (kcStdBasis k)) ^ 2) := by
  have ht : ∀ (j : ι) (k : Fin 3),
      fderiv ℝ (fun y : X N => χ j (y i) * f y) x (kcDir N i k) =
        χ j (x i) * fderiv ℝ f x (kcDir N i k) +
          fderiv ℝ (χ j) (x i) (kcStdBasis k) * f x := by
    intro j k
    exact slice_deriv_cutoff i k (hχ j) hf x
  calc
    (∑ j : ι, ∑ k : Fin 3,
        (fderiv ℝ (fun y : X N => χ j (y i) * f y) x (kcDir N i k)) ^ 2)
        = ∑ j : ι, ∑ k : Fin 3,
            (χ j (x i) * fderiv ℝ f x (kcDir N i k) +
              fderiv ℝ (χ j) (x i) (kcStdBasis k) * f x)^2 := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          refine Finset.sum_congr rfl (fun k hk => ?_)
          rw [ht j k]
    _ = (∑ k : Fin 3, (fderiv ℝ f x (kcDir N i k)) ^ 2) +
          ((f x) ^ 2) * (∑ j : ι, ∑ k : Fin 3,
            (fderiv ℝ (χ j) (x i) (kcStdBasis k)) ^ 2) := by
          exact ims_sq_sum_identity_local (a := fun j : ι => χ j (x i))
            (b := fun j : ι => fun k : Fin 3 => fderiv ℝ (χ j) (x i) (kcStdBasis k))
            (c := fun k : Fin 3 => fderiv ℝ f x (kcDir N i k))
            (m := f x)
            (by
              exact hpu (x i) hx)
            (by
              intro k
              exact pu_fderiv_sum_zero_cube hχ hx k hpu)

/-- A continuous function is integrable on the compact box `box N L`. -/
private lemma bl_cont_integrableOn {N : ℕ} {L : ℝ} (hL : 0 < L)
    {g : X N → ℝ} (hg : Continuous g) : IntegrableOn g (box N L) volume := by
  exact hg.continuousOn.integrableOn_compact (box_compact hL)

/-- The pointwise IMS identity for a Dirichlet state, at every point of the
box: inside the open cube it is the many-body identity; on the boundary the
state vanishes in a neighbourhood, so both sides are zero. -/
lemma ims_pointwise_box {N : ℕ} {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L)
    (i : Fin N) (Ψ : CInfty0Box N L)
    (χ : ι → ℝ³ → ℝ) (hχ : ∀ j : ι, ContDiff ℝ 1 (χ j))
    (hpu : ∀ y : ℝ³, y ∈ cubeOp L → ∑ j : ι, (χ j y) ^ 2 = 1) :
    ∀ x : X N, x ∈ box N L →
      (∑ j : ι, ∑ k : Fin 3,
          (fderiv ℝ (fun y : X N => χ j (y i) * (Ψ : X N → ℝ) y) x (kcDir N i k)) ^ 2) =
        (∑ k : Fin 3, (fderiv ℝ (Ψ : X N → ℝ) x (kcDir N i k)) ^ 2) +
          ((Ψ : X N → ℝ) x) ^ 2 * (∑ j : ι, ∑ k : Fin 3,
            (fderiv ℝ (χ j) (x i) (kcStdBasis k)) ^ 2) := by
  intro x hxbox
  have hΨ1 : ContDiff ℝ 1 (Ψ : X N → ℝ) := (psi_contDiff Ψ).of_le (by norm_num)
  by_cases hxi : (x i) ∈ cubeOp L
  · exact ims_pointwise_cube i hΨ1 (x := x) hxi χ hχ hpu
  · have hΨeq : (Ψ : X N → ℝ) =ᶠ[𝓝 x] 0 :=
      psi_eventually_zero_of_coord_out hL Ψ i hxi
    calc
      (∑ j : ι, ∑ k : Fin 3,
          (fderiv ℝ (fun y : X N => χ j (y i) * (Ψ : X N → ℝ) y) x (kcDir N i k)) ^ 2) = 0 := by
            apply Finset.sum_eq_zero
            intro j hj
            apply Finset.sum_eq_zero
            intro k hk
            have hfdj : fderiv ℝ (fun y : X N => χ j (y i) * (Ψ : X N → ℝ) y) x = 0 := by
              apply fderiv_zero_of_eventually_eq_zero
              filter_upwards [hΨeq] with y hy
              simp [hy]
            rw [hfdj]
            simp
      _ = (∑ k : Fin 3, (fderiv ℝ (Ψ : X N → ℝ) x (kcDir N i k)) ^ 2) +
          ((Ψ : X N → ℝ) x) ^ 2 * (∑ j : ι, ∑ k : Fin 3,
            (fderiv ℝ (χ j) (x i) (kcStdBasis k)) ^ 2) := by
            have hfdΨ : fderiv ℝ (Ψ : X N → ℝ) x = 0 := fderiv_zero_of_eventually_eq_zero hΨeq
            have hΨx : (Ψ : X N → ℝ) x = 0 := hΨeq.eq_of_nhds
            simp [hfdΨ, hΨx]

/-- The integrated IMS identity over `box N L` for a Dirichlet state whose
localised particle stays in the open cube on its support (the boundary of the
box, where the identity need not hold, carries no mass). -/
lemma ims_box_identity {N : ℕ} {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L)
    (i : Fin N) (Ψ : CInfty0Box N L)
    (χ : ι → ℝ³ → ℝ) (hχ : ∀ j : ι, ContDiff ℝ ∞ (χ j))
    (hpu : ∀ y : ℝ³, y ∈ cubeOp L → ∑ j : ι, (χ j y) ^ 2 = 1) :
    (∑ j : ι, ∑ k : Fin 3, ∫ x in box N L,
        (fderiv ℝ (fun y : X N => χ j (y i) * (Ψ : X N → ℝ) y) x (kcDir N i k)) ^ 2) =
      (∑ k : Fin 3, ∫ x in box N L,
        (fderiv ℝ (Ψ : X N → ℝ) x (kcDir N i k)) ^ 2) +
        (∑ j : ι, ∫ x in box N L, (((Ψ : X N → ℝ) x) ^ 2) *
          ∑ k : Fin 3, (fderiv ℝ (χ j) ((x i)) (kcStdBasis k)) ^ 2) := by
  let T : ι → Fin 3 → X N → ℝ := fun j k x =>
    (fderiv ℝ (fun y : X N => χ j (y i) * (Ψ : X N → ℝ) y) x (kcDir N i k)) ^ 2
  let A : Fin 3 → X N → ℝ := fun k x => (fderiv ℝ (Ψ : X N → ℝ) x (kcDir N i k)) ^ 2
  let C : ι → X N → ℝ := fun j x => (((Ψ : X N → ℝ) x) ^ 2) *
    ∑ k : Fin 3, (fderiv ℝ (χ j) (x i) (kcStdBasis k)) ^ 2
  have hf : ContDiff ℝ ∞ (Ψ : X N → ℝ) := psi_contDiff Ψ
  have hχ1 : ∀ j : ι, ContDiff ℝ 1 (χ j) := fun j => (hχ j).of_le (by norm_num)
  have hgjm : ∀ j : ι, ContDiff ℝ ∞ (fun y : X N => χ j (y i) * (Ψ : X N → ℝ) y) := by
    intro j
    have hc : ContDiff ℝ ∞ (fun y : X N => χ j (y i)) := by
      have hpi : ContDiff ℝ ∞ (fun y : X N => y i) := by
        simpa using (contDiff_apply ℝ (EuclideanSpace ℝ (Fin 3)) (n := ∞) (ι := Fin N) i)
      simpa [Function.comp_def] using (hχ j).comp hpi
    exact hc.mul hf
  have hTcont : ∀ j k, Continuous (T j k) := by
    intro j k
    dsimp [T]
    exact (firstDir_contDiff (hgjm j) (kcDir N i k)).continuous.pow 2
  have hAcont : ∀ k, Continuous (A k) := by
    intro k
    dsimp [A]
    exact (firstDir_contDiff hf (kcDir N i k)).continuous.pow 2
  have hBz : ∀ j k, Continuous (fun x : X N => fderiv ℝ (χ j) (x i) (kcStdBasis k)) := by
    intro j k
    have hfdj : ContDiff ℝ ∞ (fderiv ℝ (χ j)) := ContDiff.fderiv_right (m := ∞) (hχ j) (by simp)
    have heval : ContDiff ℝ ∞ (fun (L : ℝ³ →L[ℝ] ℝ) => L (kcStdBasis k)) := by
      exact ((ContinuousLinearMap.apply (𝕜 := ℝ) (Fₗ := ℝ) (kcStdBasis k) : (ℝ³ →L[ℝ] ℝ) →L[ℝ] ℝ).contDiff)
    have hz : ContDiff ℝ ∞ (fun z : ℝ³ => fderiv ℝ (χ j) z (kcStdBasis k)) := by
      simpa [Function.comp_def] using heval.comp hfdj
    have hpi : Continuous (fun x : X N => x i) := continuous_apply i
    exact (hz.continuous.comp hpi)
  have hBcont : ∀ j k, Continuous (fun x : X N => (fderiv ℝ (χ j) (x i) (kcStdBasis k)) ^ 2) := by
    intro j k
    exact (hBz j k).pow 2
  have hCcont : ∀ j, Continuous (C j) := by
    intro j
    dsimp [C]
    refine (hf.continuous.pow 2).mul ?_
    refine continuous_finsetSum (s := Finset.univ) (f := fun (k : Fin 3) (x : X N) =>
      (fderiv ℝ (χ j) (x i) (kcStdBasis k)) ^ 2) ?_
    intro k hk
    exact hBcont j k
  have hI_T : ∀ j k, IntegrableOn (T j k) (box N L) volume := fun j k =>
    bl_cont_integrableOn hL (hTcont j k)
  have hI_A : ∀ k, IntegrableOn (A k) (box N L) volume := fun k =>
    bl_cont_integrableOn hL (hAcont k)
  have hI_C : ∀ j, IntegrableOn (C j) (box N L) volume := fun j =>
    bl_cont_integrableOn hL (hCcont j)
  have hI_A_sum : IntegrableOn (fun x : X N => ∑ k : Fin 3, A k x) (box N L) volume := by
    refine bl_cont_integrableOn hL ?_
    refine continuous_finsetSum (s := Finset.univ) (f := fun (k : Fin 3) (x : X N) => A k x) ?_
    intro k hk
    exact hAcont k
  have hI_C_sum : IntegrableOn (fun x : X N => ∑ j : ι, C j x) (box N L) volume := by
    refine bl_cont_integrableOn hL ?_
    refine continuous_finsetSum (s := Finset.univ) (f := fun (j : ι) (x : X N) => C j x) ?_
    intro j hj
    exact hCcont j
  have hI_Tj : ∀ j : ι, IntegrableOn (fun x : X N => ∑ k : Fin 3, T j k x) (box N L) volume := by
    intro j
    refine bl_cont_integrableOn hL ?_
    refine continuous_finsetSum (s := Finset.univ) (f := fun (k : Fin 3) (x : X N) => T j k x) ?_
    intro k hk
    exact hTcont j k
  have hpt : (fun x : X N => ∑ j : ι, ∑ k : Fin 3, T j k x) =ᵐ[volume.restrict (box N L)]
      fun x : X N => (∑ k : Fin 3, A k x) + (∑ j : ι, C j x) := by
    refine (ae_restrict_mem (box_measurable N L)).mono ?_
    intro x hx
    calc
      (∑ j : ι, ∑ k : Fin 3, T j k x)
          = (∑ k : Fin 3, A k x) + (((Ψ : X N → ℝ) x) ^ 2) * (∑ j : ι, ∑ k : Fin 3,
              (fderiv ℝ (χ j) (x i) (kcStdBasis k)) ^ 2) := by
            dsimp [T, A]
            exact ims_pointwise_box hL i Ψ χ hχ1 hpu x hx
      _ = (∑ k : Fin 3, A k x) + (∑ j : ι, C j x) := by
            dsimp [C]
            rw [Finset.mul_sum]
  have hLHS : (∑ j : ι, ∑ k : Fin 3, ∫ x in box N L, T j k x) =
      ∫ x in box N L, (∑ j : ι, ∑ k : Fin 3, T j k x) := by
    calc
      (∑ j : ι, ∑ k : Fin 3, ∫ x in box N L, T j k x)
          = ∑ j : ι, ∫ x in box N L, (∑ k : Fin 3, T j k x) := by
            refine Finset.sum_congr rfl (fun j hj => ?_)
            rw [integral_finsetSum (s := Finset.univ) (μ := volume.restrict (box N L))
              (f := fun k : Fin 3 => T j k) (fun k hk => hI_T j k)]
      _ = ∫ x in box N L, (∑ j : ι, ∑ k : Fin 3, T j k x) := by
            rw [integral_finsetSum (s := Finset.univ) (μ := volume.restrict (box N L))
              (f := fun j : ι => fun x : X N => ∑ k : Fin 3, T j k x) (fun j hj => hI_Tj j)]
  have hRHS : (∑ k : Fin 3, ∫ x in box N L, A k x) + (∑ j : ι, ∫ x in box N L, C j x) =
      ∫ x in box N L, (∑ k : Fin 3, A k x) + (∑ j : ι, C j x) := by
    calc
      (∑ k : Fin 3, ∫ x in box N L, A k x) + (∑ j : ι, ∫ x in box N L, C j x)
          = (∫ x in box N L, ∑ k : Fin 3, A k x) + (∫ x in box N L, ∑ j : ι, C j x) := by
            congr 1
            · rw [integral_finsetSum (s := Finset.univ) (μ := volume.restrict (box N L))
                (f := fun k : Fin 3 => A k) (fun k hk => hI_A k)]
            · rw [integral_finsetSum (s := Finset.univ) (μ := volume.restrict (box N L))
                (f := fun j : ι => C j) (fun j hj => hI_C j)]
      _ = ∫ x in box N L, (∑ k : Fin 3, A k x) + (∑ j : ι, C j x) := by
            rw [← integral_add (μ := volume.restrict (box N L)) hI_A_sum hI_C_sum]
  change (∑ j : ι, ∑ k : Fin 3, ∫ x in box N L, T j k x) =
      (∑ k : Fin 3, ∫ x in box N L, A k x) + (∑ j : ι, ∫ x in box N L, C j x)
  calc
    (∑ j : ι, ∑ k : Fin 3, ∫ x in box N L, T j k x)
        = ∫ x in box N L, (∑ j : ι, ∑ k : Fin 3, T j k x) := hLHS
    _ = ∫ x in box N L, (∑ k : Fin 3, A k x) + (∑ j : ι, C j x) := by
          exact MeasureTheory.integral_congr_ae (μ := volume.restrict (box N L)) hpt
    _ = (∑ k : Fin 3, ∫ x in box N L, A k x) + (∑ j : ι, ∫ x in box N L, C j x) := hRHS.symm

lemma cell_err_integral_le {N m : ℕ} {ℓ A : ℝ} (hm : 1 ≤ m) (hℓ : 0 < ℓ)
    (hA0 : 0 ≤ A) (hA : ∀ t : ℝ, |deriv rhoProfile t| ≤ A) (i : Fin N)
    (Ψ : CInfty0Box N ((m : ℝ) * ℓ)) :
    (∑ c : CellIdx m, ∫ x in box N ((m : ℝ) * ℓ), ((Ψ : X N → ℝ) x) ^ 2 *
        (∑ k : Fin 3, (fderiv ℝ (cellCut ℓ m c) (x i) (kcStdBasis k)) ^ 2)) ≤
      (6 * A ^ 2 / ℓ ^ 2) * (∫ x in box N ((m : ℝ) * ℓ), ((Ψ : X N → ℝ) x) ^ 2) := by
  have hmR : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mp hm)
  have hL : 0 < (m : ℝ) * ℓ := mul_pos hmR hℓ
  have hf : ContDiff ℝ ∞ (Ψ : X N → ℝ) := psi_contDiff Ψ
  let χ : CellIdx m → ℝ³ → ℝ := fun c => cellCut ℓ m c
  have hχ : ∀ c : CellIdx m, ContDiff ℝ ∞ (χ c) := by
    intro c
    dsimp [χ]
    exact cellCut_contDiff ℓ m c
  let C0 : ℝ := 6 * A ^ 2 / ℓ ^ 2
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    positivity
  have hC : ∀ x : X N, x ∈ box N ((m : ℝ) * ℓ) →
      (∑ c : CellIdx m, ∑ k : Fin 3, (fderiv ℝ (χ c) (x i) (kcStdBasis k)) ^ 2) ≤ C0 := by
    intro x hx
    dsimp [χ, C0]
    exact cell_partial_sq_sum_le (hℓ := hℓ) (hA0 := hA0) (hA := hA) (m := m) (y := x i) (fun k => hx i k)
  let g : CellIdx m → X N → ℝ := fun c x => (((Ψ : X N → ℝ) x) ^ 2) *
      ∑ k : Fin 3, (fderiv ℝ (χ c) (x i) (kcStdBasis k)) ^ 2
  let E : X N → ℝ := fun x => ∑ c : CellIdx m, g c x
  let F : X N → ℝ := fun x => C0 * (((Ψ : X N → ℝ) x) ^ 2)
  have hgcont : ∀ c : CellIdx m, Continuous (g c) := by
    intro c
    dsimp [g]
    refine (hf.continuous.pow 2).mul ?_
    refine continuous_finsetSum (s := Finset.univ)
      (f := fun (k : Fin 3) (x : X N) => (fderiv ℝ (χ c) (x i) (kcStdBasis k)) ^ 2) ?_
    intro k hk
    have hfdj : ContDiff ℝ ∞ (fderiv ℝ (χ c)) := ContDiff.fderiv_right (m := ∞) (hχ c) (by simp)
    have heval : ContDiff ℝ ∞ (fun (L : ℝ³ →L[ℝ] ℝ) => L (kcStdBasis k)) := by
      exact ((ContinuousLinearMap.apply (𝕜 := ℝ) (Fₗ := ℝ) (kcStdBasis k) : (ℝ³ →L[ℝ] ℝ) →L[ℝ] ℝ).contDiff)
    have hz : ContDiff ℝ ∞ (fun z : ℝ³ => fderiv ℝ (χ c) z (kcStdBasis k)) := by
      simpa [Function.comp_def] using heval.comp hfdj
    have hpi : Continuous (fun x : X N => x i) := continuous_apply i
    exact ((hz.continuous.comp hpi).pow 2)
  have hEcont : Continuous E := by
    dsimp [E]
    refine continuous_finsetSum (s := Finset.univ) (f := fun (c : CellIdx m) (x : X N) => g c x) ?_
    intro c hc
    exact hgcont c
  have hFcont : Continuous F := by
    dsimp [F]
    exact continuous_const.mul (hf.continuous.pow 2)
  have hI_E : IntegrableOn E (box N ((m : ℝ) * ℓ)) volume := bl_cont_integrableOn hL hEcont
  have hI_F : IntegrableOn F (box N ((m : ℝ) * ℓ)) volume := bl_cont_integrableOn hL hFcont
  have hI_g : ∀ c, IntegrableOn (g c) (box N ((m : ℝ) * ℓ)) volume := fun c =>
    bl_cont_integrableOn hL (hgcont c)
  have hpt_le : (fun x : X N => ∑ c : CellIdx m, g c x) ≤ᵐ[volume.restrict (box N ((m : ℝ) * ℓ))]
      fun x : X N => C0 * (((Ψ : X N → ℝ) x) ^ 2) := by
    refine (ae_restrict_mem (box_measurable N ((m : ℝ) * ℓ))).mono ?_
    intro x hx
    calc
      (∑ c : CellIdx m, g c x)
          = ∑ c : CellIdx m, ((Ψ : X N → ℝ) x) ^ 2 * (∑ k : Fin 3, (fderiv ℝ (χ c) (x i) (kcStdBasis k)) ^ 2) := by
            dsimp [g]
      _ = ((Ψ : X N → ℝ) x) ^ 2 * (∑ c : CellIdx m, ∑ k : Fin 3, (fderiv ℝ (χ c) (x i) (kcStdBasis k)) ^ 2) := by
            rw [← Finset.mul_sum]
      _ ≤ ((Ψ : X N → ℝ) x) ^ 2 * C0 := mul_le_mul_of_nonneg_left (hC x hx) (sq_nonneg ((Ψ : X N → ℝ) x))
      _ = C0 * ((Ψ : X N → ℝ) x) ^ 2 := by ring
  have herr : (∑ c : CellIdx m, ∫ x in box N ((m : ℝ) * ℓ), g c x) ≤
      C0 * (∫ x in box N ((m : ℝ) * ℓ), ((Ψ : X N → ℝ) x) ^ 2) := by
    calc
      (∑ c : CellIdx m, ∫ x in box N ((m : ℝ) * ℓ), g c x)
          = ∫ x in box N ((m : ℝ) * ℓ), (∑ c : CellIdx m, g c x) := by
            rw [integral_finsetSum (s := Finset.univ) (μ := volume.restrict (box N ((m : ℝ) * ℓ)))
              (f := fun c : CellIdx m => g c) (fun c hc => hI_g c)]
      _ ≤ ∫ x in box N ((m : ℝ) * ℓ), C0 * (((Ψ : X N → ℝ) x) ^ 2) := by
            refine MeasureTheory.integral_mono_ae (μ := volume.restrict (box N ((m : ℝ) * ℓ)))
              (f := fun x : X N => ∑ c : CellIdx m, g c x)
              (g := fun x : X N => C0 * (((Ψ : X N → ℝ) x) ^ 2)) ?_ ?_ ?_
            · exact hI_E
            · exact hI_F
            · exact hpt_le
      _ = C0 * (∫ x in box N ((m : ℝ) * ℓ), ((Ψ : X N → ℝ) x) ^ 2) := by
            rw [MeasureTheory.integral_const_mul C0 (fun x : X N => ((Ψ : X N → ℝ) x) ^ 2)]
  simpa [g, χ, C0] using herr

/-- **The box-level localization bound.**  For a Dirichlet state `Ψ` in
`box N (m·ℓ)` and the `m³`-cell cutoffs `cellCut ℓ m` of `CellGrid`
(partition of unity on the cube, error density ≤ `6A²/ℓ²`), localising
particle `i` costs kinetic energy at most `(6A²/ℓ²)·‖Ψ‖²`. -/
lemma boxLocalize_kinetic_le {N m : ℕ} {ℓ A : ℝ} (hm : 1 ≤ m) (hℓ : 0 < ℓ)
    (hA0 : 0 ≤ A) (hA : ∀ t : ℝ, |deriv rhoProfile t| ≤ A) (i : Fin N)
    (Ψ : CInfty0Box N ((m : ℝ) * ℓ)) :
    (∑ c : CellIdx m, ∑ k : Fin 3, ∫ x in box N ((m : ℝ) * ℓ),
        (fderiv ℝ (fun y : X N => cellCut ℓ m c (y i) * (Ψ : X N → ℝ) y) x
          (kcDir N i k)) ^ 2) ≤
      (∑ k : Fin 3, ∫ x in box N ((m : ℝ) * ℓ),
        (fderiv ℝ (Ψ : X N → ℝ) x (kcDir N i k)) ^ 2) +
        (6 * A ^ 2 / ℓ ^ 2) * (∫ x in box N ((m : ℝ) * ℓ),
          ((Ψ : X N → ℝ) x) ^ 2) := by
  have hmR : 0 < (m : ℝ) := by
    exact_mod_cast (Nat.succ_le_iff.mp hm)
  have hL : 0 < (m : ℝ) * ℓ := mul_pos hmR hℓ
  have hχ : ∀ c : CellIdx m, ContDiff ℝ ∞ (cellCut ℓ m c) := fun c => cellCut_contDiff ℓ m c
  have hpu_cube : ∀ y : ℝ³, y ∈ cubeOp ((m : ℝ) * ℓ) →
      (∑ c : CellIdx m, (cellCut ℓ m c y) ^ 2) = 1 := by
    intro y hy
    exact cellCut_pu hℓ m (fun k => by
      have hyk : y k ∈ Set.Ioo 0 ((m : ℝ) * ℓ) := hy k
      exact ⟨le_of_lt hyk.1, le_of_lt hyk.2⟩)
  have hmain := ims_box_identity (N := N) (ι := CellIdx m) (L := (m : ℝ) * ℓ) hL i Ψ
    (fun c : CellIdx m => cellCut ℓ m c) hχ hpu_cube
  have herr := cell_err_integral_le (N := N) (m := m) (ℓ := ℓ) (A := A) hm hℓ hA0 hA i Ψ
  nlinarith
end BoseGases

end Submission
