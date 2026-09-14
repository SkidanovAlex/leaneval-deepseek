import Mathlib
import Submission.GaussianMeasure

open Module Real MeasureTheory Matrix Filter
open MeasureTheory.Measure
open scoped Real BigOperators Topology
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# Shape derivatives over positions of the Voronoi cell (paper §4, §5.1, §6)

Goal (paper Thm 4.12 first half): a local extremum of `A ↦ γ_s(V(A·ℒ))` over the
determinant-one matrices at `A = I` implies `V(ℒ)` is in *isotropic Gaussian position*
at parameter `s`, i.e.
`G := ∫_{x ∈ V(ℒ)/s} e^{−π‖x‖²} xxᵀ dx = α·I` for some scalar `α`.

Design (Session-103s, γ-route):
* (S1) shape derivative along a smooth det-one curve `A : ℝ → Matrix (Fin m)(Fin m) ℝ`
  through `A 0 = 1` with tangent `A′ 0 = M`:
  `deriv (fun t => ∫ y in V(ℒ)/s, rexp(-π·‖(A t)•ᵥ y‖²)) 0 = -2π·∫ y in V(ℒ)/s,
  rexp(-π·‖y‖²)·⟨y, M•ᵥy⟩` (one-variable calculus on the bounded set `V(ℒ)/s`).
* (S2, DONE below) trace-zero orthogonality ⟹ scalar: a symmetric matrix Frobenius-
  orthogonal to every trace-zero symmetric matrix is a scalar multiple of the identity.
* (S3) assembly: local extremum over det-one ⟹ for every trace-zero symmetric tangent
  `M`, `deriv g 0 = 0`; by (S1) this is `⟨M, G⟩_F = 0`; (S2) gives `G = α·I` ⟹ isotropic.
-/

namespace Submission.ShapeDeriv

/-- **S2.** A symmetric matrix `G` whose Frobenius inner product with every symmetric
trace-zero matrix vanishes is a scalar multiple of the identity. -/
theorem symm_of_orthogonal_to_trace_zero (m : ℕ) (hm : 2 ≤ m)
    (G : Matrix (Fin m) (Fin m) ℝ) (hG : G.IsSymm)
    (h : ∀ M : Matrix (Fin m) (Fin m) ℝ, M.IsSymm → M.trace = 0 →
      (∑ i : Fin m, ∑ j : Fin m, M i j * G i j) = 0) :
    ∃ α : ℝ, G = α • (1 : Matrix (Fin m) (Fin m) ℝ) := by
  classical
  let α : ℝ := G.trace / (m : ℝ)
  let M : Matrix (Fin m) (Fin m) ℝ := G - α • (1 : Matrix (Fin m) (Fin m) ℝ)
  have hmR : (m : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by omega : 0 < m))
  have hGpt : ∀ i j : Fin m, G i j = G j i := by
    intro i j
    have hc := congr_fun (congr_fun hG j) i
    simpa [Matrix.transpose_apply] using hc
  have hsym1 : (α • (1 : Matrix (Fin m) (Fin m) ℝ)).IsSymm := by
    rw [Matrix.IsSymm]
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · have hji : j ≠ i := by exact fun h => hij h.symm
      simp [hij, hji]
  have hsymM : M.IsSymm := by
    rw [Matrix.IsSymm]
    ext i j
    by_cases hij : i = j
    · subst j
      simp [M, Matrix.sub_apply, Matrix.transpose_apply, Matrix.smul_apply]
    · have hji : j ≠ i := by exact fun h => hij h.symm
      simp [M, Matrix.sub_apply, Matrix.transpose_apply, Matrix.smul_apply, hij, hji]
      exact hGpt j i
  have htr1 : (1 : Matrix (Fin m) (Fin m) ℝ).trace = (m : ℝ) := by
    simp
  have htrM : M.trace = 0 := by
    dsimp [M, α]
    rw [Matrix.trace_sub, Matrix.trace_smul, htr1]
    rw [smul_eq_mul]
    field_simp [hmR]
    ring_nf
  have hdiag : (∑ i : Fin m, M i i) = 0 := by
    simpa [Matrix.trace] using htrM
  have hGm : G = M + α • (1 : Matrix (Fin m) (Fin m) ℝ) := by
    dsimp [M]
    rw [sub_add_cancel]
  have hterm (i j : Fin m) : M i j * G i j = (M i j) ^ 2 + (if i = j then α * M i i else 0) := by
    have hGij : G i j = M i j + (if i = j then α else 0) := by
      have hc := congr_fun (congr_fun hGm i) j
      simpa [Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply, add_comm, add_left_comm,
        add_assoc] using hc
    by_cases hij : i = j
    · subst j
      rw [hGij]
      simp
      ring_nf
    · rw [hGij]
      simp [hij]
      ring_nf
  have hsumj : ∀ i : Fin m,
      (∑ j : Fin m, M i j * G i j) = (∑ j : Fin m, (M i j) ^ 2) + α * M i i := by
    intro i
    calc
      (∑ j : Fin m, M i j * G i j)
          = ∑ j : Fin m, ((M i j) ^ 2 + (if i = j then α * M i i else 0)) := by
            apply Finset.sum_congr rfl
            intro j hj
            exact hterm i j
      _ = (∑ j : Fin m, (M i j) ^ 2) + ∑ j : Fin m, (if i = j then α * M i i else 0) := by
            rw [Finset.sum_add_distrib]
      _ = (∑ j : Fin m, (M i j) ^ 2) + α * M i i := by
            congr 1
            rw [Finset.sum_ite_eq]
            simp
  have hsplit : (∑ i : Fin m, ∑ j : Fin m, M i j * G i j)
      = (∑ i : Fin m, ∑ j : Fin m, (M i j) ^ 2) + α * (∑ i : Fin m, M i i) := by
    calc
      (∑ i : Fin m, ∑ j : Fin m, M i j * G i j)
          = ∑ i : Fin m, ((∑ j : Fin m, (M i j) ^ 2) + α * M i i) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact hsumj i
      _ = (∑ i : Fin m, ∑ j : Fin m, (M i j) ^ 2) + α * (∑ i : Fin m, M i i) := by
            rw [Finset.sum_add_distrib]
            rw [← Finset.mul_sum]
  have hMG : (∑ i : Fin m, ∑ j : Fin m, M i j * G i j) = 0 := h M hsymM htrM
  have hconcl : (∑ i : Fin m, ∑ j : Fin m, (M i j) ^ 2) = 0 := by
    calc
      (∑ i : Fin m, ∑ j : Fin m, (M i j) ^ 2)
          = (∑ i : Fin m, ∑ j : Fin m, (M i j) ^ 2) + α * (∑ i : Fin m, M i i) := by
            rw [hdiag]
            ring
      _ = (∑ i : Fin m, ∑ j : Fin m, M i j * G i j) := hsplit.symm
      _ = 0 := hMG
  have hM0 : ∀ i j : Fin m, M i j = 0 := by
    intro i j
    have h1 : ∀ i' : Fin m, (∑ j' : Fin m, (M i' j') ^ 2) = 0 := by
      intro i'
      exact (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun k : Fin m => ∑ j' : Fin m, (M k j') ^ 2)
        (by intro k hk; exact Finset.sum_nonneg (by intro j' hj; exact sq_nonneg (M k j')))).mp
        hconcl i' (Finset.mem_univ i')
    have h2 : (M i j) ^ 2 = 0 := by
      exact (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (f := fun k : Fin m => (M i k) ^ 2)
        (by intro k hk; exact sq_nonneg (M i k))).mp (h1 i) j (Finset.mem_univ j)
    exact sq_eq_zero_iff.mp h2
  refine ⟨α, ?_⟩
  have hMzero : M = 0 := by
    ext i j
    exact hM0 i j
  rw [hGm, hMzero, zero_add]


/-! ## S1 — shape derivative along the affine position curve (paper §4, §5.1, §6)

**`shapeDeriv`** is the one-variable calculus core used by S3: for any measurable set
`K ⊆ E` (in the application `K := V(ℒ)/s`, the scaled Voronoi cell), and any `m × m`
matrix `M` acting on `E` by `mvec M` (matrix-vector multiplication through the
`WithLp`/EuclideanSpace identification),

`d/dt|₀ ∫_{y∈K} e^{−π‖(1 + tM)y‖²} dy = −2π · ∫_{y∈K} e^{−π‖y‖²}·⟨y, My⟩ dy`.

It is proved with `MeasureTheory.hasDerivAt_integral_of_dominated_loc_of_deriv_le`
(differentiation under the integral): the integrand and its partial derivative are
continuous (hence strongly measurable), the Gaussian integrand is integrable on any
measurable `K`, the derivative is dominated on a neighbourhood of `t = 0` by the
integrable function `y ↦ 24L·e^{−π‖y‖²/8}` (using `‖My‖ ≤ L‖y‖` and the elementary
decay `‖y‖²e^{−π‖y‖²/8} ≤ 8/π`), and the pointwise derivative is the chain-rule
computation `d/dt e^{−π‖y+tMy‖²} = −2π e^{−π‖y+tMy‖²}⟨y+tMy, My⟩`.
-/

section S1

variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

/-- Matrix-vector action on the Euclidean space (ℝ-linear in the matrix). -/
def mvec (M : Matrix (Fin m) (Fin m) ℝ) : E →ₗ[ℝ] E := Matrix.toLpLin 2 2 M

/-- `(1 + t•M)•y = y + t•(M•y)` along the curve. -/
lemma path_eq (M : Matrix (Fin m) (Fin m) ℝ) (t : ℝ) (y : E) :
    mvec ((1 : Matrix (Fin m) (Fin m) ℝ) + t • M) y = y + t • (mvec M y : E) := by
  simp [mvec, Matrix.toLpLin_apply]

lemma affine_path_deriv (v w : E) (x : ℝ) :
    HasDerivAt (fun t : ℝ => w + t • v) v x := by
  have hid := hasDerivAt_id (𝕜 := ℝ) x
  have hs := hid.smul_const v
  have hc : HasDerivAt (fun _t : ℝ => w) 0 x := hasDerivAt_const x w
  have hA := hc.add hs
  rw [show (fun t : ℝ => w + t • v) = (fun _t : ℝ => w) + (fun t : ℝ => t • v) by rfl]
  simpa using hA

lemma norm_sq_path_deriv (v w : E) (x : ℝ) :
    HasDerivAt (fun t : ℝ => ‖w + t • v‖ ^ 2) (2 * inner ℝ (w + x • v) v) x := by
  simpa using (affine_path_deriv v w x).norm_sq

/-- d/dt exp(-π‖w + t•v‖²) at t = x. -/
lemma exp_path_deriv' (v w : E) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp ((-Real.pi) * ‖w + t • v‖ ^ 2))
      (Real.exp ((-Real.pi) * (‖w + x • v‖ ^ 2 : ℝ)) * (-Real.pi) *
        (2 * inner ℝ (w + x • v) v)) x := by
  have hu : HasDerivAt (fun t : ℝ => ‖w + t • v‖ ^ 2)
      (2 * inner ℝ (w + x • v) v) x := norm_sq_path_deriv v w x
  have hlin : HasDerivAt (fun u : ℝ => (-Real.pi) * u) (-Real.pi)
      (‖w + x • v‖ ^ 2 : ℝ) := by
    exact (hasDerivAt_const_mul (-Real.pi) :
      HasDerivAt (fun u : ℝ => (-Real.pi) * u) (-Real.pi) (‖w + x • v‖ ^ 2 : ℝ))
  have hg : HasDerivAt (Real.exp ∘ (fun u : ℝ => (-Real.pi) * u))
      (Real.exp ((-Real.pi) * (‖w + x • v‖ ^ 2 : ℝ)) * (-Real.pi)) (‖w + x • v‖ ^ 2 : ℝ) := by
    exact (hasDerivAt_exp ((-Real.pi) * (‖w + x • v‖ ^ 2 : ℝ))).comp
      (‖w + x • v‖ ^ 2 : ℝ) hlin
  exact hg.comp x hu

/-- The integrand and its partial derivative in the parameter. -/
noncomputable def Fd (M : Matrix (Fin m) (Fin m) ℝ) (x : ℝ) (y : E) : ℝ :=
  Real.exp ((-Real.pi) * ‖y + x • (mvec M y : E)‖ ^ 2)

noncomputable def Fd' (M : Matrix (Fin m) (Fin m) ℝ) (x : ℝ) (y : E) : ℝ :=
  Real.exp ((-Real.pi) * (‖y + x • (mvec M y : E)‖ ^ 2 : ℝ)) * (-Real.pi) *
    (2 * inner ℝ (y + x • (mvec M y : E)) (mvec M y))

-- pointwise derivative of Fd·y from exp_path_deriv'
lemma Fd_hasDerivAt (M : Matrix (Fin m) (Fin m) ℝ) (y : E) (x : ℝ) :
    HasDerivAt (fun t : ℝ => Fd M t y) (Fd' M x y) x := by
  dsimp [Fd, Fd']
  exact exp_path_deriv' (mvec M y) y x

-- continuity
lemma Fd_continuous (M : Matrix (Fin m) (Fin m) ℝ) (x : ℝ) :
    Continuous (fun y : E => Fd M x y) := by
  unfold Fd
  fun_prop

lemma Fd'_continuous (M : Matrix (Fin m) (Fin m) ℝ) (x : ℝ) :
    Continuous (fun y : E => Fd' M x y) := by
  unfold Fd'
  fun_prop

-- mvec-bound helper
lemma mvec_bound (M : Matrix (Fin m) (Fin m) ℝ) :
    ∃ L : ℝ, 0 < L ∧ ∀ y : E, ‖mvec M y‖ ≤ L * ‖y‖ := by
  have hb := (mvec M).toContinuousLinearMap.bound
  rcases hb with ⟨C, hC, hb'⟩
  refine ⟨C, hC, ?_⟩
  intro y
  simpa using hb' y

/-- integrability of a pure Gaussian weight over E -/
lemma gaussian_b_integrable (b : ℝ) (hb : 0 < b) :
    Integrable (fun y : E => rexp (-b * ‖y‖ ^ 2)) (volume : Measure E) := by
  refine Integrable.of_integral_ne_zero ?_
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) (b := b) hb
  rw [h]
  have hfin : Module.finrank ℝ E = m := by simp
  rw [hfin]
  positivity

lemma Fd0_integrableOn (M : Matrix (Fin m) (Fin m) ℝ) (K : Set E) :
    Integrable (Fd M 0) (volume.restrict K) := by
  have hG : Integrable (fun y : E => rexp (-Real.pi * ‖y‖ ^ 2)) (volume.restrict K) := by
    simpa [MeasureTheory.IntegrableOn] using
      (Submission.GaussianMeasure.gaussian_density_integrable.integrableOn (s := K))
  have hpt : (fun y : E => rexp (-Real.pi * ‖y‖ ^ 2)) =ᵐ[volume.restrict K]
      (fun y : E => Fd M 0 y) := by
    refine Filter.Eventually.of_forall ?_
    intro y
    simp [Fd]
  exact hG.congr hpt

lemma mul_exp_neg_le_one {u : ℝ} : u * rexp (-u) ≤ 1 := by
  calc
    u * rexp (-u) ≤ rexp (-1) := mul_exp_neg_le_exp_neg_one u
    _ ≤ 1 := by exact (Real.exp_le_one_iff).2 (by norm_num)

lemma norm_sq_exp_decay (y : E) :
    ‖y‖ ^ 2 * rexp (-(Real.pi / 8) * ‖y‖ ^ 2) ≤ 8 / Real.pi := by
  have hm : ((Real.pi / 8) * ‖y‖ ^ 2) * rexp (-((Real.pi / 8) * ‖y‖ ^ 2)) ≤ 1 :=
    mul_exp_neg_le_one (u := (Real.pi / 8) * ‖y‖ ^ 2)
  have hstep1 : ‖y‖ ^ 2 * rexp (-(Real.pi / 8) * ‖y‖ ^ 2) =
      (8 / Real.pi) * (((Real.pi / 8) * ‖y‖ ^ 2) * rexp (-((Real.pi / 8) * ‖y‖ ^ 2))) := by
    field_simp [Real.pi_ne_zero]
  rw [hstep1]
  calc
    (8 / Real.pi) * (((Real.pi / 8) * ‖y‖ ^ 2) * rexp (-((Real.pi / 8) * ‖y‖ ^ 2))) ≤ (8 / Real.pi) * 1 := by
      exact mul_le_mul_of_nonneg_left hm (by positivity)
    _ = 8 / Real.pi := by ring

lemma norm_sq_exp_quarter_le (y : E) :
    ‖y‖ ^ 2 * rexp (-Real.pi * ‖y‖ ^ 2 / 4) ≤ (8 / Real.pi) * rexp (-(Real.pi / 8) * ‖y‖ ^ 2) := by
  have h := norm_sq_exp_decay y
  have hsplit : -Real.pi * ‖y‖ ^ 2 / 4 = (-(Real.pi / 8)) * ‖y‖ ^ 2 + (-(Real.pi / 8)) * ‖y‖ ^ 2 := by ring
  calc
    ‖y‖ ^ 2 * rexp (-Real.pi * ‖y‖ ^ 2 / 4)
        = ‖y‖ ^ 2 * rexp ((-(Real.pi / 8)) * ‖y‖ ^ 2 + (-(Real.pi / 8)) * ‖y‖ ^ 2) := by rw [hsplit]
    _ = ‖y‖ ^ 2 * (rexp ((-(Real.pi / 8)) * ‖y‖ ^ 2) * rexp ((-(Real.pi / 8)) * ‖y‖ ^ 2)) := by
          rw [Real.exp_add]
    _ = (‖y‖ ^ 2 * rexp ((-(Real.pi / 8)) * ‖y‖ ^ 2)) * rexp ((-(Real.pi / 8)) * ‖y‖ ^ 2) := by ring
    _ ≤ (8 / Real.pi) * rexp ((-(Real.pi / 8)) * ‖y‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

lemma Fd'_norm_bound (M : Matrix (Fin m) (Fin m) ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hLip : ∀ y : E, ‖mvec M y‖ ≤ L * ‖y‖) (y : E) {x : ℝ} (hx : |x| * L ≤ 1 / 2) :
    |Fd' M x y| ≤ (24 * L) * rexp (-(Real.pi / 8) * ‖y‖ ^ 2) := by
  let v : E := mvec M y
  let A : E := y + x • v
  have h1 : ‖v‖ ≤ L * ‖y‖ := hLip y
  have hxv : ‖x • v‖ ≤ ‖y‖ / 2 := by
    calc
      ‖x • v‖ = |x| * ‖v‖ := by simp [norm_smul]
      _ ≤ |x| * (L * ‖y‖) := mul_le_mul_of_nonneg_left h1 (abs_nonneg x)
      _ = (|x| * L) * ‖y‖ := by ring
      _ ≤ (1 / 2) * ‖y‖ := mul_le_mul_of_nonneg_right hx (norm_nonneg y)
      _ = ‖y‖ / 2 := by ring
  have hnormA : ‖A‖ ≤ (3 / 2) * ‖y‖ := by
    calc
      ‖A‖ = ‖y + x • v‖ := rfl
      _ ≤ ‖y‖ + ‖x • v‖ := norm_add_le _ _
      _ ≤ ‖y‖ + ‖y‖ / 2 := add_le_add le_rfl hxv
      _ = (3 / 2) * ‖y‖ := by ring
  have hnormA2 : ‖y‖ / 2 ≤ ‖A‖ := by
    have hle : ‖y‖ ≤ ‖A‖ + ‖x • v‖ := by
      have h : y = (y + x • v) + (-(x • v)) := by abel
      calc
        ‖y‖ = ‖(y + x • v) + (-(x • v))‖ := by rw [← h]
        _ ≤ ‖y + x • v‖ + ‖-(x • v)‖ := norm_add_le _ _
        _ = ‖A‖ + ‖x • v‖ := by simp [A]
    linarith
  have hsq : (‖y‖ / 2) ^ 2 ≤ ‖A‖ ^ 2 := by
    have hy2 : 0 ≤ ‖y‖ / 2 := by positivity
    have hAbs : |‖y‖ / 2| ≤ |‖A‖| := by
      rw [abs_of_nonneg hy2, abs_of_nonneg (norm_nonneg A)]
      exact hnormA2
    exact sq_le_sq.mpr hAbs
  have hd1 : rexp (-Real.pi * ‖A‖ ^ 2) ≤ rexp (-Real.pi * (‖y‖ ^ 2 / 4)) := by
    apply Real.exp_le_exp.mpr
    have hsq2 : ‖y‖ ^ 2 / 4 ≤ ‖A‖ ^ 2 := by
      have : (‖y‖ / 2) ^ 2 = ‖y‖ ^ 2 / 4 := by ring
      rwa [this] at hsq
    have hπ : 0 < Real.pi := Real.pi_pos
    nlinarith
  have h1a : |rexp ((-Real.pi) * ‖A‖ ^ 2) * (-Real.pi)| =
      rexp ((-Real.pi) * ‖A‖ ^ 2) * Real.pi := by
    rw [abs_mul, abs_neg, abs_of_pos (Real.exp_pos _),
      abs_of_pos Real.pi_pos]
  have h1b : |2 * inner ℝ A v| ≤ 2 * (‖A‖ * ‖v‖) := by
    calc
      |2 * inner ℝ A v| = 2 * |inner ℝ A v| := by
        rw [abs_mul, abs_of_pos (show 0 < (2 : ℝ) by norm_num)]
      _ ≤ 2 * (‖A‖ * ‖v‖) := by
        exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm A v) (by norm_num)
  calc
    |Fd' M x y| ≤ 2 * Real.pi * rexp (-Real.pi * ‖A‖ ^ 2) * ‖A‖ * ‖v‖ := by
      dsimp [Fd']
      calc
        |rexp ((-Real.pi) * ‖A‖ ^ 2) * (-Real.pi) * (2 * inner ℝ A v)|
            = |rexp ((-Real.pi) * ‖A‖ ^ 2) * (-Real.pi)| * |2 * inner ℝ A v| := by rw [abs_mul]
        _ = (rexp ((-Real.pi) * ‖A‖ ^ 2) * Real.pi) * |2 * inner ℝ A v| := by rw [h1a]
        _ ≤ (rexp ((-Real.pi) * ‖A‖ ^ 2) * Real.pi) * (2 * (‖A‖ * ‖v‖)) := by
              exact mul_le_mul_of_nonneg_left h1b (by positivity)
        _ = 2 * Real.pi * rexp ((-Real.pi) * ‖A‖ ^ 2) * ‖A‖ * ‖v‖ := by ring
    _ ≤ 2 * Real.pi * rexp (-Real.pi * (‖y‖ ^ 2 / 4)) * ((3 / 2) * ‖y‖) * (L * ‖y‖) := by
      gcongr
    _ = 3 * Real.pi * L * (‖y‖ ^ 2 * rexp (-Real.pi * ‖y‖ ^ 2 / 4)) := by ring
    _ ≤ 3 * Real.pi * L * ((8 / Real.pi) * rexp (-(Real.pi / 8) * ‖y‖ ^ 2)) := by
      exact mul_le_mul_of_nonneg_left (norm_sq_exp_quarter_le y) (by positivity)
    _ = (24 * L) * rexp (-(Real.pi / 8) * ‖y‖ ^ 2) := by
      field_simp [Real.pi_ne_zero]
      ring_nf

/-- **S1.** Shape derivative of the (γ-style) Gaussian integral over `K`: for any
measurable `K` and matrix `M`, `d/dt|₀ ∫_{y∈K} e^{-π‖y + t·(M·y)‖²} = -2π ∫_K
e^{-π‖y‖²}⟨y, M·y⟩`. -/
theorem shapeDeriv (M : Matrix (Fin m) (Fin m) ℝ) (K : Set E) (hK : MeasurableSet K) :
    HasDerivAt (fun t : ℝ => ∫ y in K, Fd M t y)
      (-2 * Real.pi * ∫ y in K, rexp (-Real.pi * ‖y‖ ^ 2) * inner ℝ y (mvec M y)) 0 := by
  classical
  rcases mvec_bound M with ⟨L, hLpos, hLip⟩
  have hL : 0 ≤ L := le_of_lt hLpos
  let ε : ℝ := 1 / (2 * (L + 1))
  have hεpos : 0 < ε := by positivity
  let s : Set ℝ := Metric.ball (0 : ℝ) ε
  have hs : s ∈ 𝓝 (0 : ℝ) := Metric.ball_mem_nhds 0 hεpos
  let μ : Measure E := volume.restrict K
  let bd : E → ℝ := fun y => (24 * L) * rexp (-(Real.pi / 8) * ‖y‖ ^ 2)
  have hF_meas : ∀ᶠ x in 𝓝 (0 : ℝ), AEStronglyMeasurable (Fd M x) μ := by
    refine Filter.Eventually.of_forall ?_
    intro x
    exact (Fd_continuous M x).stronglyMeasurable.aestronglyMeasurable
  have hF_int : Integrable (Fd M 0) μ := Fd0_integrableOn M K
  have hF'_meas : AEStronglyMeasurable (Fd' M 0) μ :=
    (Fd'_continuous M 0).stronglyMeasurable.aestronglyMeasurable
  have hxL : ∀ {x : ℝ}, x ∈ s → |x| * L ≤ 1 / 2 := by
    intro x hx
    have hxε : |x| ≤ ε := by
      have hd : dist x 0 < ε := hx
      simpa using (le_of_lt hd)
    have hle : ε * L ≤ 1 / 2 := by
      have hεL : ε * L = L / (2 * (L + 1)) := by
        dsimp [ε]
        ring
      rw [hεL]
      rw [div_le_iff₀ (show 0 < 2 * (L + 1) by positivity)]
      nlinarith
    calc
      |x| * L ≤ ε * L := mul_le_mul_of_nonneg_right hxε hL
      _ ≤ 1 / 2 := hle
  have h_bound : ∀ᵐ y ∂μ, ∀ x ∈ s, ‖Fd' M x y‖ ≤ bd y := by
    refine Filter.Eventually.of_forall ?_
    intro y x hx
    exact Fd'_norm_bound M L hL hLip y (hxL hx)
  have bd_integrable : Integrable bd μ := by
    have hbE : Integrable (fun y : E => rexp (-(Real.pi / 8) * ‖y‖ ^ 2)) (volume : Measure E) :=
      gaussian_b_integrable (Real.pi / 8) (by positivity)
    have hbE' : Integrable (fun y : E => (24 * L) * rexp (-(Real.pi / 8) * ‖y‖ ^ 2))
        (volume : Measure E) := by
      simpa using hbE.const_mul (24 * L)
    simpa [MeasureTheory.IntegrableOn, bd, μ] using hbE'.integrableOn (s := K)
  have h_diff : ∀ᵐ y ∂μ, ∀ x ∈ s, HasDerivAt (fun t : ℝ => Fd M t y) (Fd' M x y) x := by
    refine Filter.Eventually.of_forall ?_
    intro y x hx
    exact Fd_hasDerivAt M y x
  have hres := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℝ)
    (F := fun x : ℝ => Fd M x) (x₀ := 0) (s := s) (μ := μ)
    (F' := fun x : ℝ => Fd' M x) (bound := bd)
    hs hF_meas hF_int hF'_meas h_bound bd_integrable h_diff
  rcases hres with ⟨hint, hder⟩
  have hval : (∫ y in K, Fd' M 0 y) =
      -2 * Real.pi * (∫ y in K, rexp (-Real.pi * ‖y‖ ^ 2) * inner ℝ y (mvec M y)) := by
    have hpt : ∀ y ∈ K, Fd' M 0 y =
        -2 * Real.pi * (rexp (-Real.pi * ‖y‖ ^ 2) * inner ℝ y (mvec M y)) := by
      intro y hy
      dsimp [Fd']
      simp only [zero_smul, add_zero]
      ring_nf
    calc
      (∫ y in K, Fd' M 0 y)
          = ∫ y in K, (-2 * Real.pi * (rexp (-Real.pi * ‖y‖ ^ 2) * inner ℝ y (mvec M y))) := by
              exact MeasureTheory.setIntegral_congr_fun hK (fun y hy => hpt y hy)
      _ = -2 * Real.pi * (∫ y in K, rexp (-Real.pi * ‖y‖ ^ 2) * inner ℝ y (mvec M y)) := by
              rw [MeasureTheory.integral_const_mul]
  have hder2 : HasDerivAt (fun t : ℝ => ∫ y in K, Fd M t y)
      (∫ y in K, Fd' M 0 y) 0 := by
    simpa [μ] using hder
  exact hder2.congr_deriv hval

/-- **S1.** Shape derivative along the affine position curve `A(t) := 1 + t•M`:
`d/dt|₀ ∫_{y∈K} e^{-π‖A(t)•y‖²} = -2π ∫_K e^{-π‖y‖²}⟨y, M•y⟩` (the `mvec`-path form). -/
theorem shapeDeriv_mvec (M : Matrix (Fin m) (Fin m) ℝ) (K : Set E) (hK : MeasurableSet K) :
    HasDerivAt (fun t : ℝ => ∫ y in K,
      rexp (-Real.pi * ‖mvec ((1 : Matrix (Fin m) (Fin m) ℝ) + t • M) y‖ ^ 2))
      (-2 * Real.pi * ∫ y in K, rexp (-Real.pi * ‖y‖ ^ 2) * inner ℝ y (mvec M y)) 0 := by
  have h := shapeDeriv M K hK
  have hfun : (fun t : ℝ => ∫ y in K, Fd M t y) =
      (fun t : ℝ => ∫ y in K,
        rexp (-Real.pi * ‖mvec ((1 : Matrix (Fin m) (Fin m) ℝ) + t • M) y‖ ^ 2)) := by
    funext t
    apply MeasureTheory.setIntegral_congr_fun hK
    intro y hy
    dsimp [Fd]
    congr 1
    rw [← path_eq M t y]
  rw [hfun] at h
  exact h


/-! ## S3 — second-moment matrix and the trace pairing (paper Thm 4.12, first half)

For `K` (in the application the scaled Voronoi domain `K₀ := {y | s·y ∈ V(ℒ)}`), define
the Gaussian second-moment matrix `G` by `G_ij := ∫_K e^{−π‖y‖²} y_i y_j`.  The S3 core:

`∫_K e^{−π‖y‖²}·⟨y, M·y⟩ = Σᵢ Σⱼ M_ij · G_ij  (= ⟨M, G⟩_F)`

for every matrix `M`.  Combined with S1 (`shapeDeriv`: `d/dt|₀ ∫_K e^{−π‖(1+tM)·y‖²}
= −2π·∫_K e^{−π‖y‖²}⟨y,M·y⟩`) this turns a local extremum over the det-one matrices into
the Frobenius-orthogonality `⟨M, G⟩_F = 0` for every trace-zero symmetric `M`; S2
(`symm_of_orthogonal_to_trace_zero`) then forces `G = α·1` — isotropic Gaussian position.

Coordinates: elements of `E = EuclideanSpace ℝ (Fin m)` act as functions (`y i`) via the
`WithLp` coefficient application, with `co y := WithLp.ofLp (p := 2) y` defeq to it.
-/

/-- coordinates: `co y i = y i` (definitionally). -/
noncomputable def co (y : E) : Fin m → ℝ := WithLp.ofLp (p := 2) y

lemma coord_apply (y : E) (i : Fin m) : co y i = y i := rfl

lemma co_mvec (M : Matrix (Fin m) (Fin m) ℝ) (y : E) : co (mvec M y) = M *ᵥ co y := by
  dsimp [co, mvec]

/-- coordinate of the matrix action: `(M·y)_i = Σⱼ Mᵢⱼ·yⱼ`. -/
lemma mvec_coord_sum (M : Matrix (Fin m) (Fin m) ℝ) (y : E) (i : Fin m) :
    (mvec M y) i = ∑ j : Fin m, M i j * y j := by
  have hc0 : (mvec M y) i = co (mvec M y) i := (coord_apply (mvec M y) i).symm
  rw [hc0, co_mvec]
  simp [Matrix.mulVec, dotProduct, co]

/-- `inner ℝ x y = Σᵢ xᵢ·yᵢ`. -/
lemma inner_coord_sum (x y : E) : inner ℝ x y = ∑ i : Fin m, x i * y i := by
  dsimp
  simp [PiLp.inner_apply, mul_comm]

/-- ‖y‖²·e^{-(π/2)‖y‖²} ≤ 2/π. -/
lemma norm_sq_exp_half (y : E) : ‖y‖ ^ 2 * rexp (-(Real.pi / 2) * ‖y‖ ^ 2) ≤ 2 / Real.pi := by
  have hm := mul_exp_neg_le_one (u := (Real.pi / 2) * ‖y‖ ^ 2)
  have hstep1 : ‖y‖ ^ 2 * rexp (-(Real.pi / 2) * ‖y‖ ^ 2) =
      (2 / Real.pi) * (((Real.pi / 2) * ‖y‖ ^ 2) * rexp (-((Real.pi / 2) * ‖y‖ ^ 2))) := by
    field_simp [Real.pi_ne_zero]
  rw [hstep1]
  calc
    (2 / Real.pi) * (((Real.pi / 2) * ‖y‖ ^ 2) * rexp (-((Real.pi / 2) * ‖y‖ ^ 2))) ≤ (2 / Real.pi) * 1 := by
      exact mul_le_mul_of_nonneg_left hm (by positivity)
    _ = 2 / Real.pi := by ring

/-- ‖y‖²·e^{-π‖y‖²} ≤ (2/π)·e^{-(π/2)‖y‖²}. -/
lemma norm_sq_exp_full_le (y : E) :
    ‖y‖ ^ 2 * rexp (-Real.pi * ‖y‖ ^ 2) ≤ (2 / Real.pi) * rexp (-(Real.pi / 2) * ‖y‖ ^ 2) := by
  have h := norm_sq_exp_half y
  have hsplit : -Real.pi * ‖y‖ ^ 2 = (-(Real.pi / 2)) * ‖y‖ ^ 2 + (-(Real.pi / 2)) * ‖y‖ ^ 2 := by ring
  calc
    ‖y‖ ^ 2 * rexp (-Real.pi * ‖y‖ ^ 2)
        = ‖y‖ ^ 2 * rexp ((-(Real.pi / 2)) * ‖y‖ ^ 2 + (-(Real.pi / 2)) * ‖y‖ ^ 2) := by rw [hsplit]
    _ = ‖y‖ ^ 2 * (rexp ((-(Real.pi / 2)) * ‖y‖ ^ 2) * rexp ((-(Real.pi / 2)) * ‖y‖ ^ 2)) := by
          rw [Real.exp_add]
    _ = (‖y‖ ^ 2 * rexp ((-(Real.pi / 2)) * ‖y‖ ^ 2)) * rexp ((-(Real.pi / 2)) * ‖y‖ ^ 2) := by ring
    _ ≤ (2 / Real.pi) * rexp ((-(Real.pi / 2)) * ‖y‖ ^ 2) := by
          exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

/-- coordinate product × Gaussian bounded by a decaying Gaussian. -/
lemma coordPair_norm_le (y : E) (i j : Fin m) :
    |rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j| ≤ (2 / Real.pi) * rexp (-(Real.pi / 2) * ‖y‖ ^ 2) := by
  have h1 : |y i| ≤ ‖y‖ := by
    have h := PiLp.norm_apply_le (p := 2) (β := fun _ : Fin m => ℝ) y i
    simpa [Real.norm_eq_abs] using h
  have h2 : |y j| ≤ ‖y‖ := by
    have h := PiLp.norm_apply_le (p := 2) (β := fun _ : Fin m => ℝ) y j
    simpa [Real.norm_eq_abs] using h
  calc
    |rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j|
        = rexp (-Real.pi * ‖y‖ ^ 2) * |y i| * |y j| := by
          rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ rexp (-Real.pi * ‖y‖ ^ 2) * ‖y‖ * ‖y‖ := by
          gcongr
    _ = ‖y‖ ^ 2 * rexp (-Real.pi * ‖y‖ ^ 2) := by ring
    _ ≤ (2 / Real.pi) * rexp (-(Real.pi / 2) * ‖y‖ ^ 2) := norm_sq_exp_full_le y

/-- coordinate-pair Gaussian integrable on any measurable-restricted set (decay domination). -/
lemma coordPair_integrableOn (K : Set E) (i j : Fin m) :
    Integrable (fun y : E => rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j) (volume.restrict K) := by
  let bnd : E → ℝ := fun y => (2 / Real.pi) * rexp (-(Real.pi / 2) * ‖y‖ ^ 2)
  have hbE : Integrable bnd (volume : Measure E) := by
    have hg : Integrable (fun y : E => rexp (-(Real.pi / 2) * ‖y‖ ^ 2)) (volume : Measure E) :=
      gaussian_b_integrable (Real.pi / 2) (by positivity)
    simpa [bnd] using hg.const_mul (2 / Real.pi)
  have hb : Integrable bnd (volume.restrict K) := by
    simpa [MeasureTheory.IntegrableOn] using hbE.integrableOn (s := K)
  have hcont : Continuous (fun y : E => rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j) := by
    fun_prop
  refine Integrable.mono' hb ?meas ?ae
  · exact hcont.stronglyMeasurable.aestronglyMeasurable
  · refine Filter.Eventually.of_forall ?_
    intro y
    have hn := coordPair_norm_le y i j
    calc
      ‖rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j‖ = |rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j| := by
        rw [Real.norm_eq_abs]
      _ ≤ (2 / Real.pi) * rexp (-(Real.pi / 2) * ‖y‖ ^ 2) := hn

/-- The second-moment (isotropy) matrix of the Gaussian-weighted set `K`: `G_ij = ∫_K e^{-π‖y‖²} y_i y_j`. -/
noncomputable def secondMoment (K : Set E) (i j : Fin m) : ℝ :=
  ∫ y in K, rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j

/-- `inner ℝ y (mvec M y) = Σᵢ Σⱼ Mᵢⱼ·yᵢ·yⱼ`. -/
lemma inner_mvec_sum (M : Matrix (Fin m) (Fin m) ℝ) (y : E) :
    inner ℝ y (mvec M y) = ∑ i : Fin m, ∑ j : Fin m, M i j * y i * y j := by
  calc
    inner ℝ y (mvec M y) = ∑ i : Fin m, y i * (mvec M y) i := by
      rw [inner_coord_sum]
    _ = ∑ i : Fin m, y i * (∑ j : Fin m, M i j * y j) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [mvec_coord_sum]
    _ = ∑ i : Fin m, ∑ j : Fin m, M i j * y i * y j := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- `e^{-π‖y‖²}·inner ℝ y (mvec M y) = Σᵢ Σⱼ Mᵢⱼ·(e^{-π‖y‖²}·yᵢ·yⱼ)`. -/
lemma integrand_sum (M : Matrix (Fin m) (Fin m) ℝ) (y : E) :
    rexp (-Real.pi * ‖y‖ ^ 2) * inner ℝ y (mvec M y)
      = ∑ i : Fin m, ∑ j : Fin m, M i j * (rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j) := by
  rw [inner_mvec_sum M y]
  simp only [Finset.sum_mul, mul_assoc, mul_left_comm, mul_comm]

/-- **Trace pairing.** `∫_K e^{-π‖y‖²}·⟨y, M·y⟩ = ⟨M, G⟩_F` with
`G_ij := ∫_K e^{-π‖y‖²}·y_i·y_j`. -/
theorem trace_pairing (M : Matrix (Fin m) (Fin m) ℝ) (K : Set E) (hK : MeasurableSet K) :
    (∫ y in K, rexp (-Real.pi * ‖y‖ ^ 2) * inner ℝ y (mvec M y))
      = ∑ i : Fin m, ∑ j : Fin m, M i j * secondMoment K i j := by
  classical
  let μ : Measure E := volume.restrict K
  have hint (i j : Fin m) : Integrable
      (fun y : E => M i j * (rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j)) μ := by
    exact (coordPair_integrableOn K i j).const_mul (M i j)
  let f1 : Fin m → E → ℝ := fun i y => ∑ j : Fin m, M i j * (rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j)
  have hint1 (i : Fin m) : Integrable (f1 i) μ := by
    dsimp [f1]
    exact MeasureTheory.integrable_finsetSum (s := (Finset.univ : Finset (Fin m)))
      (f := fun (j : Fin m) (y : E) => M i j * (rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j))
      (by intro j hj; exact hint i j)
  calc
    (∫ y in K, rexp (-Real.pi * ‖y‖ ^ 2) * inner ℝ y (mvec M y))
        = ∫ y in K, (∑ i : Fin m, ∑ j : Fin m,
            M i j * (rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j)) := by
            apply MeasureTheory.setIntegral_congr_fun hK
            intro y hy
            exact integrand_sum M y
    _ = ∑ i : Fin m, ∫ y in K, (∑ j : Fin m,
            M i j * (rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j)) := by
            exact MeasureTheory.integral_finsetSum (s := (Finset.univ : Finset (Fin m)))
              (μ := volume.restrict K) (f := f1)
              (by intro i hi; simpa [μ] using hint1 i)
    _ = ∑ i : Fin m, ∑ j : Fin m,
            ∫ y in K, M i j * (rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact MeasureTheory.integral_finsetSum (s := (Finset.univ : Finset (Fin m)))
              (μ := volume.restrict K)
              (f := fun (j : Fin m) (y : E) => M i j * (rexp (-Real.pi * ‖y‖ ^ 2) * y i * y j))
              (by intro j hj; simpa [μ] using hint i j)
    _ = ∑ i : Fin m, ∑ j : Fin m, M i j * secondMoment K i j := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            rw [MeasureTheory.integral_const_mul]
            dsimp [secondMoment]



/-! ## D1 — linear change of variables for `γ_s` (det-one/`det A ≠ 0` position changes)

For `K`-style sets and an invertible matrix `A` acting on `E` by `mvec A`, the image-set
identity `{x | s·x ∈ A·S} = A·{x | s·x ∈ S}` (linearity + invertibility of `mvec A`) turns
the change of variables for the (additive-Haar = `volume`) measure
(`Measure.map (mvec A) volume = ofReal|det A⁻¹| • volume` via
`map_linearMap_addHaar_eq_smul_addHaar`, `LinearMap.det (mvec A) = A.det`) into

`γ_s(A·S) = |det A| · ∫_{y : sy∈S} e^{-π‖A·y‖²}`   (`gammaMass_comp_linearMap`).

Along a position curve `A(t) := 1 + t·M` this gives, for the scaled Voronoi domain
`K₀ := {y | s·y ∈ V(ℒ)}` (and with the det factor contributing `tr M` at `t = 0`), the
S1-shaped functional whose derivative is the S3 trace pairing.
-/

/-- The linear endomap associated to a matrix. -/
noncomputable def fA (A : Matrix (Fin m) (Fin m) ℝ) : E →ₗ[ℝ] E := mvec A

/-- `LinearMap.det (mvec A) = A.det`. -/
lemma det_fA (A : Matrix (Fin m) (Fin m) ℝ) : LinearMap.det (fA A : E →ₗ[ℝ] E) = A.det := by
  dsimp [fA, mvec]
  rw [LinearMap.det_toLpLin]

/-- scaled-set identity: `{x | s•x ∈ f''S} = f '' {x | s•x ∈ S}` for invertible `f`. -/
lemma scaled_image_eq {A : Matrix (Fin m) (Fin m) ℝ} (hdet : A.det ≠ 0) (s : ℝ) (S : Set E) :
    {x : E | s • x ∈ fA A '' S} = fA A '' {x : E | s • x ∈ S} := by
  have hf : LinearMap.det (fA A : E →ₗ[ℝ] E) ≠ 0 := by rwa [det_fA]
  let g : E ≃ₗ[ℝ] E := LinearMap.equivOfDetNeZero (fA A) hf
  have hgfun : ∀ z : E, fA A z = g z := by
    intro z
    rfl
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hyS, hxy⟩
    refine ⟨g.symm x, ?_, ?_⟩
    · change s • g.symm x ∈ S
      have hlin : g.symm (s • x) = s • g.symm x := map_smulₛₗ g.symm s x
      rw [← hlin]
      rw [← hxy]
      rw [hgfun]
      change g.symm (g y) ∈ S
      simpa [hyS]
    · rw [hgfun]
      simp
  · intro hx
    rcases hx with ⟨u, hu, hxu⟩
    refine ⟨s • u, hu, ?_⟩
    calc
      fA A (s • u) = s • fA A u := by simpa using map_smulₛₗ (fA A) s u
      _ = s • x := by rw [hxu]

/-- ∫ over the image of an invertible linear map: `∫_{f''K} g = |det f|·∫_K (g∘f)`. -/
lemma integral_image_fA {A : Matrix (Fin m) (Fin m) ℝ} (hdet : A.det ≠ 0)
    (g : E → ℝ) (K : Set E) :
    (∫ x in fA A '' K, g x) = |A.det| * (∫ x in K, g (fA A x)) := by
  have hf : LinearMap.det (fA A : E →ₗ[ℝ] E) ≠ 0 := by rwa [det_fA]
  let ce : E ≃L[ℝ] E := LinearEquiv.toContinuousLinearEquiv (LinearMap.equivOfDetNeZero (fA A) hf)
  let e : E ≃ᵐ E := ce.toHomeomorph.toMeasurableEquiv
  have hefun : ∀ z : E, e z = fA A z := by
    intro z
    rfl
  have he_inj : Function.Injective (fun z : E => e z) := by
    intro x y hxy
    have : (LinearMap.equivOfDetNeZero (fA A) hf : E → E) x =
        (LinearMap.equivOfDetNeZero (fA A) hf : E → E) y := by
      simpa [e, ce] using hxy
    exact LinearEquiv.injective (LinearMap.equivOfDetNeZero (fA A) hf) this
  have himg : fA A '' K = e '' K := by
    apply Set.image_congr
    intro x hx
    exact hefun x
  have hpre : e ⁻¹' (fA A '' K) = K := by
    calc
      e ⁻¹' (fA A '' K) = e ⁻¹' (e '' K) := by rw [himg]
      _ = K := Set.preimage_image_eq K he_inj
  have hsubst0 := MeasureTheory.setIntegral_map_equiv (μ := (volume : Measure E)) (e := e)
    (f := g) (s := fA A '' K)
  have hsubst1 : ∫ y in fA A '' K, g y ∂(map e (volume : Measure E)) = ∫ x in K, g (fA A x) := by
    rw [hpre] at hsubst0
    simpa [hefun] using hsubst0
  have hmapfun : Measure.map e (volume : Measure E) = Measure.map (fA A) (volume : Measure E) := by
    have hfun : (fun z : E => e z) = (fun z : E => fA A z) := funext (fun z => hefun z)
    exact congrArg (fun φ : E → E => Measure.map φ (volume : Measure E)) hfun
  have hmap : Measure.map (fA A) (volume : Measure E) =
      ENNReal.ofReal |(LinearMap.det (fA A : E →ₗ[ℝ] E))⁻¹| • (volume : Measure E) :=
    map_linearMap_addHaar_eq_smul_addHaar (volume : Measure E) hf
  have hsmul : (∫ y in fA A '' K, g y ∂(ENNReal.ofReal |(LinearMap.det (fA A : E →ₗ[ℝ] E))⁻¹|
      • (volume : Measure E))) = |(LinearMap.det (fA A : E →ₗ[ℝ] E))⁻¹| * (∫ y in fA A '' K, g y) := by
    rw [show (∫ y in fA A '' K, g y ∂(ENNReal.ofReal |(LinearMap.det (fA A : E →ₗ[ℝ] E))⁻¹|
        • (volume : Measure E))) = ∫ y, g y ∂((ENNReal.ofReal |(LinearMap.det (fA A : E →ₗ[ℝ] E))⁻¹|
        • (volume : Measure E)).restrict (fA A '' K)) by rfl]
    rw [Measure.restrict_smul]
    rw [MeasureTheory.integral_smul_measure]
    rw [ENNReal.toReal_ofReal]
    · rfl
    · exact abs_nonneg _
  have h1 : ∫ x in K, g (fA A x) = |(LinearMap.det (fA A : E →ₗ[ℝ] E))⁻¹| * (∫ y in fA A '' K, g y) := by
    calc
      ∫ x in K, g (fA A x)
          = ∫ y in fA A '' K, g y ∂(map e (volume : Measure E)) := hsubst1.symm
      _ = ∫ y in fA A '' K, g y ∂(Measure.map (fA A) (volume : Measure E)) := by rw [hmapfun]
      _ = ∫ y in fA A '' K, g y ∂(ENNReal.ofReal |(LinearMap.det (fA A : E →ₗ[ℝ] E))⁻¹|
              • (volume : Measure E)) := by rw [hmap]
      _ = |(LinearMap.det (fA A : E →ₗ[ℝ] E))⁻¹| * (∫ y in fA A '' K, g y) := hsmul
  calc
    (∫ x in fA A '' K, g x) = |A.det| * (∫ x in K, g (fA A x)) := by
      have h2 : |A.det| ≠ 0 := abs_ne_zero.mpr hdet
      have hd : |(LinearMap.det (fA A : E →ₗ[ℝ] E))⁻¹| = |A.det|⁻¹ := by
        rw [det_fA, abs_inv]
      rw [h1, hd]
      field_simp [h2]

/-- **D1.** Linear change of variables for `γ_s`: for `det A ≠ 0`,
`γ_s(A·S) = |det A| · ∫_{y: sy∈S} e^{-π‖A·y‖²}`. -/
theorem gammaMass_comp_linearMap (A : Matrix (Fin m) (Fin m) ℝ) (hdet : A.det ≠ 0)
    (s : ℝ) (S : Set E) :
    Submission.GaussianMeasure.gammaMass (n := m) s (fA A '' S)
      = |A.det| * (∫ x in {y : E | s • y ∈ S}, rexp (-Real.pi * ‖fA A x‖ ^ 2)) := by
  have hset : {y : E | s • y ∈ fA A '' S} = fA A '' {y : E | s • y ∈ S} :=
    scaled_image_eq hdet s S
  have hsubst := integral_image_fA hdet (fun x : E => rexp (-Real.pi * ‖x‖ ^ 2)) {y : E | s • y ∈ S}
  dsimp [Submission.GaussianMeasure.gammaMass]
  rw [hset]
  exact hsubst


end S1



variable {m : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin m)

/-- `mvec (1 + M) w − w = mvec M w` (the matrix form of `path_eq` at `t = 1`). -/
lemma mvec_one_add_sub (M : Matrix (Fin m) (Fin m) ℝ) (w : E) :
    mvec ((1 : Matrix (Fin m) (Fin m) ℝ) + M) w - w = mvec M w := by
  have h : mvec ((1 : Matrix (Fin m) (Fin m) ℝ) + M) w = w + mvec M w := by
    simpa using path_eq M 1 w
  rw [h, add_sub_cancel_left]

/-- `|co y j| ≤ ‖y‖`. -/
lemma abs_co_le (y : E) (j : Fin m) : |co y j| ≤ ‖y‖ := by
  have h := PiLp.norm_apply_le (p := 2) (β := fun _ : Fin m => ℝ) y j
  simpa [Real.norm_eq_abs, coord_apply] using h

/-- `‖v‖ ≤ Σᵢ |co v i|` (ℓ² ≤ ℓ¹). -/
lemma norm_le_sum_abs_co (v : E) : ‖v‖ ≤ ∑ j : Fin m, |co v j| := by
  have hsq : ‖v‖ ^ 2 ≤ (∑ j : Fin m, |co v j|) ^ 2 := by
    have h1 : ‖v‖ ^ 2 = ∑ j : Fin m, (v j) ^ 2 := by simp [PiLp.norm_sq_eq_of_L2]
    rw [h1]
    calc
      (∑ j : Fin m, (v j) ^ 2) = ∑ j : Fin m, |co v j| ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [coord_apply, sq_abs]
      _ ≤ (∑ j : Fin m, |co v j|) ^ 2 :=
        Finset.sum_sq_le_sq_sum_of_nonneg (s := Finset.univ)
          (f := fun j : Fin m => |co v j|) (by intro j _; exact abs_nonneg _)
  have hnn1 : 0 ≤ ‖v‖ := norm_nonneg v
  have hnn2 : 0 ≤ ∑ j : Fin m, |co v j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  nlinarith [sq_le_sq.mp hsq]

/-- **Entrywise bound for the matrix action**: `‖M·w‖ ≤ (Σᵢⱼ|Mᵢⱼ|)·‖w‖`. -/
lemma mvec_norm_le_sum_abs (M : Matrix (Fin m) (Fin m) ℝ) (w : E) :
    ‖mvec M w‖ ≤ (∑ i : Fin m, ∑ j : Fin m, |M i j|) * ‖w‖ := by
  have hcoord : ∀ i : Fin m, |co (mvec M w) i| ≤ (∑ j : Fin m, |M i j|) * ‖w‖ := by
    intro i
    have h1 : co (mvec M w) i = ∑ j : Fin m, M i j * co w j := by
      rw [co_mvec]
      simp [Matrix.mulVec, dotProduct, co]
    rw [h1]
    calc
      |∑ j : Fin m, M i j * co w j| ≤ ∑ j : Fin m, |M i j * co w j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j : Fin m, |M i j| * |co w j| := by
        apply Finset.sum_congr rfl
        intro j _
        rw [abs_mul]
      _ ≤ ∑ j : Fin m, |M i j| * ‖w‖ :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (abs_co_le w j) (abs_nonneg _))
      _ = (∑ j : Fin m, |M i j|) * ‖w‖ := by rw [Finset.sum_mul]
  calc
    ‖mvec M w‖ ≤ ∑ i : Fin m, |co (mvec M w) i| := norm_le_sum_abs_co _
    _ ≤ ∑ i : Fin m, (∑ j : Fin m, |M i j|) * ‖w‖ :=
      Finset.sum_le_sum (fun i _ => hcoord i)
    _ = (∑ i : Fin m, ∑ j : Fin m, |M i j|) * ‖w‖ := by rw [Finset.sum_mul]

/-- **The `hA` bound with `ε := Σᵢⱼ|Mᵢⱼ|`**: the deviation of `mvec (1+M)` from the
identity is bounded by the ℓ¹ norm of the matrix. -/
lemma mvec_one_add_lipschitz (M : Matrix (Fin m) (Fin m) ℝ) :
    ∀ w : E, ‖mvec ((1 : Matrix (Fin m) (Fin m) ℝ) + M) w - w‖ ≤
      (∑ i : Fin m, ∑ j : Fin m, |M i j|) * ‖w‖ := by
  intro w
  rw [mvec_one_add_sub M w]
  exact mvec_norm_le_sum_abs M w

/-- **The `hA` bound with the operator norm** `ε := ‖(mvec M).toContinuousLinearMap‖`.
NOTE: the map must be annotated `: E →L[ℝ] E` at the `le_opNorm` call site — without it
Lean leaves the scalar field undetermined and `RingHomIsometric` gets stuck. -/
lemma mvec_one_add_lipschitz_opNorm (M : Matrix (Fin m) (Fin m) ℝ) :
    ∀ w : E, ‖mvec ((1 : Matrix (Fin m) (Fin m) ℝ) + M) w - w‖ ≤
      ‖(mvec M).toContinuousLinearMap‖ * ‖w‖ := by
  intro w
  rw [mvec_one_add_sub M w]
  have h := ContinuousLinearMap.le_opNorm ((mvec M).toContinuousLinearMap : E →L[ℝ] E) w
  simpa using h

/-- entrywise-bounded matrices have small ℓ¹ norm: `Σᵢⱼ|Mᵢⱼ| ≤ m²·ε`. -/
lemma sum_abs_le_of_entry (M : Matrix (Fin m) (Fin m) ℝ) (ε : ℝ) (hε : ∀ i j : Fin m, |M i j| ≤ ε) :
    (∑ i : Fin m, ∑ j : Fin m, |M i j|) ≤ (m : ℝ) ^ 2 * ε := by
  calc
    (∑ i : Fin m, ∑ j : Fin m, |M i j|) ≤ ∑ i : Fin m, ∑ j : Fin m, ε :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hε i j))
    _ = ∑ i : Fin m, (m : ℝ) * ε := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (m : ℝ) * ((m : ℝ) * ε) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (m : ℝ) ^ 2 * ε := by ring

end Submission.ShapeDeriv