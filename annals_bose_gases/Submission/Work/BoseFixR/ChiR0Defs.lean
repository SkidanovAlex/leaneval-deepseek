import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixR.sampling_sq_sum_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.ChiR0Defs` — the box/lattice vocabulary for `SamplingSqSumLeChiR0`

This module contains the *definitions* shared by the proof of
`Work.BoseFixR.SamplingSqSumLeChiR0` and by its delegated auxiliary lemmas.

The target statement bounds the lattice sampling sum `Σ_{k : Lab N} (chat W (kmomLab ℓ N k))²`
by `ℓ³ (2χ+1)³ B ∫W` where `W ≥ 0`, `W ≤ B`, `tsupp W ⊆ ball 0 R` and `R ≤ ℓ·χ`.  The route is

* periodisation: `P(y) = Σ_{n ∈ ℤ³} W(y + ℓn)` is, on the fundamental domain `cellI ℓ` of the
  lattice `ℓℤ³`, a *finite* sum whose number of non-zero terms at `y` is at most `(2χ+1)³`
  (each coordinate of `n` must lie in an interval of length `2χ`);
* hence `0 ≤ P ≤ (2χ+1)³ B` on `cellI ℓ`, so `∫_{cellI ℓ} P² ≤ (2χ+1)³ B ∫_{cellI ℓ} P`;
* the tiling identity `∫_{ℝ³} f = Σ_{n} ∫_{cellI ℓ} f(· + ℓn)` turns `∫_{cellI ℓ} P` into `∫W`
  and the Fourier coefficients `∫_{cellI ℓ} P e^{-i⟪q,·⟫}` into `∫_{ℝ³} W e^{-i⟪q,·⟫} = Ŵ(q)`
  (the phase `⟪kmomLab ℓ N k, ℓn⟫ = 2π·(integer)` drops out);
* Bessel for the orthonormal family `1_{cellI ℓ} e^{i⟪kmomLab ℓ N k,·⟫}` of weight `ℓ³`.

The vocabulary below: the closed box `cell`, its half-open version `cellI` (the fundamental
domain), and the lattice vectors `lat ℓ n`, `lat1 n`.
-/

noncomputable section

open scoped Real Topology BigOperators Pointwise
open MeasureTheory Filter Metric

namespace Work.BoseFixR

/-! ## 1. The boxes -/

/-- The closed box `[-ℓ/2, ℓ/2]³` (definitionally `boxL ℓ`). -/
def cell (ℓ : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) := {y | ∀ i, |y i| ≤ ℓ / 2}

/-- The half-open box `[-ℓ/2, ℓ/2)³`: a fundamental domain of the lattice `ℓℤ³`. -/
def cellI (ℓ : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) :=
  {y | ∀ i, y i ∈ Set.Ico (-(ℓ / 2)) (ℓ / 2)}

lemma cell_eq_boxL (ℓ : ℝ) : cell ℓ = boxL ℓ := rfl

lemma mem_cell {ℓ : ℝ} {y : EuclideanSpace ℝ (Fin 3)} :
    y ∈ cell ℓ ↔ ∀ i, |y i| ≤ ℓ / 2 := Iff.rfl

lemma mem_cellI {ℓ : ℝ} {y : EuclideanSpace ℝ (Fin 3)} :
    y ∈ cellI ℓ ↔ ∀ i, y i ∈ Set.Ico (-(ℓ / 2)) (ℓ / 2) := Iff.rfl

lemma cellI_subset_cell (ℓ : ℝ) : cellI ℓ ⊆ cell ℓ := by
  intro y hy i
  have h := hy i
  exact abs_le.mpr ⟨(Set.mem_Ico.mp h).1, le_of_lt (Set.mem_Ico.mp h).2⟩

/-! ## 2. The `ℓ`-lattice -/

/-- The lattice vector `ℓ • n` of `ℝ³` (`n : ℤ³`). -/
noncomputable def lat (ℓ : ℝ) (n : Fin 3 → ℤ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i => ℓ * (n i : ℝ))

/-- The unit lattice vector `n ↦ n` (`n : ℤ³`). -/
noncomputable def lat1 (n : Fin 3 → ℤ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 (fun i => (n i : ℝ))

@[simp] lemma lat1_apply (n : Fin 3 → ℤ) (i : Fin 3) : lat1 n i = (n i : ℝ) := rfl

@[simp] lemma lat_apply (ℓ : ℝ) (n : Fin 3 → ℤ) (i : Fin 3) : lat ℓ n i = ℓ * (n i : ℝ) := rfl

lemma lat_eq_smul (ℓ : ℝ) (n : Fin 3 → ℤ) : lat ℓ n = ℓ • lat1 n := by
  ext i; simp [lat, lat1]

lemma lat_zero (ℓ : ℝ) : lat ℓ 0 = 0 := by ext i; simp [lat]

lemma lat_add (ℓ : ℝ) (n m : Fin 3 → ℤ) : lat ℓ (n + m) = lat ℓ n + lat ℓ m := by
  ext i
  simp only [lat, WithLp.ofLp_add, WithLp.ofLp_toLp, Pi.add_apply]
  push_cast; ring

/-- The lattice `ℤ³ → ℝ³`, `n ↦ ℓ • n`, as an additive homomorphism. -/
noncomputable def latHom (ℓ : ℝ) : (Fin 3 → ℤ) →+ EuclideanSpace ℝ (Fin 3) where
  toFun := lat ℓ
  map_zero' := lat_zero ℓ
  map_add' := lat_add ℓ

@[simp] lemma latHom_apply (ℓ : ℝ) (n : Fin 3 → ℤ) : latHom ℓ n = lat ℓ n := rfl

lemma lat_injective {ℓ : ℝ} (hℓ : ℓ ≠ 0) : Function.Injective (lat ℓ) := by
  intro n m h
  funext i
  have h' : ℓ * (n i : ℝ) = ℓ * (m i : ℝ) := by
    simpa using congrArg (fun v : EuclideanSpace ℝ (Fin 3) => v i) h
  exact_mod_cast mul_left_cancel₀ hℓ h'

lemma latHom_injective {ℓ : ℝ} (hℓ : ℓ ≠ 0) : Function.Injective (latHom ℓ) :=
  fun _ _ h => lat_injective hℓ h

/-- The lattice `ℤ³` is the range of `latHom ℓ` (for `ℓ ≠ 0`). -/
noncomputable def latEquiv {ℓ : ℝ} (hℓ : ℓ ≠ 0) : (Fin 3 → ℤ) ≃ (latHom ℓ).range where
  toFun n := ⟨latHom ℓ n, ⟨n, rfl⟩⟩
  invFun g := Classical.choose (AddMonoidHom.mem_range.mp g.2)
  left_inv n := by
    apply latHom_injective hℓ
    exact Classical.choose_spec (AddMonoidHom.mem_range.mp
      (show latHom ℓ n ∈ (latHom ℓ).range from ⟨n, rfl⟩))
  right_inv g := by
    apply Subtype.ext
    exact Classical.choose_spec (AddMonoidHom.mem_range.mp g.2)

lemma countable_range_latHom {ℓ : ℝ} (hℓ : ℓ ≠ 0) : Countable (latHom ℓ).range :=
  (latEquiv hℓ).symm.injective.countable

/-! ## 3. The momentum–lattice pairing -/

/-- The inner product of a dual-lattice momentum `2πm` with a unit lattice vector `n`. -/
lemma inner_vec_lat1 (m n : Fin 3 → ℤ) :
    inner ℝ (Work.BoseB4.vec m) (lat1 n)
      = 2 * Real.pi * ((∑ i, m i * n i : ℤ) : ℝ) := by
  show inner ℝ (WithLp.toLp 2 (fun i : Fin 3 => 2 * Real.pi * (m i : ℝ)))
      (WithLp.toLp 2 (fun i : Fin 3 => (n i : ℝ))) = _
  rw [PiLp.inner_apply]
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  rw [Int.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring

/-- The phase pairing of a box-lattice momentum with a lattice vector is a multiple of `2π`. -/
lemma inner_kmomLab_lat {ℓ : ℝ} (hℓ : ℓ ≠ 0) (N : ℕ)
    (k : Work.BoseBoxFock.Lab N) (n : Fin 3 → ℤ) :
    inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) (lat ℓ n)
      = 2 * Real.pi * ((∑ i, Work.BoseBoxFock.labVec N k i * n i : ℤ) : ℝ) := by
  rw [Work.BoseBoxFock.kmomLab, lat_eq_smul, real_inner_smul_left, real_inner_smul_right,
    ← mul_assoc, inv_mul_cancel₀ hℓ, one_mul]
  exact inner_vec_lat1 _ _

/-- `e^{-i·2π·J} = 1` for an integer `J`. -/
lemma exp_neg_I_mul_two_pi_mul_int (J : ℤ) :
    Complex.exp (-(Complex.I * (((2 * Real.pi * (J : ℝ) : ℝ)) : ℂ))) = 1 := by
  have h : -(Complex.I * (((2 * Real.pi * (J : ℝ) : ℝ)) : ℂ))
      = ((-J : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

/-- **The phase drops out.**  The exponential of a box-lattice momentum against a lattice
vector is `1`. -/
lemma exp_inner_kmomLab_lat {ℓ : ℝ} (hℓ : ℓ ≠ 0) (N : ℕ)
    (k : Work.BoseBoxFock.Lab N) (n : Fin 3 → ℤ) :
    Complex.exp (-(Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) (lat ℓ n) : ℂ)))
      = 1 := by
  rw [inner_kmomLab_lat hℓ N k n]
  exact exp_neg_I_mul_two_pi_mul_int _

end Work.BoseFixR
