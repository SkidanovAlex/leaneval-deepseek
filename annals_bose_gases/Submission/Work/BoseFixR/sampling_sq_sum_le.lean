import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.CStarAlgebra.Module.Constructions
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.sampling_sq_sum_le` — lattice Bessel/Parseval for the honest Fourier kernel

The target is the "Bessel row" of FS §9's `eq:Rough2` route: the sum over the honest box lattice
`Lab N` of the squared real Fourier kernel `chat W` is dominated by `ℓ³∫W²`.

The proof splits into two independent analytic pieces plus a reduction:

* `box_exp_orthogonal` (child A) — the *lattice orthogonality* of the plane waves on the scaled
  box `B_ℓ = {y | ∀ i, |y i| ≤ ℓ/2}`: for lattice momenta `ℓ⁻¹ • vec m`,
  `∫_{B_ℓ} e^{i⟪ℓ⁻¹ • vec m, x⟫} dx = ℓ³·δ_{m,0}`;
* `bessel_sum_integral` (child B) — finite Bessel: a family `Q` with Gram `∫Q_k conj(Q_k') = Lδ`
  satisfies `Σ_k ‖∫ W·conj(Q_k)‖² ≤ L∫W²` for `W ∈ L¹∩L²`;
* the reduction: `sampling_sq_sum_le` takes `Q_k = 1_{B_ℓ}·e^{i⟪kmomLab ℓ N k, ·⟫}`, whose Gram is
  `ℓ³δ` by child A and `labVec`'s injectivity, and concludes `Σ_k (chat W (kmomLab ℓ N k))² ≤
  Σ_k ‖∫W·conj(Q_k)‖² ≤ ℓ³∫W²`, the first inequality being `(Re z)² ≤ |z|²` applied to
  `chat W q = (∫ W e^{−i⟪q,·⟫}).re`.
-/

noncomputable section

open scoped Real Topology BigOperators Pointwise
open MeasureTheory Filter Metric

namespace Work.BoseFixR

set_option maxHeartbeats 1200000
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 0. The scaled box `B_ℓ = [-ℓ/2, ℓ/2]³` -/

/-- The scaled box of side `ℓ` (`B_ℓ = {y | ∀ i, |y i| ≤ ℓ/2}`), the support of the periodisation
in the Poisson/Parseval comparison. -/
def boxL (ℓ : ℝ) : Set (EuclideanSpace ℝ (Fin 3)) := {y | ∀ i, |y i| ≤ ℓ / 2}

/-- The volume of the scaled box: `|B_ℓ| = ℓ³`. -/
lemma volume_boxL (ℓ : ℝ) : volume (boxL ℓ) = ENNReal.ofReal (ℓ ^ 3) := by
  let C : Set (Fin 3 → ℝ) := {f | ∀ k, f k ∈ Set.Icc (-(ℓ / 2)) (ℓ / 2)}
  have hcell : boxL ℓ =
      (WithLp.ofLp : EuclideanSpace ℝ (Fin 3) → (Fin 3 → ℝ)) ⁻¹' C := by
    ext y
    simp only [boxL, Set.mem_ofPred_eq, Set.mem_preimage, C, Set.mem_Icc]
    exact ⟨fun h k => abs_le.mp (h k), fun h k => abs_le.mpr (h k)⟩
  rw [hcell]
  have hCpi : C = (Set.univ : Set (Fin 3)).pi
      (fun _ : Fin 3 => (Set.Icc (-(ℓ / 2)) (ℓ / 2) : Set ℝ)) := by
    ext f
    simp only [C, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
  have hCmeas : MeasurableSet C := by
    rw [hCpi]
    exact MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc)
  rw [MeasurePreserving.measure_preimage (PiLp.volume_preserving_ofLp (Fin 3))
    hCmeas.nullMeasurableSet]
  rw [hCpi, MeasureTheory.volume_pi,
    MeasureTheory.Measure.pi_pi (μ := fun _ : Fin 3 => (volume : Measure ℝ))
      (s := fun _ : Fin 3 => (Set.Icc (-(ℓ / 2)) (ℓ / 2) : Set ℝ))]
  simp only [Real.volume_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show ℓ / 2 - -(ℓ / 2) = ℓ by ring]
  rcases lt_or_ge 0 ℓ with h | h
  · exact (ENNReal.ofReal_pow (le_of_lt h) 3).symm
  · rw [ENNReal.ofReal_eq_zero.mpr h, zero_pow (by norm_num : (3 : ℕ) ≠ 0),
      ENNReal.ofReal_eq_zero.mpr (by nlinarith [sq_nonneg ℓ])]

lemma volume_boxL_ne_top (ℓ : ℝ) : volume (boxL ℓ) ≠ ⊤ := by
  rw [volume_boxL ℓ]; exact ENNReal.ofReal_ne_top

lemma measurableSet_boxL (ℓ : ℝ) : MeasurableSet (boxL ℓ) := by
  have h : boxL ℓ = ⋂ i : Fin 3, {y : EuclideanSpace ℝ (Fin 3) | |y i| ≤ ℓ / 2} := by
    ext y; simp only [boxL, Set.mem_ofPred_eq, Set.mem_iInter]
  rw [h]
  exact (isClosed_iInter fun i => isClosed_le
    (continuous_abs.comp (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i))
    continuous_const).measurableSet

/-- The ball of radius `R` is contained in the box of side `ℓ` as soon as `2R ≤ ℓ`
(the `‖x‖`-to-coordinates bound `|x i| ≤ ‖x‖`). -/
lemma ball_subset_boxL {R ℓ : ℝ} (hRℓ : 2 * R ≤ ℓ) :
    Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R ⊆ boxL ℓ := by
  intro x hx
  rw [Metric.mem_ball, dist_zero_right] at hx
  simp only [boxL, Set.mem_ofPred_eq]
  intro i
  calc |x i| = ‖x.ofLp i‖ := by simp
    _ ≤ ‖x‖ := PiLp.norm_apply_le x i
    _ ≤ ℓ / 2 := le_of_lt (lt_of_lt_of_le hx (by linarith))

/-- A function supported in the ball of radius `R` vanishes off the box of side `ℓ` when
`2R ≤ ℓ`. -/
lemma eq_zero_off_boxL {W : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ}
    (hsupp : tsupport W ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hRℓ : 2 * R ≤ ℓ) :
    ∀ x, x ∉ boxL ℓ → W x = 0 := by
  intro x hx
  refine Function.notMem_support.mp fun hxsupp => hx ?_
  exact ball_subset_boxL hRℓ (hsupp (subset_tsupport W hxsupp))

/-! ## 1. The lattice labels of the box `Lab N` and their momenta -/

/-- The integer labels of the cube `Lab N` are distinct (`valMinAbs` is injective, and the odd
modulus `2N+1` makes the centred representative unambiguous). -/
lemma labVec_injective (N : ℕ) : Function.Injective (Work.BoseBoxFock.labVec N) := by
  intro n m h
  funext i
  exact ZMod.injective_valMinAbs (congrFun h i)

/-- The momenta of the box lattice are additive in the difference of the integer labels. -/
lemma kmomLab_sub (ℓ : ℝ) (N : ℕ) (k k' : Work.BoseBoxFock.Lab N) :
    Work.BoseBoxFock.kmomLab ℓ N k - Work.BoseBoxFock.kmomLab ℓ N k'
      = (ℓ⁻¹ : ℝ) • Work.BoseB4.vec (Work.BoseBoxFock.labVec N k
          - Work.BoseBoxFock.labVec N k') := by
  rw [Work.BoseBoxFock.kmomLab, Work.BoseBoxFock.kmomLab, ← smul_sub, Work.BoseB4.vec_sub]
  rfl

/-! ## 2. The Fourier kernel on the box as a complex integral -/

/-- The character `1_B·e^{i⟪q,·⟫}` of the box `B` at the momentum `q`. -/
def boxChar (B : Set (EuclideanSpace ℝ (Fin 3))) (q : EuclideanSpace ℝ (Fin 3)) :
    EuclideanSpace ℝ (Fin 3) → ℂ :=
  B.indicator (fun x => Complex.exp (Complex.I * (inner ℝ q x : ℂ)))

/-- **The Fourier kernel as the real part of the windowed complex integral.**  If `W` vanishes
off `B`, then `chat W q = Re ∫ W·conj(1_B e^{i⟪q,·⟫})`. -/
lemma chat_eq_re_integral {B : Set (EuclideanSpace ℝ (Fin 3))} (hB : MeasurableSet B)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (h0 : ∀ x, x ∉ B → W x = 0)
    (q : EuclideanSpace ℝ (Fin 3)) :
    chat W q = (∫ x, (W x : ℂ) * star (boxChar B q x)).re := by
  have hstar : ∀ x, star (boxChar B q x) = B.indicator
      (fun x => Complex.exp (-(Complex.I * (inner ℝ q x : ℂ)))) x := by
    intro x
    by_cases hx : x ∈ B
    · rw [boxChar, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      rw [show star (Complex.exp (Complex.I * (inner ℝ q x : ℂ)))
          = (starRingEnd ℂ) (Complex.exp (Complex.I * (inner ℝ q x : ℂ))) from rfl]
      rw [← Complex.exp_conj]
      congr 1
      rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
      ring
    · rw [boxChar, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, star_zero]
  have hpt : ∀ x, (W x : ℂ) * star (boxChar B q x)
      = B.indicator (fun x => Complex.exp (-(Complex.I * (inner ℝ q x : ℂ))) * (W x : ℂ)) x := by
    intro x
    rw [hstar x]
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_comm]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
  have hzero : ∀ x, x ∉ B →
      Complex.exp (-(Complex.I * (inner ℝ q x : ℂ))) * (W x : ℂ) = 0 := by
    intro x hx; rw [h0 x hx]; simp
  have h1 : ∫ x, (W x : ℂ) * star (boxChar B q x)
      = ∫ x, Complex.exp (-(Complex.I * (inner ℝ q x : ℂ))) * (W x : ℂ) := by
    rw [funext hpt, integral_indicator hB]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  have h2 : (∫ x, Complex.exp (-(Complex.I * (inner ℝ q x : ℂ))) * (W x : ℂ))
      = Submission.BoseGases.kinFT (fun y => ((W y : ℝ) : ℂ)) q := rfl
  rw [h1, h2]
  rfl

/-- `(Re z)² ≤ |z|²`. -/
lemma re_sq_le_normSq (z : ℂ) : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
  have h1 := Complex.normSq_apply z
  have h2 := Complex.normSq_eq_norm_sq z
  nlinarith [sq_nonneg z.im]

/-- The squared Fourier kernel at a lattice momentum is dominated by the squared modulus of the
windowed complex Fourier coefficient. -/
lemma sq_chat_le_norm_integral {B : Set (EuclideanSpace ℝ (Fin 3))} (hB : MeasurableSet B)
    {W : EuclideanSpace ℝ (Fin 3) → ℝ} (h0 : ∀ x, x ∉ B → W x = 0)
    (q : EuclideanSpace ℝ (Fin 3)) :
    (chat W q) ^ 2 ≤ ‖∫ x, (W x : ℂ) * star (boxChar B q x)‖ ^ 2 := by
  have h := re_sq_le_normSq (∫ x, (W x : ℂ) * star (boxChar B q x))
  rwa [chat_eq_re_integral hB h0 q]

/-- The product of two box characters is the box character of the difference of the momenta
(the characters are multiplicative). -/
lemma boxChar_mul_star (B : Set (EuclideanSpace ℝ (Fin 3)))
    (q q' : EuclideanSpace ℝ (Fin 3)) (x : EuclideanSpace ℝ (Fin 3)) :
    boxChar B q x * star (boxChar B q' x)
      = B.indicator (fun x => Complex.exp (Complex.I * (inner ℝ (q - q') x : ℂ))) x := by
  have hstar : star (Complex.exp (Complex.I * (inner ℝ q' x : ℂ)))
      = Complex.exp (-(Complex.I * (inner ℝ q' x : ℂ))) := by
    rw [show star (Complex.exp (Complex.I * (inner ℝ q' x : ℂ)))
        = (starRingEnd ℂ) (Complex.exp (Complex.I * (inner ℝ q' x : ℂ))) from rfl]
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have key : Complex.exp (Complex.I * (inner ℝ q x : ℂ))
        * Complex.exp (-(Complex.I * (inner ℝ q' x : ℂ)))
      = Complex.exp (Complex.I * (inner ℝ (q - q') x : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    rw [inner_sub_left]
    push_cast
    ring
  by_cases hx : x ∈ B
  · rw [boxChar, boxChar, Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      Set.indicator_of_mem hx, hstar]
    exact key
  · rw [boxChar, boxChar, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
      Set.indicator_of_notMem hx, star_zero, mul_zero]

/-- The box character is in `L²` (it is bounded by `1` and supported in the finite-measure
box `B_ℓ`). -/
lemma memLp_boxChar (ℓ : ℝ) (q : EuclideanSpace ℝ (Fin 3)) :
    MemLp (boxChar (boxL ℓ) q) 2 := by
  rw [boxChar, memLp_indicator_iff_restrict (measurableSet_boxL ℓ)]
  haveI : IsFiniteMeasure (volume.restrict (boxL ℓ)) :=
    (isFiniteMeasure_restrict).mpr (volume_boxL_ne_top ℓ)
  exact MemLp.of_bound
    (by fun_prop : AEStronglyMeasurable
      (fun x => Complex.exp (Complex.I * (inner ℝ q x : ℂ))) (volume.restrict (boxL ℓ)))
    1 (Eventually.of_forall fun x => by rw [Complex.norm_exp_I_mul_ofReal])

/-! ## 3. Child A: lattice orthogonality of the plane waves on the box `B_ℓ` -/

private lemma inner_toLp_apply (a : Fin 3 → ℝ) (x : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (WithLp.toLp 2 a) x = ∑ i, a i * x.ofLp i := by
  rw [PiLp.inner_apply]
  simp [mul_comm]

/-- **The unit-cell complex orthogonality**: `∫_{unitCell} e^{i⟪vec m, x⟫} dx = δ_{m,0}`. -/
theorem integral_unitCell_exp_lattice (m : Fin 3 → ℤ) :
    ∫ x in Work.BoseB4.unitCell,
        Complex.exp (Complex.I * (inner ℝ (Work.BoseB4.vec m) x : ℂ))
      = if m = 0 then 1 else 0 := by
  have hmain : ∫ x in Work.BoseB4.unitCell,
        Complex.exp (Complex.I * (inner ℝ (Work.BoseB4.vec m) x : ℂ))
      = ∏ i : Fin 3, ∫ t in Set.Icc (-(1 / 2) : ℝ) (1 / 2),
          Complex.exp (Complex.I * (((2 * Real.pi * (m i : ℝ) : ℝ) : ℂ) * (t : ℂ))) := by
    rw [show Work.BoseB4.vec m = WithLp.toLp 2 (fun i : Fin 3 => 2 * Real.pi * (m i : ℝ))
      from rfl]
    calc ∫ x in Work.BoseB4.unitCell,
          Complex.exp (Complex.I * (inner ℝ (WithLp.toLp 2 (fun i : Fin 3 =>
            2 * Real.pi * (m i : ℝ))) x : ℂ))
        = ∫ x in Work.BoseB4.unitCell,
            Complex.exp (Complex.I * (∑ i, (2 * Real.pi * (m i : ℝ)) * x.ofLp i)) := by
          apply setIntegral_congr_fun Work.BoseB4.isClosed_unitCell.measurableSet
          intro x _
          simp only []
          rw [inner_toLp_apply]
      _ = ∫ y in Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-(1 / 2) : ℝ) (1 / 2)),
            Complex.exp (Complex.I * (∑ i, (2 * Real.pi * (m i : ℝ)) * y i)) := by
          rw [show Work.BoseB4.unitCell =
            {x : EuclideanSpace ℝ (Fin 3) | ∀ i, |x i| ≤ (1 / 2 : ℝ)} from rfl]
          exact Work.BoseB4.ofLp_unitCell_integral (F := fun y : Fin 3 → ℝ =>
            Complex.exp (Complex.I * (∑ i, (2 * Real.pi * (m i : ℝ)) * y i)))
      _ = ∫ y in Set.pi Set.univ (fun _ : Fin 3 => Set.Icc (-(1 / 2) : ℝ) (1 / 2)),
            (∏ i, Complex.exp (Complex.I * ((2 * Real.pi * (m i : ℝ)) * y i))) := by
          apply setIntegral_congr_fun
            (MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Icc))
          intro y _
          simp only []
          rw [← Complex.exp_sum]
          push_cast
          rw [Finset.mul_sum]
      _ = ∏ i : Fin 3, ∫ t in Set.Icc (-(1 / 2) : ℝ) (1 / 2),
            Complex.exp (Complex.I * ((2 * Real.pi * (m i : ℝ)) * t)) :=
          Work.BoseB4.prod_integral_unitCube
            (fun i t => Complex.exp (Complex.I * ((2 * Real.pi * (m i : ℝ)) * t)))
      _ = ∏ i : Fin 3, ∫ t in Set.Icc (-(1 / 2) : ℝ) (1 / 2),
            Complex.exp (Complex.I * (((2 * Real.pi * (m i : ℝ) : ℝ) : ℂ) * (t : ℂ))) := by
          apply Finset.prod_congr rfl
          intro i _
          apply setIntegral_congr_fun measurableSet_Icc
          intro t _
          push_cast
          ring
  rw [hmain]
  have hprod1 : (∏ i : Fin 3, (∫ t in Set.Icc (-(1 / 2) : ℝ) (1 / 2),
        Complex.exp (Complex.I * (((2 * Real.pi * (m i : ℝ) : ℝ) : ℂ) * (t : ℂ)))))
      = ∏ i : Fin 3, (if m i = 0 then (1 : ℂ) else 0) := by
    apply Finset.prod_congr rfl
    intro i _
    have hpoint : ∀ t : ℝ,
        Complex.exp (Complex.I * (((2 * Real.pi * (m i : ℝ) : ℝ) : ℂ) * (t : ℂ)))
          = Complex.exp (Complex.I * ((2 * Real.pi * (m i : ℝ)) * t)) := by
      intro t
      congr 1
      push_cast
      ring
    rw [setIntegral_congr_fun measurableSet_Icc (fun t _ => hpoint t)]
    exact Work.BoseB4.cos_lattice_1d (m i)
  rw [hprod1]
  have hprod : (∏ i : Fin 3, (if m i = 0 then (1 : ℂ) else 0))
      = Complex.ofReal (∏ i : Fin 3, (if m i = 0 then (1 : ℝ) else 0)) := by
    rw [Complex.ofReal_prod]
    apply Finset.prod_congr rfl
    intro i _
    by_cases h : m i = 0 <;> simp [h]
  rw [hprod]
  have hlast : (∏ i : Fin 3, (if m i = 0 then (1 : ℝ) else 0))
      = (if m = 0 then (1 : ℝ) else 0) := by
    by_cases hm : m = 0
    · subst hm; simp
    · rw [if_neg hm]
      obtain ⟨i, hi⟩ : ∃ i : Fin 3, m i ≠ 0 := by
        by_contra h
        push Not at h
        exact hm (funext h)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  rw [hlast]
  by_cases hm : m = 0 <;> simp [hm]

/-- **Lattice orthogonality of the plane waves on the scaled box.**  For `ℓ > 0` and an integer
label `m : Fin 3 → ℤ`, the integral of the character `x ↦ e^{i⟪ℓ⁻¹ • vec m, x⟫}` over the box
`B_ℓ = [-ℓ/2,ℓ/2]³` is `ℓ³` when `m = 0` and `0` otherwise. -/
theorem box_exp_orthogonal {ℓ : ℝ} (hℓ : 0 < ℓ) (m : Fin 3 → ℤ) :
    ∫ x in {y : EuclideanSpace ℝ (Fin 3) | ∀ i, |y i| ≤ ℓ / 2},
        Complex.exp (Complex.I * (inner ℝ ((ℓ⁻¹ : ℝ) • Work.BoseB4.vec m) x : ℂ))
      = if m = 0 then ((ℓ : ℂ) ^ 3) else 0 := by
  have hℓ0 : ℓ ≠ 0 := ne_of_gt hℓ
  have hbox : {y : EuclideanSpace ℝ (Fin 3) | ∀ i, |y i| ≤ ℓ / 2}
      = ℓ • Work.BoseB4.unitCell := by
    ext y
    rw [Set.mem_smul_set]
    constructor
    · intro hy
      refine ⟨(ℓ⁻¹ : ℝ) • y, ?_, ?_⟩
      · simp only [Work.BoseB4.unitCell, Set.mem_ofPred_eq]
        intro i
        rw [show ((ℓ⁻¹ : ℝ) • y) i = ℓ⁻¹ * y i by simp, abs_mul,
          abs_of_pos (inv_pos.mpr hℓ)]
        calc ℓ⁻¹ * |y i| ≤ ℓ⁻¹ * (ℓ / 2) :=
              mul_le_mul_of_nonneg_left (hy i) (le_of_lt (inv_pos.mpr hℓ))
          _ = 1 / 2 := by field_simp
      · exact smul_inv_smul₀ hℓ0 y
    · rintro ⟨z, hz, rfl⟩
      simp only [Work.BoseB4.unitCell, Set.mem_ofPred_eq] at hz
      intro i
      rw [show (ℓ • z) i = ℓ * z i by simp, abs_mul, abs_of_pos hℓ]
      calc ℓ * |z i| ≤ ℓ * (1 / 2) := mul_le_mul_of_nonneg_left (hz i) (le_of_lt hℓ)
        _ = ℓ / 2 := by ring
  have hscale : ∫ x in ℓ • Work.BoseB4.unitCell,
        Complex.exp (Complex.I * (inner ℝ ((ℓ⁻¹ : ℝ) • Work.BoseB4.vec m) x : ℂ))
      = ℓ ^ 3 • ∫ y in Work.BoseB4.unitCell,
          Complex.exp (Complex.I * (inner ℝ ((ℓ⁻¹ : ℝ) • Work.BoseB4.vec m) (ℓ • y) : ℂ)) := by
    have hsc := MeasureTheory.Measure.setIntegral_comp_smul_of_pos (μ := volume)
      (f := fun x => Complex.exp
        (Complex.I * (inner ℝ ((ℓ⁻¹ : ℝ) • Work.BoseB4.vec m) x : ℂ)))
      (s := Work.BoseB4.unitCell) hℓ
    rw [finrank_euclideanSpace_fin] at hsc
    rw [hsc, smul_smul, mul_inv_cancel₀ (pow_ne_zero 3 hℓ0), one_smul]
  have hpt : (∫ y in Work.BoseB4.unitCell,
        Complex.exp (Complex.I * (inner ℝ ((ℓ⁻¹ : ℝ) • Work.BoseB4.vec m) (ℓ • y) : ℂ)))
      = ∫ y in Work.BoseB4.unitCell,
          Complex.exp (Complex.I * (inner ℝ (Work.BoseB4.vec m) y : ℂ)) := by
    apply setIntegral_congr_fun Work.BoseB4.isClosed_unitCell.measurableSet
    intro y _
    simp only []
    congr 1
    rw [real_inner_smul_left, real_inner_smul_right, ← mul_assoc, inv_mul_cancel₀ hℓ0,
      one_mul]
  rw [hbox, hscale, hpt, integral_unitCell_exp_lattice m]
  by_cases hm : m = 0 <;> simp [hm, Complex.real_smul]

/-! ## 4. Child B: finite Bessel for a family with Gram `L·δ` -/

/-- **Finite Bessel inequality.**  If the Gram matrix of the family `Q` is `L·δ` (with `L > 0`),
then for every `W ∈ L¹∩L²` the sum of the squared moduli of the "Fourier coefficients"
`∫ W·conj(Q_k)` is at most `L∫W²`. -/
theorem bessel_sum_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : ι → EuclideanSpace ℝ (Fin 3) → ℂ) (W : EuclideanSpace ℝ (Fin 3) → ℝ) {L : ℝ}
    (hL : 0 < L)
    (hQ : ∀ k, MeasureTheory.MemLp (Q k) 2)
    (hgram : ∀ k k', ∫ x, Q k x * star (Q k' x) = if k = k' then (L : ℂ) else 0)
    (hW : MeasureTheory.Integrable W)
    (hW2 : MeasureTheory.MemLp W 2) :
    ∑ k, ‖∫ x, (W x : ℂ) * star (Q k x)‖ ^ 2 ≤ L * ∫ x, (W x) ^ 2 := by
  have hL0 : L ≠ 0 := ne_of_gt hL
  have hsq : Real.sqrt L * Real.sqrt L = L := by rw [← sq, Real.sq_sqrt (le_of_lt hL)]
  have hLinv : (Real.sqrt L)⁻¹ * ((Real.sqrt L)⁻¹ * L) = 1 := by
    rw [← mul_assoc, ← mul_inv, hsq, inv_mul_cancel₀ hL0]
  let μ : Measure (EuclideanSpace ℝ (Fin 3)) := volume
  let v : ι → MeasureTheory.Lp ℂ 2 μ := fun k => (hQ k).toLp (Q k)
  let w : MeasureTheory.Lp ℂ 2 μ := (hW2.ofReal).toLp (fun x => (W x : ℂ))
  -- (1) the Gram pairing in `L²`
  have hvgram : ∀ k k', inner ℂ (v k) (v k') = if k = k' then (L : ℂ) else 0 := by
    intro k k'
    dsimp only [v]
    rw [MeasureTheory.L2.inner_def]
    calc ∫ x, inner ℂ ((hQ k).toLp (Q k) x) ((hQ k').toLp (Q k') x)
        = ∫ x, star (Q k x * star (Q k' x)) := by
          refine integral_congr_ae ?_
          filter_upwards [MeasureTheory.MemLp.coeFn_toLp (hQ k),
            MeasureTheory.MemLp.coeFn_toLp (hQ k')] with x h1 h2
          rw [h1, h2, RCLike.inner_apply, starRingEnd_apply, star_mul, star_star]
      _ = star (∫ x, Q k x * star (Q k' x)) := integral_conj
      _ = star (if k = k' then (L : ℂ) else 0) := by rw [hgram k k']
      _ = if k = k' then (L : ℂ) else 0 := by
          by_cases h : k = k' <;> simp [h, Complex.conj_ofReal]
  -- (2) `w` is the complexification of `W`
  have hwcoe : ∀ᵐ x ∂μ, w x = (W x : ℂ) := by
    dsimp only [w]
    exact MeasureTheory.MemLp.coeFn_toLp hW2.ofReal
  -- (3) the complex Fourier coefficients are the `L²` pairings
  have hvw : ∀ k, inner ℂ (v k) w = ∫ x, (W x : ℂ) * star (Q k x) := by
    intro k
    dsimp only [v]
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MeasureTheory.MemLp.coeFn_toLp (hQ k), hwcoe] with x h1 h2
    rw [h1, h2, RCLike.inner_apply, starRingEnd_apply]
  -- (4) the scalar `(√L)⁻¹` is real, so it pulls out of the inner products
  have hstar_inv : (starRingEnd ℂ) (((Real.sqrt L : ℂ))⁻¹) = (((Real.sqrt L : ℂ))⁻¹) := by
    rw [starRingEnd_apply, ← Complex.ofReal_inv]; simp
  have hinner_uv : ∀ k k', inner ℂ (((Real.sqrt L : ℂ))⁻¹ • v k)
        (((Real.sqrt L : ℂ))⁻¹ • v k')
      = (((Real.sqrt L : ℂ))⁻¹) * ((((Real.sqrt L : ℂ))⁻¹) * inner ℂ (v k) (v k')) := by
    intro k k'
    rw [inner_smul_left, hstar_inv, inner_smul_right]
  have hinner_uw : ∀ k, inner ℂ (((Real.sqrt L : ℂ))⁻¹ • v k) w
      = (((Real.sqrt L : ℂ))⁻¹) * inner ℂ (v k) w := by
    intro k
    rw [inner_smul_left, hstar_inv]
  -- (5) the rescaled family is orthonormal
  have hvdiag : ∀ k, inner ℂ (v k) (v k) = (L : ℂ) := by
    intro k
    simpa using hvgram k k
  have hvoff : ∀ k k', k ≠ k' → inner ℂ (v k) (v k') = 0 := by
    intro k k' h
    simpa [h] using hvgram k k'
  have hkey : (((Real.sqrt L : ℂ))⁻¹) * ((((Real.sqrt L : ℂ))⁻¹) * (L : ℂ)) = 1 := by
    rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, ← Complex.ofReal_mul, hLinv,
      Complex.ofReal_one]
  have horth : Orthonormal ℂ (fun k => (((Real.sqrt L : ℂ))⁻¹) • v k) := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hinner_uv i j]
    rcases eq_or_ne i j with hij | hij
    · subst hij
      rw [hvdiag i, hkey]
      simp
    · rw [hvoff i j hij, mul_zero, mul_zero]
      simp [hij]
  -- (6) Bessel
  have hbess : ∑ k, ‖inner ℂ (((Real.sqrt L : ℂ))⁻¹ • v k) w‖ ^ 2 ≤ ‖w‖ ^ 2 := by
    have h := horth.sum_inner_products_le w (s := Finset.univ)
    simpa using h
  -- (7) the norm of `w`
  have hwnorm : ‖w‖ ^ 2 = ∫ x, (W x) ^ 2 := by
    have h1 := norm_sq_eq_re_inner (𝕜 := ℂ) w
    rw [h1, RCLike.re_eq_complex_re, MeasureTheory.L2.inner_def]
    have h2 : (∫ a, inner ℂ (w a) (w a)) = ∫ a, (((W a) ^ 2 : ℝ) : ℂ) := by
      refine integral_congr_ae ?_
      filter_upwards [hwcoe] with x hx
      rw [hx, RCLike.inner_apply]
      have hstar : (starRingEnd ℂ) ((W x : ℂ)) = ((W x : ℂ)) := by simp
      rw [hstar, ← Complex.ofReal_mul]
      exact congrArg (fun t : ℝ => (t : ℂ)) (by ring : W x * W x = W x ^ 2)
    have h3 : (∫ a, (((W a) ^ 2 : ℝ) : ℂ)) = (((∫ a, (W a) ^ 2 : ℝ)) : ℂ) :=
      integral_ofReal (f := fun a => (W a) ^ 2)
    rw [h2, h3, Complex.ofReal_re]
  -- (8) the scaling factor of the rescaling
  have hscale : ∀ k, L * ‖inner ℂ (((Real.sqrt L : ℂ))⁻¹ • v k) w‖ ^ 2
      = ‖inner ℂ (v k) w‖ ^ 2 := by
    intro k
    rw [hinner_uw k, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    rw [show Complex.normSq (((Real.sqrt L : ℂ))⁻¹ * inner ℂ (v k) w)
        = Complex.normSq (((Real.sqrt L : ℂ))⁻¹) * Complex.normSq (inner ℂ (v k) w)
        from map_mul Complex.normSq _ _]
    rw [← Complex.ofReal_inv, Complex.normSq_ofReal]
    have key : L * ((Real.sqrt L)⁻¹ * (Real.sqrt L)⁻¹ * Complex.normSq (inner ℂ (v k) w))
        = (Real.sqrt L)⁻¹ * ((Real.sqrt L)⁻¹ * L) * Complex.normSq (inner ℂ (v k) w) := by
      ring
    rw [key, hLinv, one_mul]
  calc ∑ k, ‖∫ x, (W x : ℂ) * star (Q k x)‖ ^ 2
      = ∑ k, L * ‖inner ℂ (((Real.sqrt L : ℂ))⁻¹ • v k) w‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro k _
        rw [← hvw k, ← hscale k]
    _ = L * ∑ k, ‖inner ℂ (((Real.sqrt L : ℂ))⁻¹ • v k) w‖ ^ 2 :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ L * ‖w‖ ^ 2 := mul_le_mul_of_nonneg_left hbess (le_of_lt hL)
    _ = L * ∫ x, (W x) ^ 2 := by rw [hwnorm]

-- NOTE (requester): the lattice↔continuum (Poisson/Parseval) comparison for the *square* of
-- the honest Fourier kernel, i.e. the "Bessel" row of FS §9's eq:Rough2 route.  The
-- periodisation `P(x) = Σ_m W(x - ℓm)` of a function supported in a ball of radius `R` with
-- `2R ≤ ℓ` has torus Fourier coefficients `ℓ⁻³·ĉ_j`, `ĉ_j = ∫W e^{-i⟨2πj/ℓ,y⟩}dy`, and
-- `chat W = Re ĉ`; torus Parseval gives `Σ_{j∈ℤ³}|ĉ_j|² = ℓ³∫|W|²` and hence
-- `Σ_j (chat W (2πj/ℓ))² ≤ ℓ³∫W²` (use `(Re z)² ≤ |z|²` for the general, non-even, case).
-- The honest lattice `Lab N = Fin 3 → ZMod (2N+1)` samples a *subset* of `ℤ³` (via
-- `labVec`/`kmomLab`, with `labVec` injective), so the honest sum is at most the full one.
-- Route: 3D torus Fourier/Plancherel (Mathlib's 1D `Real.tsum_eq_tsum_fourier` iterated, or
-- the corpus's `Submission.Work.SmallBoxBridge.Resolve.*` Fourier machinery), plus
-- `labVec`'s injectivity and `‖labVec N k i‖ ≤ N`.
theorem sampling_sq_sum_le {W : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hW : MeasureTheory.Integrable W) (hW2 : MeasureTheory.MemLp W 2)
    (hsupp : tsupport W ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : 2 * R ≤ ℓ) (N : ℕ) :
    ∑ k : Work.BoseBoxFock.Lab N,
        (Work.BoseFixR.chat W (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
      ≤ ℓ ^ 3 * ∫ x : EuclideanSpace ℝ (Fin 3), (W x) ^ 2 := by
  classical
  have hB : MeasurableSet (boxL ℓ) := measurableSet_boxL ℓ
  have h0 : ∀ x, x ∉ boxL ℓ → W x = 0 := eq_zero_off_boxL hsupp hRℓ
  -- the Gram matrix of the honest box characters is `ℓ³·δ`
  have hgram : ∀ k k' : Work.BoseBoxFock.Lab N,
      ∫ x, boxChar (boxL ℓ) (Work.BoseBoxFock.kmomLab ℓ N k) x
          * star (boxChar (boxL ℓ) (Work.BoseBoxFock.kmomLab ℓ N k') x)
        = if k = k' then ((ℓ ^ 3 : ℝ) : ℂ) else 0 := by
    intro k k'
    have hpt : (fun x => boxChar (boxL ℓ) (Work.BoseBoxFock.kmomLab ℓ N k) x
          * star (boxChar (boxL ℓ) (Work.BoseBoxFock.kmomLab ℓ N k') x))
        = fun x => (boxL ℓ).indicator (fun x => Complex.exp (Complex.I *
            (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k - Work.BoseBoxFock.kmomLab ℓ N k') x : ℂ))) x :=
      funext fun x =>
        boxChar_mul_star (boxL ℓ) (Work.BoseBoxFock.kmomLab ℓ N k)
          (Work.BoseBoxFock.kmomLab ℓ N k') x
    rw [hpt, integral_indicator hB, kmomLab_sub ℓ N k k', boxL,
      box_exp_orthogonal hℓ (Work.BoseBoxFock.labVec N k - Work.BoseBoxFock.labVec N k')]
    rw [show ((ℓ : ℂ) ^ 3) = ((ℓ ^ 3 : ℝ) : ℂ) from (Complex.ofReal_pow ℓ 3).symm]
    by_cases hkk : k = k'
    · subst hkk; simp
    · rw [if_neg hkk,
        if_neg fun hm => hkk (labVec_injective N (sub_eq_zero.mp hm))]
  have hb := bessel_sum_integral (fun k => boxChar (boxL ℓ) (Work.BoseBoxFock.kmomLab ℓ N k))
    W (L := ℓ ^ 3) (by positivity) (fun k => memLp_boxChar ℓ _) hgram hW hW2
  calc ∑ k : Work.BoseBoxFock.Lab N,
        (chat W (Work.BoseBoxFock.kmomLab ℓ N k)) ^ 2
      ≤ ∑ k : Work.BoseBoxFock.Lab N,
          ‖∫ x, (W x : ℂ) * star (boxChar (boxL ℓ) (Work.BoseBoxFock.kmomLab ℓ N k) x)‖ ^ 2 :=
        Finset.sum_le_sum fun k _ => sq_chat_le_norm_integral hB h0 _
    _ ≤ ℓ ^ 3 * ∫ x : EuclideanSpace ℝ (Fin 3), (W x) ^ 2 := hb

end Work.BoseFixR
