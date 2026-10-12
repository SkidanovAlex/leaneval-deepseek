import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.chi_sq_bounds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.bessel_honest` (BF2 — the honest Bessel bound)

`n₊^χ ≤ ‖χ‖∞² · N ≤ (48/π) · N` at the honest box model: the number-operator sum over the
χ-label cube is dominated by `48/π` times the total number operator.

Three ingredients:

* `frame_of_synthesis` — the synthesis bound `Σ_l (Σ_k c_k f k l)² ≤ C Σ_k c_k²` implies the
  frame bound `Σ_k ⟪f k, w⟫² ≤ C ‖w‖²` (duality, elementary);
* `bessel_frame_le` — the Fock-space Bessel inequality for a frame of one-particle vectors,
  generalising `Work.BoseB4.bessel_le_totNumOp_v2` to a frame dominated by `C · 1`;
* `frame_int_bound` — the analytic frame bound of the honest χ-modes: the Gram quadratic form
  of the localised plane waves is at most `χ(0)² ≤ 48/π` (lattice Parseval on the unit cell).
-/

noncomputable section
open scoped Real Topology BigOperators
open scoped MatrixOrder
open MeasureTheory Filter Metric

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## 1. Duality: the synthesis bound implies the frame bound -/

/-- **Duality: the synthesis bound gives the frame bound.**  If the "synthesis" operator of a
family `f : ι → Fin m → ℝ` is bounded, `Σ_l (Σ_k c_k f k l)² ≤ C Σ_k c_k²` for every
coefficient vector `c`, then so is its adjoint, i.e. the frame operator
`S = Σ_k |f k⟩⟨f k|` satisfies `S ≤ C·1` in the quadratic form sense:
`Σ_k (gram (f k) w)² ≤ C Σ_l (w l)²` for every `w : Fin m → ℝ`. -/
theorem frame_of_synthesis {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (f : ι → Fin m → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ c : ι → ℝ, ∑ l : Fin m, (∑ k : ι, c k * f k l) ^ 2 ≤ C * ∑ k : ι, (c k) ^ 2) :
    ∀ w : Fin m → ℝ, ∑ k : ι, (Work.BoseB4.gram (f k) w) ^ 2
      ≤ C * ∑ l : Fin m, (w l) ^ 2 := by
  intro w
  classical
  set Q : ℝ := ∑ k : ι, (Work.BoseB4.gram (f k) w) ^ 2 with hQdef
  set u : Fin m → ℝ := fun l => ∑ k : ι, Work.BoseB4.gram (f k) w * f k l with hudef
  -- `Q = ⟪w, u⟫`
  have hQu : Q = ∑ l : Fin m, w l * u l := by
    rw [hQdef, hudef]
    have h1 : ∀ k : ι, (Work.BoseB4.gram (f k) w) ^ 2
        = ∑ l : Fin m, Work.BoseB4.gram (f k) w * (f k l * w l) := by
      intro k
      rw [pow_two, Work.BoseB4.gram, Finset.mul_sum]
    simp only [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hQnn : 0 ≤ Q := by
    rw [hQdef]
    exact Finset.sum_nonneg fun k _ => sq_nonneg _
  -- the synthesis bound applied to `c k = ⟪f k, w⟫`
  have hnorm : ∑ l : Fin m, (u l) ^ 2 ≤ C * Q := by
    have hh := h (fun k => Work.BoseB4.gram (f k) w)
    simpa only [hudef, hQdef] using hh
  have hCS : Q ^ 2 ≤ (∑ l : Fin m, (w l) ^ 2) * (∑ l : Fin m, (u l) ^ 2) := by
    rw [hQu]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ w u
  by_cases hQ0 : Q = 0
  · rw [hQ0]
    exact mul_nonneg hC (Finset.sum_nonneg fun l _ => sq_nonneg _)
  · have hQpos : 0 < Q := lt_of_le_of_ne hQnn (Ne.symm hQ0)
    have hWnn : 0 ≤ ∑ l : Fin m, (w l) ^ 2 := Finset.sum_nonneg fun l _ => sq_nonneg _
    have h1 : Q ^ 2 ≤ (∑ l : Fin m, (w l) ^ 2) * (C * Q) :=
      le_trans hCS (mul_le_mul_of_nonneg_left hnorm hWnn)
    have h2 : Q * (Q - C * ∑ l : Fin m, (w l) ^ 2) ≤ 0 := by nlinarith [h1]
    have h3 : Q - C * ∑ l : Fin m, (w l) ^ 2 ≤ 0 := by
      by_contra hcon
      push Not at hcon
      nlinarith [h2, mul_pos hQpos hcon]
    linarith

/-! ## 2. The Fock-space Bessel inequality for a frame -/

/-- **Bessel inequality for a frame of one-particle mode vectors.**

Generalisation of `Work.BoseB4.bessel_le_totNumOp_v2` (the orthonormal case) to a family
`f : ι → Fin m → ℝ` whose frame operator `S = Σ_k |f k⟩⟨f k|` is dominated by `C · 1`
(the hypothesis `hS` is the quadratic form `⟪S w, w⟫ = Σ_k (gram (f k) w)² ≤ C ‖w‖²`). -/
theorem bessel_frame_le {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (f : ι → Fin m → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hS : ∀ w : Fin m → ℝ, ∑ k : ι, (Work.BoseB4.gram (f k) w) ^ 2
        ≤ C * ∑ l : Fin m, (w l) ^ 2)
    (Φ : Work.BoseB4.RealFock m) :
    ∑ k : ι, Work.BoseB4.bomb m (Work.BoseB4.annOf m (f k) Φ) (Work.BoseB4.annOf m (f k) Φ)
      ≤ C * Work.BoseB4.bomb m (Work.BoseB4.totNumOp m Φ) Φ := by
  classical
  -- the difference matrix `A = C·1 - S`
  set A : Fin m → Fin m → ℝ :=
    fun l l' => C * (if l = l' then (1 : ℝ) else 0) - ∑ k : ι, f k l * f k l' with hA
  have hAl : ∀ l l', A l l'
      = C * (if l = l' then (1 : ℝ) else 0) - ∑ k : ι, f k l * f k l' := by
    intro l l'
    rw [hA]
  have hsym : ∀ l l', A l l' = A l' l := by
    intro l l'
    rw [hAl l l', hAl l' l]
    congr 1
    · by_cases hl : l = l'
      · rw [if_pos hl, if_pos hl.symm]
      · rw [if_neg hl, if_neg (Ne.symm hl)]
    · exact Finset.sum_congr rfl fun k _ => by ring
  -- its quadratic form is `C ‖v‖² - Σ_k ⟪f k, v⟫²`
  have hquad : ∀ v : Fin m → ℝ, 0 ≤ ∑ l : Fin m, ∑ l' : Fin m, v l * A l l' * v l' := by
    intro v
    have hstep : ∀ l l' : Fin m, v l * A l l' * v l'
        = C * (v l * (if l = l' then (1 : ℝ) else 0) * v l')
          - ∑ k : ι, v l * (f k l * f k l') * v l' := by
      intro l l'
      rw [hAl l l', mul_sub, sub_mul, Finset.mul_sum, Finset.sum_mul]
      congr 1
      ring
    have key : ∑ l : Fin m, ∑ l' : Fin m, v l * A l l' * v l'
        = C * ∑ l : Fin m, (v l) ^ 2 - ∑ k : ι, (Work.BoseB4.gram (f k) v) ^ 2 := by
      have hinner : ∀ l : Fin m,
          ∑ l' : Fin m, v l * A l l' * v l'
            = (∑ l' : Fin m, C * (v l * (if l = l' then (1 : ℝ) else 0) * v l'))
              - ∑ l' : Fin m, ∑ k : ι, v l * (f k l * f k l') * v l' := by
        intro l
        rw [Finset.sum_congr rfl (fun l' _ => hstep l l'), Finset.sum_sub_distrib]
      simp only [hinner, Finset.sum_sub_distrib]
      congr 1
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_eq_single l (by
              intro b _ hb
              rw [if_neg (Ne.symm hb)]
              ring)
            (by
              intro hh
              exact absurd (Finset.mem_univ l) hh)]
        rw [if_pos rfl]
        ring
      · rw [Finset.sum_congr rfl (fun l _ => Finset.sum_comm), Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Work.BoseB4.gram, pow_two, Finset.sum_mul_sum]
        exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun l' _ => by ring
    rw [key]
    linarith [hS v]
  have hpsd : (Matrix.of A).PosSemidef := Work.BoseB4.PosSemidefOfQuadform A hsym hquad
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_mul_star_self.mp hpsd.nonneg
  have hfact : ∀ l l', A l l' = ∑ p : Fin m, B l p * B l' p := by
    intro l l'
    have hh := congrFun (congrFun hB l) l'
    rw [Matrix.mul_apply] at hh
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial,
      Matrix.of_apply] at hh
    exact hh
  -- `Σ_k a†(f k) a(f k)` and `C • N` in `besselOpMat` form
  have hSum : (∑ k : ι, (Work.BoseB4.creOf m (f k)).comp (Work.BoseB4.annOf m (f k)))
      = Work.BoseB4.besselOpMat m (fun l l' => ∑ k : ι, f k l * f k l') := by
    rw [Work.BoseB4.besselOpMat]
    exact Work.BoseB4.finset_sum_creOf_comp_annOf f Finset.univ
  have hN : C • Work.BoseB4.totNumOp m
      = Work.BoseB4.besselOpMat m (fun l l' => C * (if l = l' then (1 : ℝ) else 0)) := by
    rw [Work.BoseB4.totNumOp_eq_double_sum m, Work.BoseB4.besselOpMat, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [smul_smul]
  have hop : Work.BoseB4.besselOpMat m A
      = C • Work.BoseB4.totNumOp m
        - ∑ k : ι, (Work.BoseB4.creOf m (f k)).comp (Work.BoseB4.annOf m (f k)) := by
    rw [hSum, hN, ← Work.BoseB4.besselOpMat_sub]
    rfl
  -- the factored operator is a sum of `a†(w_p)a(w_p)`
  have hsplit : Work.BoseB4.besselOpMat m A
      = ∑ p : Fin m,
          (Work.BoseB4.creOf m (fun l => B l p)).comp (Work.BoseB4.annOf m (fun l => B l p)) := by
    have hA' : A = fun l l' => ∑ p : Fin m, B l p * B l' p := by
      funext l l'
      exact hfact l l'
    rw [hA']
    simp only [Work.BoseB4.besselOpMat]
    rw [← Work.BoseB4.finset_sum_creOf_comp_annOf (m := m) (W := fun p l => B l p) Finset.univ]
  have hpos : 0 ≤ Work.BoseB4.bomb m (Work.BoseB4.besselOpMat m A Φ) Φ := by
    rw [hsplit, LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_nonneg fun p _ => ?_
    rw [LinearMap.comp_apply, Work.BoseB4.CreOf_annOf_adjoint]
    exact Work.BoseB4.Bomb_self_nonneg _
  -- conclude by linearity
  have key2 : Work.BoseB4.bomb m (Work.BoseB4.besselOpMat m A Φ) Φ
      = C * Work.BoseB4.bomb m (Work.BoseB4.totNumOp m Φ) Φ
        - ∑ k : ι, Work.BoseB4.bomb m (Work.BoseB4.annOf m (f k) Φ)
            (Work.BoseB4.annOf m (f k) Φ) := by
    simp only [hop, LinearMap.sub_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      map_sub, map_smul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.comp_apply, Work.BoseB4.CreOf_annOf_adjoint]
  linarith [hpos, key2]

/-! ## 3. The analytic frame bound of the honest χ-modes -/

/-- `χ_Λ` at `ℓ = 1` is `χ`. -/
lemma corpusBox_chiLam_one : Work.BoseK15.corpusBox.chiLam 1 = Work.BoseK15.corpusBox.chi := by
  funext x
  simp only [Work.BoseB4.BoxData.chiLam, inv_one, one_smul]

/-- `χ² cos⟪p,·⟫` is integrable: the bump is continuous with compact support. -/
lemma corpusBox_integrable_chiSq_cos (p : ℝ³) :
    Integrable (fun x : ℝ³ => (Work.BoseK15.corpusBox.chi x) ^ 2 * Real.cos (inner ℝ p x)) := by
  have h := Work.BoseB4.BoxData.integrable_chiLam_sq_mul_cos Work.BoseK15.corpusBox
    (by norm_num : (0 : ℝ) < 1) p
  rwa [corpusBox_chiLam_one] at h

/-- `χ x ^ 2 ≤ χ 0 ^ 2`. -/
lemma corpusBox_chi_sq_le (x : ℝ³) :
    (Work.BoseK15.corpusBox.chi x) ^ 2 ≤ (Work.BoseK15.corpusBox.chi 0) ^ 2 := by
  simpa only [Work.BoseK15.corpusBox_chi, chiSqBounds_chi_zero_sq] using chiSqBounds_chi_sq_le x

/-- The centred representatives of the cube labels are distinct. -/
lemma labVec_injective (N : ℕ) : Function.Injective (labVec N) := by
  intro n m h
  funext i
  refine ZMod.injective_valMinAbs ?_
  have h' := congrFun h i
  simpa only [labVec] using h'

/-- `vec` is additive in the difference of integral vectors. -/
lemma vec_sub_vec (n m : Fin 3 → ℤ) :
    Work.BoseB4.vec n - Work.BoseB4.vec m = Work.BoseB4.vec (n - m) := by
  rw [Work.BoseB4.vec_sub (m := n) (n := m)]
  congr 1

/-- **The lattice-frame bound behind `bessel_honest`.**  For the corpus bump `χ` and the
integer labels `labVec N i` of the cube, the Gram quadratic form of the localised plane waves
`Q(e^{i⟨vec (labVec N i), x⟩} χ)` is bounded by `χ(0)² ≤ 48/π` (Parseval on the unit cell). -/
theorem frame_int_bound (N : ℕ) (c : Lab N → ℝ) :
    (∑ i : Lab N, ∑ j : Lab N, c i * c j *
      (Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec N i - labVec N j))
        - Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec N i))
          * Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec N j))))
      ≤ (48 / Real.pi) * ∑ i : Lab N, (c i) ^ 2 := by
  classical
  set A : Lab N → Lab N → ℝ := fun i j =>
    Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec N i - labVec N j)) with hA
  set B : Lab N → ℝ := fun i =>
    Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec N i)) with hB
  -- the synthesis functions and the trigonometric identity
  set F : ℝ³ → ℝ := fun x => ∑ i : Lab N, c i * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N i)) x) with hF
  set G : ℝ³ → ℝ := fun x => ∑ i : Lab N, c i * Real.sin (inner ℝ (Work.BoseB4.vec (labVec N i)) x) with hG
  have htrig : ∀ x : ℝ³, F x ^ 2 + G x ^ 2 = ∑ i : Lab N, ∑ j : Lab N, c i * c j *
      Real.cos (inner ℝ (Work.BoseB4.vec (labVec N i - labVec N j)) x) := by
    intro x
    have hcos : ∀ i j : Lab N,
        Real.cos (inner ℝ (Work.BoseB4.vec (labVec N i - labVec N j)) x)
        = Real.cos (inner ℝ (Work.BoseB4.vec (labVec N i)) x)
            * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N j)) x)
          + Real.sin (inner ℝ (Work.BoseB4.vec (labVec N i)) x)
            * Real.sin (inner ℝ (Work.BoseB4.vec (labVec N j)) x) := by
      intro i j
      have hsub : inner ℝ (Work.BoseB4.vec (labVec N i)) x
            - inner ℝ (Work.BoseB4.vec (labVec N j)) x
          = inner ℝ (Work.BoseB4.vec (labVec N i - labVec N j)) x := by
        rw [← inner_sub_left, vec_sub_vec]
      rw [← hsub, Real.cos_sub]
    rw [hF, hG]
    simp only [hcos]
    rw [pow_two, pow_two, Finset.sum_mul_sum, Finset.sum_mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  -- Step B: the A-sum is the weighted integral of `F² + G²`
  have hBsum : (∑ i : Lab N, ∑ j : Lab N, c i * c j * A i j)
      = ∫ x, (Work.BoseK15.corpusBox.chi x) ^ 2 * (F x ^ 2 + G x ^ 2) := by
    have hint : ∀ i j : Lab N, Integrable (fun x : ℝ³ => c i * c j *
        ((Work.BoseK15.corpusBox.chi x) ^ 2
          * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N i - labVec N j)) x))) :=
      fun i j => (corpusBox_integrable_chiSq_cos _).const_mul _
    have h1 : ∀ i j : Lab N, c i * c j * A i j
        = ∫ x, c i * c j * ((Work.BoseK15.corpusBox.chi x) ^ 2
            * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N i - labVec N j)) x)) := by
      intro i j
      rw [hA]
      show c i * c j * (∫ x, (Work.BoseK15.corpusBox.chi x) ^ 2
            * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N i - labVec N j)) x)) = _
      rw [MeasureTheory.integral_const_mul]
    have hkey : ∀ x : ℝ³,
        (∑ i : Lab N, ∑ j : Lab N, c i * c j * ((Work.BoseK15.corpusBox.chi x) ^ 2
            * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N i - labVec N j)) x)))
          = (Work.BoseK15.corpusBox.chi x) ^ 2 * (F x ^ 2 + G x ^ 2) := by
      intro x
      rw [htrig x, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    calc (∑ i : Lab N, ∑ j : Lab N, c i * c j * A i j)
        = ∑ i : Lab N, ∑ j : Lab N, ∫ x, c i * c j * ((Work.BoseK15.corpusBox.chi x) ^ 2
            * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N i - labVec N j)) x)) := by
          simp only [h1]
      _ = ∑ i : Lab N, ∫ x, ∑ j : Lab N, c i * c j * ((Work.BoseK15.corpusBox.chi x) ^ 2
            * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N i - labVec N j)) x)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hint i j)]
      _ = ∫ x, ∑ i : Lab N, ∑ j : Lab N, c i * c j * ((Work.BoseK15.corpusBox.chi x) ^ 2
            * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N i - labVec N j)) x)) := by
          rw [MeasureTheory.integral_finsetSum Finset.univ
            (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hint i j))]
      _ = ∫ x, (Work.BoseK15.corpusBox.chi x) ^ 2 * (F x ^ 2 + G x ^ 2) :=
          MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hkey)
  -- `F² + G²` is continuous, hence integrable on the compact cell
  have hFc : Continuous F := by
    rw [hF]
    fun_prop
  have hGc : Continuous G := by
    rw [hG]
    fun_prop
  have hFGint : IntegrableOn (fun x : ℝ³ => F x ^ 2 + G x ^ 2) Work.BoseB4.unitCell :=
    ((hFc.pow 2).add (hGc.pow 2)).continuousOn.integrableOn_compact Work.BoseB4.isCompact_unitCell
  -- Step C: comparison with `χ(0)²` on the unit cell
  have hC1 : (∫ x, (Work.BoseK15.corpusBox.chi x) ^ 2 * (F x ^ 2 + G x ^ 2))
      = ∫ x in Work.BoseB4.unitCell, (Work.BoseK15.corpusBox.chi x) ^ 2 * (F x ^ 2 + G x ^ 2) := by
    refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Work.BoseB4.unitCell) (fun x hx => ?_)).symm
    have h0 : Work.BoseK15.corpusBox.chi x = 0 := by
      by_contra hne
      exact hx (Work.BoseK15.corpusBox.chi_supp (Function.mem_support.mpr hne))
    rw [h0]
    ring
  have hC2 : (∫ x in Work.BoseB4.unitCell,
        (Work.BoseK15.corpusBox.chi x) ^ 2 * (F x ^ 2 + G x ^ 2))
      ≤ ∫ x in Work.BoseB4.unitCell,
        (Work.BoseK15.corpusBox.chi 0) ^ 2 * (F x ^ 2 + G x ^ 2) := by
    have hχc : Continuous (fun x : ℝ³ => (Work.BoseK15.corpusBox.chi x) ^ 2 * (F x ^ 2 + G x ^ 2)) :=
      ((Work.BoseK15.corpusBox.chi_cont.pow 2).mul ((hFc.pow 2).add (hGc.pow 2)))
    refine MeasureTheory.setIntegral_mono_on
      (hχc.continuousOn.integrableOn_compact Work.BoseB4.isCompact_unitCell)
      (hFGint.const_mul _) Work.BoseB4.isClosed_unitCell.measurableSet ?_
    intro x _
    exact mul_le_mul_of_nonneg_right (corpusBox_chi_sq_le x) (by positivity)
  have hC3 : (∫ x in Work.BoseB4.unitCell,
        (Work.BoseK15.corpusBox.chi 0) ^ 2 * (F x ^ 2 + G x ^ 2))
      = (Work.BoseK15.corpusBox.chi 0) ^ 2
        * ∫ x in Work.BoseB4.unitCell, (F x ^ 2 + G x ^ 2) :=
    MeasureTheory.integral_const_mul _ _
  -- Step D: Parseval on the unit cell
  have hD : (∫ x in Work.BoseB4.unitCell, (F x ^ 2 + G x ^ 2))
      = ∑ i : Lab N, (c i) ^ 2 := by
    have hint : ∀ i j : Lab N, IntegrableOn (fun x : ℝ³ => c i * c j
        * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N i - labVec N j)) x))
        Work.BoseB4.unitCell := by
      intro i j
      refine (((Real.continuous_cos.comp ?_).const_mul (c i * c j))).continuousOn.integrableOn_compact
        Work.BoseB4.isCompact_unitCell
      exact continuous_const.inner continuous_id
    have h1 : ∀ i j : Lab N, (∫ x in Work.BoseB4.unitCell, c i * c j
          * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N i - labVec N j)) x))
        = c i * c j * (if labVec N i - labVec N j = 0 then (1 : ℝ) else 0) := by
      intro i j
      rw [MeasureTheory.integral_const_mul]
      show c i * c j * (∫ x in Work.BoseB4.unitCell,
          Real.cos (inner ℝ (Work.BoseB4.vec (labVec N i - labVec N j)) x)) = _
      rw [Work.BoseB4.vec, Work.BoseB4.integral_unitCell_cos_lattice]
    calc (∫ x in Work.BoseB4.unitCell, (F x ^ 2 + G x ^ 2))
        = ∫ x in Work.BoseB4.unitCell, ∑ i : Lab N, ∑ j : Lab N, c i * c j *
            Real.cos (inner ℝ (Work.BoseB4.vec (labVec N i - labVec N j)) x) := by
          refine MeasureTheory.setIntegral_congr_fun Work.BoseB4.isClosed_unitCell.measurableSet
            (fun x _ => htrig x)
      _ = ∑ i : Lab N, ∫ x in Work.BoseB4.unitCell,
            ∑ j : Lab N, c i * c j
              * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N i - labVec N j)) x) := by
          rw [MeasureTheory.integral_finsetSum Finset.univ
            (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hint i j))]
      _ = ∑ i : Lab N, ∑ j : Lab N, ∫ x in Work.BoseB4.unitCell,
            c i * c j * Real.cos (inner ℝ (Work.BoseB4.vec (labVec N i - labVec N j)) x) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hint i j)]
      _ = ∑ i : Lab N, ∑ j : Lab N, c i * c j
            * (if labVec N i - labVec N j = 0 then (1 : ℝ) else 0) := by
          simp only [h1]
      _ = ∑ i : Lab N, (c i) ^ 2 := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have hif : ∀ j : Lab N,
              (if labVec N i - labVec N j = 0 then (1 : ℝ) else 0)
                = (if j = i then (1 : ℝ) else 0) := by
            intro j
            by_cases h : j = i
            · rw [if_pos h, if_pos (by rw [h, sub_self])]
            · rw [if_neg h, if_neg (fun h0 => h (labVec_injective N (sub_eq_zero.mp h0)).symm)]
          simp only [hif]
          rw [Finset.sum_eq_single i]
          · rw [if_pos rfl]
            ring
          · intro j _ hji
            rw [if_neg hji]
            ring
          · intro h
            exact absurd (Finset.mem_univ i) h
  -- Step E: the constant
  have hE : (Work.BoseK15.corpusBox.chi 0) ^ 2 ≤ 48 / Real.pi := by
    simpa only [Work.BoseK15.corpusBox_chi] using chi_sq_bounds.2 0
  -- Step B + C + D + E
  have hmain : (∑ i : Lab N, ∑ j : Lab N, c i * c j * A i j)
      ≤ (48 / Real.pi) * ∑ i : Lab N, (c i) ^ 2 := by
    rw [hBsum, hC1]
    calc (∫ x in Work.BoseB4.unitCell,
          (Work.BoseK15.corpusBox.chi x) ^ 2 * (F x ^ 2 + G x ^ 2))
        ≤ ∫ x in Work.BoseB4.unitCell,
            (Work.BoseK15.corpusBox.chi 0) ^ 2 * (F x ^ 2 + G x ^ 2) := hC2
      _ = (Work.BoseK15.corpusBox.chi 0) ^ 2
            * ∫ x in Work.BoseB4.unitCell, (F x ^ 2 + G x ^ 2) := hC3
      _ = (Work.BoseK15.corpusBox.chi 0) ^ 2 * ∑ i : Lab N, (c i) ^ 2 := by rw [hD]
      _ ≤ (48 / Real.pi) * ∑ i : Lab N, (c i) ^ 2 :=
          mul_le_mul_of_nonneg_right hE (Finset.sum_nonneg fun i _ => sq_nonneg _)
  -- drop the (nonnegative) condensate term
  have hdrop : (∑ i : Lab N, ∑ j : Lab N, c i * c j * (A i j - B i * B j))
      = (∑ i : Lab N, ∑ j : Lab N, c i * c j * A i j)
        - (∑ i : Lab N, c i * B i) ^ 2 := by
    have h1 : ∀ i j : Lab N, c i * c j * (A i j - B i * B j)
        = c i * c j * A i j - c i * c j * (B i * B j) := fun i j => by ring
    calc (∑ i : Lab N, ∑ j : Lab N, c i * c j * (A i j - B i * B j))
        = ∑ i : Lab N, ∑ j : Lab N,
            (c i * c j * A i j - c i * c j * (B i * B j)) := by simp only [h1]
      _ = (∑ i : Lab N, ∑ j : Lab N, c i * c j * A i j)
            - ∑ i : Lab N, ∑ j : Lab N, c i * c j * (B i * B j) := by
          simp only [Finset.sum_sub_distrib]
      _ = (∑ i : Lab N, ∑ j : Lab N, c i * c j * A i j)
            - (∑ i : Lab N, c i * B i) ^ 2 := by
          congr 1
          rw [pow_two, Finset.sum_mul_sum]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hdrop]
  linarith [hmain, sq_nonneg (∑ i : Lab N, c i * B i)]

/-! ## 4. The assembly -/

/-- `ℓ • kmomLab ℓ N n = vec (labVec N n)` (`ℓ ≠ 0`). -/
lemma smul_kmomLab {ℓ : ℝ} (hℓ : ℓ ≠ 0) (N : ℕ) (n : Lab N) :
    ℓ • kmomLab ℓ N n = Work.BoseB4.vec (labVec N n) := by
  rw [kmomLab, smul_smul, mul_inv_cancel₀ hℓ, one_smul]

/-- `ℓ • (kmomLab ℓ N i - kmomLab ℓ N j) = vec (labVec N i - labVec N j)` (`ℓ ≠ 0`). -/
lemma smul_kmomLab_sub {ℓ : ℝ} (hℓ : ℓ ≠ 0) (N : ℕ) (i j : Lab N) :
    ℓ • (kmomLab ℓ N i - kmomLab ℓ N j)
      = Work.BoseB4.vec (labVec N i - labVec N j) := by
  rw [smul_sub, smul_kmomLab hℓ, smul_kmomLab hℓ, Work.BoseB4.vec_sub]
  congr 1

theorem bessel_honest (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (fc fu : Work.BoseBoxFix.LowCut)
    (HM : ∀ μ, HonestModes v μ) (μ : ℝ) :
    ∀ f : (HonestBoxFam v h fc fu HM μ).F.H,
      (HonestBoxFam v h fc fu HM μ).F.bp
          ((∑ k : (HonestBoxFam v h fc fu HM μ).Mode, (HonestBoxFam v h fc fu HM μ).F.nOp k) f) f
        ≤ (48 / Real.pi) * (HonestBoxFam v h fc fu HM μ).F.bp ((HonestBoxFam v h fc fu HM μ).T.N f) f := by
  show ∀ Φ : Work.BoseB4.RealFock (HM μ).m,
      Work.BoseB4.bomb (HM μ).m
          ((∑ k : Lab (HM μ).N, (Work.BoseB4.creOf (HM μ).m ((HM μ).f k)).comp
            (Work.BoseB4.annOf (HM μ).m ((HM μ).f k))) Φ) Φ
        ≤ (48 / Real.pi) * Work.BoseB4.bomb (HM μ).m
            (Work.BoseB4.totNumOp (HM μ).m Φ) Φ
  intro Φ
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  -- the Gram quadratic form of the honest χ-modes is the kernel of `frame_int_bound`
  have hgram : ∀ k k' : Lab (HM μ).N,
      Work.BoseB4.gram ((HM μ).f k) ((HM μ).f k')
        = Work.BoseK15.corpusBox.hatChiSq (Work.BoseB4.vec (labVec (HM μ).N k - labVec (HM μ).N k'))
          - Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec (HM μ).N k))
            * Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec (HM μ).N k')) := by
    intro k k'
    rw [(HM μ).hf k k', Work.BoseB7.ccrKernel,
      smul_kmomLab_sub (ne_of_gt hℓ) (HM μ).N k k', smul_kmomLab (ne_of_gt hℓ) (HM μ).N k,
      smul_kmomLab (ne_of_gt hℓ) (HM μ).N k']
  -- the synthesis bound
  have hsyn : ∀ c : Lab (HM μ).N → ℝ,
      ∑ l : Fin (HM μ).m, (∑ k : Lab (HM μ).N, c k * (HM μ).f k l) ^ 2
        ≤ (48 / Real.pi) * ∑ k : Lab (HM μ).N, (c k) ^ 2 := by
    intro c
    rw [(Work.BoseB4.gram_quadForm_eq_sum_sq (HM μ).f c).symm]
    have hcongr : ∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N,
          c i * Work.BoseB4.gram ((HM μ).f i) ((HM μ).f j) * c j
        = ∑ i : Lab (HM μ).N, ∑ j : Lab (HM μ).N, c i * c j *
            (Work.BoseK15.corpusBox.hatChiSq
                (Work.BoseB4.vec (labVec (HM μ).N i - labVec (HM μ).N j))
              - Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec (HM μ).N i))
                * Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec (labVec (HM μ).N j))) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hgram i j]
      ring
    rw [hcongr]
    exact frame_int_bound (HM μ).N c
  -- the frame bound
  have hframe := frame_of_synthesis (HM μ).f (48 / Real.pi) (by positivity) hsyn
  -- reduce the goal to the Fock-space statement
  have hgoal := bessel_frame_le (HM μ).f (48 / Real.pi) (by positivity) hframe Φ
  have hL : Work.BoseB4.bomb (HM μ).m ((∑ k : Lab (HM μ).N,
        (Work.BoseB4.creOf (HM μ).m ((HM μ).f k)).comp
          (Work.BoseB4.annOf (HM μ).m ((HM μ).f k))) Φ) Φ
      = ∑ k : Lab (HM μ).N, Work.BoseB4.bomb (HM μ).m
          (Work.BoseB4.annOf (HM μ).m ((HM μ).f k) Φ)
          (Work.BoseB4.annOf (HM μ).m ((HM μ).f k) Φ) := by
    rw [LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.comp_apply, Work.BoseB4.CreOf_annOf_adjoint]
  rw [hL]
  exact hgoal

end Work.BoseBoxFock
