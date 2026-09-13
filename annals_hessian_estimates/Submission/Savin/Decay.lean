/-
# The decay lemma for the contact sets

Savin's iteration for the weak Harnack inequality: iterating the "enlarge opening" lemma
(`Submission.Savin.Enlarge.enlarge_opening`) and the covering lemma
(`Commons.MeasureTheory.Covering.growing_ink_spots`) shows that the measure of the complement of
the contact set `T_{a M^k}` of the iterated opening decays geometrically in `k`.

If `φ` solves `Fop C ε (D²φ) = 0` in `B_{3/2}`, `T_j` denotes the contact set of opening
`a M^j`, `S := B_{1/2}` and `E_j := S \ T_j`, then (with `μ` the density constant of the
enlarge-opening lemma and `θ := μ / 5^4`)

  `|E_K| ≤ ofReal ((1 - θ)^K) |S|`

provided the opening `a M^K` stays in the range where the growth lemma applies
(`48 ε (a M^K) 2^(2p+4) ≤ c`) and `E_0` occupies at most the `(1-μ)`-fraction of `S` at the
initial step (the base case, supplied by the density corollary `Submission.density_contactPt`).

The proof is the standard one: `E_{j+1} ⊆ E_j` by monotonicity of the contact sets in the
opening; if `(1-μ)`-of a ball is covered by the ink `E_{j+1}` then that ball cannot touch `T_j`
(because then the enlarge-opening lemma would force a `μ`-fraction of the ball to lie in
`T_{j+1}`), so the ball is contained in `E_j`; the covering lemma then gives
`|E_{j+1}| ≤ (1 - θ)|E_j|`, which iterates.
-/
import Mathlib
import ChallengeDeps
import Submission.Savin.Enlarge
import Submission.Commons.MeasureTheory.Covering.growing_ink_spots

open Metric MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace Topology ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Submission

local notation "ℝ⁴" => EuclideanSpace ℝ (Fin 4)

noncomputable section

/-- The closed ball and the open ball have the same measure after intersecting with a set. -/
theorem volume_inter_closedBall (x : ℝ⁴) (r : ℝ) (B : Set ℝ⁴) :
    volume (B ∩ closedBall x r) = volume (B ∩ ball x r) := by
  refine le_antisymm ?_
    (measure_mono (Set.inter_subset_inter subset_rfl ball_subset_closedBall))
  have hset : B ∩ closedBall x r = (B ∩ ball x r) ∪ (B ∩ sphere x r) := by
    rw [← Set.inter_union_distrib_left, ball_union_sphere]
  rw [hset]
  calc volume ((B ∩ ball x r) ∪ (B ∩ sphere x r))
      ≤ volume (B ∩ ball x r) + volume (B ∩ sphere x r) := measure_union_le _ _
    _ = volume (B ∩ ball x r) := by
        rw [measure_mono_null (Set.inter_subset_right)
          (MeasureTheory.Measure.addHaar_sphere volume x r), add_zero]

/-- The closed ball and the open ball have the same measure after deleting a set. -/
theorem volume_sdiff_closedBall (x : ℝ⁴) (r : ℝ) (B : Set ℝ⁴) :
    volume (closedBall x r \ B) = volume (ball x r \ B) := by
  rw [Set.sdiff_eq, Set.sdiff_eq, Set.inter_comm (closedBall x r) Bᶜ,
    Set.inter_comm (ball x r) Bᶜ]
  exact volume_inter_closedBall x r Bᶜ

/-- If a ball `ball x r` with `0 < r` is contained in a ball of the same centre type, then the
corresponding closed ball is too. -/
theorem closedBall_subset_closedBall_of_ball_subset {x y : ℝ⁴} {r R : ℝ} (hr : 0 < r)
    (h : ball x r ⊆ ball y R) : closedBall x r ⊆ closedBall y R := by
  have h1 : closure (ball x r) ⊆ closure (closedBall y R) :=
    closure_mono (subset_trans h ball_subset_closedBall)
  rwa [closure_ball x hr.ne', isClosed_closedBall.closure_eq] at h1

/-- Measure-theoretic arithmetic: if `δ ≥ 0` and a `δ`-fraction of `A` lies in `B`, then the
part of `A` outside `B` has measure at most `(1-δ)|A|`. -/
theorem volume_sdiff_le_ofReal {A B : Set ℝ⁴} (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hfin : volume A ≠ ⊤) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (h : ENNReal.ofReal δ * volume A ≤ volume (A ∩ B)) :
    volume (A \ B) ≤ ENNReal.ofReal (1 - δ) * volume A := by
  have hABfin : volume (A ∩ B) < ⊤ :=
    lt_of_le_of_lt (measure_mono Set.inter_subset_left) hfin.lt_top
  have hset : A \ B = A \ (A ∩ B) := by
    ext z; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto
  rw [hset, measure_sdiff Set.inter_subset_left (hAm.inter hBm).nullMeasurableSet hABfin.ne]
  refine le_trans (tsub_le_tsub_left h _) ?_
  have h1mδ : 0 ≤ 1 - δ := by linarith
  have hsum : ENNReal.ofReal δ * volume A + ENNReal.ofReal (1 - δ) * volume A = volume A := by
    rw [← add_mul, ← ENNReal.ofReal_add hδ0 h1mδ, show δ + (1 - δ) = 1 by ring]
    simp
  have hgoal : volume A ≤ ENNReal.ofReal (1 - δ) * volume A + ENNReal.ofReal δ * volume A := by
    rw [add_comm, hsum]
  rwa [tsub_le_iff_right]

/-- The decay constant `θ` of the decay lemma is at most `1` (it is used as the base of a
geometric decay). -/
theorem one_sub_theta_nonneg {C : ℝ⁴ →L[ℝ] ℝ⁴} {c M : ℝ} (hm : 1 < M) (hc : 0 < c)
    (htrC : 0 ≤ trOp C) :
    0 ≤ 1 - (((M - 1) / (8 * M)) ^ 4 / ((1 + (2 * trOp C / c + 3)) ^ 4 * 5 ^ 4)) := by
  have hMpos : 0 < M := by linarith
  have hKpos : 0 < 1 + (2 * trOp C / c + 3) := by positivity
  have hk0 : 0 ≤ (M - 1) / (8 * M) :=
    (div_pos (by linarith) (mul_pos (by norm_num) hMpos)).le
  have hX : 0 ≤ 2 * trOp C / c + 3 := by
    have : 0 ≤ 2 * trOp C / c := div_nonneg (by linarith) hc.le
    linarith
  have hklt : (M - 1) / (8 * M) < 1 + (2 * trOp C / c + 3) := by
    have h1 : (M - 1) / (8 * M) < 1 := by
      rw [div_lt_one (mul_pos (by norm_num) hMpos)]
      linarith
    linarith
  have hlt : ((M - 1) / (8 * M)) ^ 4 / ((1 + (2 * trOp C / c + 3)) ^ 4 * 5 ^ 4) < 1 := by
    rw [div_lt_one (by positivity)]
    nlinarith [pow_lt_pow_left₀ hklt hk0 (by norm_num : (4 : ℕ) ≠ 0), pow_pos hKpos 4]
  linarith

/-- **The decay lemma.**  The measure of the complement of the contact set of opening `a M^K`
decays geometrically in `K`, uniformly in the opening `a` (as long as the growth lemma applies).
The constant `θ` is the density constant of the enlarge-opening lemma divided by `5^4`. -/
theorem decay_contactPt {φ : ℝ⁴ → ℝ} (hφ : ContDiffOn ℝ 2 φ (ball 0 (3 / 2)))
    {C : ℝ⁴ →L[ℝ] ℝ⁴} (hC : C.IsSymmetric) {c c' : ℝ} (hc : 0 < c)
    (hcq : ∀ v : ℝ⁴, c * ‖v‖ ^ 2 ≤ ⟪C v, v⟫) (hcq' : ∀ v : ℝ⁴, ⟪C v, v⟫ ≤ c' * ‖v‖ ^ 2)
    {ε : ℝ} (hε : 0 < ε) (heq : ∀ x ∈ ball 0 (3 / 2), Fop C ε (hessOp φ x) = 0)
    {a p M : ℝ} (ha : 0 < a) (hp : 0 < p) (hM1 : 1 < M)
    (hM : M = 1 + 128 * ((1 / p) * (2 ^ p - 1))) (hpbig : 16 * c' / c + 2 ≤ p)
    {K : ℕ} (hbig : 48 * ε * (a * M ^ K) * 2 ^ (2 * p + 4) ≤ c)
    (hbig' : 3 * ε * (a * M ^ K) ≤ c / 2)
    (hbase : volume (closedBall 0 (1 / 2) \ contactPt a φ) ≤
      ENNReal.ofReal (1 - (((M - 1) / (8 * M)) ^ 4 / (1 + (2 * trOp C / c + 3)) ^ 4))
        * volume (closedBall (0 : ℝ⁴) (1 / 2))) :
    volume (closedBall 0 (1 / 2) \ contactPt (a * M ^ K) φ) ≤
      ENNReal.ofReal ((1 - (((M - 1) / (8 * M)) ^ 4 /
        ((1 + (2 * trOp C / c + 3)) ^ 4 * 5 ^ 4))) ^ K) * volume (closedBall (0 : ℝ⁴) (1 / 2)) := by
  have hφ1 : ContDiffOn ℝ 1 φ (ball 0 1) :=
    (hφ.of_le (m := 1) (by norm_num)).mono (ball_subset_ball (by norm_num))
  have h2p : (1 : ℝ) < 2 ^ p := Real.one_lt_rpow (by norm_num) hp
  have hMpos : 0 < M := by linarith
  have htrC : 0 ≤ trOp C := by
    rw [trOp_eq_sum]
    refine Finset.sum_nonneg fun i _ => ?_
    have h2 := hcq (stdB4 i)
    have h3 : ‖stdB4 i‖ = 1 := stdB4.orthonormal.1 i
    rw [h3] at h2
    nlinarith [h2]
  set μ : ℝ := ((M - 1) / (8 * M)) ^ 4 / (1 + (2 * trOp C / c + 3)) ^ 4 with hμdef
  set θ : ℝ := μ / 5 ^ 4 with hθdef
  have hKpos : 0 < 1 + (2 * trOp C / c + 3) := by positivity
  have hMm1 : 0 < M - 1 := by linarith
  have hk0 : 0 ≤ (M - 1) / (8 * M) :=
    (div_pos hMm1 (mul_pos (by norm_num) hMpos)).le
  have hklt : (M - 1) / (8 * M) < 1 + (2 * trOp C / c + 3) := by
    have hX : 0 ≤ 2 * trOp C / c + 3 := by
      have : 0 ≤ 2 * trOp C / c := div_nonneg (by linarith [htrC]) hc.le
      linarith
    have h1 : (M - 1) / (8 * M) < 1 := by
      rw [div_lt_one (mul_pos (by norm_num) hMpos)]
      linarith
    linarith
  have hμpos : 0 < μ := by
    rw [hμdef]
    exact div_pos (pow_pos (div_pos hMm1 (mul_pos (by norm_num) hMpos)) 4) (pow_pos hKpos 4)
  have hμlt1 : μ < 1 := by
    rw [hμdef, div_lt_one (pow_pos hKpos 4)]
    exact pow_lt_pow_left₀ hklt hk0 (by norm_num)
  have hθle : 0 ≤ 1 - θ := by
    have h1 : θ < 1 := by
      rw [hθdef, div_lt_one (by norm_num : (0 : ℝ) < 5 ^ 4)]
      linarith
    linarith
  have hθeq : ((M - 1) / (8 * M)) ^ 4 / ((1 + (2 * trOp C / c + 3)) ^ 4 * 5 ^ 4) = θ := by
    rw [hθdef, hμdef, div_div]
  rw [hθeq]
  -- the base estimate, phrased for open balls
  have hbase_ball : volume (ball 0 (1 / 2) \ contactPt a φ) ≤
      ENNReal.ofReal (1 - μ) * volume (ball (0 : ℝ⁴) (1 / 2)) := by
    rw [← volume_sdiff_closedBall 0 (1 / 2) (contactPt a φ),
      ← MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball volume (0 : ℝ⁴) (1 / 2)]
    exact hbase
  -- one step of the iteration
  have hstep : ∀ j : ℕ, j + 1 ≤ K →
      volume (ball 0 (1 / 2) \ contactPt (a * M ^ (j + 1)) φ) ≤
        ENNReal.ofReal (1 - θ) * volume (ball 0 (1 / 2) \ contactPt (a * M ^ j) φ) := by
    intro j hj
    have hcl : IsClosed (contactPt (a * M ^ j) φ) := isClosed_contactPt hφ1
    have hcl' : IsClosed (contactPt (a * M ^ (j + 1)) φ) := isClosed_contactPt hφ1
    have hMp : 0 < M ^ j := pow_pos hMpos j
    have hlt : a * M ^ j < a * M ^ (j + 1) := by
      rw [pow_succ]
      have h2 : M ^ j * 1 < M ^ j * M := mul_lt_mul_of_pos_left hM1 hMp
      simpa using mul_lt_mul_of_pos_left h2 ha
    have hEF : ball 0 (1 / 2) \ contactPt (a * M ^ (j + 1)) φ ⊆
        ball 0 (1 / 2) \ contactPt (a * M ^ j) φ :=
      Set.sdiff_subset_sdiff subset_rfl (contactPt_mono (mul_pos ha hMp) hlt)
    have hsize : volume (ball 0 (1 / 2) \ contactPt (a * M ^ (j + 1)) φ) ≤
        ENNReal.ofReal (1 - μ) * volume (ball (0 : ℝ⁴) (1 / 2)) := by
      refine le_trans (measure_mono ?_) hbase_ball
      have hT0 : contactPt a φ ⊆ contactPt (a * M ^ (j + 1)) φ := by
        refine contactPt_mono ha ?_
        have h1 : 1 < M ^ (j + 1) := one_lt_pow₀ hM1 (Nat.succ_ne_zero j)
        nlinarith [ha]
      exact Set.sdiff_subset_sdiff subset_rfl hT0
    have hEnl : ∀ (y : ℝ⁴) (r : ℝ), 0 < r → ball y r ⊆ ball 0 (1 / 2) →
        (ball y r ∩ contactPt (a * M ^ j) φ).Nonempty →
        ENNReal.ofReal μ * volume (ball y r) ≤
          volume (ball y r ∩ contactPt (a * M ^ (j + 1)) φ) := by
      intro y r hr hyb hne
      obtain ⟨x₁, hx₁, hx₁T⟩ := hne
      have hyc : closedBall y r ⊆ closedBall 0 (1 / 2) :=
        closedBall_subset_closedBall_of_ball_subset hr hyb
      have hy3 : closedBall y r ⊆ ball 0 (3 / 2) := by
        intro z hz
        rw [mem_ball, dist_zero_right]
        have hz1 : ‖z‖ ≤ 1 / 2 := by
          have hh := hyc hz
          rwa [mem_closedBall, dist_zero_right] at hh
        linarith
      have hbigj : 48 * ε * (a * M ^ j) * 2 ^ (2 * p + 4) ≤ c := by
        refine le_trans ?_ hbig
        have hMle : M ^ j ≤ M ^ K := pow_le_pow_right₀ hM1.le (Nat.le_of_succ_le hj)
        have haM : a * M ^ j ≤ a * M ^ K := mul_le_mul_of_nonneg_left hMle ha.le
        have h1 : 48 * ε * (a * M ^ j) ≤ 48 * ε * (a * M ^ K) :=
          mul_le_mul_of_nonneg_left haM (by positivity)
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
      have hbigj' : 3 * ε * (M * (a * M ^ j)) ≤ c / 2 := by
        have hpoweq : M * (a * M ^ j) = a * M ^ (j + 1) := by rw [pow_succ]; ring
        rw [hpoweq]
        refine le_trans ?_ hbig'
        have hMle : M ^ (j + 1) ≤ M ^ K := pow_le_pow_right₀ hM1.le hj
        have haM : a * M ^ (j + 1) ≤ a * M ^ K := mul_le_mul_of_nonneg_left hMle ha.le
        exact mul_le_mul_of_nonneg_left haM (by positivity)
      have henl := enlarge_opening (φ := φ) hφ hC hc hcq hcq' hε heq
        (a := a * M ^ j) (p := p) (r := r) (M := M) (mul_pos ha hMp) hp hr hM1 hM hpbig
        hbigj hbigj' hx₁T hx₁ hy3 hyc
      rw [show M * (a * M ^ j) = a * M ^ (j + 1) from by rw [pow_succ]; ring] at henl
      rw [MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball volume y r,
        volume_inter_closedBall y r (contactPt (a * M ^ (j + 1)) φ),
        Set.inter_comm (contactPt (a * M ^ (j + 1)) φ) (ball y r)] at henl
      exact henl
    have hmain : ∀ (y : ℝ⁴) (r : ℝ), 0 < r → ball y r ⊆ ball 0 (1 / 2) →
        ENNReal.ofReal (1 - μ) * volume (ball y r) <
          volume (ball y r ∩ (ball 0 (1 / 2) \ contactPt (a * M ^ (j + 1)) φ)) →
        ball y r ⊆ ball 0 (1 / 2) \ contactPt (a * M ^ j) φ := by
      intro y r hr hyb hstrict
      by_contra hcon
      obtain ⟨z, hz, hznF⟩ := Set.not_subset.mp hcon
      have hzT : z ∈ contactPt (a * M ^ j) φ := by
        by_contra hzt
        exact hznF ⟨hyb hz, hzt⟩
      have hEnlz := hEnl y r hr hyb ⟨z, hz, hzT⟩
      have hA : volume (ball y r \ contactPt (a * M ^ (j + 1)) φ) ≤
          ENNReal.ofReal (1 - μ) * volume (ball y r) :=
        volume_sdiff_le_ofReal measurableSet_ball hcl'.measurableSet
          (measure_ball_lt_top.ne) hμpos.le hμlt1.le hEnlz
      have hset : ball y r ∩ (ball 0 (1 / 2) \ contactPt (a * M ^ (j + 1)) φ) =
          ball y r \ contactPt (a * M ^ (j + 1)) φ := by
        ext w
        simp only [Set.mem_inter_iff, Set.mem_sdiff]
        constructor
        · rintro ⟨hw, -, hwt⟩; exact ⟨hw, hwt⟩
        · rintro ⟨hw, hwt⟩; exact ⟨hw, hyb hw, hwt⟩
      rw [hset] at hstrict
      exact absurd hA (not_le.mpr hstrict)
    have hgi := Commons.MeasureTheory.Covering.growing_ink_spots (d := 4) (R := 1 / 2)
      (by norm_num) (E := ball 0 (1 / 2) \ contactPt (a * M ^ (j + 1)) φ)
      (F := ball 0 (1 / 2) \ contactPt (a * M ^ j) φ)
      (isOpen_ball.sdiff hcl') (isOpen_ball.sdiff hcl) hEF
      (fun _ hz => hz.1) hμpos hμlt1 hmain hsize
    rwa [show (1 : ℝ) - μ / 5 ^ 4 = 1 - θ from by rw [hθdef]] at hgi
  -- the induction
  have hind : ∀ j : ℕ, j ≤ K →
      volume (ball 0 (1 / 2) \ contactPt (a * M ^ j) φ) ≤
        ENNReal.ofReal ((1 - θ) ^ j) * volume (ball 0 (1 / 2) \ contactPt a φ) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
        intro hj
        have hjle : j ≤ K := Nat.le_of_succ_le hj
        calc volume (ball 0 (1 / 2) \ contactPt (a * M ^ (j + 1)) φ)
            ≤ ENNReal.ofReal (1 - θ) * volume (ball 0 (1 / 2) \ contactPt (a * M ^ j) φ) :=
              hstep j hj
          _ ≤ ENNReal.ofReal (1 - θ) * (ENNReal.ofReal ((1 - θ) ^ j)
                * volume (ball 0 (1 / 2) \ contactPt a φ)) := mul_le_mul_right (ih hjle) _
          _ = (ENNReal.ofReal (1 - θ) * ENNReal.ofReal ((1 - θ) ^ j))
                * volume (ball 0 (1 / 2) \ contactPt a φ) := by rw [mul_assoc]
          _ = ENNReal.ofReal ((1 - θ) ^ (j + 1))
                * volume (ball 0 (1 / 2) \ contactPt a φ) := by
              rw [← ENNReal.ofReal_mul hθle, pow_succ']
  have hK := hind K le_rfl
  have hle : volume (ball 0 (1 / 2) \ contactPt a φ) ≤ volume (ball (0 : ℝ⁴) (1 / 2)) :=
    measure_mono Set.sdiff_subset
  calc volume (closedBall 0 (1 / 2) \ contactPt (a * M ^ K) φ)
      = volume (ball 0 (1 / 2) \ contactPt (a * M ^ K) φ) :=
        volume_sdiff_closedBall 0 (1 / 2) _
    _ ≤ ENNReal.ofReal ((1 - θ) ^ K) * volume (ball 0 (1 / 2) \ contactPt a φ) := hK
    _ ≤ ENNReal.ofReal ((1 - θ) ^ K) * volume (ball (0 : ℝ⁴) (1 / 2)) := mul_le_mul_right hle _
    _ = ENNReal.ofReal ((1 - θ) ^ K) * volume (closedBall (0 : ℝ⁴) (1 / 2)) := by
        rw [← MeasureTheory.Measure.addHaar_closedBall_eq_addHaar_ball volume (0 : ℝ⁴) (1 / 2)]

end

end Submission
