import Mathlib
import Submission.Work.HP.ArchDefs
import Submission.Work.HP.evaldefs
import Submission.Work.HP.veronese_first

/-!
# `Work.HP.eval_bounds`

The elementary analytic facts about the forms `f_a = formEvalR d n a`, their gradients
`gradVec d n a` and their second-order Taylor expansion, on the Euclidean balls of radius
`1` and `2`, together with the homogeneity of `f_a`, the closedness of the set of `a` with a
real zero on the unit sphere, and the implication "real zero ⟹ unit-sphere zero".

The monomial-level input is `Work.HP.veronese_first` (`Submission/Work/HP/veronese_first.lean`)
and `Work.HP.veronese_taylor2` (`Submission/Work/HP/veronese_taylor2.lean`); the elementary
`rNorm` API and the homogeneity of `formEvalR` are in `Submission/Work/HP/evaldefs.lean`.
-/

set_option autoImplicit false

namespace Work.HP

open MeasureTheory MvPolynomial

/-- `dotR` against the gradient, expanded over the monomial basis. -/
lemma dotR_gradVec (d n : ℕ) (a : Mon d n → ℝ) (x w : Fin (n + 1) → ℝ) :
    dotR (gradVec d n a x) w = ∑ m : Mon d n, a m * ∑ j, dm d n m x j * (w j) := by
  have h1 : dotR (gradVec d n a x) w
      = ∑ j, (∑ m : Mon d n, a m * dm d n m x j) * w j := by
    simp only [dotR, gradVec, gradF_eq_sum_dm]
  rw [h1]
  have h2 : ∀ j : Fin (n + 1), (∑ m : Mon d n, a m * dm d n m x j) * w j
      = ∑ m : Mon d n, (a m * dm d n m x j) * w j := fun j => Finset.sum_mul _ _ _
  simp only [h2]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

/-- The difference of the monomial evaluations, expanded over the monomial basis. -/
lemma formEvalR_sub (d n : ℕ) (a : Mon d n → ℝ) (x y : Fin (n + 1) → ℝ) :
    formEvalR d n a y - formEvalR d n a x
      = ∑ m : Mon d n, a m * (veronese d n y m - veronese d n x m) := by
  rw [formEvalR, formEvalR, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun m _ => by ring)

/-- The difference of two gradients, coordinatewise over the monomial basis. -/
lemma gradVec_sub_apply (d n : ℕ) (a : Mon d n → ℝ) (x y : Fin (n + 1) → ℝ)
    (j : Fin (n + 1)) :
    (gradVec d n a y - gradVec d n a x) j
      = ∑ m : Mon d n, a m * (dm d n m y j - dm d n m x j) := by
  rw [Pi.sub_apply, gradVec, gradVec, gradF_eq_sum_dm, gradF_eq_sum_dm,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun m _ => by ring)


/-- The set of coefficient vectors admitting a zero on the Euclidean unit sphere is closed:
it is the projection of a closed subset of a product whose second factor is compact. -/
lemma isClosed_IPt_aux (d n : ℕ) : IsClosed {a : Mon d n → ℝ | IPt d n a} := by
  classical
  let K : Set (Fin (n + 1) → ℝ) := {x | rNorm x = 1}
  have hKclosed : IsClosed K := isClosed_eq (by unfold rNorm; fun_prop) continuous_const
  have hsub : K ⊆ Metric.closedBall (0 : Fin (n + 1) → ℝ) 1 := by
    intro x hx
    change rNorm x = 1 at hx
    rw [Metric.mem_closedBall, dist_zero_right]
    refine (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr (fun i => ?_)
    exact (abs_coord_le_rNorm x i).trans (le_of_eq hx)
  have hKcpt : IsCompact K :=
    (isCompact_closedBall (0 : Fin (n + 1) → ℝ) 1).of_isClosed_subset hKclosed hsub
  have hKcptspace : CompactSpace K := isCompact_iff_compactSpace.mp hKcpt
  have hmono : ∀ m : Mon d n, Continuous (fun p : (Mon d n → ℝ) × K =>
      veronese d n (p.2 : Fin (n + 1) → ℝ) m) := by
    intro m
    unfold veronese
    exact continuous_finsetProd _ (fun i _ =>
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)).pow _)
  have hcont : Continuous (fun p : (Mon d n → ℝ) × K =>
      formEvalR d n p.1 (p.2 : Fin (n + 1) → ℝ)) := by
    simp only [formEvalR]
    exact continuous_finsetSum _ (fun m _ =>
      ((continuous_apply m).comp continuous_fst).mul (hmono m))
  have hTclosed : IsClosed
      {p : (Mon d n → ℝ) × K | formEvalR d n p.1 (p.2 : Fin (n + 1) → ℝ) = 0} :=
    isClosed_eq hcont continuous_const
  have hproj : IsClosed (Prod.fst ''
      {p : (Mon d n → ℝ) × K | formEvalR d n p.1 (p.2 : Fin (n + 1) → ℝ) = 0}) :=
    isClosedMap_fst_of_compactSpace _ hTclosed
  convert hproj using 1
  ext a
  constructor
  · rintro ⟨x, hx1, hx0⟩
    exact ⟨(a, ⟨x, hx1⟩), hx0, rfl⟩
  · rintro ⟨p, hp, heq⟩
    refine ⟨(p.2 : Fin (n + 1) → ℝ), p.2.2, ?_⟩
    rw [← heq]
    exact hp

/-- A nonzero real zero of `f_a` can be scaled to the Euclidean unit sphere. -/
lemma realSol_IPt_aux (d n : ℕ) (a : Mon d n → ℤ) : RealSol d n a → IPt d n (toR a) := by
  rintro ⟨x, hxne, hx0⟩
  have hpos : 0 < rNorm x := by
    rcases lt_or_eq_of_le (rNorm_nonneg x) with h | h
    · exact h
    · exact absurd (rNorm_eq_zero.mp h.symm) hxne
  refine ⟨(rNorm x)⁻¹ • x, ?_, ?_⟩
  · rw [rNorm_smul_of_pos _ _ (inv_pos.mpr hpos), inv_mul_cancel₀ (ne_of_gt hpos)]
  · rw [formEvalR_homogeneous, ← formEval_eq_formEvalR, hx0, mul_zero]


/-- Derivative of a finite product of functions of one variable (lambda form). -/
lemma hasDerivAt_prod_fun {ι : Type*} [Fintype ι] [DecidableEq ι] (g : ι → ℝ → ℝ) (g' : ι → ℝ)
    (t : ℝ) (h : ∀ i ∈ (Finset.univ : Finset ι), HasDerivAt (g i) (g' i) t) :
    HasDerivAt (fun s : ℝ => ∏ i, g i s)
      (∑ i, (∏ j ∈ Finset.univ.erase i, g j t) * g' i) t := by
  have hp := HasDerivAt.finsetProd (u := Finset.univ) (f := g) (f' := g') h
  convert hp using 1
  ext s
  rw [Finset.prod_apply]

/-- The derivative of a monomial along a straight line:
`d/dt (ν_m(x + t·h)) = ∇ν_m(x + t·h)·h`. -/
lemma hasDerivAt_veronese_along (d n : ℕ) (m : Mon d n) (x h : Fin (n + 1) → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => veronese d n (x + s • h) m)
      (∑ j, dm d n m (x + t • h) j * (h j)) t := by
  have hder : ∀ i : Fin (n + 1), HasDerivAt (fun s : ℝ => (x i + s * h i) ^ ((m.1 i : ℕ)))
      ((m.1 i : ℝ) * (x i + t * h i) ^ ((m.1 i : ℕ) - 1) * h i) t := by
    intro i
    have h1 : HasDerivAt (fun s : ℝ => x i + s * h i) (h i) t := by
      simpa using ((hasDerivAt_id t).mul_const (h i)).const_add (x i)
    convert h1.pow ((m.1 i : ℕ)) using 1
  have hp := hasDerivAt_prod_fun (g := fun i s => (x i + s * h i) ^ ((m.1 i : ℕ)))
    (g' := fun i => (m.1 i : ℝ) * (x i + t * h i) ^ ((m.1 i : ℕ) - 1) * h i) t
    (fun i _ => hder i)
  have hval : (∑ i : Fin (n + 1),
        (∏ j ∈ Finset.univ.erase i, (x j + t * h j) ^ ((m.1 j : ℕ))) *
          ((m.1 i : ℝ) * (x i + t * h i) ^ ((m.1 i : ℕ) - 1) * h i))
      = ∑ j, dm d n m (x + t • h) j * (h j) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [dm]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hfun : (fun s : ℝ => veronese d n (x + s • h) m)
      = fun s : ℝ => ∏ i : Fin (n + 1), (x i + s * h i) ^ ((m.1 i : ℕ)) := by
    funext s
    simp only [veronese, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hfun, ← hval]
  exact hp

/-- Second-order Taylor bound for a single monomial on the ball of radius `2`:
`|ν_m(y) - ν_m(x) - ∇ν_m(x)·(y - x)| ≤ (n+1)·2^{4d+4}·‖y - x‖²`. -/
lemma veronese_taylor2_aux (d n : ℕ) (m : Mon d n) (x y : Fin (n + 1) → ℝ)
    (hx : rNorm x ≤ 2) (hy : rNorm y ≤ 2) :
    |veronese d n y m - veronese d n x m - ∑ j, dm d n m x j * (y j - x j)|
      ≤ ((n + 1 : ℝ) * 2 ^ (4 * d + 4)) * rNorm (y - x) ^ 2 := by
  classical
  obtain ⟨-, -, -, hv4⟩ := veronese_first d n
  set h : Fin (n + 1) → ℝ := y - x with hh
  set C : ℝ := (n + 1 : ℝ) * 2 ^ (3 * d) * rNorm h ^ 2 with hCdef
  -- (A) the segment from `x` to `y` stays in the ball of radius `2`
  have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → rNorm (x + t • h) ≤ 2 := by
    intro t ht0 ht1
    have hsplit : x + t • h = (1 - t) • x + t • y := by
      funext i
      simp only [hh, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hsplit]
    calc rNorm ((1 - t) • x + t • y)
        ≤ rNorm ((1 - t) • x) + rNorm (t • y) := rNorm_add_le _ _
      _ = (1 - t) * rNorm x + t * rNorm y := by
            rw [rNorm_smul', rNorm_smul', abs_of_nonneg (by linarith), abs_of_nonneg ht0]
      _ ≤ 2 := by nlinarith
  -- (B) the derivative is Lipschitz with constant `C` along the segment
  have hDbound : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      |(∑ j, dm d n m (x + t • h) j * (h j)) - (∑ j, dm d n m x j * (h j))| ≤ C := by
    intro t ht0 ht1
    have hz2 : rNorm (x + t • h) ≤ 2 := hseg t ht0 ht1
    have hcoord : ∀ j : Fin (n + 1),
        |dm d n m (x + t • h) j - dm d n m x j| ≤ 2 ^ (3 * d) * (t * rNorm h) := by
      intro j
      have h1 := hv4 m x (x + t • h) j hx hz2
      have h2 : (x + t • h) - x = t • h := by
        funext i
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [h2, rNorm_smul', abs_of_nonneg ht0] at h1
      exact h1
    have hrn : rNorm (fun j : Fin (n + 1) => dm d n m (x + t • h) j - dm d n m x j)
        ≤ (n + 1 : ℝ) * (2 ^ (3 * d) * (t * rNorm h)) := by
      have hcard := rNorm_le_card_mul
        (fun j : Fin (n + 1) => dm d n m (x + t • h) j - dm d n m x j) hcoord
      simpa using hcard
    have hdiff : (∑ j, dm d n m (x + t • h) j * (h j)) - (∑ j, dm d n m x j * (h j))
        = dotR (fun j : Fin (n + 1) => dm d n m (x + t • h) j - dm d n m x j) h := by
      rw [dotR, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    rw [hdiff]
    have hR : 0 ≤ rNorm h := rNorm_nonneg h
    have hA : 0 ≤ (n + 1 : ℝ) := by positivity
    have hB : (0 : ℝ) ≤ 2 ^ (3 * d : ℕ) := by positivity
    have hδ : 0 ≤ (n + 1 : ℝ) * (2 ^ (3 * d) * (t * rNorm h)) :=
      mul_nonneg hA (mul_nonneg hB (mul_nonneg ht0 hR))
    refine (abs_dotR_le _ _).trans ?_
    refine (mul_le_mul hrn le_rfl hR hδ).trans ?_
    calc (n + 1 : ℝ) * (2 ^ (3 * d) * (t * rNorm h)) * rNorm h
        ≤ (n + 1 : ℝ) * (2 ^ (3 * d) * rNorm h) * rNorm h := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hA) hR
          exact mul_le_mul_of_nonneg_left (by nlinarith [hR, ht1]) hB
      _ = C := by rw [hCdef]; ring
  -- (C) the mean value inequality on `t ↦ ν_m(x + t·h) - t·S`
  set S : ℝ := ∑ j, dm d n m x j * (h j) with hSdef
  have hS_eq : S = ∑ j, dm d n m x j * (y j - x j) := by
    rw [hSdef]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    simp only [hh, Pi.sub_apply]
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => veronese d n (x + s • h) m - s * S)
      ((∑ j, dm d n m (x + t • h) j * (h j)) - S) t := by
    intro t
    have h1 := hasDerivAt_veronese_along d n m x h t
    have h2 : HasDerivAt (fun s : ℝ => s * S) S t := by
      simpa using (hasDerivAt_id t).mul_const S
    have h3 := h1.sub h2
    convert h3 using 1
  have hmv : |veronese d n (x + (1 : ℝ) • h) m - 1 * S
      - (veronese d n (x + (0 : ℝ) • h) m - 0 * S)| ≤ C := by
    have hmvt := norm_image_sub_le_of_norm_deriv_le_segment_01'
      (f := fun s : ℝ => veronese d n (x + s • h) m - s * S)
      (f' := fun t => (∑ j, dm d n m (x + t • h) j * (h j)) - S) (C := C)
      (fun t _ => (hderiv t).hasDerivWithinAt)
      (fun t ht => by
        rw [Real.norm_eq_abs]
        exact hDbound t ht.1 (le_of_lt ht.2))
    simpa [Real.norm_eq_abs] using hmvt
  have hx1 : x + (1 : ℝ) • h = y := by
    funext i
    simp only [hh, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hx0 : x + (0 : ℝ) • h = x := by
    funext i
    simp
  rw [hx1, hx0] at hmv
  simp only [one_mul, zero_mul, sub_zero] at hmv
  have hfinal : |veronese d n y m - veronese d n x m - S| ≤ C := by
    convert hmv using 1
    ring_nf
  have hmain : |veronese d n y m - veronese d n x m - ∑ j, dm d n m x j * (y j - x j)| ≤ C := by
    rw [← hS_eq]
    exact hfinal
  refine hmain.trans ?_
  rw [hCdef]
  have hR2 : 0 ≤ rNorm h ^ 2 := by positivity
  have hA : 0 ≤ (n + 1 : ℝ) := by positivity
  have hpow : (2 : ℝ) ^ (3 * d) ≤ 2 ^ (4 * d + 4) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  calc (n + 1 : ℝ) * 2 ^ (3 * d) * rNorm h ^ 2
      ≤ (n + 1 : ℝ) * 2 ^ (4 * d + 4) * rNorm h ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hA) hR2
    _ = (n + 1 : ℝ) * 2 ^ (4 * d + 4) * rNorm (y - x) ^ 2 := by rw [hh]

theorem eval_bounds (d n : ℕ) (hd : 2 ≤ d) (hn : 3 ≤ n) :
    (∃ C, 0 < C ∧ ∀ (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ), rNorm x ≤ 2 →
        |formEvalR d n a x| ≤ C * rNorm a) ∧
    (∃ C, 0 < C ∧ ∀ (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ), rNorm x ≤ 1 →
        rNorm (gradVec d n a x) ≤ C * rNorm a) ∧
    (∃ C, 0 < C ∧ ∀ (a : Mon d n → ℝ) (x y : Fin (n + 1) → ℝ), rNorm x ≤ 2 → rNorm y ≤ 2 →
        |formEvalR d n a y - formEvalR d n a x| ≤ C * rNorm a * rNorm (y - x)) ∧
    (∃ C, 0 < C ∧ ∀ (a : Mon d n → ℝ) (x y : Fin (n + 1) → ℝ), rNorm x ≤ 2 → rNorm y ≤ 2 →
        rNorm (gradVec d n a y - gradVec d n a x) ≤ C * rNorm a * rNorm (y - x)) ∧
    (∃ C, 0 < C ∧ ∀ (a : Mon d n → ℝ) (x y : Fin (n + 1) → ℝ), rNorm x ≤ 2 → rNorm y ≤ 2 →
        |formEvalR d n a y - formEvalR d n a x - dotR (gradVec d n a x) (y - x)|
          ≤ C * rNorm a * (rNorm (y - x)) ^ 2) ∧
    (∀ (a : Mon d n → ℝ) (x : Fin (n + 1) → ℝ) (t : ℝ),
        formEvalR d n a (t • x) = t ^ d * formEvalR d n a x) ∧
    IsClosed {a : Mon d n → ℝ | IPt d n a} ∧
    (∀ a : Mon d n → ℤ, RealSol d n a → IPt d n (toR a)) := by
  classical
  obtain ⟨hv1, hv2, hv3, hv4⟩ := veronese_first d n
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (1) |f_a(x)| ≤ C ‖a‖ for ‖x‖ ≤ 2
    refine ⟨((NN d n : ℝ) + 1) * 2 ^ d, by positivity, ?_⟩
    intro a x hx
    have hν : ∀ m : Mon d n, |veronese d n x m| ≤ 2 ^ d := fun m => hv1 m x hx
    have hsum : |formEvalR d n a x| ≤ (NN d n : ℝ) * 2 ^ d * rNorm a := by
      calc |formEvalR d n a x| = |∑ m : Mon d n, a m * veronese d n x m| := by
            rw [formEvalR]
        _ ≤ ∑ m : Mon d n, |a m * veronese d n x m| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _m : Mon d n, rNorm a * 2 ^ d := by
              refine Finset.sum_le_sum (fun m _ => ?_)
              rw [abs_mul]
              exact mul_le_mul (abs_coeff_le_rNorm a m) (hν m) (by positivity) (rNorm_nonneg a)
        _ = (NN d n : ℝ) * 2 ^ d * rNorm a := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              ring
    calc |formEvalR d n a x| ≤ (NN d n : ℝ) * 2 ^ d * rNorm a := hsum
      _ ≤ ((NN d n : ℝ) + 1) * 2 ^ d * rNorm a := by
            have h2 : (0 : ℝ) ≤ 2 ^ d * rNorm a :=
              mul_nonneg (by positivity) (rNorm_nonneg a)
            nlinarith [h2]
  · -- (2) ‖∇f_a(x)‖ ≤ C ‖a‖ for ‖x‖ ≤ 1
    refine ⟨(n + 1 : ℝ) * ((NN d n : ℝ) * ((d : ℝ) * 2 ^ (d - 1))) + 1, ?_, ?_⟩
    · have h2 : (0 : ℝ) ≤ (NN d n : ℝ) := Nat.cast_nonneg _
      have h3 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      have h5 : 0 ≤ (n + 1 : ℝ) * ((NN d n : ℝ) * ((d : ℝ) * 2 ^ (d - 1))) :=
        mul_nonneg (by positivity) (mul_nonneg h2 (mul_nonneg h3 (by positivity)))
      linarith
    intro a x hx
    have hx2 : rNorm x ≤ 2 := le_trans hx (by norm_num)
    have hdm : ∀ (m : Mon d n) (j : Fin (n + 1)),
        |dm d n m x j| ≤ (d : ℝ) * 2 ^ (d - 1) := fun m j => hv2 m x j hx2
    have hcoord : ∀ j : Fin (n + 1),
        |gradVec d n a x j| ≤ (NN d n : ℝ) * ((d : ℝ) * 2 ^ (d - 1)) * rNorm a := by
      intro j
      have h : |gradVec d n a x j| ≤ ∑ _m : Mon d n, rNorm a * ((d : ℝ) * 2 ^ (d - 1)) := by
        rw [gradVec, gradF_eq_sum_dm]
        calc |∑ m : Mon d n, a m * dm d n m x j|
            ≤ ∑ m : Mon d n, |a m * dm d n m x j| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _m : Mon d n, rNorm a * ((d : ℝ) * 2 ^ (d - 1)) := by
                refine Finset.sum_le_sum (fun m _ => ?_)
                rw [abs_mul]
                exact mul_le_mul (abs_coeff_le_rNorm a m) (hdm m j) (by positivity) (rNorm_nonneg a)
      calc |gradVec d n a x j| ≤ ∑ _m : Mon d n, rNorm a * ((d : ℝ) * 2 ^ (d - 1)) := h
        _ = (NN d n : ℝ) * ((d : ℝ) * 2 ^ (d - 1)) * rNorm a := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              ring
    calc rNorm (gradVec d n a x)
        ≤ (Fintype.card (Fin (n + 1)) : ℝ)
            * ((NN d n : ℝ) * ((d : ℝ) * 2 ^ (d - 1)) * rNorm a) :=
          rNorm_le_card_mul _ hcoord
      _ = (n + 1 : ℝ) * ((NN d n : ℝ) * ((d : ℝ) * 2 ^ (d - 1))) * rNorm a := by
            rw [Fintype.card_fin]; push_cast; ring
      _ ≤ ((n + 1 : ℝ) * ((NN d n : ℝ) * ((d : ℝ) * 2 ^ (d - 1))) + 1) * rNorm a := by
            nlinarith [rNorm_nonneg a]
  · -- (3) |f_a(y) - f_a(x)| ≤ C ‖a‖ ‖y - x‖ for ‖x‖, ‖y‖ ≤ 2
    refine ⟨(NN d n : ℝ) * 2 ^ (3 * d) + 1, by positivity, ?_⟩
    intro a x y hx hy
    have hν : ∀ m : Mon d n,
        |veronese d n y m - veronese d n x m| ≤ 2 ^ (3 * d) * rNorm (y - x) :=
      fun m => hv3 m x y hx hy
    rw [formEvalR_sub]
    calc |∑ m : Mon d n, a m * (veronese d n y m - veronese d n x m)|
        ≤ ∑ _m : Mon d n, rNorm a * (2 ^ (3 * d) * rNorm (y - x)) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun m _ => ?_))
          rw [abs_mul]
          exact mul_le_mul (abs_coeff_le_rNorm a m) (hν m) (by positivity) (rNorm_nonneg a)
      _ = (NN d n : ℝ) * (2 ^ (3 * d) * rNorm (y - x)) * rNorm a := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
      _ ≤ ((NN d n : ℝ) * 2 ^ (3 * d) + 1) * rNorm a * rNorm (y - x) := by
            have h1 : 0 ≤ rNorm a * rNorm (y - x) :=
              mul_nonneg (rNorm_nonneg a) (rNorm_nonneg (y - x))
            nlinarith [h1]
  · -- (4) ‖∇f_a(y) - ∇f_a(x)‖ ≤ C ‖a‖ ‖y - x‖ for ‖x‖, ‖y‖ ≤ 2
    refine ⟨(n + 1 : ℝ) * ((NN d n : ℝ) * 2 ^ (3 * d)) + 1, by positivity, ?_⟩
    intro a x y hx hy
    have hdm : ∀ (m : Mon d n) (j : Fin (n + 1)),
        |dm d n m y j - dm d n m x j| ≤ 2 ^ (3 * d) * rNorm (y - x) :=
      fun m j => hv4 m x y j hx hy
    have hcoord : ∀ j : Fin (n + 1),
        |(gradVec d n a y - gradVec d n a x) j|
          ≤ (NN d n : ℝ) * (2 ^ (3 * d) * rNorm (y - x)) * rNorm a := by
      intro j
      rw [gradVec_sub_apply]
      calc |∑ m : Mon d n, a m * (dm d n m y j - dm d n m x j)|
          ≤ ∑ m : Mon d n, |a m * (dm d n m y j - dm d n m x j)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _m : Mon d n, rNorm a * (2 ^ (3 * d) * rNorm (y - x)) := by
              refine Finset.sum_le_sum (fun m _ => ?_)
              rw [abs_mul]
              exact mul_le_mul (abs_coeff_le_rNorm a m) (hdm m j) (by positivity) (rNorm_nonneg a)
        _ = (NN d n : ℝ) * (2 ^ (3 * d) * rNorm (y - x)) * rNorm a := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
              ring
    calc rNorm (gradVec d n a y - gradVec d n a x)
        ≤ (Fintype.card (Fin (n + 1)) : ℝ)
            * ((NN d n : ℝ) * (2 ^ (3 * d) * rNorm (y - x)) * rNorm a) :=
          rNorm_le_card_mul _ hcoord
      _ = (n + 1 : ℝ) * ((NN d n : ℝ) * 2 ^ (3 * d)) * rNorm a * rNorm (y - x) := by
            rw [Fintype.card_fin]; push_cast; ring
      _ ≤ ((n + 1 : ℝ) * ((NN d n : ℝ) * 2 ^ (3 * d)) + 1) * rNorm a * rNorm (y - x) := by
            have h1 : 0 ≤ rNorm a * rNorm (y - x) :=
              mul_nonneg (rNorm_nonneg a) (rNorm_nonneg (y - x))
            nlinarith [h1]
  · -- (5) second-order Taylor bound
    refine ⟨(NN d n : ℝ) * ((n + 1 : ℝ) * 2 ^ (4 * d + 4)) + 1, by positivity, ?_⟩
    intro a x y hx hy
    have hsub : formEvalR d n a y - formEvalR d n a x - dotR (gradVec d n a x) (y - x)
        = ∑ m : Mon d n, a m * (veronese d n y m - veronese d n x m
            - ∑ j, dm d n m x j * ((y - x) j)) := by
      rw [formEvalR_sub, dotR_gradVec, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun m _ => by ring)
    rw [hsub]
    calc |∑ m : Mon d n, a m * (veronese d n y m - veronese d n x m
            - ∑ j, dm d n m x j * ((y - x) j))|
        ≤ ∑ _m : Mon d n,
            rNorm a * (((n + 1 : ℝ) * 2 ^ (4 * d + 4)) * rNorm (y - x) ^ 2) := by
          refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun m _ => ?_))
          rw [abs_mul]
          exact mul_le_mul (abs_coeff_le_rNorm a m) (veronese_taylor2_aux d n m x y hx hy)
            (by positivity) (rNorm_nonneg a)
      _ = (NN d n : ℝ) * (((n + 1 : ℝ) * 2 ^ (4 * d + 4)) * rNorm (y - x) ^ 2) * rNorm a := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          ring
      _ ≤ ((NN d n : ℝ) * ((n + 1 : ℝ) * 2 ^ (4 * d + 4)) + 1) * rNorm a
            * rNorm (y - x) ^ 2 := by
          have h1 : 0 ≤ rNorm a * rNorm (y - x) ^ 2 :=
            mul_nonneg (rNorm_nonneg a) (by positivity)
          nlinarith [h1]
  · -- (6) homogeneity
    intro a x t
    exact formEvalR_homogeneous d n a x t
  · -- (7) closedness of the set of forms with a real zero on the unit sphere
    exact isClosed_IPt_aux d n
  · -- (8) a real zero can be scaled to the unit sphere
    exact realSol_IPt_aux d n

end Work.HP
