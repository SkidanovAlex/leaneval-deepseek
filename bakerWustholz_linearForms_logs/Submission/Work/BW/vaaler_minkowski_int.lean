import Mathlib
import Submission.Work.BW.vaalerVolumeAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Vaaler's sharp form of Minkowski's theorem on linear forms

For an `n × k` real matrix `A` of full column rank (`(Aᵀ A).det ≠ 0`) and `r > 0` with
`√det (Aᵀ A) ≤ r^k`, there is a nonzero integer vector `t` with `‖A t‖_∞ ≤ r`.

The proof has two ingredients:

* Vaaler's geometric inequality `Work.BW.vaalerSection`, giving the sharp lower bound for the
  `k`-dimensional volume of the tube `{x | ‖A x‖_∞ ≤ 1}`;
* Minkowski's convex body theorem for the standard lattice `ℤᵏ ⊆ ℝᵏ`, applied to the tube.
-/

set_option linter.unusedVariables false

namespace Work.BW

open MeasureTheory Module Matrix
open scoped Pointwise

/-- The closed tube `{x | ‖A x‖_∞ ≤ r}`. -/
private def tube {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) (r : ℝ) : Set (Fin k → ℝ) :=
  {x | ∀ i, |(A.mulVec x) i| ≤ r}

/-- The Gram determinant `det (Aᵀ A)` is nonnegative. -/
private lemma gram_det_nonneg {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ) :
    0 ≤ (A.transpose * A).det := by
  have h : (A.conjTranspose * A).PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  have hc : A.conjTranspose = A.transpose := by
    ext i j; simp [Matrix.conjTranspose_apply]
  rw [hc] at h
  exact h.det_nonneg

/-- **Vaaler's inequality.** The volume of the tube is at least `2^k r^k / √det (Aᵀ A)`. -/
private lemma volume_tube_ge {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (hA : (A.transpose * A).det ≠ 0) {r : ℝ} (hr : 0 < r) :
    ENNReal.ofReal (2 ^ k * r ^ k / Real.sqrt (A.transpose * A).det) ≤ volume (tube A r) := by
  have hscale : volume (tube A r) = ENNReal.ofReal (r ^ k) * volume (tube A 1) := by
    have hset : tube A r = r • tube A 1 := by
      ext x
      rw [Set.mem_smul_set]
      constructor
      · intro hx
        refine ⟨r⁻¹ • x, ?_, ?_⟩
        · intro i
          rw [Matrix.mulVec_smul]
          simp only [Pi.smul_apply, smul_eq_mul]
          rw [abs_mul, abs_of_nonneg (inv_nonneg.mpr hr.le)]
          calc r⁻¹ * |(A.mulVec x) i| ≤ r⁻¹ * r :=
                mul_le_mul_of_nonneg_left (hx i) (inv_nonneg.mpr hr.le)
            _ = 1 := inv_mul_cancel₀ hr.ne'
        · rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      · rintro ⟨y, hy, rfl⟩
        intro i
        rw [Matrix.mulVec_smul]
        simp only [Pi.smul_apply, smul_eq_mul]
        rw [abs_mul, abs_of_nonneg hr.le]
        calc r * |(A.mulVec y) i| ≤ r * 1 := mul_le_mul_of_nonneg_left (hy i) hr.le
          _ = r := mul_one r
    rw [hset, MeasureTheory.Measure.addHaar_smul_of_nonneg (μ := volume) hr.le]
    simp [Module.finrank_fintype_fun_eq_card]
  have hV : ENNReal.ofReal (2 ^ k / Real.sqrt (A.transpose * A).det) ≤ volume (tube A 1) := by
    have hvs : (2 : ℝ) ^ k / Real.sqrt (A.transpose * A).det ≤ (volume (tube A 1)).toReal := by
      simpa [tube] using vaalerSectionAux A
    calc ENNReal.ofReal (2 ^ k / Real.sqrt (A.transpose * A).det)
        ≤ ENNReal.ofReal ((volume (tube A 1)).toReal) := ENNReal.ofReal_le_ofReal hvs
      _ ≤ volume (tube A 1) := ENNReal.ofReal_toReal_le
  calc ENNReal.ofReal (2 ^ k * r ^ k / Real.sqrt (A.transpose * A).det)
      = ENNReal.ofReal (r ^ k) * ENNReal.ofReal (2 ^ k / Real.sqrt (A.transpose * A).det) := by
        rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ r ^ k)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (r ^ k) * volume (tube A 1) := by gcongr
    _ = volume (tube A r) := hscale.symm

/-- The strict form: `√det (Aᵀ A) < r^k` yields a nonzero integer vector with `‖A t‖_∞ ≤ r`. -/
private theorem strict_aux {n k : ℕ} (A : Matrix (Fin n) (Fin k) ℝ)
    (hA : (A.transpose * A).det ≠ 0) {r : ℝ} (hr : 0 < r)
    (h : Real.sqrt (A.transpose * A).det < r ^ k) :
    ∃ t : Fin k → ℤ, t ≠ 0 ∧ ∀ i, |∑ j, A i j * (t j : ℝ)| ≤ r := by
  have hdet_pos : 0 < Real.sqrt (A.transpose * A).det := by
    rw [Real.sqrt_pos]
    exact lt_of_le_of_ne' (gram_det_nonneg A) hA
  have hvol : (2 : ENNReal) ^ k < volume (tube A r) := by
    have hle := volume_tube_ge A hA hr
    have hlt : (2 : ℝ) ^ k < 2 ^ k * r ^ k / Real.sqrt (A.transpose * A).det := by
      rw [lt_div_iff₀ hdet_pos]
      exact mul_lt_mul_of_pos_left h (by positivity)
    have hof : (2 : ENNReal) ^ k = ENNReal.ofReal ((2 : ℝ) ^ k) := by
      rw [ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2)]
      simp
    rw [hof]
    refine lt_of_lt_of_le ?_ hle
    rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (by positivity : (0:ℝ) ≤ (2:ℝ)^k)]
    exact hlt
  haveI : Countable ↥((Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin k)))).toAddSubgroup) :=
    inferInstanceAs (Countable ↥(Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin k)))))
  have hFvol : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin k))) = 1 := by
    rw [ZSpan.fundamentalDomain_pi_basisFun, MeasureTheory.volume_pi_pi]
    simp [Real.volume_Ico]
  have hsymm : ∀ x ∈ tube A r, -x ∈ tube A r := by
    intro x hx i
    have h1 : (A.mulVec (-x)) i = -(A.mulVec x) i := by simp [Matrix.mulVec_neg]
    rw [h1, abs_neg]; exact hx i
  have hconv : Convex ℝ (tube A r) := by
    have heq : tube A r = (Matrix.toLin' A) ⁻¹'
        (Set.univ.pi (fun _ : Fin n => Set.Icc (-r) r)) := by
      ext x
      simp only [tube, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi,
        Matrix.toLin'_apply, Set.mem_Icc, abs_le]
    rw [heq]
    exact (convex_pi (fun i _ => convex_Icc (-r) r)).linear_preimage (Matrix.toLin' A)
  have hineq : volume (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin k)))
      * 2 ^ Module.finrank ℝ (Fin k → ℝ) < volume (tube A r) := by
    rw [hFvol, one_mul, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    exact hvol
  obtain ⟨x0, hx0ne, hx0mem⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      (ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin k)) volume) hsymm hconv hineq
  have hcoord : ∀ i, ∃ z : ℤ, (x0 : Fin k → ℝ) i = (z : ℝ) := by
    intro i
    have hmem : (x0 : Fin k → ℝ)
        ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin k))) := by simpa using x0.2
    have h :=
      (Module.Basis.mem_span_iff_repr_mem ℤ (Pi.basisFun ℝ (Fin k)) (x0 : Fin k → ℝ)).mp hmem i
    obtain ⟨z, hz⟩ := h
    refine ⟨z, ?_⟩
    rw [Pi.basisFun_repr] at hz
    simpa using hz.symm
  choose z hz using hcoord
  refine ⟨z, ?_, ?_⟩
  · intro hz0
    exact hx0ne (Subtype.ext (funext (fun i => by rw [hz i, hz0]; simp)))
  · intro i
    have hmem : ∀ i, |(A.mulVec (x0 : Fin k → ℝ)) i| ≤ r := hx0mem
    have hmv : (A.mulVec (x0 : Fin k → ℝ)) i = ∑ j, A i j * (x0 : Fin k → ℝ) j :=
      Matrix.mulVec_apply_eq_sum A _ i
    calc |∑ j, A i j * (z j : ℝ)|
        = |∑ j, A i j * (x0 : Fin k → ℝ) j| := by
          congr 1
          exact Finset.sum_congr rfl (fun j _ => by rw [← hz j])
      _ = |(A.mulVec (x0 : Fin k → ℝ)) i| := by rw [hmv]
      _ ≤ r := hmem i

theorem vaaler_minkowski_int {n k : ℕ} (hk : 1 ≤ k) (A : Matrix (Fin n) (Fin k) ℝ)
    (hA : (A.transpose * A).det ≠ 0) {r : ℝ} (hr : 0 < r)
    (h : Real.sqrt (A.transpose * A).det ≤ r ^ k) :
    ∃ t : Fin k → ℤ, t ≠ 0 ∧ ∀ i, |∑ j, A i j * (t j : ℝ)| ≤ r := by
  haveI : Nonempty (Fin k) := ⟨0, by omega⟩
  -- `n ≥ 1` because otherwise `Aᵀ A` would be the zero matrix.
  have hn : n ≠ 0 := by
    rintro rfl
    exact hA (by
      have hz : A.transpose * A = 0 := by
        ext i j
        simp [Matrix.mul_apply]
      rw [hz, Matrix.det_zero])
  -- For every natural `m` a solution exists with target `r * (1 + 1/(m+1))`.
  have hstep : ∀ m : ℕ, ∃ t : Fin k → ℤ, t ≠ 0 ∧
      ∀ i, |∑ j, A i j * (t j : ℝ)| ≤ r * (1 + (1:ℝ)/(m+1)) := by
    intro m
    have hdpos : 0 < r * (1 + (1:ℝ)/(m+1)) := by
      have : (0:ℝ) < 1 + (1:ℝ)/(m+1) := by positivity
      exact mul_pos hr this
    have hlt : Real.sqrt (A.transpose * A).det < (r * (1 + (1:ℝ)/(m+1))) ^ k := by
      have h1 : r < r * (1 + (1:ℝ)/(m+1)) := by
        have : (0:ℝ) < (1:ℝ)/(m+1) := by positivity
        nlinarith [hr]
      have h2 : r ^ k < (r * (1 + (1:ℝ)/(m+1))) ^ k :=
        pow_lt_pow_left₀ h1 hr.le (by omega)
      linarith
    exact strict_aux A hA hdpos hlt
  have hle2 : ∀ m : ℕ, r * (1 + (1:ℝ)/(m+1)) ≤ 2*r := by
    intro m
    have hm1 : (1:ℝ)/(m+1) ≤ 1 := by
      push_cast
      rw [div_le_iff₀ (by positivity : (0:ℝ) < ((m:ℝ)+1)), one_mul]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)
    nlinarith [hr]
  -- The finite set of admissible vectors with target `2 r`.
  set W : Set (Fin k → ℤ) := {t | t ≠ 0 ∧ ∀ i, |∑ j, A i j * (t j : ℝ)| ≤ 2*r} with hWdef
  have hWmem : ∀ t : Fin k → ℤ, t ∈ W ↔ t ≠ 0 ∧ ∀ i, |∑ j, A i j * (t j : ℝ)| ≤ 2*r := by
    intro t; simp [hWdef]
  have hWne : W.Nonempty := by
    obtain ⟨t0, ht0ne, ht0le⟩ := hstep 0
    exact ⟨t0, (hWmem t0).mpr ⟨ht0ne, fun i => le_trans (ht0le i) (hle2 0)⟩⟩
  have hWfin : W.Finite := by
    have hφinj : Function.Injective (fun t : Fin k → ℤ => (fun j => (t j : ℝ))) := by
      intro a b hab
      funext j
      have h := congrFun hab j
      change ((a j : ℤ) : ℝ) = ((b j : ℤ) : ℝ) at h
      exact_mod_cast h
    refine Set.Finite.of_finite_image ?_ (fun a _ b _ hab => hφinj hab)
    have hL : Set.Finite ((tube A (2*r)) ∩
        (Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin k))) : Set (Fin k → ℝ))) := by
      have hc : IsCompact (tube A (2*r)) := by
        have hpre : tube A (2*r) = (Matrix.toLin' A) ⁻¹'
            (Set.univ.pi (fun _ : Fin n => Set.Icc (-(2*r)) (2*r))) := by
          ext x
          simp only [tube, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_univ_pi,
            Matrix.toLin'_apply, Set.mem_Icc, abs_le]
        rw [hpre]
        refine (LinearMap.isClosedEmbedding_of_injective ?_).isCompact_preimage
          (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc))
        rw [LinearMap.ker_eq_bot']
        intro x hx
        have hx' : A.mulVec x = 0 := by simpa [Matrix.toLin'_apply] using hx
        have h2 : (A.transpose * A).mulVec x = 0 := by
          have h1 : (A.transpose * A).mulVec x = A.transpose.mulVec (A.mulVec x) :=
            (Matrix.mulVec_mulVec x A.transpose A).symm
          rw [h1, hx', Matrix.mulVec_zero]
        exact Matrix.mulVec_injective_of_det_ne_zero hA (by rw [h2, Matrix.mulVec_zero])
      exact ZSpan.setFinite_inter (Pi.basisFun ℝ (Fin k)) hc.isBounded
    refine Set.Finite.subset hL ?_
    rintro x ⟨t, htW, rfl⟩
    have htW' := (hWmem t).mp htW
    refine ⟨?_, ?_⟩
    · intro i
      have h1 : (A.mulVec (fun j => (t j : ℝ))) i = ∑ j, A i j * (t j : ℝ) :=
        Matrix.mulVec_apply_eq_sum A _ i
      rw [h1]; exact htW'.2 i
    · change (fun j => (t j : ℝ)) ∈ Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin k)))
      rw [Module.Basis.mem_span_iff_repr_mem]
      intro i
      exact ⟨t i, by rw [Pi.basisFun_repr]; simp⟩
  haveI : Nonempty (Fin n) := ⟨0, Nat.pos_of_ne_zero hn⟩
  -- The `ℓ^∞` norm of `A t`.
  let f : (Fin k → ℤ) → ℝ := fun t =>
    (Finset.univ.image (fun i => |∑ j, A i j * (t j : ℝ)|)).max'
      (Finset.image_nonempty.mpr Finset.univ_nonempty)
  have hf_lower : ∀ (t : Fin k → ℤ) (i : Fin n), |∑ j, A i j * (t j : ℝ)| ≤ f t := by
    intro t i
    exact Finset.le_max' (Finset.univ.image (fun i => |∑ j, A i j * (t j : ℝ)|))
      (|∑ j, A i j * (t j : ℝ)|)
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hf_le : ∀ (t : Fin k → ℤ) (c : ℝ),
      (∀ i, |∑ j, A i j * (t j : ℝ)| ≤ c) → f t ≤ c := by
    intro t c hc
    exact Finset.max'_le _ _ _ (fun y hy => by
      rw [Finset.mem_image] at hy
      obtain ⟨i, _, rfl⟩ := hy
      exact hc i)
  obtain ⟨ts, hts_mem, hts_min⟩ :=
    Finset.exists_min_image hWfin.toFinset f (hWfin.toFinset_nonempty.mpr hWne)
  have hts_W : ts ∈ W := (hWfin.mem_toFinset).mp hts_mem
  have hbound : f ts ≤ r := by
    by_contra hc
    push_neg at hc
    have hδpos : 0 < f ts - r := by linarith
    obtain ⟨M, hM⟩ := exists_nat_gt (r / (f ts - r))
    have hsmall : r * (1 + (1:ℝ)/(M+1)) < f ts := by
      push_cast
      have hps : (0:ℝ) < (M:ℝ)+1 := by positivity
      have hMr : r / (f ts - r) < (M:ℝ)+1 := by linarith [hM]
      rw [div_lt_iff₀ hδpos] at hMr
      have hlt : r / ((M:ℝ)+1) < f ts - r := by
        rw [div_lt_iff₀ hps]
        nlinarith [hMr]
      have heq : r * (1 + (1:ℝ)/((M:ℝ)+1)) = r + r/((M:ℝ)+1) := by ring
      rw [heq]; linarith
    obtain ⟨tm, htmne, htmle⟩ := hstep M
    have htmW : tm ∈ W :=
      (hWmem tm).mpr ⟨htmne, fun i => le_trans (htmle i) (hle2 M)⟩
    have h1 : f ts ≤ f tm := hts_min tm (hWfin.mem_toFinset.mpr htmW)
    have h2 : f tm ≤ r * (1 + (1:ℝ)/(M+1)) := hf_le tm _ htmle
    linarith
  exact ⟨ts, hts_W.1, fun i => le_trans (hf_lower ts i) hbound⟩

end Work.BW
