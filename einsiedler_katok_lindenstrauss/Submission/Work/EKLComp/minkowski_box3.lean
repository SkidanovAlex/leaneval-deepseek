import Mathlib
import Submission.Work.EKLComp.EucDefs

namespace Work.EKLComp

open MeasureTheory

/-- **Minkowski's box theorem in dimension 3.**  If `b` is a basis of `ℝ³` whose matrix of
coordinates has determinant `1`, and `c i > 0` with `∏ i, 2 * c i > 8`, then the box
`∏ i, [-c i, c i]` contains a nonzero point of the lattice `span_ℤ {b i}`. -/
theorem minkowski_box3 (b : Module.Basis (Fin 3) ℝ (Fin 3 → ℝ))
    (hb : Matrix.det (fun i j => b j i) = 1)
    (c : Fin 3 → ℝ) (hc : ∀ i, 0 < c i) (hbig : 8 < ∏ i, (2 * c i)) :
    ∃ x ∈ Submodule.span ℤ (Set.range (fun i => b i)), x ≠ 0 ∧ ∀ i, |x i| ≤ c i := by
  classical
  -- Determinant of the coordinate matrix of `b`.
  have hdet : (Matrix.of (b : Fin 3 → Fin 3 → ℝ)).det = 1 := by
    have h1 : (Matrix.of (b : Fin 3 → Fin 3 → ℝ)).transpose = (fun i j => b j i) := by
      ext i j; simp [Matrix.of_apply]
    rw [← Matrix.det_transpose, h1, hb]
  -- The box.
  set s : Set (Fin 3 → ℝ) := Set.Icc (fun i => -(c i)) (fun i => c i) with hs
  -- Volume of the fundamental domain of the lattice `span_ℤ {b i}` is `1`.
  have hvolF : volume (ZSpan.fundamentalDomain b) = 1 := by
    rw [ZSpan.volume_fundamentalDomain b, hdet, abs_one, ENNReal.ofReal_one]
  -- Volume of the box.
  have hprod_pos : 0 < ∏ i, (2 * c i) := Finset.prod_pos (fun i _ => by linarith [hc i])
  have hvols : volume s = ENNReal.ofReal (∏ i, (2 * c i)) := by
    rw [hs, Real.volume_Icc_pi]
    have hprod : (∏ i : Fin 3, ENNReal.ofReal ((fun i => c i) i - (fun i => -(c i)) i))
        = ∏ i : Fin 3, ENNReal.ofReal (2 * c i) := by
      refine Finset.prod_congr rfl fun i _ => ?_
      congr 1
      ring
    rw [hprod, ← ENNReal.ofReal_prod_of_nonneg (f := fun i => (2 : ℝ) * c i)]
    intro i _
    linarith [hc i]
  -- The Minkowski hypothesis.
  have hlt : volume (ZSpan.fundamentalDomain b) * 2 ^ Module.finrank ℝ (Fin 3 → ℝ) < volume s := by
    rw [hvolF, Module.finrank_fin_fun, hvols, one_mul]
    rw [show (2 : ENNReal) ^ 3 = 8 by norm_num]
    rw [show (8 : ENNReal) = ENNReal.ofReal (8 : ℝ) from (ENNReal.ofReal_natCast 8).symm]
    rw [ENNReal.ofReal_lt_ofReal_iff hprod_pos]
    exact hbig
  -- Symmetry and convexity of the box.
  have hsymm : ∀ x ∈ s, -x ∈ s := by
    intro x hx
    simp only [hs, Set.mem_Icc, Pi.le_def, Pi.neg_apply] at hx ⊢
    exact ⟨fun i => by linarith [hx.2 i], fun i => by linarith [hx.1 i]⟩
  have hconv : Convex ℝ s := by
    rw [hs]; exact convex_Icc _ _
  -- Countability of the lattice.
  have h_fund := ZSpan.isAddFundamentalDomain' b volume
  have : Countable (Submodule.span ℤ (Set.range (fun i => b i))).toAddSubgroup := by
    change Countable (Submodule.span ℤ (Set.range (fun i => b i)))
    infer_instance
  -- Minkowski's convex body theorem.
  obtain ⟨x, hxne, hxmem⟩ :=
    MeasureTheory.exists_ne_zero_mem_lattice_of_measure_mul_two_pow_lt_measure
      h_fund hsymm hconv hlt
  refine ⟨(x : Fin 3 → ℝ), ?_, ?_, ?_⟩
  · exact (Submodule.mem_toAddSubgroup _).mp x.2
  · intro h
    exact hxne (Subtype.ext h)
  · rw [hs, Set.mem_Icc, Pi.le_def] at hxmem
    intro i
    rw [abs_le]
    exact ⟨hxmem.1 i, hxmem.2 i⟩

end Work.EKLComp
