import Mathlib
import Submission.Work.Thom.ModelGeometry

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

open scoped Topology

noncomputable section

/-- Continuity of dropping the last coordinate (`fun_prop`-friendly, local copy). -/
@[fun_prop]
theorem continuous_strip_lp' {n : ℕ} : Continuous (Work.Morse.strip (n := n)) := by
  unfold Work.Morse.strip; fun_prop

/-- The norm of a point of `mLower n`. -/
theorem mLower_norm_eq_one {n : ℕ} {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : v ∈ mLower n) :
    ‖v‖ = 1 := by
  obtain ⟨h, -⟩ := hv
  exact h

/-- The last coordinate of a point of `mLower n` is at most `1/2`. -/
theorem mLower_ofLp_last_le {n : ℕ} {v : EuclideanSpace ℝ (Fin (n + 1))} (hv : v ∈ mLower n) :
    v.ofLp (Fin.last n) ≤ 1 / 2 := by
  obtain ⟨-, h⟩ := hv
  exact h

/-- The south pole `Work.Morse.snocLp 0 (-1)` lies in `mLower n`. -/
theorem snocLp_zero_neg_one_mem_mLower (n : ℕ) :
    Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin n)) (-1) ∈ mLower n := by
  constructor
  · have h : ‖Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin n)) (-1)‖ ^ 2 = 1 := by
      rw [Work.Morse.snocLp_norm_sq]; simp
    nlinarith [norm_nonneg (Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin n)) (-1))]
  · rw [Work.Morse.snocLp_ofLp_last]; norm_num

/-- `mLower n`, the set of unit vectors of `ℝ^{n+1}` whose last coordinate is `≤ 1/2`, is
contractible (the unit sphere minus a small open cap around the north pole: a closed disc).

Suggested proof: adapt `Work.Cohomology.sphereCapContractibleLt`
(`Submission/Work/Cohomology/sphereCapContractibleLt.lean`), which proves `ContractibleSpace` for
`{x : EuclideanSpace ℝ (Fin (m+1)) // ‖x‖ = 1 ∧ x (Fin.last m) < ε}` (`0 < ε ≤ 1`) with the
explicit contraction (writing `x = (x', z) = (Work.Morse.strip x, x (Fin.last m))`)

  `G (s, x) = (√(s·(2 − s·(1 + z))/(1 − z)) • x', s·(1 + z) − 1)`,

a nullhomotopy of the identity at the south pole `Work.Morse.snocLp 0 (-1)`.  For the *closed* cap
`z ≤ 1/2` the identical formula works: `‖x‖ = 1` gives `1 − z ≠ 0` (since `z ≤ 1/2 < 1`) and
`s·(1+z) − 1 ≤ z ≤ 1/2` throughout, so the same pointwise norm computation and endpoint
computations apply verbatim. -/
theorem mLowerContractible (n : ℕ) : ContractibleSpace ↥(mLower n) := by
  rw [contractible_iff_id_nullhomotopic]
  -- the south pole, the value of the contraction at `s = 0`
  let p : ↥(mLower n) := ⟨Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin n)) (-1),
    snocLp_zero_neg_one_mem_mLower n⟩
  -- the underlying map of the contraction, into the ambient space
  let G : unitInterval × ↥(mLower n) → EuclideanSpace ℝ (Fin (n+1)) := fun q =>
      Work.Morse.snocLp
        (Real.sqrt ((q.1:ℝ) * (2 - (q.1:ℝ) * (1 + q.2.1.ofLp (Fin.last n))) /
            (1 - q.2.1.ofLp (Fin.last n))) • Work.Morse.strip q.2.1)
        ((q.1:ℝ) * (1 + q.2.1.ofLp (Fin.last n)) - 1)
  have hden : ∀ q : unitInterval × ↥(mLower n),
      1 - q.2.1.ofLp (Fin.last n) ≠ 0 := by
    intro q; have hh : q.2.1.ofLp (Fin.last n) ≤ 1 / 2 := mLower_ofLp_last_le q.2.2
    intro hc; linarith
  have hGcont : Continuous G := by fun_prop
  -- the map lands in the closed cap
  have hGmem : ∀ q : unitInterval × ↥(mLower n),
      ‖G q‖ = 1 ∧ (G q).ofLp (Fin.last n) ≤ 1 / 2 := by
    intro q
    have hs0 : 0 ≤ (q.1:ℝ) := q.1.2.1
    have hs1 : (q.1:ℝ) ≤ 1 := q.1.2.2
    have hstrip : ‖Work.Morse.strip q.2.1‖ ^ 2 = 1 - (q.2.1.ofLp (Fin.last n)) ^ 2 := by
      have h := Work.Morse.snocLp_norm_sq (Work.Morse.strip q.2.1)
        (q.2.1.ofLp (Fin.last n))
      rw [Work.Morse.snocLp_strip] at h
      rw [mLower_norm_eq_one q.2.2] at h
      norm_num at h
      linarith
    have hz1 : q.2.1.ofLp (Fin.last n) ≤ 1 / 2 := mLower_ofLp_last_le q.2.2
    have hz_ne : (1:ℝ) - q.2.1.ofLp (Fin.last n) ≠ 0 := by linarith
    have hzge : -1 ≤ q.2.1.ofLp (Fin.last n) :=
      by nlinarith [hstrip, sq_nonneg (q.2.1.ofLp (Fin.last n)),
        norm_nonneg (Work.Morse.strip q.2.1)]
    have hrad : 0 ≤ (q.1:ℝ) * (2 - (q.1:ℝ) * (1 + q.2.1.ofLp (Fin.last n))) /
        (1 - q.2.1.ofLp (Fin.last n)) := by
      apply div_nonneg
      · apply mul_nonneg hs0; nlinarith [hz1, hs1]
      · linarith
    have hc2 : (Real.sqrt ((q.1:ℝ) * (2 - (q.1:ℝ) * (1 + q.2.1.ofLp (Fin.last n))) /
          (1 - q.2.1.ofLp (Fin.last n)))) ^ 2
        = (q.1:ℝ) * (2 - (q.1:ℝ) * (1 + q.2.1.ofLp (Fin.last n))) /
          (1 - q.2.1.ofLp (Fin.last n)) :=
      Real.sq_sqrt hrad
    constructor
    · have key : ‖G q‖ ^ 2 = 1 := by
        simp only [G]
        rw [Work.Morse.snocLp_norm_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, hc2, hstrip]
        field_simp
        ring
      nlinarith [norm_nonneg (G q), key]
    · simp only [G]
      rw [Work.Morse.snocLp_ofLp_last]
      nlinarith [hs1, hzge, hz1]
  -- the homotopy, from the constant map at the south pole to the identity
  have H : ContinuousMap.Homotopy (ContinuousMap.const (↥(mLower n)) p)
      (ContinuousMap.id (↥(mLower n))) :=
    { toContinuousMap := ⟨fun q => ⟨G q, hGmem q⟩, Continuous.subtype_mk hGcont hGmem⟩
      map_zero_left := by
        intro x
        apply Subtype.ext
        change G (0, x) = p.1
        simp only [G, p]
        simp
      map_one_left := by
        intro x
        apply Subtype.ext
        change G (1, x) = x.1
        simp only [G]
        rw [show ((1:unitInterval):ℝ) = 1 from rfl]
        rw [show (1:ℝ) * (2 - 1 * (1 + x.1.ofLp (Fin.last n))) / (1 - x.1.ofLp (Fin.last n)) = 1 by
              have hx : x.1.ofLp (Fin.last n) ≤ 1 / 2 := mLower_ofLp_last_le x.2
              have hne : (1:ℝ) - x.1.ofLp (Fin.last n) ≠ 0 := by linarith
              field_simp
              ring]
        simp only [Real.sqrt_one, one_smul]
        rw [show (1:ℝ) * (1 + x.1.ofLp (Fin.last n)) - 1 = x.1.ofLp (Fin.last n) by ring]
        exact Work.Morse.snocLp_strip x.1 }
  exact ⟨p, ⟨H.symm⟩⟩

end

end Work.Thom
