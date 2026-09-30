import Mathlib
import Submission.Work.Morse.TwoBallsBasic

set_option synthInstance.maxHeartbeats 400000

/-!
# The spherical cap `{x ∈ Sᵐ | x_m < ε}` is contractible

For `0 < ε ≤ 1`, the set of points of the unit sphere `Sᵐ ⊆ ℝᵐ⁺¹` whose last coordinate is
`< ε` is an open spherical cap around the "south pole" `(0, …, 0, -1)`, hence homeomorphic to an
open ball and contractible.

The proof exhibits the contraction explicitly.  Writing `x = (y, z)` for the decomposition given
by `Work.Morse.snocLp` / `Work.Morse.strip` (`y` the first `m` coordinates, `z` the last one),
the point of the cap at "height" `z` is scaled radially by the homotopy parameter `s ∈ [0,1]`:
the south pole `z = -1` is the centre and the boundary `z = ε` is scaled towards it.  Concretely
we use the map

  `H(s, x) = ( √(s (2 - s (1+z)) / (1-z)) • y , s (1+z) - 1 )`.

At `s = 0` this is the south pole, at `s = 1` it is `x`, and it stays on the sphere and inside the
cap throughout, so it is a homotopy from the constant map at the south pole to the identity.
-/

namespace Work.Cohomology

open scoped Topology

noncomputable section

/-- The unit sphere in `ℝᵐ⁺¹` restricted to the cap below height `ε`. -/
abbrev sphereCap (m : ℕ) (ε : ℝ) : Type :=
  {x : EuclideanSpace ℝ (Fin (m+1)) // ‖x‖ = 1 ∧ x (Fin.last m) < ε}

/-- Continuity of dropping the last coordinate (kept `fun_prop`-friendly). -/
@[fun_prop]
theorem continuous_strip_lp {n : ℕ} : Continuous (Work.Morse.strip (n := n)) := by
  unfold Work.Morse.strip; fun_prop

/-- For `0 < ε ≤ 1` the spherical cap `{x ∈ Sᵐ | x_m < ε}` is contractible. -/
theorem sphereCapContractibleLt (m : ℕ) (ε : ℝ) (h0 : 0 < ε) (h1 : ε ≤ 1) :
    ContractibleSpace {x : EuclideanSpace ℝ (Fin (m+1)) // ‖x‖ = 1 ∧ x (Fin.last m) < ε} := by
  change ContractibleSpace (sphereCap m ε)
  rw [contractible_iff_id_nullhomotopic]
  -- the south pole, the value of the contraction at `s = 0`
  let p : sphereCap m ε := ⟨Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin m)) (-1), by
    constructor
    · have h : ‖Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin m)) (-1)‖ ^ 2 = 1 := by
        rw [Work.Morse.snocLp_norm_sq]; simp
      nlinarith [norm_nonneg (Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin m)) (-1))]
    · rw [Work.Morse.snocLp_ofLp_last]; linarith⟩
  -- the underlying map of the contraction, into the ambient space
  let G : unitInterval × sphereCap m ε → EuclideanSpace ℝ (Fin (m+1)) := fun q =>
      Work.Morse.snocLp
        (Real.sqrt ((q.1:ℝ) * (2 - (q.1:ℝ) * (1 + q.2.1 (Fin.last m))) /
            (1 - q.2.1 (Fin.last m))) • Work.Morse.strip q.2.1)
        ((q.1:ℝ) * (1 + q.2.1 (Fin.last m)) - 1)
  have hden : ∀ q : unitInterval × sphereCap m ε,
      1 - q.2.1 (Fin.last m) ≠ 0 := by
    intro q; have hh : q.2.1 (Fin.last m) < ε := q.2.2.2; intro hc; linarith
  have hGcont : Continuous G := by fun_prop
  -- the map lands in the cap
  have hGmem : ∀ q : unitInterval × sphereCap m ε,
      ‖G q‖ = 1 ∧ (G q) (Fin.last m) < ε := by
    intro q
    have hs0 : 0 ≤ (q.1:ℝ) := q.1.2.1
    have hs1 : (q.1:ℝ) ≤ 1 := q.1.2.2
    have hstrip : ‖Work.Morse.strip q.2.1‖ ^ 2 = 1 - (q.2.1 (Fin.last m)) ^ 2 := by
      have h := Work.Morse.snocLp_norm_sq (Work.Morse.strip q.2.1) (q.2.1.ofLp (Fin.last m))
      rw [Work.Morse.snocLp_strip] at h
      rw [q.2.2.1] at h
      norm_num at h
      linarith
    have hz1 : q.2.1 (Fin.last m) < 1 := lt_of_lt_of_le q.2.2.2 h1
    have hz_ne : (1:ℝ) - q.2.1 (Fin.last m) ≠ 0 := by linarith
    have hzge : -1 ≤ q.2.1 (Fin.last m) :=
      by nlinarith [hstrip, sq_nonneg (q.2.1 (Fin.last m)), norm_nonneg (Work.Morse.strip q.2.1)]
    have hrad : 0 ≤ (q.1:ℝ) * (2 - (q.1:ℝ) * (1 + q.2.1 (Fin.last m))) /
        (1 - q.2.1 (Fin.last m)) := by
      apply div_nonneg
      · apply mul_nonneg hs0; nlinarith [hz1, hs1]
      · linarith
    have hc2 : (Real.sqrt ((q.1:ℝ) * (2 - (q.1:ℝ) * (1 + q.2.1 (Fin.last m))) /
          (1 - q.2.1 (Fin.last m)))) ^ 2
        = (q.1:ℝ) * (2 - (q.1:ℝ) * (1 + q.2.1 (Fin.last m))) /
          (1 - q.2.1 (Fin.last m)) :=
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
      nlinarith [hs1, hzge, q.2.2.2]
  -- the homotopy, from the constant map at the south pole to the identity
  have H : ContinuousMap.Homotopy (ContinuousMap.const (sphereCap m ε) p)
      (ContinuousMap.id (sphereCap m ε)) :=
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
        rw [show (1:ℝ) * (2 - 1 * (1 + x.1 (Fin.last m))) / (1 - x.1 (Fin.last m)) = 1 by
              have hne : (1:ℝ) - x.1 (Fin.last m) ≠ 0 := by have hx := x.2.2; linarith
              field_simp
              ring]
        simp only [Real.sqrt_one, one_smul]
        rw [show (1:ℝ) * (1 + x.1 (Fin.last m)) - 1 = x.1 (Fin.last m) by ring]
        exact Work.Morse.snocLp_strip x.1 }
  exact ⟨p, ⟨H.symm⟩⟩

end

end Work.Cohomology
