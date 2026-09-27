import Mathlib
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.FP.lindDefs
import Submission.Work.KT.FP.wPen_admissible

/-!
# `Work.KT.FP.lindAt_admissible`

For a compact Hausdorff space `X`, a Laurent matrix `P` of degree at most `m` over `C(X, ℂ)` whose
associated unit `P.map (laurentMap X)` on `X × S¹` is invertible, the linearised pencil
`z ↦ z • linAf X n m + linBf X n m P` is invertible on some closed annulus `ρ ≤ ‖z‖ ≤ 1` with
`0 < ρ ≤ 1`.

The proof is the bridge from Laurent matrices to polynomial coefficient sequences
(`Work.KT.FP.polyOf_coeffSeq_map_eq`): the `W`-polynomial of the coefficient sequence
`coeffSeq X n m P`, evaluated at a point of `X × S¹`, is `zᵐ` times the value of `P.map
(laurentMap X)` — the degree bound `hb` makes the truncated coefficient sum equal the full Laurent
expansion.  Hence the pointwise invertibility hypothesis of `wPen_admissible` is available, and
`wPen_admissible` supplies the annulus for the `W` pencil `wPenAf`/`wPenBf`, which is `linAf`/
`linBf` by definition.
-/

namespace Work.KT.FP

open Matrix

theorem lindAt_admissible (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n m : ℕ) (P : Matrix (Fin n) (Fin n) (LaurentPolynomial C(X, ℂ)))
    (hb : ∀ (i j : Fin n) (k : ℤ), (m : ℤ) < k ∨ k < -(m : ℤ) → (P i j).coeff k = 0)
    (hunit : IsUnit (P.map (Work.KT.laurentMap X))) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧
      ∀ z : ℂ, ρ ≤ ‖z‖ → ‖z‖ ≤ 1 → IsUnit (z • linAf X n m + linBf X n m P) := by
  -- The pointwise invertibility hypothesis of `wPen_admissible`.
  have hb' : ∀ (x : X) (z : Sph ℂ),
      IsUnit ((polyOf X n (2 * m) (coeffSeq X n m P)).map (fun f => f (x, z))) := by
    intro x z
    have hzc : (z : ℂ) ≠ 0 := by
      intro h
      have h' := Metric.mem_sphere.mp z.2
      rw [dist_eq_norm, sub_zero, h, norm_zero] at h'
      exact zero_ne_one h'
    have hN : IsUnit ((P.map (Work.KT.laurentMap X)).map (fun f => f (x, z))) :=
      IsUnit.map (RingHom.mapMatrix (ContinuousMap.evalAlgHom ℂ ℂ (x, z)).toRingHom) hunit
    rw [polyOf_coeffSeq_map_eq X n m P hb x z]
    exact (isUnit_smul_of_ne_zero (n := n) (c := (z : ℂ) ^ m) (M := _)
      (pow_ne_zero m hzc)).mpr hN
  obtain ⟨-, ρ, hρ0, hρ1, hρ⟩ := wPen_admissible X n (2 * m) (coeffSeq X n m P) hb'
  exact ⟨ρ, hρ0, le_of_lt hρ1, fun z hz1 hz2 => by
    simpa only [linAf, linBf] using hρ z hz1 hz2⟩

end Work.KT.FP
