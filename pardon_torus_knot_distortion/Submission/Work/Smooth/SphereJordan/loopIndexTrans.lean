import Mathlib
import Submission.Work.Smooth.SphereJordan.planeIndex
import Submission.Work.Smooth.SphereJordan.planeIndexGeom
import Submission.Work.Smooth.SphereJordan.argChangeLift

/-!
# Additivity of the plane index under concatenation of loops

`loopIndex : C(unitInterval, ℂ) → ℤ` (`Submission/Work/Smooth/SphereJordan/planeIndex.lean`)
is the winding number of a closed plane curve about the origin, characterised by
`loopIndex_spec`: for every continuous lift `Λ` of `c` through `Complex.exp`, the increment
`Λ 1 - Λ 0` equals `(loopIndex c : ℂ) * (2 * π * I)`.

This file proves that the index is additive with respect to the concatenation of closed paths
based at a point `a ≠ 0`:

`loopIndexTrans` — `loopIndex (p.trans q) = loopIndex p + loopIndex q`.

The proof is the classical one: choose lifts `Λp` of `p` and `Λq` of `q` (`argChangeLift`);
replace `Λq` by the lift `Λq' = Λq + (Λp 1 - Λq 0)` of `q`, which starts at `Λp 1`; then
`P.trans Q`, where `P` and `Q` are the paths carried by `Λp` and `Λq'`, is a continuous lift of
`p.trans q`, and its increment is the sum of the increments of `Λp` and `Λq`.  Comparing with
`loopIndex_spec` for `p.trans q`, `p` and `q` and cancelling the non-zero factor `2 * π * I`
(`two_pi_I_ne_zero`) gives the result.

The comparison of the lifts is done on `ℝ` rather than on `[0,1]`, using that the extension
`Path.extend` of a concatenation is given on the two halves by
`Path.extend_trans_of_le_half` and `Path.extend_trans_of_half_le`; this keeps the proof free of
the bookkeeping of the two different proofs that a real number such as `2 * t` lies in `[0,1]`.
-/

noncomputable section

open Set

namespace Work.Smooth.SphereJordan

/-- **A lift of a path is a lift of its extension.**  If `Λ` is a lift of the path `c` through
`Complex.exp`, then the extension to `ℝ` of the path carried by `Λ` is a lift of `c.extend`. -/
lemma exp_extend_eq_of_lift {x y : ℂ} {Λ : C(unitInterval, ℂ)} {c : Path x y}
    (h : ∀ t, Complex.exp (Λ t) = c t) :
    ∀ r : ℝ, Complex.exp ((⟨Λ, rfl, rfl⟩ : Path (Λ 0) (Λ 1)).extend r) = c.extend r := by
  intro r
  rcases le_total r 0 with hr | hr
  · rw [Path.extend_of_le_zero (⟨Λ, rfl, rfl⟩ : Path (Λ 0) (Λ 1)) hr,
      Path.extend_of_le_zero c hr]
    exact (h 0).trans c.source
  · rcases le_total 1 r with hr1 | hr1
    · rw [Path.extend_of_one_le (⟨Λ, rfl, rfl⟩ : Path (Λ 0) (Λ 1)) hr1,
        Path.extend_of_one_le c hr1]
      exact (h 1).trans c.target
    · have hm : r ∈ Set.Icc (0 : ℝ) 1 := ⟨hr, hr1⟩
      rw [Path.extend_apply (⟨Λ, rfl, rfl⟩ : Path (Λ 0) (Λ 1)) hm, Path.extend_apply c hm]
      exact h ⟨r, hm⟩

theorem loopIndexTrans {a : ℂ} (ha : a ≠ 0) (p q : Path a a)
    (hp : ∀ t : Set.Icc (0 : ℝ) 1, p t ≠ 0) (hq : ∀ t : Set.Icc (0 : ℝ) 1, q t ≠ 0) :
    Work.Smooth.SphereJordan.loopIndex (p.trans q) =
      Work.Smooth.SphereJordan.loopIndex p + Work.Smooth.SphereJordan.loopIndex q := by
  -- The argument lifts of `p` and `q`.
  obtain ⟨Λp, hΛp, -, -⟩ := argChangeLift (p : C(unitInterval, ℂ)) hp
  obtain ⟨Λq, hΛq, -, -⟩ := argChangeLift (q : C(unitInterval, ℂ)) hq
  have hp1 : (p : C(unitInterval, ℂ)) 1 = a := p.target
  have hq0 : (q : C(unitInterval, ℂ)) 0 = a := q.source
  -- The lift of `q` shifted so that it starts at `Λp 1` (where the lift of `p` ends).
  let Λq' : C(unitInterval, ℂ) :=
    ⟨fun t => Λq t + (Λp 1 - Λq 0), Λq.continuous.add continuous_const⟩
  have hΛq'_exp : ∀ t : unitInterval, Complex.exp (Λq' t) = (q : C(unitInterval, ℂ)) t := by
    intro t
    change Complex.exp (Λq t + (Λp 1 - Λq 0)) = (q : C(unitInterval, ℂ)) t
    rw [Complex.exp_add, Complex.exp_sub, hΛq t, hΛp 1, hΛq 0, hp1, hq0, div_self ha, mul_one]
  have hΛq'0 : Λq' 0 = Λp 1 := by
    change Λq 0 + (Λp 1 - Λq 0) = Λp 1
    ring
  -- The two paths carried by the lifts, and their concatenation.
  let P : Path (Λp 0) (Λp 1) := ⟨Λp, rfl, rfl⟩
  let Q : Path (Λp 1) (Λq' 1) := ⟨Λq', hΛq'0, rfl⟩
  have hPext : ∀ r : ℝ, Complex.exp (P.extend r) = p.extend r :=
    exp_extend_eq_of_lift hΛp
  have hQext : ∀ r : ℝ, Complex.exp (Q.extend r) = q.extend r :=
    exp_extend_eq_of_lift hΛq'_exp
  -- `P.trans Q` is a lift of `p.trans q`, compared after extending to `ℝ`.
  have hRext : ∀ r : ℝ, Complex.exp ((P.trans Q).extend r) = (p.trans q).extend r := by
    intro r
    rcases le_total r (1 / 2) with hr | hr
    · rw [Path.extend_trans_of_le_half P Q hr, Path.extend_trans_of_le_half p q hr]
      exact hPext (2 * r)
    · rw [Path.extend_trans_of_half_le P Q hr, Path.extend_trans_of_half_le p q hr]
      exact hQext (2 * r - 1)
  have hRlift : ∀ t : unitInterval, Complex.exp ((P.trans Q) t) = (p.trans q) t := by
    intro t
    rw [← Path.extend_extends' (P.trans Q) t, ← Path.extend_extends' (p.trans q) t]
    exact hRext t
  have hne : ∀ t : unitInterval, (p.trans q) t ≠ 0 := by
    intro t
    rw [← hRlift t]
    exact Complex.exp_ne_zero _
  have hloop : (p.trans q) 0 = (p.trans q) 1 := by
    rw [Path.source (p.trans q), Path.target (p.trans q)]
  have hloopP : (p : C(unitInterval, ℂ)) 0 = (p : C(unitInterval, ℂ)) 1 :=
    p.source.trans p.target.symm
  have hloopQ : (q : C(unitInterval, ℂ)) 0 = (q : C(unitInterval, ℂ)) 1 :=
    q.source.trans q.target.symm
  -- The defining property of the index, applied to the three closed paths.
  have hspecR := loopIndex_spec (p.trans q) hne hloop (P.trans Q : C(unitInterval, ℂ)) hRlift
  have hspecP := loopIndex_spec (p : C(unitInterval, ℂ)) hp hloopP Λp hΛp
  have hspecQ := loopIndex_spec (q : C(unitInterval, ℂ)) hq hloopQ Λq' hΛq'_exp
  -- The increment of the concatenated lift is the sum of the increments.
  have hincr : (P.trans Q : C(unitInterval, ℂ)) 1 - (P.trans Q : C(unitInterval, ℂ)) 0 =
      (Λp 1 - Λp 0) + (Λq 1 - Λq 0) := by
    rw [show (P.trans Q : C(unitInterval, ℂ)) 1 = Λq' 1 from Path.target (P.trans Q),
      show (P.trans Q : C(unitInterval, ℂ)) 0 = Λp 0 from Path.source (P.trans Q)]
    change Λq 1 + (Λp 1 - Λq 0) - Λp 0 = (Λp 1 - Λp 0) + (Λq 1 - Λq 0)
    ring
  have hincrQ : Λq' 1 - Λq' 0 = Λq 1 - Λq 0 := by
    change Λq 1 + (Λp 1 - Λq 0) - (Λq 0 + (Λp 1 - Λq 0)) = Λq 1 - Λq 0
    ring
  -- Cancel the non-zero factor `2 * π * I`.
  have key : ((loopIndex (p.trans q) : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) =
      ((loopIndex p + loopIndex q : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) := by
    rw [← hspecR, hincr, hspecP, ← hincrQ, hspecQ]
    push_cast
    ring
  have hcast : ((loopIndex (p.trans q) : ℤ) : ℂ) = ((loopIndex p + loopIndex q : ℤ) : ℂ) :=
    mul_right_cancel₀ two_pi_I_ne_zero key
  exact Int.cast_inj.mp hcast

end Work.Smooth.SphereJordan
