import Mathlib
import Submission.Work.CKFinal.Socket.orbit_free_bad_finite
import Submission.Work.CKFinal.Socket.dist_vadd_lt_of_abs_lt

namespace Work.CKFinal.Socket

open UpperHalfPlane Matrix MeasureTheory
open scoped Topology

/-- `SL(2, ℤ)` (a subtype of `Matrix (Fin 2) (Fin 2) ℤ`) is countable. -/
instance instCountableSpecialLinearGroupTwoInt :
    Countable (Matrix.SpecialLinearGroup (Fin 2) ℤ) := by
  refine Function.Injective.countable (f := fun γ : Matrix.SpecialLinearGroup (Fin 2) ℤ =>
    ((γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0, (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1,
     (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0, (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1)) ?_
  intro A B h
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp only [Prod.mk.injEq] at h
  fin_cases i <;> fin_cases j <;> tauto

/-- **Density of orbit-free points.** Every point of `ℍ` has arbitrarily close points whose whole
`SL(2,ℤ)`-orbit avoids the imaginary axis `{z | Re z = 0}`.

Sketch (the "bad" set `Bad = ⋃_{γ} S_γ`, `S_γ = {σ | (γ•σ).re = 0}`, is meagre).
Each `S_γ` is closed: `σ ↦ (γ•σ).re` is continuous (prove continuity of `σ ↦ γ•σ` from
`UpperHalfPlane.coe_specialLinearGroup_apply` via
`Topology.IsEmbedding.continuous_iff UpperHalfPlane.isEmbedding_coe`).
Each `S_γ` has empty interior: given `σ₀ ∈ S_γ` and a ball `B`, the map `w ↦ γ⁻¹•w` is continuous
at `γ•σ₀`, so for small `δ > 0` the point `γ⁻¹ • ((γ•σ₀) +ᵥ (δ:ℝ))` lies in `B` and has real part
`δ ≠ 0` (translation by `δ` shifts real part by `δ`; `(γσ₀).re = 0`).
`SL(2,ℤ)` is countable, so `Bad` is meagre and cannot contain the ball `Metric.ball u ε`, which is a
Baire space (`IsOpen.baireSpace`) — equivalently `nonempty_interior_of_iUnion_of_closed` applied in
that ball.
Alternative route avoiding Baire: on the horizontal line `{u + s | s ∈ ℝ}`, `S_γ ∩ {u+s}` is the
zero set of the real quadratic `ac(x²+y²) + (ad+bc)x + bd` in `x = u.re + s` (`y = u.im`, `a,b,c,d`
the entries of `γ`), which is finite because a nonvanishing quadratic has at most two roots and the
polynomial is not identically zero (`ac = 0 ∧ ad+bc = 0` would contradict `ad - bc = 1`). Then avoid
countably many finite sets, e.g. by measure: `Set.Countable.measure_zero` with `Real.volume_Ioo`. -/
theorem F2_S2op_orbit_free_near (u : UpperHalfPlane) (ε : ℝ) (hε : 0 < ε) :
    ∃ σ : UpperHalfPlane, dist σ u < ε ∧
      ∀ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ, (γ • σ).re ≠ 0 := by
  have hy : 0 < u.im := u.im_pos
  -- The small horizontal segment through `u`; every point of it is within `ε` of `u`.
  set I : Set ℝ := Set.Ioo (-(ε * u.im)) (ε * u.im) with hI
  -- Each `γ` is bad only on a finite set of real shifts `s`, hence on a null set.
  have hzero : volume (⋃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      {s : ℝ | (γ • (s +ᵥ u)).re = 0}) = 0 := by
    apply measure_iUnion_null
    intro γ
    exact (orbit_free_bad_finite u γ).countable.measure_zero volume
  -- The segment is not covered by that null set (it has positive measure).
  have hnot : ¬ (I ⊆ ⋃ γ : Matrix.SpecialLinearGroup (Fin 2) ℤ,
      {s : ℝ | (γ • (s +ᵥ u)).re = 0}) := by
    intro hsub
    have h1 : volume I = 0 := measure_mono_null hsub hzero
    rw [hI, Real.volume_Ioo] at h1
    have hne : ENNReal.ofReal (ε * u.im - -(ε * u.im)) ≠ 0 :=
      ENNReal.ofReal_ne_zero_iff.mpr (by nlinarith)
    exact hne h1
  obtain ⟨s, hsI, hs⟩ := Set.not_subset.mp hnot
  rw [hI] at hsI
  -- `s +ᵥ u` is close to `u` and its whole orbit avoids the imaginary axis.
  refine ⟨s +ᵥ u, dist_vadd_lt_of_abs_lt hε (abs_lt.mpr ⟨hsI.1, hsI.2⟩), ?_⟩
  intro γ hcon
  exact hs (Set.mem_iUnion.mpr ⟨γ, hcon⟩)

end Work.CKFinal.Socket
