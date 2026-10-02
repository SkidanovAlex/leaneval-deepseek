import Mathlib
import Submission.Work.Stems.Hur2b.Assembly
import Submission.Work.Stems.Hur2b.PsiCancel
import Submission.Work.Stems.Hur2b.psiFunCancel_boundary
import Submission.Work.Stems.Hur2b.cubD_comp_cubD

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Agreement of the cancellation family along the seams of `∂I³`

`psiFunCancel x₀ c s` is the interpolation family of `Submission/Work/Stems/Hur2b/PsiCancel.lean`.
The point of this file is that it *glues* along the seams of the `1`-skeleton of the boundary of a
`3`-cube: if `z ∈ I³` lies on two distinct faces `{zᵢ = b}` and `{zᵢ' = b'}` of the cube, then the
value computed on the face `i` at `z` and the value computed on the face `i'` at `z` coincide, for
every value of the interpolation parameter.

The mechanism is completely explicit.  For a point `t` of the square lying on the edge where the
`q`-th coordinate equals `0` or `1`, `psiFunCancel` is the `K₁`-filling of the corresponding edge of
the face, evaluated at radial coordinate `s` and tangential coordinate `clamp (2u - 1/2)`, where `u`
is the *other* coordinate of `t` (`psiFunCancel_coord` below).  For `z` on two faces `i ≠ i'`, the
two square points `z ∘ i.succAbove` and `z ∘ i'.succAbove` lie on the edges of their squares cut out
by the *same* pair of frozen cube coordinates, and the free cube coordinate is the same in both
parametrisations; hence both sides are the `K₁`-filling of the same cube edge evaluated at the same
point of `I²`.
-/

open scoped unitInterval Topology

namespace Work.Stems.Hur2b

open Work.Stems.Cubical
open Work.Stems.Hur2

noncomputable section

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-! ## The two ends of `I`, indexed by `Fin 2` -/

/-- The two ends `0`, `1` of `I`, indexed by `Fin 2` in the order used by `face3`. -/
def endVal : Fin 2 → unitInterval := ![0, 1]

@[simp] theorem endVal_zero : endVal 0 = 0 := rfl

@[simp] theorem endVal_one : endVal 1 = 1 := rfl

theorem endVal_eq (b : Fin 2) :
    endVal b = (if (b : ℕ) = 0 then 0 else 1 : unitInterval) := by
  fin_cases b <;> rfl

theorem face3_eq (τ : C(IC 3, X)) (i : Fin 3) (b : Fin 2) :
    face3 τ i b = faceCube i (endVal b) τ := by
  rw [face3, ← endVal_eq b]

/-! ## The value on an edge of the square -/

/-- **The value of `psiFunCancel` on an edge of the square.**  If the `q`-th coordinate of `t` is
the end `endVal r` of `I`, then `psiFunCancel x₀ c s t` is the `K₁`-filling of the `q`-th face of
`c` at the end `endVal r`, evaluated at radial coordinate `s` and tangential coordinate
`clamp (2u - 1/2)`, where `u` is the other coordinate of `t`. -/
theorem psiFunCancel_coord (x₀ : X) (c : C(IC 2, X)) (s : unitInterval) (q r : Fin 2)
    (t : IC 2) (ht : t q = endVal r) :
    psiFunCancel x₀ c s t =
      K₁ x₀ (c.comp (faceCM q (endVal r)))
        (pair2 s (clamp (2 * (t (q.succAbove 0) : ℝ) - 1/2))) := by
  fin_cases q <;> fin_cases r
  · have ht0 : t 0 = 0 := by simpa using ht
    have ht' : t = pair2 0 (t 1) := by
      funext j; fin_cases j <;> simp [pair2, ht0]
    rw [ht', psiFunCancel_pair2_0_left]
    simp [Fin.one_succAbove_zero, pair2]
  · have ht0 : t 0 = 1 := by simpa using ht
    have ht' : t = pair2 1 (t 1) := by
      funext j; fin_cases j <;> simp [pair2, ht0]
    rw [ht', psiFunCancel_pair2_1_right]
    simp [Fin.one_succAbove_zero, pair2]
  · have ht1 : t 1 = 0 := by simpa using ht
    have ht' : t = pair2 (t 0) 0 := by
      funext j; fin_cases j <;> simp [pair2, ht1]
    rw [ht', psiFunCancel_pair2_0_bot]
    simp [Fin.one_succAbove_zero, pair2]
  · have ht1 : t 1 = 1 := by simpa using ht
    have ht' : t = pair2 (t 0) 1 := by
      funext j; fin_cases j <;> simp [pair2, ht1]
    rw [ht', psiFunCancel_pair2_1_top]
    simp [Fin.one_succAbove_zero, pair2]

/-! ## The seam agreement -/

theorem psiFunCancel_seam_agree {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X] (x₀ : X)
    (τ : ContinuousMap (Work.Stems.Cubical.IC 3) X) {i i' : Fin 3} (h : i ≠ i')
    {b b' : Fin 2} {z : Work.Stems.Cubical.IC 3}
    (hi : z i = (if (b : ℕ) = 0 then 0 else 1 : unitInterval))
    (hi' : z i' = (if (b' : ℕ) = 0 then 0 else 1 : unitInterval)) (s : unitInterval) :
    Work.Stems.Hur2b.psiFunCancel x₀ (Work.Stems.Hur2b.face3 τ i b) s (fun j => z (i.succAbove j))
      = Work.Stems.Hur2b.psiFunCancel x₀ (Work.Stems.Hur2b.face3 τ i' b') s
          (fun j => z (i'.succAbove j)) := by
  -- positions of the two faces outside of each other
  obtain ⟨q, hq⟩ : ∃ q : Fin 2, i.succAbove q = i' := by
    rcases Fin.eq_self_or_eq_succAbove i i' with h' | ⟨q, hq⟩
    · exact absurd h'.symm h
    · exact ⟨q, hq.symm⟩
  obtain ⟨q', hq'⟩ : ∃ q' : Fin 2, i'.succAbove q' = i := by
    rcases Fin.eq_self_or_eq_succAbove i' i with h' | ⟨q', hq'⟩
    · exact absurd h' h
    · exact ⟨q', hq'.symm⟩
  have hpred : q.predAbove i = q' := by
    have h1 : i'.succAbove (q.predAbove i) = i := by
      have h2 := Fin.succAbove_succAbove_predAbove i q
      rw [hq] at h2
      exact h2
    exact Fin.succAbove_right_injective (h1.trans hq'.symm)
  -- the two faces cut out the same cube edge
  have hedge : (face3 τ i b).comp (faceCM q (endVal b')) =
      (face3 τ i' b').comp (faceCM q' (endVal b)) := by
    rw [face3_eq, face3_eq]
    ext u
    simp only [ContinuousMap.comp_apply, faceCM_apply, faceCube]
    rw [faceFun_faceFun i q (endVal b) (endVal b') u, hq, hpred]
  -- the free coordinate is parametrised by the same point of `I`
  have hidx : i.succAbove (q.succAbove (0 : Fin 1)) =
      i'.succAbove (q'.succAbove (0 : Fin 1)) := by
    have h2 := Fin.succAbove_succAbove_succAbove_predAbove i q (0 : Fin 1)
    rw [hq, hpred] at h2
    exact h2.symm
  have hfree : z (i.succAbove (q.succAbove (0 : Fin 1))) =
      z (i'.succAbove (q'.succAbove (0 : Fin 1))) := by
    rw [hidx]
  have htL : (fun j => z (i.succAbove j)) q = endVal b' := by
    show z (i.succAbove q) = endVal b'
    rw [hq]
    exact hi'.trans (endVal_eq b').symm
  have htR : (fun j => z (i'.succAbove j)) q' = endVal b := by
    show z (i'.succAbove q') = endVal b
    rw [hq']
    exact hi.trans (endVal_eq b).symm
  have hL := psiFunCancel_coord x₀ (face3 τ i b) s q b' (fun j => z (i.succAbove j)) htL
  have hR := psiFunCancel_coord x₀ (face3 τ i' b') s q' b (fun j => z (i'.succAbove j)) htR
  rw [hL, hR, hedge, hfree]

end

end Work.Stems.Hur2b
