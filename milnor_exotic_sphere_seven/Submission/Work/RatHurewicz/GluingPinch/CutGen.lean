import Mathlib
import Submission.Work.RatHurewicz.GluingPinch.CutDefs
import Submission.Work.Stems.WedgePinch

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The general-`n` cut lemma

A based `n`-cube which is `x₀` on the coordinate hyperplane `{u i = a}` splits, in `π_n(X,x₀)`, as
the product of the classes of the two affine readings `cutL i a p h` and `cutR i a p h`
(`Cl_defs`/`CutDefs.lean`).  This is the general-`n`, general-coordinate version of
`Work.Stems.Hur2b.cl_cut_vertical`.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical
open Work.Stems.Hur2

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X}

theorem stretchI_eq_left {a : unitInterval} {s : unitInterval} (hs : (s : ℝ) ≤ 1/2) :
    stretchI a s = clamp ((a : ℝ) * ((clamp (2 * (s : ℝ)) : unitInterval) : ℝ)) := by
  show clamp (min (1:ℝ) (2 * (s : ℝ)) * (a : ℝ)
      + max (0:ℝ) (2 * (s : ℝ) - 1) * (1 - (a : ℝ))) = _
  have h1 : min (1:ℝ) (2 * (s : ℝ)) = 2 * (s : ℝ) := min_eq_right (by linarith)
  have h2 : max (0:ℝ) (2 * (s : ℝ) - 1) = 0 := max_eq_left (by linarith)
  have hmem : (2 * (s : ℝ)) ∈ Set.Icc (0:ℝ) 1 := by
    constructor <;> linarith [s.2.1, s.2.2]
  have hc : ((clamp (2 * (s : ℝ)) : unitInterval) : ℝ) = 2 * (s : ℝ) := by
    rw [clamp_of_mem hmem]
  rw [h1, h2, hc]
  congr 1
  ring

theorem stretchI_eq_right {a : unitInterval} {s : unitInterval} (hs : 1/2 ≤ (s : ℝ)) :
    stretchI a s
      = clamp ((a : ℝ) + (1 - (a : ℝ)) * ((clamp (2 * (s : ℝ) - 1) : unitInterval) : ℝ)) := by
  show clamp (min (1:ℝ) (2 * (s : ℝ)) * (a : ℝ)
      + max (0:ℝ) (2 * (s : ℝ) - 1) * (1 - (a : ℝ))) = _
  have h1 : min (1:ℝ) (2 * (s : ℝ)) = 1 := min_eq_left (by linarith [s.2.2])
  have h2 : max (0:ℝ) (2 * (s : ℝ) - 1) = 2 * (s : ℝ) - 1 := max_eq_right (by linarith)
  have hmem : (2 * (s : ℝ) - 1) ∈ Set.Icc (0:ℝ) 1 := by
    constructor <;> linarith [s.2.1, s.2.2]
  have hc : ((clamp (2 * (s : ℝ) - 1) : unitInterval) : ℝ) = 2 * (s : ℝ) - 1 := by
    rw [clamp_of_mem hmem]
  rw [h1, h2, hc]
  congr 1
  ring

/-- The stretched cube is the concatenation of the two affine readings. -/
theorem coordUpd_stretch_eq_transAt {n : ℕ} (i : Fin n) (a : unitInterval)
    (p : GenLoop (Fin n) X x₀) (h : ∀ u : IC n, u i = a → p.1 u = x₀) :
    (⟨p.1.comp (coordUpd n i (stretchI a)),
        fun u hu => p.2 _ (coordUpd_mem_boundary i (stretchI a)
          (stretchI_zero_val a) (stretchI_one_val a) hu)⟩ : GenLoop (Fin n) X x₀)
      = GenLoop.transAt i (cutL i a p h) (cutR i a p h) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  refine Eq.trans ?_ (Work.Stems.GenLoop.transAt_apply n i (cutL i a p h) (cutR i a p h) t).symm
  by_cases ht : (t i : ℝ) ≤ 1 / 2
  · rw [if_pos ht]
    have harg : Function.update t i (stretchI a (t i))
        = Function.update (Work.Stems.sigmaA i t) i
            (clamp ((a : ℝ) * (((Work.Stems.sigmaA i t) i : unitInterval) : ℝ))) := by
      funext j
      by_cases hj : j = i
      · subst hj
        rw [Function.update_apply, if_pos rfl, Function.update_apply, if_pos rfl,
          Work.Stems.sigmaA_apply_self]
        exact stretchI_eq_left ht
      · rw [Function.update_apply, if_neg hj, Function.update_apply, if_neg hj,
          Work.Stems.sigmaA_apply_of_ne i t hj]
    show p.1 (Function.update t i (stretchI a (t i))) = (cutL i a p h) (Work.Stems.sigmaA i t)
    rw [harg]
    rfl
  · rw [if_neg ht]
    push_neg at ht
    have harg : Function.update t i (stretchI a (t i))
        = Function.update (Work.Stems.sigmaB i t) i
            (clamp ((a : ℝ) + (1 - (a : ℝ)) *
              (((Work.Stems.sigmaB i t) i : unitInterval) : ℝ))) := by
      funext j
      by_cases hj : j = i
      · subst hj
        rw [Function.update_apply, if_pos rfl, Function.update_apply, if_pos rfl,
          Work.Stems.sigmaB_apply_self]
        exact stretchI_eq_right ht.le
      · rw [Function.update_apply, if_neg hj, Function.update_apply, if_neg hj,
          Work.Stems.sigmaB_apply_of_ne i t hj]
    show p.1 (Function.update t i (stretchI a (t i))) = (cutR i a p h) (Work.Stems.sigmaB i t)
    rw [harg]
    rfl

/-- **The cut lemma**: a based cube which is `x₀` on the hyperplane `{u i = a}` splits as the
product of the classes of its two affine readings. -/
theorem cl_cut_gen {n : ℕ} [NeZero n] [Nontrivial (Fin n)] (i : Fin n) (p : GenLoop (Fin n) X x₀)
    (a : unitInterval) (h : ∀ u : IC n, u i = a → p.1 u = x₀) :
    cl n X x₀ p = cl n X x₀ (cutL i a p h) * cl n X x₀ (cutR i a p h) := by
  have hcl : cl n X x₀ (⟨p.1.comp (coordUpd n i (stretchI a)),
      fun u hu => p.2 _ (coordUpd_mem_boundary i (stretchI a)
        (stretchI_zero_val a) (stretchI_one_val a) hu)⟩ : GenLoop (Fin n) X x₀)
      = cl n X x₀ p :=
    cl_coordUpd i (stretchI a) (stretchI_zero_val a) (stretchI_one_val a) p
  have htrans := coordUpd_stretch_eq_transAt i a p h
  rw [← hcl, htrans]
  have hmul : cl n X x₀ (GenLoop.transAt i (cutL i a p h) (cutR i a p h))
      = cl n X x₀ (cutR i a p h) * cl n X x₀ (cutL i a p h) := by
    have hspec := HomotopyGroup.mul_spec (N := Fin n) (X := X) (x := x₀) (i := i)
      (p := cutR i a p h) (q := cutL i a p h)
    have h' : (show HomotopyGroup (Fin n) X x₀ from
        Quotient.mk _ (GenLoop.transAt i (cutL i a p h) (cutR i a p h)))
        = (show HomotopyGroup (Fin n) X x₀ from Quotient.mk _ (cutR i a p h))
          * (show HomotopyGroup (Fin n) X x₀ from Quotient.mk _ (cutL i a p h)) := by
      simpa only [cl] using hspec.symm
    simpa only [cl] using h'
  rw [hmul, mul_comm]

end

end Work.RatHurewicz
