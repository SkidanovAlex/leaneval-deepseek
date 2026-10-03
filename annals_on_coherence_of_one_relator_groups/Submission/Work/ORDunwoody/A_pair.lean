/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# `A τ a [x, swapLetter x] = 0`

`Dunwoody/AlphaWord.lean` defines the word-level integral

    A τ a w = Σ_{s ∈ faceSteps D a w} stepHit τ s     (in `ZMod 2`)

of a word `w` over `Fin P.n × Bool` read at `a`.  This file proves that `A` vanishes on the word
`x · swapLetter x`, the word that walks along a generator edge and immediately back.

The mathematical content is exactly the observation that the boundary walk of `x` and of
`swapLetter x` traverse *the same cells* — the positive generator edge `(x.1,true)` based at the
appropriate point — once forwards and once backwards, and that the contribution `stepHit τ` of a
step does not see the direction (`phi` is symmetric, `phi_comm`).  So the two contributions cancel
in `ZMod 2`.

The two lists of steps are

* `posSteps D a j`, the cells `⟨a, j, k⟩` traversed forwards, and
* `negSteps D (a * genE P (j,true)) j`, the same cells `⟨a, j, k⟩` traversed backwards and in the
  reverse order (the cell list of `negSteps` is enumerated by the base point
  `(a * genE P (j,true)) * (genE P (j,true))⁻¹ = a`, which is where the group identity is used).

Consequently the sum of the contributions of the two lists is `X + X = 0` in `ZMod 2`
(`sum_posSteps_add_sum_negSteps_mul`), and `A_pair` is the bookkeeping of the two cases
`x = (j,true)`, `x = (j,false)`.

The result is the second of the two moves generating `WordRel` for which `A` must be invariant
(the first being `A_face = alpha_faceWalk`), which is what makes `A` well defined on the kernel of
`P.π` — see the discussion in `Dunwoody/AlphaWord.lean`.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.AlphaWord

universe u

namespace Work.ORDunwoody

open Work.ORDunwoody.Cayley
open Work.ORDunwoody.Dunwoody

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-- The contribution `stepHit τ` of a step does not see its direction: the cochain `phi τ` is
symmetric. -/
theorem Dunwoody.stepHit_bwd_eq_fwd (τ : Track D) (e : Cell D) :
    stepHit τ (DStep.bwd e) = stepHit τ (DStep.fwd e) := by
  rw [stepHit_bwd, stepHit_fwd, phi_comm]

/-- **The two readings of one generator edge cancel.**  The positive generator edge `(j,true)` based
at `a` traversed forwards (`posSteps D a j`) and the negative letter `(j,false)` read at
`a * genE P (j,true)` — i.e. the same edge traversed backwards, `negSteps D (a * genE P (j,true)) j`
— visit the same cells, so their contributions add to `0` in `ZMod 2`. -/
theorem Dunwoody.sum_posSteps_add_sum_negSteps_mul (τ : Track D) (a : G) (j : Fin P.n) :
    ((posSteps D a j).map (stepHit τ)).sum
      + ((negSteps D (a * CayV.genE P (j, true)) j).map (stepHit τ)).sum = 0 := by
  by_cases h : D.L (j, true) = 0
  · -- a collapsed generator edge carries no pattern point, so both steps contribute `0`
    simp only [posSteps, negSteps, dif_pos h]
    simp
  · -- the two lists are the same cells with `bwd`/`fwd` interchanged
    simp only [posSteps, negSteps, dif_neg h]
    have hG : (stepHit τ) ∘ (fun k : Fin (D.L (j, true)) =>
          DStep.bwd ({ c := a * CayV.genE P (j, true) * (CayV.genE P (j, true))⁻¹, j := j, k := k } : Cell D))
        = (stepHit τ) ∘ (fun k : Fin (D.L (j, true)) =>
          DStep.fwd ({ c := a, j := j, k := k } : Cell D)) := by
      funext k
      simp only [Function.comp_apply]
      rw [mul_inv_cancel_right]
      exact stepHit_bwd_eq_fwd τ _
    rw [List.map_map, List.map_map, List.map_reverse, List.sum_reverse, hG]
    exact CharTwo.add_self_eq_zero _

/-- **The word-level integral kills an adjacent inverse pair** (`WordRel`'s deleting move). -/
theorem A_pair {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
    {T : Work.ORDunwoody.GTree G V} {t₀ : V} {P : Work.ORDunwoody.FinPresentation G}
    {D : Work.ORDunwoody.Cayley.GeoData T t₀ P}
    (τ : Work.ORDunwoody.Dunwoody.Track D) (a : G) (x : Fin P.n × Bool) :
    Work.ORDunwoody.Dunwoody.A τ a [x, Work.ORDunwoody.Cayley.swapLetter x] = 0 := by
  obtain ⟨j, b⟩ := x
  cases b with
  | true =>
      -- `x = (j,true)`: the walk goes forwards along the generator edge based at `a` and back
      show A τ a [(j, true), (j, false)] = 0
      simp only [A, faceSteps_true, faceSteps_false, faceSteps_nil, List.map_append, List.sum_append,
        List.map_nil, List.sum_nil, add_zero]
      exact sum_posSteps_add_sum_negSteps_mul τ a j
  | false =>
      -- `x = (j,false)`: the same, read at the other end of the generator edge
      show A τ a [(j, false), (j, true)] = 0
      simp only [A, faceSteps_true, faceSteps_false, faceSteps_nil, List.map_append, List.sum_append,
        List.map_nil, List.sum_nil, add_zero]
      have h := sum_posSteps_add_sum_negSteps_mul τ (a * (CayV.genE P (j, true))⁻¹) j
      rw [show a * (CayV.genE P (j, true))⁻¹ * CayV.genE P (j, true) = a from by group] at h
      rw [add_comm] at h
      exact h

end Work.ORDunwoody
