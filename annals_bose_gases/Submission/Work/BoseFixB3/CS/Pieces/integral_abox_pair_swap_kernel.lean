import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB3.CS.Ledger
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB3.CS.Pieces.integral_abox_pair_swap_kernel`

The **pair-swap kernel identity** for the centred analysis box `abox n ℓ`: the box integral of
the *swapped* kernel coincides with `ℓ⁶` times the box integral of the *diagonal-inserted*
kernel,

    ∫_{x ∈ abox n ℓ} ∫_{y ∈ acube ℓ} ∫_{z ∈ acube ℓ} K(x_{i←y, j←z}, y, z) dy dz dx
      = ℓ⁶ · ∫_{x ∈ abox n ℓ} K(x, x_i, x_j) dx     (i ≠ j).

## Why it is true

The map `(x, y, z) ↦ (x_{i←y, j←z}, y, z)` on `X n × ℝ³ × ℝ³` merely permutes the three
"slots" `i`, `j` and the two extra variables `y`, `z` (it is the involution `i ↔ y`, `j ↔ z`
applied to the two coordinates `x_i, x_j` of `x`), so it preserves Lebesgue measure and the
product set `abox n ℓ × acube ℓ × acube ℓ`.  Equivalently, and this is the route taken below:
peeling the two slots `i, j` off the box integral (`abox_integral_peel2_gen`) turns the two
box integrals into the *same* iterated integral over the remaining `n - 2` coordinates, because

* the swapped kernel at `ins2 i j' y z r2` is `K(ins2 i j' y z r2, y, z)` — the extra variables
  of the peel are exactly the slot values — and the two free peel variables integrate out with
  total volume `(ℓ³)² = ℓ⁶`;
* the diagonal kernel `K(x, x_i, x_j)` at `ins2 i j' y z r2` is again `K(ins2 i j' y z r2, y, z)`,
  and the two cube integrals are interchanged by Fubini.

## Route

`abox_integral_peel2_gen` (`Submission.Work.SmallBoxPairIdent`) does the peel, with
`ins2`/`rest2` the coordinate insertion of `Submission.Q0Value`; `real_volume_acube` gives the
`ℓ³` constant integral, `integral_swap_acube_real` the Fubini swap.  The `n ≤ 1` cases are
vacuous (`i ≠ j` is unsatisfiable).
-/

noncomputable section

open MeasureTheory
open scoped Topology Real ENNReal

namespace Work.BoseFixB3.CS.Pieces

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option maxHeartbeats 2000000 in
theorem integral_abox_pair_swap_kernel {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (i j : Fin n) (hij : i ≠ j)
    {K : Submission.BoseGases.X n → EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hKc : Continuous (fun p : Submission.BoseGases.X n × EuclideanSpace ℝ (Fin 3)
        × EuclideanSpace ℝ (Fin 3) => K p.1 p.2.1 p.2.2)) :
    ∫ x in Submission.BoseGases.abox n ℓ,
        (∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
          K (Function.update (Function.update x i y) j z) y z)
      = ℓ ^ 6 * ∫ x in Submission.BoseGases.abox n ℓ, K x (x i) (x j) := by
  rcases n with _ | _ | p
  · exact i.elim0
  · exact absurd ((Fin.eq_zero i).trans (Fin.eq_zero j).symm) hij
  · obtain ⟨j', hj'⟩ := Fin.exists_succAbove_eq (x := j) (y := i) hij.symm
    set f : Submission.BoseGases.X (p+2) → ℝ := fun x =>
      ∫ y in Submission.BoseGases.acube ℓ, ∫ z in Submission.BoseGases.acube ℓ,
        K (Function.update (Function.update x i y) j z) y z with hf
    set g : Submission.BoseGases.X (p+2) → ℝ := fun x => K x (x i) (x j) with hg
    -- Continuity (hence box integrability) of the two integrands.
    have hf_cont : Continuous f := by
      rw [hf]
      have hinn : Continuous (fun q : Submission.BoseGases.X (p+2) × E3 =>
          ∫ v in Submission.BoseGases.acube ℓ,
            K (Function.update (Function.update q.1 i q.2) j v) q.2 v) := by
        refine continuous_parametric_integral_of_continuous
          (f := fun (q : Submission.BoseGases.X (p+2) × E3) (v : E3) =>
            K (Function.update (Function.update q.1 i q.2) j v) q.2 v) ?_ (acube_compact hℓ)
        show Continuous (fun qv : (Submission.BoseGases.X (p+2) × E3) × E3 =>
            K (Function.update (Function.update qv.1.1 i qv.1.2) j qv.2) qv.1.2 qv.2)
        exact hKc.comp ((((continuous_fst.comp continuous_fst).update i
            (continuous_snd.comp continuous_fst)).update j continuous_snd).prodMk
          ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
      refine continuous_parametric_integral_of_continuous
        (f := fun (x : Submission.BoseGases.X (p+2)) (u : E3) =>
          ∫ v in Submission.BoseGases.acube ℓ,
            K (Function.update (Function.update x i u) j v) u v) ?_ (acube_compact hℓ)
      exact hinn
    have hg_cont : Continuous g := by
      rw [hg]
      fun_prop
    have hf_int : IntegrableOn f (abox (p+2) ℓ) volume :=
      ContinuousOn.integrableOn_compact (abox_compact (p+2) hℓ) hf_cont.continuousOn
    have hg_int : IntegrableOn g (abox (p+2) ℓ) volume :=
      ContinuousOn.integrableOn_compact (abox_compact (p+2) hℓ) hg_cont.continuousOn
    -- The two-slot peel of the box integral.
    have hpeel_f : (∫ x in abox (p+2) ℓ, f x)
        = ∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ, f (ins2 i j' y z r2) :=
      abox_integral_peel2_gen (i := i) (j' := j') (F := f) hf_int
    have hpeel_g : (∫ x in abox (p+2) ℓ, g x)
        = ∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ, g (ins2 i j' y z r2) :=
      abox_integral_peel2_gen (i := i) (j' := j') (F := g) hg_int
    -- The two free peel variables are a constant: their integral is `(ℓ³)² = ℓ⁶`.
    have hconst : ∀ c : ℝ, (∫ z in acube ℓ, ∫ y in acube ℓ, c) = ℓ ^ 6 * c := by
      intro c
      have h1 : (∫ y in acube ℓ, c) = ℓ ^ 3 * c := by
        rw [MeasureTheory.integral_const, real_volume_acube ℓ hℓ.le, smul_eq_mul]
      calc (∫ z in acube ℓ, ∫ y in acube ℓ, c)
          = ∫ z in acube ℓ, (ℓ ^ 3 * c) := by
            refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
            exact h1
        _ = ℓ ^ 6 * c := by
            rw [MeasureTheory.integral_const, real_volume_acube ℓ hℓ.le, smul_eq_mul]
            ring
    -- The two-slot update behind the swapped kernel.
    have hupd : ∀ (r2 : Submission.BoseGases.X p) (y z u v : E3),
        Function.update (Function.update (ins2 i j' y z r2) i u) j v = ins2 i j' u v r2 := by
      intro r2 y z u v
      rw [Function.update_comm (a := i) (b := j) hij u v (ins2 i j' y z r2), ← hj']
      exact upd_upd_ins2 i j' y z u v r2
    -- The pointwise values of the two integrands on the peeled fibre.
    have hf_point : ∀ (r2 : Submission.BoseGases.X p) (y z : E3),
        f (ins2 i j' y z r2)
          = ∫ a in acube ℓ, ∫ b in acube ℓ, K (ins2 i j' a b r2) a b := by
      intro r2 y z
      rw [hf]
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      refine integral_congr_ae (Filter.Eventually.of_forall fun b => ?_)
      simp only [hupd r2 y z a b]
    have hg_point : ∀ (r2 : Submission.BoseGases.X p) (y z : E3),
        g (ins2 i j' y z r2) = K (ins2 i j' y z r2) y z := by
      intro r2 y z
      rw [hg]
      have hz : (ins2 i j' y z r2) j = z := by
        rw [← hj']; exact ins2_apply_succ i j' y z r2
      simp only [ins2_apply_i, hz]
    -- The swapped side: peel, insert the pointwise value, integrate out `y, z`.
    have step_f : (∫ x in abox (p+2) ℓ, f x)
        = ℓ ^ 6 * ∫ r2 in abox p ℓ,
            (∫ a in acube ℓ, ∫ b in acube ℓ, K (ins2 i j' a b r2) a b) := by
      rw [hpeel_f]
      rw [show (∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ, f (ins2 i j' y z r2))
            = ∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ,
                (∫ a in acube ℓ, ∫ b in acube ℓ, K (ins2 i j' a b r2) a b) from by
          refine integral_congr_ae (Filter.Eventually.of_forall fun r2 => ?_)
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          exact hf_point r2 y z]
      rw [show (∫ r2 in abox p ℓ, ∫ z in acube ℓ, ∫ y in acube ℓ,
                (∫ a in acube ℓ, ∫ b in acube ℓ, K (ins2 i j' a b r2) a b))
            = ∫ r2 in abox p ℓ,
                ℓ ^ 6 * (∫ a in acube ℓ, ∫ b in acube ℓ, K (ins2 i j' a b r2) a b) from by
          refine integral_congr_ae (Filter.Eventually.of_forall fun r2 => ?_)
          exact hconst (∫ a in acube ℓ, ∫ b in acube ℓ, K (ins2 i j' a b r2) a b)]
      rw [MeasureTheory.integral_const_mul]
    -- The diagonal side: peel, insert the pointwise value, Fubini.
    have step_g : (∫ x in abox (p+2) ℓ, g x)
        = ∫ r2 in abox p ℓ,
            (∫ a in acube ℓ, ∫ b in acube ℓ, K (ins2 i j' a b r2) a b) := by
      rw [hpeel_g]
      refine integral_congr_ae (Filter.Eventually.of_forall fun r2 => ?_)
      simp only []
      rw [show (∫ z in acube ℓ, ∫ y in acube ℓ, g (ins2 i j' y z r2))
            = ∫ z in acube ℓ, ∫ y in acube ℓ, K (ins2 i j' y z r2) y z from by
          refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          exact hg_point r2 y z]
      refine (integral_swap_acube_real hℓ (F := fun y z : E3 => K (ins2 i j' y z r2) y z) ?_).symm
      show Continuous (fun q : E3 × E3 => K (ins2 i j' q.1 q.2 r2) q.1 q.2)
      exact hKc.comp (((contDiff_ins2 i j').continuous.comp
          ((continuous_fst.prodMk continuous_snd).prodMk continuous_const)).prodMk
        (continuous_fst.prodMk continuous_snd))
    rw [step_f, step_g]

end Work.BoseFixB3.CS.Pieces
