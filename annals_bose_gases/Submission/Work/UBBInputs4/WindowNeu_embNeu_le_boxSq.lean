import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.UBBInputs4.ExtClass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs4.WindowNeu_embNeu_le_boxSq`

The bridge from the **covariant** `n₊`-window on the extended (Neumann) class back to the
normalisation delivered by round 2.

`Work.UBBInputs4.WindowNeu W N L Φ` is FS's `eq:apriorinn+` in its covariant form
`cnPlus L Φ ≤ W N L · aboxSq N L Φ`, where the excited count `cnPlus` and the mass are both
taken over the *centred* box `abox N L` on which the mean projections `Pᵢ, Qᵢ` live.  The
delivered consumers (round 2/3) normalise instead by `boxSq N L Ψ = ∫_{box N L} Ψ²` on the
*Dirichlet* box `box N L = [0,L]^{3N}`, and they see only Dirichlet states
`Ψ : CInfty0Box N L`, embedded into the Neumann class by `embNeu hL Ψ`.

The two boxes are *not* nested (`abox N L` is centred at the origin, `box N L` starts at the
origin), so `aboxSq ≤ boxSq` is **not** a set-monotonicity statement.  What makes it true is
the Dirichlet support condition: `Ψ` vanishes off `box N L` (`tsupport Ψ ⊆ interior (box N L)`,
hence `Ψ = 0` outside the box), so the centred-box integral is really an integral over the
overlap `abox N L ∩ box N L ⊆ box N L`:

    aboxSq N L (embNeu hL Ψ) = ∫_{abox ∩ box} Ψ² ≤ ∫_{box} Ψ² = boxSq N L Ψ .

Composing with the window hypothesis (and `W N L ≥ 0`) gives the requested bound
`cnPlus L Ψ ≤ W N L · boxSq N L Ψ`; the excited count itself is unchanged by `embNeu`
(definitionally, `embNeu hL Ψ` is `Ψ`).
-/

noncomputable section

open MeasureTheory
open scoped Topology Real BigOperators

namespace Work.UBBInputs4

open Submission.BoseGases
open Work.UBBInputs2
open _root_.BoseGases

set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **The centred-box mass of a Dirichlet state is bounded by its Dirichlet-box mass.**
The Dirichlet state `Ψ` is supported in the interior of `box N L`, so
`∫_{abox N L} Ψ² = ∫_{abox N L ∩ box N L} Ψ² ≤ ∫_{box N L} Ψ²`.  (The boxes `abox N L` and
`box N L` are not nested; it is the support condition that makes the comparison true.) -/
lemma aboxSq_embNeu_le_boxSq {N : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : BoseGases.CInfty0Box N L) :
    aboxSq N L (embNeu hL Ψ) ≤ boxSq N L Ψ := by
  have hfun : ((embNeu hL Ψ : CNeu N L) : X N → ℝ) = (Ψ : X N → ℝ) := rfl
  rw [aboxSq_def, boxSq, hfun]
  -- the state vanishes off `box N L`, so the centred-box integral is supported on the overlap
  have hstep1 : (∫ x in abox N L, ((Ψ : X N → ℝ) x) ^ 2)
      = ∫ x in abox N L ∩ box N L, ((Ψ : X N → ℝ) x) ^ 2 := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (abox_measurable N L)
      Set.inter_subset_left ?_
    intro x hx
    have hxb : x ∉ box N L := fun hb => hx.2 ⟨hx.1, hb⟩
    rw [psi_eq_zero_of_not_mem_interior Ψ (fun h => hxb (interior_subset h))]
    ring
  -- the overlap is contained in the Dirichlet box
  have hstep2 : (∫ x in abox N L ∩ box N L, ((Ψ : X N → ℝ) x) ^ 2)
      ≤ ∫ x in box N L, ((Ψ : X N → ℝ) x) ^ 2 :=
    setIntegral_mono_set (cont_integrableOn_box hL ((psi_contDiff Ψ).continuous.pow 2))
      (ae_of_all _ (fun x => sq_nonneg _)) (LE.le.eventuallyLE Set.inter_subset_right)
  rw [hstep1]
  exact hstep2

theorem WindowNeu_embNeu_le_boxSq {W : ℕ → ℝ → ℝ} {N : ℕ} {L : ℝ} (hL : 0 < L)
    (hW : 0 ≤ W N L) (Ψ : BoseGases.CInfty0Box N L)
    (h : Work.UBBInputs4.WindowNeu W N L (Submission.BoseGases.embNeu hL Ψ)) :
    Submission.BoseGases.cnPlus L (Ψ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℝ)
      ≤ W N L * Work.UBBInputs2.boxSq N L Ψ := by
  have hfun : ((embNeu hL Ψ : CNeu N L) : X N → ℝ) = (Ψ : X N → ℝ) := rfl
  -- the excited count is definitionally unchanged by the embedding
  rw [WindowNeu] at h
  have hcn : cnPlus L ((embNeu hL Ψ : CNeu N L) : X N → ℝ) = cnPlus L (Ψ : X N → ℝ) := by
    rw [hfun]
  rw [hcn] at h
  exact le_trans h (mul_le_mul_of_nonneg_left (aboxSq_embNeu_le_boxSq hL Ψ) hW)

end Work.UBBInputs4
