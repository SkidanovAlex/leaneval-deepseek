import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.slotProj_adjoint
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FibreProjDefs` — the `S`-sectors of the box ↔ model fibre decomposition

The fibre decomposition (`fibre_decomposition`) splits a state `Φ` of `Fin n → Ω` into the parts
with *exactly* `j` slots in the model space `V = span{e l}`, `j = 0, …, n`, and those parts are
pairwise orthogonal with squared norms adding up to `‖Φ‖²`.

The natural size-`j`/size-`j'` bookkeeping is by the *sets* of occupied slots, so we separate the
two indices: for a set `S` of slots define the `S`-**sector**

`slotExact e S Φ = ∑_{T ⊇ S} (-1)^{|T|-|S|} • slotProj e T Φ`,

the inclusion–exclusion form of "the slots in `S` are in `V` and the slots outside `S` are in
`Vᗮ" (the sign convention is the one of `SlotProjDefs.fibre`).  Then

`fibre e j Φ = ∑_{S : S.card = j} slotExact e S Φ`   (`fibre_eq_sum_slotExact`, definitional),

`∑_{S} slotExact e S Φ = Φ`   (`slotExact_sum_eq`),

`slotExact e S (slotExact e S' Φ) = if S = S' then slotExact e S Φ else 0`   (`slotExact_comp`),

and the sector integrals are diagonal (`slotExact_orth`).

The four facts above need `S`, `S'` to range over all subsets of `Fin n`, which is what the
`Finset.univ : Finset (Finset (Fin n))` sums below do.
-/

noncomputable section

namespace Work.BoseBoxFock

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- **The `S`-sector of the fibre decomposition**: the part of `Φ` whose slots in `S` are projected
onto `V` and whose slots outside `S` are projected onto the orthogonal complement, written by
inclusion–exclusion over the supersets of `S`:
`slotExact e S Φ = ∑_{T ⊇ S} (-1)^{|T| − |S|} slotProj e T Φ`. -/
def slotExact {m n : ℕ} (e : Fin m → Ω → ℂ) (S : Finset (Fin n)) (Φ : (Fin n → Ω) → ℂ) :
    (Fin n → Ω) → ℂ :=
  ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
    (-1 : ℂ) ^ (T.card - S.card) • slotProj e T Φ

/-- The `j`-fibre of `SlotProjDefs.fibre` is the sum of the `S`-sectors over the `j`-element slot
sets.  This holds by definition (the two double sums are the same term). -/
theorem fibre_eq_sum_slotExact {m n : ℕ} (e : Fin m → Ω → ℂ) (j : ℕ)
    (Φ : (Fin n → Ω) → ℂ) :
    fibre e j Φ = ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = j),
      slotExact e S Φ := by
  simp only [fibre, slotExact]

end Work.BoseBoxFock
