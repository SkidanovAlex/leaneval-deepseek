import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.SlotProjDefs` — the mode-projection kernels of BF3c

The box-side fibre decomposition of the box ↔ model bridge (`BF3C_PLAN.md` §1) needs the
orthogonal projection onto the span `V` of the honest modes (`modeONBCplx`), as a *kernel*
on `ℝ³ × ℝ³`:

* `PV e x y = Σ_l e l x * conj (e l y)` — the kernel of the orthogonal projection onto
  `V_ℂ = span{e l}` when the `e l` are orthonormal;
* `slotProj e S Φ x` — the state `Φ` with the slots in `S` projected onto `V` (the integral
  over the `|S|` fibre variables of `Π_{i ∈ S} PV (x i) (z i)` times `Φ` at the modified
  configuration).

These are *definitions only*: the operator algebra (self-adjointness, idempotence, the
resolution form used by `BF3C_PLAN.md` §1) is proved in the modules that consume them.
-/

noncomputable section

namespace Work.BoseBoxFock

set_option autoImplicit false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The kernel of the orthogonal projection onto the span of the modes `e`. -/
def PV {m : ℕ} (e : Fin m → ℝ³ → ℂ) (x y : ℝ³) : ℂ :=
  ∑ l : Fin m, e l x * star (e l y)

/-- The `S`-slot projection of a state `Φ` onto `V` (the slots in `S` are integrated against
`PV`, the others are kept). -/
def slotProj {m n : ℕ} (e : Fin m → ℝ³ → ℂ) (S : Finset (Fin n))
    (Φ : (Fin n → ℝ³) → ℂ) (x : Fin n → ℝ³) : ℂ :=
  ∫ z : {i : Fin n // i ∈ S} → ℝ³,
    (∏ i : {i : Fin n // i ∈ S}, PV e (x i.1) (z i)) *
      Φ (fun i => if h : i ∈ S then z ⟨i, h⟩ else x i)

/-- **The `j`-fibre of `Φ`**: its component with *exactly* `j` slots in `V`, obtained from the
slot projections by inclusion–exclusion over the supersets of the `j`-sets:
`(exactly S in V) = Σ_{T ⊇ S} (−1)^{|T|−|S|} slotProj T`, and
`fibre j Φ = Σ_{|S| = j} (exactly S) Φ`.  By the finite algebra
`Σ_{S ⊆ U}(−1)^{|U|−|S|} = (1−1)^{|U|} = δ_{U,∅}`, the `fibre j Φ` add up to `Φ`
(`fibre_decomposition`); and — since `slotProj` is idempotent, commuting and self-adjoint
(`slotProj_idem_and_comm`, `slotProj_adjoint`) — the `(exactly S)` for `S ≠ S'` are *disjoint*
projections (`Q_i(1−Q_i) = 0` in a slot of the symmetric difference), so the fibres are pairwise
orthogonal. -/
def fibre {m n : ℕ} (e : Fin m → ℝ³ → ℂ) (j : ℕ) (Φ : (Fin n → ℝ³) → ℂ) :
    (Fin n → ℝ³) → ℂ :=
  ∑ S ∈ Finset.univ.filter (fun S : Finset (Fin n) => S.card = j),
    ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
      (-1 : ℂ) ^ (T.card - S.card) • slotProj e T Φ

end Work.BoseBoxFock
