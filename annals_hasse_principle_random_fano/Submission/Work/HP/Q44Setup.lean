import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.MDBasic.mem_Gam_iff

/-!
# Setup for `Work.HP.quartic44` (BLBS §3.4, the case `(d,n) = (4,4)`, `N = 70`)

This file is **sorry-free**.  It collects the definitions shared between
`Submission/Work/HP/quartic44.lean` and the lemmas delegated underneath it.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

namespace Work.HP

open MvPolynomial Finset

/-- The pair set of `quartic44`, **without** the successive-minimum constraint. -/
def Q44Pair (Z Δ : ℝ) : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)) :=
  {p | LinearIndependent ℤ ![p.1, p.2] ∧ eNorm p.1 ≤ Z ∧ eNorm p.2 ≤ Z ∧
    dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ Δ}

/-- The pair set of `quartic44`, with the `j`-th successive-minimum constraint.  This is
literally the set whose cardinality is `ell44 j Z Δ M`. -/
def Q44PairLam (j : ℕ) (Z Δ M : ℝ) : Set ((Fin 5 → ℤ) × (Fin 5 → ℤ)) :=
  {p | LinearIndependent ℤ ![p.1, p.2] ∧ eNorm p.1 ≤ Z ∧ eNorm p.2 ≤ Z ∧
    dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ Δ ∧ lam (Gam 4 4 p.1 p.2) j ≤ M}

theorem ell44_eq (j : ℕ) (Z Δ M : ℝ) : ell44 j Z Δ M = (Q44PairLam j Z Δ M).ncard := rfl

theorem Q44PairLam_subset (j : ℕ) (Z Δ M : ℝ) :
    Q44PairLam j Z Δ M ⊆ Q44Pair Z Δ := fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1⟩

/-- `W(L) ⊆ ℤ^{70}`: the `ℤ`-span of the Veronese images of the vectors of `L`.  It is the
coefficient space of the quartic forms restricted to `L`, and has rank `15` when `L` has
rank `3`. -/
def verSpan (L : Submodule ℤ (Fin 5 → ℤ)) : Submodule ℤ (Mon 4 4 → ℤ) :=
  Submodule.span ℤ (Set.range fun u : L => veronese 4 4 (u : Fin 5 → ℤ))

/-- The integer quartic forms that vanish identically on `L`, i.e. `W(L)^⊥`. -/
def vanishOn (L : Submodule ℤ (Fin 5 → ℤ)) : Submodule ℤ (Mon 4 4 → ℤ) :=
  orthLat (verSpan L)

theorem verSpan_le_iff {L : Submodule ℤ (Fin 5 → ℤ)} {P : Submodule ℤ (Mon 4 4 → ℤ)} :
    verSpan L ≤ P ↔ ∀ u : L, veronese 4 4 (u : Fin 5 → ℤ) ∈ P := by
  rw [verSpan, Submodule.span_le]
  simp [Set.range_subset_iff]

theorem mem_vanishOn {L : Submodule ℤ (Fin 5 → ℤ)} {a : Mon 4 4 → ℤ} :
    a ∈ vanishOn L ↔ ∀ u : L, formEval 4 4 a (u : Fin 5 → ℤ) = 0 := by
  rw [vanishOn, mem_orthLat]
  constructor
  · intro h u
    exact h (veronese 4 4 (u : Fin 5 → ℤ)) (Submodule.subset_span ⟨u, rfl⟩)
  · intro h z hz
    have hsub : verSpan L ≤ LinearMap.ker (Fintype.linearCombination ℤ a) := by
      rw [verSpan_le_iff]
      intro u
      rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
      have h2 : (∑ x, veronese 4 4 (u : Fin 5 → ℤ) x • a x)
          = ∑ x, a x * veronese 4 4 (u : Fin 5 → ℤ) x := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_eq_mul, mul_comm]
      rw [h2]
      simpa [formEval] using h u
    have hz' := hsub hz
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at hz'
    have h2 : (∑ i, z i • a i) = ∑ i, a i * z i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_eq_mul, mul_comm]
    rw [h2] at hz'
    exact hz'

/-- Every form that vanishes on all of `L` vanishes at any two vectors of `L`; i.e.
`vanishOn L ⊆ Gam 4 4 x y` for `x, y ∈ L`. -/
theorem vanishOn_le_Gam {L : Submodule ℤ (Fin 5 → ℤ)} {x y : Fin 5 → ℤ}
    (hx : x ∈ L) (hy : y ∈ L) : vanishOn L ≤ Gam 4 4 x y := by
  intro a ha
  rw [MDBasic.mem_Gam_iff]
  exact ⟨(mem_vanishOn (L := L) (a := a)).mp ha ⟨x, hx⟩,
    (mem_vanishOn (L := L) (a := a)).mp ha ⟨y, hy⟩⟩

/-- The set of rank-`3` sublattices of `ℤ^5` whose successive minima are bounded by the
scales `s : Fin 3 → ℝ`. -/
def lat3Set (s : Fin 3 → ℝ) : Set (Submodule ℤ (Fin 5 → ℤ)) :=
  {L | rk L = 3 ∧ ∀ j : Fin 3, lam L (j.val + 1) ≤ s j}


/-- The `i`-th linear form `Σ_j X_j v_{j,i}` attached to a triple `v` of vectors of `ℤ^5`. -/
def linForm (v : Fin 3 → (Fin 5 → ℤ)) (i : Fin 5) : MvPolynomial (Fin 3) ℤ :=
  ∑ j : Fin 3, MvPolynomial.C (v j i) * MvPolynomial.X j

/-- `verPoly v m`, the polynomial version of the `m`-th coordinate of `ν(Σ_j X_j v_j)`. -/
def verPoly (v : Fin 3 → (Fin 5 → ℤ)) (m : Mon 4 4) : MvPolynomial (Fin 3) ℤ :=
  ∏ i : Fin 5, (linForm v i) ^ (m.1 i : ℕ)

/-- `wCoeff v e m` is the coefficient of `t^e` in the `m`-th coordinate of `ν(Σ_j t_j v_j)`.
Equivalently, `ν(Σ_j t_j v_j) = ∑_{|e|=4} t^e • wCoeff v e`, a family of `15` vectors of `ℤ^{70}`
spanning the Veronese image of the `ℚ`-span of `v`. -/
def wCoeff (v : Fin 3 → (Fin 5 → ℤ)) (e : Fin 3 →₀ ℕ) (m : Mon 4 4) : ℤ :=
  (verPoly v m).coeff e

/-- The degree-`4` exponent vectors of three variables. -/
abbrev Tri4 := {e : Fin 3 →₀ ℕ // e.sum (fun _ n => n) = 4}

/-- The witness class of a coefficient vector `a` relative to a triple `v`: the tuple of
pairings `⟨a, wCoeff v e⟩` over the monomials `e` of degree `4`. -/
def wClass (v : Fin 3 → (Fin 5 → ℤ)) (a : Mon 4 4 → ℤ) : Tri4 → ℤ :=
  fun e => ∑ m, a m * wCoeff v e.1 m

end Work.HP
