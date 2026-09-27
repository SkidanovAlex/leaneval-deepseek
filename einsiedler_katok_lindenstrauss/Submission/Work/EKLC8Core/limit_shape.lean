/-
# `EKLC8Core.limit_shape`: the limit of the "almost unipotent" displacements

This is Step 11 of `ROUTE_LEAD.md` §5 (EKL §4.5): the shape of the limit displacement
`h` of the low-entropy argument.

A sequence `H n ∈ SL₃(ℝ)` whose entries are close to those of some element of
`U_(01)` — more precisely, whose diagonal entries are close to `1` and whose entries
`(1,0)`, `(1,2)`, `(2,0)` are close to `0`, all with the *same* error bound `c n → 0` —
and whose `U_(12)`-entries are bounded below by `ρ²/2`, has a limit `HInf` which

* is exactly of the shape `[[1,p,q],[0,1,0],[0,r,1]]` (so `HInf ∈ U_(01) = ⟨U_01, U_02, U_21⟩`),
* still satisfies the lower bound `u12max HInf ≥ ρ²/2` (so it is not the identity, and in
  particular the limit is a *genuine* displacement of the Heisenberg group).

Note that the two hypotheses `0 ≤ c n` and `HInf ∈ SL₃(ℝ)` are not needed for the proof
(they are part of the caller's setting and are kept so the statement matches the request
verbatim); the entry bounds and `c n → 0` alone force the shape, the lower bound on
`u12max` is preserved by continuity, and the resulting shape generates the entire
`U_(01)`-membership statement through `uparShape_mem`.
-/
import Mathlib
import Submission.Work.EKLC8Core.Vol
import Submission.Work.EKLC8Core.uparShape_mem
import Submission.Work.EKLC8Core.uparShape_eq_one_iff

namespace Work.EKLC8Core

set_option linter.unusedVariables false

open scoped Matrix

/-- **The limit shape.** If `H n → HInf` in `SL₃(ℝ)`, if the diagonal entries of `H n` tend
to `1` and its `(1,0)`, `(1,2)`, `(2,0)` entries tend to `0` (measured by the common error
bound `c n → 0`), and if `u12max (H n) ≥ ρ²/2` throughout, then the same holds at the limit
and `HInf` is the Heisenberg shape `[[1,p,q],[0,1,0],[0,r,1]] ∈ U_(01)`, distinct from the
identity. -/
theorem limit_shape {H : ℕ → SL3} {HInf : SL3} {c : ℕ → ℝ} {ρ : ℝ}
    (hρ : 0 < ρ) (hc : Filter.Tendsto c Filter.atTop (nhds 0)) (hc0 : ∀ n, 0 ≤ c n)
    (htend : Filter.Tendsto H Filter.atTop (nhds HInf))
    (h00 : ∀ n, |(H n : Matrix (Fin 3) (Fin 3) ℝ) 0 0 - 1| ≤ c n)
    (h11 : ∀ n, |(H n : Matrix (Fin 3) (Fin 3) ℝ) 1 1 - 1| ≤ c n)
    (h22 : ∀ n, |(H n : Matrix (Fin 3) (Fin 3) ℝ) 2 2 - 1| ≤ c n)
    (h10 : ∀ n, |(H n : Matrix (Fin 3) (Fin 3) ℝ) 1 0| ≤ c n)
    (h12 : ∀ n, |(H n : Matrix (Fin 3) (Fin 3) ℝ) 1 2| ≤ c n)
    (h20 : ∀ n, |(H n : Matrix (Fin 3) (Fin 3) ℝ) 2 0| ≤ c n)
    (hlower : ∀ n, ρ ^ 2 / 2 ≤ u12max (H n : Matrix (Fin 3) (Fin 3) ℝ)) :
    (HInf : Matrix (Fin 3) (Fin 3) ℝ) 0 0 = 1 ∧ (HInf : Matrix (Fin 3) (Fin 3) ℝ) 1 1 = 1 ∧
    (HInf : Matrix (Fin 3) (Fin 3) ℝ) 2 2 = 1 ∧ (HInf : Matrix (Fin 3) (Fin 3) ℝ) 1 0 = 0 ∧
    (HInf : Matrix (Fin 3) (Fin 3) ℝ) 1 2 = 0 ∧ (HInf : Matrix (Fin 3) (Fin 3) ℝ) 2 0 = 0 ∧
    ρ ^ 2 / 2 ≤ u12max (HInf : Matrix (Fin 3) (Fin 3) ℝ) ∧
    HInf ∈ Upar h01 h02 h21 ∧ HInf ≠ 1 := by
  -- Convergence in the subtype `SL₃(ℝ) ⊆ ℝ^{3×3}` is entrywise convergence of matrices.
  have hmat : Filter.Tendsto (fun n => (H n : Matrix (Fin 3) (Fin 3) ℝ)) Filter.atTop
      (nhds (HInf : Matrix (Fin 3) (Fin 3) ℝ)) :=
    (continuous_subtype_val.tendsto HInf).comp htend
  have hentry (i j : Fin 3) : Filter.Tendsto (fun n => (H n : Matrix (Fin 3) (Fin 3) ℝ) i j)
      Filter.atTop (nhds ((HInf : Matrix (Fin 3) (Fin 3) ℝ) i j)) :=
    ((continuous_apply j).tendsto _).comp (((continuous_apply i).tendsto _).comp hmat)
  -- An entry of `HInf` which is `c n`-close to the constant `K` along the sequence equals `K`.
  have hlim (i j : Fin 3) (K : ℝ)
      (hK : ∀ n, |(H n : Matrix (Fin 3) (Fin 3) ℝ) i j - K| ≤ c n) :
      (HInf : Matrix (Fin 3) (Fin 3) ℝ) i j = K := by
    have h1 : Filter.Tendsto (fun n => |(H n : Matrix (Fin 3) (Fin 3) ℝ) i j - K|)
        Filter.atTop (nhds |(HInf : Matrix (Fin 3) (Fin 3) ℝ) i j - K|) :=
      (continuous_abs.tendsto _).comp ((hentry i j).sub tendsto_const_nhds)
    have h2 : |(HInf : Matrix (Fin 3) (Fin 3) ℝ) i j - K| ≤ 0 :=
      le_of_tendsto_of_tendsto h1 hc (Filter.Eventually.of_forall hK)
    have h3 : |(HInf : Matrix (Fin 3) (Fin 3) ℝ) i j - K| = 0 := le_antisymm h2 (abs_nonneg _)
    linarith [abs_eq_zero.mp h3]
  have hd00 : (HInf : Matrix (Fin 3) (Fin 3) ℝ) 0 0 = 1 := hlim 0 0 1 h00
  have hd11 : (HInf : Matrix (Fin 3) (Fin 3) ℝ) 1 1 = 1 := hlim 1 1 1 h11
  have hd22 : (HInf : Matrix (Fin 3) (Fin 3) ℝ) 2 2 = 1 := hlim 2 2 1 h22
  have hd10 : (HInf : Matrix (Fin 3) (Fin 3) ℝ) 1 0 = 0 :=
    hlim 1 0 0 (fun n => by simpa using h10 n)
  have hd12 : (HInf : Matrix (Fin 3) (Fin 3) ℝ) 1 2 = 0 :=
    hlim 1 2 0 (fun n => by simpa using h12 n)
  have hd20 : (HInf : Matrix (Fin 3) (Fin 3) ℝ) 2 0 = 0 :=
    hlim 2 0 0 (fun n => by simpa using h20 n)
  -- `u12max` is continuous, so the lower bound passes to the limit.
  have hcontu : Continuous (fun M : Matrix (Fin 3) (Fin 3) ℝ => u12max M) := by
    unfold u12max
    fun_prop
  have hu12lim : Filter.Tendsto (fun n => u12max ((H n : Matrix (Fin 3) (Fin 3) ℝ)))
      Filter.atTop (nhds (u12max ((HInf : SL3) : Matrix (Fin 3) (Fin 3) ℝ))) :=
    (hcontu.tendsto _).comp hmat
  have hu12 : ρ ^ 2 / 2 ≤ u12max ((HInf : SL3) : Matrix (Fin 3) (Fin 3) ℝ) :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hu12lim (Filter.Eventually.of_forall hlower)
  -- The limit has the Heisenberg shape, hence lies in `U_(01)`.
  have hshape : HInf = uparShape ((HInf : Matrix (Fin 3) (Fin 3) ℝ) 0 1)
      ((HInf : Matrix (Fin 3) (Fin 3) ℝ) 0 2)
      ((HInf : Matrix (Fin 3) (Fin 3) ℝ) 2 1) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [uparShape, hd00, hd11, hd22, hd10, hd12, hd20]
  have hmem : HInf ∈ Upar h01 h02 h21 := by
    rw [hshape]
    exact uparShape_mem _ _ _
  -- `u12max HInf ≥ ρ²/2 > 0`, while `u12max 1 = 0`.
  have hne : HInf ≠ 1 := by
    intro hEq
    have hzero : u12max ((HInf : SL3) : Matrix (Fin 3) (Fin 3) ℝ) = 0 := by
      rw [hEq, Matrix.SpecialLinearGroup.coe_one]
      simp [u12max]
    have hpos : 0 < u12max ((HInf : SL3) : Matrix (Fin 3) (Fin 3) ℝ) := by
      have : (0 : ℝ) < ρ ^ 2 / 2 := by positivity
      linarith
    linarith
  exact ⟨hd00, hd11, hd22, hd10, hd12, hd20, hu12, hmem, hne⟩

end Work.EKLC8Core
