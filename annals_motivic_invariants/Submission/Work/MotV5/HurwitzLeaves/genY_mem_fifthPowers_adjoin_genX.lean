import Mathlib
import Submission.Work.MotV5.Defs
import Submission.Work.MotV5.KerDefs
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Relations
import Submission.Work.MotC2.TranslationDefs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `genY ∈ (fifthPowers)⟮genX⟯` for a Weierstrass curve in characteristic 5

The function field `K = N(E)` of a Weierstrass curve `E` over a field `N` of characteristic `5`
is generated over the subfield `F = {s ^ 5 | s : K}` of fifth powers by the coordinate `genX E`.
This file proves the second half of that statement (the first half, `genX E ∈ F⟮genX E⟯`, being
`IntermediateField.mem_adjoin_simple_self`):

  `genY E ∈ F⟮genX E⟯`.

The proof is elementary and uses no nonsingularity of `E`.  Completing the square in the
Weierstrass relation `y² + (a₁x + a₃) y = x³ + a₂x² + a₄x + a₆` (legitimate because `2 ≠ 0` in
characteristic `5`) produces `h = a₁x + a₃`, `g = x³ + a₂x² + a₄x + a₆` and `Y = y + h/2` with

  `Y² = g + (h/2)² =: G`,  hence  `Y⁵ = Y · G²`.

Both `h` and `G` are polynomials in `x`, hence lie in `M = F⟮x⟯`; `Y⁵ = y⁵ + (h/2)⁵` lies in `M`
because `y⁵ ∈ F` and `h/2 ∈ M`.  If `Y = 0` then already `y = -h/2 ∈ M`; otherwise `G ≠ 0` and
`y = Y - h/2` with `Y = Y⁵ · (G²)⁻¹ ∈ M`.  This is the content of the auxiliary lemma
`mem_subfield_of_quadratic`, stated for an arbitrary subfield of a field of characteristic `5`.

This is the hypothesis used downstream (`Work.MotV5.ker_deriv_fifthpowers`,
`fifthPowers_adjoin_genX_eq_top`) to identify the kernel of a derivation of `K/N` with `F`.

## Main results

* `Work.MotV5.HurwitzLeaves.mem_subfield_of_quadratic` — the elementary algebra lemma above;
* `Work.MotV5.HurwitzLeaves.genY_mem_fifthPowers_adjoin_genX` — the target statement.
-/

open WeierstrassCurve

namespace Work.MotV5.HurwitzLeaves

/-- **The quadratic trick.**  Let `K` be a field of characteristic `5`, `S ⊆ K` a subfield, and
`y, h, g ∈ K` with `h, g ∈ S`, `y ^ 5 ∈ S` and `y² + h y = g`.  Then `y ∈ S`.

Indeed, for `Y = y + h/2` one has `Y² = G := g + (h/2)²` and `Y⁵ = y⁵ + (h/2)⁵`, so
`Y² ∈ S` and `Y⁵ ∈ S`.  If `Y = 0` then `y = -h/2 ∈ S`; otherwise `Y = Y⁵ / (Y²)² ∈ S` since
`Y² ≠ 0`, and then `y = Y - h/2 ∈ S`. -/
theorem mem_subfield_of_quadratic {K : Type*} [Field K] [CharP K 5]
    (S : Subfield K) (y h g : K) (hh : h ∈ S) (hg : g ∈ S) (hy : y ^ 5 ∈ S)
    (hrel : y ^ 2 + h * y = g) : y ∈ S := by
  have h2 : (2 : K) ≠ 0 := CharP.cast_ne_zero_of_ne_of_prime K (by norm_num) (by norm_num)
  have h2S : (2 : K) ∈ S := by simp
  have hh2S : h / 2 ∈ S := S.div_mem hh h2S
  set Y : K := y + h / 2 with hY
  -- completing the square: `Y² = g + (h/2)²`
  have hY2 : Y ^ 2 = g + (h / 2) ^ 2 := by
    rw [hY]; field_simp; linear_combination 4 * hrel
  -- `Y⁵ = y⁵ + (h/2)⁵` by Frobenius, hence `Y⁵ ∈ S`
  have hY5 : Y ^ 5 = y ^ 5 + (h / 2) ^ 5 := by rw [hY, add_pow_char y (h / 2) 5]
  have hY5S : Y ^ 5 ∈ S := by rw [hY5]; exact S.add_mem hy (S.pow_mem hh2S 5)
  -- `Y⁴ = (Y²)² = (g + (h/2)²)² ∈ S`
  have hY4S : Y ^ 4 ∈ S := by
    have : Y ^ 4 = (Y ^ 2) ^ 2 := by ring
    rw [this, hY2]
    exact S.pow_mem (S.add_mem hg (S.pow_mem hh2S 2)) 2
  have hYS : Y ∈ S := by
    rcases eq_or_ne Y 0 with h0 | hne
    · rw [h0]; exact S.zero_mem
    · have h4ne : Y ^ 4 ≠ 0 := pow_ne_zero 4 hne
      have hEq : Y = Y ^ 5 * (Y ^ 4)⁻¹ := by
        have heq : Y ^ 5 = Y * Y ^ 4 := by ring
        rw [heq, mul_assoc, mul_inv_cancel₀ h4ne, mul_one]
      rw [hEq]
      exact S.mul_mem hY5S (S.inv_mem hY4S)
  have hy' : y = Y - h / 2 := by rw [hY]; ring
  rw [hy']
  exact S.sub_mem hYS hh2S

theorem genY_mem_fifthPowers_adjoin_genX {N : Type*} [Field N] [IsAlgClosed N] [CharP N 5]
    (E : WeierstrassCurve N) :
    Work.MotC2.genY E ∈ IntermediateField.adjoin (↥(Work.MotV5.fifthPowers E))
      ({Work.MotC2.genX E} : Set (Work.MotC2.Func E)) := by
  set x : Work.MotC2.Func E := Work.MotC2.genX E with hx
  set y : Work.MotC2.Func E := Work.MotC2.genY E with hy
  set M : IntermediateField ↥(Work.MotV5.fifthPowers E) (Work.MotC2.Func E) :=
    IntermediateField.adjoin (↥(Work.MotV5.fifthPowers E)) ({x} : Set (Work.MotC2.Func E)) with hM
  have hxM : x ∈ M := by
    rw [hM]; exact IntermediateField.mem_adjoin_simple_self _ x
  -- every `N`-polynomial in `x` lies in `M`
  have haeval : ∀ p : Polynomial N, Polynomial.aeval x p ∈ M := by
    intro p
    have h1 : Polynomial.aeval x p ∈ Algebra.adjoin N ({x} : Set (Work.MotC2.Func E)) :=
      Polynomial.aeval_mem_adjoin_singleton N (p := p) x
    have h2 : Algebra.adjoin N ({x} : Set (Work.MotC2.Func E)) ≤
        (M.restrictScalars N).toSubalgebra := by
      rw [Algebra.adjoin_le_iff]
      rintro z rfl
      exact hxM
    exact h2 h1
  -- the coefficients of the completed square
  set h : Work.MotC2.Func E :=
    algebraMap N (Work.MotC2.Func E) E.a₁ * x + algebraMap N (Work.MotC2.Func E) E.a₃ with hhdef
  set g : Work.MotC2.Func E := x ^ 3 + algebraMap N (Work.MotC2.Func E) E.a₂ * x ^ 2 +
      algebraMap N (Work.MotC2.Func E) E.a₄ * x + algebraMap N (Work.MotC2.Func E) E.a₆ with hgdef
  have hhM : h ∈ M := by
    rw [hhdef]
    have := haeval (Polynomial.C E.a₁ * Polynomial.X + Polynomial.C E.a₃)
    simpa [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C] using this
  have hgM : g ∈ M := by
    rw [hgdef]
    have := haeval (Polynomial.X ^ 3 + Polynomial.C E.a₂ * Polynomial.X ^ 2 +
      Polynomial.C E.a₄ * Polynomial.X + Polynomial.C E.a₆)
    simpa [map_add, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] using this
  -- `y ^ 5` lies in `M` because it lies in the subfield of fifth powers
  have hy5M : y ^ 5 ∈ M := by
    have hF : y ^ 5 ∈ Work.MotV5.fifthPowers E := Work.MotV5.fifthPowers_pow_mem E y
    have := IntermediateField.algebraMap_mem M (⟨y ^ 5, hF⟩ : ↥(Work.MotV5.fifthPowers E))
    simpa using this
  -- the Weierstrass relation in the completed-square coordinates `h`, `g`
  have hrel : y ^ 2 + h * y = g := by
    have H := Work.MotC2.genY_sq_relation (L := N) E
    rw [← hx, ← hy] at H
    rw [hhdef, hgdef]
    linear_combination (norm := first | refl_ring1 | ring1) H
  have hyM : y ∈ M := by
    have hkey := mem_subfield_of_quadratic (S := M.toSubfield) (y := y) (h := h) (g := g)
      ((IntermediateField.mem_toSubfield M h).mpr hhM)
      ((IntermediateField.mem_toSubfield M g).mpr hgM)
      ((IntermediateField.mem_toSubfield M (y ^ 5)).mpr hy5M)
      hrel
    exact (IntermediateField.mem_toSubfield M y).mp hkey
  exact hyM

end Work.MotV5.HurwitzLeaves
