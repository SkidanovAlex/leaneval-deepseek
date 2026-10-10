import Mathlib
import Submission.Work.MotK.TwRuling.SdWNdeg
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The products of two elements of `L(5·O)` span `L(10·O)`

Let `R` be a field, `E` a Weierstrass curve over `R`, `x = genX E`, `y = genY E` in the function
field `Om = E.FunctionField`, and

* `sdBas E = ![1, x, y, x², xy]` — the basis of `L(5·O)`,
* `sdTen E = (1, x, …, x⁵; y, xy, x²y, x³y)` — the ten monomials of `L(10·O)`.

The main result `productSpan_eq` says that the `R`-span of the 25 products `b_i b_j` of two
elements of the basis coincides with the `R`-span of the ten monomials.  This is the
"`L(5·O)·L(5·O) = L(10·O)`" statement.

The only non-trivial inputs are the Weierstrass relation `y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆`
(it exhibits `y²`, hence `xy²` and `x²y²`, in the span of the ten monomials) and its multiples by
`x` and `x²` (which exhibit `x⁵` in the span of the products).
-/

open WeierstrassCurve WeierstrassCurve.Affine

namespace Work.MotK.TwRuling

noncomputable section

variable {R : Type} [Field R]

/-- Every product of two elements of the basis `1, x, y, x², xy` lies in the span of the ten
monomials `1, x, …, x⁵, y, xy, x²y, x³y`. -/
private theorem sdBas_mul_mem (E : WeierstrassCurve R) (m l : Fin 5) :
    sdBas E m * sdBas E l ∈ Submodule.span R (Set.range (sdTen E)) := by
  let S : Submodule R (Affine.FunctionField E) := Submodule.span R (Set.range (sdTen E))
  have hgen : ∀ (i : Fin 6 ⊕ Fin 4), sdTen E i ∈ S := fun i =>
    Submodule.subset_span (Set.mem_range_self i)
  have h1 : (1 : Affine.FunctionField E) ∈ S := hgen (Sum.inl 0)
  have hx : Work.MotV.genX E ∈ S := by simpa using hgen (Sum.inl 1)
  have hy : Work.MotV.genY E ∈ S := by simpa using hgen (Sum.inr 0)
  have hx2 : (Work.MotV.genX E)^2 ∈ S := by simpa using hgen (Sum.inl 2)
  have hxy : Work.MotV.genX E * Work.MotV.genY E ∈ S := by simpa using hgen (Sum.inr 1)
  have hx3 : (Work.MotV.genX E)^3 ∈ S := by simpa using hgen (Sum.inl 3)
  have hx2y : (Work.MotV.genX E)^2 * Work.MotV.genY E ∈ S := by simpa using hgen (Sum.inr 2)
  have hx4 : (Work.MotV.genX E)^4 ∈ S := by simpa using hgen (Sum.inl 4)
  have hx3y : (Work.MotV.genX E)^3 * Work.MotV.genY E ∈ S := by simpa using hgen (Sum.inr 3)
  have hsm : ∀ (c : R) {v : Affine.FunctionField E}, v ∈ S →
      algebraMap R (Affine.FunctionField E) c * v ∈ S := by
    intro c v hv
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem S c hv
  have hc6 : algebraMap R (Affine.FunctionField E) E.a₆ ∈ S := by simpa using hsm E.a₆ h1
  -- the Weierstrass relation, solved for `y²`
  have hrel : (Work.MotV.genY E)^2 =
      (Work.MotV.genX E)^3 + algebraMap R (Affine.FunctionField E) E.a₂ * (Work.MotV.genX E)^2
        + algebraMap R (Affine.FunctionField E) E.a₄ * Work.MotV.genX E
        + algebraMap R (Affine.FunctionField E) E.a₆
        - algebraMap R (Affine.FunctionField E) E.a₁ * (Work.MotV.genX E * Work.MotV.genY E)
        - algebraMap R (Affine.FunctionField E) E.a₃ * Work.MotV.genY E := by
    linear_combination (norm := first | refl_ring1 | ring1) sdWeierstrass E
  have hy2 : (Work.MotV.genY E)^2 ∈ S := by
    rw [hrel]
    exact Submodule.sub_mem S (Submodule.sub_mem S
      (Submodule.add_mem S (Submodule.add_mem S (Submodule.add_mem S hx3 (hsm E.a₂ hx2))
        (hsm E.a₄ hx)) hc6) (hsm E.a₁ hxy)) (hsm E.a₃ hy)
  -- the relation multiplied by `x`
  have hxy2 : Work.MotV.genX E * (Work.MotV.genY E)^2 ∈ S := by
    have h : Work.MotV.genX E * (Work.MotV.genY E)^2 =
        (Work.MotV.genX E)^4 + algebraMap R (Affine.FunctionField E) E.a₂ * (Work.MotV.genX E)^3
          + algebraMap R (Affine.FunctionField E) E.a₄ * (Work.MotV.genX E)^2
          + algebraMap R (Affine.FunctionField E) E.a₆ * Work.MotV.genX E
          - algebraMap R (Affine.FunctionField E) E.a₁ * ((Work.MotV.genX E)^2 * Work.MotV.genY E)
          - algebraMap R (Affine.FunctionField E) E.a₃ * (Work.MotV.genX E * Work.MotV.genY E) := by
      linear_combination (norm := first | refl_ring1 | ring1) (Work.MotV.genX E) * sdWeierstrass E
    rw [h]
    exact Submodule.sub_mem S (Submodule.sub_mem S
      (Submodule.add_mem S (Submodule.add_mem S (Submodule.add_mem S hx4 (hsm E.a₂ hx3))
        (hsm E.a₄ hx2)) (hsm E.a₆ hx)) (hsm E.a₁ hx2y)) (hsm E.a₃ hxy)
  -- the relation multiplied by `x²`
  have hx2y2 : (Work.MotV.genX E)^2 * (Work.MotV.genY E)^2 ∈ S := by
    have h : (Work.MotV.genX E)^2 * (Work.MotV.genY E)^2 =
        (Work.MotV.genX E)^5 + algebraMap R (Affine.FunctionField E) E.a₂ * (Work.MotV.genX E)^4
          + algebraMap R (Affine.FunctionField E) E.a₄ * (Work.MotV.genX E)^3
          + algebraMap R (Affine.FunctionField E) E.a₆ * (Work.MotV.genX E)^2
          - algebraMap R (Affine.FunctionField E) E.a₁ * ((Work.MotV.genX E)^3 * Work.MotV.genY E)
          - algebraMap R (Affine.FunctionField E) E.a₃ * ((Work.MotV.genX E)^2 * Work.MotV.genY E) := by
      linear_combination (norm := first | refl_ring1 | ring1) (Work.MotV.genX E)^2 * sdWeierstrass E
    rw [h]
    exact Submodule.sub_mem S (Submodule.sub_mem S
      (Submodule.add_mem S (Submodule.add_mem S
        (Submodule.add_mem S (hgen (Sum.inl 5)) (hsm E.a₂ hx4))
        (hsm E.a₄ hx3)) (hsm E.a₆ hx2)) (hsm E.a₁ hx3y)) (hsm E.a₃ hx2y)
  fin_cases m <;> fin_cases l <;> simp [sdBas]
  · exact h1
  · exact hx
  · exact hy
  · exact hx2
  · exact hxy
  · exact hx
  · rw [show Work.MotV.genX E * Work.MotV.genX E = (Work.MotV.genX E)^2 by ring]; exact hx2
  · exact hxy
  · rw [show Work.MotV.genX E * (Work.MotV.genX E)^2 = (Work.MotV.genX E)^3 by ring]; exact hx3
  · rw [show Work.MotV.genX E * (Work.MotV.genX E * Work.MotV.genY E)
        = (Work.MotV.genX E)^2 * Work.MotV.genY E by ring]; exact hx2y
  · exact hy
  · rw [show Work.MotV.genY E * Work.MotV.genX E = Work.MotV.genX E * Work.MotV.genY E by ring]
    exact hxy
  · rw [show Work.MotV.genY E * Work.MotV.genY E = (Work.MotV.genY E)^2 by ring]; exact hy2
  · rw [show Work.MotV.genY E * (Work.MotV.genX E)^2
        = (Work.MotV.genX E)^2 * Work.MotV.genY E by ring]; exact hx2y
  · rw [show Work.MotV.genY E * (Work.MotV.genX E * Work.MotV.genY E)
        = Work.MotV.genX E * (Work.MotV.genY E)^2 by ring]; exact hxy2
  · exact hx2
  · rw [show (Work.MotV.genX E)^2 * Work.MotV.genX E = (Work.MotV.genX E)^3 by ring]; exact hx3
  · exact hx2y
  · rw [show (Work.MotV.genX E)^2 * (Work.MotV.genX E)^2 = (Work.MotV.genX E)^4 by ring]; exact hx4
  · rw [show (Work.MotV.genX E)^2 * (Work.MotV.genX E * Work.MotV.genY E)
        = (Work.MotV.genX E)^3 * Work.MotV.genY E by ring]; exact hx3y
  · exact hxy
  · rw [show Work.MotV.genX E * Work.MotV.genY E * Work.MotV.genX E
        = (Work.MotV.genX E)^2 * Work.MotV.genY E by ring]; exact hx2y
  · rw [show Work.MotV.genX E * Work.MotV.genY E * Work.MotV.genY E
        = Work.MotV.genX E * (Work.MotV.genY E)^2 by ring]; exact hxy2
  · rw [show Work.MotV.genX E * Work.MotV.genY E * (Work.MotV.genX E)^2
        = (Work.MotV.genX E)^3 * Work.MotV.genY E by ring]; exact hx3y
  · rw [show Work.MotV.genX E * Work.MotV.genY E * (Work.MotV.genX E * Work.MotV.genY E)
        = (Work.MotV.genX E)^2 * (Work.MotV.genY E)^2 by ring]; exact hx2y2

/-- Every one of the ten monomials `1, x, …, x⁵, y, xy, x²y, x³y` is a linear combination of
products of two elements of the basis `1, x, y, x², xy`. -/
private theorem sdTen_mem_prod (E : WeierstrassCurve R) (i : Fin 6 ⊕ Fin 4) :
    sdTen E i ∈
      Submodule.span R (Set.range (fun p : Fin 5 × Fin 5 => sdBas E p.1 * sdBas E p.2)) := by
  let T : Submodule R (Affine.FunctionField E) :=
    Submodule.span R (Set.range (fun p : Fin 5 × Fin 5 => sdBas E p.1 * sdBas E p.2))
  have hprod : ∀ m l : Fin 5, sdBas E m * sdBas E l ∈ T := fun m l =>
    Submodule.subset_span (Set.mem_range_self
      (f := fun p : Fin 5 × Fin 5 => sdBas E p.1 * sdBas E p.2) (m, l))
  have hsm : ∀ (c : R) {v : Affine.FunctionField E}, v ∈ T →
      algebraMap R (Affine.FunctionField E) c * v ∈ T := by
    intro c v hv
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem T c hv
  have h1 : (1 : Affine.FunctionField E) ∈ T := by
    rw [show (1 : Affine.FunctionField E) = sdBas E 0 * sdBas E 0 by simp [sdBas]]
    exact hprod 0 0
  have hx : Work.MotV.genX E ∈ T := by
    rw [show Work.MotV.genX E = sdBas E 0 * sdBas E 1 by simp [sdBas]]
    exact hprod 0 1
  have hy : Work.MotV.genY E ∈ T := by
    rw [show Work.MotV.genY E = sdBas E 0 * sdBas E 2 by simp [sdBas]]
    exact hprod 0 2
  have hx2 : (Work.MotV.genX E)^2 ∈ T := by
    rw [show (Work.MotV.genX E)^2 = sdBas E 1 * sdBas E 1 by simp [sdBas]; ring]
    exact hprod 1 1
  have hxy : Work.MotV.genX E * Work.MotV.genY E ∈ T := by
    rw [show Work.MotV.genX E * Work.MotV.genY E = sdBas E 1 * sdBas E 2 by simp [sdBas]]
    exact hprod 1 2
  have hx3 : (Work.MotV.genX E)^3 ∈ T := by
    rw [show (Work.MotV.genX E)^3 = sdBas E 1 * sdBas E 3 by simp [sdBas]; ring]
    exact hprod 1 3
  have hx2y : (Work.MotV.genX E)^2 * Work.MotV.genY E ∈ T := by
    rw [show (Work.MotV.genX E)^2 * Work.MotV.genY E = sdBas E 1 * sdBas E 4 by
      simp [sdBas]; ring]
    exact hprod 1 4
  have hx4 : (Work.MotV.genX E)^4 ∈ T := by
    rw [show (Work.MotV.genX E)^4 = sdBas E 3 * sdBas E 3 by simp [sdBas]; ring]
    exact hprod 3 3
  have hx3y : (Work.MotV.genX E)^3 * Work.MotV.genY E ∈ T := by
    rw [show (Work.MotV.genX E)^3 * Work.MotV.genY E = sdBas E 3 * sdBas E 4 by
      simp [sdBas]; ring]
    exact hprod 3 4
  have hx2y2 : (Work.MotV.genX E)^2 * (Work.MotV.genY E)^2 ∈ T := by
    rw [show (Work.MotV.genX E)^2 * (Work.MotV.genY E)^2 = sdBas E 4 * sdBas E 4 by
      simp [sdBas]; ring]
    exact hprod 4 4
  have g0 : sdTen E (Sum.inl 0) ∈ T := by simpa using h1
  have g1 : sdTen E (Sum.inl 1) ∈ T := by simpa using hx
  have g2 : sdTen E (Sum.inl 2) ∈ T := by simpa using hx2
  have g3 : sdTen E (Sum.inl 3) ∈ T := by simpa using hx3
  have g4 : sdTen E (Sum.inl 4) ∈ T := by simpa using hx4
  have g5 : sdTen E (Sum.inl 5) ∈ T := by
    rw [show sdTen E (Sum.inl 5) = (Work.MotV.genX E)^5 by simp]
    have h5rel : (Work.MotV.genX E)^5 = (Work.MotV.genX E)^2 * (Work.MotV.genY E)^2
        + algebraMap R (Affine.FunctionField E) E.a₁ * ((Work.MotV.genX E)^3 * Work.MotV.genY E)
        + algebraMap R (Affine.FunctionField E) E.a₃ * ((Work.MotV.genX E)^2 * Work.MotV.genY E)
        - algebraMap R (Affine.FunctionField E) E.a₂ * (Work.MotV.genX E)^4
        - algebraMap R (Affine.FunctionField E) E.a₄ * (Work.MotV.genX E)^3
        - algebraMap R (Affine.FunctionField E) E.a₆ * (Work.MotV.genX E)^2 := by
      linear_combination (norm := first | refl_ring1 | ring1) -(Work.MotV.genX E)^2 * sdWeierstrass E
    rw [h5rel]
    exact Submodule.sub_mem T (Submodule.sub_mem T (Submodule.sub_mem T
      (Submodule.add_mem T (Submodule.add_mem T hx2y2 (hsm E.a₁ hx3y)) (hsm E.a₃ hx2y))
      (hsm E.a₂ hx4)) (hsm E.a₄ hx3)) (hsm E.a₆ hx2)
  have g6 : sdTen E (Sum.inr 0) ∈ T := by simpa using hy
  have g7 : sdTen E (Sum.inr 1) ∈ T := by simpa using hxy
  have g8 : sdTen E (Sum.inr 2) ∈ T := by simpa using hx2y
  have g9 : sdTen E (Sum.inr 3) ∈ T := by simpa using hx3y
  rcases i with i | j
  · fin_cases i
    · exact g0
    · exact g1
    · exact g2
    · exact g3
    · exact g4
    · exact g5
  · fin_cases j
    · exact g6
    · exact g7
    · exact g8
    · exact g9

theorem productSpan_eq (R : Type) [Field R] (E : WeierstrassCurve R) :
    Submodule.span R (Set.range (fun p : Fin 5 × Fin 5 =>
        Work.MotK.TwRuling.sdBas E p.1 * Work.MotK.TwRuling.sdBas E p.2))
      = Submodule.span R (Set.range (Work.MotK.TwRuling.sdTen E)) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro v ⟨p, rfl⟩
    exact sdBas_mul_mem E p.1 p.2
  · rw [Submodule.span_le]
    rintro v ⟨i, rfl⟩
    exact sdTen_mem_prod E i

end

end Work.MotK.TwRuling
