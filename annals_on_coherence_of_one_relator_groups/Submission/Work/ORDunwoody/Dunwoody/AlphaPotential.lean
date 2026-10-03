/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The potential of the counting cochain: `sigma τ` on the group

`DESIGN_N13.md` §10.3 gives the proof of

    (W1)  alpha τ (closed walk in `graph`) = 0

by exhibiting an explicit *potential* `psi τ` of the cochain `phi τ`.  This file builds the first
half: the function `sigma τ : G → ZMod 2`, defined by evaluating the word-level integral `A τ` on a
word spelling the group element, and the crossing equation

    sigma τ (a * genE P (j,true)) = sigma τ a + A τ a [(j,true)]

on the Cayley graph of `G` with respect to the positive generators, which is what makes the
recursion `S τ (pos (i+1)) = S τ (pos i) + [m_i ∈ τ]` close up at the far end of a generator edge.

The well-definedness of `sigma` uses `A_eq_zero_of_mem_normalClosure` (the vanishing of `A` on
`ker π = normalClosure P.rel`) together with `A_reverse`.
-/
import Mathlib
import Submission.Work.ORDunwoody.Dunwoody.AlphaWord
import Submission.Work.ORDunwoody.A_reverse
import Submission.Work.ORDunwoody.A_eq_zero_of_mem_normalClosure
import Submission.Work.ORDunwoody.A_endPt_rev

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

universe u

namespace Work.ORDunwoody.Dunwoody

open Work.ORDunwoody.Cayley
open scoped Sym2

variable {G : Type u} [Group G] {V : Type u} [MulAction G V] [DecidableEq V]
variable {T : GTree G V} {t₀ : V} {P : FinPresentation G}
variable {D : GeoData T t₀ P}

/-- **The word-level integral at the base point `1` only depends on the image of the word in
`G`.** -/
theorem A_eq_of_pi_eq (τ : Track D) {W₁ W₂ : List (Fin P.n × Bool)}
    (h : P.π (FreeGroup.mk W₁) = P.π (FreeGroup.mk W₂)) : A τ 1 W₁ = A τ 1 W₂ := by
  have hmem : FreeGroup.mk (W₁ ++ W₂.reverse.map Cayley.swapLetter) ∈
      Subgroup.normalClosure (P.rel : Set (FreeGroup (Fin P.n))) := by
    rw [← P.ker_eq, MonoidHom.mem_ker, ← FreeGroup.mul_mk,
      Work.ORDunwoody.mk_reverse_map_swapLetter, map_mul, map_inv, h, mul_inv_cancel]
  have hA : A τ (1 : G) (W₁ ++ W₂.reverse.map Cayley.swapLetter) = 0 :=
    Work.ORDunwoody.A_eq_zero_of_mem_normalClosure τ (1 : G) hmem
  rw [A_append (τ := τ) (a := 1), endPt_eq_mul, one_mul] at hA
  have hrev : A τ (P.π (FreeGroup.mk W₁)) (W₂.reverse.map Cayley.swapLetter) = A τ 1 W₂ := by
    have hb : endPt P (1 : G) W₂ = P.π (FreeGroup.mk W₁) := by
      rw [endPt_eq_mul, one_mul, h]
    rw [← hb, ← A_reverse (τ := τ) (a := 1) (w := W₂)]
  rw [hrev] at hA
  have hneg : ∀ x : ZMod 2, -x = x := by decide
  have := eq_neg_of_add_eq_zero_left hA
  rwa [hneg] at this

/-! ## A word for every group element -/

/-- A chosen word spelling a group element, via the surjectivity of `P.π`. -/
noncomputable def liftWord (g : G) : FreeGroup (Fin P.n) := Classical.choose (P.surj g)

theorem liftWord_spec (g : G) : P.π (liftWord (P := P) g) = g := Classical.choose_spec (P.surj g)

/-- **The potential of the counting cochain on `G`**: the value of the word-level integral at the
base point `1`, evaluated on a word spelling the group element. -/
noncomputable def sigma (τ : Track D) (g : G) : ZMod 2 :=
  A τ 1 (FreeGroup.toWord (liftWord (P := P) g))

/-- `sigma` can be evaluated on any word spelling the group element. -/
theorem sigma_eq (τ : Track D) {u : FreeGroup (Fin P.n)} {g : G} (h : P.π u = g) :
    sigma τ g = A τ 1 (FreeGroup.toWord u) := by
  rw [sigma]
  exact A_eq_of_pi_eq τ (by rw [FreeGroup.mk_toWord, FreeGroup.mk_toWord, liftWord_spec, h])

/-- **The crossing equation on the Cayley graph**: reading one further positive generator changes
`sigma` by `A τ a` of that single letter. -/
theorem sigma_genE (τ : Track D) (a : G) (j : Fin P.n) :
    sigma τ (a * CayV.genE P (j, true)) = sigma τ a + A τ a [(j, true)] := by
  have hpi : P.π (liftWord (P := P) a * FreeGroup.of j) = a * CayV.genE P (j, true) := by
    rw [map_mul, liftWord_spec, CayV.genE_true]
  have h1 : sigma τ (a * CayV.genE P (j, true)) =
      A τ 1 (FreeGroup.toWord (liftWord (P := P) a * FreeGroup.of j)) :=
    sigma_eq (τ := τ) hpi
  have h2 : A τ 1 (FreeGroup.toWord (liftWord (P := P) a * FreeGroup.of j)) =
      A τ 1 (FreeGroup.toWord (liftWord (P := P) a) ++ [(j, true)]) :=
    A_eq_of_pi_eq τ (by
      rw [FreeGroup.mk_toWord, ← FreeGroup.mul_mk, FreeGroup.mk_toWord]
      rw [show FreeGroup.mk [(j, true)] = FreeGroup.of j from
        (CayV.genF_eq_mk P.n (j, true)).symm])
  rw [h1, h2, A_append (τ := τ) (a := 1), endPt_eq_mul, one_mul, FreeGroup.mk_toWord,
    liftWord_spec]
  rw [sigma]

end Work.ORDunwoody.Dunwoody
