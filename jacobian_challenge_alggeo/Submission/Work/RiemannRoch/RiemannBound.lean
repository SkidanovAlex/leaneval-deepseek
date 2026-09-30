/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Area RR: Riemann's inequality (RR2.c)

`deg D - l D` is bounded above, independently of `D`.  The proof is Stichtenoth 1.4.14: a
transcendental `x` with pole divisor `B` of degree `n = [K : k(x)]` admits a `k(x)`-basis whose
elements lie in `L(r·B)`, which produces `n(m+1-r)` independent elements of `L(m·B)`, whence
`deg(mB) - l(mB) ≤ n(r-1)`; an arbitrary `D` is transported into `L(mB + div z)` by a suitable
nonzero function.
-/
import Submission.Work.RiemannRoch.Genus
import Submission.Work.RiemannRoch.Pole.deg_poleDivisor
import Submission.Work.RiemannRoch.Pole.l_nsmul_poleDivisor_ge
import Submission.Work.RiemannRoch.Pole.exists_basis_mem_L
import Submission.Work.RiemannRoch.Pole.exists_transcendental
import Submission.Work.RiemannRoch.RR.l_add_div
import Submission.Work.RiemannRoch.RR.l_sub_l_le
import Submission.Work.CurveBasics.Order.deg_div
import Submission.Work.CurveBasics.Order.finiteDimensional_adjoin_functionField

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.RiemannRoch

open Work.CurveBasics

namespace Curve

noncomputable section

variable {k : Type u} [Field k]

/-- The positive part dominates a divisor (pointwise order on divisors). -/
theorem le_pos' (C : Curve k) (D : C.Div) : D ≤ Work.CurveBasics.Linear.Curve.Div.pos D :=
  Finsupp.le_def.mpr fun Q => by
    rw [Work.CurveBasics.Linear.Curve.Div.pos_apply]; exact le_max_right 0 (D Q)

theorem pos_nonneg' (C : Curve k) (D : C.Div) (Q : C.Place) :
    0 ≤ Work.CurveBasics.Linear.Curve.Div.pos D Q :=
  Work.CurveBasics.Linear.Curve.Div.isEffective_pos D Q

/-- **Riemann's inequality** (RR2.c of the design): `deg D - l D` is bounded above. -/
theorem exists_riemann_bound (C : Curve k) :
    ∃ γ : ℤ, ∀ D : C.Div, C.deg D - C.l D ≤ γ := by
  obtain ⟨x, hx⟩ := Work.RiemannRoch.Pole.exists_transcendental C
  haveI hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set C.functionField))
      C.functionField := Work.CurveBasics.Order.finiteDimensional_adjoin_functionField C hx
  obtain ⟨r, b, hb⟩ := Work.RiemannRoch.Pole.exists_basis_mem_L C x hx
  have hdegB : C.deg (poleDivisor C x) =
      (Module.finrank (IntermediateField.adjoin k ({x} : Set C.functionField))
        C.functionField : ℤ) :=
    Work.RiemannRoch.Pole.deg_poleDivisor C x hx
  have hnpos : 1 ≤ Module.finrank (IntermediateField.adjoin k ({x} : Set C.functionField))
      C.functionField := Module.finrank_pos
  refine ⟨(Module.finrank (IntermediateField.adjoin k ({x} : Set C.functionField))
      C.functionField : ℤ) * ((r : ℤ) - 1), ?_⟩
  -- the bound for multiples of the pole divisor of `x`
  have hkey : ∀ m : ℕ, r ≤ m →
      C.deg (m • poleDivisor C x) - C.l (m • poleDivisor C x) ≤
        (Module.finrank (IntermediateField.adjoin k ({x} : Set C.functionField))
          C.functionField : ℤ) * ((r : ℤ) - 1) := by
    intro m hm
    have hlow : (Module.finrank (IntermediateField.adjoin k ({x} : Set C.functionField))
          C.functionField : ℤ) * ((m : ℤ) + 1 - (r : ℤ)) ≤
        (C.l (m • poleDivisor C x) : ℤ) := by
      have h := Work.RiemannRoch.Pole.l_nsmul_poleDivisor_ge C x hx b r hb m hm
      have hcard : Fintype.card (Fin (Module.finrank
          (IntermediateField.adjoin k ({x} : Set C.functionField)) C.functionField)) =
          Module.finrank (IntermediateField.adjoin k ({x} : Set C.functionField))
            C.functionField := Fintype.card_fin _
      rw [hcard] at h
      have h' : ((Module.finrank (IntermediateField.adjoin k ({x} : Set C.functionField))
            C.functionField * (m + 1 - r) : ℕ) : ℤ) ≤
          (C.l (m • poleDivisor C x) : ℤ) := by exact_mod_cast h
      have hcast : ((m + 1 - r : ℕ) : ℤ) = (m : ℤ) + 1 - (r : ℤ) := by omega
      calc (Module.finrank (IntermediateField.adjoin k ({x} : Set C.functionField))
              C.functionField : ℤ) * ((m : ℤ) + 1 - (r : ℤ))
          = ((Module.finrank (IntermediateField.adjoin k ({x} : Set C.functionField))
              C.functionField * (m + 1 - r) : ℕ) : ℤ) := by
            rw [Nat.cast_mul, hcast]
        _ ≤ _ := h'
    have hdeg : C.deg (m • poleDivisor C x) =
        (m : ℤ) * (Module.finrank (IntermediateField.adjoin k ({x} : Set C.functionField))
          C.functionField : ℤ) := by
      rw [Curve.deg_nsmul, hdegB]; simp
    linarith [hlow, hdeg]
  intro D
  set γ : ℤ := (Module.finrank (IntermediateField.adjoin k ({x} : Set C.functionField))
      C.functionField : ℤ) * ((r : ℤ) - 1) with hγ
  have hD1 : C.deg D - (C.l D : ℤ) ≤
      C.deg (Work.CurveBasics.Linear.Curve.Div.pos D) -
        (C.l (Work.CurveBasics.Linear.Curve.Div.pos D) : ℤ) := by
    have h := Work.RiemannRoch.RR.l_sub_l_le C (le_pos' C D)
    linarith [h]
  -- choose `m ≥ r` with `m·n > deg D⁺ + γ`
  set m : ℕ := max r ((C.deg (Work.CurveBasics.Linear.Curve.Div.pos D) + γ).toNat + 1) with hm
  have hmr : r ≤ m := le_max_left _ _
  have hmbig : C.deg (Work.CurveBasics.Linear.Curve.Div.pos D) + γ <
      (m : ℤ) * (Module.finrank (IntermediateField.adjoin k ({x} : Set C.functionField))
        C.functionField : ℤ) := by
    have hmlt : C.deg (Work.CurveBasics.Linear.Curve.Div.pos D) + γ < (m : ℤ) := by
      have h2 : (C.deg (Work.CurveBasics.Linear.Curve.Div.pos D) + γ).toNat + 1 ≤ m := by
        rw [hm]; exact le_max_right _ _
      have h3 : C.deg (Work.CurveBasics.Linear.Curve.Div.pos D) + γ <
          (((C.deg (Work.CurveBasics.Linear.Curve.Div.pos D) + γ).toNat + 1 : ℕ) : ℤ) := by
        omega
      calc C.deg (Work.CurveBasics.Linear.Curve.Div.pos D) + γ
          < (((C.deg (Work.CurveBasics.Linear.Curve.Div.pos D) + γ).toNat + 1 : ℕ) : ℤ) := h3
        _ ≤ (m : ℤ) := by exact_mod_cast h2
    have hn1 : (1 : ℤ) ≤ (Module.finrank
        (IntermediateField.adjoin k ({x} : Set C.functionField)) C.functionField : ℤ) := by
      exact_mod_cast hnpos
    have hm0 : (0 : ℤ) ≤ (m : ℤ) := Nat.cast_nonneg m
    nlinarith
  have hdegmB : C.deg (m • poleDivisor C x) =
      (m : ℤ) * (Module.finrank (IntermediateField.adjoin k ({x} : Set C.functionField))
        C.functionField : ℤ) := by
    rw [Curve.deg_nsmul, hdegB]; simp
  have hlpos : (0 : ℤ) < (C.l (m • poleDivisor C x -
      Work.CurveBasics.Linear.Curve.Div.pos D) : ℤ) := by
    have hsub : m • poleDivisor C x - Work.CurveBasics.Linear.Curve.Div.pos D ≤
        m • poleDivisor C x :=
      Finsupp.le_def.mpr fun Q => by
        simp only [Finsupp.sub_apply]
        linarith [pos_nonneg' C D Q]
    have h1 := Work.RiemannRoch.RR.l_sub_l_le C hsub
    have h2 := hkey m hmr
    have h3 : C.deg (m • poleDivisor C x - Work.CurveBasics.Linear.Curve.Div.pos D) =
        C.deg (m • poleDivisor C x) - C.deg (Work.CurveBasics.Linear.Curve.Div.pos D) :=
      Curve.deg_sub C _ _
    linarith [h1, h2, h3, hdegmB, hmbig]
  obtain ⟨z, hz0, hz⟩ : ∃ z : C.functionField, z ≠ 0 ∧
      z ∈ C.L (m • poleDivisor C x - Work.CurveBasics.Linear.Curve.Div.pos D) := by
    have hne : C.L (m • poleDivisor C x - Work.CurveBasics.Linear.Curve.Div.pos D) ≠ ⊥ := by
      intro hbot
      have : C.l (m • poleDivisor C x - Work.CurveBasics.Linear.Curve.Div.pos D) = 0 := by
        rw [Curve.l, hbot]; simp
      rw [this] at hlpos
      simp at hlpos
    obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).mp hne
    exact ⟨z, hz0, hz⟩
  have hle : Work.CurveBasics.Linear.Curve.Div.pos D ≤ m • poleDivisor C x + C.div z := by
    refine Finsupp.le_def.mpr fun Q => ?_
    have hz' := (Curve.mem_L_iff C).mp hz
    rcases hz' with h0 | heff
    · exact absurd h0 hz0
    have hq := heff Q
    simp only [Finsupp.add_apply, Finsupp.sub_apply] at hq
    simp only [Finsupp.add_apply]
    linarith
  have hfinal : C.deg (Work.CurveBasics.Linear.Curve.Div.pos D) -
      (C.l (Work.CurveBasics.Linear.Curve.Div.pos D) : ℤ) ≤ γ := by
    have h1 := Work.RiemannRoch.RR.l_sub_l_le C hle
    have h2 : C.deg (m • poleDivisor C x + C.div z) =
        C.deg (m • poleDivisor C x) + C.deg (C.div z) := Curve.deg_add C _ _
    have h3 : C.deg (C.div z) = 0 := Work.CurveBasics.Order.deg_div C z
    have h4 : C.l (m • poleDivisor C x + C.div z) = C.l (m • poleDivisor C x) :=
      Work.RiemannRoch.RR.l_add_div C (m • poleDivisor C x) hz0
    have h5 := hkey m hmr
    linarith [h1, h2, h3, h4, h5]
  linarith [hD1, hfinal]

end

end Curve

end Work.RiemannRoch
