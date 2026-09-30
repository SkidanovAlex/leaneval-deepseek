import Mathlib
import Submission.Work.RiemannRoch.Differentials

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.RiemannRoch.RR

open Work.RiemannRoch

universe u

/-- The lattice `A(D ⊔ E)` is contained in `A(D) + A(E)`: an adèle bounded by the maximum
of `D` and `E` can be split, place by place, according to which of the two bounds is larger. -/
theorem Asub_sup_le {k : Type u} [Field k] (C : Work.CurveBasics.Curve k) (D E : C.Div) :
    Curve.Asub C (D ⊔ E) ≤ Curve.Asub C D ⊔ Curve.Asub C E := by
  intro x hx
  rw [Curve.mem_Asub, Curve.mem_A] at hx
  let xf : C.Place → C.functionField := (x : C.Place → C.functionField)
  have hxf : ∀ Q, xf Q = 0 ∨ -((D ⊔ E) Q) ≤ C.ordAt (xf Q) Q := hx
  -- Split `x = y + (x - y)` where `y` keeps the `Q`-component exactly when `D Q ≥ E Q`.
  let y : Curve.Adeles C :=
    ⟨fun Q => if E Q ≤ D Q then xf Q else 0, by
      refine Set.Finite.subset x.2 ?_
      intro Q hQ
      simp only [Set.mem_setOf_eq] at hQ ⊢
      by_cases h : E Q ≤ D Q
      · simpa [xf, h] using hQ
      · rw [if_neg h, Curve.ordAt_zero] at hQ
        exact absurd hQ (lt_irrefl 0)⟩
  let yf : C.Place → C.functionField := (y : C.Place → C.functionField)
  have hyval : ∀ Q, yf Q = if E Q ≤ D Q then xf Q else 0 := fun Q => rfl
  have hyA : yf ∈ Curve.A C D := by
    rw [Curve.mem_A]
    intro Q
    rw [hyval Q]
    by_cases h : E Q ≤ D Q
    · rw [if_pos h]
      rcases hxf Q with h0 | h0
      · exact Or.inl h0
      · refine Or.inr ?_
        have hsup : (D ⊔ E) Q = D Q := by
          rw [Finsupp.sup_apply, max_eq_left h]
        linarith
    · rw [if_neg h]
      exact Or.inl rfl
  have hzval : ∀ Q, ((x - y : Curve.Adeles C) : C.Place → C.functionField) Q = xf Q - yf Q :=
    fun Q => rfl
  have hzA : ((x - y : Curve.Adeles C) : C.Place → C.functionField) ∈ Curve.A C E := by
    rw [Curve.mem_A]
    intro Q
    rw [hzval Q]
    by_cases h : E Q ≤ D Q
    · refine Or.inl ?_
      rw [hyval Q, if_pos h, sub_self]
    · have hy0 : yf Q = 0 := by rw [hyval Q, if_neg h]
      by_cases hx0 : xf Q = 0
      · refine Or.inl ?_
        rw [hy0, hx0, sub_zero]
      · refine Or.inr ?_
        rw [hy0, sub_zero]
        rcases hxf Q with h0 | h0
        · exact absurd h0 hx0
        · have hsup : (D ⊔ E) Q = E Q := by
            rw [Finsupp.sup_apply, max_eq_right (le_of_lt (lt_of_not_ge h))]
          linarith
  have hyD : y ∈ Curve.Asub C D := Curve.mem_Asub.mpr hyA
  have hzE : (x - y) ∈ Curve.Asub C E := Curve.mem_Asub.mpr hzA
  have hsum : y + (x - y) = x := by abel
  rw [← hsum]
  exact Submodule.add_mem_sup hyD hzE

theorem mem_WD_sup {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    {ω : Module.Dual k (Work.RiemannRoch.Curve.Adeles C)} {D E : C.Div}
    (hD : ω ∈ Work.RiemannRoch.Curve.WD C D) (hE : ω ∈ Work.RiemannRoch.Curve.WD C E) :
    ω ∈ Work.RiemannRoch.Curve.WD C (D ⊔ E) := by
  rw [Curve.mem_WD_iff] at hD hE ⊢
  intro a ha
  rw [Submodule.mem_sup] at ha
  obtain ⟨b, hb, c, hc, rfl⟩ := ha
  -- `b ∈ Asub (D ⊔ E) ⊆ Asub D + Asub E`, so `b = b₁ + b₂`.
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := Submodule.mem_sup.mp (Asub_sup_le C D E hb)
  rw [map_add, map_add, hD b₁ (Submodule.mem_sup_left hb₁),
    hE b₂ (Submodule.mem_sup_left hb₂), hD c (Submodule.mem_sup_right hc), add_zero,
    zero_add]

end Work.RiemannRoch.RR
