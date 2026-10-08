import Mathlib
import Submission.Work.Hering.Wagner.Core
import Submission.Work.Hering.Wagner.closure_transvections_eq_top
import Submission.Work.Hering.Wagner.eq_transvection_of_fixes_coatom

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Step 6 of Wagner's proposition: a subgroup containing transvection pieces is everything

Let `U` be a `3`-dimensional `𝔽₂`-space and `P ≤ GL(U)` a subgroup with the following property:
for every hyperplane `X ≤ U` and every `0 ≠ a ∈ X` there is `τ ∈ P` fixing `X` pointwise and
sending some `c ∉ X` to `c + w` with `w ∈ X`, `w ≠ 0`, `w ≠ a`.

Then `P = ⊤`.

The argument: by `eq_transvection_of_fixes_coatom`, such a `τ` is the transvection
`y ↦ y + f y • w` for the unique `f` with `ker f = X`.  Applying the hypothesis twice, with
`a ∈ X` and then with `a := w`, produces two transvections of `P` with the same `f` and with
distinct directions `w, w' ∈ X`.  Since `X` is `2`-dimensional, `X = span {w, w'}`, and every
other direction `u ∈ X` is `0`, `w`, `w'` or `w + w'`, giving respectively `1`, `t_w`, `t_{w'}`
and `t_w * t_{w'}`; so `P` contains *all* transvections with functional `f`.  As `f` varies,
every transvection is obtained, and the transvections generate `GL(U)`.
-/

set_option autoImplicit false

namespace Work.Hering.Wagner

open Module Submodule

/-- Two `LinearEquiv.transvection`s with the same functional and direction, but different
proofs of the vanishing condition, coincide. -/
theorem transvection_eq_of_proof_irrel {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    {f : Module.Dual (ZMod 2) V} {v : V} (h₁ h₂ : f v = 0) :
    LinearEquiv.transvection h₁ = LinearEquiv.transvection h₂ :=
  congrArg (fun h => LinearEquiv.transvection (f := f) (v := v) h) (Subsingleton.elim h₁ h₂)

/-- **Step 6 of Wagner's proposition.**  A subgroup of `GL(U)`, `dim U = 3`, containing the
"transvection pieces" produced by the orbit-counting part of the proof is all of `GL(U)`. -/
theorem step6_subgroup_eq_top {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [Module.Finite (ZMod 2) U] (hU : Module.finrank (ZMod 2) U = 3)
    (P : Subgroup (U ≃ₗ[ZMod 2] U))
    (hP : ∀ (X : Submodule (ZMod 2) U), Module.finrank (ZMod 2) X + 1 = Module.finrank (ZMod 2) U →
        ∀ a : U, a ∈ X → a ≠ 0 →
        ∃ τ ∈ P, (∀ x ∈ X, τ x = x) ∧
          ∃ c : U, c ∉ X ∧ ∃ w ∈ X, w ≠ 0 ∧ w ≠ a ∧ τ c = c + w) :
    P = ⊤ := by
  -- Every transvection lies in `P`.
  have htrans : LinearEquiv.transvections (ZMod 2) U ⊆ (P : Set (U ≃ₗ[ZMod 2] U)) := by
    intro e he
    rw [LinearEquiv.mem_transvections_iff] at he
    obtain ⟨f, v, hfv, rfl⟩ := he
    by_cases hf : f = 0
    · -- the zero functional gives the identity
      subst hf
      rw [transvection_eq_of_proof_irrel hfv (LinearMap.zero_apply v)]
      rw [LinearEquiv.transvection.of_left_eq_zero]
      exact Subgroup.one_mem P
    · -- the functional is nonzero, so its kernel `X` is a hyperplane
      set X : Submodule (ZMod 2) U := LinearMap.ker f with hX
      have hXfin : Module.finrank (ZMod 2) X + 1 = Module.finrank (ZMod 2) U := by
        rw [hX]; exact Module.Dual.finrank_ker_add_one_of_ne_zero hf
      have hX2 : Module.finrank (ZMod 2) X = 2 := by omega
      -- a nonzero vector of `X`
      obtain ⟨a, haX, ha0⟩ : ∃ a : U, a ∈ X ∧ a ≠ 0 := by
        by_contra h
        push Not at h
        have hbot : X = ⊥ := by
          ext x
          exact ⟨fun hx => h x hx, fun hx => by rw [hx]; exact X.zero_mem⟩
        rw [hbot] at hX2
        simp at hX2
      -- first application of the hypothesis: a transvection `t_w` with `w ∈ X ∖ {0, a}`
      obtain ⟨τ₁, hτ₁P, hτ₁fix, c₁, hc₁X, w₁, hw₁X, hw₁0, _, hτ₁c⟩ := hP X hXfin a haX ha0
      have hw₁ker : f w₁ = 0 := LinearMap.mem_ker.mp (hX ▸ hw₁X)
      have hτ₁eq : τ₁ = LinearEquiv.transvection hw₁ker :=
        eq_transvection_of_fixes_coatom hXfin hX.symm hτ₁fix hc₁X hw₁ker hτ₁c
      rw [hτ₁eq] at hτ₁P
      -- second application, with `a := w₁`: another transvection of `P`, with `w₂ ≠ w₁`
      obtain ⟨τ₂, hτ₂P, hτ₂fix, c₂, hc₂X, w₂, hw₂X, hw₂0, hw₂w₁, hτ₂c⟩ :=
        hP X hXfin w₁ hw₁X hw₁0
      have hw₂ker : f w₂ = 0 := LinearMap.mem_ker.mp (hX ▸ hw₂X)
      have hτ₂eq : τ₂ = LinearEquiv.transvection hw₂ker :=
        eq_transvection_of_fixes_coatom hXfin hX.symm hτ₂fix hc₂X hw₂ker hτ₂c
      rw [hτ₂eq] at hτ₂P
      have hw₁₂ : w₁ ≠ w₂ := fun h => hw₂w₁ h.symm
      -- `X = span {w₁, w₂}`, so every vector of `X` is `0`, `w₁`, `w₂` or `w₁ + w₂`
      have hspan : X = Submodule.span (ZMod 2) ({w₁, w₂} : Set U) := by
        refine (Submodule.eq_of_le_of_finrank_eq (S₁ := Submodule.span (ZMod 2) ({w₁, w₂} : Set U))
          (S₂ := X) ?_ ?_).symm
        · rw [Submodule.span_le]
          rintro x (rfl | rfl)
          · exact hw₁X
          · exact hw₂X
        · have hli : LinearIndependent (ZMod 2) ![w₁, w₂] := by
            rw [linearIndependent_fin2]
            refine ⟨by simpa using hw₂0, ?_⟩
            intro c hc
            rcases zmod2_eq_zero_or_eq_one c with h0 | h1
            · rw [h0, zero_smul] at hc
              exact hw₁0 (by simpa using hc.symm)
            · rw [h1, one_smul] at hc
              exact hw₁₂ (by simpa using hc.symm)
          have hr : Set.range ![w₁, w₂] = ({w₁, w₂} : Set U) := by
            ext x
            simp [or_comm]
          rw [← hr, finrank_span_eq_card hli, Fintype.card_fin, hX2]
      -- `v ∈ X`, so `v = k₁ • w₁ + k₂ • w₂`
      have hvX : v ∈ X := by rw [hX]; exact LinearMap.mem_ker.mpr hfv
      have hvspan : v ∈ Submodule.span (ZMod 2) ({w₁, w₂} : Set U) := by
        rw [← hspan]; exact hvX
      rw [Submodule.mem_span_pair] at hvspan
      obtain ⟨k₁, k₂, hk⟩ := hvspan
      rcases zmod2_eq_zero_or_eq_one k₁ with hk₁ | hk₁ <;>
        rcases zmod2_eq_zero_or_eq_one k₂ with hk₂ | hk₂
      · -- `v = 0`: the transvection is the identity
        have hv0 : v = 0 := by rw [hk₁, hk₂] at hk; simpa using hk.symm
        subst hv0
        rw [transvection_eq_of_proof_irrel hfv (f.map_zero)]
        rw [LinearEquiv.transvection.of_right_eq_zero]
        exact Subgroup.one_mem P
      · -- `v = w₂`
        have hv2 : v = w₂ := by rw [hk₁, hk₂] at hk; simpa using hk.symm
        subst hv2
        rw [transvection_eq_of_proof_irrel hfv hw₂ker]
        exact hτ₂P
      · -- `v = w₁`
        have hv1 : v = w₁ := by rw [hk₁, hk₂] at hk; simpa using hk.symm
        subst hv1
        rw [transvection_eq_of_proof_irrel hfv hw₁ker]
        exact hτ₁P
      · -- `v = w₁ + w₂`: the transvection is the product of the two others
        have hv12 : v = w₁ + w₂ := by rw [hk₁, hk₂] at hk; simpa using hk.symm
        subst hv12
        have hsum : f (w₁ + w₂) = 0 := by rw [map_add, hw₁ker, hw₂ker, add_zero]
        have hprod : LinearEquiv.transvection hw₁ker * LinearEquiv.transvection hw₂ker ∈ P :=
          Subgroup.mul_mem P hτ₁P hτ₂P
        have heq : LinearEquiv.transvection hw₁ker * LinearEquiv.transvection hw₂ker
            = LinearEquiv.transvection hsum := by
          rw [LinearEquiv.mul_eq_trans]
          exact LinearEquiv.transvection.trans_of_left_eq hw₁ker hw₂ker hsum
        rw [transvection_eq_of_proof_irrel hfv hsum, ← heq]
        exact hprod
  -- The closure of the transvections is everything, and it is contained in `P`.
  have hle : Subgroup.closure (LinearEquiv.transvections (ZMod 2) U) ≤ P :=
    (Subgroup.closure_le P).mpr htrans
  rw [closure_transvections_eq_top (V := U) (by omega)] at hle
  exact eq_top_iff.mpr hle

end Work.Hering.Wagner
