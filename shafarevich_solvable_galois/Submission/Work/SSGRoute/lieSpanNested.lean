import Mathlib
import Submission.Work.SSGRoute.prop5.magLead_mem_nestedImage
import Submission.Work.SSGRoute.prop5.nestedLieDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The nested span equals the Lie span (clash-free copy)

In `prop5/magLead_mem_nestedImage.lean` the left-nested bracket monomials `lnMon w` are already
available together with `nestedSpan_bracket_le`; here we record the remaining elementary facts
relating the spans `nestedSpan X j` (of the `lnMon w`, `|w| = j`) and `lieSpan X j` (of the
`brkMon X c`, `size c = j`): `lnMon_mem_lieSpan`, `brkMon_mem_nestedSpan` and
`nestedSpan_eq_lieSpan`.
-/

noncomputable section

namespace Work.SSGRoute.prop5

variable {X : Type*}


/-- Left comb: `lcombAux t [y₁,…,yₖ] = [[[t,y₁],y₂],…,yₖ]`. -/
def lcombAux (X : Type*) : Magma X → List X → Magma X
  | t, [] => t
  | t, y :: rest => lcombAux X (Magma.mul t (Magma.gen y)) rest

theorem brkMon_lcombAux (X : Type*) :
    ∀ (t : Magma X) (l : List X),
      brkMon X (lcombAux X t l) =
        l.foldl (fun acc y => acc * wordEl (X := X) [y] - wordEl [y] * acc) (brkMon X t) := by
  intro t l
  induction l generalizing t with
  | nil => simp [lcombAux]
  | cons y rest ih =>
      rw [lcombAux, ih (Magma.mul t (Magma.gen y)), brkMon_mul, brkMon_gen]
      rfl

theorem size_lcombAux (X : Type*) :
    ∀ (t : Magma X) (l : List X), Magma.size (lcombAux X t l) = Magma.size t + l.length := by
  intro t l
  induction l generalizing t with
  | nil => simp [lcombAux]
  | cons y rest ih =>
      rw [lcombAux, ih, Magma.size_mul, Magma.size_gen]
      simp [Nat.add_assoc, Nat.add_comm]

/-- `lnMon` of a nonempty word is a bracket monomial of the same size. -/
theorem lnMon_mem_lieSpan (X : Type*) (w : List X) (j : ℕ) (hw : w.length = j) :
    lnMon w ∈ lieSpan X j := by
  cases w with
  | nil =>
      simp only [List.length_nil] at hw
      subst hw
      rw [show lnMon (X := X) [] = 0 from rfl]
      exact Submodule.zero_mem _
  | cons x rest =>
      refine Submodule.subset_span ⟨lcombAux X (Magma.gen x) rest, ?_, ?_⟩
      · rw [size_lcombAux, Magma.size_gen, ← hw]
        simp only [List.length_cons]
        omega
      · rw [brkMon_lcombAux]
        rfl


/-- Every bracket monomial lies in the nested span. -/
theorem brkMon_mem_nestedSpan (X : Type*) (c : Magma X) :
    brkMon X c ∈ nestedSpan (X := X) (Magma.size c) := by
  induction c with
  | gen x => exact Submodule.subset_span ⟨[x], rfl, rfl⟩
  | mul a b iha ihb =>
      rw [brkMon_mul, Magma.size_mul]
      exact nestedSpan_bracket_le iha ihb

theorem lieSpan_le_nestedSpan (X : Type*) (j : ℕ) :
    lieSpan X j ≤ nestedSpan (X := X) j := by
  refine Submodule.span_le.mpr ?_
  rintro a ⟨c, hc, rfl⟩
  rw [← hc]
  exact brkMon_mem_nestedSpan X c

theorem nestedSpan_le_lieSpan (X : Type*) (j : ℕ) :
    nestedSpan (X := X) j ≤ lieSpan X j := by
  refine Submodule.span_le.mpr ?_
  rintro a ⟨w, hw, rfl⟩
  exact lnMon_mem_lieSpan X w j hw

theorem nestedSpan_eq_lieSpan (X : Type*) (j : ℕ) :
    nestedSpan (X := X) j = lieSpan X j :=
  le_antisymm (nestedSpan_le_lieSpan X j) (lieSpan_le_nestedSpan X j)


end Work.SSGRoute.prop5
