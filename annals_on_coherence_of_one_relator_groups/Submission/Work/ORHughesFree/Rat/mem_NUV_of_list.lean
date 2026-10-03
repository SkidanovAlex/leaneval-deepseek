import Mathlib
import Submission.Work.ORHughesFree.Rat.Xgen_mem_closure_iff
import Submission.Work.ORHughesFree.Rat.Ugen_mem_NUV_iff
import Submission.Work.ORHughesFree.Rat.Xgen_mem_NUV_iff
import Submission.Work.ORHughesFree.Rat.Orbit
import Submission.Work.ORHughesFree.Rat.FreeProduct.relNE_append
import Submission.Work.ORHughesFree.Rat.listProd_Xgen_eq_mk
import Submission.Work.ORHughesFree.Rat.Xgen_actR_actL_mul
import Submission.Work.ORHughesFree.Rat.mem_NUV_of_relNE

/-!
# The `V`-part of the `X`-part of `U ♮ X` is the orbit of the `A V`-words

An element of the `X`-part `XPart U` of the free product monoid `U ♮ X` is a word
`l = [x₁, …, xₙ]` of `X`-letters modulo the `U`-action `relNE`.  This file characterises when such
a class lies in the `V`-part `Orbit.NUV V`:

`[x₁, …, xₙ] ∈ NUV V`  iff  some `relNE`-equivalent word `l'` has *all* its letters in `Rat.A V`.

The construction of the representative is the first-letter recursion `Xgen_mem_closure_iff`, run
along the word: `Xgen x * q ∈ NUV V` produces `v : U` with `actR v x ∈ Rat.A V` and
`Ugen v⁻¹ * q ∈ NUV V`, and multiplying by `Ugen v⁻¹` on the left replaces the next letter `y` by
`actL v⁻¹ y` (and leaves the rest of the word alone).  The letters thus collected successively are
`actR v x`, and the word `actR v x :: m` obtained from the recursion is `relNE`-equivalent to the
original word because the two have the same value in `U ♮ X` (this is the identity
`Xgen (actR v x) * Xgen (actL v⁻¹ y) = Xgen x * Xgen y`).
-/

namespace Work.ORHughesFree.Rat

open Work.ORHughesFree
open Work.ORHughesFree.Rat.FreeProduct

variable {U : Type} [Group U]

/-! ### The product of the `X`-letters of a list -/

/-- `Q l` is the product in `U ♮ X` of the `X`-letters of the list `l`; for `l = []` it is `1`. -/
private noncomputable def Q (l : List (RatU U)) : FreeProduct.NU U :=
  (l.map FreeProduct.NU.Xgen).prod

private theorem Q_nil : Q ([] : List (RatU U)) = 1 := rfl

private theorem Q_cons (x : RatU U) (xs : List (RatU U)) :
    Q (x :: xs) = FreeProduct.NU.Xgen x * Q xs := by
  simp only [Q, List.map_cons, List.prod_cons]

/-- For a nonempty list, the product of its `X`-letters is the corresponding point of the
`X`-part of `U ♮ X`. -/
private theorem Q_eq_mk (l : List (RatU U)) (hl : l ≠ []) :
    Q l = (Sum.inr (Quotient.mk _ ⟨l, hl⟩) : FreeProduct.NU U) :=
  listProd_Xgen_eq_mk l hl

/-! ### The recursion along the word -/

/-- The main construction: if the product of the `X`-letters of a nonempty list `l` lies in the
`V`-part of `U ♮ X`, then some `relNE`-equivalent word has all its letters in `Rat.A V`. -/
private theorem exists_orbit_A (V : Subgroup U) :
    ∀ n, ∀ (l : List (RatU U)), l.length = n → ∀ (hl : l ≠ []),
      Q l ∈ Orbit.NUV V →
      ∃ (l' : List (RatU U)) (hl' : l' ≠ []),
        FreeProduct.relNE ⟨l, hl⟩ ⟨l', hl'⟩ ∧ ∀ x ∈ l', x ∈ A V := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro l hlen hl hmem
    cases l with
    | nil => exact absurd rfl hl
    | cons x xs =>
      cases xs with
      | nil =>
        -- `l = [x]`: the single letter is already in `A V`
        have hQx : Q [x] = FreeProduct.NU.Xgen x := by rw [Q_cons, Q_nil, mul_one]
        rw [hQx] at hmem
        have hx : x ∈ A V := (Xgen_mem_NUV_iff V x).mp hmem
        refine ⟨[x], hl, FreeProduct.relNE_refl _, ?_⟩
        intro z hz
        have hz' : z = x := by simpa using hz
        rw [hz']
        exact hx
      | cons y ys =>
        -- `l = x :: y :: ys`: peel off the first letter
        rw [Q_cons] at hmem
        obtain ⟨v, hv1, hv2⟩ := (Xgen_mem_closure_iff V x (Q (y :: ys))).mp hmem
        -- `Ugen v⁻¹` replaces the second letter `y` by `actL v⁻¹ y`
        have hv2' : FreeProduct.NU.Ugen v⁻¹ * (FreeProduct.NU.Xgen y * Q ys) ∈ Orbit.NUV V := by
          have h := hv2
          rw [Q_cons y ys] at h
          exact h
        have hmem2 : Q (FreeProduct.actL v⁻¹ y :: ys) ∈ Orbit.NUV V := by
          have he : Q (FreeProduct.actL v⁻¹ y :: ys)
              = (FreeProduct.NU.Ugen v⁻¹ * FreeProduct.NU.Xgen y) * Q ys := by
            rw [Q_cons, FreeProduct.NU.Ugen_mul_Xgen]
          rw [he, mul_assoc]
          exact hv2'
        have hl2 : (FreeProduct.actL v⁻¹ y :: ys) ≠ [] := by simp
        have hlen2 : (FreeProduct.actL v⁻¹ y :: ys).length = ys.length + 1 := rfl
        have hlt : ys.length + 1 < n := by
          simp only [List.length_cons] at hlen
          omega
        obtain ⟨m, hm, hrel2, hall2⟩ :=
          ih (ys.length + 1) hlt (FreeProduct.actL v⁻¹ y :: ys) hlen2 hl2 hmem2
        have hl'' : (FreeProduct.actR v x :: m) ≠ [] := by simp
        -- the two words have the same value in `U ♮ X`
        have hQm : Q m = Q (FreeProduct.actL v⁻¹ y :: ys) := by
          have h1 : (Sum.inr (Quotient.mk _ ⟨m, hm⟩) : FreeProduct.NU U)
              = Sum.inr (Quotient.mk _ ⟨FreeProduct.actL v⁻¹ y :: ys, hl2⟩) :=
            congrArg Sum.inr (Quotient.sound hrel2).symm
          rw [Q_eq_mk m hm, Q_eq_mk (FreeProduct.actL v⁻¹ y :: ys) hl2]
          exact h1
        have hQeq : Q (FreeProduct.actR v x :: m) = Q (x :: y :: ys) := by
          calc Q (FreeProduct.actR v x :: m)
              = FreeProduct.NU.Xgen (FreeProduct.actR v x) * Q m := Q_cons _ _
            _ = FreeProduct.NU.Xgen (FreeProduct.actR v x)
                  * Q (FreeProduct.actL v⁻¹ y :: ys) := by rw [hQm]
            _ = FreeProduct.NU.Xgen (FreeProduct.actR v x)
                  * (FreeProduct.NU.Xgen (FreeProduct.actL v⁻¹ y) * Q ys) := by rw [Q_cons]
            _ = (FreeProduct.NU.Xgen (FreeProduct.actR v x)
                  * FreeProduct.NU.Xgen (FreeProduct.actL v⁻¹ y)) * Q ys := by rw [mul_assoc]
            _ = (FreeProduct.NU.Xgen x * FreeProduct.NU.Xgen y) * Q ys := by
                  rw [Xgen_actR_actL_mul]
            _ = Q (x :: y :: ys) := by rw [Q_cons x (y :: ys), Q_cons y ys, mul_assoc]
        refine ⟨FreeProduct.actR v x :: m, hl'', ?_, ?_⟩
        · have hfin : (Sum.inr (Quotient.mk _ ⟨x :: y :: ys, hl⟩) : FreeProduct.NU U)
              = Sum.inr (Quotient.mk _ ⟨FreeProduct.actR v x :: m, hl''⟩) := by
            rw [← Q_eq_mk (x :: y :: ys) hl, ← hQeq,
              Q_eq_mk (FreeProduct.actR v x :: m) hl'']
          exact Quotient.exact (Sum.inr.inj hfin)
        · intro z hz
          rw [List.mem_cons] at hz
          rcases hz with rfl | hz
          · exact hv1
          · exact hall2 z hz

theorem mem_NUV_of_list {U : Type} [Group U] (V : Subgroup U) (l : List (Work.ORHughesFree.RatU U)) (hl : l ≠ []) :
    ((Sum.inr (Quotient.mk _ ⟨l, hl⟩) : Work.ORHughesFree.Rat.FreeProduct.NU U) ∈
        Work.ORHughesFree.Rat.Orbit.NUV V) ↔
      ∃ (l' : List (Work.ORHughesFree.RatU U)) (hl' : l' ≠ []),
        Work.ORHughesFree.Rat.FreeProduct.relNE ⟨l, hl⟩ ⟨l', hl'⟩ ∧
          ∀ x ∈ l', x ∈ Work.ORHughesFree.Rat.A V := by
  constructor
  · intro h
    rw [← Q_eq_mk l hl] at h
    exact exists_orbit_A V l.length l rfl hl h
  · rintro ⟨l', hl', hrel, hall⟩
    exact mem_NUV_of_relNE V hl hl' hrel hall

end Work.ORHughesFree.Rat
