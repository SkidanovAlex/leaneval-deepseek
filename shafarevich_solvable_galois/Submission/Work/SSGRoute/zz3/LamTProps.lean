import Mathlib
import Submission.Work.SSGRoute.zz3.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Properties of the left-nested bracket map `Λ` on the degree-`3` part

`Λ = LamT n` acts on `TT n = (Fin 3 → XX n) → ZMod 2` by

  `(Λ g)(x,y,z) = g(x,y,z) + g(y,x,z) + g(y,z,x) + g(z,y,x)`,

i.e. `Λ = Q id + Q sw01 + Q swcyc + Q sw02` where `Q α g = fun w => g (w ∘ α)`.

We prove the two structural facts used in the `(3,3)` diagonal graded step:

* `LamT_idem`  : `Λ` is idempotent (`Λ ∘ Λ = Λ`);
* `LamT_dTT_comm` : `Λ` commutes with the involution `dTT`.

Both are computations in the group ring of the four index permutations
`{id, sw01, swcyc, sw02} ⊆ Sym(3)`: multiplying this element by itself, every
product is one of the six permutations of `Fin 3`, the four elements of the set
occurring with odd multiplicity `3` and the two others (`lamT_sw12`, `lamT_sw2cyc`) with
even multiplicity `2`.  In characteristic `2` this gives `Λ ∘ Λ = Λ`.
-/

namespace Work.SSGRoute.ZZ3

/-! ## The composition table of the four index permutations -/

/-- The transposition of the last two entries. -/
def lamT_sw12 : Fin 3 → Fin 3 := ![0, 2, 1]

/-- The inverse three-cycle. -/
def lamT_sw2cyc : Fin 3 → Fin 3 := ![2, 0, 1]

theorem lamT_comp_sw01_sw01 : (sw01 ∘ sw01 : Fin 3 → Fin 3) = id := by decide

theorem lamT_comp_sw01_swcyc : (sw01 ∘ swcyc : Fin 3 → Fin 3) = lamT_sw12 := by decide

theorem lamT_comp_sw01_sw02 : (sw01 ∘ sw02 : Fin 3 → Fin 3) = lamT_sw2cyc := by decide

theorem lamT_comp_swcyc_sw01 : (swcyc ∘ sw01 : Fin 3 → Fin 3) = sw02 := by decide

theorem lamT_comp_swcyc_swcyc : (swcyc ∘ swcyc : Fin 3 → Fin 3) = lamT_sw2cyc := by decide

theorem lamT_comp_swcyc_sw02 : (swcyc ∘ sw02 : Fin 3 → Fin 3) = lamT_sw12 := by decide

theorem lamT_comp_sw02_sw01 : (sw02 ∘ sw01 : Fin 3 → Fin 3) = swcyc := by decide

theorem lamT_comp_sw02_swcyc : (sw02 ∘ swcyc : Fin 3 → Fin 3) = sw01 := by decide

theorem lamT_comp_sw02_sw02 : (sw02 ∘ sw02 : Fin 3 → Fin 3) = id := by decide

/-! ## Idempotence of `Λ` -/

/-- `Λ` is idempotent: expanding `Λ (Λ g)` into the sixteen terms
`g (w ∘ (α ∘ β))` (`α, β ∈ {id, sw01, swcyc, sw02}`) and pushing the composition
table through, each of `w`, `w ∘ sw01`, `w ∘ swcyc`, `w ∘ sw02` occurs three
times and `w ∘ lamT_sw12`, `w ∘ lamT_sw2cyc` twice; in `ZMod 2` the odd multiplicities
survive and the even ones cancel. -/
theorem LamT_idem (n : ℕ) (g : TT n) : LamT n (LamT n g) = LamT n g := by
  funext w
  simp only [LamT_apply, Function.comp_assoc, Function.comp_id,
    lamT_comp_sw01_sw01, lamT_comp_sw01_swcyc, lamT_comp_sw01_sw02,
    lamT_comp_swcyc_sw01, lamT_comp_swcyc_swcyc, lamT_comp_swcyc_sw02,
    lamT_comp_sw02_sw01, lamT_comp_sw02_swcyc, lamT_comp_sw02_sw02]
  ring_nf
  rw [show (3 : ZMod 2) = 1 from rfl, show (2 : ZMod 2) = 0 from rfl]
  ring

/-! ## Equivariance of `Λ` under the involution `dTT` -/

/-- `Λ` intertwines the involution `dTT` with itself: `dTT` acts on the index by
`w ↦ (i ↦ sg (w i))`, a pointwise operation which commutes with inserting one of
the fixed index permutations `sw01`, `swcyc`, `sw02` into `w`. -/
theorem LamT_dTT_comm (n : ℕ) (g : TT n) : LamT n (dTT n g) = dTT n (LamT n g) := by
  funext w
  simp only [LamT_apply, dTT_apply, Function.comp_def]

end Work.SSGRoute.ZZ3

namespace Work.SSGRoute.zz3

/-- `Λ` is an idempotent retraction onto the degree-`3` Lie part, equivariant
for the involution `dTT`. -/
theorem LamTProps (n : ℕ) :
    (∀ g : Work.SSGRoute.ZZ3.TT n, Work.SSGRoute.ZZ3.LamT n (Work.SSGRoute.ZZ3.LamT n g)
        = Work.SSGRoute.ZZ3.LamT n g) ∧
    (∀ g : Work.SSGRoute.ZZ3.TT n, Work.SSGRoute.ZZ3.LamT n (Work.SSGRoute.ZZ3.dTT n g)
        = Work.SSGRoute.ZZ3.dTT n (Work.SSGRoute.ZZ3.LamT n g)) :=
  ⟨fun g => Work.SSGRoute.ZZ3.LamT_idem n g,
   fun g => Work.SSGRoute.ZZ3.LamT_dTT_comm n g⟩

end Work.SSGRoute.zz3
