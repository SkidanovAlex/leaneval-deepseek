import Mathlib
import Submission.Work.BrauerSuzuki.Q8.Vocab

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `1 ∉ B`

`B = Bset x` is the set of `G`-conjugates of the elements of `A* = C* \ (T · H*)`.
The identity lies in both `T = ⟨x²⟩` and `H* = O_{2'}(C*)`, hence `1 ∈ T · H*`, so `1 ∉ A*`.
Since conjugation fixes the identity, no conjugate of an element of `A*` can be `1` either,
i.e. `1 ∉ B`.

Note this needs neither finiteness of `G` nor the structural hypothesis `Ctx G x S`.
-/

set_option autoImplicit false

open scoped Pointwise

namespace Work.BrauerSuzuki.Q8

theorem step9_one_notMem_Bset {G : Type*} [Group G] {x : G} :
    (1 : G) ∉ Work.BrauerSuzuki.Q8.Bset x := by
  rintro ⟨a, ha, hconj⟩
  obtain ⟨haC, haT⟩ := ha
  -- `1 = 1 * 1 ∈ T · H*`
  have hone : (1 : G) ∈ (T x : Set G) * (Hstar x : Set G) := by
    rw [Set.mem_mul]
    exact ⟨1, (T x).one_mem, 1, (Hstar x).one_mem, one_mul 1⟩
  -- `a` is conjugate to `1`, hence `a = 1`
  have ha1 : a = 1 := by
    obtain ⟨c, hc⟩ := hconj
    rw [SemiconjBy] at hc
    have hc1 : c = a * c := by simpa using hc
    have h : (1 : G) * c = a * c := by rw [one_mul]; exact hc1
    exact (mul_right_cancel h).symm
  rw [ha1] at haT
  exact haT hone

end Work.BrauerSuzuki.Q8
