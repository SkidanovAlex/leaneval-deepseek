import Mathlib
import Submission.Work.ThmF.ChV3.Prove.OrbitCountDefs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

open Work.ThmF.ChV3

/-!
# `AT R T P ⊆ orb P (N_G(R))` from one witness

`Step11Out.reg` says that `C_Q(P)` acts sharply transitively on `AT R T P`: for `A, B` in `AT`
there is a *unique* `y ∈ C_Q(P)` with `A.map (conj y) = B`.  Hence conjugating a single member
`A₀ ∈ AT R T P` that already lies in the `N_G(R)`-orbit of `P` by `C_Q(P) ≤ C_G(P) ≤ N_G(R)`
reaches all of `AT R T P`, keeping us inside that orbit.
-/

/-- If one member `A₀` of `AT R T P` lies in the `N_G(R)`-orbit of `P`, then all of `AT R T P`
does. -/
theorem AT_subset_orb_of_witness_101 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {P R T : Subgroup G}
    (hRn : Work.ThmF.ChV3.CG P ≤ Work.ThmF.ChV3.NG R)
    (h11 : Work.ThmF.ChV3.Step11Out H Q t P R T)
    {A0 : Subgroup G} (hA0 : A0 ∈ Work.ThmF.ChV3.Prove.AT R T P)
    (hA0orb : A0 ∈ Work.ThmF.ChV3.Prove.orb P (Work.ThmF.ChV3.NG R)) :
    Work.ThmF.ChV3.Prove.AT R T P ⊆ Work.ThmF.ChV3.Prove.orb P (Work.ThmF.ChV3.NG R) := by
  classical
  -- the witness data of `A₀`
  obtain ⟨g0, hg0N, hg0⟩ := hA0orb
  -- the `AT`-data of `A₀`
  have hA0R : A0 ≤ R := hA0.1
  have hA0c : Nat.card A0 = Nat.card P := hA0.2.1
  have hA0T : ¬ A0 ≤ T := hA0.2.2.1
  have hA0P : A0 ≠ P := hA0.2.2.2
  -- `C_Q(P) ≤ C_G(P) ≤ N_G(R)`
  have hCQR : CQ Q P ≤ NG R := le_trans inf_le_right hRn
  intro A hA
  -- the `AT`-data of `A`
  have hAR : A ≤ R := hA.1
  have hAc : Nat.card A = Nat.card P := hA.2.1
  have hAT : ¬ A ≤ T := hA.2.2.1
  have hAP : A ≠ P := hA.2.2.2
  -- sharp transitivity: a `y ∈ C_Q(P)` with `cj y A₀ = A`
  obtain ⟨y, hy, -⟩ := h11.reg A0 A hA0R hAR hA0c hAc hA0T hAT hA0P hAP
  have hyA : cj (y : G) A0 = A := hy
  have hyN : (y : G) ∈ NG R := hCQR y.2
  -- then `A = cj (y * g₀) P` with `y * g₀ ∈ N_G(R)`
  refine ⟨(y : G) * g0, mul_mem hyN hg0N, ?_⟩
  have : cj ((y : G) * g0) P = A := by
    rw [cj_mul, ← hg0, hyA]
  exact this.symm

end Work.ThmF.ChV3.Prove
