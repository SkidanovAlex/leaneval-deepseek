import Mathlib
import Submission.Work.CORE3.Case1aFrattiniApi
import Submission.Work.CORE3.Case1aSetup

namespace Work.CORE3

open Work.GW2
open Subgroup

/-! ## Support lemmas for `Work.CORE3.Case1aFrattiniSAct`

The two group-theoretic ingredients of Bender 1981, §3, p. 222 ("As `S` centralizes `U/F(U)`"):

* a reflection `x ∈ S − S₀` acts on `u ∈ U` through an element of `I_U(x) ⊆ F(U)`;
* conjugation by an element of `S ≤ N_G(U)` preserves `F(U)` (characteristic in `U`).

The assembly then writes `s ∈ S₀` as a product `x·y` of two reflections, so that
`u⁻¹ (s u s⁻¹) = (u⁻¹ (x u x⁻¹)) · x (u⁻¹ (y u y⁻¹)) x⁻¹` is a product of two `F(U)`-elements.
-/

/-- Under Case (1) of Theorem 2.10, for `x ∈ S − S₀` (a reflection of the dihedral Sylow
2-subgroup `S`) and `u ∈ U`, the commutator `u⁻¹ (x u x⁻¹)` lies in `F(U)`: Case (1) exhibits
`I_U(x)` as a Hall subgroup of `F(U)` (so `I_U(x) ⊆ F(U)`, definitionally), and `u⁻¹ (x u x⁻¹)`
lies in `I_U(x)` because `x` is an involution (`Work.CORE3.OutsideS0OrderTwo`). -/
theorem c1aSAct_reflection {G : Type} [Group G] [Finite G] (hBc : BenderCtx G)
    (B : BenderSetup G) (h1 : Case1 B) {x : G} (hxS : x ∈ (B.S : Subgroup G))
    (hxS0 : x ∉ B.S0) {u : G} (hu : u ∈ B.U) :
    u⁻¹ * (x * u * x⁻¹) ∈ fittingIn B.U := by
  obtain ⟨n, hn2, hdih⟩ := SylowDihedral G hBc B
  have hxord : orderOf x = 2 := OutsideS0OrderTwo G hBc B n hn2 hdih x hxS hxS0
  have hx2 : x * x = 1 := by
    have h : x ^ 2 = 1 := by rw [← hxord]; exact pow_orderOf_eq_one x
    simpa [pow_two] using h
  obtain ⟨Ix, hIxc, hHallx⟩ := h1.1 x hxS hxS0
  -- `x` normalizes `U`, so `u⁻¹ * (x * u * x⁻¹) ∈ U`
  have hxU : x ∈ Subgroup.normalizer (B.U : Set G) :=
    Work.CORE2A.bender_s_mem_normalizer_U B hxS
  have hmemU : u⁻¹ * (x * u * x⁻¹) ∈ B.U :=
    B.U.mul_mem (B.U.inv_mem hu) ((Subgroup.mem_normalizer_iff.mp hxU u).mp hu)
  -- and `x` inverts it, so it lies in `I_U(x) ⊆ F(U)`
  have hinv : x * (u⁻¹ * (x * u * x⁻¹)) * x⁻¹ = (u⁻¹ * (x * u * x⁻¹))⁻¹ :=
    c1aInverted_of_sq_eq_one hx2
  refine hHallx.1 ?_
  show u⁻¹ * (x * u * x⁻¹) ∈ (Ix : Set G)
  rw [hIxc]
  exact Work.CORE2A.mem_invSet.mpr ⟨hmemU, hinv⟩

/-- Conjugation by an element of `S ≤ N_G(U)` preserves `F(U)`: `F(U)` is characteristic in `U`
(`Work.CORE3.c1aConjSub_fittingIn_eq_self`) and `S ≤ H ≤ N_G(U)`. -/
theorem c1aSAct_conj {G : Type} [Group G] [Finite G] (B : BenderSetup G) {x : G}
    (hxS : x ∈ (B.S : Subgroup G)) {z : G} (hz : z ∈ fittingIn B.U) :
    x * z * x⁻¹ ∈ fittingIn B.U := by
  have hxU : x ∈ Subgroup.normalizer (B.U : Set G) :=
    Work.CORE2A.bender_s_mem_normalizer_U B hxS
  have hxU' : x⁻¹ ∈ Subgroup.normalizer (B.U : Set G) :=
    (Subgroup.normalizer (B.U : Set G)).inv_mem hxU
  have hFs : conjSub x⁻¹ (fittingIn B.U) = fittingIn B.U :=
    c1aConjSub_fittingIn_eq_self hxU'
  have hz' : z ∈ conjSub x⁻¹ (fittingIn B.U) := by rw [hFs]; exact hz
  exact (Work.CORE2A.mem_conjSub_iff' (g := x) (K := fittingIn B.U) (x := z)).mp hz'

/-- Bender 1981, §3, p. 222: "As `S` centralizes `U/F(U)`."  Under Case (1) of Theorem 2.10,
for every `s ∈ S − S₀` the set `invSet B.U s` is the underlying set of a Hall subgroup of `F(U)`,
so in particular `invSet B.U s ⊆ F(U)`; for `s` an involution (`orderOf s = 2` by
`Work.CORE3.OutsideS0OrderTwo` / `Work.CORE2A.dihedral_index_two`) this says that the commutator
`u⁻¹ * (s * u * s⁻¹)` lies in `F(U)`.  Since `S − S₀` is the non-trivial coset of the index-two
subgroup `S₀`, a product of two of its elements runs over all of `S₀`; a conjugation by an
element of `S ⊆ H` preserves `F(U)` because `F(U)` is characteristic in `U` (see
`Work.CORE3.c1aConjSub_fittingIn_eq_self`) and `U ◁ H`.

Deliverable: `Work.CORE3.SActsTriviallyModFitting B`, i.e. `∀ s ∈ S, ∀ u ∈ U,
u⁻¹ * (s * u * s⁻¹) ∈ fittingIn B.U`.

Useful existing lemmas: `Work.CORE3.c1aConjSub_fittingIn_eq_self`, `Work.CORE3.c1aFittingIn_le`,
`Work.CORE3.c1aLe_normalizer_pCoreIn`, `Work.CORE2A.bSetup_exists_mem_S_not_mem_S0`,
`Work.CORE3.OutsideS0OrderTwo`, `Work.CORE3.SylowDihedral`, and the toolkit `T.c15`
(`Coprime15Prop`, Bender 1.5(i)).  (A helper `U_conj_mem`, giving `h * u * h⁻¹ ∈ B.U` for
`h ∈ B.H`, `u ∈ B.U`, is already proved in `Submission/Work/CORE3/Case1aFrattini.lean`.) -/
theorem Case1aFrattiniSAct (G : Type) [Group G] [Finite G] (hFT : Work.GW2.FeitThompsonProp)
    (T : Work.GW2.LocalToolkit) (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (h1 : Work.GW2.Case1 B) : Work.CORE3.SActsTriviallyModFitting B := by
  intro s hsS u hu
  by_cases hs0 : s ∈ B.S0
  · -- `s ∈ S₀` is a product of two reflections `x`, `y` of `S − S₀`
    obtain ⟨y, hyS, hyS0⟩ := Work.CORE2A.bSetup_exists_mem_S_not_mem_S0 B
    set x : G := s * y⁻¹ with hxdef
    have hxS : x ∈ (B.S : Subgroup G) := by
      rw [hxdef]
      exact (B.S : Subgroup G).mul_mem hsS ((B.S : Subgroup G).inv_mem hyS)
    have hxS0 : x ∉ B.S0 := by
      intro hx
      refine hyS0 ?_
      have h : s⁻¹ * x ∈ B.S0 := B.S0.mul_mem (B.S0.inv_mem hs0) hx
      rw [hxdef, ← mul_assoc, inv_mul_cancel, one_mul] at h
      simpa using B.S0.inv_mem h
    have hs_eq : s = x * y := by rw [hxdef]; group
    have hA : u⁻¹ * (x * u * x⁻¹) ∈ fittingIn B.U :=
      c1aSAct_reflection hBc B h1 hxS hxS0 hu
    have hB' : u⁻¹ * (y * u * y⁻¹) ∈ fittingIn B.U :=
      c1aSAct_reflection hBc B h1 hyS hyS0 hu
    have hC : x * (u⁻¹ * (y * u * y⁻¹)) * x⁻¹ ∈ fittingIn B.U :=
      c1aSAct_conj B hxS hB'
    have hD : (u⁻¹ * (x * u * x⁻¹)) * (x * (u⁻¹ * (y * u * y⁻¹)) * x⁻¹) ∈ fittingIn B.U :=
      (fittingIn B.U).mul_mem hA hC
    rw [hs_eq]
    convert hD using 1
    group
  · -- `s ∈ S − S₀` is a reflection
    exact c1aSAct_reflection hBc B h1 hsS hs0 hu

end Work.CORE3
