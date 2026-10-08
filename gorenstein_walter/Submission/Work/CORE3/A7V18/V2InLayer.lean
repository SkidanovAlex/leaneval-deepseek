import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1aFrattini
import Submission.Work.CORE3.Case1aAbelian
import Submission.Work.CORE3.MData.MDataLayerLeLayerNormalizer
import Submission.Work.CORE2A.Basic

/-!
# CORE3 / A7V18: `V₂ = ⟨t, t₂⟩ ≤ E(M)` (Bender 1981, §3, p. 222)

Deliverable `Work.CORE3.A7V18.V2InLayer`: for a maximal `M ⊇ N_G(P₂)` (with
`P₂ ∈ Syl_p(C_U(S))`) in the subcase `Ĥ = H`, Bender's `V₂ = ⟨t, t₂⟩` lies in `E(M) = layerIn M`.

The plan is Bender's Lemma 2.9 (`I.h29`) with `V = V₂`, `N = M`:

* `P₂ ≤ C_U(S)` gives `S ≤ C_G(P₂) ≤ N_G(P₂) ≤ M`, so `V₂ ≤ S ≤ M` (`S_le_M`);
* `V₂` is a Klein four-group (`isFourGroup_V2`), so Lemma 2.9's disjunction applies;
* its first disjunct `V₂ ⊓ O₂(M) ≠ ⊥` forces `M = B.H` (`V2FirstDisjImpliesH`), which is
  incompatible with the hypothesis list (`V2NotH`), so the second disjunct holds;
* the second disjunct upgrades to the full containment `V₂ ≤ layerIn M`: `V₂` is abelian, so for
  `1 ≠ z ∈ V₂ ⊓ layerIn M` and `y ∈ V₂` one has `y = z * y * z⁻¹ ∈ layerIn M` (normal in `M`),
  which is `V2_le_layerIn_of_inf`.

The two cited modules (`V2FirstDisjImpliesH`, `V2NotH`) state the pieces of this argument about
`M` and `B.H`; they are being proved in parallel in this directory.
-/

namespace Work.CORE3.A7V18

open Subgroup
open Work.GW2

variable {G : Type} [Group G] [Finite G]

/-- `S ≤ M` for a maximal subgroup `M` containing `N_G(P₂)`, where `P₂ ≤ C_U(S)`: every element of
`S` centralizes `P₂` (as `P₂ ≤ C_G(S)`), so `S ≤ C_G(P₂) ≤ N_G(P₂) ≤ M`. -/
theorem S_le_M (B : BenderSetup G) {P2 M : Subgroup G}
    (hP2 : P2 ≤ B.U ⊓ centralizer ((B.S : Subgroup G) : Set G))
    (hNM : normalizer (P2 : Set G) ≤ M) : (B.S : Subgroup G) ≤ M := by
  have hSC : (B.S : Subgroup G) ≤ centralizer (P2 : Set G) := by
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hP2 hx).2 s hs).symm
  exact hSC.trans ((Subgroup.centralizer_le_normalizer (P2 : Set G)).trans hNM)

/-- `V₂ = ⟨t, t₂⟩` is a Klein four-group: `t` and `t₂` are distinct commuting involutions
(`t ∈ S₀` and `t₂ ∈ S - S₀`). -/
theorem isFourGroup_V2 (B : BenderSetup G) (D : Case1aData B) :
    IsFourGroup (Subgroup.zpowers B.t ⊔ Subgroup.zpowers D.t2 : Subgroup G) := by
  have hcomm : B.t * D.t2 = D.t2 * B.t :=
    Subgroup.mem_centralizer_iff.mp (Work.CORE2A.bSetup_S_le_H B D.t2_mem) B.t
      (Set.mem_singleton B.t)
  refine Work.CORE3.MData.isFourGroup_zpowers_sup (a := B.t) (b := D.t2) ?_ ?_ hcomm ?_ ?_ ?_
  · rw [← B.t_order]; exact pow_orderOf_eq_one B.t
  · rw [← D.t2_order]; exact pow_orderOf_eq_one D.t2
  · exact Work.CORE2A.bSetup_t_ne_one B
  · intro h
    have h2 : orderOf D.t2 = 2 := D.t2_order
    rw [h, orderOf_one] at h2
    exact absurd h2 (by norm_num)
  · intro h; exact D.t2_nmem (h ▸ B.t_mem)

/-- `V₂` is commutative, for `V₂` a Klein four-group. -/
theorem V2_mul_comm (B : BenderSetup G) (D : Case1aData B)
    (hV4 : IsFourGroup (Subgroup.zpowers B.t ⊔ Subgroup.zpowers D.t2 : Subgroup G)) :
    ∀ {a b : G}, a ∈ (Subgroup.zpowers B.t ⊔ Subgroup.zpowers D.t2 : Subgroup G) →
      b ∈ (Subgroup.zpowers B.t ⊔ Subgroup.zpowers D.t2 : Subgroup G) → a * b = b * a := by
  have hcomm := Work.CORE2A.IsFourGroup.isMulCommutative' hV4
  intro a b ha hb
  exact congrArg Subtype.val (hcomm.is_comm.comm (⟨a, ha⟩ : ↥(Subgroup.zpowers B.t ⊔
    Subgroup.zpowers D.t2 : Subgroup G)) (⟨b, hb⟩ : ↥(Subgroup.zpowers B.t ⊔
    Subgroup.zpowers D.t2 : Subgroup G)))

theorem V2InLayer (I : Work.CORE3.Case1Inputs) (hFr : Work.GW2.Case1aFrattiniProp)
    (hAb : Work.GW2.Case1aAbelianProp) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G,
      Work.GW2.Case1 B → B.Hhat = B.H → ∀ D : Work.GW2.Case1aData B, ∀ P2 M : Subgroup G,
        P2 ≤ B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) → IsPGroup D.p P2 →
        ¬ D.p ∣ P2.relIndex (B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G)) →
        IsCoatom M → Subgroup.normalizer (P2 : Set G) ≤ M →
        (Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G) ≠ ⊥ →
        (Subgroup.zpowers B.t ⊔ Subgroup.zpowers D.t2 : Subgroup G) ≤ Work.GW2.layerIn M := by
  sorry

end Work.CORE3.A7V18
