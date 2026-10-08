import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Counting.Count11
import Submission.Work.CORE4.Counting.Fibre11P
import Submission.Work.CORE4.Case2EHcard
import Submission.Work.CORE4.Case2EightObjExists

namespace Work.CORE4.Counting

/-- **Bender §4 (11) in the §4 configuration.**  Let `E := layerIn h.D.M` (Bender's `E(M)`), `p` a prime, `P ≤ D.F` of order `p`, `Kp ≤ D.K0` of order `p` (`Kp` is the order-`p` subgroup of `K₀ = F(U) ⊓ K` provided by `PrimeDvdFK0` plus Cauchy), `A := P ⊔ Kp` the `(p,p)`-subgroup of `F ⊔ K`, and `p1 := #{X ≤ A : X ~ P}`.  If also `E` acts transitively on its order-`p` subgroups and has `qk'` of them, then `P · E` (= `P ⊔ E`) contains exactly `(p1 - 1) * qk' + 1` conjugates of `P`.

This is the §4 instance of `Work.CORE4.Counting.Count11`; the two additional inputs are supplied by `EConjLayerIn` (transitivity, from `EConjPrime` transported along the §4 (9) isomorphism `E(M) ≃* PSL(2, GF pF kF)`) and by `Work.CORE4.L2PrimeCountTransfer` (`#{Y ≤ E : |Y| = p} = q k'`, given `p ∣ k`).

Proof route: apply `Count11` with `P`, `E := layerIn h.D.M`, `Kp`.  Need `P ⊓ E = ⊥`: `P ≤ D.F ≤ B.U` (`Case2Data.F_le_U`) and `B.U ⊓ layerIn D.M = D.K` (`Work.CORE4.U_inf_layerIn_le_K` with `Work.CORE4.K_le_layerIn`), while `D.F ⊓ D.K = ⊥` (`Work.CORE4.F_inf_K_eq_bot_c4`), so `D.F ⊓ E = ⊥` and hence `P ⊓ E = ⊥`.  Need `∀ x ∈ P, ∀ y ∈ E, x * y = y * x`: `P ≤ D.F ≤ centralizer E` (`Case2Pre.F_cent`). -/
theorem ElevenGW (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B)
        (p p1 qk' : ℕ) (P Kp : Subgroup G),
        p.Prime → P ≤ h.D.F → Nat.card ↥P = p → Kp ≤ h.D.K0 → Nat.card ↥Kp = p →
        (∀ Y : Subgroup G, Y ≤ Work.GW2.layerIn h.D.M → Nat.card ↥Y = p →
          ∃ e ∈ Work.GW2.layerIn h.D.M, Y = Work.GW2.conjSub e Kp) →
        (Work.CORE4.Counting.conjIn P Kp p).ncard = p1 →
        {Y : Subgroup G | Y ≤ Work.GW2.layerIn h.D.M ∧ Nat.card ↥Y = p}.ncard = qk' →
        {X : Subgroup G | Nat.card ↥X = p ∧ X ≤ P ⊔ Work.GW2.layerIn h.D.M ∧
          (∃ g : G, X = Work.GW2.conjSub g P)}.ncard = (p1 - 1) * qk' + 1 := by
  intro G _ _ hbc B h p p1 qk' P Kp hp hPF hPcard hKpK0 hKpcard hconj hbase hcount
  -- `K ≤ E(M)` and `Kp ≤ K₀ ≤ K ≤ E(M)`.
  have hKE : h.D.K ≤ Work.GW2.layerIn h.D.M := K_le_layerIn B h
  have hK0 : h.D.K0 ≤ h.D.K := by
    show Work.GW2.Case2Data.K0 h.D ≤ h.D.K
    rw [Work.GW2.Case2Data.K0]
    exact inf_le_right
  have hKpK : Kp ≤ h.D.K := hKpK0.trans hK0
  have hKpE : Kp ≤ Work.GW2.layerIn h.D.M := hKpK.trans hKE
  -- `U ⊓ E(M) = K`.
  have hUinfE : B.U ⊓ Work.GW2.layerIn h.D.M = h.D.K :=
    le_antisymm (U_inf_layerIn_le_K I hbc B h) (le_inf h.D.K_le_U hKE)
  -- `P ⊓ E(M) = ⊥`: `P ⊓ E ≤ F ⊓ K = ⊥`.
  have hPE : P ⊓ Work.GW2.layerIn h.D.M = ⊥ := by
    have h1 : P ⊓ Work.GW2.layerIn h.D.M ≤ h.D.F ⊓ h.D.K := by
      refine le_inf (le_trans inf_le_left hPF) ?_
      calc P ⊓ Work.GW2.layerIn h.D.M
          ≤ h.D.F ⊓ Work.GW2.layerIn h.D.M := inf_le_inf_right _ hPF
        _ ≤ B.U ⊓ Work.GW2.layerIn h.D.M := inf_le_inf_right _ (h.D.F_le_U B)
        _ = h.D.K := hUinfE
    exact le_bot_iff.mp (h1.trans (le_of_eq (F_inf_K_eq_bot_c4 B h.D)))
  -- `P` commutes elementwise with `E(M)` (both lie in the centralizer of `F`).
  have hcent : ∀ x ∈ P, ∀ y ∈ Work.GW2.layerIn h.D.M, x * y = y * x :=
    fun x hx y hy =>
      (Subgroup.mem_centralizer_iff.mp
        (Work.GW2.Case2Pre.F_cent B h.D h.pre (hPF hx)) y hy).symm
  -- Uniformity of the fibre counts over the order-`p` subgroups of `E(M)`.
  have hunif := fibreCount_conj_eq P (Work.GW2.layerIn h.D.M) Kp p hcent hconj
  have hbase' : ∀ Y : Subgroup G, Y ≤ Work.GW2.layerIn h.D.M → Nat.card ↥Y = p →
      {X : Subgroup G | Nat.card ↥X = p ∧ X ≤ P ⊔ Y ∧
        (∃ g : G, X = Work.GW2.conjSub g P)}.ncard = p1 :=
    fun Y hYE hYc => (hunif Y hYE hYc).trans hbase
  -- The fibre decomposition of Bender §4 (11).
  have hmain := Fibre11P P (Work.GW2.layerIn h.D.M) p p1 hp hPcard hPE hcent hbase'
  rw [hcount] at hmain
  exact hmain

end Work.CORE4.Counting
