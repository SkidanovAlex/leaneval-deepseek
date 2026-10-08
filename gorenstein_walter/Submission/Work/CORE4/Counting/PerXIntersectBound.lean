import Mathlib
import Submission.Work.CORE4.Case2PerXBound9
import Submission.Work.CORE4.Case2CountAssembly
import Submission.Work.CORE4.Case2Fibre9
import Submission.Work.CORE4.Counting.EConjLayerIn
import Submission.Work.CORE4.Case2Count11
import Submission.Work.CORE4.Case2EightObjExists
import Submission.Work.CORE4.Counting.FibreCtx

namespace Work.CORE4.Counting

open Subgroup

variable {G : Type} [Group G] [Finite G]

set_option linter.unusedSectionVars false in
/-- Conjugation transports the relation `A ≤ C_G(B)` to the conjugates: if `A` commutes
elementwise with `B`, then `A^e` commutes elementwise with `B^e`. -/
theorem conjSub_le_centralizer_of_le {A B : Subgroup G} {e : G}
    (h : A ≤ Subgroup.centralizer (B : Set G)) :
    Work.GW2.conjSub e A ≤
      Subgroup.centralizer (((Work.GW2.conjSub e B : Subgroup G)) : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hc : b * a = a * b := Subgroup.mem_centralizer_iff.mp (h ha) b hb
  calc e * b * e⁻¹ * (e * a * e⁻¹) = e * (b * a) * e⁻¹ := by group
    _ = e * (a * b) * e⁻¹ := by rw [hc]
    _ = e * a * e⁻¹ * (e * b * e⁻¹) := by group

theorem PerXIntersectBound (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) (k k' p : ℕ)
        (P A : Subgroup G),
        Even k → Odd k' →
        ((2 * k = Work.CORE4.qOf h + 1 ∧ 2 * k' = Work.CORE4.qOf h - 1) ∨
          (2 * k = Work.CORE4.qOf h - 1 ∧ 2 * k' = Work.CORE4.qOf h + 1)) →
        k = Nat.card ↥h.D.K * Nat.card ↥B.S0 →
        p.Prime → P ≤ h.D.F → Nat.card ↥P = p → Work.GW2.Case2EightObj h.D p P A →
        ∀ g : G, Work.GW2.conjSub g P ≠ P → Work.GW2.conjSub g P ≤ A →
          {Y : Subgroup G | Y ∈ Work.CORE4.inConjSet P (Work.GW2.layerIn h.D.M) ∧
              Y ∈ Work.GW2.conjSub g '' Work.CORE4.inConjSet P (Work.GW2.layerIn h.D.M) ∧
              Y ≠ Work.GW2.conjSub g P}.ncard ≤ Work.GW2.Case2EightP1 P A - 1 := by
  intro G _ _ hbc B h k k' p P A hkeven hkodd hcases hkK hp hPF hPcard hObj g hXne hXleA
  classical
  -- ## The environment
  set E : Subgroup G := Work.GW2.layerIn h.D.M with hE
  set X : Subgroup G := Work.GW2.conjSub g P with hX
  -- `A` is the `(p,p)`-group `P ⊔ (A ⊓ K)`, and `K ≤ E`, so `A ≤ P ⊔ E`.
  have hKE : h.D.K ≤ E := by rw [hE]; exact Work.CORE4.K_le_layerIn B h
  have hFK : h.D.F ⊓ h.D.K = ⊥ := Work.CORE4.F_inf_K_eq_bot_c4 B h.D
  have hcommFK : ∀ f ∈ h.D.F, ∀ c ∈ h.D.K, f * c = c * f :=
    Work.CORE4.F_commute_K_c4 I B h.D h.pre
  have hPA : P ≤ A := hObj.2.2.2.2.2.2.1
  obtain ⟨hAeq, -⟩ :=
    Work.CORE4.eq_sup_inf_of_le_sup_of_card_eq_sq (F := h.D.F) (K := h.D.K)
      hp h.F_cyclic hFK hcommFK hObj.2.2.2.1 hObj.2.2.2.2.1 hObj.2.2.2.2.2.1 hPA hPF hPcard
  have hAle : A ≤ P ⊔ E := by
    rw [hAeq]
    exact sup_le le_sup_left (le_trans (le_trans inf_le_right hKE) le_sup_right)
  have hXW : X ≤ P ⊔ E := hXleA.trans hAle
  have hXneP : X ≠ P := hXne
  have hXc : ∃ g' : G, X = Work.GW2.conjSub g' P := ⟨g, hX⟩
  -- ## The geometric core: every element of the double image lies in `A`
  have hmain : ∀ Y : Subgroup G, Y ∈ Work.CORE4.inConjSet P E →
      Y ∈ Work.GW2.conjSub g '' Work.CORE4.inConjSet P E → Y ≠ X → Y ≤ A := by
    intro Y hY1 hY2 hYneX
    obtain ⟨hYleW, hYc⟩ := hY1
    obtain ⟨Z, hZmem, hZY⟩ := hY2
    -- `Y ≤ W^X` and `X ≤ W^X`, and `X` is central in `W^X = P^g ⊔ E^g`
    have hYleWX : Y ≤ Work.GW2.conjSub g (P ⊔ E) := by
      rw [← hZY]; exact Subgroup.map_mono hZmem.1
    have hXleWX : X ≤ Work.GW2.conjSub g (P ⊔ E) := by
      rw [hX]; exact Subgroup.map_mono le_sup_left
    have hPcent : P ≤ Subgroup.centralizer (((P ⊔ E : Subgroup G)) : Set G) := by
      rw [hE]; exact Work.CORE4.P_le_cent_sup h hPF
    have hXcent :
        X ≤ Subgroup.centralizer ((Work.GW2.conjSub g (P ⊔ E) : Subgroup G) : Set G) := by
      rw [hX]
      exact conjSub_le_centralizer_of_le (e := g) hPcent
    have hXCY : X ≤ Subgroup.centralizer (Y : Set G) :=
      hXcent.trans (Subgroup.centralizer_le hYleWX)
    have hYCX : Y ≤ Subgroup.centralizer (X : Set G) :=
      (Work.CORE4.le_centralizer_comm).mp hXCY
    -- `Y = P` is immediate; otherwise the fibre structure identifies `P ⊔ Y` with `P ⊔ X`
    rcases eq_or_ne Y P with hYP | hYP
    · rw [hYP]; exact hPA
    · have hfib : P ⊔ Y = P ⊔ X :=
        FibreCtx I G hbc B h p P hp hPF hPcard Y X hYleW hXW hYc hXc hYP hXneP hYCX
      calc Y ≤ P ⊔ Y := le_sup_right
        _ = P ⊔ X := hfib
        _ ≤ A := sup_le hPA hXleA
  -- ## Counting
  have hXmem : Work.GW2.conjSub g P ∈
      {Y : Subgroup G | Y ≤ A ∧ ∃ h' : G, Y = Work.GW2.conjSub h' P} :=
    ⟨hXleA, ⟨g, rfl⟩⟩
  have hsub : {Y : Subgroup G | Y ∈ Work.CORE4.inConjSet P (Work.GW2.layerIn h.D.M) ∧
        Y ∈ Work.GW2.conjSub g '' Work.CORE4.inConjSet P (Work.GW2.layerIn h.D.M) ∧
        Y ≠ Work.GW2.conjSub g P} ⊆
      ({Y : Subgroup G | Y ≤ A ∧ ∃ h' : G, Y = Work.GW2.conjSub h' P} \
        {Work.GW2.conjSub g P}) := by
    rintro Y ⟨hY1, hY2, hYne⟩
    refine ⟨⟨hmain Y hY1 hY2 ?_, hY1.2⟩, ?_⟩
    · exact hX.symm ▸ hYne
    · simpa using hYne
  calc {Y : Subgroup G | Y ∈ Work.CORE4.inConjSet P (Work.GW2.layerIn h.D.M) ∧
        Y ∈ Work.GW2.conjSub g '' Work.CORE4.inConjSet P (Work.GW2.layerIn h.D.M) ∧
        Y ≠ Work.GW2.conjSub g P}.ncard
      ≤ ({Y : Subgroup G | Y ≤ A ∧ ∃ h' : G, Y = Work.GW2.conjSub h' P} \
          {Work.GW2.conjSub g P}).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = ({Y : Subgroup G | Y ≤ A ∧ ∃ h' : G, Y = Work.GW2.conjSub h' P} :
          Set (Subgroup G)).ncard - 1 := Set.ncard_sdiff_singleton_of_mem hXmem
    _ = Work.GW2.Case2EightP1 P A - 1 := by rw [Work.GW2.Case2EightP1]

end Work.CORE4.Counting
