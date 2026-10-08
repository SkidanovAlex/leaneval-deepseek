import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.CentKpE
import Submission.Work.CORE4.Case2EightObjExists

namespace Work.CORE4

/-- The Dedekind (modular) identity for subgroups in the form used below: if `A` normalizes `B`
and `A ≤ C`, then `(A ⊔ B) ⊓ C = A ⊔ (B ⊓ C)`.  (The subgroup lattice of a group is modular,
but Mathlib has no `IsModularLattice (Subgroup G)` instance, so the identity is proved here from
`Subgroup.coe_mul_of_left_le_normalizer_right`.) -/
theorem sup_inf_assoc_of_le_normalizer {G : Type*} [Group G] {A B C : Subgroup G}
    (hN : A ≤ Subgroup.normalizer (B : Set G)) (hAC : A ≤ C) :
    (A ⊔ B) ⊓ C = A ⊔ (B ⊓ C) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxAB, hxC⟩ := Subgroup.mem_inf.mp hx
    have hx' : x ∈ (↑(A ⊔ B) : Set G) := hxAB
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A B hN] at hx'
    obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hx'
    have hbC : b ∈ C := by
      have : b = a⁻¹ * x := by rw [← hab]; group
      rw [this]
      exact C.mul_mem (C.inv_mem (hAC ha)) hxC
    rw [← hab]
    exact Subgroup.mul_mem_sup ha (Subgroup.mem_inf.mpr ⟨hb, hbC⟩)
  · exact sup_le (le_inf le_sup_left hAC) (le_inf (inf_le_left.trans le_sup_right) inf_le_right)

/-- **Bender 1981, §4, p. 227, the display `M^g ∩ P×E = N_{P×E}(X) = P K S₀ = C_{P×E}(A)` (the `C`-half).**

Let `E := layerIn h.D.M` (Bender's `E(M)`), `p` an odd prime, `P ≤ D.F` of order `p` (so
`P ≤ C_G(E)` by `Case2Pre.F_cent`, and `P ≤ B.U ⊓ E`-free: `P ≤ F ≤ U` while `F ⊓ E = ⊥`),
`Kp ≤ K₀ = F(U) ⊓ K` of order `p`, and `A = P ⊔ Kp` the `(p,p)`-subgroup of `F ⊔ K`.  Since `P`
commutes with `E`, the subgroup `P ⊔ E` is the internal direct product `P × E`; then

    C_{P ⊔ E}(A) = P ⊔ K ⊔ S₀,   with |P ⊔ K ⊔ S₀| = p · |K| · |S₀|  (= p k).

Route.  `C_{P⊔E}(P) = P ⊔ E` (as `P ≤ C_G(E)`), so
`C_{P⊔E}(A) = C_{P⊔E}(P) ⊓ C_{P⊔E}(Kp) = (P ⊔ E) ⊓ (P ⊔ C_E(Kp)) = P ⊔ C_E(Kp)` (Dedekind; the
peel step needs `P ≤ C_{P⊔E}(Kp)`, i.e. `P ≤ C_G(E)` and `Kp ≤ E`), and `C_E(Kp) = K ⊔ S₀` is
`Work.CORE4.CentKpE` (already proved), which also gives `K ≤ K ⊔ S₀ = C_E(Kp) ≤ E`.  Since
`S₀ ≤ E`, both `K ⊔ S₀ ≤ E`.

For the order: `P ⊓ E = ⊥` (`P ≤ F ≤ B.U` and `B.U ⊓ E = K`, with `F ⊓ K = ⊥`), so
`P ⊓ (K ⊔ S₀) ≤ P ⊓ E = ⊥`; and `K ⊓ S₀ = ⊥` (`K` is odd, `S₀` is a 2-group).  Hence
`|P ⊔ K ⊔ S₀| = p |K| |S₀|`.

(Alternative for `P ⊓ E = ⊥`: `P ⊓ E ≤ Z(E) = ⊥` via `h.nine` and the centre of `PSL(2,q)`.)

Together with `k = |K| |S₀|` (`Work.CORE4.Case2KmulS0`) this is the `|C_{P×E}(A)| = pk` of p. 227.

(The `X`-half of the display, `N_{P⊔E}(X) = P K S₀` for `X` a conjugate of `P`, additionally needs
the fusion data `A^g = A`, `P K = X K` of p. 227, which are not hypotheses here.) -/
theorem CentAPE (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) (p : ℕ)
        (P Kp A : Subgroup G),
        p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
        Kp ≤ Work.GW2.Case2Data.K0 h.D → Nat.card ↥Kp = p → A = P ⊔ Kp →
        Subgroup.centralizer (A : Set G) ⊓ (P ⊔ Work.GW2.layerIn h.D.M) = P ⊔ h.D.K ⊔ B.S0 ∧
        Nat.card ↥(P ⊔ h.D.K ⊔ B.S0) = p * Nat.card ↥h.D.K * Nat.card ↥B.S0 := by
  intro G _ _ hbc B h p P Kp A hpp hPle hPcard hKpK0 hKpcard hA
  have hKpK : Kp ≤ h.D.K := le_trans hKpK0 inf_le_right
  have hKE : h.D.K ≤ Work.GW2.layerIn h.D.M := K_le_layerIn B h
  have hKpE : Kp ≤ Work.GW2.layerIn h.D.M := le_trans hKpK hKE
  have hS0E : B.S0 ≤ Work.GW2.layerIn h.D.M := le_trans B.S0_le (S_le_layerIn h)
  have hKSE : h.D.K ⊔ B.S0 ≤ Work.GW2.layerIn h.D.M := sup_le hKE hS0E
  -- ## (1) centralizer facts
  have hPcentE : P ≤ Subgroup.centralizer (Work.GW2.layerIn h.D.M : Set G) :=
    le_trans hPle (Work.GW2.Case2Pre.F_cent B h.D h.pre)
  have hPcentKp : P ≤ Subgroup.centralizer (Kp : Set G) :=
    hPcentE.trans (Subgroup.centralizer_le (show (Kp : Set G) ⊆
      (Work.GW2.layerIn h.D.M : Set G) from fun x hx => hKpE hx))
  have hEcentP : Work.GW2.layerIn h.D.M ≤ Subgroup.centralizer (P : Set G) :=
    (Subgroup.le_centralizer_iff (H := Work.GW2.layerIn h.D.M) (K := P)).mpr hPcentE
  have hPcentP : P ≤ Subgroup.centralizer (P : Set G) :=
    le_trans hPle (CentKpE_le_centralizer_of_isCyclic h.F_cyclic hPle)
  have hPN : P ≤ Subgroup.normalizer (Work.GW2.layerIn h.D.M : Set G) :=
    hPcentE.trans (Subgroup.centralizer_le_normalizer _)
  have hCentKpE : Subgroup.centralizer (Kp : Set G) ⊓ Work.GW2.layerIn h.D.M = h.D.K ⊔ B.S0 :=
    CentKpE I G hbc B h p Kp hpp hKpK0 hKpcard
  have hmod : (P ⊔ Work.GW2.layerIn h.D.M) ⊓ Subgroup.centralizer (Kp : Set G)
      = P ⊔ (Work.GW2.layerIn h.D.M ⊓ Subgroup.centralizer (Kp : Set G)) :=
    sup_inf_assoc_of_le_normalizer hPN hPcentKp
  -- ## (2) the subgroup identity
  have hsupCP : P ⊔ (h.D.K ⊔ B.S0) ≤ Subgroup.centralizer (P : Set G) :=
    sup_le hPcentP (sup_le (hKE.trans hEcentP) (hS0E.trans hEcentP))
  have hmain : Subgroup.centralizer (A : Set G) ⊓ (P ⊔ Work.GW2.layerIn h.D.M)
      = P ⊔ h.D.K ⊔ B.S0 := by
    rw [hA, Subgroup.centralizer_sup]
    calc (Subgroup.centralizer (P : Set G) ⊓ Subgroup.centralizer (Kp : Set G)) ⊓
            (P ⊔ Work.GW2.layerIn h.D.M)
        = Subgroup.centralizer (P : Set G) ⊓
            (Subgroup.centralizer (Kp : Set G) ⊓ (P ⊔ Work.GW2.layerIn h.D.M)) :=
          inf_assoc _ _ _
      _ = Subgroup.centralizer (P : Set G) ⊓
            (P ⊔ (Work.GW2.layerIn h.D.M ⊓ Subgroup.centralizer (Kp : Set G))) := by
          rw [inf_comm (Subgroup.centralizer (Kp : Set G)) (P ⊔ Work.GW2.layerIn h.D.M), hmod]
      _ = Subgroup.centralizer (P : Set G) ⊓ (P ⊔ (h.D.K ⊔ B.S0)) := by
          rw [inf_comm (Work.GW2.layerIn h.D.M) (Subgroup.centralizer (Kp : Set G)), hCentKpE]
      _ = P ⊔ (h.D.K ⊔ B.S0) := inf_eq_right.mpr hsupCP
      _ = P ⊔ h.D.K ⊔ B.S0 := (sup_assoc P h.D.K B.S0).symm
  -- ## (3) the cardinality
  have hKS0bot : h.D.K ⊓ B.S0 = ⊥ := by
    have h' := inf_le_inf (Work.GW2.Case2Data.K_le_U B h.D) B.S0_le
    rw [Work.GW2.BenderSetup.U_inf_S B] at h'
    exact le_bot_iff.mp h'
  have hKN : h.D.K ≤ Subgroup.normalizer ((B.S0 : Subgroup G) : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (S0CentK I G hbc B h)).trans
      (Subgroup.centralizer_le_normalizer _)
  have hcardKS0 : Nat.card ↥(h.D.K ⊔ B.S0) = Nat.card ↥h.D.K * Nat.card ↥B.S0 :=
    card_sup_of_disjoint_normalizer hKS0bot hKN
  have hPEbot : P ⊓ (h.D.K ⊔ B.S0) = ⊥ := by
    have hle : P ⊓ (h.D.K ⊔ B.S0) ≤ h.D.F ⊓ h.D.K := by
      intro x hx
      obtain ⟨hxP, hxSup⟩ := Subgroup.mem_inf.mp hx
      refine Subgroup.mem_inf.mpr ⟨hPle hxP, ?_⟩
      have hxU : x ∈ B.U := Work.GW2.Case2Data.F_le_U B h.D (hPle hxP)
      exact U_inf_layerIn_le_K I hbc B h (Subgroup.mem_inf.mpr ⟨hxU, hKSE hxSup⟩)
    rw [F_inf_K_eq_bot_c4 B h.D] at hle
    exact le_bot_iff.mp hle
  have hPSup : P ≤ Subgroup.normalizer ((h.D.K ⊔ B.S0 : Subgroup G) : Set G) := by
    have h1 : P ≤ Subgroup.centralizer ((h.D.K : Subgroup G) : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (F_commute_K_c4 I B h.D h.pre x (hPle hx) k hk).symm
    have h2 : P ≤ Subgroup.centralizer ((B.S0 : Subgroup G) : Set G) :=
      hPcentE.trans (Subgroup.centralizer_le (show (B.S0 : Set G) ⊆
        (Work.GW2.layerIn h.D.M : Set G) from fun x hx => hS0E hx))
    have h3 : P ≤ Subgroup.centralizer (((h.D.K ⊔ B.S0 : Subgroup G)) : Set G) := by
      rw [Subgroup.centralizer_sup]
      exact le_inf h1 h2
    exact h3.trans (Subgroup.centralizer_le_normalizer _)
  have hcardP : Nat.card ↥(P ⊔ (h.D.K ⊔ B.S0)) = Nat.card ↥P * Nat.card ↥(h.D.K ⊔ B.S0) :=
    card_sup_of_disjoint_normalizer hPEbot hPSup
  have hcard : Nat.card ↥(P ⊔ h.D.K ⊔ B.S0) = p * Nat.card ↥h.D.K * Nat.card ↥B.S0 := by
    rw [show P ⊔ h.D.K ⊔ B.S0 = P ⊔ (h.D.K ⊔ B.S0) from (sup_assoc P h.D.K B.S0),
      hcardP, hcardKS0, hPcard, mul_assoc]
  exact ⟨hmain, hcard⟩

end Work.CORE4
