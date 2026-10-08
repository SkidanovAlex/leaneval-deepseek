import Mathlib
import Submission.Work.CORE4.BadCountInH
import Submission.Work.CORE4.Case2PerXBound9

namespace Work.CORE4

open Subgroup

/-- Every `G`-conjugate of `P` inside `W = P ⊔ E(M)` that centralizes `A` lies in `A`.

Write `E := layerIn h.D.M`, so `𝓓 = inConjSet P E = {Z ≤ W : Z ~ P}` and `W = P ⊔ E` is the
direct product of `P` and `E` (`P` centralizes `E` and `P ⊓ E = ⊥`).  By `exists_Kp_A_eq`,
`A = P ⊔ Kp` with `Kp` the `p`-torsion of the cyclic `K`, `Kp ≤ E`.  For `Z ∈ 𝓓` centralizing `A`,
the `E`-projection `π Z` of `Z` along `W = P × E` is an order-`p` subgroup of `E` contained in
`C_G(Kp)` (`z * (π z)⁻¹ ∈ P` centralizes `Kp`); by `eq_Kp_of_le_centralizer_Kp` (uniqueness of the
order-`p` subgroup of `C_G(Kp) ⊓ E(M)`, a torus of `L₂(q)`) it equals `Kp`.  Finally
`Z ≤ P ⊔ πZ = P ⊔ Kp = A` (`Fibre9SupProj`).

This is exactly the `(p₁ − 1)` half used in `Work.CORE4.BadCountInH_first`; it uses no fusion data
beyond `Case2EightObj`. -/
lemma mem_A_of_mem_inConjSet {G : Type} [Group G] [Finite G]
    (I : Work.GW2.C4Inputs) (hbc : Work.GW2.BenderCtx G)
    {B : Work.GW2.BenderSetup G} (h : Work.GW2.Case2Ctx B)
    {p : ℕ} {P A : Subgroup G} (hp : p.Prime) (hPF : P ≤ h.D.F)
    (hPcard : Nat.card ↥P = p) (hObj : Work.GW2.Case2EightObj h.D p P A) :
    ∀ Z : Subgroup G, Z ∈ inConjSet P (Work.GW2.layerIn h.D.M) →
      Z ≤ Subgroup.centralizer (A : Set G) → Z ≤ A := by
  classical
  set E : Subgroup G := Work.GW2.layerIn h.D.M with hE
  intro Z hZ hZc
  obtain ⟨Kp, hKpK, hKpcard, hKpomega, hAeq⟩ := exists_Kp_A_eq I h hp hPF hPcard hObj
  obtain ⟨hpodd, hp2, hpFne⟩ := p_parity_facts I hbc h hp hPF hPcard hObj
  have hKpA : Kp ≤ A := by rw [hAeq]; exact le_sup_right
  haveI : Fact p.Prime := ⟨hp⟩
  -- `P` commutes with `E = E(M)`
  have hPcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    rw [hE] at hy
    exact (Subgroup.mem_centralizer_iff.mp
      (Work.GW2.Case2Pre.F_cent B h.D h.pre (hPF hx)) y hy).symm
  -- `Z(E(M)) = 1` (the layer is `L₂(q)`), so `P ⊓ E = ⊥`
  have hcenterE : Subgroup.center ↥E = ⊥ := by
    obtain ⟨pF, kF, hpF, hpFodd, h7q, hφ, -⟩ := h.nine
    haveI : Fact pF.Prime := hpF
    obtain ⟨φ⟩ := hφ
    rw [hE]
    exact Work.CORE4.center_eq_bot_of_mulEquiv φ
      (Work.CORE4.center_PSL2_bot pF kF hpFodd (by omega))
  have hPEinf : P ⊓ E = ⊥ :=
    Work.CORE4.inf_eq_bot_of_le_centralizer
      (fun x hx => Subgroup.mem_centralizer_iff.mpr (fun y hy => (hPcomm x hx y hy).symm))
      hcenterE
  -- the projection `π : ↥(P ⊔ E) →* ↥E` of the direct product `W = P × E`
  obtain ⟨π, hπ⟩ := Work.CORE4.ProjOfInfBot P E hPcomm hPEinf
  have hproj : ∀ x : ↥(P ⊔ E), (x : G) * (((π x : ↥E) : G))⁻¹ ∈ P :=
    Work.CORE4.proj_mul_inv_mem hPcomm π hπ
  -- `P` centralizes `Kp ≤ E`
  have hPcentKp : P ≤ Subgroup.centralizer (Kp : Set G) := by
    have hPcentE : P ≤ Subgroup.centralizer (Work.GW2.layerIn h.D.M : Set G) :=
      hPF.trans (Work.GW2.Case2Pre.F_cent B h.D h.pre)
    have hKpE : Kp ≤ Work.GW2.layerIn h.D.M := hKpK.trans (Work.CORE4.K_le_layerIn B h)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp (hPcentE hx) y (hKpE hy)
  obtain ⟨hZle, hZconj⟩ := hZ
  by_cases hZP : Z = P
  · rw [hZP]; exact hObj.2.2.2.2.2.2.1
  · -- `Z` has order `p` and meets `P` trivially
    obtain ⟨hZcard, hZbot⟩ := Work.CORE4.Fibre9CardConj hp hPcard hZconj hZP
    -- the image `Yim = πZ ≤ E(M)`
    set Yim : Subgroup G := Subgroup.map E.subtype ((Z.subgroupOf (P ⊔ E)).map π) with hYim
    have hYimcard : Nat.card ↥Yim = p := by
      rw [hYim, Work.CORE4.Fibre9ImageCard (P := P) (E := E) (X := Z) π hproj hZle hZbot,
        hZcard]
    have hYimE : Yim ≤ Work.GW2.layerIn h.D.M := by
      rw [hYim]
      exact (Subgroup.map_subtype_le _).trans (le_of_eq hE)
    -- `Yim` commutes with `Kp`
    have hYimcent : Yim ≤ Subgroup.centralizer (Kp : Set G) := by
      rw [hYim]
      intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨e, he, rfl⟩ := hy
      rw [Subgroup.mem_map] at he
      obtain ⟨x, hx, hxval⟩ := he
      rw [Subgroup.mem_subgroupOf] at hx
      rw [← hxval]
      exact proj_mem_centralizer_Kp_bcih (P := P) (E := E) (Kp := Kp) (Z := Z) (A := A)
        hproj hZc hKpA hPcentKp hx
    -- uniqueness of the order-`p` subgroup of `C_G(Kp) ⊓ E(M)`
    have hYimKp : Yim = Kp :=
      eq_Kp_of_le_centralizer_Kp I hbc h hp ⟨hpodd, hp2, hpFne⟩ hKpK hKpcard hYimE hYimcard
        hYimcent
    calc Z ≤ P ⊔ Z := le_sup_right
      _ = P ⊔ Yim := Work.CORE4.Fibre9SupProj (P := P) (E := E) (Y := Z) π hproj hZle
      _ = P ⊔ Kp := by rw [hYimKp]
      _ = A := hAeq.symm

end Work.CORE4
