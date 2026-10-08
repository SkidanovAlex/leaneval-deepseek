import Mathlib
import Submission.Work.CORE4.Counting.ECommuteCtx
import Submission.Work.CORE4.Case2Fibre9
import Submission.Work.CORE4.Fibre9SupProj
import Submission.Work.CORE4.Fibre9ImageCard
import Submission.Work.CORE4.Fibre9Commute
import Submission.Work.CORE4.Fibre9CardConj
import Submission.Work.CORE4.ProjOfInfBot
import Submission.Work.CORE4.CountFibre

namespace Work.CORE4.Counting

open Subgroup

set_option linter.style.haveILetI false

/-- **The fibre structure of `𝓓` at the `Case2Ctx` level.**  Two conjugates `Y ≠ P`, `Z ≠ P` of
`P` inside `W = P ⊔ E(M)` that commute generate the same `(p,p)`-group with `P`: `P ⊔ Y = P ⊔ Z`;
equivalently their images in `E(M) ≅ L₂(q)` coincide.

This is `Work.CORE4.Case2Fibre9` with its hypotheses `h2 : Case2 B`, `hplus : Case2PrePlus`,
`h7 : Case2SevenFacts`, `h8 : Case2EightAll` removed: that proof used them only to call
`Work.CORE4.Case2ECommute9`, whose single use of `h8` is the fact `p ∣ |K₀|` now supplied by
`Work.CORE4.Counting.ECommuteCtx` directly from `h : Case2Ctx B`.  Everything else in the proof
(the projection `π` of `ProjOfInfBot` with kernel `P`, `Fibre9ImageCard`, `Fibre9SupProj`,
`Fibre9Commute`, `Fibre9CardConj`, `center_eq_bot_of_mulEquiv` applied to the §4 (9) isomorphism
`E(M) ≃* PSL(2, GF pF kF)`) is available at the `Case2Ctx` level. -/
theorem FibreCtx (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B) (p : ℕ) (P : Subgroup G),
        p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
        ∀ Y Z : Subgroup G,
          Y ≤ P ⊔ Work.GW2.layerIn h.D.M → Z ≤ P ⊔ Work.GW2.layerIn h.D.M →
          (∃ g : G, Y = Work.GW2.conjSub g P) → (∃ g : G, Z = Work.GW2.conjSub g P) →
          Y ≠ P → Z ≠ P → Y ≤ Subgroup.centralizer (Z : Set G) →
          P ⊔ Y = P ⊔ Z := by
  intro G _ _ hbc B h p P hpp hPF hPcard Y Z hYle hZle hYc hZc hYne hZne hcomm
  classical
  -- The layer `E = E(M)` of `M`
  set E : Subgroup G := Work.GW2.layerIn h.D.M with hE
  have hYle' : Y ≤ P ⊔ E := by rw [hE]; exact hYle
  have hZle' : Z ≤ P ⊔ E := by rw [hE]; exact hZle
  -- `P` commutes with `E`, is commutative, and `P ⊓ E = ⊥` (the centre of `E ≅ L₂(q)` is trivial)
  have hPcomm : ∀ x ∈ P, ∀ y ∈ E, x * y = y * x := by
    intro x hx y hy
    rw [hE] at hy
    exact (Subgroup.mem_centralizer_iff.mp
      (Work.GW2.Case2Pre.F_cent B h.D h.pre (hPF hx)) y hy).symm
  have hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    haveI : IsMulCommutative ↥h.D.F := h.F_cyclic.isMulCommutative
    have hFc : h.D.F ≤ Subgroup.centralizer (h.D.F : Set G) := Subgroup.le_centralizer h.D.F
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp (hFc (hPF hx)) y (hPF hy)).symm
  have hcenterE : Subgroup.center ↥E = ⊥ := by
    obtain ⟨pF, kF, hpF, hpFodd, h7q, hφ, -⟩ := h.nine
    haveI : Fact pF.Prime := hpF
    obtain ⟨φ⟩ := hφ
    rw [hE]
    exact Work.CORE4.center_eq_bot_of_mulEquiv φ
      (Work.CORE4.center_PSL2_bot pF kF hpFodd (by omega))
  have hPEinf : P ⊓ E = ⊥ :=
    Work.CORE4.inf_eq_bot_of_le_centralizer
      (fun x hx => Subgroup.mem_centralizer_iff.mpr (fun y hy => (hPcomm x hx y hy).symm)) hcenterE
  -- The projection `π : ↥(P ⊔ E) →* ↥E` along `P`
  obtain ⟨π, hπ⟩ := Work.CORE4.ProjOfInfBot P E hPcomm hPEinf
  have hproj : ∀ x : ↥(P ⊔ E), (x : G) * (((π x : ↥E) : G))⁻¹ ∈ P :=
    Work.CORE4.proj_mul_inv_mem hPcomm π hπ
  -- `Y` and `Z` have order `p` and meet `P` trivially
  obtain ⟨hYcard, hYPbot⟩ := Work.CORE4.Fibre9CardConj hpp hPcard hYc hYne
  obtain ⟨hZcard, hZPbot⟩ := Work.CORE4.Fibre9CardConj hpp hPcard hZc hZne
  -- the images `πY` and `πZ`, as subgroups of `G`
  set Yim : Subgroup G := Subgroup.map E.subtype ((Y.subgroupOf (P ⊔ E)).map π) with hYim
  set Zim : Subgroup G := Subgroup.map E.subtype ((Z.subgroupOf (P ⊔ E)).map π) with hZim
  have hYimcard : Nat.card ↥Yim = p := by
    rw [hYim]
    rw [Work.CORE4.Fibre9ImageCard (P := P) (E := E) (X := Y) π hproj hYle' hYPbot, hYcard]
  have hZimcard : Nat.card ↥Zim = p := by
    rw [hZim]
    rw [Work.CORE4.Fibre9ImageCard (P := P) (E := E) (X := Z) π hproj hZle' hZPbot, hZcard]
  have hYimE : Yim ≤ E := by rw [hYim]; exact Subgroup.map_subtype_le _
  have hZimE : Zim ≤ E := by rw [hZim]; exact Subgroup.map_subtype_le _
  have hYimleM : Yim ≤ Work.GW2.layerIn h.D.M := by rw [hE] at hYimE; exact hYimE
  have hZimleM : Zim ≤ Work.GW2.layerIn h.D.M := by rw [hE] at hZimE; exact hZimE
  have hYimcent : Yim ≤ Subgroup.centralizer (Zim : Set G) :=
    Work.CORE4.Fibre9Commute (P := P) (E := E) (Y := Y) (Z := Z) hPcomm hPab π hπ
      hYle' hZle' hcomm
  -- two commuting order-`p` subgroups of `E ≅ L₂(q)` coincide
  have him_eq : Yim = Zim :=
    ECommuteCtx I G hbc B h p P hpp hPF hPcard
      Yim Zim hYimleM hZimleM hYimcard hZimcard hYimcent
  -- `π` does not change the join with `P`
  have hPY : P ⊔ Y = P ⊔ Yim :=
    Work.CORE4.Fibre9SupProj (P := P) (E := E) (Y := Y) π hproj hYle'
  have hPZ : P ⊔ Z = P ⊔ Zim :=
    Work.CORE4.Fibre9SupProj (P := P) (E := E) (Y := Z) π hproj hZle'
  rw [hPY, hPZ, him_eq]

end Work.CORE4.Counting
