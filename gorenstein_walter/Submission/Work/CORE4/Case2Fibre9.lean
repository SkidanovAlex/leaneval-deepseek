import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2ECommute9
import Submission.Work.CORE4.Case2CentCard
import Submission.Work.CORE4.Case2ParityQOf
import Submission.Work.CORE4.ProjOfInfBot
import Submission.Work.CORE4.CountFibre
import Submission.Work.CORE4.Case2Count11
import Submission.Work.CORE4.Fibre9SupProj
import Submission.Work.CORE4.Fibre9ImageCard
import Submission.Work.CORE4.Fibre9Commute
import Submission.Work.CORE4.Fibre9CardConj

namespace Work.CORE4

variable {G : Type} [Group G] [Finite G]

open Subgroup

/-- **The fibre structure of `𝓓 = {conjugates of P inside P ⊔ E(M)}`.**  Two conjugates `Y ≠ P`,
`Z ≠ P` of `P`, both inside `W = P ⊔ E(M)`, that commute generate the same `(p,p)`-group with `P`:
`P ⊔ Y = P ⊔ Z`; equivalently their images in `E(M)` coincide.  Route: the projection
`π : ↥(P ⊔ E(M)) →* ↥E(M)` of `ProjOfInfBot` (`P` is abelian, `P ⟂ E(M)` elementwise and
`P ⊓ E(M) = ⊥`), `Case2CentCard.commute_iff_proj` (two elements of `P × E(M)` commute iff their
`E(M)`-coordinates do) and `Case2ECommute9` (two commuting order-`p` subgroups of `E(M)` coincide);
finally `Y ≤ P · πY`, so `P ⊔ Y = P ⊔ πY`. -/
theorem Case2Fibre9 (I : Work.GW2.C4Inputs) {B : Work.GW2.BenderSetup G}
    (hbc : Work.GW2.BenderCtx G) (h2 : Work.GW2.Case2 B) (h : Work.GW2.Case2Ctx B)
    (hplus : Work.GW2.Case2PrePlus B h.D)
    (h7 : Work.GW2.Case2SevenFacts B h.D) (h8 : Work.GW2.Case2EightAll B h.D)
    (p : ℕ) (P : Subgroup G) (hpp : p.Prime) (hPF : P ≤ h.D.F) (hPcard : Nat.card P = p)
    (Y Z : Subgroup G) (hYle : Y ≤ P ⊔ Work.GW2.layerIn h.D.M)
    (hZle : Z ≤ P ⊔ Work.GW2.layerIn h.D.M)
    (hYc : ∃ g : G, Y = Work.GW2.conjSub g P) (hZc : ∃ g : G, Z = Work.GW2.conjSub g P)
    (hYne : Y ≠ P) (hZne : Z ≠ P)
    (hcomm : Y ≤ Subgroup.centralizer (Z : Set G)) :
    P ⊔ Y = P ⊔ Z := by
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
    exact center_eq_bot_of_mulEquiv φ (center_PSL2_bot pF kF hpFodd (by omega))
  have hPEinf : P ⊓ E = ⊥ :=
    inf_eq_bot_of_le_centralizer
      (fun x hx => Subgroup.mem_centralizer_iff.mpr (fun y hy => (hPcomm x hx y hy).symm)) hcenterE
  -- The projection `π : ↥(P ⊔ E) →* ↥E` along `P`
  obtain ⟨π, hπ⟩ := ProjOfInfBot P E hPcomm hPEinf
  have hproj : ∀ x : ↥(P ⊔ E), (x : G) * (((π x : ↥E) : G))⁻¹ ∈ P :=
    proj_mul_inv_mem hPcomm π hπ
  -- `Y` and `Z` have order `p` and meet `P` trivially
  obtain ⟨hYcard, hYPbot⟩ := Fibre9CardConj hpp hPcard hYc hYne
  obtain ⟨hZcard, hZPbot⟩ := Fibre9CardConj hpp hPcard hZc hZne
  -- the images `πY` and `πZ`, as subgroups of `G`
  set Yim : Subgroup G := Subgroup.map E.subtype ((Y.subgroupOf (P ⊔ E)).map π) with hYim
  set Zim : Subgroup G := Subgroup.map E.subtype ((Z.subgroupOf (P ⊔ E)).map π) with hZim
  have hYimcard : Nat.card ↥Yim = p := by
    rw [hYim]
    rw [Fibre9ImageCard (P := P) (E := E) (X := Y) π hproj hYle' hYPbot, hYcard]
  have hZimcard : Nat.card ↥Zim = p := by
    rw [hZim]
    rw [Fibre9ImageCard (P := P) (E := E) (X := Z) π hproj hZle' hZPbot, hZcard]
  have hYimE : Yim ≤ E := by rw [hYim]; exact Subgroup.map_subtype_le _
  have hZimE : Zim ≤ E := by rw [hZim]; exact Subgroup.map_subtype_le _
  have hYimleM : Yim ≤ Work.GW2.layerIn h.D.M := by rw [hE] at hYimE; exact hYimE
  have hZimleM : Zim ≤ Work.GW2.layerIn h.D.M := by rw [hE] at hZimE; exact hZimE
  have hYimcent : Yim ≤ Subgroup.centralizer (Zim : Set G) :=
    Fibre9Commute (P := P) (E := E) (Y := Y) (Z := Z) hPcomm hPab π hπ hYle' hZle' hcomm
  -- two commuting order-`p` subgroups of `E ≅ L₂(q)` coincide
  have him_eq : Yim = Zim := Case2ECommute9 I hbc h2 h hplus h7 h8 p P hpp hPF hPcard
    Yim Zim hYimleM hZimleM hYimcard hZimcard hYimcent
  -- `π` does not change the join with `P`
  have hPY : P ⊔ Y = P ⊔ Yim := Fibre9SupProj (P := P) (E := E) (Y := Y) π hproj hYle'
  have hPZ : P ⊔ Z = P ⊔ Zim := Fibre9SupProj (P := P) (E := E) (Y := Z) π hproj hZle'
  rw [hPY, hPZ, him_eq]

end Work.CORE4
