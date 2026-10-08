import Mathlib
import Submission.Work.ZJB2.Defs
import Submission.Work.GLUE.PcoreApi

/-!
# ZJB2 — leaf `mRCentralizes` (MRc): `[P, O_{p'}(N(R))] = 1`

Source: Glauberman 1968, p. 1121 (the proof of Theorem 5.2).  With `P = O_p(G)`,
`R = (P·C_G(P)) ∩ S` and `M = O_{p'}(N_G(R))`, the claim is `M ≤ C_G(P)`.

**Route.**  `R` is normal in `S` (it is `(P ⊔ C_G(P)) ⊓ S`, with `P ⊴ G`,
`C_G(P) ⊴ G`, hence `P ⊔ C_G(P) ⊴ G`), so `S ≤ N_G(R)`; and `P ≤ S` for every
Sylow `p`-subgroup (`O_p(G)` is normal).  Hence `P ≤ N_G(R)`, and in `H = N_G(R)`
both `P ⊓ H = P` and `O_{p'}(H)` are normal.  Their orders are coprime (one is a
`p`-group, the other a `p'`-group), so `P ⊓ O_{p'}(H) = ⊥`; as both are normal,
the commutator `⁅P, O_{p'}(H)⁆ ≤ P ⊓ O_{p'}(H) = ⊥`, i.e. `P` and `O_{p'}(H)`
commute elementwise.  Since `M` is the image of `O_{p'}(H)` in `G`, this is
`M ≤ C_G(P)`.
-/

namespace Work.ZJB2

open Subgroup

/-- `R = Rsub p G S` is normal in `S`: it is `(P ⊔ C_G(P)) ⊓ S`, the two factors
being normal in `G` (so normalized by `S`. -/
theorem sylow_le_normalizer_Rsub (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G]
    (S : Sylow p G) : (S : Subgroup G) ≤ Subgroup.normalizer (Work.ZJB.Rsub p G S : Set G) := by
  have hPC : (Work.GW2.pCore p G ⊔ Subgroup.centralizer (Work.GW2.pCore p G : Set G)).Normal :=
    inferInstance
  have hkey : ∀ s ∈ (S : Subgroup G), ∀ x ∈ Work.ZJB.Rsub p G S,
      s * x * s⁻¹ ∈ Work.ZJB.Rsub p G S := by
    intro s hs x hx
    exact ⟨hPC.conj_mem x hx.1 s,
      (S : Subgroup G).mul_mem ((S : Subgroup G).mul_mem hs hx.2) ((S : Subgroup G).inv_mem hs)⟩
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hkey s hs x
  · intro hx
    have h := hkey s⁻¹ ((S : Subgroup G).inv_mem hs) (s * x * s⁻¹) hx
    rwa [show s⁻¹ * (s * x * s⁻¹) * (s⁻¹)⁻¹ = x by group] at h

/-- `O_p(G) ≤ N_G(R)` (`O_p(G) ≤ S` and `S ≤ N_G(R)`). -/
theorem pCore_le_normalizer_Rsub (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G]
    (S : Sylow p G) :
    Work.GW2.pCore p G ≤ Subgroup.normalizer (Work.ZJB.Rsub p G S : Set G) :=
  le_trans (Work.GW2.pCore_le_sylow S) (sylow_le_normalizer_Rsub p G S)

/-- **The core of `mRCentralizes`.**  For any subgroup `N ≤ G` containing `P = O_p(G)`,
every element of the image of `O_{p'}(N)` in `G` centralizes `P`.

Mathematically: in `N` the subgroups `P` (normal, a `p`-group) and `O_{p'}(N)`
(normal, a `p'`-group) are of coprime order, hence have trivial intersection, hence
trivial commutator. -/
theorem commute_of_mem_map_opPrime (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G]
    (N : Subgroup G) (hP : Work.GW2.pCore p G ≤ N)
    {x : G} (hx : x ∈ (Work.ZJB.OpPrime p ↥N).map N.subtype) :
    x ∈ Subgroup.centralizer (Work.GW2.pCore p G : Set G) := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  -- Work inside `↥N`.
  let A : Subgroup ↥N := Subgroup.comap N.subtype (Work.GW2.pCore p G)
  let B : Subgroup ↥N := Work.ZJB.OpPrime p ↥N
  have hA_norm : A.Normal := Subgroup.Normal.comap (Work.GW2.pCore_normal p G) N.subtype
  have hB_norm : B.Normal := Work.ZJB.piCore_normal' {q : ℕ | q ≠ p} ↥N
  -- `A` is a `p`-group, `B` is a `p'`-group.
  have hA_pg : IsPGroup p ↥A := IsPGroup.comap_subtype (Work.GW2.pCore_isPGroup (G := G))
  have hB_pg : IsPGroup (Nat.card ↥B) ↥B := IsPGroup.card
  have hBpi : Subgroup.IsPiSubgroup {q : ℕ | q ≠ p} B := by
    show Subgroup.IsPiSubgroup {q : ℕ | q ≠ p} (Work.GW2.piCore {q : ℕ | q ≠ p} ↥N)
    rw [Work.GW2.piCore_eq_oPiCore]
    exact OddOrder.Isaacs.Ch03.oPiCore.isPiGroup {q : ℕ | q ≠ p}
  have hcop : Nat.Coprime p (Nat.card ↥B) := by
    rw [Nat.Prime.coprime_iff_not_dvd Fact.out]
    intro hdvd
    have hne : Nat.card ↥B ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
    have hmem : p ∈ (Nat.card ↥B).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨Fact.out, hdvd, hne⟩
    exact (hBpi p hmem) rfl
  have hdisj : Disjoint A B := IsPGroup.disjoint_of_coprime hA_pg hB_pg hcop
  have hinf : A ⊓ B = ⊥ := eq_bot_iff.mpr (disjoint_iff_inf_le.mp hdisj)
  -- Both normal: the commutator lies in the intersection, which is trivial.
  have hcomm : ⁅A, B⁆ = ⊥ := bot_unique (hinf ▸ Subgroup.commutator_le_inf A B)
  have hcent : A ≤ Subgroup.centralizer (B : Set ↥N) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have haN : (⟨a, hP ha⟩ : ↥N) ∈ A := ha
  have hcomm' : y * (⟨a, hP ha⟩ : ↥N) = (⟨a, hP ha⟩ : ↥N) * y :=
    Subgroup.mem_centralizer_iff.mp (hcent haN) y hy
  exact (congr_arg Subtype.val hcomm').symm

theorem mRCentralizes (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] : Work.ZJB.MRCentralizesProp p G := by
  show ∀ S : Sylow p G, Work.ZJB.MR p G S ≤ Subgroup.centralizer (Work.GW2.pCore p G : Set G)
  intro S x hx
  exact commute_of_mem_map_opPrime p G (Subgroup.normalizer (Work.ZJB.Rsub p G S : Set G))
    (pCore_le_normalizer_Rsub p G S) hx

end Work.ZJB2
