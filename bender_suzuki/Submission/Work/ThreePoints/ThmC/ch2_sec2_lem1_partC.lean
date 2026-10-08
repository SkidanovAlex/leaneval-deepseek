import Mathlib
import Submission.Work.ThreePoints.ThmC.app3_1_thm
import Submission.Work.DoubleTransitivity.Basic
import Submission.Work.DoubleTransitivity.Action

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints.ThmC

open Submission.Blueprint

/-- The fixed point set `Ω_P = fixedPts H P` of `P` is stable under `N_G(P)`: if `m` normalises
`P` and `ω` is fixed by `P`, then for every `p ∈ P`,
`p • (m • ω) = m • ((m⁻¹ p m) • ω) = m • ω`. -/
theorem fixedPts_smul_mem {G : Type} [Group G] {H P : Subgroup G} {m : G}
    (hm : m ∈ Subgroup.normalizer (P : Set G)) {ω : G ⧸ H}
    (hω : ω ∈ Submission.Blueprint.fixedPts H P) :
    m • ω ∈ Submission.Blueprint.fixedPts H P := by
  intro x hx
  have hx' : m⁻¹ * x * m ∈ P := ((Subgroup.mem_normalizer_iff.mp hm) (m⁻¹ * x * m)).mpr (by
    rw [show m * (m⁻¹ * x * m) * m⁻¹ = x from by group]; exact hx)
  calc x • (m • ω) = (x * m) • ω := by rw [mul_smul]
    _ = (m * (m⁻¹ * x * m)) • ω := by rw [show x * m = m * (m⁻¹ * x * m) from by group]
    _ = m • ((m⁻¹ * x * m) • ω) := by rw [mul_smul]
    _ = m • ω := by rw [hω _ hx']

/-- **Peterfalvi I Ch. II §2 Lemma 1 (c) (p. 164).**  Given parts (a) and (b), if `M = N_G(P)` has
2-rank `1` (`¬ HasFourGroup M`) then `P` is a `p`-Sylow of `D = twoPoint H g`.

Proof sketch (the source's).  It suffices to prove `N_D(P) = M ⊓ D ≤ conj u D = D^u`: then
`P ≤ N_D(P) ≤ D ⊓ D^u` and `P` is a `p`-Sylow of `D ⊓ D^u`, so `P` is a `p`-Sylow of `N_D(P)`,
hence of `D` (if `P < R` with `R` a `p`-subgroup of `D` then `P < N_R(P) ≤ N_D(P)`).

Apply Appendix III (1) (`Work.ThreePoints.ThmC.app3_1_thm`) with `F := M`, `A := fixedPts H P`,
`a := (g : G ⧸ H)` (so `Stab_F a = M ⊓ conj g H`), `t := u`, `b := (1 : G ⧸ H)`:
`M` acts transitively (indeed `2`-transitively, part (b)) on `Ω_P`, `M ⊓ conj g H` is strongly
embedded in `M` (part (b), using `P ≤ conj g H`) and maximal in `M` (a point stabiliser of a
`2`-transitive action is maximal), `¬ HasFourGroup M` is the hypothesis, and `u ∈ M` is an
involution with `u ∉ conj g H` (else the involution `u ∈ H ⊓ conj g H` would fix the two distinct
points `1, g`) whose unique fixed point in `Ω = G ⧸ H` is `1`.  The conclusion of App. III (1) is
`(M ⊓ conj g H) ⊓ conj u (M ⊓ conj g H) = (M ⊓ conj g H) ⊓ (M ⊓ H)`; since
`conj u (conj g H) = conj (u*g) H` and `conj u D = H ⊓ conj (u*g) H` (as `u ∈ H`), this yields
`M ⊓ H ⊓ conj g H ≤ conj (u*g) H`, i.e. `N_D(P) ≤ conj u D`. -/
theorem ch2_sec2_lem1_partC {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    (h2t : Submission.Blueprint.IsTwoTransitiveOn H)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hFT : Submission.Blueprint.FeitThompsonProp)
    {g : G} (hg : g ∉ H) {u : G} (hu : u ∈ Submission.Blueprint.involutions (H : Set G))
    {p : ℕ} (hp : p.Prime) (hpodd : p ≠ 2) {P : Subgroup G}
    (hP : Work.ThreePoints.ThmC.IsSylowOf p P
      (Submission.Blueprint.twoPoint H g ⊓
        Submission.Blueprint.conj u (Submission.Blueprint.twoPoint H g)))
    (huP : u ∈ Subgroup.normalizer (P : Set G))
    (hA : Work.ThreePoints.ThmC.IsMaxP3 H p P)
    (hB : Work.DoubleTransitivity.IsTwoTransitiveOnSub (Subgroup.normalizer (P : Set G))
        (Submission.Blueprint.fixedPts H P) ∧
      ∀ g₁ : G, P ≤ Submission.Blueprint.conj g₁ H →
        LeanEval.GroupTheory.Defs.IsStronglyEmbedded
          ((Subgroup.normalizer (P : Set G) ⊓ Submission.Blueprint.conj g₁ H).subgroupOf
            (Subgroup.normalizer (P : Set G)))) :
    ¬ Submission.Blueprint.HasFourGroup (Subgroup.normalizer (P : Set G)) →
      Work.ThreePoints.ThmC.IsSylowOf p P (Submission.Blueprint.twoPoint H g) := by
  intro hC
  classical
  set D : Subgroup G := Submission.Blueprint.twoPoint H g with hDdef
  set M : Subgroup G := Subgroup.normalizer (P : Set G) with hMdef
  set S : Set (G ⧸ H) := Submission.Blueprint.fixedPts H P with hSdef
  have huH : u ∈ H := hu.1
  have hu2 : orderOf u = 2 := hu.2
  have huM : u ∈ M := huP
  have hPD : P ≤ D := hP.1.trans inf_le_left
  have hPg : P ≤ Submission.Blueprint.conj g H := hPD.trans inf_le_right
  have hPH : P ≤ H := hPD.trans inf_le_left
  -- `N_G(P)` acts on the fixed point set `Ω_P = fixedPts H P` of `P`
  letI : SMul M ↥S := ⟨fun m ω => ⟨(m : G) • (ω : G ⧸ H), fixedPts_smul_mem m.2 ω.2⟩⟩
  letI : MulAction M ↥S :=
    { one_smul := fun ω => Subtype.ext (one_smul G (ω : G ⧸ H))
      mul_smul := fun m n ω => Subtype.ext (mul_smul (m : G) (n : G) (ω : G ⧸ H)) }
  have smul_val : ∀ (m : ↥M) (x : ↥S), ((m • x : ↥S) : G ⧸ H) = (m : G) • (x : G ⧸ H) :=
    fun m x => rfl
  have hga : (g : G ⧸ H) ∈ S := by
    rw [hSdef, Work.DoubleTransitivity.mk_mem_fixedPts_iff]; exact hPg
  have h1b : ((1 : G) : G ⧸ H) ∈ S := by
    rw [hSdef, Work.DoubleTransitivity.pt_mem_fixedPts_iff]; exact hPH
  let a : ↥S := ⟨(g : G ⧸ H), hga⟩
  let b : ↥S := ⟨((1 : G) : G ⧸ H), h1b⟩
  have aval : (a : G ⧸ H) = (g : G ⧸ H) := rfl
  have bval : (b : G ⧸ H) = ((1 : G) : G ⧸ H) := rfl
  let t : ↥M := ⟨u, huM⟩
  have tval : (t : G) = u := rfl
  -- `u ∉ conj g H`: else `u` would be an involution of the odd-order group `H ⊓ conj g H`
  have hu_not_conj : u ∉ Submission.Blueprint.conj g H := by
    intro huc
    have hmem : u ∈ H ⊓ Submission.Blueprint.conj g H := ⟨huH, huc⟩
    have h2 : 2 ∣ Nat.card ↥(H ⊓ Submission.Blueprint.conj g H) := by
      have h3 : orderOf (⟨u, hmem⟩ : ↥(H ⊓ Submission.Blueprint.conj g H)) = 2 := by
        rw [← Subgroup.orderOf_coe (⟨u, hmem⟩ : ↥(H ⊓ Submission.Blueprint.conj g H))]
        exact hu2
      rw [← h3]; exact orderOf_dvd_natCard _
    exact Nat.not_even_iff_odd.mpr (hH.2.2 g hg) (even_iff_two_dvd.mpr h2)
  -- the two dictionaries identifying the point stabilisers of `a` and `b` inside `↥M`
  have stabc : ∀ y : G, (hy : y ∈ M) →
      (y ∈ Submission.Blueprint.conj g H ↔ (⟨y, hy⟩ : ↥M) ∈ MulAction.stabilizer (↥M) a) := by
    intro y hy
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro hyconj
      apply Subtype.ext
      rw [smul_val, aval]
      exact (Work.DoubleTransitivity.smul_mk_eq_mk_iff).mpr hyconj
    · intro h
      have h2 : y • (g : G ⧸ H) = (g : G ⧸ H) := by
        have := congrArg (fun z : ↥S => (z : G ⧸ H)) h
        rwa [aval, smul_val] at this
      exact (Work.DoubleTransitivity.smul_mk_eq_mk_iff).mp h2
  have stabb : ∀ y : G, (hy : y ∈ M) →
      (y ∈ H ↔ (⟨y, hy⟩ : ↥M) ∈ MulAction.stabilizer (↥M) b) := by
    intro y hy
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro hyH
      apply Subtype.ext
      rw [smul_val, bval]
      show y • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H)
      rw [Work.DoubleTransitivity.smul_mk, mul_one]
      exact Work.DoubleTransitivity.mk_one_eq_iff.mpr hyH
    · intro h
      have h2 : y • ((1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H) := by
        have := congrArg (fun z : ↥S => (z : G ⧸ H)) h
        rwa [bval, smul_val] at this
      rw [Work.DoubleTransitivity.smul_mk, mul_one] at h2
      exact Work.DoubleTransitivity.mk_one_eq_iff.mp h2
  have hstab_eq : MulAction.stabilizer (↥M) a =
      (M ⊓ Submission.Blueprint.conj g H).subgroupOf M := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      exact ⟨y.2, (stabc (y : G) y.2).mpr h⟩
    · intro h
      exact (stabc (y : G) y.2).mp h.2
  have hstrong : IsStronglyEmbedded (MulAction.stabilizer (↥M) a) := by
    rw [hstab_eq]
    exact hB.2 g hPg
  -- a point stabiliser of a `2`-transitive action is maximal
  have hmax : IsCoatom (MulAction.stabilizer (↥M) a) := by
    rw [hstab_eq]
    refine ⟨?_, ?_⟩
    · intro htop
      have hmem : t ∈ (M ⊓ Submission.Blueprint.conj g H).subgroupOf M := by
        rw [htop]; trivial
      exact hu_not_conj ((Subgroup.mem_subgroupOf.mp hmem).2)
    · intro J hJ
      rw [eq_top_iff]
      intro m _
      have hKle : (M ⊓ Submission.Blueprint.conj g H).subgroupOf M ≤ J := le_of_lt hJ
      obtain ⟨j, hjJ, hjK⟩ : ∃ j ∈ J,
          j ∉ (M ⊓ Submission.Blueprint.conj g H).subgroupOf M := by
        by_contra h
        push_neg at h
        exact hJ.ne (le_antisymm hKle (fun x hx => h x hx))
      have hja_ne : (a : G ⧸ H) ≠ ((j • a : ↥S) : G ⧸ H) := by
        intro h
        have hfix : j ∈ MulAction.stabilizer (↥M) a := by
          rw [MulAction.mem_stabilizer_iff]
          exact Subtype.ext h.symm
        exact hjK (hstab_eq ▸ hfix)
      have htransJ : ∀ x : ↥S, ∃ j' ∈ J, j' • a = x := by
        intro x
        by_cases hx : x = a
        · exact ⟨1, J.one_mem, by rw [hx, one_smul]⟩
        · have hxa : (a : G ⧸ H) ≠ (x : G ⧸ H) := by
            intro h
            exact hx (Subtype.ext h).symm
          obtain ⟨mm, hmmM, hma, hmd⟩ :=
            hB.1 (a : G ⧸ H) a.2 ((j • a : ↥S) : G ⧸ H) (j • a).2 hja_ne
              (a : G ⧸ H) a.2 (x : G ⧸ H) x.2 hxa
          have hmmK : (⟨mm, hmmM⟩ : ↥M) ∈
              (M ⊓ Submission.Blueprint.conj g H).subgroupOf M := by
            rw [← hstab_eq, MulAction.mem_stabilizer_iff]
            exact Subtype.ext hma
          refine ⟨(⟨mm, hmmM⟩ : ↥M) * j, J.mul_mem (hKle hmmK) hjJ, ?_⟩
          apply Subtype.ext
          simpa [smul_val, Subgroup.coe_mul, mul_smul] using hmd
      obtain ⟨j', hj'J, hj'a⟩ := htransJ (m • a)
      have hfix : j'⁻¹ * m ∈ MulAction.stabilizer (↥M) a := by
        rw [MulAction.mem_stabilizer_iff]
        have hcomp : (j'⁻¹ * m) • a = j'⁻¹ • (m • a) := mul_smul _ _ _
        rw [hcomp, ← hj'a, inv_smul_smul]
      have hmemJ : j'⁻¹ * m ∈ J := hKle (hstab_eq ▸ hfix)
      rw [show m = j' * (j'⁻¹ * m) from by group]
      exact J.mul_mem hj'J hmemJ
  have htrans : MulAction.IsPretransitive (↥M) ↥S :=
    ⟨fun c d => by
      obtain ⟨c, hc⟩ := c
      obtain ⟨d, hd⟩ := d
      obtain ⟨y, hy, hycd⟩ := hB.1.isTransitiveOnSub c hc d hd
      exact ⟨⟨y, hy⟩, Subtype.ext (by rw [smul_val]; exact hycd)⟩⟩
  have ht : orderOf t = 2 := by
    rw [← Subgroup.orderOf_coe t, tval]; exact hu2
  have htH : t ∉ MulAction.stabilizer (↥M) a := fun h => hu_not_conj ((stabc u huM).mpr h)
  have hb : t • b = b := by
    apply Subtype.ext
    rw [smul_val, bval, tval, Work.DoubleTransitivity.smul_mk, mul_one]
    exact Work.DoubleTransitivity.mk_one_eq_iff.mpr huH
  -- the unique fixed point of `u` in `Ω` is the point `H` (whence in `Ω_P` as well)
  have hbuniq : ∀ c : ↥S, t • c = c → c = b := by
    intro c hc
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (c : G ⧸ H)
    have hfix : u • (QuotientGroup.mk x : G ⧸ H) = (QuotientGroup.mk x : G ⧸ H) := by
      have h2 := congrArg (fun z : ↥S => (z : G ⧸ H)) hc
      rw [smul_val, tval, ← hx] at h2
      exact h2
    have hucx : u ∈ Submission.Blueprint.conj x H :=
      (Work.DoubleTransitivity.smul_mk_eq_mk_iff).mp hfix
    have hxH : x ∈ H := by
      by_contra hxH
      have hmem : u ∈ H ⊓ Submission.Blueprint.conj x H := ⟨huH, hucx⟩
      have h2 : 2 ∣ Nat.card ↥(H ⊓ Submission.Blueprint.conj x H) := by
        have h3 : orderOf (⟨u, hmem⟩ : ↥(H ⊓ Submission.Blueprint.conj x H)) = 2 := by
          rw [← Subgroup.orderOf_coe (⟨u, hmem⟩ : ↥(H ⊓ Submission.Blueprint.conj x H))]
          exact hu2
        rw [← h3]; exact orderOf_dvd_natCard _
      exact Nat.not_even_iff_odd.mpr (hH.2.2 x hxH) (even_iff_two_dvd.mpr h2)
    apply Subtype.ext
    rw [← hx, bval]
    exact Work.DoubleTransitivity.mk_one_eq_iff.mpr hxH
  -- Appendix III (1): `Stab_M(a) ⊓ conj t Stab_M(a) = Stab_M(a) ⊓ Stab_M(b)`
  have hres := app3_1_thm (F := ↥M) (A := ↥S) a htrans hstrong hmax hC hBrSz hFT
    ht htH hb hbuniq
  -- hence `N_D(P) = M ⊓ D ≤ conj u D`
  have key : M ⊓ D ≤ Submission.Blueprint.conj u D := by
    intro x hx
    rw [hDdef, Submission.Blueprint.twoPoint, Subgroup.mem_inf, Subgroup.mem_inf] at hx
    obtain ⟨hxM, hxH, hxg⟩ := hx
    have hmemA : (⟨x, hxM⟩ : ↥M) ∈ MulAction.stabilizer (↥M) a := (stabc x hxM).mp hxg
    have hmemB : (⟨x, hxM⟩ : ↥M) ∈ MulAction.stabilizer (↥M) b := (stabb x hxM).mp hxH
    have hmem : (⟨x, hxM⟩ : ↥M) ∈
        Submission.Blueprint.conj t (MulAction.stabilizer (↥M) a) := by
      have h1 : (⟨x, hxM⟩ : ↥M) ∈
          MulAction.stabilizer (↥M) a ⊓ MulAction.stabilizer (↥M) b := ⟨hmemA, hmemB⟩
      rw [← hres] at h1
      exact h1.2
    rw [Submission.Blueprint.conj, Subgroup.mem_map] at hmem
    obtain ⟨y, hyA, hyx⟩ := hmem
    have hyG : (y : G) = u⁻¹ * x * u := by
      have h : ((MulAut.conj t) y : G) = x := by
        simpa only [MulEquiv.coe_toMonoidHom] using congrArg (fun z : ↥M => (z : G)) hyx
      rw [MulAut.conj_apply] at h
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
      rw [tval] at h
      rw [← h]; group
    have hyH : (y : G) ∈ H := by
      rw [hyG]
      exact H.mul_mem (H.mul_mem (H.inv_mem huH) hxH) huH
    have hyconj : (y : G) ∈ Submission.Blueprint.conj g H := (stabc (y : G) y.2).mpr hyA
    rw [hDdef, Submission.Blueprint.twoPoint, Submission.Blueprint.conj, Subgroup.mem_map]
    refine ⟨(y : G), ⟨hyH, hyconj⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hyG]; group
  -- `P` is a `p`-Sylow of `D`
  have hPp : IsPGroup p P := hP.2.1
  refine ⟨hPD, hPp, ?_⟩
  intro Q hPQ hQD hQp
  by_contra hne
  have hPQne : P ≠ Q := fun h => hne h.symm
  haveI : Fact p.Prime := ⟨hp⟩
  have hnil : Group.IsNilpotent ↥Q := hQp.isNilpotent
  have hnc : NormalizerCondition ↥Q := Group.normalizerCondition_of_isNilpotent
  have hPsub_ne : (P.subgroupOf Q) ≠ ⊤ := by
    intro htop
    rw [Subgroup.subgroupOf_eq_top] at htop
    exact hPQne (le_antisymm hPQ htop)
  -- in a `p`-group every proper subgroup is properly contained in its normaliser
  have hgrow : P.subgroupOf Q < Subgroup.normalizer (P.subgroupOf Q) :=
    hnc (P.subgroupOf Q) (lt_top_iff_ne_top.mpr hPsub_ne)
  set N : Subgroup G := (Subgroup.normalizer (P.subgroupOf Q)).map Q.subtype with hNdef
  have hN_eq : N = M ⊓ Q := by
    rw [hNdef, ← Subgroup.subgroupOf_normalizer_eq hPQ, Subgroup.subgroupOf_map_subtype]
  have hN_le_M : N ≤ M := by rw [hN_eq]; exact inf_le_left
  have hN_le_Q : N ≤ Q := by rw [hN_eq]; exact inf_le_right
  have hN_pg : IsPGroup p N := hQp.to_le hN_le_Q
  have hPN : P ≤ N := by
    have h1 : (P.subgroupOf Q).map Q.subtype ≤ N := by
      rw [hNdef]; exact Subgroup.map_mono hgrow.1
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPQ] at h1
  have hPNne : N ≠ P := by
    intro hNP
    have hmap1 : (Subgroup.normalizer (P.subgroupOf Q)).map Q.subtype = N := by rw [hNdef]
    have hmap2 : (P.subgroupOf Q).map Q.subtype = P := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPQ]
    have heq : (Subgroup.normalizer (P.subgroupOf Q)).map Q.subtype
        = (P.subgroupOf Q).map Q.subtype := by rw [hmap1, hmap2, hNP]
    exact hgrow.ne (Subgroup.map_injective Q.subtype_injective heq.symm)
  have hN_le_D : N ≤ D := hN_le_Q.trans hQD
  have hN_le_cD : N ≤ Submission.Blueprint.conj u D :=
    (le_inf hN_le_M hN_le_D).trans key
  exact hPNne (hP.2.2 N hPN (le_inf hN_le_D hN_le_cD) hN_pg)

end Work.ThreePoints.ThmC
