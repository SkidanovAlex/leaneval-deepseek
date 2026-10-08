import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.Case2SevenAux
import Submission.Work.CORE4.Case2SevenCentralizer
import Submission.Work.CORE4.Case2EightObjExists

namespace Work.CORE4.SevenNine

open Work.GW2 Subgroup
open scoped commutatorElement

set_option linter.unusedSectionVars false

/-! ## Group-theoretic preliminaries

Two small general facts that the proof of Bender §4 (7) needs, both stated for abstract
subgroups of `G`:

* `commutator_le_centralizer_of_cyclic_normal`: if `A ⊴ L` is cyclic then `⁅L, L⁆ ≤ C_G(A)`.
  Indeed conjugation gives a homomorphism `L →* MulAut A`, and `MulAut A` is commutative for
  cyclic `A` (indeed `IsCyclic.mulAutMulEquiv : MulAut A ≃* (ZMod |A|)ˣ`);
* normalizer bookkeeping: `N_G(H ⊓ K) ⊇ N_G(H) ⊓ N_G(K)` and, for the commutator,
  `x ∈ N_G(A) ∩ N_G(B) → x ∈ N_G(⁅A, B⁆)`. -/

/-- **The automorphism group of a cyclic group is commutative.**  `MulAut A ≃* (ZMod |A|)ˣ`
for cyclic `A`, and the units of a commutative ring are commutative. -/
theorem mulAut_mul_comm_of_isCyclic {A : Type} [Group A] [IsCyclic A] (a b : MulAut A) :
    a * b = b * a := by
  have h : IsCyclic.mulAutMulEquiv A (a * b) = IsCyclic.mulAutMulEquiv A (b * a) := by
    rw [map_mul, map_mul, mul_comm]
  exact (IsCyclic.mulAutMulEquiv A).injective h

/-- **A cyclic normal subgroup is centralized by the commutator subgroup.**  If `A ≤ L` and
`A ⊴ L` with `A` cyclic, then `⁅L, L⁆ ≤ C_G(A)`: the conjugation action of `L` on `A` lands in
`MulAut A`, which is abelian, so every commutator of `L` acts trivially on `A`. -/
theorem commutator_le_centralizer_of_cyclic_normal {G : Type} [Group G] {A L : Subgroup G}
    (hAL : A ≤ L) (hAn : (A.subgroupOf L).Normal) (hcyc : IsCyclic ↥A) :
    ⁅L, L⁆ ≤ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hL : L ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAL).mp hAn
  have hxy : ⁅x, y⁆ ∈ L := L.mul_mem (L.mul_mem (L.mul_mem hx hy) (L.inv_mem hx)) (L.inv_mem hy)
  have hz : (⟨⁅x, y⁆, hL hxy⟩ : Subgroup.normalizer (A : Set G)) ∈
      A.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    have heq : (⟨⁅x, y⁆, hL hxy⟩ : Subgroup.normalizer (A : Set G)) =
        ⁅(⟨x, hL hx⟩ : Subgroup.normalizer (A : Set G)),
          (⟨y, hL hy⟩ : Subgroup.normalizer (A : Set G))⁆ := Subtype.ext rfl
    rw [heq, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mulAut_mul_comm_of_isCyclic (A := ↥A) _ _
  rw [A.normalizerMonoidHom_ker, Subgroup.mem_subgroupOf] at hz
  exact hz

section NormalizerHelpers

variable {G : Type} [Group G]

/-- `N_G(H) ⊓ N_G(K) ≤ N_G(H ⊓ K)`. -/
theorem mem_normalizer_inf {H K : Subgroup G} {x : G}
    (hH : x ∈ Subgroup.normalizer (H : Set G)) (hK : x ∈ Subgroup.normalizer (K : Set G)) :
    x ∈ Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hH hK ⊢
  intro h
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hH h, hK h]

/-- If `x` normalizes `A` then conjugation by `x` maps `A` into itself. -/
theorem map_conj_le_of_mem_normalizer {A : Subgroup G} {x : G}
    (h : x ∈ Subgroup.normalizer (A : Set G)) :
    A.map (MulAut.conj x).toMonoidHom ≤ A := by
  intro y hy
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hy
  show (MulAut.conj x) a ∈ A
  rw [MulAut.conj_apply]
  exact (Subgroup.mem_normalizer_iff.mp h a).mp ha

/-- **`N_G(A) ⊓ N_G(B) ≤ N_G(⁅A, B⁆)`**: conjugation preserves the commutator of two subgroups. -/
theorem mem_normalizer_commutator {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer (⁅A, B⁆ : Subgroup G) := by
  have hmA := map_conj_le_of_mem_normalizer hA
  have hmB := map_conj_le_of_mem_normalizer hB
  have hmA' := map_conj_le_of_mem_normalizer ((Subgroup.normalizer (A : Set G)).inv_mem hA)
  have hmB' := map_conj_le_of_mem_normalizer ((Subgroup.normalizer (B : Set G)).inv_mem hB)
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hle : (⁅A, B⁆ : Subgroup G).map (MulAut.conj x).toMonoidHom ≤ ⁅A, B⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hmA hmB
    refine hle ?_
    exact Subgroup.mem_map.mpr ⟨h, hh,
      by show (MulAut.conj x) h = x * h * x⁻¹; rw [MulAut.conj_apply]⟩
  · intro hh
    have hle : (⁅A, B⁆ : Subgroup G).map (MulAut.conj x⁻¹).toMonoidHom ≤ ⁅A, B⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hmA' hmB'
    have h2 : x⁻¹ * (x * h * x⁻¹) * x ∈ (⁅A, B⁆ : Subgroup G) :=
      hle (Subgroup.mem_map.mpr ⟨x * h * x⁻¹, hh, by
        show (MulAut.conj x⁻¹) (x * h * x⁻¹) = x⁻¹ * (x * h * x⁻¹) * x
        rw [MulAut.conj_apply]; simp⟩)
    simpa [mul_assoc] using h2

end NormalizerHelpers

/-! ## The `Case2Ctx6` structural facts -/

section Case2Ctx6Helpers

variable {G : Type} [Group G] [Finite G]

/-- `E(K) = layerIn K`, viewed inside `↥K`, is the layer of `K`, hence normal. -/
theorem layerIn_subgroupOf_normal_C6 (K : Subgroup G) :
    ((layerIn K).subgroupOf K).Normal := by
  have h1 : (layerIn K).subgroupOf K = layer ↥K := by
    rw [← Subgroup.comap_subtype (layerIn K) K]
    exact Subgroup.comap_map_eq_self_of_injective (Subtype.val_injective) _
  rw [h1]
  exact Work.CORE4.layer_normal K

/-- `U ⊓ M ⊴ M ⊓ H` at the `Case2Ctx6` level.  This is the proof of
`Work.GW2.Case2Ctx.U_inf_M_normal`, which uses only `B.U_normal` and `B.U_le_H`. -/
theorem U_inf_M_normal_C6 (B : BenderSetup G) (C : Case2Ctx6 B) :
    ((B.U ⊓ C.D.M).subgroupOf (C.D.M ⊓ B.H)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (le_inf inf_le_right (le_trans inf_le_left B.U_le_H))]
  intro a b ha hb
  obtain ⟨haU, haM⟩ := Subgroup.mem_inf.mp ha
  obtain ⟨hbM, hbH⟩ := Subgroup.mem_inf.mp hb
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact (Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal a b haU hbH
  · exact C.D.M.mul_mem (C.D.M.mul_mem hbM haM) (C.D.M.inv_mem hbM)

/-- `F ⊴ M ⊓ H` (Bender's (5): `N_G(F) = M`, and `F ≤ U ⊓ M ≤ M ⊓ H`). -/
theorem F_normal_C6 (B : BenderSetup G) (C : Case2Ctx6 B) (hpre : Case2Pre B C.D) :
    ((C.D.F).subgroupOf (C.D.M ⊓ B.H)).Normal := by
  have hFM : C.D.F ≤ C.D.M := le_trans (Case2Data.F_le_UinfM B C.D) inf_le_right
  have hFH : C.D.F ≤ B.H := le_trans (Case2Data.F_le_U B C.D) B.U_le_H
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (le_inf hFM hFH)]
  calc C.D.M ⊓ B.H ≤ C.D.M := inf_le_left
    _ ≤ Subgroup.normalizer (C.D.F : Set G) := by rw [Case2Pre.N_F B C.D hpre]

/-- **`S ⊓ M` normalizes `K`.**  Bender's (1) says `K = ⁅S ⊓ E(M), U ⊓ M⁆` (`Case2PrePlus`),
and any `x ∈ S ⊓ M` normalizes `S ⊓ E(M)` (it lies in `S` and in `M`, and `E(M) ⊴ M`) and
`U ⊓ M` (it lies in `H` and in `M`, and `U ⊴ H`), hence normalizes their commutator. -/
theorem S_le_normalizer_K_C6 (B : BenderSetup G) (C : Case2Ctx6 B)
    (hplus : Case2PrePlus B C.D) :
    (B.S : Subgroup G) ⊓ C.D.M ≤ Subgroup.normalizer (C.D.K : Set G) := by
  intro x hx
  obtain ⟨hxS, hxM⟩ := Subgroup.mem_inf.mp hx
  have hMn : C.D.M ≤ Subgroup.normalizer ((layerIn C.D.M) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Work.CORE4.layerIn_le C.D.M)).mp
      (layerIn_subgroupOf_normal_C6 C.D.M)
  have hUn : B.H ≤ Subgroup.normalizer (B.U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer B.U_le_H).mp B.U_normal
  have hSE : x ∈ Subgroup.normalizer (((B.S : Subgroup G) ⊓ layerIn C.D.M) : Set G) :=
    mem_normalizer_inf (Subgroup.le_normalizer hxS) (hMn hxM)
  have hUM : x ∈ Subgroup.normalizer ((B.U ⊓ C.D.M : Subgroup G) : Set G) :=
    mem_normalizer_inf (hUn (B.S_le_H hxS)) (Subgroup.le_normalizer hxM)
  rw [hplus.2.1]
  exact mem_normalizer_commutator hSE hUM

/-- **`K ⊴ (U ⊓ M) ⊔ (S ⊓ M)`.**  `K ⊴ U ⊓ M` (Bender 1.5(iii), the input `I.toolkit.c15`) and
`S ⊓ M` normalizes `K` by `S_le_normalizer_K_C6`; the join of the two normalizers contains both
generators. -/
theorem K_normal_in_join_C6 (I : C4Inputs) (B : BenderSetup G) (C : Case2Ctx6 B)
    (hplus : Case2PrePlus B C.D) :
    (C.D.K.subgroupOf
      (((B.U ⊓ C.D.M) ⊔ ((B.S : Subgroup G) ⊓ C.D.M)) : Subgroup G)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (le_trans (Case2Data.K_le B C.D) le_sup_left)]
  refine sup_le ?_ ?_
  · exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Case2Data.K_le B C.D)).mp (Work.CORE4.Case2Data.K_normal_in_UinfM I B C.D)
  · exact S_le_normalizer_K_C6 B C hplus

end Case2Ctx6Helpers

/-- Bender 1981, §4 (7) (p. 225), conjunct `π⁅S ⊓ M, B₀⁆ ⊆ π = π(F(U))`, at the design-pass-9
`Case2Ctx6` level (§4 (1)–(6) plus `Case2PrePlus`).  `C.D.B0` is Bender's `B`, the
`(2)`-form `B₀ = (U ⊓ M) ⊓ C_G(S ⊓ E(M))` being part of `Case2PrePlus`.

ROUTE (established; please follow).  Bender's own argument: `⁅S ⊓ M, B₀⁆` lies both in
`(H ⊓ M)'` (so it centralizes the cyclic normal subgroups `K` and `F` of `H ⊓ M`) and in
`U ⊓ M` (so it is a subgroup of the odd group `U ⊓ M ⊇ K₀F`).

* `⁅S ⊓ M, B₀⁆ ≤ ⁅B.H ⊓ C.D.M, B.H ⊓ C.D.M⁆ = (H ⊓ M)'` (commutator monotonicity) and
  `⁅S ⊓ M, B₀⁆ ≤ ⁅B.H ⊓ C.D.M, B.U ⊓ C.D.M⁆ ≤ B.U ⊓ C.D.M`, since
  `B.U ⊓ C.D.M ⊴ B.H ⊓ C.D.M` (this is `Case2Ctx.U_inf_M_normal`'s proof, which uses only
  `B.U_normal`, `B.U_le_H`; copy it for the `Case2Ctx6` binders).
* `F ⊴ H ⊓ M`: `N_G(F) = C.D.M` (`Case2Pre.N_F`) and `F ≤ B.U ⊓ C.D.M = H ⊓ M`.
* `K ⊴ H ⊓ M`: `K ⊴ B.U ⊓ C.D.M` (`Case2Data.K_normal_in_UinfM`) and `S ⊓ M` normalizes `K`
  because `K = ⁅B.S ⊓ layerIn C.D.M, B.U ⊓ C.D.M⁆` (`Case2PrePlus`) and any `x ∈ S ⊓ M`
  normalizes `B.S ⊓ layerIn C.D.M` (as `layerIn C.D.M ⊴ C.D.M` and `x ∈ C.D.M`) and
  `B.U ⊓ C.D.M` (as `B.U ⊴ B.H`); so `K ⊴ (B.U ⊓ C.D.M) ⊔ (B.S ⊓ C.D.M)`, and
  `H ⊓ M = (B.U ⊓ C.D.M) ⊔ (B.S ⊓ C.D.M)`.
  [For that last equality: `(B.U ⊓ C.D.M) ⊴ (B.H ⊓ C.D.M)`, `B.S ⊓ C.D.M ≤ B.H ⊓ C.D.M`;
  `(B.U ⊓ C.D.M).relIndex (B.H ⊓ C.D.M) = B.U.relIndex (B.H ⊓ C.D.M)` divides
  `B.U.relIndex B.H = |H : U| = |S|` (a power of 2, via `Subgroup.relIndex_sup_left` inside
  `↥B.H` and `Work.CORE4.relIndex_eq_card_of_sup_eq_inf_eq_bot`); the 2-part of `|H ⊓ M|` is
  `|B.S ⊓ C.D.M|` because `B.S ⊓ C.D.M ∈ Syl₂(C.D.M)` (`Case2PrePlus`) and `B.U ⊓ C.D.M` is odd;
  so `|H ⊓ M| = |B.U ⊓ C.D.M| * |B.S ⊓ C.D.M| = |(B.U ⊓ C.D.M) ⊔ (B.S ⊓ C.D.M)|`
  (`Work.CORE4.card_sup_of_disjoint_normalizer`, `B.S ⊓ C.D.M ≤ N_G(B.U ⊓ C.D.M)`).
  Alternatively: `B.H = B.U ⊔ B.S` (`I.toolkit.split`, whose side conditions `S ≃* DihedralGroup n`
  with `n ≥ 2` are `Work.CORE2B.L27su_S_dihedral hbc B`) makes
  `(B.H ⊓ C.D.M)/(B.U ⊓ C.D.M) ↪ B.H/B.U ≅ B.S` a 2-group, and combined with the Sylow fact
  above this pins the index down.]
* general lemma: for `A ⊴ L` cyclic, `⁅L, L⁆ ≤ C_G(A)` (conjugation acts on a cyclic group through
  an abelian group).  Apply it to `L = H ⊓ M` with `A = K` and `A = F`
  (`F` cyclic is `C.F_cyclic`, `K` cyclic is `Case2Pre.K_cyclic`): `(H ⊓ M)' ≤ C_G(K ⊓ F) = C_G(K₀F)`
  (as `C.D.K0 ≤ C.D.K`).
* hence `⁅S ⊓ M, B₀⁆ ≤ (B.U ⊓ C.D.M) ⊓ C_G(C.D.K0 ⊔ C.D.F)`, so
  `π⁅S ⊓ M, B₀⁆ ⊆ π(B.U ⊓ C_G(C.D.K0 ⊔ C.D.F)) = B.piFU` by the already proved
  `Work.CORE4.Case2SevenCentralizer`.

Do NOT use `Work.CORE4.Case2Seven`, `Case2SevenFacts` or anything depending on `sorryAx`. -/
theorem pi_comm_SM_B0 {G : Type} [Group G] [Finite G] (I : Work.GW2.C4Inputs)
    (hbc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h2 : Work.GW2.Case2 B)
    (C : Work.GW2.Case2Ctx6 B) (hplus : Work.GW2.Case2PrePlus B C.D) :
    Work.GW2.primesOf ⁅(B.S : Subgroup G) ⊓ C.D.M, C.D.B0⁆ ⊆ B.piFU := by
  have hpre : Case2Pre B C.D := C.pre
  have hFcyc : IsCyclic ↥C.D.F := C.F_cyclic
  -- `S ⊓ M ≤ M ⊓ H` and `B₀ ≤ M ⊓ H`
  have hSMH : (B.S : Subgroup G) ⊓ C.D.M ≤ C.D.M ⊓ B.H :=
    le_inf inf_le_right (le_trans inf_le_left B.S_le_H)
  have hB0MH : C.D.B0 ≤ C.D.M ⊓ B.H :=
    le_inf (le_trans (Case2Data.B0_le B C.D) inf_le_right)
      (le_trans (le_trans (Case2Data.B0_le B C.D) inf_le_left) B.U_le_H)
  -- `B₀ ≤ U ⊓ M`
  have hB0UM : C.D.B0 ≤ B.U ⊓ C.D.M := Case2Data.B0_le B C.D
  -- the join used to apply the cyclic-normal-centralizer lemma with `A = K`
  set Lk : Subgroup G := (B.U ⊓ C.D.M) ⊔ ((B.S : Subgroup G) ⊓ C.D.M) with hLk
  -- `⁅S ⊓ M, B₀⁆ ≤ B.U` (via `⁅M ⊓ H, U ⊓ M⁆ ≤ U ⊓ M`)
  have hUMnormal : (C.D.M ⊓ B.H) ≤ Subgroup.normalizer ((B.U ⊓ C.D.M : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (le_inf inf_le_right (le_trans inf_le_left B.U_le_H))).mp (U_inf_M_normal_C6 B C)
  have hleUM : ⁅(B.S : Subgroup G) ⊓ C.D.M, C.D.B0⁆ ≤ B.U ⊓ C.D.M :=
    le_trans (Subgroup.commutator_mono hSMH hB0UM)
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hUMnormal)
  -- `⁅S ⊓ M, B₀⁆ ≤ C_G(K)`
  have hkcyc : IsCyclic ↥C.D.K := Case2Pre.K_cyclic B C.D hpre
  have hknormal : (C.D.K.subgroupOf Lk).Normal := K_normal_in_join_C6 I B C hplus
  have hk_le : C.D.K ≤ Lk := le_trans (Case2Data.K_le B C.D) le_sup_left
  have hCK : ⁅(B.S : Subgroup G) ⊓ C.D.M, C.D.B0⁆ ≤ Subgroup.centralizer (C.D.K : Set G) :=
    le_trans (Subgroup.commutator_mono le_sup_right (le_trans hB0UM le_sup_left))
      (commutator_le_centralizer_of_cyclic_normal hk_le hknormal hkcyc)
  -- `⁅S ⊓ M, B₀⁆ ≤ C_G(F)`
  have hFnormal : ((C.D.F).subgroupOf (C.D.M ⊓ B.H)).Normal := F_normal_C6 B C hpre
  have hF_le : C.D.F ≤ C.D.M ⊓ B.H :=
    le_inf (le_trans (Case2Data.F_le_UinfM B C.D) inf_le_right)
      (le_trans (Case2Data.F_le_U B C.D) B.U_le_H)
  have hCF : ⁅(B.S : Subgroup G) ⊓ C.D.M, C.D.B0⁆ ≤ Subgroup.centralizer (C.D.F : Set G) :=
    le_trans (Subgroup.commutator_mono hSMH hB0MH)
      (commutator_le_centralizer_of_cyclic_normal hF_le hFnormal hFcyc)
  -- `K₀ ≤ K`, so `C_G(K) ≤ C_G(K₀) ⊓ C_G(F) = C_G(K₀ ⊔ F)`
  have hK0leK : C.D.K0 ≤ C.D.K := by
    show fittingIn B.U ⊓ C.D.K ≤ C.D.K
    exact inf_le_right
  have hCFin : ⁅(B.S : Subgroup G) ⊓ C.D.M, C.D.B0⁆ ≤
      Subgroup.centralizer (((C.D.K0 ⊔ C.D.F : Subgroup G)) : Set G) := by
    rw [Subgroup.centralizer_sup]
    exact le_inf (le_trans hCK (Subgroup.centralizer_le fun x hx => hK0leK hx)) hCF
  have hmain : ⁅(B.S : Subgroup G) ⊓ C.D.M, C.D.B0⁆ ≤
      B.U ⊓ Subgroup.centralizer (((C.D.K0 ⊔ C.D.F : Subgroup G)) : Set G) :=
    le_inf (le_trans hleUM inf_le_left) hCFin
  have hmono := Work.CORE4.SevenX.PiFU.primesOf_mono hmain
  rw [Work.CORE4.Case2SevenCentralizer I G hbc B C h2 hplus] at hmono
  exact hmono

end Work.CORE4.SevenNine
