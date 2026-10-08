import Mathlib
import Submission.Work.CORE4.NotA7Defs
import Submission.Work.CORE4.A7FourGroupBound
import Submission.Work.CORE4.InvSetCountNormalFourB
import Submission.Work.CORE4.ElementaryAbelianRankTwo
import Submission.Work.CORE4.A7Fusion
import Submission.Work.CORE4.A7CosetEvenCardBound
import Submission.Work.CORE4.A7OrderThreeCentralizer
import Submission.Work.CORE4.NotA7.A3U_M_eq_E_sup_F
import Submission.Work.CORE4.NotA7.A3UOddCore
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.API
import Submission.Work.CORE4.DihOrCycSub
import Submission.Work.CORE4.NotA7.N_le_centralizer_A
import Submission.Work.CORE4.NotA7.A7CentralizerUniqueFour

open scoped MatrixGroups

namespace Work.CORE4.NotA7

open Work.GW2 Subgroup

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

variable {G : Type} [Group G] [Finite G]

/-! ## Auxiliary lemmas for `Work.CORE4.NotA7.A6EvenStructure` -/

/-- **`E(M) ⊓ F = Z(E(M))`** in the `A₇` case: with `O(M) = F` (`A7UData`), the centre of the
layer (odd order, `LayerCtx6`) is an odd normal subgroup of `M`, hence lies in `O(M) = F`; the
reverse inclusion is `F ≤ C(E(M))` (`Case2Pre.F_cent`). -/
theorem layerIn_inf_F_eq_center (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
      Work.GW2.Hyp9 G B C → Work.GW2.A7Facts1 C.D → Work.GW2.A7Facts2 B C.D →
        Work.GW2.oddCoreIn C.D.M = C.D.F →
          C.D.F.subgroupOf (Work.GW2.layerIn C.D.M) =
            Subgroup.center ↥(Work.GW2.layerIn C.D.M) := by
  intro G _inst _fin B C hHyp hf1 hf2 hoddC
  have hbc : Work.GW2.BenderCtx G := hHyp.1
  set E : Subgroup G := Work.GW2.layerIn C.D.M with hEdef
  have hEM : E ≤ C.D.M := by rw [hEdef]; exact Work.CORE4.layerIn_le C.D.M
  have hME : C.D.M ≤ Subgroup.normalizer (E : Set G) := by
    rw [hEdef]; exact Work.CORE4.layerIn_le_normalizer C.D.M
  have hFcentE : C.D.F ≤ Subgroup.centralizer (E : Set G) := by
    rw [hEdef]; exact Work.GW2.Case2Pre.F_cent B C.D C.pre
  -- `Z(E) ≤ F`
  have hZE : (Subgroup.center ↥E).map E.subtype ≤ C.D.F := by
    have hZM : (Subgroup.center ↥E).map E.subtype ≤ C.D.M :=
      (Subgroup.map_subtype_le (Subgroup.center ↥E)).trans hEM
    have hZnorm : (((Subgroup.center ↥E).map E.subtype).subgroupOf C.D.M).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hZM]
      intro h k hh hk
      rw [Subgroup.mem_map] at hh ⊢
      obtain ⟨z, hz, hzx⟩ := hh
      refine ⟨⟨k * (z : G) * k⁻¹, Subgroup.le_normalizer_iff.mp hME k hk (z : G) z.2⟩, ?_, ?_⟩
      · rw [Subgroup.mem_center_iff] at hz ⊢
        intro w
        have hwE : k⁻¹ * (w : G) * k ∈ E := by
          have h := (Subgroup.mem_normalizer_iff.mp (hME (C.D.M.inv_mem hk)) (w : G)).mp w.2
          simpa using h
        have hcomm : (k⁻¹ * (w : G) * k) * (z : G) =
            (z : G) * (k⁻¹ * (w : G) * k) :=
          congrArg Subtype.val (hz ⟨k⁻¹ * (w : G) * k, hwE⟩)
        apply Subtype.ext
        show (w : G) * (k * (z : G) * k⁻¹) = (k * (z : G) * k⁻¹) * (w : G)
        calc (w : G) * (k * (z : G) * k⁻¹)
            = k * ((k⁻¹ * (w : G) * k) * (z : G)) * k⁻¹ := by group
          _ = k * ((z : G) * (k⁻¹ * (w : G) * k)) * k⁻¹ := by rw [hcomm]
          _ = (k * (z : G) * k⁻¹) * (w : G) := by group
      · have hz' : (z : G) = h := hzx
        show k * (z : G) * k⁻¹ = k * h * k⁻¹
        rw [hz']
    have hZodd : Odd (Nat.card ↥((Subgroup.center ↥E).map E.subtype)) := by
      rw [Subgroup.card_map_of_injective E.subtype_injective]
      exact (Work.CORE4.LayerCtx6 I hbc C (Work.CORE4.DihOrCycSub hbc.sylow C.D.M)).2.1
    have h := le_oddCoreIn_of_normal_of_odd_aux hZM hZnorm hZodd
    rwa [hoddC] at h
  -- `E ⊓ F ≤ Z(E)`
  have hEF : E ⊓ C.D.F ≤ (Subgroup.center ↥E).map E.subtype := by
    intro y hy
    obtain ⟨hyE, hyF⟩ := Subgroup.mem_inf.mp hy
    rw [Subgroup.mem_map]
    refine ⟨⟨y, hyE⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    show (z : G) * (y : G) = (y : G) * (z : G)
    exact Subgroup.mem_centralizer_iff.mp (hFcentE hyF) (z : G) z.2
  have hmap : (C.D.F.subgroupOf E).map E.subtype = (Subgroup.center ↥E).map E.subtype := by
    rw [Subgroup.subgroupOf_map_subtype]
    refine le_antisymm ?_ (le_inf hZE (Subgroup.map_subtype_le _))
    rwa [inf_comm]
  exact Subgroup.map_injective E.subtype_injective hmap

/-- **`M/F ≅ A₇`**: under `A7UData` there is a surjective homomorphism `↥M →* A₇` with kernel
exactly `F = O(M)`. -/
theorem hom_M_A7 (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
      Work.GW2.Hyp9 G B C → Work.GW2.IsA7Case C.D → Work.GW2.A7Facts1 C.D →
        Work.GW2.A7Facts2 B C.D → Work.CORE4.A7UData B C.D →
          ∃ π : ↥C.D.M →* alternatingGroup (Fin 7), π.ker = C.D.F.subgroupOf C.D.M := by
  intro G _inst _fin B C hHyp hA7 hf1 hf2 hUD
  obtain ⟨ha7iso⟩ := hA7
  have hU3 : IsPGroup 3 B.U := hUD.1
  have hoddC : Work.GW2.oddCoreIn C.D.M = C.D.F := hUD.2.2.1
  have hEM : Work.GW2.layerIn C.D.M ≤ C.D.M := Work.CORE4.layerIn_le C.D.M
  have hFM : C.D.F ≤ C.D.M :=
    le_trans (Work.GW2.Case2Data.F_le_B0 B C.D)
      (le_trans (Work.GW2.Case2Data.B0_le B C.D) inf_le_right)
  have hNF : Subgroup.normalizer (C.D.F : Set G) = C.D.M := Work.GW2.Case2Pre.N_F B C.D C.pre
  have hFnormM : C.D.M ≤ Subgroup.normalizer (C.D.F : Set G) := le_of_eq hNF.symm
  haveI hFnorm_sub : (C.D.F.subgroupOf C.D.M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hFnormM
  have hEnormF : Work.GW2.layerIn C.D.M ≤ Subgroup.normalizer (C.D.F : Set G) := by
    rw [hNF]; exact hEM
  have hEnormM : C.D.M ≤ Subgroup.normalizer (Work.GW2.layerIn C.D.M : Set G) :=
    Work.CORE4.layerIn_le_normalizer C.D.M
  haveI hEnorm_sub : ((Work.GW2.layerIn C.D.M).subgroupOf C.D.M).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hEnormM
  have hMEF : C.D.M = Work.GW2.layerIn C.D.M ⊔ C.D.F := A3U_M_eq_E_sup_F I G B C hHyp hf2 hU3
  have hZF : C.D.F.subgroupOf (Work.GW2.layerIn C.D.M)
      = Subgroup.center ↥(Work.GW2.layerIn C.D.M) :=
    layerIn_inf_F_eq_center I G B C hHyp hf1 hf2 hoddC
  let φ : ↥(Work.GW2.layerIn C.D.M) →* (↥C.D.M ⧸ C.D.F.subgroupOf C.D.M) :=
    (QuotientGroup.mk' (C.D.F.subgroupOf C.D.M)).comp (Subgroup.inclusion hEM)
  have hφker : φ.ker = Subgroup.center ↥(Work.GW2.layerIn C.D.M) := by
    ext x
    rw [MonoidHom.mem_ker]
    dsimp only [φ, MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
    rw [← hZF]
    exact Subgroup.mem_subgroupOf.symm
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (C.D.F.subgroupOf C.D.M) y
    have htop : ((Work.GW2.layerIn C.D.M).subgroupOf C.D.M) ⊔ (C.D.F.subgroupOf C.D.M) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hEM hFM, ← hMEF, Subgroup.subgroupOf_self]
    have hm : m ∈ ((Work.GW2.layerIn C.D.M).subgroupOf C.D.M) ⊔ (C.D.F.subgroupOf C.D.M) := by
      rw [htop]; exact Subgroup.mem_top m
    obtain ⟨e, he, f, hf, hef⟩ := Subgroup.mem_sup_of_normal_left.mp hm
    refine ⟨⟨(e : G), Subgroup.mem_subgroupOf.mp he⟩, ?_⟩
    have hxe : (Subgroup.inclusion hEM ⟨(e : G), Subgroup.mem_subgroupOf.mp he⟩ : ↥C.D.M) = e :=
      Subtype.ext (by rw [Subgroup.coe_inclusion])
    simp only [φ, MonoidHom.comp_apply, hxe]
    rw [QuotientGroup.mk'_eq_mk']
    exact ⟨f, hf, hef⟩
  have Φ : (↥(Work.GW2.layerIn C.D.M) ⧸ Subgroup.center ↥(Work.GW2.layerIn C.D.M))
      ≃* (↥C.D.M ⧸ C.D.F.subgroupOf C.D.M) :=
    (QuotientGroup.quotientMulEquivOfEq hφker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)
  let Θ : (↥C.D.M ⧸ C.D.F.subgroupOf C.D.M) ≃* alternatingGroup (Fin 7) :=
    Φ.symm.trans ha7iso
  refine ⟨Θ.toMonoidHom.comp (QuotientGroup.mk' (C.D.F.subgroupOf C.D.M)), ?_⟩
  rw [MonoidHom.ker_comp_of_injective _ _ Θ.injective, QuotientGroup.ker_mk']

/-- The cardinality shadow of the first isomorphism theorem: for `π : ↥M →* T` with
`ker π = F.subgroupOf M` and `X ≤ M`, `|X| = |X ⊓ F| · |π(X)|`. -/
theorem card_eq_card_inf_mul_card_range {G T : Type} [Group G] [Group T] [Finite G] [Finite T]
    {M F : Subgroup G} (π : ↥M →* T) (hker : π.ker = F.subgroupOf M)
    (X : Subgroup G) (hXM : X ≤ M) :
    Nat.card ↥X = Nat.card ↥(X ⊓ F : Subgroup G) *
      Nat.card ↥((π.comp (Subgroup.inclusion hXM)).range) := by
  let φ : ↥X →* T := π.comp (Subgroup.inclusion hXM)
  have hkerφ : φ.ker = (X ⊓ F).subgroupOf X := by
    ext x
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    constructor
    · intro h
      have hmem : Subgroup.inclusion hXM x ∈ π.ker := by
        rw [MonoidHom.mem_ker]
        simpa only [φ, MonoidHom.comp_apply] using h
      rw [hker, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion] at hmem
      exact ⟨x.2, hmem⟩
    · rintro ⟨_hx, hF⟩
      have hmem : Subgroup.inclusion hXM x ∈ π.ker := by
        rw [hker, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]
        exact hF
      rw [MonoidHom.mem_ker] at hmem
      simpa only [φ, MonoidHom.comp_apply] using hmem
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (φ.ker)
  have h2 : Nat.card (↥X ⧸ φ.ker) = Nat.card ↥φ.range :=
    Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv
  have h3 : Nat.card ↥φ.ker = Nat.card ↥(X ⊓ F : Subgroup G) := by
    rw [hkerφ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : X ⊓ F ≤ X)).toEquiv
  rw [h2, h3] at h1
  dsimp only [φ] at h1
  exact h1.trans (mul_comm _ _)

/-- The conjugate of a four-group is a four-group. -/
theorem isFourGroup_conjSub {G : Type} [Group G] {V : Subgroup G} (hV : IsFourGroup V)
    (g : G) : IsFourGroup (Work.GW2.conjSub g V) := by
  have hmap : Work.GW2.conjSub g V = V.map (MulAut.conj g).toMonoidHom := rfl
  refine ⟨?_, ?_⟩
  · rw [hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hV.1
  · intro x hx
    rw [hmap, Subgroup.mem_map] at hx
    obtain ⟨v, hv, hveq⟩ := hx
    rw [← hveq, pow_two]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hv2 : v * v = 1 := by
      have h := hV.2 v hv
      rwa [pow_two] at h
    calc (g * v * g⁻¹) * (g * v * g⁻¹) = g * (v * v) * g⁻¹ := by group
      _ = 1 := by rw [hv2]; group

/-- For `x ∈ M`, `π x` lies in the image of `W ≤ M` (where `ker π = F`) iff `x = w * f` with
`w ∈ W`, `f ∈ F`, provided `F` centralizes `W`. -/
theorem mem_range_iff_exists_mul {G T : Type} [Group G] [Group T]
    {M F W : Subgroup G} (π : ↥M →* T) (hker : π.ker = F.subgroupOf M)
    (hWM : W ≤ M) (hFM : F ≤ M)
    (hFcent : F ≤ Subgroup.centralizer (W : Set G))
    (x : G) (hxM : x ∈ M) :
    π ⟨x, hxM⟩ ∈ (π.comp (Subgroup.inclusion hWM)).range ↔
      ∃ w ∈ W, ∃ f ∈ F, w * f = x := by
  constructor
  · rintro ⟨y, hy⟩
    have hy' : π (Subgroup.inclusion hWM y) = π ⟨x, hxM⟩ := hy
    have h1 : (⟨x, hxM⟩ : ↥M) * (Subgroup.inclusion hWM y)⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hy']
      group
    rw [hker, Subgroup.mem_subgroupOf] at h1
    have hval : x * (y : G)⁻¹ ∈ F := by
      simpa [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion] using h1
    refine ⟨(y : G), y.2, x * (y : G)⁻¹, hval, ?_⟩
    have hcw : (y : G) * (x * (y : G)⁻¹) = (x * (y : G)⁻¹) * (y : G) :=
      Subgroup.mem_centralizer_iff.mp (hFcent hval) (y : G) y.2
    rw [hcw]
    group
  · rintro ⟨w, hw, f, hf, hwf⟩
    refine ⟨⟨w, hw⟩, ?_⟩
    simp only [MonoidHom.comp_apply]
    change π ⟨w, hWM hw⟩ = π ⟨x, hxM⟩
    have hxeq : (⟨x, hxM⟩ : ↥M) = ⟨w, hWM hw⟩ * ⟨f, hFM hf⟩ := Subtype.ext hwf.symm
    have hf1 : π ⟨f, hFM hf⟩ = 1 :=
      MonoidHom.mem_ker.mp (by rw [hker]; exact Subgroup.mem_subgroupOf.mpr hf)
    rw [hxeq, map_mul, hf1, mul_one]

/-- **Uniqueness of the four-group of `C_M(A)`.**  If `W₁, W₂ ≤ M` are four-groups contained in
`C_G(A)` where `A ∋ k` and the image of `k` in `T` satisfies the uniqueness of the order-`4`
subgroup of its centralizer (`hT`), then `W₁ = W₂`.

Indeed both images `π(Wᵢ)` are order-`4` subgroups of `C_T(π k)`, hence equal; `π` has kernel `F`,
so `π x ∈ π(Wᵢ)` iff `x = w f` with `w ∈ Wᵢ`, `f ∈ F`.  Hence `W₁ ≤ W₂ ⊔ F` and `W₂ ≤ W₁ ⊔ F`;
for `x ∈ W₁` of order `≤ 2` and `x = w f` one gets `w w = f` with `w w ∈ W₂` and `f ∈ F`, so
`f = 1` (as `W₂ ⊓ F = ⊥`) and `x = w ∈ W₂`. -/
theorem eq_of_isFourGroup_of_le_centralizer {G T : Type} [Group G] [Group T]
    {M F A : Subgroup G} (π : ↥M →* T) (hker : π.ker = F.subgroupOf M)
    (hFcard : Nat.card ↥F = 3) (hFM : F ≤ M)
    (hFcentM : F ≤ Subgroup.centralizer (M : Set G))
    (k : G) (hkM : k ∈ M) (hkA : k ∈ A)
    (hT : ∀ U₁ U₂ : Subgroup T,
      U₁ ≤ Subgroup.centralizer ({π ⟨k, hkM⟩} : Set T) →
      U₂ ≤ Subgroup.centralizer ({π ⟨k, hkM⟩} : Set T) →
      Nat.card ↥U₁ = 4 → Nat.card ↥U₂ = 4 → U₁ = U₂)
    (W₁ W₂ : Subgroup G) (hW1M : W₁ ≤ M) (hW2M : W₂ ≤ M)
    (hW1C : W₁ ≤ Subgroup.centralizer (A : Set G))
    (hW2C : W₂ ≤ Subgroup.centralizer (A : Set G))
    (hW1f : Work.GW2.IsFourGroup W₁) (hW2f : Work.GW2.IsFourGroup W₂)
    (h1 : Nat.card ↥W₁ = 4) (h2 : Nat.card ↥W₂ = 4) : W₁ = W₂ := by
  have hinfbot : ∀ (W : Subgroup G), Nat.card ↥W = 4 → W ⊓ F = ⊥ := by
    intro W hW
    have hdvd1 : Nat.card ↥(W ⊓ F) ∣ 4 := by
      rw [← hW]; exact Subgroup.card_dvd_of_le inf_le_left
    have hdvd3 : Nat.card ↥(W ⊓ F) ∣ 3 := by
      rw [← hFcard]; exact Subgroup.card_dvd_of_le inf_le_right
    have hgcd : Nat.card ↥(W ⊓ F) ∣ 1 := by
      have h := Nat.dvd_gcd hdvd1 hdvd3
      rw [show Nat.gcd 4 3 = 1 from by norm_num] at h
      exact h
    exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp hgcd)
  have hFcentW : ∀ (W : Subgroup G), W ≤ M → F ≤ Subgroup.centralizer (W : Set G) := by
    intro W hWM f hf
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_iff.mp (hFcentM hf) w (hWM hw)
  have himg4 : ∀ (W : Subgroup G) (hWM : W ≤ M), Nat.card ↥W = 4 →
      Nat.card ↥((π.comp (Subgroup.inclusion hWM)).range) = 4 := by
    intro W hWM hW
    have hkerW : (π.comp (Subgroup.inclusion hWM)).ker = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hmem : Subgroup.inclusion hWM x ∈ π.ker := by
        rw [MonoidHom.mem_ker]
        simpa only [MonoidHom.comp_apply] using hx
      rw [hker, Subgroup.mem_subgroupOf, Subgroup.coe_inclusion] at hmem
      have hmem2 : (x : G) ∈ W ⊓ F := ⟨x.2, hmem⟩
      rw [hinfbot W hW] at hmem2
      exact Subtype.ext (Subgroup.mem_bot.mp hmem2)
    have hh := Subgroup.card_ker_mul_card_range (π.comp (Subgroup.inclusion hWM))
    rw [hkerW] at hh
    simp only [Subgroup.card_bot, one_mul] at hh
    rw [hh, hW]
  have himgC : ∀ (W : Subgroup G) (hWM : W ≤ M) (hWC : W ≤ Subgroup.centralizer (A : Set G)),
      (π.comp (Subgroup.inclusion hWM)).range ≤
        Subgroup.centralizer ({π ⟨k, hkM⟩} : Set T) := by
    intro W hWM hWC z hz
    obtain ⟨y, rfl⟩ := hz
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    rw [Set.mem_singleton_iff] at hu
    subst hu
    simp only [MonoidHom.comp_apply]
    have hcomm : Subgroup.inclusion hWM y * (⟨k, hkM⟩ : ↥M) =
        (⟨k, hkM⟩ : ↥M) * Subgroup.inclusion hWM y := by
      apply Subtype.ext
      show (y : G) * k = k * (y : G)
      exact (Subgroup.mem_centralizer_iff.mp (hWC y.2) k hkA).symm
    rw [← map_mul, ← map_mul, hcomm]
  have hR : (π.comp (Subgroup.inclusion hW1M)).range =
      (π.comp (Subgroup.inclusion hW2M)).range :=
    hT _ _ (himgC W₁ hW1M hW1C) (himgC W₂ hW2M hW2C) (himg4 W₁ hW1M h1) (himg4 W₂ hW2M h2)
  have hchar1 : ∀ (x : G) (hxM : x ∈ M),
      π ⟨x, hxM⟩ ∈ (π.comp (Subgroup.inclusion hW1M)).range ↔
        ∃ w ∈ W₁, ∃ f ∈ F, w * f = x :=
    fun x hxM => mem_range_iff_exists_mul π hker hW1M hFM (hFcentW W₁ hW1M) x hxM
  have hchar2 : ∀ (x : G) (hxM : x ∈ M),
      π ⟨x, hxM⟩ ∈ (π.comp (Subgroup.inclusion hW2M)).range ↔
        ∃ w ∈ W₂, ∃ f ∈ F, w * f = x :=
    fun x hxM => mem_range_iff_exists_mul π hker hW2M hFM (hFcentW W₂ hW2M) x hxM
  have hF3 : ∀ f ∈ F, f * f * f = 1 := by
    intro f hf
    have hdvd : orderOf f ∣ 3 := by
      rw [← hFcard]; exact Subgroup.orderOf_dvd_natCard F hf
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · have hf1 : f = 1 := orderOf_eq_one_iff.mp h
      rw [hf1]; group
    · have h3 := pow_orderOf_eq_one f
      rw [h, pow_three] at h3
      simpa [mul_assoc] using h3
  have key : ∀ (W W' : Subgroup G) (hWM : W ≤ M) (hW'M : W' ≤ M)
      (hW'C : W' ≤ Subgroup.centralizer (A : Set G)) (hW'card : Nat.card ↥W' = 4)
      (hf : Work.GW2.IsFourGroup W) (hWcard : Nat.card ↥W = 4) (hR' : (π.comp (Subgroup.inclusion hWM)).range = (π.comp (Subgroup.inclusion hW'M)).range)
      (x : G) (hx : x ∈ W), x ∈ W' := by
    intro W W' hWM hW'M hW'C hW'card hf hWcard hR' x hx
    have hxM : x ∈ M := hWM hx
    have hmem : π ⟨x, hWM hx⟩ ∈ (π.comp (Subgroup.inclusion hWM)).range :=
      ⟨⟨x, hx⟩, rfl⟩
    have hmem' : π ⟨x, hxM⟩ ∈ (π.comp (Subgroup.inclusion hWM)).range := by
      rwa [show π ⟨x, hWM hx⟩ = π ⟨x, hxM⟩ from congrArg π (Subtype.ext rfl)]
    rw [hR'] at hmem'
    obtain ⟨w, hw, f, hfF, hwf⟩ := (mem_range_iff_exists_mul π hker hW'M hFM
      (hFcentW W' hW'M) x hxM).mp hmem'
    have hx2 : x * x = 1 := by
      have h := hf.2 x hx
      rwa [pow_two] at h
    have hcw : w * f = f * w :=
      Subgroup.mem_centralizer_iff.mp (hFcentW W' hW'M hfF) w hw
    have hstep : (w * f) * (w * f) = w * w * (f * f) := by
      calc (w * f) * (w * f) = w * (f * w) * f := by group
        _ = w * (w * f) * f := by rw [hcw]
        _ = w * w * (f * f) := by group
    have hprod : w * w * (f * f) = 1 := by
      have h := hx2
      rw [← hwf] at h
      rwa [hstep] at h
    have hww : w * w = f := by
      have h3 : w * w = (f * f)⁻¹ := eq_inv_of_mul_eq_one_left hprod
      have h4 : f * f = f⁻¹ := eq_inv_of_mul_eq_one_left (hF3 f hfF)
      rw [h3, h4, inv_inv]
    have hmem2 : w * w ∈ W' ⊓ F := by
      refine Subgroup.mem_inf.mpr ⟨W'.mul_mem hw hw, ?_⟩
      rw [hww]; exact hfF
    rw [hinfbot W' hW'card] at hmem2
    have hww1 : w * w = 1 := Subgroup.mem_bot.mp hmem2
    have hf1 : f = 1 := by rw [← hww, hww1]
    rw [← hwf, hf1, mul_one]
    exact hw
  exact le_antisymm (key W₁ W₂ hW1M hW2M hW2C h2 hW1f h1 hR)
    (key W₂ W₁ hW2M hW1M hW1C h1 hW2f h2 hR.symm)

theorem A6EvenStructure (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B),
      Work.GW2.Hyp9 G B C → Work.GW2.IsA7Case C.D → Work.GW2.A7Facts1 C.D →
        Work.GW2.A7Facts2 B C.D → Work.CORE4.A7Mid B C.D →
          ∀ y : G, orderOf y = 2 → y ∉ C.D.M → y ∈ B.H →
            let V : Subgroup G := Work.GW2.pCoreIn 2 (B.H ⊓ C.D.M)
            let N : Subgroup G := C.D.M ⊓ Work.GW2.conjSub y C.D.M
            V ≤ N ∧ N ≤ Subgroup.normalizer (V : Set G) ∧
              Odd (V.relIndex N) ∧ Nat.card ↥N ≤ 108 ∧
              (∃ v ∈ V, y * v * y⁻¹ ≠ v) := by
  intro G _inst _fin B C hHyp hA7 hf1 hf2 hMid y hy2 hyM hyH
  obtain ⟨hUD, _hNotInv, hf5⟩ := hMid
  have hbc : Work.GW2.BenderCtx G := hHyp.1
  have hU3 : IsPGroup 3 B.U := hUD.1
  have hB0F : C.D.B0 = C.D.F := hUD.2.1
  have hKcard : Nat.card ↥C.D.K = 3 := hf1.1
  have hFcard : Nat.card ↥C.D.F = 3 := hf1.2.1
  have hVHhatEq : Work.GW2.pCoreIn 2 B.Hhat = Work.GW2.pCoreIn 2 (B.H ⊓ C.D.M) := hf2.2.1
  set V : Subgroup G := Work.GW2.pCoreIn 2 (B.H ⊓ C.D.M) with hVdef
  set N : Subgroup G := C.D.M ⊓ Work.GW2.conjSub y C.D.M with hNdef
  have hV4 : Work.GW2.IsFourGroup V := by rw [hVdef]; exact hf2.1
  have hyy : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at h
  -- `V ≤ H ⊓ M` and `V ⊴ Ĥ`
  have hVleHM : V ≤ B.H ⊓ C.D.M := by rw [hVdef]; exact Subgroup.map_subtype_le _
  have hVleH : V ≤ B.H := hVleHM.trans inf_le_left
  have hVleM : V ≤ C.D.M := hVleHM.trans inf_le_right
  have hVnormHhat : B.Hhat ≤ Subgroup.normalizer (V : Set G) := by
    rw [← hVHhatEq]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Work.CORE4.pCoreIn_le_self 2 B.Hhat)).mp
      (Work.CORE4.subgroupOf_pCoreIn_normal 2 B.Hhat)
  have hyHhat : y ∈ B.Hhat := B.H_le_Hhat hyH
  -- `V ≤ N`
  have hVN : V ≤ N := by
    intro v hv
    rw [hNdef]
    refine Subgroup.mem_inf.mpr ⟨hVleM hv, ?_⟩
    rw [Work.GW2.conjSub, Subgroup.mem_map]
    refine ⟨y⁻¹ * v * y, hVleM ?_, ?_⟩
    · have h := (Subgroup.mem_normalizer_iff.mp (hVnormHhat (B.Hhat.inv_mem hyHhat)) v).mp hv
      simpa using h
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  -- `F ≤ Z(M)`
  have hFZ : C.D.F ≤ Subgroup.centralizer ((C.D.M : Subgroup G) : Set G) := by
    have hME : C.D.M = Work.GW2.layerIn C.D.M ⊔ C.D.F := A3U_M_eq_E_sup_F I G B C hHyp hf2 hU3
    have hFcentE : C.D.F ≤ Subgroup.centralizer ((Work.GW2.layerIn C.D.M : Subgroup G) : Set G) :=
      Work.GW2.Case2Pre.F_cent B C.D C.pre
    have hE : Work.GW2.layerIn C.D.M ≤ Subgroup.centralizer ((C.D.F : Subgroup G) : Set G) :=
      Subgroup.le_centralizer_iff.mpr hFcentE
    have hFcommF : C.D.F ≤ Subgroup.centralizer ((C.D.F : Subgroup G) : Set G) :=
      Subgroup.le_centralizer_iff_isMulCommutative.mpr (A7_F_isMulCommutative I B C hf1)
    rw [hME]
    exact Subgroup.le_centralizer_iff.mp (sup_le hE hFcommF)
  -- `N ≤ C_M(A)`
  have hNcentA : N ≤ Subgroup.centralizer (((C.D.F ⊔ C.D.K : Subgroup G)) : Set G) :=
    N_le_centralizer_A I G B C hHyp hA7 hf1 hf2 hUD hf5 hFZ y hy2 hyM hyH
  -- `V ≤ C(A)` (via `V = S ⊓ C_G(U)`)
  have hA_le_U : (C.D.F ⊔ C.D.K : Subgroup G) ≤ B.U :=
    sup_le (Work.GW2.Case2Data.F_le_U B C.D) (Work.GW2.Case2Data.K_le_U B C.D)
  have hV_CU : V ≤ Subgroup.centralizer (B.U : Set G) := by
    have h26 := I.thm26 G I.toolkit.ft hbc B
    rw [← hVHhatEq, ← h26.2.1]
    exact inf_le_right
  have hVC : V ≤ Subgroup.centralizer (((C.D.F ⊔ C.D.K : Subgroup G)) : Set G) :=
    le_trans hV_CU (Subgroup.centralizer_le hA_le_U)
  -- the homomorphism `π : ↥M →* A₇` with kernel `F`
  obtain ⟨π, hπker⟩ := hom_M_A7 I G B C hHyp hA7 hf1 hf2 hUD
  -- `K ⊓ F = ⊥`
  have hKFbot : C.D.K ⊓ C.D.F = ⊥ := by
    have hAcard : Nat.card ↥(C.D.F ⊔ C.D.K : Subgroup G) = 9 := A7UMCard hB0F hKcard hFcard
    by_contra hne
    have hKleF : C.D.K ≤ C.D.F := by
      have hdvd : Nat.card ↥(C.D.K ⊓ C.D.F) ∣ 3 := by
        rw [← hKcard]; exact Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
      · exact absurd (Subgroup.card_eq_one.mp h) hne
      · have hcard : Nat.card ↥(C.D.K ⊓ C.D.F) = Nat.card ↥C.D.K := by rw [h, hKcard]
        have hEq : C.D.K ⊓ C.D.F = C.D.K :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard])
        rw [← hEq]
        exact inf_le_right
    have hsup : (C.D.F ⊔ C.D.K : Subgroup G) = C.D.F := sup_eq_left.mpr hKleF
    rw [hsup] at hAcard
    omega
  -- an element `k ∈ K` of order `3`
  have hKne : C.D.K ≠ ⊥ := by
    intro h; rw [h] at hKcard; simp at hKcard
  obtain ⟨kK, hkK1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKne
  set k : G := (kK : G) with hkdef
  have hkK : k ∈ C.D.K := kK.2
  have hkM : k ∈ C.D.M := Work.GW2.Case2Data.K_le_M B C.D hkK
  have hkA : k ∈ (C.D.F ⊔ C.D.K : Subgroup G) := Subgroup.mem_sup_right hkK
  have hk3 : orderOf k = 3 := by
    have hdvd : orderOf k ∣ Nat.card ↥C.D.K := Subgroup.orderOf_dvd_natCard C.D.K hkK
    rw [hKcard] at hdvd
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) (fun h1 => hkK1 (Subtype.ext h1))
    · exact h
  have hπk3 : orderOf (π ⟨k, hkM⟩) = 3 := by
    have hdvd : orderOf (π ⟨k, hkM⟩) ∣ orderOf (⟨k, hkM⟩ : ↥C.D.M) := orderOf_map_dvd π _
    have hord : orderOf (⟨k, hkM⟩ : ↥C.D.M) = 3 :=
      (orderOf_injective (Subgroup.subtype C.D.M) Subtype.val_injective ⟨k, hkM⟩).symm.trans hk3
    rw [hord] at hdvd
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exfalso
      have hmem : (⟨k, hkM⟩ : ↥C.D.M) ∈ π.ker :=
        MonoidHom.mem_ker.mpr (orderOf_eq_one_iff.mp h)
      rw [hπker, Subgroup.mem_subgroupOf] at hmem
      have h1 : k ∈ C.D.K ⊓ C.D.F := ⟨hkK, hmem⟩
      rw [hKFbot] at h1
      exact hkK1 (Subtype.ext (Subgroup.mem_bot.mp h1))
    · exact h
  -- the image of `N` in `A₇`
  have hNM : N ≤ C.D.M := inf_le_left
  have hFM : C.D.F ≤ C.D.M :=
    le_trans (Work.GW2.Case2Data.F_le_B0 B C.D)
      (le_trans (Work.GW2.Case2Data.B0_le B C.D) inf_le_right)
  have hrangeC : (π.comp (Subgroup.inclusion hNM)).range ≤
      Subgroup.centralizer ({π ⟨k, hkM⟩} : Set (alternatingGroup (Fin 7))) := by
    intro z hz
    obtain ⟨u, rfl⟩ := hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    simp only [MonoidHom.comp_apply]
    have hcomm : Subgroup.inclusion hNM u * (⟨k, hkM⟩ : ↥C.D.M) =
        (⟨k, hkM⟩ : ↥C.D.M) * Subgroup.inclusion hNM u := by
      apply Subtype.ext
      show (u : G) * k = k * (u : G)
      exact (Subgroup.mem_centralizer_iff.mp (hNcentA u.2) k hkA).symm
    rw [← map_mul, ← map_mul, hcomm]
  have hrdvd := Subgroup.card_dvd_of_le hrangeC
  have hCval := Work.AUTA7.A7.CentralizerOrderThree hπk3
  have hcardN : Nat.card ↥N = Nat.card ↥(N ⊓ C.D.F : Subgroup G) *
      Nat.card ↥((π.comp (Subgroup.inclusion hNM)).range) :=
    card_eq_card_inf_mul_card_range π hπker N hNM
  have hNa_dvd : Nat.card ↥(N ⊓ C.D.F : Subgroup G) ∣ 3 := by
    rw [← hFcard]; exact Subgroup.card_dvd_of_le inf_le_right
  have h4N : 4 ∣ Nat.card ↥N := by
    have h : 4 ∣ Nat.card ↥V := by rw [hV4.1]
    exact h.trans (Subgroup.card_dvd_of_le hVN)
  have hN_le : Nat.card ↥N ≤ 108 := by
    rw [hcardN]
    rcases hCval with hc | hc
    · have hb : Nat.card ↥((π.comp (Subgroup.inclusion hNM)).range) ≤ 36 := by
        rw [hc] at hrdvd
        exact Nat.le_of_dvd (by norm_num) hrdvd
      calc Nat.card ↥(N ⊓ C.D.F : Subgroup G) *
            Nat.card ↥((π.comp (Subgroup.inclusion hNM)).range)
          ≤ 3 * 36 := Nat.mul_le_mul (Nat.le_of_dvd (by norm_num) hNa_dvd) hb
        _ = 108 := by norm_num
    · have hb : Nat.card ↥((π.comp (Subgroup.inclusion hNM)).range) ≤ 9 := by
        rw [hc] at hrdvd
        exact Nat.le_of_dvd (by norm_num) hrdvd
      calc Nat.card ↥(N ⊓ C.D.F : Subgroup G) *
            Nat.card ↥((π.comp (Subgroup.inclusion hNM)).range)
          ≤ 3 * 9 := Nat.mul_le_mul (Nat.le_of_dvd (by norm_num) hNa_dvd) hb
        _ ≤ 108 := by norm_num
  -- `8 ∤ |N|`
  have hN8 : ¬ (8 ∣ Nat.card ↥N) := by
    intro h8dvd
    rw [hcardN] at h8dvd
    have hb36 : Nat.card ↥((π.comp (Subgroup.inclusion hNM)).range) ∣ 36 := by
      rcases hCval with hc | hc
      · rwa [hc] at hrdvd
      · exfalso
        have hb9 : Nat.card ↥((π.comp (Subgroup.inclusion hNM)).range) ∣ 9 := by
          rwa [hc] at hrdvd
        have hbodd : Odd (Nat.card ↥((π.comp (Subgroup.inclusion hNM)).range)) :=
          Odd.of_dvd_nat (by norm_num) hb9
        have haodd : Odd (Nat.card ↥(N ⊓ C.D.F : Subgroup G)) :=
          Odd.of_dvd_nat (by norm_num) hNa_dvd
        have h4 : 4 ∣ Nat.card ↥N := h4N
        rw [hcardN] at h4
        exact Nat.not_even_iff_odd.mpr (haodd.mul hbodd)
          (even_iff_two_dvd.mpr (dvd_trans (by norm_num : 2 ∣ 4) h4))
    have hb8 : 8 ∣ Nat.card ↥((π.comp (Subgroup.inclusion hNM)).range) := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hNa_dvd with h | h
      · rw [h, one_mul] at h8dvd; exact h8dvd
      · rw [h] at h8dvd
        exact (show Nat.Coprime 8 3 from by norm_num).dvd_of_dvd_mul_left h8dvd
    exact absurd (hb8.trans hb36) (by norm_num)
  -- `Odd (V.relIndex N)`
  have hmul : 4 * V.relIndex N = Nat.card ↥N := by
    have h := Subgroup.relIndex_mul_card (H := V) (K := N)
    rw [inf_of_le_left hVN] at h
    rw [hV4.1, mul_comm] at h
    exact h
  have hodd : Odd (V.relIndex N) := by
    refine Nat.not_even_iff_odd.mp ?_
    intro hev
    rw [even_iff_two_dvd] at hev
    obtain ⟨t, ht⟩ := hev
    apply hN8
    refine ⟨t, ?_⟩
    rw [← hmul, ht]
    ring
  -- `N ≤ N_G(V)`
  have hVnormN : N ≤ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro n hn v hv
    have hnM : n ∈ C.D.M := hNM hn
    have hVnM : Work.GW2.conjSub n V ≤ C.D.M := by
      intro x hx
      rw [Work.GW2.conjSub, Subgroup.mem_map] at hx
      obtain ⟨v', hv', rfl⟩ := hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact C.D.M.mul_mem (C.D.M.mul_mem hnM (hVleM hv')) (C.D.M.inv_mem hnM)
    have hVnC : Work.GW2.conjSub n V ≤
        Subgroup.centralizer (((C.D.F ⊔ C.D.K : Subgroup G)) : Set G) := by
      intro x hx
      rw [Work.GW2.conjSub, Subgroup.mem_map] at hx
      obtain ⟨v', hv', rfl⟩ := hx
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hna : Commute n a := (Subgroup.mem_centralizer_iff.mp (hNcentA hn) a ha).symm
      have hna' : n⁻¹ * a = a * n⁻¹ := hna.inv_left
      have hva : v' * a = a * v' := (Subgroup.mem_centralizer_iff.mp (hVC hv') a ha).symm
      calc a * (n * v' * n⁻¹) = (a * n) * v' * n⁻¹ := by group
        _ = (n * a) * v' * n⁻¹ := by rw [hna.symm]
        _ = n * (a * v') * n⁻¹ := by group
        _ = n * (v' * a) * n⁻¹ := by rw [hva]
        _ = n * v' * (a * n⁻¹) := by group
        _ = n * v' * (n⁻¹ * a) := by rw [← hna']
        _ = (n * v' * n⁻¹) * a := by group
    have hVn4 : Nat.card ↥(Work.GW2.conjSub n V) = 4 := (isFourGroup_conjSub hV4 n).1
    have heq : Work.GW2.conjSub n V = V :=
      (eq_of_isFourGroup_of_le_centralizer π hπker hFcard hFM hFZ k hkM hkA
        (fun U₁ U₂ hc1 hc2 hd1 hd2 => A7CentralizerUniqueFour _ hπk3 U₁ U₂ hc1 hc2 hd1 hd2)
        V (Work.GW2.conjSub n V) hVleM hVnM hVC hVnC hV4 (isFourGroup_conjSub hV4 n)
        hV4.1 hVn4).symm
    have hmem : n * v * n⁻¹ ∈ Work.GW2.conjSub n V := by
      rw [Work.GW2.conjSub, Subgroup.mem_map]
      exact ⟨v, hv, rfl⟩
    rwa [heq] at hmem
  -- `y` acts non-trivially on `V`
  have hact : ∃ v ∈ V, y * v * y⁻¹ ≠ v := by
    by_contra hcon
    push_neg at hcon
    have hcomm : y ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      calc v * y = (y * v * y⁻¹) * y := by rw [hcon v hv]
        _ = y * v := by group
    have hyV : y ∉ V := fun h => hyM (hVleM h)
    exact Work.CORE4.ElementaryAbelianRankTwo G hbc.sylow V hV4 y hyy hyV hcomm
  exact ⟨hVN, hVnormN, hodd, hN_le, hact⟩

end Work.CORE4.NotA7
