import Mathlib
import Submission.Work.CORE2B.fittingIn_U_normalizer
import Submission.Work.CORE2B.isPGroup_pCoreIn_two
import Submission.Work.CORE2B.L27cf_helpers
import Submission.OddOrder.Isaacs.Ch02_Subnormality.Basic
import Submission.OddOrder.GroupTheory.SubgroupInAmbient

/-!
# CORE2B — the `2`-part of `F(Ĥ)` lies in `O₂(Ĥ)`

Bender 1981, Lemma 2.7 (`t` centralizes `O₂(M)`) and Lemma 2.9 use the elementary fact that a
`p`-element of the Fitting subgroup of a finite group already lies in the `p`-core: the Fitting
subgroup is nilpotent, so its unique Sylow `p`-subgroup consists exactly of its `p`-elements, and
being (characteristic, hence) normal in the ambient group it is contained in `O_p`.

Formally the cleanest route is the *subnormality* formulation, as in
`Submission/Work/CORE3/pCoreIn_of_pow_eq_one_of_mem_fittingIn.lean` and
`Submission/Work/BMAX/inf_fittingIn_le_pCoreIn_of_le_pCoreIn.lean`:

* `⟨x⟩ ≤ F(H)` is a `{p}`-subgroup of the finite nilpotent group `F(H)`, hence subnormal in
  `F(H)` (Isaacs Lemma 2.1: subgroups of nilpotent groups are subnormal) and therefore in `H`
  (as `F(H) ⊴ H`);
* a subnormal `{p}`-subgroup lies in `O_{⟨p⟩}(H)`, which is a normal `p`-subgroup of `H` and
  hence lies in `O_p(H)`.

Since the areas `CORE2A`, `CORE3`, `BMAX`, `GLUE`, … each carry their *own* copy of the
`Work.GW2` vocabulary (two of them cannot be imported into a single file), the helper lemmas are
reproved here against the `CORE2B` copy, exactly as in the modules above.

Main output: `L27v12_twopart_mem_pCoreIn_Hhat` — an element of `2`-power order of `F(Ĥ)` lies in
`O₂(Ĥ)`.
-/

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 1. Transport of `IsPGroup` on `zpowers` along an injective homomorphism -/

/-- **Transport of `IsPGroup` along an injective homomorphism sending `y` to `x`.**

If `f y = x` for an injective `f` and `⟨x⟩` is a `q`-group then so is `⟨y⟩`. -/
theorem L27v12_zpowers_isPGroup_of_map_eq {H G : Type*} [Group H] [Group G] (f : H →* G)
    (hf : Function.Injective f) {y : H} {x : G} (hyx : f y = x) {q : ℕ}
    (hx : IsPGroup q ↥(Subgroup.zpowers x)) : IsPGroup q ↥(Subgroup.zpowers y) := by
  have hcomap : (Subgroup.zpowers x).comap f = Subgroup.zpowers y := by
    ext z
    rw [Subgroup.mem_comap, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, hf (by rw [map_zpow, hyx, hk])⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [← hyx, ← map_zpow, hk]⟩
  rw [← hcomap]
  exact hx.comap_of_injective f hf

/-! ## 2. `q`-elements of a normal nilpotent subgroup lie in `O_q` -/

/-- **An element generating a `q`-subgroup of a normal nilpotent subgroup `F ⊴ H` lies in
`O_q(H)`.**

Indeed `⟨x⟩ ≤ F` is a `q`-subgroup; `F` nilpotent makes every subgroup of `F` subnormal in `F`
(Isaacs Lemma 2.1, `isSubnormal_of_isNilpotent_finite`), and `F ⊴ H` makes `⟨x⟩` subnormal in
`H`; a subnormal `q`-subgroup lies in `O_{⟨q⟩}(H)` (`le_oPiCore_of_isSubnormal`), and
`O_{⟨q⟩}(H)` is a normal `q`-subgroup of `H`, hence contained in `pCore q H` by the universal
property of the `q`-core. -/
theorem L27v12_mem_pCore_of_mem_normal_isNilpotent_of_isPGroup {H : Type*} [Group H] [Finite H]
    {F : Subgroup H} (hFn : F.Normal) (hFnil : Group.IsNilpotent ↥F) {q : ℕ} [Fact q.Prime]
    {x : H} (hxF : x ∈ F) (hx : IsPGroup q ↥(Subgroup.zpowers x)) :
    x ∈ Work.GW2.pCore q H := by
  haveI := hFn
  haveI := hFnil
  -- `⟨x⟩ ≤ F` and `⟨x⟩` is subnormal in `H` (`F` is normal and `F` is nilpotent)
  have hPF : Subgroup.zpowers x ≤ F := Subgroup.zpowers_le.mpr hxF
  have hsub : (Subgroup.zpowers x).IsSubnormal :=
    Subgroup.IsSubnormal.trans hPF
      (OddOrder.Isaacs.Ch02.isSubnormal_of_isNilpotent_finite
        ((Subgroup.zpowers x).subgroupOf F))
      (Subgroup.Normal.isSubnormal hFn)
  -- `⟨x⟩` is a `{q}`-subgroup
  have hpi : Subgroup.IsPiSubgroup ({q} : Set ℕ) (Subgroup.zpowers x) :=
    OddOrder.GroupTheory.isPiSubgroup_singleton_of_isPGroup hx
  -- a subnormal `q`-subgroup lies in `O_{⟨q⟩}(H)`
  have hle : Subgroup.zpowers x ≤ OddOrder.Isaacs.Ch03.oPiCore ({q} : Set ℕ) H :=
    OddOrder.GroupTheory.le_oPiCore_of_isSubnormal hsub hpi
  -- and `O_{⟨q⟩}(H) ≤ O_q(H)` (`O_{⟨q⟩}(H)` is a normal `q`-subgroup of `H`)
  have hPG : IsPGroup q ↥(OddOrder.Isaacs.Ch03.oPiCore ({q} : Set ℕ) H) :=
    OddOrder.GroupTheory.isPGroup_of_isPiSubgroup_singleton
      (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup ({q} : Set ℕ))
  haveI : (OddOrder.Isaacs.Ch03.oPiCore ({q} : Set ℕ) H).Normal := inferInstance
  have hle2 : OddOrder.Isaacs.Ch03.oPiCore ({q} : Set ℕ) H ≤ Work.GW2.pCore q H :=
    Subgroup.normal_le_normalCore.mpr (le_sSup ⟨inferInstance, hPG⟩)
  exact hle2 (hle (Subgroup.mem_zpowers x))

/-! ## 3. The relative form: `q`-elements of `F(K)` lie in `O_q(K)` -/

/-- **`O_q(K)` contains every `q`-element of the Fitting subgroup `F(K)`** (in the ambient
group `G`).

`x ∈ F(K)` is the image under `K.subtype` of some `y ∈ F(↥K)`; `y` generates a `q`-subgroup of
the normal nilpotent subgroup `F(↥K) ⊴ ↥K`, so `y ∈ O_q(↥K)` by
`L27v12_mem_pCore_of_mem_normal_isNilpotent_of_isPGroup`, and mapping back down gives the
claim. -/
theorem L27v12_pCoreIn_of_mem_fittingIn_of_isPGroup_zpowers {G : Type} [Group G] [Finite G]
    (K : Subgroup G) (q : ℕ) [Fact q.Prime] {x : G}
    (hx : x ∈ Work.GW2.fittingIn K) (hxq : IsPGroup q ↥(Subgroup.zpowers x)) :
    x ∈ Work.GW2.pCoreIn q K := by
  rw [Work.GW2.fittingIn] at hx
  obtain ⟨y, hyfit, hyx⟩ := Subgroup.mem_map.mp hx
  -- `F(↥K)` is normal and nilpotent
  have hnil : Group.IsNilpotent ↥(Work.GW2.fitting ↥K) := L27cf_isNilpotent_fitting
  have hnorm : (Work.GW2.fitting ↥K).Normal := by
    rw [L27cf_fitting_eq_isaacsFitting]
    exact OddOrder.Isaacs.Ch01.fitting.normal ↥K
  -- transport the `q`-group hypothesis along `K.subtype`
  have hyq : IsPGroup q ↥(Subgroup.zpowers y) :=
    L27v12_zpowers_isPGroup_of_map_eq K.subtype K.subtype_injective hyx hxq
  rw [Work.GW2.pCoreIn]
  exact Subgroup.mem_map.mpr
    ⟨y, L27v12_mem_pCore_of_mem_normal_isNilpotent_of_isPGroup hnorm hnil hyfit hyq, hyx⟩

/-! ## 4. The target -/

/-- **The `2`-part of `F(Ĥ)` lies in `O₂(Ĥ)`.**  An element of `2`-power order of the Fitting
subgroup of `Ĥ` lies in the `2`-core of `Ĥ`: `⟨y⟩` is a cyclic `2`-group inside the normal
nilpotent subgroup `F(Ĥ) ⊴ Ĥ`, hence subnormal in `Ĥ` and therefore inside `O₂(Ĥ)`. -/
theorem L27v12_twopart_mem_pCoreIn_Hhat (G : Type) [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) {y : G} (hy : y ∈ Work.GW2.fittingIn B.Hhat)
    {k : ℕ} (h2 : orderOf y = 2 ^ k) :
    y ∈ Work.GW2.pCoreIn 2 B.Hhat := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine L27v12_pCoreIn_of_mem_fittingIn_of_isPGroup_zpowers B.Hhat 2 hy ?_
  -- `orderOf y = 2 ^ k` says exactly that `⟨y⟩` is a `2`-group
  exact IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, h2])

end Work.CORE2B
