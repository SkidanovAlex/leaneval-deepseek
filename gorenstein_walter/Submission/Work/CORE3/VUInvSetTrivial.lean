import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.SylowCentralizerPcoreInTwo
import Submission.Work.CORE3.exists_mul_of_mem_sup_of_normal
import Submission.Work.CORE3.Case1bFive

set_option linter.dupNamespace false
set_option linter.style.haveILetI false

/-!
# CORE3: Bender 1981 §3, (5) — `I_{VU}(y) = 1` for every involution `y ∉ Ĥ`

The leaf `Work.CORE3.VUInvSetTrivial`, the unbundled form of Bender's statement (5) (Bender
1981, J. Algebra 70, §3, p. 223): in Case (1) of Theorem 2.10, with `V = O₂(Ĥ)` a four-group and
`U = O(Ĥ)`, every involution `y ∉ Ĥ` inverts no non-trivial element of `VU = V ⊔ U`.

The proof follows Bender literally.  For `x ∈ I_{VU}(y)`:

* `x ∈ VU = V·U`; writing `x = v·u` with `v ∈ V`, `u ∈ U` and using `V ≤ C_G(U)`, the odd power
  `x ^ |U| = v` is inverted by `y`; as `v² = 1` this says that `y` *centralizes* `v`; if `v ≠ 1`
  then `y ∈ C_G(v) ≤ Ĥ` (Claim A), contradicting `y ∉ Ĥ`.  Hence `x ∈ U`.
* For `1 ≠ x ∈ U` inverted by `y` the auxiliary lemmas of this area give the contradiction
  (`not_invset_U_mem` below): `V` is a Sylow 2-subgroup of `C_G(x)`
  (`SylowCentralizerPcoreInTwo`), so Sylow conjugacy inside the `y`-invariant `C_G(x)` produces
  `c ∈ C_G(x)` with `c*y ∈ N_G(V) = Ĥ` still inverting `x`; then
  `exists_involution_inverting_of_mem_U` produces an involution `s ∈ Ĥ − V` inverting `x`; hence
  `x ∈ I_U(s) = D.K ⊆ F(U)`, so `N_G(⟨x⟩) ≤ Ĥ` by Case (1) (second clause), while
  `y ∈ N_G(⟨x⟩)` — contradiction.
-/

namespace Work.CORE3

open Work.GW2

open Subgroup

/-- **Bender 1981 §3, p. 223, (5), the `U`-part.**

No involution `y ∉ Ĥ` inverts a non-trivial element of `U = O(Ĥ)`.

This assembles the auxiliary lemmas of the area: `V = O₂(Ĥ)` is a Sylow 2-subgroup of `C_G(x)`
(`SylowCentralizerPcoreInTwo`); Sylow conjugacy inside the `y`-invariant `C_G(x)`
(`sylow_conj_of_odd_relIndex`) moves `y` into `N_G(V) = Ĥ` while still inverting `x`; and
`exists_involution_inverting_of_mem_U` turns any `h ∈ Ĥ` inverting `x` into an involution
`s ∈ Ĥ − V` inverting `x`.  Then `x ∈ D.K ⊆ F(U)` and Case (1) applied to `⟨x⟩` contradicts
`y ∉ Ĥ`. -/
theorem not_invset_U_mem (I : Case1Inputs) (G : Type) [Group G] [Finite G]
    (hBc : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B) (D : Case1bData B) {x y : G}
    (hxU : x ∈ B.U) (hx1 : x ≠ 1) (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    (hxy : y * x * y⁻¹ = x⁻¹) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h26 : Thm26Concl B := I.h26 G I.T.ft hBc B
  have hV2 : IsPGroup 2 (pCoreIn 2 B.Hhat) := Work.CORE2A.thm26Concl_isPGroup_O2 h26
  have hVcU : pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
    rw [← Work.CORE2A.thm26Concl_centralizer_eq h26]; exact inf_le_right
  have hNV : Subgroup.normalizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) = B.Hhat :=
    NormalizerPcoreEqHhat G hBc B D.four
  -- `y⁻¹ x y = x⁻¹`
  have hyx : y⁻¹ * x * y = x⁻¹ := by
    have h' := congrArg (fun z => y⁻¹ * z * y) hxy
    have h : y⁻¹ * x⁻¹ * y = x := by simpa [mul_assoc] using h'.symm
    have h2 : y⁻¹ * x * y = (y⁻¹ * x⁻¹ * y)⁻¹ := by group
    rw [h2, h]
  -- `V ≤ C_G(x)`
  have hVcx : pCoreIn 2 B.Hhat ≤ Subgroup.centralizer ({x} : Set G) :=
    le_trans hVcU (Subgroup.centralizer_le (by
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]; exact hxU))
  -- `y` normalizes `C_G(x)`
  have hyC : Work.GW2.conjSub y (Subgroup.centralizer ({x} : Set G)) ≤
      Subgroup.centralizer ({x} : Set G) := by
    intro w hw
    rw [Work.CORE2A.mem_conjSub_iff] at hw
    rw [Subgroup.mem_centralizer_iff] at hw ⊢
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    have hx : x = y * x⁻¹ * y⁻¹ := by
      have h' := congrArg (fun t => y * t * y⁻¹) hyx
      simpa [mul_assoc] using h'
    have hcinv : x⁻¹ * (y⁻¹ * w * y) = (y⁻¹ * w * y) * x⁻¹ :=
      ((commute_iff_eq x (y⁻¹ * w * y)).mpr (hw x (by simp))).inv_left.eq
    have h1 : (y * x⁻¹ * y⁻¹) * w = y * (x⁻¹ * (y⁻¹ * w * y)) * y⁻¹ := by group
    have h2 : y * ((y⁻¹ * w * y) * x⁻¹) * y⁻¹ = w * (y * x⁻¹ * y⁻¹) := by group
    rw [hx, h1, hcinv, h2]
  -- `V` is a Sylow 2-subgroup of `C_G(x)`
  have hodd := odd_relIndex_centralizer_of_mem_U I G hBc B h1 D hxU hx1 hy2 hyH hxy
  -- Sylow conjugacy of `yVy⁻¹` and `V` inside `C_G(x)`
  obtain ⟨c, hc, hconj⟩ := sylow_conj_of_odd_relIndex hVcx hyC hV2 hodd
  have hcx : c * x * c⁻¹ = x := by
    have hcomm : x * c = c * x := (Subgroup.mem_centralizer_iff.mp hc) x (by simp)
    rw [← hcomm]; group
  -- `h := c * y ∈ N_G(V) = Ĥ` inverts `x`
  have hhH : c * y ∈ B.Hhat := by
    rw [← hNV, Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have h1 : y * z * y⁻¹ ∈ Work.GW2.conjSub y (pCoreIn 2 B.Hhat) := by
        rw [Work.CORE2A.mem_conjSub_iff]
        have h4 : y⁻¹ * (y * z * y⁻¹) * y = z := by group
        rw [h4]; exact hz
      have h2 : c * (y * z * y⁻¹) * c⁻¹ ∈ pCoreIn 2 B.Hhat := (hconj _).mp h1
      have h3 : (c * y) * z * (c * y)⁻¹ = c * (y * z * y⁻¹) * c⁻¹ := by group
      rw [h3]; exact h2
    · intro hz
      have h2 : c * (y * z * y⁻¹) * c⁻¹ ∈ pCoreIn 2 B.Hhat := by
        have h3 : c * (y * z * y⁻¹) * c⁻¹ = (c * y) * z * (c * y)⁻¹ := by group
        rw [h3]; exact hz
      have h1 : y * z * y⁻¹ ∈ Work.GW2.conjSub y (pCoreIn 2 B.Hhat) := (hconj _).mpr h2
      rw [Work.CORE2A.mem_conjSub_iff] at h1
      have h4 : y⁻¹ * (y * z * y⁻¹) * y = z := by group
      rwa [h4] at h1
  have hcxinv : c * x⁻¹ * c⁻¹ = x⁻¹ := by
    have h' := congrArg Inv.inv hcx
    simpa [mul_assoc] using h'
  have hhx : (c * y) * x * (c * y)⁻¹ = x⁻¹ := by
    have h3 : (c * y) * x * (c * y)⁻¹ = c * (y * x * y⁻¹) * c⁻¹ := by group
    rw [h3, hxy, hcxinv]
  -- an involution `s ∈ Ĥ − V` inverting `x`
  obtain ⟨s, hsH, hs2, hsV, hsx⟩ :=
    exists_involution_inverting_of_mem_U I G hBc B h1 D hxU hx1 hhH hhx
  have hxK : x ∈ D.K := by
    have hmem : x ∈ (D.K : Set G) := by
      rw [D.inv s hsH hs2 hsV]
      exact ⟨hxU, hsx⟩
    exact hmem
  have hle : Subgroup.zpowers x ≤ fittingIn B.U := by
    rw [Subgroup.zpowers_le]; exact D.hall.1 hxK
  have hne : Subgroup.zpowers x ≠ ⊥ := fun hbot => hx1 (Subgroup.zpowers_eq_bot.mp hbot)
  have hnorm : Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) ≤ B.Hhat :=
    h1.2 _ hne hle
  have hyN : y ∈ Subgroup.normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
    have hmap : Subgroup.map (MulAut.conj y).toMonoidHom (Subgroup.zpowers x) =
        Subgroup.zpowers x := by
      rw [MonoidHom.map_zpowers]
      change Subgroup.zpowers ((MulAut.conj y) x) = Subgroup.zpowers x
      rw [MulAut.conj_apply, hxy, Subgroup.zpowers_inv]
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rw [← hmap]
      exact ⟨z, hz, rfl⟩
    · intro hz
      have h1' : y * z * y⁻¹ ∈ Subgroup.map (MulAut.conj y).toMonoidHom
          (Subgroup.zpowers x) := by rw [hmap]; exact hz
      rw [Subgroup.mem_map] at h1'
      obtain ⟨w, hw, hwy⟩ := h1'
      have h2 : z = w := by
        have h4 := congrArg (fun t => y⁻¹ * t * y) hwy
        have h5 : w = z := by simpa [MulAut.conj_apply, mul_assoc] using h4
        exact h5.symm
      rw [h2]; exact hw
  exact hyH (hnorm hyN)

theorem VUInvSetTrivial (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs) (h : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B) :
    ∀ y : G, orderOf y = 2 → y ∉ B.Hhat →
      Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) y = {1} := by
  intro y hy2 hyH
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h26 : Thm26Concl B := I.h26 G I.T.ft h B
  have hVleH : pCoreIn 2 B.Hhat ≤ B.Hhat := Work.CORE2A.thm26Concl_O2_le_Hhat h26
  have hUleH : B.U ≤ B.Hhat := Work.CORE2A.thm26Concl_U_le_Hhat h26
  have hVcU : pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
    rw [← Work.CORE2A.thm26Concl_centralizer_eq h26]; exact inf_le_right
  have hUodd : Odd (Nat.card B.U) := Work.CORE2A.bSetup_U_odd B
  have hCA : ∀ v ∈ pCoreIn 2 B.Hhat, v ≠ 1 →
      Subgroup.centralizer ({v} : Set G) ≤ B.Hhat :=
    fun v hv hv1 => centralizer_le_Hhat_of_mem_pCoreIn_two G h B I.T.fus h26 D.four hv hv1
  have hNV : Subgroup.normalizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) = B.Hhat :=
    NormalizerPcoreEqHhat G h B D.four
  have hVnorm : ∀ s ∈ B.Hhat, ∀ v ∈ pCoreIn 2 B.Hhat, s * v * s⁻¹ ∈ pCoreIn 2 B.Hhat := by
    intro s hs v hv
    have h1' : B.Hhat ≤ Subgroup.normalizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
      rw [hNV]
    exact ((Subgroup.mem_normalizer_iff.mp (h1' hs)) v).mp hv
  have hUnorm : ∀ s ∈ B.Hhat, ∀ u ∈ B.U, s * u * s⁻¹ ∈ B.U := by
    intro s hs u hu
    have h1' : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := by
      rw [← Work.CORE2A.thm26Concl_oddCore_eq h26]
      simpa [oddCoreIn] using
        Work.CORE3.le_normalizer_map_subtype B.Hhat (Work.GW2.oddCore ↥B.Hhat)
    exact ((Subgroup.mem_normalizer_iff.mp (h1' hs)) u).mp hu
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
  · exact ⟨Subgroup.mem_sup_left (Subgroup.one_mem _), by simp⟩
  · intro x hx
    obtain ⟨hxVU, hxy⟩ := hx
    obtain ⟨v, hv, u, hu, hxeq⟩ :=
      Work.CORE3.exists_mul_of_mem_sup_of_normal (S := B.Hhat) (V := pCoreIn 2 B.Hhat)
        (U := B.U) hVleH hUleH hVnorm hUnorm x hxVU
    by_cases hv1 : v = 1
    · have hxU : x ∈ B.U := by rw [hxeq, hv1, one_mul]; exact hu
      by_cases hx1 : x = 1
      · exact hx1
      · exact (not_invset_U_mem I G h B h1 D hxU hx1 hy2 hyH hxy).elim
    · exfalso
      -- `y` inverts `x`, hence `x ^ |U| = v` is fixed by `y`
      have hum : u ^ Nat.card B.U = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard B.U hu)
      have hv2 : v ^ 2 = 1 := D.four.2 v hv
      obtain ⟨k, hk⟩ := hUodd
      have hvm : v ^ Nat.card B.U = v := by
        rw [hk, pow_succ, pow_mul, hv2, one_pow, one_mul]
      have hcomm : v * u = u * v := ((Subgroup.mem_centralizer_iff.mp (hVcU hv)) u hu).symm
      have hpow : ∀ m : ℕ, (v * u) ^ m = v ^ m * u ^ m :=
        fun m => ((commute_iff_eq v u).mpr hcomm).mul_pow m
      have hxpow : x ^ Nat.card B.U = v := by
        rw [hxeq, hpow, hvm, hum, mul_one]
      have hyx : y * x ^ Nat.card B.U * y⁻¹ = (x ^ Nat.card B.U)⁻¹ := by
        rw [← MulAut.conj_apply, map_pow]
        have h1' : (MulAut.conj y) x = x⁻¹ := by rw [MulAut.conj_apply]; exact hxy
        rw [h1', inv_pow]
      have hvv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hv2)
      have hyv : y * v * y⁻¹ = v := by
        rw [← hxpow, hyx, hxpow, hvv]
      have hyc : y ∈ Subgroup.centralizer ({v} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        have h2 := congrArg (fun w => w * y) hyv
        have h1' : y * v = v * y := by simpa [mul_assoc] using h2
        exact h1'.symm
      exact hyH (hCA v hv hv1 hyc)

end Work.CORE3
