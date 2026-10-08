import Mathlib
import Submission.Work.CORE3.A7V18.NP2Defs
import Submission.Work.CORE3.Case1aFrattiniApi
import Submission.Work.CORE2A.inf_U_S_eq_bot

set_option linter.style.haveILetI false

/-!
# CORE3 / A7V18: the centralizer of `V₂ = ⟨t, t₂⟩`

`Work.CORE3.A7V18.CentralizerV2`: in Bender's §3 setting (minimal-counterexample context,
`t ∈ S₀` the involution of the cyclic index-two subgroup, `t₂ ∈ S − S₀` an involution),

  `C_G(V₂) = (C_U(t₂)) · V₂`,   `V₂ = ⟨t, t₂⟩`, `U = O(H)`, `H = C_G(t)`, `S ∈ Syl₂(G)`.

## The argument

`C_G(V₂) = C_G(t) ⊓ C_G(t₂) = H ⊓ C_G(t₂)`, and `H = U ⊔ S` with `U = O(H)` normal in `H` and
`U ⊓ S = 1` (`Work.CORE3.H_eq_U_sup_S`, `Work.CORE2A.inf_U_S_eq_bot`), so an element `x` of the
centralizer is a product `x = u · y` with `u ∈ U`, `y ∈ S`
(`Work.CORE2A.exists_mul_of_mem_sup_of_normal`).  Since `U ⊴ H` and `U ⊓ S = 1`, the condition
`x a x⁻¹ = a` forces `y a y⁻¹ = a`: conjugating the element `y a y⁻¹ ∈ S` by `u` lands in the
coset `a U`, and `a U ⊓ S = {a}`.  Hence `y ∈ S ⊓ C_G(a) = ⟨t, a⟩` — the dihedral computation
`inf_S_centralizer_of_mem_notMem` below, which is `inf_S_centralizer_t1` with an arbitrary
`a ∈ S − S₀` in place of `t₁` — and `u = x y⁻¹ ∈ U ⊓ C_G(a)`, so `x ∈ (U ⊓ C_G(a)) · ⟨t, a⟩`.

The converse inclusion is immediate: `U ⊓ C_G(a) ≤ C_G(t)` (as `U ≤ H = C_G(t)`) centralizes
both generators `t` and `a` of `⟨t, a⟩`, and each generator commutes with `a`.
-/

namespace Work.CORE3.A7V18

open Subgroup
open Work.GW2

variable {G : Type} [Group G] [Finite G]

/-! ## The dihedral input: `S ⊓ C_G(a) = ⟨t, a⟩` for `a ∈ S − S₀` -/

/-- **The centralizer in `S` of an element outside the cyclic index-two subgroup.**  If
`a ∈ S − S₀` then the elements of the Sylow `2`-subgroup `S` commuting with `a` are exactly the
elements of `⟨t, a⟩`.

This is `Work.CORE3.Work.CORE3.inf_S_centralizer_t1` with `t₁` replaced by an arbitrary
`a ∈ S − S₀`: `a` inverts the cyclic subgroup `S₀`
(`Work.CORE2A.inverts_of_dihedral_cyclic_index_two`) and the only elements of `S₀` of order `≤ 2`
are `1` and `t` (cyclicity), so an element `y ∈ S` commuting with `a` either lies in `S₀` (where
it is `1` or `t`, as `a` acts by inversion there) or lies in the other coset, `y = a · c` with
`c ∈ S₀`, where commutation with `a` forces `c` to be `1` or `t` as well. -/
theorem inf_S_centralizer_of_mem_notMem (hBc : BenderCtx G) (B : BenderSetup G)
    (a : G) (haS : a ∈ (B.S : Subgroup G)) (ha0 : a ∉ B.S0) :
    (B.S : Subgroup G) ⊓ Subgroup.centralizer ({a} : Set G)
      = Subgroup.zpowers B.t ⊔ Subgroup.zpowers a := by
  -- `t` commutes with `a` (both lie in `S ≤ H = C_G(t)`)
  have hcomm : B.t * a = a * B.t :=
    (Subgroup.mem_centralizer_iff.mp (Work.CORE2A.bSetup_S_le_H B haS)) B.t (by simp)
  -- `a` is an involution
  have haorder : orderOf a = 2 := by
    obtain ⟨n, hn, hdih⟩ := Work.CORE3.SylowDihedral G hBc B
    exact Work.CORE3.OutsideS0OrderTwo G hBc B n hn hdih a haS ha0
  have ha2 : a * a = 1 := by
    have h : a ^ 2 = 1 := by rw [← haorder]; exact pow_orderOf_eq_one a
    simpa [pow_two] using h
  -- `a` inverts `S₀`
  have hinvS0 : Inverts a B.S0 := by
    obtain ⟨n, hn, hdih⟩ := Work.CORE3.SylowDihedral G hBc B
    exact Work.CORE2A.inverts_of_dihedral_cyclic_index_two n hn (B.S : Subgroup G) B.S0 hdih
      B.S0_le B.S0_cyclic B.S0_index a haS ha0
  -- the only elements of the cyclic group `S₀` squaring to `1` are `1` and `t`
  have hsq_of : ∀ x ∈ B.S0, x ^ 2 = 1 → x = 1 ∨ x = B.t := by
    intro x hx0 hx2
    have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with h | h
    · left; exact orderOf_eq_one_iff.mp h
    · right
      haveI : IsCyclic ↥B.S0 := B.S0_cyclic
      exact congrArg Subtype.val (Work.CORE2A.eq_of_orderOf_eq_two_of_isCyclic
        (a := (⟨x, hx0⟩ : ↥B.S0)) (b := (⟨B.t, B.t_mem⟩ : ↥B.S0))
        (by rw [Subgroup.orderOf_mk]; exact h)
        (by rw [Subgroup.orderOf_mk]; exact B.t_order))
  refine le_antisymm ?_ ?_
  · rintro y ⟨hyS, hyC⟩
    have hyc : a * y = y * a := (Subgroup.mem_centralizer_iff.mp hyC) a (by simp)
    by_cases hy0 : y ∈ B.S0
    · -- `y ∈ S₀`: `a` inverts `y` while `y` commutes with `a`, so `y ^ 2 = 1`, `y ∈ {1, t}`
      have hinv : a * y * a⁻¹ = y⁻¹ := hinvS0 y hy0
      have hfix : a * y * a⁻¹ = y := by rw [hyc]; group
      have hsq : y ^ 2 = 1 := by
        have hyinv : y⁻¹ = y := by rw [← hinv, hfix]
        calc y ^ 2 = y * y := pow_two y
          _ = y⁻¹ * y := by rw [hyinv]
          _ = 1 := inv_mul_cancel y
      rcases hsq_of y hy0 hsq with rfl | rfl
      · exact (Subgroup.zpowers B.t ⊔ Subgroup.zpowers a).one_mem
      · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t)
    · -- `y ∉ S₀`: write `y = a * c` with `c ∈ S₀`; commutation with `a` forces `c ^ 2 = 1`
      obtain ⟨c, hc, hceq⟩ := Work.CORE2A.exists_mul_of_notMem_of_relIndex_eq_two
        B.S0_index haS ha0 hyS hy0
      have hcc : a * c * a = c := by
        have h1 : a * (a * c) = (a * c) * a := by rw [← hceq]; exact hyc
        rw [← mul_assoc, ha2, one_mul] at h1
        exact h1.symm
      have hfix : a * c * a⁻¹ = c := by
        have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
        rw [hainv]; exact hcc
      have hinv : a * c * a⁻¹ = c⁻¹ := hinvS0 c hc
      have hsq : c ^ 2 = 1 := by
        have hcinv : c⁻¹ = c := by rw [← hinv, hfix]
        calc c ^ 2 = c * c := pow_two c
          _ = c⁻¹ * c := by rw [hcinv]
          _ = 1 := inv_mul_cancel c
      rcases hsq_of c hc hsq with rfl | rfl
      · rw [hceq, mul_one]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers a)
      · rw [hceq]
        exact (Subgroup.zpowers B.t ⊔ Subgroup.zpowers a).mul_mem
          (Subgroup.mem_sup_right (Subgroup.mem_zpowers a))
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers B.t))
  · refine le_inf ?_ ?_
    · exact sup_le (Subgroup.zpowers_le.mpr (B.S0_le B.t_mem)) (Subgroup.zpowers_le.mpr haS)
    · refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hcomm.symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        rfl

/-! ## The general form of the target -/

/-- `C_G(⟨t, a⟩) = (U ⊓ C_G(a)) · ⟨t, a⟩` for `a ∈ S − S₀`, `U = O(C_G(t))`.

This is the `(t, a)`-analogue of `Work.CORE3.Work.CORE3.centralizer_V1` (which is the case
`a = t₁`), with the dihedral input `inf_S_centralizer_of_mem_notMem`. -/
theorem centralizer_zpowers_sup_eq (hBc : BenderCtx G) (T : LocalToolkit) (B : BenderSetup G)
    (a : G) (haS : a ∈ (B.S : Subgroup G)) (ha0 : a ∉ B.S0) :
    Subgroup.centralizer ((Subgroup.zpowers B.t ⊔ Subgroup.zpowers a : Subgroup G) : Set G)
      = (B.U ⊓ Subgroup.centralizer ({a} : Set G)) ⊔
        (Subgroup.zpowers B.t ⊔ Subgroup.zpowers a) := by
  have hUsup : B.U ⊔ (B.S : Subgroup G) = B.H := Work.CORE3.H_eq_U_sup_S G T hBc B
  have hUinf : B.U ⊓ (B.S : Subgroup G) = ⊥ := Work.CORE2A.inf_U_S_eq_bot B
  have hSLeH : (B.S : Subgroup G) ≤ B.H := Work.CORE2A.bSetup_S_le_H B
  have hULeH : B.U ≤ B.H := Work.CORE2A.bSetup_U_le_H B
  have hUnorm : (B.U.subgroupOf B.H).Normal := Work.CORE2A.subgroupOf_oddCoreIn_normal B.H
  have haH : a ∈ B.H := hSLeH haS
  -- `t` and `a` commute (both lie in `S ≤ H = C_G(t)`)
  have hcomm : B.t * a = a * B.t :=
    (Subgroup.mem_centralizer_iff.mp (Work.CORE2A.bSetup_S_le_H B haS)) B.t (by simp)
  have hS_inf := inf_S_centralizer_of_mem_notMem hBc B a haS ha0
  have hkey : Subgroup.centralizer ((Subgroup.zpowers B.t ⊔ Subgroup.zpowers a : Subgroup G) :
        Set G) = B.H ⊓ Subgroup.centralizer ({a} : Set G) := by
    rw [Subgroup.centralizer_sup, Work.CORE3.Work.CORE3.centralizer_zpowers_eq,
      Work.CORE3.Work.CORE3.centralizer_zpowers_eq]
  rw [hkey]
  refine le_antisymm ?_ ?_
  · rintro x ⟨hxH, hxC⟩
    -- write `x = u * y` with `u ∈ U`, `y ∈ S`
    obtain ⟨u, hu, y, hy, huy⟩ :=
      Work.CORE2A.exists_mul_of_mem_sup_of_normal hULeH hSLeH hUnorm hUsup x hxH
    have hxc : a * x = x * a := (Subgroup.mem_centralizer_iff.mp hxC) a (by simp)
    have hxc' : a * (u * y) = (u * y) * a := by rw [huy]; exact hxc
    have hyS : y * a * y⁻¹ ∈ (B.S : Subgroup G) :=
      (B.S : Subgroup G).mul_mem ((B.S : Subgroup G).mul_mem hy haS)
        ((B.S : Subgroup G).inv_mem hy)
    have hya : u * (y * a * y⁻¹) * u⁻¹ = a := by
      calc u * (y * a * y⁻¹) * u⁻¹ = (u * y) * a * (u * y)⁻¹ := by group
        _ = a * (u * y) * (u * y)⁻¹ := by rw [← hxc']
        _ = a := by group
    have hy_eq : y * a * y⁻¹ = u⁻¹ * a * u := by
      have h2 : u * (y * a * y⁻¹) * u⁻¹ = u * (u⁻¹ * a * u) * u⁻¹ := by
        rw [hya]; group
      exact mul_left_cancel (mul_right_cancel h2)
    -- `a⁻¹ (y a y⁻¹) ∈ U` and also lies in `S`, hence it is `1` and `y` commutes with `a`
    have hconj : a⁻¹ * u⁻¹ * a ∈ B.U := by
      have h := Work.CORE3.Work.CORE3.U_conj_mem B (B.H.inv_mem haH) (B.U.inv_mem hu)
      simpa using h
    have hyU : a⁻¹ * (y * a * y⁻¹) ∈ B.U := by
      have heq : a⁻¹ * (y * a * y⁻¹) = (a⁻¹ * u⁻¹ * a) * u := by
        rw [hy_eq]; group
      rw [heq]
      exact B.U.mul_mem hconj hu
    have hy_bot : a⁻¹ * (y * a * y⁻¹) ∈ (⊥ : Subgroup G) := by
      rw [← hUinf]
      exact ⟨hyU, (B.S : Subgroup G).mul_mem ((B.S : Subgroup G).inv_mem haS) hyS⟩
    have hy_eq_a : y * a * y⁻¹ = a := by
      have hone : a⁻¹ * (y * a * y⁻¹) = 1 := Subgroup.mem_bot.mp hy_bot
      calc y * a * y⁻¹ = a * (a⁻¹ * (y * a * y⁻¹)) := by group
        _ = a * 1 := by rw [hone]
        _ = a := mul_one a
    have hyC : y ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : z = a := Set.mem_singleton_iff.mp hz
      rw [hz']
      have h1 : y * a = a * y := by
        calc y * a = (y * a * y⁻¹) * y := by group
          _ = a * y := by rw [hy_eq_a]
      exact h1.symm
    have huC : u ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : z = a := Set.mem_singleton_iff.mp hz
      rw [hz']
      have h1 : u * a * u⁻¹ = a := by
        calc u * a * u⁻¹ = u * (y * a * y⁻¹) * u⁻¹ := by rw [hy_eq_a]
          _ = a := hya
      have h2 : u * a = a * u := by
        have h3 := congrArg (fun z => z * u) h1
        simpa [mul_assoc] using h3
      exact h2.symm
    have hyV : y ∈ Subgroup.zpowers B.t ⊔ Subgroup.zpowers a := by
      rw [← hS_inf]; exact ⟨hy, hyC⟩
    have huUC : u ∈ B.U ⊓ Subgroup.centralizer ({a} : Set G) := ⟨hu, huC⟩
    rw [← huy]
    exact Subgroup.mul_mem_sup huUC hyV
  · refine sup_le ?_ ?_
    · exact le_inf (le_trans inf_le_left hULeH) inf_le_right
    · -- `⟨t, a⟩ ≤ H` and `⟨t, a⟩ ≤ C_G(a)` (both generators commute with `a`)
      refine le_inf ?_ ?_
      · exact sup_le (Subgroup.zpowers_le.mpr (hSLeH (B.S0_le B.t_mem)))
          (Subgroup.zpowers_le.mpr haH)
      · refine sup_le ?_ ?_
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
          intro z hz
          have hz' : z = a := Set.mem_singleton_iff.mp hz
          rw [hz']
          exact hcomm.symm
        · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
          intro z hz
          have hz' : z = a := Set.mem_singleton_iff.mp hz
          rw [hz']

/-! ## The deliverable -/

theorem CentralizerV2 (G : Type) [Group G] [Finite G] (T : Work.GW2.LocalToolkit)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (D : Work.GW2.Case1aData B) :
    Subgroup.centralizer ((Work.CORE3.A7V18.V2 B D : Subgroup G) : Set G)
      = (B.U ⊓ Subgroup.centralizer ({D.t2} : Set G)) ⊔ Work.CORE3.A7V18.V2 B D := by
  rw [Work.CORE3.A7V18.V2]
  exact centralizer_zpowers_sup_eq hBc T B D.t2 D.t2_mem D.t2_nmem

end Work.CORE3.A7V18
