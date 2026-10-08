import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.exists_mul_of_mem_sup_of_normal
import Submission.Work.CORE3.SylowCentralizerPcoreInTwo
import Submission.Work.CORE3.InvolutionInvertingMemU

open scoped Pointwise

set_option linter.dupNamespace false
set_option linter.style.haveILetI false

namespace Work.CORE3


open Work.GW2

/-- In a group of cardinality `2`, all elements commute.  (Used to see that the `index ≠ 2`
side condition of `InvolutionFusionProp` is automatic in the minimal-counterexample setting:
a normal subgroup of index `2` in a simple non-abelian group is trivial, forcing `|G| = 2`.) -/
theorem commute_of_card_two {G : Type*} [Group G] (hcard : Nat.card G = 2) (a b : G) :
    a * b = b * a := by
  have h2 : ∀ c : G, c * c = 1 := by
    intro c
    have hdvd : orderOf c ∣ 2 := by
      simpa [hcard] using orderOf_dvd_natCard c
    have h3 : c ^ orderOf c = 1 := pow_orderOf_eq_one c
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · rw [h1, pow_one] at h3
      rw [h3, one_mul]
    · rw [h1] at h3
      simpa [pow_two] using h3
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (h2 (a * b))).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by
          rw [inv_eq_of_mul_eq_one_right (h2 b), inv_eq_of_mul_eq_one_right (h2 a)]

/-- An element of odd order cannot invert a nontrivial element of odd order.  Indeed, if
`g * a * g⁻¹ = a⁻¹` and `orderOf g = 2k+1` then `g^(2k+1) = 1`, so `a = a⁻¹`, i.e. `a ^ 2 = 1`;
thus `orderOf a ∣ 2`, and as `orderOf a` is odd, `a = 1`. -/
theorem eq_one_of_conj_eq_inv_of_odd {G : Type*} [Group G] {g a : G}
    (hg : Odd (orderOf g)) (h : g * a * g⁻¹ = a⁻¹) (ha : Odd (orderOf a)) : a = 1 := by
  have hstep : ∀ i : ℕ, g ^ (2 * i + 1) * a * (g ^ (2 * i + 1))⁻¹ = a⁻¹ := by
    intro i
    induction i with
    | zero => simpa using h
    | succ j ih =>
      have h2 : g ^ 2 * a * (g ^ 2)⁻¹ = a := by
        have h1 : g ^ 2 * a * (g ^ 2)⁻¹ = g * (g * a * g⁻¹) * g⁻¹ := by
          rw [pow_two, mul_inv_rev]; group
        rw [h1, h]
        have h3 : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
        rw [h3, h, inv_inv]
      have h4 : 2 * (j + 1) + 1 = 2 * j + 1 + 2 := by ring
      rw [h4, pow_add]
      have h5 : g ^ (2 * j + 1) * g ^ 2 * a * (g ^ (2 * j + 1) * g ^ 2)⁻¹
          = g ^ (2 * j + 1) * (g ^ 2 * a * (g ^ 2)⁻¹) * (g ^ (2 * j + 1))⁻¹ := by
        rw [mul_inv_rev]; group
      rw [h5, h2, ih]
  obtain ⟨k, hk⟩ := hg
  have hgk : g ^ (2 * k + 1) = 1 := by rw [← hk]; exact pow_orderOf_eq_one g
  have haeq : a = a⁻¹ := by
    have h1 := hstep k
    rw [hgk] at h1
    simpa using h1
  have ha2 : a ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [haeq]
    exact mul_inv_cancel a
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr ha2
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
  · exact orderOf_eq_one_iff.mp h1
  · exact absurd (h1 ▸ ha) (by decide)




open Work.GW2

/-- **Bender 1981 §3, p. 223 (Claim A):** `C_G(v) ≤ Ĥ` for every `1 ≠ v ∈ O₂(Ĥ)`.

`N_G(V) = Ĥ` (`Work.CORE3.NormalizerPcoreEqHhat`) is transitive on `V^#` by clause 2 of
`InvolutionFusionProp`, so `v = g t g⁻¹` for some `g ∈ Ĥ` (here `t ∈ V` is the special
involution with `C_G(t) = B.H ≤ Ĥ`); hence `C_G(v) = g C_G(t) g⁻¹ ≤ Ĥ`. -/
theorem centralizer_le_Hhat_of_mem_pCoreIn_two (G : Type) [Group G] [Finite G]
    (h : BenderCtx G) (B : BenderSetup G) (hfus : InvolutionFusionProp)
    (h26 : Thm26Concl B) (h4 : IsFourGroup (pCoreIn 2 B.Hhat)) {v : G}
    (hv : v ∈ pCoreIn 2 B.Hhat) (hv1 : v ≠ 1) :
    Subgroup.centralizer ({v} : Set G) ≤ B.Hhat := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup G := h.simple
  -- `t ∈ V`
  have htV : B.t ∈ pCoreIn 2 B.Hhat := by
    rw [← Work.CORE2A.thm26Concl_centralizer_eq h26, Subgroup.mem_inf]
    refine ⟨Work.CORE2A.bSetup_t_mem_S B, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun u hu =>
      ((Subgroup.mem_centralizer_iff.mp (Work.CORE2A.bSetup_U_le_H B hu)) B.t
        (by simp)).symm)
  -- no normal subgroup of index two
  have hno2 : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
    intro N hN h2
    haveI := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hb | ht
    · have hcard : Nat.card G = 2 := by
        rw [← Subgroup.index_bot, ← hb]; exact h2
      obtain ⟨a, b, hab⟩ := h.nonab
      exact hab (commute_of_card_two hcard a b)
    · rw [ht, Subgroup.index_top] at h2
      exact absurd h2 (by norm_num)
  obtain ⟨n, hn2, hdih⟩ := SylowDihedral G h B
  obtain ⟨g, hg, hgt⟩ := (hfus G B.S n hn2 hdih hno2).2 (pCoreIn 2 B.Hhat) h4 B.t htV v hv
    (Work.CORE2A.bSetup_t_ne_one B) hv1
  rw [NormalizerPcoreEqHhat G h B h4] at hg
  intro c hc
  have hvc : v * c = c * v := (Subgroup.mem_centralizer_iff.mp hc) v (by simp)
  have hd : g⁻¹ * c * g ∈ B.H := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    have h1 : B.t * (g⁻¹ * c * g) = g⁻¹ * (v * c) * g := by rw [← hgt]; group
    have h2 : (g⁻¹ * c * g) * B.t = g⁻¹ * (c * v) * g := by rw [← hgt]; group
    rw [h1, h2, hvc]
  have hdH : g⁻¹ * c * g ∈ B.Hhat := B.H_le_Hhat hd
  have hce : c = g * (g⁻¹ * c * g) * g⁻¹ := by group
  rw [hce]
  exact B.Hhat.mul_mem (B.Hhat.mul_mem hg hdH) (B.Hhat.inv_mem hg)




open Work.GW2

/-- **Auxiliary (Bender 1981 §3, p. 223):** `V = O₂(Ĥ)` is a Sylow 2-subgroup of `C_G(x)` for
`1 ≠ x ∈ U = O(Ĥ)` inverted by an involution `y ∉ Ĥ`.

If `T ∈ Syl₂(C_G(x))` with `V ≤ T` had order `8`, then `V ⊴ T` gives `T ≤ N_G(V) = Ĥ` and `T` is
a Sylow 2-subgroup of `G`; conjugating `y T y⁻¹` back into `T` by an element of `C_G(x)` produces
`g ∈ N_G(T)` inverting `x`, and in `N_G(T)/T` (of odd order) the element `g T` would invert the
nontrivial odd-order element `x T`, impossible (`eq_one_of_conj_eq_inv_of_odd`). -/
theorem odd_relIndex_centralizer_of_mem_U (I : Case1Inputs) (G : Type) [Group G] [Finite G]
    (hBc : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B) (D : Case1bData B) {x y : G}
    (hxU : x ∈ B.U) (hx1 : x ≠ 1) (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    (hxy : y * x * y⁻¹ = x⁻¹) :
    Odd ((pCoreIn 2 B.Hhat).relIndex (Subgroup.centralizer ({x} : Set G))) :=
  Work.CORE3.SylowCentralizerPcoreInTwo I G hBc B h1 D hxU hx1 hy2 hyH hxy

/-- **Auxiliary:** an involution `s ∈ Ĥ − V` inverting `x ∈ U^#` exists as soon as some `h ∈ Ĥ`
inverts `x`.

The odd part of `h` gives a `2`-element `g ∈ Ĥ` with `g x g⁻¹ = x⁻¹`; `g² ∈ V` (as `|Ĥ/V|` has
`2`-part `2`), and if `g² ≠ 1` then `v := γ(g)·g` for a suitable `v ∈ V` makes `g v` an
involution (`γ` the action of `g` on the four-group `V`). -/
theorem exists_involution_inverting_of_mem_U (I : Case1Inputs) (G : Type) [Group G] [Finite G]
    (hBc : BenderCtx G) (B : BenderSetup G) (h1 : Case1 B) (D : Case1bData B) {x h : G}
    (hxU : x ∈ B.U) (hx1 : x ≠ 1) (hhH : h ∈ B.Hhat) (hhx : h * x * h⁻¹ = x⁻¹) :
    ∃ s : G, s ∈ B.Hhat ∧ orderOf s = 2 ∧ s ∉ pCoreIn 2 B.Hhat ∧ s * x * s⁻¹ = x⁻¹ :=
  Work.CORE3.InvolutionInvertingMemU I G hBc B h1 D hxU hx1 hhH hhx

/-- **Sylow conjugacy inside a `y`-invariant subgroup.**  If `V ≤ C` is a Sylow 2-subgroup of
`C` (i.e. `Odd (V.relIndex C)`) and `y` normalizes `C`, then `yVy⁻¹` is conjugate to `V` by an
element of `C`: there is `c ∈ C` with `z ∈ yVy⁻¹ ↔ c z c⁻¹ ∈ V` for all `z`. -/
theorem sylow_conj_of_odd_relIndex {G : Type} [Group G] [Finite G]
    {C V : Subgroup G} {y : G} (hVC : V ≤ C) (hyC : Work.GW2.conjSub y C ≤ C)
    (hV2 : IsPGroup 2 V) (hodd : Odd (V.relIndex C)) :
    ∃ c ∈ C, ∀ z : G, z ∈ Work.GW2.conjSub y V ↔ c * z * c⁻¹ ∈ V := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hW : Work.GW2.conjSub y V ≤ C :=
    le_trans (Work.CORE2A.conjSub_mono hVC y) hyC
  have hnd : ¬ 2 ∣ V.relIndex C :=
    fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  have hPa : IsPGroup 2 (V.subgroupOf C) :=
    IsPGroup.of_equiv hV2 (Subgroup.subgroupOfEquivOfLe hVC).symm
  have hQa : IsPGroup 2 ((Work.GW2.conjSub y V).subgroupOf C) :=
    IsPGroup.of_equiv (hV2.map (MulAut.conj y).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hW).symm
  have hPa_index : (V.subgroupOf C).index = V.relIndex C := rfl
  have hQa_index : ((Work.GW2.conjSub y V).subgroupOf C).index = (V.subgroupOf C).index := by
    have h1 := Subgroup.card_mul_index ((Work.GW2.conjSub y V).subgroupOf C)
    have h2 := Subgroup.card_mul_index (V.subgroupOf C)
    have hcard : Nat.card ↥((Work.GW2.conjSub y V).subgroupOf C) =
        Nat.card ↥(V.subgroupOf C) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hW).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVC).toEquiv, Work.CORE2A.card_conjSub]
    have h3 := h1.trans h2.symm
    rw [hcard] at h3
    exact Nat.mul_left_cancel Nat.card_pos h3
  let P : Sylow 2 ↥C := hPa.toSylow (by rw [hPa_index]; exact hnd)
  let Q : Sylow 2 ↥C := hQa.toSylow (by rw [hQa_index, hPa_index]; exact hnd)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (M := ↥C) Q P
  have hsmul : MulAut.conj g • ((Work.GW2.conjSub y V).subgroupOf C) = V.subgroupOf C := by
    have h := congrArg (fun S : Sylow 2 ↥C => (S : Subgroup ↥C)) hg
    rw [Sylow.coe_subgroup_smul] at h
    have hQcoe : (Q : Subgroup ↥C) = (Work.GW2.conjSub y V).subgroupOf C := rfl
    have hPcoe : (P : Subgroup ↥C) = V.subgroupOf C := rfl
    rw [hQcoe, hPcoe] at h
    exact h
  refine ⟨(g : G), g.2, ?_⟩
  intro z
  constructor
  · intro hz
    have hm : MulAut.conj g • (⟨z, hW hz⟩ : ↥C) ∈
        MulAut.conj g • ((Work.GW2.conjSub y V).subgroupOf C) :=
      Subgroup.smul_mem_pointwise_smul (⟨z, hW hz⟩ : ↥C) (MulAut.conj g)
        ((Work.GW2.conjSub y V).subgroupOf C) (Subgroup.mem_subgroupOf.mpr hz)
    rw [hsmul] at hm
    have hm' : (((MulAut.conj g) (⟨z, hW hz⟩ : ↥C) : ↥C) : G) ∈ V :=
      Subgroup.mem_subgroupOf.mp hm
    simpa [MulAut.conj_apply] using hm'
  · intro hz
    have hzC : (g : G) * z * (g : G)⁻¹ ∈ C := hVC hz
    have hm : (⟨(g : G) * z * (g : G)⁻¹, hzC⟩ : ↥C) ∈
        MulAut.conj g • ((Work.GW2.conjSub y V).subgroupOf C) := by
      rw [hsmul]
      exact Subgroup.mem_subgroupOf.mpr hz
    obtain ⟨s, hsQ, hs⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hm
    have hsG : (s : G) = z := by
      have h2 := congrArg (fun w : ↥C => (w : G)) hs
      simp only [MulAut.smul_def, MulAut.conj_apply, Subgroup.coe_mul] at h2
      exact mul_left_cancel (mul_right_cancel h2)
    rw [← hsG]
    exact Subgroup.mem_subgroupOf.mp hsQ

/-- **Bender 1981 §3, p. 223 (5)**, the decisive sub-case: no involution `y ∉ Ĥ` inverts a
nontrivial element of `U = O(Ĥ)`.

(`V = O₂(Ĥ)` is a Sylow 2-subgroup of `C_G(x)` for `x ∈ U^#`; conjugating `y` by a suitable
element of `C_G(x)` produces `h ∈ N_G(V) = Ĥ` inverting `x`; an involution `s ∈ Ĥ − V`
inverting `x` then lies in `D.K = I_U(s) ≤ F(U)`, so `⟨x⟩ ≤ F(U)` and `Case1`'s second clause
gives `N_G(⟨x⟩) ≤ Ĥ ∋ y`, a contradiction.) -/
theorem not_invset_U_of_mem (I : Case1Inputs) (G : Type) [Group G] [Finite G]
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
  have hne : Subgroup.zpowers x ≠ ⊥ := fun h => hx1 (Subgroup.zpowers_eq_bot.mp h)
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
      have h1 : y * z * y⁻¹ ∈ Subgroup.map (MulAut.conj y).toMonoidHom
          (Subgroup.zpowers x) := by rw [hmap]; exact hz
      rw [Subgroup.mem_map] at h1
      obtain ⟨w, hw, hwy⟩ := h1
      have h2 : z = w := by
        have h4 := congrArg (fun t => y⁻¹ * t * y) hwy
        have h5 : w = z := by simpa [MulAut.conj_apply, mul_assoc] using h4
        exact h5.symm
      rw [h2]; exact hw
  exact hyH (hnorm hyN)





open Work.GW2

/-- Bender 1981 §3, p. 223, (5).  Deliverable `Work.GW2.Case1bFiveProp`.

`I_{VU}(y) = 1` for every involution `y ∉ Ĥ`, where `V = O₂(Ĥ)`, `U = O(Ĥ)`.

Writing `x ∈ V ⊔ U = V·U` as `x = v·u` (`v ∈ V`, `u ∈ U`, `V` and `U` normal in `Ĥ` and
commuting), the element `x ^ |U| = v` is inverted by `y`; if `v ≠ 1` then `v ∈ V^#` is fixed by
`y` (as `v² = 1`), so `y ∈ C_G(v) ≤ Ĥ` by Claim A (`centralizer_le_Hhat_of_mem_pCoreIn_two`), a
contradiction.  Hence `x ∈ U`, which is excluded by `not_invset_U_of_mem`. -/
theorem Case1bFive (I : Case1Inputs) : Case1bFiveProp := by
  intro G _ _ hFT hBc B h1 D y hy2 hyH
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h26 : Thm26Concl B := I.h26 G hFT hBc B
  have hVleH : pCoreIn 2 B.Hhat ≤ B.Hhat := Work.CORE2A.thm26Concl_O2_le_Hhat h26
  have hUleH : B.U ≤ B.Hhat := Work.CORE2A.thm26Concl_U_le_Hhat h26
  have hVcU : pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
    rw [← Work.CORE2A.thm26Concl_centralizer_eq h26]; exact inf_le_right
  have hUodd : Odd (Nat.card B.U) := Work.CORE2A.bSetup_U_odd B
  have hCA : ∀ v ∈ pCoreIn 2 B.Hhat, v ≠ 1 →
      Subgroup.centralizer ({v} : Set G) ≤ B.Hhat :=
    fun v hv hv1 => centralizer_le_Hhat_of_mem_pCoreIn_two G hBc B I.T.fus h26 D.four hv hv1
  have hNV : Subgroup.normalizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) = B.Hhat :=
    NormalizerPcoreEqHhat G hBc B D.four
  have hVnorm : ∀ s ∈ B.Hhat, ∀ v ∈ pCoreIn 2 B.Hhat, s * v * s⁻¹ ∈ pCoreIn 2 B.Hhat := by
    intro s hs v hv
    have h1 : B.Hhat ≤ Subgroup.normalizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
      rw [hNV]
    exact ((Subgroup.mem_normalizer_iff.mp (h1 hs)) v).mp hv
  have hUnorm : ∀ s ∈ B.Hhat, ∀ u ∈ B.U, s * u * s⁻¹ ∈ B.U := by
    intro s hs u hu
    have h1 : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := by
      rw [← Work.CORE2A.thm26Concl_oddCore_eq h26]
      simpa [oddCoreIn] using
        Work.CORE3.le_normalizer_map_subtype B.Hhat (Work.GW2.oddCore ↥B.Hhat)
    exact ((Subgroup.mem_normalizer_iff.mp (h1 hs)) u).mp hu
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
      · exact (not_invset_U_of_mem I G hBc B h1 D hxU hx1 hy2 hyH hxy).elim
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
        have h1 : (MulAut.conj y) x = x⁻¹ := by rw [MulAut.conj_apply]; exact hxy
        rw [h1, inv_pow]
      have hvv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hv2)
      have hyv : y * v * y⁻¹ = v := by
        rw [← hxpow, hyx, hxpow, hvv]
      have hyc : y ∈ Subgroup.centralizer ({v} : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        have h2 := congrArg (fun w => w * y) hyv
        have h1 : y * v = v * y := by simpa [mul_assoc] using h2
        exact h1.symm
      exact hyH (hCA v hv hv1 hyc)

end Work.CORE3

namespace Work.CORE3

namespace Work.CORE3

open Work.GW2

/-- The statement under the skeleton's original doubly nested name
`Work.CORE3.Work.CORE3.Case1bFive`. -/
theorem Case1bFive (I : Case1Inputs) : Case1bFiveProp :=
  _root_.Work.CORE3.Case1bFive I

end Work.CORE3

end Work.CORE3
