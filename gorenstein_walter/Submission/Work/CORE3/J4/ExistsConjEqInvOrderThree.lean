import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.CentralizerPcoreEqVU
import Submission.Work.CORE3.InvSetVUSingleton
import Submission.Work.CORE3.OrderThreeLeCentralizer
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.FourGroupOddOrderCommutingInvolution
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.J4.J4InvolutionMemOfSup
import Submission.Work.CORE3.exists_mul_of_mem_sup_of_normal

/-!
# `Work.CORE3.J4.ExistsConjEqInvOrderThree`

Setting (Bender 1981, §3, subcase `V = O₂(Ĥ)`):  `G` a minimal counterexample, `B` a Bender
setup with `Case1 B`, `V := O₂(Ĥ)` a four-group, `U := O(Ĥ)` of order `3`, `VU = V ⊔ U`
normal of index `6` in `Ĥ` with `C_Ĥ(V) = VU`.

The leaf proves: for every `x ∈ Ĥ` of order `3` with `x ∉ VU` there is `h ∈ Ĥ` with
`h * x * h⁻¹ = x⁻¹`.

The mathematical content is the following.  `x ∉ VU = C_Ĥ(V)` means that conjugation by `x`
acts on the four-group `V` as a `3`-cycle.  An involution `h ∈ Ĥ` outside `V` (there is one: a
Sylow `2`-subgroup `S ≅ D₈` of `Ĥ` contains `V` and `D₈` has involutions outside its Klein
subgroup) acts on `V` as a transposition, and it inverts `U` (`D.inv`, using `D.hall`/`D.ne` and
`|U| = 3` to identify `D.K` with `U`).  Hence `h x h⁻¹ x` acts trivially on `V`, i.e. lies in
`VU`; comparing the `U`-component of the identity `x (h x h⁻¹ x) x⁻¹ = h (h x h⁻¹ x) h⁻¹`
shows `h x h⁻¹ x ∈ V`.  Finally, replacing `h` by `h * v` for a suitable `v ∈ V` adjusts the
`V`-component, and `v ↦ v * (x v x⁻¹)` being a bijection of `V` (its kernel is
`C_V(x) = 1`) produces the exact inverter.
-/

namespace Work.CORE3.J4

open Subgroup
open Work.GW2

set_option linter.unusedVariables false

/-- **An involution of `Ĥ` outside `O₂(Ĥ)`.**  In the `Case1bData` setting there is an involution
`h ∈ Ĥ` with `h ∉ pCoreIn 2 B.Hhat`.

`S := B.S` is a Sylow `2`-subgroup of `G` of order `8` containing `V = O₂(Ĥ)`; as a Sylow
`2`-subgroup of a D-group with dihedral non-cyclic Sylow, `S ≅ D₈`.  The elements
`e⁻¹ (sr 0)` and `e⁻¹ (sr 1)` have order `2`; they cannot both lie in `V`, since then their
product `e⁻¹ (sr 0 · sr 1) = e⁻¹ (r 1)` would lie in `V` while having order `4`, whereas `V` has
exponent `2`. -/
lemma exists_involution_Hhat_notMem_pCore {G : Type} [Group G] [Finite G]
    (I : Case1Inputs) (hBc : BenderCtx G) (B : BenderSetup G) (D : Case1bData B) :
    ∃ h ∈ B.Hhat, orderOf h = 2 ∧ h ∉ pCoreIn 2 B.Hhat := by
  have h26 : Thm26Concl B := I.h26 G I.T.ft hBc B
  have hVleS : pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) := Work.CORE2A.thm26Concl_O2_le_S h26
  obtain ⟨n, hn2, ⟨e⟩⟩ := SylowDihedral G hBc B
  have hcardS : Nat.card ↥(B.S : Subgroup G) = 2 * n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  have hn4 : n = 4 := by rw [D.S8] at hcardS; omega
  have e4 : ↥(B.S : Subgroup G) ≃* DihedralGroup 4 := hn4 ▸ e
  let g1 : ↥(B.S : Subgroup G) := e4.symm (DihedralGroup.sr 0)
  let g2 : ↥(B.S : Subgroup G) := e4.symm (DihedralGroup.sr 1)
  have hg1mem : (g1 : G) ∈ B.Hhat := Work.CORE2A.bSetup_S_le_Hhat B g1.2
  have hg2mem : (g2 : G) ∈ B.Hhat := Work.CORE2A.bSetup_S_le_Hhat B g2.2
  have hg1ord : orderOf (g1 : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    show orderOf (e4.symm (DihedralGroup.sr 0)) = 2
    rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr]
  have hg2ord : orderOf (g2 : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    show orderOf (e4.symm (DihedralGroup.sr 1)) = 2
    rw [MulEquiv.orderOf_eq, DihedralGroup.orderOf_sr]
  by_cases h1 : (g1 : G) ∈ pCoreIn 2 B.Hhat
  · refine ⟨(g2 : G), hg2mem, hg2ord, ?_⟩
    intro h2
    have hprod : (g1 : G) * (g2 : G) ∈ pCoreIn 2 B.Hhat :=
      (pCoreIn 2 B.Hhat).mul_mem h1 h2
    have hprod2 : ((g1 : G) * (g2 : G)) ^ 2 = 1 := D.four.2 _ hprod
    have hord4 : orderOf ((g1 : G) * (g2 : G)) = 4 := by
      have hcoe : (g1 : G) * (g2 : G) = ((g1 * g2 : ↥(B.S : Subgroup G)) : G) := rfl
      rw [hcoe, Subgroup.orderOf_coe]
      have hmult : g1 * g2 = e4.symm (DihedralGroup.sr 0 * DihedralGroup.sr 1) := by
        simp only [g1, g2, map_mul]
      rw [hmult, MulEquiv.orderOf_eq, DihedralGroup.sr_mul_sr]
      have h4 : orderOf (DihedralGroup.r ((1 : ZMod 4) - 0) : DihedralGroup 4) = 4 := by
        rw [sub_zero, DihedralGroup.orderOf_r]
        decide
      simpa using h4
    have hdvd : orderOf ((g1 : G) * (g2 : G)) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hprod2
    rw [hord4] at hdvd
    norm_num at hdvd
  · exact ⟨(g1 : G), hg1mem, hg1ord, h1⟩

/-- **Step I.**  Let `V` be a Klein four-group, `x ∈ N(V)` of order `3` not centralizing `V`,
and `h ∈ N(V)` an involution not centralizing `V`.  Then `h * x * h⁻¹ * x` centralizes `V`.

Indeed conjugation by `x` and by `h` give an order-`3` and an order-`2` element of `Aut V ≅ S₃`,
and an involution conjugates an order-`3` element to its inverse, so
`h x h⁻¹ x ∈ C_G(V)`; the proof below computes this on the explicit `3`-cycle
`V = {1, a, b, a b}` supplied by `fourGroup_oddOrder_conjCycle`. -/
lemma involution_mul_conj_orderThree_mem_centralizer {G : Type} [Group G] [Finite G]
    {V : Subgroup G} {x h : G}
    (hV4 : IsFourGroup V)
    (hxN : x ∈ Subgroup.normalizer (V : Set G))
    (hhN : h ∈ Subgroup.normalizer (V : Set G))
    (hx3 : orderOf x = 3)
    (hxnc : x ∉ Subgroup.centralizer (V : Set G))
    (hh2 : h * h = 1)
    (hhnc : h ∉ Subgroup.centralizer (V : Set G)) :
    h * x * h⁻¹ * x ∈ Subgroup.centralizer (V : Set G) := by
  classical
  have hxodd : Odd (orderOf x) := by rw [hx3]; norm_num
  obtain ⟨a, b, haV, hbV, ha1, hb1, hab, hVset, hxa, hxb, hxab⟩ :=
    fourGroup_oddOrder_conjCycle hV4 hxN hxodd hxnc
  have hhinv : h⁻¹ = h := inv_eq_of_mul_eq_one_right hh2
  have ha2 : a * a = 1 := by have := hV4.2 a haV; simpa [pow_two] using this
  have hb2 : b * b = 1 := by have := hV4.2 b hbV; simpa [pow_two] using this
  have hab2 : (a * b) * (a * b) = 1 := by
    have := hV4.2 (a * b) (V.mul_mem haV hbV); simpa [pow_two] using this
  have hVcomm : IsMulCommutative ↥V := Work.CORE2A.IsFourGroup.isMulCommutative' hV4
  have hcommV : ∀ u ∈ V, ∀ w ∈ V, u * w = w * u := by
    intro u hu w hw
    exact congrArg Subtype.val (hVcomm.is_comm.comm (⟨u, hu⟩ : V) (⟨w, hw⟩))
  have hmemV : ∀ y : G, y ∈ V ↔ y = 1 ∨ y = a ∨ y = b ∨ y = a * b := by
    intro y
    change y ∈ (V : Set G) ↔ y = 1 ∨ y = a ∨ y = b ∨ y = a * b
    rw [hVset]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  have hφaV : h * a * h⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hhN a).mp haV
  have hφbV : h * b * h⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hhN b).mp hbV
  have hφa1 : h * a * h⁻¹ ≠ 1 := by
    intro hc; apply ha1
    calc a = h⁻¹ * (h * a * h⁻¹) * h := by group
      _ = h⁻¹ * 1 * h := by rw [hc]
      _ = 1 := by group
  have hφb1 : h * b * h⁻¹ ≠ 1 := by
    intro hc; apply hb1
    calc b = h⁻¹ * (h * b * h⁻¹) * h := by group
      _ = h⁻¹ * 1 * h := by rw [hc]
      _ = 1 := by group
  have hφab : h * (a * b) * h⁻¹ = (h * a * h⁻¹) * (h * b * h⁻¹) := by group
  have haab : a * (a * b) = b := by
    calc a * (a * b) = (a * a) * b := by rw [mul_assoc]
      _ = b := by rw [ha2, one_mul]
  have habb : (a * b) * b = a := by
    calc (a * b) * b = a * (b * b) := by rw [mul_assoc]
      _ = a := by rw [hb2, mul_one]
  have hba : b * a = a * b := hcommV b hbV a haV
  have hφaa : h * (h * a * h⁻¹) * h⁻¹ = a := by
    rw [hhinv]
    calc h * (h * a * h) * h = (h * h) * a * (h * h) := by group
      _ = a := by rw [hh2, one_mul, mul_one]
  have hφbb : h * (h * b * h⁻¹) * h⁻¹ = b := by
    rw [hhinv]
    calc h * (h * b * h) * h = (h * h) * b * (h * h) := by group
      _ = b := by rw [hh2, one_mul, mul_one]
  have hstep1 : ∀ y : G, (h * x * h⁻¹ * x) * y * (h * x * h⁻¹ * x)⁻¹
      = (h * x * h⁻¹) * (x * y * x⁻¹) * (h * x * h⁻¹)⁻¹ := by intro y; group
  have hstep2 : ∀ y : G, (h * x * h⁻¹) * y * (h * x * h⁻¹)⁻¹
      = h * (x * (h * y * h⁻¹) * x⁻¹) * h⁻¹ := by
    intro y; rw [hhinv, mul_inv_rev, mul_inv_rev]; simp only [hhinv]; group
  have hkey : (h * a * h⁻¹ = a ∧ h * b * h⁻¹ = a * b) ∨
              (h * a * h⁻¹ = b ∧ h * b * h⁻¹ = a) ∨
              (h * a * h⁻¹ = a * b ∧ h * b * h⁻¹ = b) := by
    rcases (hmemV (h * a * h⁻¹)).mp hφaV with hu1 | hu | hu | hu
    · exact absurd hu1 hφa1
    · rcases (hmemV (h * b * h⁻¹)).mp hφbV with hw1 | hw | hw | hw
      · exact absurd hw1 hφb1
      · exfalso; apply hab
        have hc : h * a * h⁻¹ = h * b * h⁻¹ := hu.trans hw.symm
        calc a = h⁻¹ * (h * a * h⁻¹) * h := by group
          _ = h⁻¹ * (h * b * h⁻¹) * h := by rw [hc]
          _ = b := by group
      · exfalso; apply hhnc
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have hvh : h * v * h⁻¹ = v := by
          rcases (hmemV v).mp hv with rfl | rfl | rfl | rfl
          · group
          · exact hu
          · exact hw
          · rw [hφab, hu, hw]
        calc v * h = (h * v * h⁻¹) * h := by rw [hvh]
          _ = h * v := by group
      · exact Or.inl ⟨hu, hw⟩
    · refine Or.inr (Or.inl ⟨hu, ?_⟩)
      have := hφaa; rw [hu] at this; exact this
    · refine Or.inr (Or.inr ⟨hu, ?_⟩)
      have h1 : h * (a * b) * h⁻¹ = a := by have := hφaa; rw [hu] at this; exact this
      rw [hφab, hu] at h1
      have h2 : (a * b) * a = b := by
        calc (a * b) * a = a * (b * a) := by rw [mul_assoc]
          _ = a * (a * b) := by rw [hcommV b hbV a haV]
          _ = (a * a) * b := by rw [mul_assoc]
          _ = b := by rw [ha2, one_mul]
      calc h * b * h⁻¹ = (a * b) * ((a * b) * (h * b * h⁻¹)) := by
            rw [← mul_assoc, hab2, one_mul]
        _ = (a * b) * a := by rw [h1]
        _ = b := h2
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  rcases hkey with ⟨hu, hw⟩ | ⟨hu, hw⟩ | ⟨hu, hw⟩
  · -- case 1 : `h a h⁻¹ = a`, `h b h⁻¹ = a * b`
    have ka : (h * x * h⁻¹ * x) * a * (h * x * h⁻¹ * x)⁻¹ = a := by
      rw [hstep1 a, hxa, hstep2 b, hw, hxab, hu]
    have kb : (h * x * h⁻¹ * x) * b * (h * x * h⁻¹ * x)⁻¹ = b := by
      rw [hstep1 b, hxb, hstep2 (a * b), hφab, hu, hw, haab, hxb, hφab, hu, hw, haab]
    have keya : (h * x * h⁻¹ * x) * a = a * (h * x * h⁻¹ * x) := by
      calc (h * x * h⁻¹ * x) * a
          = (h * x * h⁻¹ * x) * a * (h * x * h⁻¹ * x)⁻¹ * (h * x * h⁻¹ * x) := by group
        _ = a * (h * x * h⁻¹ * x) := by rw [ka]
    have keyb : (h * x * h⁻¹ * x) * b = b * (h * x * h⁻¹ * x) := by
      calc (h * x * h⁻¹ * x) * b
          = (h * x * h⁻¹ * x) * b * (h * x * h⁻¹ * x)⁻¹ * (h * x * h⁻¹ * x) := by group
        _ = b * (h * x * h⁻¹ * x) := by rw [kb]
    rcases (hmemV v).mp hv with rfl | rfl | rfl | rfl
    · simp
    · exact keya.symm
    · exact keyb.symm
    · calc (a * b) * (h * x * h⁻¹ * x) = a * (b * (h * x * h⁻¹ * x)) := by rw [mul_assoc]
        _ = a * ((h * x * h⁻¹ * x) * b) := by rw [keyb.symm]
        _ = (a * (h * x * h⁻¹ * x)) * b := by rw [← mul_assoc]
        _ = ((h * x * h⁻¹ * x) * a) * b := by rw [keya.symm]
        _ = (h * x * h⁻¹ * x) * (a * b) := by rw [mul_assoc]
  · -- case 2 : `h a h⁻¹ = b`, `h b h⁻¹ = a`
    have ka : (h * x * h⁻¹ * x) * a * (h * x * h⁻¹ * x)⁻¹ = a := by
      rw [hstep1 a, hxa, hstep2 b, hw, hxa, hw]
    have kb : (h * x * h⁻¹ * x) * b * (h * x * h⁻¹ * x)⁻¹ = b := by
      rw [hstep1 b, hxb, hstep2 (a * b), hφab, hu, hw, hba, hxab, hu]
    have keya : (h * x * h⁻¹ * x) * a = a * (h * x * h⁻¹ * x) := by
      calc (h * x * h⁻¹ * x) * a
          = (h * x * h⁻¹ * x) * a * (h * x * h⁻¹ * x)⁻¹ * (h * x * h⁻¹ * x) := by group
        _ = a * (h * x * h⁻¹ * x) := by rw [ka]
    have keyb : (h * x * h⁻¹ * x) * b = b * (h * x * h⁻¹ * x) := by
      calc (h * x * h⁻¹ * x) * b
          = (h * x * h⁻¹ * x) * b * (h * x * h⁻¹ * x)⁻¹ * (h * x * h⁻¹ * x) := by group
        _ = b * (h * x * h⁻¹ * x) := by rw [kb]
    rcases (hmemV v).mp hv with rfl | rfl | rfl | rfl
    · simp
    · exact keya.symm
    · exact keyb.symm
    · calc (a * b) * (h * x * h⁻¹ * x) = a * (b * (h * x * h⁻¹ * x)) := by rw [mul_assoc]
        _ = a * ((h * x * h⁻¹ * x) * b) := by rw [keyb.symm]
        _ = (a * (h * x * h⁻¹ * x)) * b := by rw [← mul_assoc]
        _ = ((h * x * h⁻¹ * x) * a) * b := by rw [keya.symm]
        _ = (h * x * h⁻¹ * x) * (a * b) := by rw [mul_assoc]
  · -- case 3 : `h a h⁻¹ = a * b`, `h b h⁻¹ = b`
    have ka : (h * x * h⁻¹ * x) * a * (h * x * h⁻¹ * x)⁻¹ = a := by
      rw [hstep1 a, hxa, hstep2 b, hw, hxb, hφab, hu, hw, habb]
    have kb : (h * x * h⁻¹ * x) * b * (h * x * h⁻¹ * x)⁻¹ = b := by
      rw [hstep1 b, hxb, hstep2 (a * b), hφab, hu, hw, habb, hxa, hw]
    have keya : (h * x * h⁻¹ * x) * a = a * (h * x * h⁻¹ * x) := by
      calc (h * x * h⁻¹ * x) * a
          = (h * x * h⁻¹ * x) * a * (h * x * h⁻¹ * x)⁻¹ * (h * x * h⁻¹ * x) := by group
        _ = a * (h * x * h⁻¹ * x) := by rw [ka]
    have keyb : (h * x * h⁻¹ * x) * b = b * (h * x * h⁻¹ * x) := by
      calc (h * x * h⁻¹ * x) * b
          = (h * x * h⁻¹ * x) * b * (h * x * h⁻¹ * x)⁻¹ * (h * x * h⁻¹ * x) := by group
        _ = b * (h * x * h⁻¹ * x) := by rw [kb]
    rcases (hmemV v).mp hv with rfl | rfl | rfl | rfl
    · simp
    · exact keya.symm
    · exact keyb.symm
    · calc (a * b) * (h * x * h⁻¹ * x) = a * (b * (h * x * h⁻¹ * x)) := by rw [mul_assoc]
        _ = a * ((h * x * h⁻¹ * x) * b) := by rw [keyb.symm]
        _ = (a * (h * x * h⁻¹ * x)) * b := by rw [← mul_assoc]
        _ = ((h * x * h⁻¹ * x) * a) * b := by rw [keya.symm]
        _ = (h * x * h⁻¹ * x) * (a * b) := by rw [mul_assoc]

/-- **Steps I–III combined.**  Self-contained version of the main computation.

`V` is a Klein four-group and `U` a subgroup of order `3` with `V ⊓ U = ⊥`, both normal in
`S`; `x ∈ N(V)` has order `3` and does not centralize `V`, `h ∈ N(V)` is an involution not
centralizing `V` and inverting `U`, and `C_S(V) = V ⊔ U`.  Then some `h'` of the form `h * v`
(`v ∈ V`) inverts `x`. -/
lemma exists_conj_eq_inv_aux {G : Type} [Group G] [Finite G]
    {V U S : Subgroup G} {x h : G}
    (hV4 : IsFourGroup V) (hU3 : Nat.card U = 3) (hdisj : V ⊓ U = ⊥)
    (hVleS : V ≤ S) (hUleS : U ≤ S)
    (hVn : ∀ s ∈ S, ∀ v ∈ V, s * v * s⁻¹ ∈ V)
    (hUn : ∀ s ∈ S, ∀ u ∈ U, s * u * s⁻¹ ∈ U)
    (hxS : x ∈ S) (hhS : h ∈ S)
    (hxN : x ∈ Subgroup.normalizer (V : Set G))
    (hhN : h ∈ Subgroup.normalizer (V : Set G))
    (hx3 : orderOf x = 3) (hxnc : x ∉ Subgroup.centralizer (V : Set G))
    (hh2 : h * h = 1) (hhnc : h ∉ Subgroup.centralizer (V : Set G))
    (hCV : Subgroup.centralizer (V : Set G) ⊓ S = V ⊔ U)
    (hhInvU : ∀ u ∈ U, h * u * h⁻¹ = u⁻¹) :
    ∃ v ∈ V, (h * v) * x * (h * v)⁻¹ = x⁻¹ := by
  classical
  have hhinv : h⁻¹ = h := inv_eq_of_mul_eq_one_right hh2
  have hxodd : Odd (orderOf x) := by rw [hx3]; norm_num
  obtain ⟨a, b, haV, hbV, ha1, hb1, hab, hVset, hxa, hxb, hxab⟩ :=
    fourGroup_oddOrder_conjCycle hV4 hxN hxodd hxnc
  have ha2 : a * a = 1 := by have := hV4.2 a haV; simpa [pow_two] using this
  have hb2 : b * b = 1 := by have := hV4.2 b hbV; simpa [pow_two] using this
  have hab1 : a * b ≠ 1 := by
    intro hc; apply hab
    calc a = a * (b * b) := by rw [hb2, mul_one]
      _ = (a * b) * b := by rw [mul_assoc]
      _ = b := by rw [hc, one_mul]
  have habb : (a * b) * b = a := by
    calc (a * b) * b = a * (b * b) := by rw [mul_assoc]
      _ = a := by rw [hb2, mul_one]
  have haab : a * (a * b) = b := by
    calc a * (a * b) = (a * a) * b := by rw [mul_assoc]
      _ = b := by rw [ha2, one_mul]
  have hVMC : IsMulCommutative ↥V := Work.CORE2A.IsFourGroup.isMulCommutative' hV4
  have hcommV : ∀ p ∈ V, ∀ q ∈ V, p * q = q * p := fun p hp q hq =>
    congrArg Subtype.val (hVMC.is_comm.comm (⟨p, hp⟩ : V) (⟨q, hq⟩ : V))
  have hmemV : ∀ y : G, y ∈ V ↔ y = 1 ∨ y = a ∨ y = b ∨ y = a * b := by
    intro y
    change y ∈ (V : Set G) ↔ y = 1 ∨ y = a ∨ y = b ∨ y = a * b
    rw [hVset]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  -- ## Step I, II : `m = h x h⁻¹ x ∈ V`
  have hUcentx : U ≤ Subgroup.centralizer ({x} : Set G) :=
    OrderThreeLeCentralizer ((Subgroup.le_normalizer_iff.mpr hUn) hxS) hx3 hU3
  set m : G := h * x * h⁻¹ * x with hmdef
  have hmC : m ∈ Subgroup.centralizer (V : Set G) := by
    rw [hmdef]
    exact involution_mul_conj_orderThree_mem_centralizer hV4 hxN hhN hx3 hxnc hh2 hhnc
  have hmS : m ∈ S := by
    rw [hmdef]; exact S.mul_mem (S.mul_mem (S.mul_mem hhS hxS) (S.inv_mem hhS)) hxS
  have hmVU : m ∈ V ⊔ U := by
    have h1 : m ∈ Subgroup.centralizer (V : Set G) ⊓ S := ⟨hmC, hmS⟩
    rwa [hCV] at h1
  obtain ⟨v, hvV, u, huU, hmvu⟩ :=
    exists_mul_of_mem_sup_of_normal hVleS hUleS hVn hUn m hmVU
  have hxmx : x * m * x⁻¹ = h * m * h⁻¹ := by
    rw [hmdef, hhinv]
    rw [show x * (h * x * h * x) * x⁻¹ = x * h * x * h from by group]
    rw [show h * (h * x * h * x) * h = x * h * x * h from by
      rw [show h * (h * x * h * x) * h = (h * h) * (x * h * x * h) from by group,
        hh2, one_mul]]
  have hux : u * x = x * u := Subgroup.mem_centralizer_singleton_iff.mp (hUcentx huU)
  have hu2V : u * u ∈ V := by
    have h1 : (x * v * x⁻¹) * u = (h * v * h⁻¹) * u⁻¹ := by
      have h2 := hxmx
      rw [hmvu] at h2
      have e1 : x * (v * u) * x⁻¹ = (x * v * x⁻¹) * u := by
        calc x * (v * u) * x⁻¹ = (x * v * x⁻¹) * (x * u * x⁻¹) := by group
          _ = (x * v * x⁻¹) * u := by
              rw [show x * u * x⁻¹ = u from by rw [hux.symm, mul_assoc, mul_inv_cancel, mul_one]]
      have e2 : h * (v * u) * h⁻¹ = (h * v * h⁻¹) * u⁻¹ := by
        calc h * (v * u) * h⁻¹ = (h * v * h⁻¹) * (h * u * h⁻¹) := by group
          _ = (h * v * h⁻¹) * u⁻¹ := by rw [hhInvU u huU]
      rwa [e1, e2] at h2
    have h3 : u * u = (x * v * x⁻¹)⁻¹ * (h * v * h⁻¹) := by
      calc u * u = (x * v * x⁻¹)⁻¹ * ((x * v * x⁻¹) * u) * u := by group
        _ = (x * v * x⁻¹)⁻¹ * ((h * v * h⁻¹) * u⁻¹) * u := by rw [h1]
        _ = (x * v * x⁻¹)⁻¹ * (h * v * h⁻¹) := by group
    rw [h3]
    exact V.mul_mem (V.inv_mem (hVn x hxS v hvV)) (hVn h hhS v hvV)
  have hu2 : u * u = 1 := by
    have hmem : u * u ∈ V ⊓ U := ⟨hu2V, U.mul_mem huU huU⟩
    rw [hdisj] at hmem
    simpa using hmem
  have hu1 : u = 1 := by
    have hdvd2 : orderOf u ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hu2)
    have hdvd3 : orderOf u ∣ 3 := by
      have h := Subgroup.orderOf_dvd_natCard U huU
      rwa [hU3] at h
    have hg : orderOf u ∣ 1 := by
      have h := Nat.dvd_gcd hdvd2 hdvd3
      rwa [show Nat.gcd 2 3 = 1 from by norm_num] at h
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hg)
  have hmV : m ∈ V := by rw [hmvu, hu1, mul_one]; exact hvV
  have hmx : h * x * h⁻¹ = m * x⁻¹ := by rw [hmdef]; group
  -- ## Step III
  have hβmem : ∀ y ∈ V, y * (x * y * x⁻¹) ∈ V := fun y hy => V.mul_mem hy (hVn x hxS y hy)
  have hβ1 : ∀ w ∈ V, w * (x * w * x⁻¹) = 1 → w = 1 := by
    intro w hw hc
    rcases (hmemV w).mp hw with h1 | h1 | h1 | h1
    · exact h1
    · rw [h1] at hc ⊢
      rw [hxa] at hc
      exact absurd hc hab1
    · rw [h1] at hc ⊢
      rw [hxb] at hc
      have e : b * (a * b) = a := by rw [← mul_assoc, hcommV b hbV a haV, habb]
      rw [e] at hc
      exact absurd hc ha1
    · rw [h1] at hc ⊢
      rw [hxab] at hc
      have e : (a * b) * a = b := by rw [hcommV (a * b) (V.mul_mem haV hbV) a haV, haab]
      rw [e] at hc
      exact absurd hc hb1
  have hmulcomm : ∀ p ∈ V, ∀ q ∈ V, ∀ r ∈ V, ∀ s ∈ V,
      (p * q) * (r * s) = (p * r) * (q * s) := by
    intro p hp q hq r hr s hs
    calc (p * q) * (r * s) = p * (q * (r * s)) := by rw [mul_assoc p q (r * s)]
      _ = p * ((q * r) * s) := by rw [← mul_assoc q r s]
      _ = p * ((r * q) * s) := by rw [hcommV q hq r hr]
      _ = p * (r * (q * s)) := by rw [mul_assoc r q s]
      _ = (p * r) * (q * s) := by rw [← mul_assoc p r (q * s)]
  have hβinj : ∀ y ∈ V, ∀ z ∈ V, y * (x * y * x⁻¹) = z * (x * z * x⁻¹) → y = z := by
    intro y hy z hz heq
    have hz' : z⁻¹ ∈ V := V.inv_mem hz
    have hcy : x * y * x⁻¹ ∈ V := hVn x hxS y hy
    have hcz : x * z * x⁻¹ ∈ V := hVn x hxS z hz
    have hczi : (x * z * x⁻¹)⁻¹ ∈ V := V.inv_mem hcz
    have hc1 : x * (y * z⁻¹) * x⁻¹ = (x * y * x⁻¹) * (x * z⁻¹ * x⁻¹) := by group
    have hc2 : x * z⁻¹ * x⁻¹ = (x * z * x⁻¹)⁻¹ := by group
    have key : (y * z⁻¹) * (x * (y * z⁻¹) * x⁻¹) = 1 := by
      rw [hc1, hc2]
      rw [hmulcomm y hy z⁻¹ hz' (x * y * x⁻¹) hcy (x * z * x⁻¹)⁻¹ hczi]
      rw [hcommV z⁻¹ hz' (x * z * x⁻¹)⁻¹ hczi, ← mul_inv_rev z (x * z * x⁻¹), heq,
        mul_inv_cancel]
    have := hβ1 (y * z⁻¹) (V.mul_mem hy hz') key
    calc y = y * z⁻¹ * z := by group
      _ = 1 * z := by rw [this]
      _ = z := one_mul z
  let g : ↥V → ↥V := fun y =>
    ⟨h * (y.1 * (x * y.1 * x⁻¹)) * h⁻¹, hVn h hhS _ (hβmem y.1 y.2)⟩
  have hginj : Function.Injective g := by
    intro y z hyz
    apply Subtype.ext
    have h1 : h * (y.1 * (x * y.1 * x⁻¹)) * h⁻¹ = h * (z.1 * (x * z.1 * x⁻¹)) * h⁻¹ :=
      Subtype.ext_iff.mp hyz
    have h2 : y.1 * (x * y.1 * x⁻¹) = z.1 * (x * z.1 * x⁻¹) := by
      calc y.1 * (x * y.1 * x⁻¹) = h⁻¹ * (h * (y.1 * (x * y.1 * x⁻¹)) * h⁻¹) * h := by group
        _ = h⁻¹ * (h * (z.1 * (x * z.1 * x⁻¹)) * h⁻¹) * h := by rw [h1]
        _ = z.1 * (x * z.1 * x⁻¹) := by group
    exact hβinj y.1 y.2 z.1 z.2 h2
  obtain ⟨y0, hy0⟩ := (Finite.injective_iff_surjective.mp hginj) ⟨m, hmV⟩
  have hy0' : h * (y0.1 * (x * y0.1 * x⁻¹)) * h⁻¹ = m := Subtype.ext_iff.mp hy0
  have hv2 : y0.1 * y0.1 = 1 := by have := hV4.2 y0.1 y0.2; simpa [pow_two] using this
  have hvxv : y0.1 * x * y0.1⁻¹ = (y0.1 * (x * y0.1 * x⁻¹)) * x := by
    rw [inv_eq_of_mul_eq_one_right hv2]; group
  refine ⟨y0.1, y0.2, ?_⟩
  calc (h * y0.1) * x * (h * y0.1)⁻¹
      = h * (y0.1 * x * y0.1⁻¹) * h⁻¹ := by group
    _ = h * ((y0.1 * (x * y0.1 * x⁻¹)) * x) * h⁻¹ := by rw [hvxv]
    _ = (h * (y0.1 * (x * y0.1 * x⁻¹)) * h⁻¹) * (h * x * h⁻¹) := by group
    _ = m * (m * x⁻¹) := by rw [hy0', hmx]
    _ = x⁻¹ := by
        have hm2 : m * m = 1 := by have := hV4.2 m hmV; simpa [pow_two] using this
        rw [← mul_assoc, hm2, one_mul]

theorem ExistsConjEqInvOrderThree {G : Type} [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) (hU3 : Nat.card B.U = 3)
    {x : G} (hxH : x ∈ B.Hhat) (hx3 : orderOf x = 3)
    (hxVU : x ∉ (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U)) :
    ∃ h ∈ B.Hhat, h * x * h⁻¹ = x⁻¹ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, hhH, hh2ord, hhV⟩ := exists_involution_Hhat_notMem_pCore I hBc B D
  set V : Subgroup G := Work.GW2.pCoreIn 2 B.Hhat with hV
  set U : Subgroup G := B.U with hU
  have h26 : Thm26Concl B := I.h26 G I.T.ft hBc B
  have hV4 : IsFourGroup V := by rw [hV]; exact D.four
  have hU3' : Nat.card U = 3 := by rw [hU]; exact hU3
  have hVleH : V ≤ B.Hhat := by rw [hV]; exact Subgroup.map_subtype_le _
  have hUleH : U ≤ B.Hhat := by rw [hU]; exact Work.CORE2A.bSetup_U_le_Hhat B
  have hVnorm : B.Hhat ≤ Subgroup.normalizer (V : Set G) := by
    rw [hV]
    simpa [Work.GW2.pCoreIn] using
      Work.CORE3.le_normalizer_map_subtype B.Hhat (Work.GW2.pCore 2 ↥B.Hhat)
  have hUnorm : B.Hhat ≤ Subgroup.normalizer (U : Set G) := by
    have h := Work.CORE3.le_normalizer_map_subtype B.Hhat (Work.GW2.oddCore ↥B.Hhat)
    have hUeq : ((Subgroup.map B.Hhat.subtype (Work.GW2.oddCore ↥B.Hhat)) : Subgroup G) = U := by
      rw [hU]; exact h26.1
    rwa [hUeq] at h
  have hdisj : V ⊓ U = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hV4.1, hU3']
    norm_num
  have hhVU : h ∉ V ⊔ U := by
    intro hh
    exact hhV (Work.CORE3.J4.involution_mem_of_mem_sup hdisj
      (le_trans hUleH hVnorm) (by rw [hU3']; norm_num) hh hh2ord)
  have hh2 : h * h = 1 := by
    have := pow_orderOf_eq_one h; rw [hh2ord] at this; simpa [pow_two] using this
  have hhInvU : ∀ u ∈ U, h * u * h⁻¹ = u⁻¹ := by
    have hKU : D.K = U := by
      have hle : D.K ≤ U := by
        rw [hU]
        exact D.hall.1.trans (Subgroup.map_subtype_le (Work.GW2.fitting ↥B.U))
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      have hdvd : Nat.card ↥D.K ∣ 3 := by
        have h := Subgroup.card_dvd_of_le hle
        rwa [hU3'] at h
      have h1 : 1 < Nat.card ↥D.K := by
        rw [Subgroup.one_lt_card_iff_ne_bot]; exact D.ne
      rcases Nat.Prime.eq_one_or_self_of_dvd (by norm_num : Nat.Prime 3) _ hdvd with hh | hh
      · omega
      · rw [hU3', hh]
    intro u hu
    have hset := D.inv h hhH hh2ord hhV
    have hu' : u ∈ Work.GW2.invSet B.U h := by
      rw [← hset, hKU]
      exact hu
    exact (Work.CORE2A.mem_invSet.mp hu').2
  have hCV : Subgroup.centralizer (V : Set G) ⊓ B.Hhat = V ⊔ U := by
    rw [hV, hU]
    exact Work.CORE3.CentralizerPcoreEqVU G I hBc B h1 D
  have hxnc : x ∉ Subgroup.centralizer (V : Set G) := by
    intro hxcen
    have h1 : x ∈ Subgroup.centralizer (V : Set G) ⊓ B.Hhat := ⟨hxcen, hxH⟩
    rw [hCV] at h1
    exact hxVU (by rwa [hV, hU] at h1)
  have hhnc : h ∉ Subgroup.centralizer (V : Set G) := by
    intro hhcen
    have h1 : h ∈ Subgroup.centralizer (V : Set G) ⊓ B.Hhat := ⟨hhcen, hhH⟩
    rw [hCV] at h1
    exact hhVU h1
  obtain ⟨v, hvV, hvconj⟩ :=
    exists_conj_eq_inv_aux (S := B.Hhat) (V := V) (U := U) hV4 hU3' hdisj hVleH hUleH
      (fun s hs v hv => (Subgroup.mem_normalizer_iff.mp (hVnorm hs) v).mp hv)
      (fun s hs u hu => (Subgroup.mem_normalizer_iff.mp (hUnorm hs) u).mp hu)
      hxH hhH (hVnorm hxH) (hVnorm hhH) hx3 hxnc hh2 hhnc hCV hhInvU
  exact ⟨h * v, B.Hhat.mul_mem hhH (hVleH hvV), hvconj⟩

end Work.CORE3.J4

