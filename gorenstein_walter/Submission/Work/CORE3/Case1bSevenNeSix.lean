import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.SevenHints
import Submission.Work.CORE3.SevenConjK
import Submission.Work.CORE3.BenderSix
import Submission.Work.CORE3.SixInvSetElements
import Submission.Work.CORE3.SixInvSetMulTable
import Submission.Work.CORE3.VUInvSetTrivial
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.Case1bDStructure
import Submission.Work.CORE3.J4.J4U3
import Submission.Work.CORE3.InvolutionMemVOfMemCentralizer

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- If `s` inverts `x` then `s` inverts every power of `x`. -/
private lemma conj_zpow_eq {G : Type} [Group G] {s x : G} (h : s * x * s⁻¹ = x⁻¹) (n : ℤ) :
    s * x ^ n * s⁻¹ = x ^ (-n) := by
  have h1 : (MulAut.conj s) x = x⁻¹ := by rw [MulAut.conj_apply]; exact h
  rw [show s * x ^ n * s⁻¹ = (MulAut.conj s) (x ^ n) by rw [MulAut.conj_apply], map_zpow, h1,
    inv_zpow, ← zpow_neg]

/-- If `s` and `t` both invert `x`, then `s * t` centralizes `⟨x⟩`. -/
private lemma mul_mem_centralizer_zpowers {G : Type} [Group G] {x s t : G}
    (hs : s * x * s⁻¹ = x⁻¹) (ht : t * x * t⁻¹ = x⁻¹) :
    s * t ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  have key : (s * t) * x ^ k * (s * t)⁻¹ = x ^ k := by
    calc (s * t) * x ^ k * (s * t)⁻¹ = s * (t * x ^ k * t⁻¹) * s⁻¹ := by group
      _ = s * x ^ (-k) * s⁻¹ := by rw [conj_zpow_eq ht k]
      _ = x ^ (-(-k)) := conj_zpow_eq hs (-k)
      _ = x ^ k := by rw [neg_neg]
  calc x ^ k * (s * t) = ((s * t) * x ^ k * (s * t)⁻¹) * (s * t) := by rw [key]
    _ = (s * t) * x ^ k := by group

/-- **Bender 1981, §3, p. 224, item (7), the `n ≠ 6` half, with `|U| = 3`.**
In Case (1) of Bender's Theorem 2.10, subcase `V = O₂(Ĥ)` of type `(2,2)`, an involution
`y ∉ Ĥ` inverting a nontrivial odd-order subgroup `X ≤ Ĥ` with `C_G(X)` of even order does
*not* have `I_Ĥ(y) = 6`: a coset of six involutions is incompatible with `|U| = 3`.

Proof.  `X` is a conjugate of `U = O(Ĥ)` (`SevenConjU`, using `|U| = 3` and the evenness of
`|C_G(X)|`), say `X = U^g`; then `|X| = 3`, so `X = ⟨x⟩` for some `x` of order `3` in `X`.

By the delegated lemma `InvolutionMemVOfMemCentralizer`, every involution centralizing `U` lies
in `V = O₂(Ĥ)`; conjugating by `g`, every involution `u ∈ C_G(X)` with `u * u = 1` lies in
`V^g = conjSub g V` — a four-group, so `u * u = 1` for *all* `u ∈ V^g`.

If `I_Ĥ(y)` has six elements, then (`SixInvSetElements`) it contains two distinct involutions
`b₁ ≠ b₂`, and (`invSetIn_six_mul_table`, applied with `a := x` and twice, once with the pair
swapped) `b₁ * x * b₁ = x⁻¹ = b₂ * x * b₂`.  Hence both `b₁ * y` and `b₂ * y` are involutions
centralizing `X` (`mul_mem_centralizer_zpowers`), so both lie in `V^g`; their product
`(b₁ * y) * (b₂ * y) = b₁ * b₂` therefore also lies in `V^g`, giving `(b₁ * b₂)² = 1`.  But
`Ĥ/VU` is non-abelian of order `6`, so `b₁ * b₂`, the product of two distinct involutions
modulo `VU`, has order `3`: `(b₁ * b₂)³ = 1` while `(b₁ * b₂)² ≠ 1` (otherwise `b₁ * b₂ = 1`
and `b₁ = b₂`).  Contradiction. -/
theorem Case1bSevenNeSix (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) (hU3 : Nat.card B.U = 3) {y : G} (hy2 : orderOf y = 2)
    (hyH : y ∉ B.Hhat) {X : Subgroup G} (hXH : X ≤ B.Hhat) (hXne : X ≠ ⊥)
    (hXodd : Odd (Nat.card X)) (hinv : ∀ x ∈ X, y * x * y⁻¹ = x⁻¹)
    (hC : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (h6 : Work.GW2.cosetInvCount B.Hhat y = 6) :
    False := by
  classical
  have hy : y * y = 1 := ((orderOf_eq_two_iff_mul_self y).mp hy2).1
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  -- Bender's (5) for `VU = O₂(Ĥ) ⊔ O(Ĥ)`
  have h5 : ∀ z : G, orderOf z = 2 → z ∉ B.Hhat →
      Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) z = {1} :=
    fun z hz hzH => Work.CORE3.VUInvSetTrivial G I hBc B h1 D z hz hzH
  have hI6 : (Work.CORE3.invSetIn B.Hhat y).ncard = 6 := by
    rw [Work.CORE3.ncard_invSetIn_eq_cosetInvCount B.Hhat y hy hyH]
    exact h6
  -- Bender (7), conjugacy half: `X` is a conjugate of `U` (here `|U| = 3`)
  obtain ⟨g, hXg⟩ :=
    Work.CORE3.SevenConjU G I hBc B h1 D hU3 hy2 hyH hXH hXne hXodd hinv hC
  have hXcard : Nat.card X = 3 := by
    rw [hXg, Work.CORE2A.card_conjSub, hU3]
  -- a generator `x` of `X`
  obtain ⟨x, hxX, hx1⟩ : ∃ x ∈ X, x ≠ 1 := by
    by_contra hcon
    exact hXne ((Subgroup.eq_bot_iff_forall X).mpr (fun z hz => by
      by_contra hz1
      exact hcon ⟨z, hz, hz1⟩))
  have hx3 : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 3 := by
      rw [← hXcard]; exact Subgroup.orderOf_dvd_natCard X hxX
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hXeq : X = Subgroup.zpowers x :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxX) (by
      rw [Nat.card_zpowers, hx3, hXcard])).symm
  have hxI : x ∈ Work.CORE3.invSetIn B.Hhat y :=
    ⟨hXH hxX, by simpa [hyinv] using hinv x hxX⟩
  -- the two distinct involutions `b₁, b₂` of `I_Ĥ(y)`
  obtain ⟨_a, b1, b2, _haI, _haord, hb1I, hb1ord, hb2I, hb2ord, hb12⟩ :=
    Work.CORE3.SixInvSetElements G I hBc B h1 D h5 y hy2 hyH h6
  obtain ⟨hconj1, hcube⟩ :=
    Work.CORE3.invSetIn_six_mul_table (Hh := B.Hhat) hy hI6 hxI hx3 hb1I hb1ord hb2I hb2ord hb12
  obtain ⟨hconj2, _⟩ :=
    Work.CORE3.invSetIn_six_mul_table (Hh := B.Hhat) hy hI6 hxI hx3 hb2I hb2ord hb1I hb1ord
      hb12.symm
  -- `V^g = conjSub g V`
  set Vg : Subgroup G := Work.GW2.conjSub g (Work.GW2.pCoreIn 2 B.Hhat) with hVg
  have hVgsq : ∀ v ∈ Vg, v * v = 1 := by
    intro v hv
    rw [hVg, Work.CORE2A.conjSub_eq_map, Subgroup.mem_map] at hv
    obtain ⟨u, hu, rfl⟩ := hv
    have hu2 : u * u = 1 := by
      have h := D.four.2 u hu
      rwa [pow_two] at h
    show (g * u * g⁻¹) * (g * u * g⁻¹) = 1
    rw [show (g * u * g⁻¹) * (g * u * g⁻¹) = g * (u * u) * g⁻¹ by group, hu2, mul_one,
      mul_inv_cancel]
  -- every involution of `C_G(X)` lies in `V^g`
  have hInvolVg : ∀ u : G, u * u = 1 → u ∈ Subgroup.centralizer (X : Set G) → u ∈ Vg := by
    intro u hu2 huC
    have hw2 : (g⁻¹ * u * g) * (g⁻¹ * u * g) = 1 := by
      rw [show (g⁻¹ * u * g) * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g by group, hu2, mul_one]
      exact inv_mul_cancel g
    have hwC : g⁻¹ * u * g ∈ Subgroup.centralizer (B.U : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have hga : g * a * g⁻¹ ∈ (X : Set G) := by
        rw [hXg]
        exact Work.CORE2A.mem_conjSub_iff.mpr (by
          have h : g⁻¹ * (g * a * g⁻¹) * g = a := by group
          rw [h]; exact ha)
      have hcomm := (Subgroup.mem_centralizer_iff.mp huC) (g * a * g⁻¹) hga
      calc a * (g⁻¹ * u * g) = g⁻¹ * ((g * a * g⁻¹) * u) * g := by group
        _ = g⁻¹ * (u * (g * a * g⁻¹)) * g := by rw [hcomm]
        _ = (g⁻¹ * u * g) * a := by group
    have hwV : g⁻¹ * u * g ∈ Work.GW2.pCoreIn 2 B.Hhat :=
      Work.CORE3.InvolutionMemVOfMemCentralizer I hBc B h1 D hU3 hw2 hwC
    rw [hVg, Work.CORE2A.mem_conjSub_iff]
    exact hwV
  have hb1sq : b1 * b1 = 1 := ((orderOf_eq_two_iff_mul_self b1).mp hb1ord).1
  have hb2sq : b2 * b2 = 1 := ((orderOf_eq_two_iff_mul_self b2).mp hb2ord).1
  have hyb1 : y * b1 * y = b1 := hb1I.2.trans (inv_eq_of_mul_eq_one_right hb1sq)
  have hyb2 : y * b2 * y = b2 := hb2I.2.trans (inv_eq_of_mul_eq_one_right hb2sq)
  have hb1y2 : (b1 * y) * (b1 * y) = 1 := by
    rw [show (b1 * y) * (b1 * y) = b1 * (y * b1 * y) by group, hyb1, hb1sq]
  have hb2y2 : (b2 * y) * (b2 * y) = 1 := by
    rw [show (b2 * y) * (b2 * y) = b2 * (y * b2 * y) by group, hyb2, hb2sq]
  have hb1yC : b1 * y ∈ Subgroup.centralizer (X : Set G) := by
    rw [hXeq]
    refine mul_mem_centralizer_zpowers ?_ (hinv x hxX)
    rw [inv_eq_of_mul_eq_one_right hb1sq]
    exact hconj1
  have hb2yC : b2 * y ∈ Subgroup.centralizer (X : Set G) := by
    rw [hXeq]
    refine mul_mem_centralizer_zpowers ?_ (hinv x hxX)
    rw [inv_eq_of_mul_eq_one_right hb2sq]
    exact hconj2
  have hb1yV : b1 * y ∈ Vg := hInvolVg (b1 * y) hb1y2 hb1yC
  have hb2yV : b2 * y ∈ Vg := hInvolVg (b2 * y) hb2y2 hb2yC
  have hprodin : b1 * b2 ∈ Vg := by
    have h1 : (b1 * y) * (b2 * y) = b1 * b2 := by
      rw [show (b1 * y) * (b2 * y) = b1 * (y * b2 * y) by group, hyb2]
    rw [← h1]
    exact Vg.mul_mem hb1yV hb2yV
  have hqsq : (b1 * b2) * (b1 * b2) = 1 := hVgsq _ hprodin
  have hq2ne : (b1 * b2) ^ 2 ≠ 1 := by
    intro h2
    have hdvd2 : orderOf (b1 * b2) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
    have hdvd3 : orderOf (b1 * b2) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hcube
    have hone : orderOf (b1 * b2) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
      · exact h
      · rw [h] at hdvd3
        norm_num at hdvd3
    have hq1 : b1 * b2 = 1 := orderOf_eq_one_iff.mp hone
    refine hb12 ?_
    calc b1 = b1 * (b2 * b2) := by rw [hb2sq, mul_one]
      _ = (b1 * b2) * b2 := by group
      _ = 1 * b2 := by rw [hq1]
      _ = b2 := one_mul b2
  rw [pow_two] at hq2ne
  exact hq2ne hqsq

end Work.CORE3
