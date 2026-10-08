/-
# Auxiliary lemmas for Peterfalvi Ch. I §2 Prop. 2(b)

The target of `Submission.Work.NormalComplement.bender_prelim` is Peterfalvi's
Ch. I §2 Prop. 2(b): if `H` is a strongly embedded subgroup of the finite group `G` and
`t ∉ H` is an involution, then `D = H ∩ H^t = twoPoint H t` acts transitively on the
involutions of `H`.

This module collects the elementary geometric facts about a strongly embedded subgroup
`H` that the proof needs:

* `conj_eq_of_mem_conj_of_involution`: an involution of `G` lies in at most one conjugate of
  `H` (the uniqueness of the fixed point of an involution on `Ω = G ⧸ H`,
  `Work.ThreePoints.ncard_fixedPts_zpowers`);
* `existsUnique_involution_conj`: **Peterfalvi I Ch. I §2 Prop. 1(a)** in the form used by
  Lemma 1: for `s ∈ Inv(H)` and `w ∈ Inv(G) ∖ Inv(H)` there is exactly one involution `z`
  with `z * s * z⁻¹ = w` (existence from `Work.ThreePoints.odd_orderOf_mul` +
  `Work.ThreePoints.exists_involution_conj_of_odd_orderOf_mul`, uniqueness from the finiteness
  of `Inv(G) ∖ Inv(H)` and the surjectivity just established).
-/
import Mathlib
import Submission.Work.NormalComplement.Prelim
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Sec2
import Submission.Work.ThreePoints.exists_involution_conj_of_odd_orderOf_mul
import Submission.Work.DoubleTransitivity.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false

open Classical
open scoped Pointwise commutatorElement
open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.NormalComplement

open Work.ThreePoints

variable {G : Type} [Group G] [Finite G]

/-- The set of involutions of `G` transforming `H` into `H^t`, i.e. Peterfalvi's
`Inv(Ht) = {u ∈ Inv(G) | H^u = H^t}` (Ch. I §2 Prop. 2).  Note that
`u ∈ invOfConj H t ↔ orderOf u = 2 ∧ conj u H = conj t H` definitionally. -/
def invOfConj (H : Subgroup G) (t : G) : Set G :=
  {z : G | orderOf z = 2 ∧ conj z H = conj t H}

omit [Finite G] in
theorem mem_invOfConj {H : Subgroup G} {t z : G} :
    z ∈ invOfConj H t ↔ orderOf z = 2 ∧ conj z H = conj t H := Iff.rfl

/-- **An involution of `G` lies in a unique conjugate of a strongly embedded subgroup.**
(Uniqueness of the fixed point of an involution in `Ω = G ⧸ H`.) -/
theorem conj_eq_of_mem_conj_of_involution {H : Subgroup G} (hH : IsStronglyEmbedded H) {u : G}
    (hu : orderOf u = 2) {g g' : G} (hg : u ∈ conj g H) (hg' : u ∈ conj g' H) :
    conj g H = conj g' H := by
  have h1 : (g : G ⧸ H) ∈ fixedPts H (Subgroup.zpowers u) := by
    rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
    exact Subgroup.zpowers_le.mpr hg
  have h2 : (g' : G ⧸ H) ∈ fixedPts H (Subgroup.zpowers u) := by
    rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk]
    exact Subgroup.zpowers_le.mpr hg'
  obtain ⟨ω, hω⟩ := Set.ncard_eq_one.mp (ncard_fixedPts_zpowers hH hu)
  have hgω : (g : G ⧸ H) = ω := by rw [hω] at h1; exact h1
  have hg'ω : (g' : G ⧸ H) = ω := by rw [hω] at h2; exact h2
  have hq : (g : G ⧸ H) = (g' : G ⧸ H) := by rw [hgω, hg'ω]
  rw [← stabilizer_mk H g, ← stabilizer_mk H g', hq]

/-- **Peterfalvi I Ch. I §2 Prop. 1(a)** (existence and uniqueness of the conjugating
involution), in the case where one of the involutions lies in `H` and the other does not.
For `s ∈ Inv(H)` and `w ∈ Inv(G) ∖ Inv(H)` there is exactly one involution `z ∉ H` with
`z * s * z⁻¹ = w`. -/
theorem existsUnique_involution_conj {H : Subgroup G} (hH : IsStronglyEmbedded H) {s w : G}
    (hs : orderOf s = 2) (hsH : s ∈ H) (hw : orderOf w = 2) (hwH : w ∉ H) :
    ∃! z : G, orderOf z = 2 ∧ z ∉ H ∧ z * s * z⁻¹ = w := by
  have hconj1 : conj 1 H = H := DoubleTransitivity.conj_one H
  have horder : ∀ z : G, orderOf (z * s * z⁻¹) = orderOf s := by
    intro z
    rw [← MulAut.conj_apply]
    exact orderOf_injective (MulAut.conj z).toMonoidHom (MulAut.conj z).injective s
  -- `s` and any `w' ∉ H` have no common conjugate of `H`, i.e. distinct fixed points on `Ω`
  have hsep' : ∀ w' : G, w' ∉ H → ∀ ω : G ⧸ H, s • ω = ω → w' • ω ≠ ω := by
    intro w' hw'H ω hω hwω
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective ω
    have hsg : s ∈ conj g H := DoubleTransitivity.smul_mk_eq_mk_iff.mp hω
    have hwg : w' ∈ conj g H := DoubleTransitivity.smul_mk_eq_mk_iff.mp hwω
    have hs1 : s ∈ conj 1 H := by rw [hconj1]; exact hsH
    have heq : conj g H = conj 1 H := conj_eq_of_mem_conj_of_involution hH hs hsg hs1
    exact hw'H (by rw [heq, hconj1] at hwg; exact hwg)
  -- conjugation by `z ∉ H` sends `s ∈ H` outside `H`
  have hnotmem : ∀ z : G, z ∉ H → z * s * z⁻¹ ∉ H := by
    intro z hz hmem
    have h1 : z * s * z⁻¹ ∈ conj z H := by
      simpa [MulAut.conj_apply] using Subgroup.mem_map_of_mem (MulAut.conj z).toMonoidHom hsH
    have h2 : z * s * z⁻¹ ∈ conj 1 H := by rw [hconj1]; exact hmem
    have hord : orderOf (z * s * z⁻¹) = 2 := by rw [horder z, hs]
    have heq : conj z H = conj 1 H := conj_eq_of_mem_conj_of_involution hH hord h1 h2
    have hzN : z ∈ Subgroup.normalizer (H : Set G) := by
      rw [← DoubleTransitivity.conj_eq_self_iff_mem_normalizer]
      rw [heq, hconj1]
    rw [IsStronglyEmbedded.normalizer_eq hH] at hzN
    exact hz hzN
  -- existence for every `w' ∉ H`
  have hex : ∀ w' : G, orderOf w' = 2 → w' ∉ H →
      ∃ z : G, orderOf z = 2 ∧ z ∉ H ∧ z * s * z⁻¹ = w' := by
    intro w' hw'2 hw'H
    obtain ⟨u, hu2, hus, _⟩ := exists_involution_conj_of_odd_orderOf_mul hs hw'2
      (odd_orderOf_mul hH hs hw'2 (hsep' w' hw'H))
    refine ⟨u, hu2, ?_, hus⟩
    intro huH'
    rw [← hus] at hw'H
    exact hw'H (H.mul_mem (H.mul_mem huH' hsH) (H.inv_mem huH'))
  obtain ⟨u, hu2, huH, hus⟩ := hex w hw hwH
  refine ⟨u, ⟨hu2, huH, hus⟩, ?_⟩
  intro y hy
  obtain ⟨hy2, hyH, hys⟩ := hy
  -- the self-map `z ↦ z s z⁻¹` of `{z | orderOf z = 2 ∧ z ∉ H}` is a bijection
  let A := {z : G // orderOf z = 2 ∧ z ∉ H}
  have hAfin : Finite A := Subtype.finite
  let Ψ : A → A := fun z => ⟨z.1 * s * z.1⁻¹,
    ⟨by rw [horder z.1, hs], hnotmem z.1 z.2.2⟩⟩
  have hsurj : Function.Surjective Ψ := by
    intro a
    obtain ⟨z, hz2, hzH, hz⟩ := hex a.1 a.2.1 a.2.2
    exact ⟨⟨z, hz2, hzH⟩, Subtype.ext hz⟩
  have hinj := (Finite.injective_iff_surjective).mpr hsurj
  have key : Ψ ⟨y, hy2, hyH⟩ = Ψ ⟨u, hu2, huH⟩ := by
    apply Subtype.ext
    show y * s * y⁻¹ = u * s * u⁻¹
    rw [hys, hus]
  exact congrArg Subtype.val (hinj key)

/-- A strongly embedded subgroup contains an involution (it has even order, so Cauchy applies). -/
theorem exists_mem_orderOf_eq_two {H : Subgroup G} (hH : IsStronglyEmbedded H) :
    ∃ s : G, s ∈ H ∧ orderOf s = 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card H := even_iff_two_dvd.mp (IsStronglyEmbedded.even_card hH)
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 2 h2
  have hs2 : s * s = 1 := by
    have h := pow_orderOf_eq_one s
    rw [hs, pow_two] at h
    exact h
  have hsne : s ≠ 1 := by
    intro h1
    rw [h1] at hs
    simp at hs
  refine ⟨(s : G), s.2, orderOf_eq_two_of ?_ ?_⟩
  · intro h1
    exact hsne (Subtype.ext h1)
  · have h := congrArg (Subtype.val) hs2
    simpa using h

/-- **Peterfalvi I Ch. I §2 Prop. 2**, first half: `z ↦ z * t` is a bijection between the
involutions transforming `H` into `H^t` and `K = J(D,t) = invertedBy (twoPoint H t) t`.
(Cf. App. I (1).) -/
theorem kapp_ncard_eq_invOfConj_ncard {H : Subgroup G} {t : G}
    (hH : IsStronglyEmbedded H) (ht : orderOf t = 2) (htH : t ∉ H) :
    (invertedBy (twoPoint H t) t).ncard = (invOfConj H t).ncard := by
  have ht2 : t * t = 1 := mul_self_eq_one_of_orderOf_eq_two ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hN : Subgroup.normalizer (H : Set G) = H := IsStronglyEmbedded.normalizer_eq hH
  -- `z ∈ Inv(Ht)` gives `z * t ∈ K`
  have hfw : ∀ z ∈ invOfConj H t, z * t ∈ invertedBy (twoPoint H t) t := by
    intro z hz
    obtain ⟨hz2, hzj⟩ := hz
    have hzsq : z * z = 1 := mul_self_eq_one_of_orderOf_eq_two hz2
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzsq
    have htzH : t * z ∈ H := by
      rw [← hN, ← DoubleTransitivity.conj_eq_self_iff_mem_normalizer]
      rw [DoubleTransitivity.conj_mul, hzj, ← DoubleTransitivity.conj_mul, ht2,
        DoubleTransitivity.conj_one]
    have hstep : t * (z * t) * t = t * z * (t * t) := by simp only [mul_assoc]
    have htz : t * (z * t) * t = t * z := by rw [hstep, ht2, mul_one]
    have htz' : t * (z * t) * t⁻¹ = t * z := by rw [htinv]; exact htz
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have : z * t = (t * z)⁻¹ := by rw [mul_inv_rev, htinv, hzinv]
      rw [this]; exact H.inv_mem htzH
    · have hgoal : z * t ∈ conj t H := by
        rw [Work.ThreePoints.mem_conj_iff]
        rw [htinv, htz]; exact htzH
      exact hgoal
    · have h2 : (z * t)⁻¹ = t * z := by rw [mul_inv_rev, htinv, hzinv]
      rw [htz', h2]
  -- `d ∈ K` gives `d * t ∈ Inv(Ht)`
  have hbw : ∀ d ∈ invertedBy (twoPoint H t) t, d * t ∈ invOfConj H t := by
    intro d hd
    obtain ⟨hdD, hdd⟩ := hd
    obtain ⟨hdH, _⟩ := hdD
    have htdt : t * d * t = d⁻¹ := by simpa [htinv] using hdd
    have hdfac : d * t = t * (t⁻¹ * d * t) := by group
    have hddt : (d * t) * (d * t) = d * (t * d * t) := by simp only [mul_assoc]
    have hsq : (d * t) * (d * t) = 1 := by rw [hddt, htdt, mul_inv_cancel]
    have hne : d * t ≠ 1 := by
      intro hcon
      have h1 : d = t⁻¹ := eq_inv_of_mul_eq_one_left hcon
      rw [htinv] at h1
      exact htH (h1 ▸ hdH)
    refine ⟨orderOf_eq_two_of hne hsq, ?_⟩
    rw [hdfac, DoubleTransitivity.conj_mul]
    have hthis : t⁻¹ * d * t = d⁻¹ := by simpa [htinv] using hdd
    rw [hthis, conj_eq_self_of_mem (H.inv_mem hdH)]
  refine Set.ncard_congr (s := invertedBy (twoPoint H t) t) (t := invOfConj H t)
    (fun d _ => d * t) hbw (fun a b _ _ hab => mul_right_cancel hab) ?_
  intro z hz
  exact ⟨z * t, hfw z hz, by rw [show z * t * t = z * (t * t) from by simp only [mul_assoc],
    ht2, mul_one]⟩

/-- **Peterfalvi I Ch. I §2 Lemma 1** (pp. 151–152): for `X ≤ H`, `u ∈ Inv(H)` and `t ∉ H` an
involution, the orbit of `u` under `X` is at least as large as `J(X,t) = invertedBy X t`.
(The source's "`X` of odd order" is not used in the proof.) -/
theorem lemma1_ncard_orbit_ge {H X : Subgroup G} (hH : IsStronglyEmbedded H) {u t : G}
    (hu : orderOf u = 2) (huH : u ∈ H) (ht : orderOf t = 2) (htH : t ∉ H) (hX : X ≤ H) :
    (invertedBy X t).ncard ≤ ((fun x : G => x * u * x⁻¹) '' (X : Set G)).ncard := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_orderOf_eq_two ht)
  -- the map `x ↦ x⁻¹ * u * x` is injective on `J(X,t)`
  have hinj : ∀ x ∈ invertedBy X t, ∀ y ∈ invertedBy X t,
      x⁻¹ * u * x = y⁻¹ * u * y → x = y := by
    intro x hx y hy hxy
    obtain ⟨hxX, hxt⟩ := hx
    obtain ⟨hyX, hyt⟩ := hy
    have hxt' : t * x * t = x⁻¹ := by simpa [htinv] using hxt
    have hyt' : t * y * t = y⁻¹ := by simpa [htinv] using hyt
    -- `t * x⁻¹` inverts `x`
    have htxt : t * x⁻¹ * t = x := by
      have h := congrArg Inv.inv hxt'
      rw [mul_inv_rev, mul_inv_rev, htinv, inv_inv] at h
      simpa only [mul_assoc] using h
    have htyt : t * y⁻¹ * t = y := by
      have h := congrArg Inv.inv hyt'
      rw [mul_inv_rev, mul_inv_rev, htinv, inv_inv] at h
      simpa only [mul_assoc] using h
    have hsqx : (t * x⁻¹) * (t * x⁻¹) = (t * x⁻¹ * t) * x⁻¹ := by simp only [mul_assoc]
    have hsqx1 : (t * x⁻¹) * (t * x⁻¹) = 1 := by rw [hsqx, htxt, mul_inv_cancel]
    have hsqy1 : (t * y⁻¹) * (t * y⁻¹) = 1 := by
      rw [show (t * y⁻¹) * (t * y⁻¹) = (t * y⁻¹ * t) * y⁻¹ from by simp only [mul_assoc],
        htyt, mul_inv_cancel]
    have hxu : t * x⁻¹ ∉ H := by
      intro hmem
      refine htH ?_
      have : t = (t * x⁻¹) * x := by group
      rw [this]; exact H.mul_mem hmem (hX hxX)
    have hyu : t * y⁻¹ ∉ H := by
      intro hmem
      refine htH ?_
      have : t = (t * y⁻¹) * y := by group
      rw [this]; exact H.mul_mem hmem (hX hyX)
    have hxne : t * x⁻¹ ≠ 1 := by
      intro hcon
      have : t = x := mul_inv_eq_one.mp hcon
      exact htH (this ▸ hX hxX)
    have hyne : t * y⁻¹ ≠ 1 := by
      intro hcon
      have : t = y := mul_inv_eq_one.mp hcon
      exact htH (this ▸ hX hyX)
    have hxord : orderOf (t * x⁻¹) = 2 := orderOf_eq_two_of hxne hsqx1
    have hyord : orderOf (t * y⁻¹) = 2 := orderOf_eq_two_of hyne hsqy1
    have h1w : (t * x⁻¹) * u * (t * x⁻¹)⁻¹ = t * (x⁻¹ * u * x) * t := by
      have hinv : (t * x⁻¹)⁻¹ = x * t := by rw [mul_inv_rev, htinv, inv_inv]
      rw [hinv]; group
    have h2w : (t * y⁻¹) * u * (t * y⁻¹)⁻¹ = t * (y⁻¹ * u * y) * t := by
      have hinv : (t * y⁻¹)⁻¹ = y * t := by rw [mul_inv_rev, htinv, inv_inv]
      rw [hinv]; group
    have hwx : orderOf (t * (x⁻¹ * u * x) * t) = 2 := by
      have hfac : t * (x⁻¹ * u * x) * t = (MulAut.conj t) ((MulAut.conj x⁻¹) u) := by
        rw [MulAut.conj_apply, MulAut.conj_apply, inv_inv, htinv]
      rw [hfac, MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, hu]
    have hwxH : t * (x⁻¹ * u * x) * t ∉ H := by
      intro hmem
      have hcin : t * (x⁻¹ * u * x) * t ∈ conj (t * x⁻¹) H := by
        have hval : (MulAut.conj (t * x⁻¹)) u = t * (x⁻¹ * u * x) * t := by
          rw [MulAut.conj_apply, mul_inv_rev, inv_inv, htinv]; group
        rw [← hval]
        exact Subgroup.mem_map_of_mem (MulAut.conj (t * x⁻¹)).toMonoidHom huH
      have hcin2 : t * (x⁻¹ * u * x) * t ∈ conj (1 : G) H := by
        rw [DoubleTransitivity.conj_one]; exact hmem
      have heq : conj (t * x⁻¹) H = conj (1 : G) H :=
        conj_eq_of_mem_conj_of_involution hH hwx hcin hcin2
      rw [DoubleTransitivity.conj_one] at heq
      have hzN : t * x⁻¹ ∈ Subgroup.normalizer (H : Set G) := by
        rw [← DoubleTransitivity.conj_eq_self_iff_mem_normalizer]
        exact heq
      rw [IsStronglyEmbedded.normalizer_eq hH] at hzN
      exact hxu hzN
    have hkey := (existsUnique_involution_conj hH hu huH hwx hwxH).unique
      ⟨hxord, hxu, h1w⟩ ⟨hyord, hyu, h2w.trans (by rw [hxy])⟩
    have h1 : x⁻¹ = y⁻¹ := mul_left_cancel hkey
    exact inv_injective h1
  have hsub : ((fun x : G => x⁻¹ * u * x) '' (invertedBy X t : Set G)) ⊆
      ((fun x : G => x * u * x⁻¹) '' (X : Set G)) := by
    rintro y ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, X.inv_mem hx.1, by group⟩
  have himg : (invertedBy X t).ncard =
      ((fun x : G => x⁻¹ * u * x) '' (invertedBy X t : Set G)).ncard :=
    Set.ncard_congr (fun x _ => x⁻¹ * u * x) (fun x hx => ⟨x, hx, rfl⟩)
      (fun a b ha hb h => hinj a ha b hb h)
      (fun y hy => by obtain ⟨x, hx, rfl⟩ := hy; exact ⟨x, hx, rfl⟩)
  rw [himg]
  exact Set.ncard_le_ncard hsub

/-- **Peterfalvi I Ch. I §2 Prop. 1(c)** in the form used by Prop. 2: the number of involutions
`z` with `H^z = H^t` is `n = |Inv(H)|`.  Equivalently `|Inv(Ht)| = |Inv(H)|`.

Proof: fix `s ∈ Inv(H)`.  The map `z ↦ z s z⁻¹` is a bijection of the set `A` of involutions
outside `H` (existence and uniqueness of the conjugating involution, `existsUnique_involution_conj`),
and it carries `Inv(Ht) ⊆ A` onto the involutions lying in `H^t`; conjugation by `t` identifies
those with the involutions of `H`. -/
theorem invOfConj_ncard_eq_involutions_ncard {H : Subgroup G} {t : G}
    (hH : IsStronglyEmbedded H) (ht : orderOf t = 2) (htH : t ∉ H) :
    (invOfConj H t).ncard = (involutions (H : Set G)).ncard := by
  obtain ⟨s, hsH, hs2⟩ := exists_mem_orderOf_eq_two hH
  have htinj : t⁻¹ = t := inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_orderOf_eq_two ht)
  have htne : conj t H ≠ H := by
    intro h
    have hN : t ∈ Subgroup.normalizer (H : Set G) :=
      (DoubleTransitivity.conj_eq_self_iff_mem_normalizer t H).mp h
    rw [IsStronglyEmbedded.normalizer_eq hH] at hN
    exact htH hN
  have hordz : ∀ z : G, orderOf (z * s * z⁻¹) = 2 := by
    intro z
    have h : z * s * z⁻¹ = (MulAut.conj z) s := by rw [MulAut.conj_apply]
    rw [h, MulEquiv.orderOf_eq, hs2]
  have hnotmem : ∀ z : G, z ∉ H → z * s * z⁻¹ ∉ H := by
    intro z hz hmem
    have h1 : z * s * z⁻¹ ∈ conj z H := by
      simpa [MulAut.conj_apply] using Subgroup.mem_map_of_mem (MulAut.conj z).toMonoidHom hsH
    have h2 : z * s * z⁻¹ ∈ conj (1 : G) H := by
      rw [DoubleTransitivity.conj_one]; exact hmem
    have heq : conj z H = conj (1 : G) H :=
      conj_eq_of_mem_conj_of_involution hH (hordz z) h1 h2
    have hzN : z ∈ Subgroup.normalizer (H : Set G) := by
      rw [← DoubleTransitivity.conj_eq_self_iff_mem_normalizer]
      rw [heq, DoubleTransitivity.conj_one]
    rw [IsStronglyEmbedded.normalizer_eq hH] at hzN
    exact hz hzN
  have hmemA : ∀ z ∈ invOfConj H t, orderOf z = 2 ∧ z ∉ H := by
    intro z hz
    obtain ⟨hz2, hzj⟩ := hz
    refine ⟨hz2, ?_⟩
    intro hzH
    exact htne (hzj ▸ conj_eq_self_of_mem hzH)
  have hconjz : ∀ z : G, z * s * z⁻¹ ∈ conj z H := by
    intro z
    simpa [MulAut.conj_apply] using Subgroup.mem_map_of_mem (MulAut.conj z).toMonoidHom hsH
  -- step 1: `|Inv(Ht)| = |Inv(H^t)|`
  have h1 : (invOfConj H t).ncard = (involutions (conj t H : Set G)).ncard := by
    refine Set.ncard_congr (s := invOfConj H t) (t := involutions (conj t H : Set G))
      (fun z _ => z * s * z⁻¹) ?_ ?_ ?_
    · intro z hz
      obtain ⟨-, hzj⟩ := hz
      exact ⟨hzj ▸ hconjz z, hordz z⟩
    · intro a b ha hb hab
      exact (existsUnique_involution_conj hH hs2 hsH (hordz a) (hnotmem a (hmemA a ha).2)).unique
        ⟨(hmemA a ha).1, (hmemA a ha).2, rfl⟩
        ⟨(hmemA b hb).1, (hmemA b hb).2, hab.symm⟩
    · intro w hw
      obtain ⟨hwc, hw2⟩ := hw
      have hwH : w ∉ H := by
        intro hmem
        have heq : conj t H = conj (1 : G) H := conj_eq_of_mem_conj_of_involution hH hw2 hwc
          (by rw [DoubleTransitivity.conj_one]; exact hmem)
        rw [DoubleTransitivity.conj_one] at heq
        exact htne heq
      obtain ⟨z, hz2, hzH, hz⟩ := (existsUnique_involution_conj hH hs2 hsH hw2 hwH).exists
      refine ⟨z, ?_, hz⟩
      refine ⟨hz2, ?_⟩
      exact conj_eq_of_mem_conj_of_involution hH (hordz z) (hconjz z) (by rw [hz]; exact hwc)
  rw [h1]
  -- step 2: conjugation by `t` identifies `Inv(H^t)` with `Inv(H)`
  refine Set.ncard_congr (s := involutions (conj t H : Set G)) (t := involutions (H : Set G))
    (fun x _ => t⁻¹ * x * t) ?_ ?_ ?_
  · intro x hx
    obtain ⟨hxc, hx2⟩ := hx
    refine ⟨?_, ?_⟩
    · have hmem : x ∈ conj t H := hxc
      rw [Work.ThreePoints.mem_conj_iff] at hmem
      exact hmem
    · have hval : t⁻¹ * x * t = (MulAut.conj t⁻¹) x := by rw [MulAut.conj_apply, inv_inv]
      rw [hval, MulEquiv.orderOf_eq, hx2]
  · intro a b _ _ hab
    exact mul_left_cancel (mul_right_cancel hab)
  · intro y hy
    refine ⟨t * y * t⁻¹, ⟨?_, ?_⟩, ?_⟩
    · have hmem : t * y * t⁻¹ ∈ conj t H := by
        rw [Work.ThreePoints.mem_conj_iff]
        rw [show t⁻¹ * (t * y * t⁻¹) * t = y from by group]
        exact hy.1
      exact hmem
    · have hval : t * y * t⁻¹ = (MulAut.conj t) y := by rw [MulAut.conj_apply]
      rw [hval, MulEquiv.orderOf_eq, hy.2]
    · show t⁻¹ * (t * y * t⁻¹) * t = y
      group

end Work.NormalComplement
