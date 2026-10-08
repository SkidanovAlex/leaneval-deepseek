import Mathlib
import Submission.Work.DoubleTransitivity.Basic
import Submission.Work.DoubleTransitivity.App1.Defs
import Submission.Work.DoubleTransitivity.App1.app1_1b
import Submission.Work.DoubleTransitivity.Sec1.unique_fixed
import Submission.Work.DoubleTransitivity.Sec2.prop1a_exists
import Submission.Work.DoubleTransitivity.Sec2.prop1a_unique
import Submission.Work.DoubleTransitivity.Sec2.lemma1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.DoubleTransitivity.Sec2.prop2`

Peterfalvi, *Le théorème de Bender–Suzuki I*, Ch. I §2 **Proposition 2 (b)** (p. 152).

Let `H` be a Bender subgroup of the finite group `G` with `H ≠ ⊤` (the standing hypothesis (A0)
of Ch. I §2, i.e. `H` is strongly embedded), and let `t ∉ H` be an involution.  With

* `D = H ∩ H^t = twoPoint H t` (the two-point stabiliser of `H` and `H^t`),
* `K = J(D,t) = {x ∈ D | t x t⁻¹ = x⁻¹} = invertedBy (twoPoint H t) t`,
* `n = |Inv(H)| = (involutions (H : Set G)).ncard`,

the proposition asserts

1. `D` acts by conjugation transitively on `Inv(H)`;
2. `|K| = n`;
3. `|u^D| = n` for every `u ∈ Inv(H)`, where `u^D = conjOrbit (twoPoint H t) u`.

The proof follows the source.  Write `Inv(Ht)` for the set of involutions `u` of `G`
transforming `H` into `H^t` (`conj u H = conj t H`), i.e. the involutions of the coset `Ht`.

* `|K| = |Inv(Ht)|`: the map `x ↦ x t` is a bijection, because for `x ∈ K` one has
  `(x t)² = x (t x t) = 1` and `conj (x t) H = conj x (conj t H) = conj t H` (using `x ∈ H^t`),
  while conversely an involution `u` with `conj u H = conj t H` satisfies `t⁻¹ u ∈ N_G(H) = H`
  (Bender subgroups are self-normalising), so `u ∈ Ht` and `u t = (t⁻¹ u)⁻¹ ∈ H ∩ H^t`
  is inverted by `t`.
* `|Inv(Ht)| = |Inv(H)|` (Prop. 1 (c)): fix an involution `s ∈ H`.  The map `u ↦ u⁻¹ s u` sends
  `Inv(Ht)` into `Inv(H^t)`; it is injective because `s`, lying in `H`, and `u⁻¹ s u`, lying in
  `H^t ≠ H`, share no fixed point (an involution lies in exactly one conjugate of `H`,
  `Sec1.unique_fixed`), so Prop. 1 (a) (`prop1a_unique`) gives uniqueness of the involution
  conjugating `s` to a given element; and it is surjective by Prop. 1 (a)'s existence half
  (`prop1a_exists`): if `u⁻¹ s u = w ∈ conj t H`, then `s = u w u⁻¹ ∈ conj (u * t) H`, so
  `conj (u * t) H = H` by uniqueness of the conjugate of `H` containing `s`, whence `u * t ∈ H`
  and `conj u H = conj t H`.  Conjugation by `t` then identifies `Inv(H^t)` with `Inv(H)`.

Finally, for `u ∈ Inv(H)` Peterfalvi's Lemma 1 (`Work.DoubleTransitivity.Sec2.lemma1`) says that
`x ↦ x⁻¹ u x` is injective on `K`, so `n = |K| ≤ |u^D|`; and `u^D ⊆ Inv(H)` has at most `n`
elements.  Hence `u^D = Inv(H)` for every `u ∈ Inv(H)`, which is statement 1, and gives
statement 3 at once.
-/

namespace Work.DoubleTransitivity.Sec2

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-- Conjugation by an element of `H` fixes `H`. -/
private lemma conj_self_eq_of_mem' {H : Subgroup G} {k : G} (hk : k ∈ H) : conj k H = H :=
  (conj_eq_self_iff_mem_normalizer k H).mpr (Subgroup.le_normalizer hk)

/-- Two involutions lying in conjugates of `H` with distinct canonical points share no fixed
point of `Ω` (uniqueness of the fixed point of an involution). -/
private lemma not_exists_common_fixed' {H : Subgroup G} (hH : IsBender H) {u₀ v₀ g h : G}
    (hu : orderOf u₀ = 2) (hv : orderOf v₀ = 2) (hu' : u₀ ∈ conj g H)
    (hv' : v₀ ∈ conj h H) (hab : (QuotientGroup.mk g : Omega H) ≠ QuotientGroup.mk h) :
    ¬ ∃ ω : Omega H, u₀ • ω = ω ∧ v₀ • ω = ω := by
  rintro ⟨ω, hωu, hωv⟩
  have h1 : ω = (QuotientGroup.mk g : Omega H) :=
    Sec1.eq_of_smul_eq_of_orderOf_eq_two hH hu hωu (smul_mk_eq_mk_iff.mpr hu')
  have h2 : ω = (QuotientGroup.mk h : Omega H) :=
    Sec1.eq_of_smul_eq_of_orderOf_eq_two hH hv hωv (smul_mk_eq_mk_iff.mpr hv')
  exact hab (h1.symm.trans h2)

/-- An involution of order `2` is its own inverse. -/
private lemma inv_eq_self' {u : G} (hu : orderOf u = 2) : u⁻¹ = u :=
  App1.inv_eq_self_of_orderOf_eq_two hu

/-- The involutions transforming `H` into the conjugate `H^t` (i.e. the involutions of the
coset `Ht`). -/
private def invHt' (H : Subgroup G) (t : G) : Set G :=
  {u : G | orderOf u = 2 ∧ conj u H = conj t H}

/-! ## `K = J(D,t)` and `Inv(Ht)` have the same number of elements -/

private lemma mul_t_mem_invHt' {H : Subgroup G} {t x : G} (ht : orderOf t = 2) (htH : t ∉ H)
    (hx : x ∈ invertedBy (twoPoint H t) t) : x * t ∈ invHt' H t := by
  obtain ⟨hxD, hxinv⟩ := hx
  have hxH : x ∈ H := (Subgroup.mem_inf.mp hxD).1
  have hxA : x ∈ conj t H := (Subgroup.mem_inf.mp hxD).2
  have htt : t * t = 1 := App1.mul_self_eq_one_of_orderOf_eq_two ht
  have htin : t⁻¹ = t := inv_eq_self' ht
  refine ⟨?_, ?_⟩
  · refine orderOf_eq_prime ?_ ?_
    · rw [pow_two]
      have h : t * x * t = x⁻¹ := by simpa only [htin] using hxinv
      calc (x * t) * (x * t) = x * (t * x * t) := by group
        _ = x * x⁻¹ := by rw [h]
        _ = 1 := mul_inv_cancel x
    · intro h1
      have hxt : x = t := by
        calc x = x * 1 := (mul_one x).symm
          _ = x * (t * t) := by rw [htt]
          _ = (x * t) * t := by group
          _ = 1 * t := by rw [h1]
          _ = t := one_mul t
      exact htH (hxt ▸ hxH)
  · rw [conj_mul, conj_self_eq_of_mem' hxA]

private lemma mul_t_mem_of_mem_invHt' {H : Subgroup G} (hH : IsBender H) {t u : G}
    (ht : orderOf t = 2) (hu : u ∈ invHt' H t) : u * t ∈ H := by
  have huconj : conj u H = conj t H := hu.2
  have htin : t⁻¹ = t := inv_eq_self' ht
  have hnorm : Subgroup.normalizer (H : Set G) ≤ H := hH.normalizer_le le_rfl hH.1
  have hc : conj (t⁻¹ * u) H = H := by
    rw [conj_mul, huconj, ← conj_mul, inv_mul_cancel, conj_one]
  have hmem : t⁻¹ * u ∈ H := hnorm ((conj_eq_self_iff_mem_normalizer _ _).mp hc)
  have htu : t * u ∈ H := by simpa [htin] using hmem
  have h2 : (t * u)⁻¹ ∈ H := H.inv_mem htu
  rwa [show (t * u)⁻¹ = u * t from by rw [mul_inv_rev, htin, inv_eq_self' hu.1]] at h2

private lemma mul_t_mem_Kset' {H : Subgroup G} (hH : IsBender H) {t u : G} (ht : orderOf t = 2)
    (hu : u ∈ invHt' H t) : u * t ∈ invertedBy (twoPoint H t) t := by
  have hu2 : orderOf u = 2 := hu.1
  have htt : t * t = 1 := App1.mul_self_eq_one_of_orderOf_eq_two ht
  have htin : t⁻¹ = t := inv_eq_self' ht
  have hu_inv : u⁻¹ = u := inv_eq_self' hu2
  have hutH : u * t ∈ H := mul_t_mem_of_mem_invHt' hH ht hu
  have htu : t * u ∈ H := by
    have h2 : (u * t)⁻¹ ∈ H := H.inv_mem hutH
    rwa [show (u * t)⁻¹ = t * u from by rw [mul_inv_rev, htin, hu_inv]] at h2
  refine ⟨?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨hutH, ?_⟩
    rw [mem_conj]
    have h1 : t⁻¹ * (u * t) * t = t * u := by
      calc t⁻¹ * (u * t) * t = (t * u) * (t * t) := by rw [htin]; group
        _ = t * u := by rw [htt, mul_one]
    rw [h1]
    exact htu
  · have h2 : (u * t)⁻¹ = t * u := by rw [mul_inv_rev, htin, hu_inv]
    rw [h2]
    group

private theorem ncard_Kset_eq_ncard_invHt' {H : Subgroup G} (hH : IsBender H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) :
    (invertedBy (twoPoint H t) t).ncard = (invHt' H t).ncard := by
  have htt : t * t = 1 := App1.mul_self_eq_one_of_orderOf_eq_two ht
  have hmaps : Set.MapsTo (fun x => x * t) (invertedBy (twoPoint H t) t) (invHt' H t) :=
    fun x hx => mul_t_mem_invHt' ht htH hx
  have hinj : Set.InjOn (fun x => x * t) (invertedBy (twoPoint H t) t) :=
    fun x _ y _ hxy => mul_right_cancel hxy
  have hsurj : Set.SurjOn (fun x => x * t) (invertedBy (twoPoint H t) t) (invHt' H t) := by
    intro u hu
    exact ⟨u * t, mul_t_mem_Kset' hH ht hu, by show (u * t) * t = u; rw [mul_assoc, htt, mul_one]⟩
  exact Set.BijOn.ncard_eq (f := fun x => x * t) ⟨hmaps, hinj, hsurj⟩

/-! ## `|Inv(Ht)| = |Inv(H)|` (Peterfalvi I §2, Prop. 1 (c)) -/

private theorem ncard_invHt_eq_ncard_involutions' {H : Subgroup G} (hH : IsBender H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) :
    (invHt' H t).ncard = (involutions (H : Set G)).ncard := by
  classical
  obtain ⟨s₀, hs₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥H) 2 hH.1
  have hsH : (s₀ : G) ∈ H := s₀.2
  have hs2 : orderOf (s₀ : G) = 2 := by rw [Subgroup.orderOf_coe, hs₀]
  have hmk_ne : (QuotientGroup.mk (1 : G) : Omega H) ≠ (QuotientGroup.mk t : Omega H) := by
    intro hc
    exact htH (mk_one_eq_iff.mp hc.symm)
  have hcard1 : (invHt' H t).ncard = (involutions (conj t H : Set G)).ncard := by
    refine Set.ncard_congr (fun u _ => u⁻¹ * (s₀ : G) * u) ?_ ?_ ?_
    · intro u hu
      have hutH : u * t ∈ H := mul_t_mem_of_mem_invHt' hH ht hu
      refine ⟨?_, ?_⟩
      · change u⁻¹ * (s₀ : G) * u ∈ conj t H
        rw [mem_conj]
        have h1 : t⁻¹ * (u⁻¹ * (s₀ : G) * u) * t = (u * t)⁻¹ * (s₀ : G) * (u * t) := by group
        rw [h1]
        exact H.mul_mem (H.mul_mem (H.inv_mem hutH) hsH) hutH
      · simpa [MulAut.conj_apply, hs2] using MulEquiv.orderOf_eq (MulAut.conj u⁻¹) (s₀ : G)
    · intro a b ha hb hab
      have ha2 : orderOf a = 2 := ha.1
      have haA : conj a H = conj t H := ha.2
      have hb2 : orderOf b = 2 := hb.1
      have hw2 : orderOf (a⁻¹ * (s₀ : G) * a) = 2 := by
        simpa [MulAut.conj_apply, hs2] using MulEquiv.orderOf_eq (MulAut.conj a⁻¹) (s₀ : G)
      have hwa : a⁻¹ * (s₀ : G) * a ∈ conj a⁻¹ H :=
        Subgroup.mem_map.mpr ⟨(s₀ : G), hsH, by
          change MulAut.conj a⁻¹ (s₀ : G) = a⁻¹ * (s₀ : G) * a
          rw [MulAut.conj_apply, inv_inv]⟩
      have hane : (QuotientGroup.mk a⁻¹ : Omega H) ≠ (QuotientGroup.mk (1 : G) : Omega H) := by
        intro hc
        have haH : a⁻¹ ∈ H := mk_one_eq_iff.mp hc
        have hconjH : conj a H = H := by
          rw [← inv_eq_self' ha2]
          exact conj_self_eq_of_mem' haH
        have h1 : conj t H = H := by rw [← haA, hconjH]
        exact htH (hH.normalizer_le le_rfl hH.1 ((conj_eq_self_iff_mem_normalizer t H).mp h1))
      have hno : ¬ ∃ ω : Omega H, (s₀ : G) • ω = ω ∧ (a⁻¹ * (s₀ : G) * a) • ω = ω :=
        not_exists_common_fixed' hH hs2 hw2 (by rw [conj_one]; exact hsH) hwa hane.symm
      obtain ⟨v, -, hv2⟩ :=
        prop1a_unique (H := H) hH (s := (s₀ : G)) (t := a⁻¹ * (s₀ : G) * a) hs2 hw2 hno
      have h1 : a = v := hv2 a ⟨ha2, rfl⟩
      have h2 : b = v := hv2 b ⟨hb2, hab.symm⟩
      exact h1.trans h2.symm
    · intro w hw
      obtain ⟨hwA, hw2⟩ := hw
      have hno : ¬ ∃ ω : Omega H, (s₀ : G) • ω = ω ∧ w • ω = ω :=
        not_exists_common_fixed' hH hs2 hw2 (by rw [conj_one]; exact hsH) hwA hmk_ne
      obtain ⟨u, hu2, huconj, -, -⟩ :=
        prop1a_exists (H := H) hH (s := (s₀ : G)) (t := w) hs2 hw2 hno
      have hs_ut : (s₀ : G) ∈ conj (u * t) H := by
        rw [conj_mul]
        refine Subgroup.mem_map.mpr ⟨w, hwA, ?_⟩
        change MulAut.conj u w = (s₀ : G)
        rw [MulAut.conj_apply, ← huconj]
        group
      have hfix : (s₀ : G) • (QuotientGroup.mk (u * t) : Omega H) = QuotientGroup.mk (u * t) :=
        smul_mk_eq_mk_iff.mpr hs_ut
      have hfix1 : (s₀ : G) • (QuotientGroup.mk (1 : G) : Omega H) = QuotientGroup.mk 1 :=
        smul_mk_eq_mk_iff.mpr (by rw [conj_one]; exact hsH)
      have hutH : u * t ∈ H :=
        mk_one_eq_iff.mp (Sec1.eq_of_smul_eq_of_orderOf_eq_two hH hs2 hfix hfix1)
      have hA : conj u (conj t H) = H := by
        rw [← conj_mul, conj_self_eq_of_mem' hutH]
      have hu2' : u * u = 1 := App1.mul_self_eq_one_of_orderOf_eq_two hu2
      refine ⟨u, ⟨hu2, ?_⟩, huconj⟩
      conv_lhs => rw [← hA]
      rw [← conj_mul, hu2', conj_one]
  have hcard2 : (involutions (conj t H : Set G)).ncard = (involutions (H : Set G)).ncard := by
    have htt : t * t = 1 := App1.mul_self_eq_one_of_orderOf_eq_two ht
    have hconj : conj t (conj t H) = H := by rw [← conj_mul, htt, conj_one]
    refine Set.ncard_congr (fun w _ => MulAut.conj t w) ?_ ?_ ?_
    · intro w hw
      obtain ⟨hwA, hw2⟩ := hw
      have hmem : MulAut.conj t w ∈ conj t (conj t H) :=
        Subgroup.mem_map.mpr ⟨w, hwA, rfl⟩
      rw [hconj] at hmem
      exact ⟨hmem, by simpa [MulAut.conj_apply, hw2] using MulEquiv.orderOf_eq (MulAut.conj t) w⟩
    · intro a _ b _ hab
      exact (MulAut.conj t).injective hab
    · intro u hu
      refine ⟨MulAut.conj t⁻¹ u, ⟨?_, ?_⟩, ?_⟩
      · change MulAut.conj t⁻¹ u ∈ conj t H
        rw [mem_conj]
        have h1 : t⁻¹ * (MulAut.conj t⁻¹ u) * t = u := by
          rw [MulAut.conj_apply, inv_eq_self' ht]
          calc t * (t * u * t⁻¹) * t = (t * t) * u * (t⁻¹ * t) := by group
            _ = u := by rw [htt, inv_mul_cancel, one_mul, mul_one]
        rw [h1]
        exact hu.1
      · simpa [MulAut.conj_apply, hu.2] using MulEquiv.orderOf_eq (MulAut.conj t⁻¹) u
      · rw [MulAut.conj_apply, show MulAut.conj t⁻¹ u = t⁻¹ * u * (t⁻¹)⁻¹ from
            MulAut.conj_apply t⁻¹ u]
        group
  rw [hcard1, hcard2]

/-- `|K| = n`: Peterfalvi I §2 Prop. 2 (b) / Prop. 1 (c), from Prop. 1 (a). -/
private theorem ncard_Kset_eq_ncard_involutions' {H : Subgroup G} (hH : IsBender H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) :
    (invertedBy (twoPoint H t) t).ncard = (involutions (H : Set G)).ncard :=
  (ncard_Kset_eq_ncard_invHt' hH ht htH).trans (ncard_invHt_eq_ncard_involutions' hH ht htH)

/-- **Peterfalvi I §2 Prop. 2 (b).**  Let `H` be a Bender subgroup of the finite group `G`
with `H ≠ ⊤`, let `t ∉ H` be an involution and put `D = H ∩ H^t`.  Then `D` acts by conjugation
transitively on the involutions of `H`, the set `K = J(D,t) = invertedBy D t` has as many
elements as `H` has involutions, and so has the orbit `u^D` of every involution `u` of `H`. -/
theorem prop2 {G : Type} [Group G] [Finite G] {H : Subgroup G} (hH : IsBender H)
    (hne : H ≠ ⊤) {t : G} (ht : orderOf t = 2) (htH : t ∉ H) :
    (∀ u v : G, u ∈ Submission.Blueprint.involutions (H : Set G) →
      v ∈ Submission.Blueprint.involutions (H : Set G) →
      ∃ d ∈ Submission.Blueprint.twoPoint H t, d⁻¹ * u * d = v) ∧
    (Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t).ncard =
      (Submission.Blueprint.involutions (H : Set G)).ncard ∧
    (∀ u : G, u ∈ Submission.Blueprint.involutions (H : Set G) →
      (conjOrbit (Submission.Blueprint.twoPoint H t) u).ncard =
        (Submission.Blueprint.involutions (H : Set G)).ncard) := by
  classical
  -- `D = H ∩ H^t` has odd order (Bender property) and is contained in `H`.
  have hDodd : Odd (Nat.card ↥(twoPoint H t)) :=
    Nat.not_even_iff_odd.mp (fun heven => hH.2 t htH (even_iff_two_dvd.mp heven))
  have hDleH : twoPoint H t ≤ H := inf_le_left
  -- Statement 2: `|K| = n`, proved above from Prop. 1 (a).
  have hKcard : (Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t).ncard =
      (Submission.Blueprint.involutions (H : Set G)).ncard :=
    ncard_Kset_eq_ncard_involutions' hH ht htH
  -- For every `u ∈ Inv(H)` the orbit `u^D` is all of `Inv(H)`: it is contained in `Inv(H)` and
  -- Peterfalvi's Lemma 1 makes it at least as large as `K`, hence of size `n = |Inv(H)|`.
  have horbit : ∀ u ∈ Submission.Blueprint.involutions (H : Set G),
      conjOrbit (Submission.Blueprint.twoPoint H t) u =
        Submission.Blueprint.involutions (H : Set G) := by
    intro u hu
    have hsub : conjOrbit (Submission.Blueprint.twoPoint H t) u ⊆
        Submission.Blueprint.involutions (H : Set G) := by
      rintro v ⟨x, hx, rfl⟩
      exact ⟨H.mul_mem (H.mul_mem (H.inv_mem (hDleH hx)) hu.1) (hDleH hx),
        by simpa [MulAut.conj_apply, hu.2] using
          MulEquiv.orderOf_eq (MulAut.conj x⁻¹) u⟩
    have hle : (Submission.Blueprint.involutions (H : Set G)).ncard ≤
        (conjOrbit (Submission.Blueprint.twoPoint H t) u).ncard := by
      rw [← hKcard]
      exact lemma1 hH hne hDleH hDodd hu ht htH
    exact Set.eq_of_subset_of_ncard_le hsub hle
  refine ⟨?_, hKcard, ?_⟩
  · -- Statement 1: transitivity of `D` on `Inv(H)`.
    intro u v hu hv
    have hv' : v ∈ conjOrbit (Submission.Blueprint.twoPoint H t) u := by
      rw [horbit u hu]; exact hv
    obtain ⟨d, hd, hdu⟩ := hv'
    exact ⟨d, hd, hdu⟩
  · -- Statement 3: the orbit of `u ∈ Inv(H)` has `n` elements.
    intro u hu
    rw [horbit u hu]

end Work.DoubleTransitivity.Sec2
