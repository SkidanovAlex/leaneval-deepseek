import Mathlib
import Submission.Work.ThmF.ChV12.lemma4
import Submission.Work.ZassenhausTwoGroup.centralizer_le_H
import Submission.Work.ZassenhausTwoGroup.fpf_on_Q
import Submission.Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q
import Submission.Work.ThmF.ChV12.odd_card_centralizer_of_conj_ut
import Submission.Work.ThmF.ChV12.lemma2a_cent_split
import Submission.Work.ZassenhausSuzuki.QSZ_invH_le_centerQ
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausPSL2.ZData.t_conj_eq_inv
import Submission.Work.ThompsonFrobenius.Structure

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Suzuki 1962, Proposition 14 (HB XI, 11.4): the centraliser of a strongly real element

In a split rank-one Zassenhaus configuration `H = Q ⋊ D` with `Q` a `2`-group, let `z` be a
*strongly real* element (`z = a * b` with `a`, `b` involutions) with `z² ≠ 1`.  Then

* `C_G(z)` is abelian,
* `|C_G(z)|` is odd,
* every `z' ∈ C_G(z)`, `z' ≠ 1`, is again strongly real and `C_G(z') = C_G(z)`.

This is Suzuki, *On a class of doubly transitive groups*, Ann. of Math. 75 (1962), Proposition 14
(and Huppert–Blackburn XI, Lemma 11.4) for the Zassenhaus / Suzuki case of the Bender–Suzuki
theorem.

The proof follows Suzuki's.  By `exists_conj_eq_inv_mul_t` (Peterfalvi II Ch. V §2 Lemma 4)
`z` is conjugate to `u * t` for an involution `u ∈ H`; the oddness of `|C_G(z)|` is
`odd_card_centralizer_of_conj_ut` (Peterfalvi II Ch. V §2 Lemma 4).  Writing `z = g⁻¹ (u t) g`,
the involution `α = g⁻¹ u g` inverts `z` and normalises `A = C_G(z)`.  Since the centraliser of
an involution of `H` lies in the `2`-group `Q`, the fixed-point subgroup `C_A(α)` is a subgroup
both of a `2`-group and of the odd-order group `A`, hence trivial; Burnside's lemma
(`eq_inv_of_fpf_order_two`) then makes `α` invert all of `A`, so `A` is abelian.  The same
argument applies to any `z' ∈ A#`, and `C_G(z') ⊆ C_G(z)` follows from the abelianness of
`C_G(z')` and the fact that `z ∈ C_G(z')`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Submission.Blueprint

namespace Work.ZassenhausSuzuki

variable {G : Type} [Group G] [Finite G]

/-- In a split rank-one Zassenhaus configuration with `Q` a `2`-group, the involutions of `H`
commute pairwise (Peterfalvi II Ch. V §1 Prop. 1 (c), via `Inv(H) ⊆ Z(Q)`). -/
theorem invH_commute_z {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) (h2 : IsPGroup 2 Q) :
    ∀ u ∈ involutions (H : Set G), ∀ v ∈ involutions (H : Set G), u * v = v * u := by
  intro u hu v hv
  have hu' := Work.ThmF.mem_centerOf.mp (QSZ_invH_le_centerQ h h2 u hu)
  have hv' := Work.ThmF.mem_centerOf.mp (QSZ_invH_le_centerQ h h2 v hv)
  exact hu'.2 v hv'.1

/-- In a split rank-one Zassenhaus configuration with `Q` a `2`-group, the centraliser of an
involution `u ∈ H` is contained in `Q` (Suzuki's Proposition 1, in the form needed here). -/
theorem centralizer_le_Q_of_mem_involutions {H Q : Subgroup G} {t : G}
    (h : IsSplitRankOne H Q t) (hZ : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {u : G} (hu : u ∈ involutions (H : Set G)) :
    Subgroup.centralizer ({u} : Set G) ≤ Q := by
  have huQ : u ∈ Q := (Work.ThmF.mem_centerOf.mp (QSZ_invH_le_centerQ h h2 u hu)).1
  have hucen : ∀ w ∈ Q, u * w = w * u :=
    (Work.ThmF.mem_centerOf.mp (QSZ_invH_le_centerQ h h2 u hu)).2
  have hu_ne : u ≠ 1 := by
    intro h1
    have h2u : orderOf u = 2 := hu.2
    rw [h1, orderOf_one] at h2u
    exact absurd h2u (by norm_num)
  intro c hc
  have hcH : c ∈ H := Work.ZassenhausTwoGroup.centralizer_le_H h hZ huQ hu_ne hc
  obtain ⟨q, hq, d, hd, hcd⟩ := Work.ThmF.ChV12.decomp_exists h.normal h.sup_eq c hcH
  have hcu : c * u = u * c := Subgroup.mem_centralizer_singleton_iff.mp hc
  have hqcq : q⁻¹ * u * q = u := by
    rw [mul_assoc, hucen q hq, ← mul_assoc, inv_mul_cancel, one_mul]
  have hdu : d * u * d⁻¹ = u := by
    have h2' : q * d * u = u * (q * d) := by rw [← hcd]; exact hcu
    calc d * u * d⁻¹ = q⁻¹ * (q * d * u) * d⁻¹ := by group
      _ = q⁻¹ * (u * (q * d)) * d⁻¹ := by rw [h2']
      _ = q⁻¹ * u * q := by group
      _ = u := hqcq
  have hd1 : d = 1 := by
    by_contra hdne
    exact hu_ne (Work.ZassenhausTwoGroup.fpf_on_Q h hZ d hd hdne u huQ hdu)
  rw [hcd, hd1, mul_one]
  exact hq

/-- **Burnside's lemma, twisted form.**  If `α` is an involution inverting `w` and acting on the
centraliser `C_G(w)` with no non-trivial fixed point, then `α` inverts every element of `C_G(w)`
and `C_G(w)` is abelian. -/
theorem inv_of_involution_of_fpf {α w : G} (hα2 : α * α = 1) (hw : α * w * α⁻¹ = w⁻¹)
    (hfpf : ∀ y : G, y ∈ Subgroup.centralizer ({w} : Set G) → α * y * α⁻¹ = y → y = 1) :
    (∀ x ∈ Subgroup.centralizer ({w} : Set G), α * x * α⁻¹ = x⁻¹) ∧
      IsMulCommutative ↥(Subgroup.centralizer ({w} : Set G)) := by
  have hα_inv : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα2
  have haw : α * w = w⁻¹ * α := by
    calc α * w = (α * w * α⁻¹) * α := by group
      _ = w⁻¹ * α := by rw [hw]
  have haw' : α * w⁻¹ = w * α := by
    have h := congrArg Inv.inv hw
    have h1 : α * w⁻¹ * α⁻¹ = w := by simpa [mul_inv_rev, inv_inv, mul_assoc] using h
    calc α * w⁻¹ = (α * w⁻¹ * α⁻¹) * α := by group
      _ = w * α := by rw [h1]
  have hnorm : ∀ x ∈ Subgroup.centralizer ({w} : Set G),
      α * x * α⁻¹ ∈ Subgroup.centralizer ({w} : Set G) := by
    intro x hx
    have hxcomm : x * w = w * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    have hx' : x * w⁻¹ = w⁻¹ * x := by
      have h := congrArg (fun z => w⁻¹ * z * w⁻¹) hxcomm
      simpa [mul_assoc] using h.symm
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc (α * x * α⁻¹) * w = α * (x * (α⁻¹ * w)) := by group
      _ = α * (x * (w⁻¹ * α)) := by rw [hα_inv, haw]
      _ = α * ((x * w⁻¹) * α) := by group
      _ = α * ((w⁻¹ * x) * α) := by rw [hx']
      _ = (α * w⁻¹) * (x * α) := by group
      _ = (w * α) * (x * α) := by rw [haw']
      _ = w * (α * x * α) := by group
      _ = w * (α * x * α⁻¹) := by rw [hα_inv]
  let φhom : ↥(Subgroup.centralizer ({w} : Set G)) →*
      ↥(Subgroup.centralizer ({w} : Set G)) :=
    { toFun := fun x => ⟨α * (x : G) * α⁻¹, hnorm x x.2⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x y; ext
        show α * ((x : G) * (y : G)) * α⁻¹
          = (α * (x : G) * α⁻¹) * (α * (y : G) * α⁻¹)
        group }
  have hφ2 : ∀ x, φhom (φhom x) = x := by
    intro x; ext
    show α * (α * (x : G) * α⁻¹) * α⁻¹ = (x : G)
    calc α * (α * (x : G) * α⁻¹) * α⁻¹ = (α * α) * (x : G) * (α⁻¹ * α⁻¹) := by group
      _ = (x : G) := by rw [hα2, hα_inv, hα2]; group
  have hφfpf : ∀ x, φhom x = x → x = 1 := by
    intro x hx
    have hval : α * (x : G) * α⁻¹ = (x : G) := by
      have := congrArg Subtype.val hx
      simpa [φhom] using this
    exact Subtype.ext (hfpf (x : G) x.2 hval)
  have key := Work.ZassenhausPSL2.ZData.eq_inv_of_fpf_order_two φhom hφ2 hφfpf
  have hinv : ∀ x ∈ Subgroup.centralizer ({w} : Set G), α * x * α⁻¹ = x⁻¹ := by
    intro x hx
    have := congrArg Subtype.val (key ⟨x, hx⟩)
    simpa [φhom] using this
  refine ⟨hinv, IsMulCommutative.of_comm (fun a b => ?_)⟩
  have ha : α * (a : G) * α⁻¹ = (a : G)⁻¹ := hinv (a : G) a.2
  have hb : α * (b : G) * α⁻¹ = (b : G)⁻¹ := hinv (b : G) b.2
  have h1 : α * ((a : G) * (b : G)) * α⁻¹ = (a : G)⁻¹ * (b : G)⁻¹ := by
    calc α * ((a : G) * (b : G)) * α⁻¹
        = (α * (a : G) * α⁻¹) * (α * (b : G) * α⁻¹) := by group
      _ = (a : G)⁻¹ * (b : G)⁻¹ := by rw [ha, hb]
  have hab := hinv ((a : G) * (b : G)) ((Subgroup.centralizer ({w} : Set G)).mul_mem a.2 b.2)
  have h2 : (a : G)⁻¹ * (b : G)⁻¹ = (b : G)⁻¹ * (a : G)⁻¹ := by
    rw [← h1, hab, mul_inv_rev]
  exact Subtype.ext (by
    have h3 := congrArg Inv.inv h2
    have h4 : (b : G) * (a : G) = (a : G) * (b : G) := by
      simpa [mul_inv_rev, inv_inv] using h3
    exact h4.symm)

theorem centralizer_abelian_of_strongly_real {G : Type} [Group G] [Finite G] {H Q : Subgroup G}
    {t : G} (h : Submission.Blueprint.IsSplitRankOne H Q t)
    (hZ : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {z : G} (hz2 : z * z ≠ 1) (hsr : ∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = z) :
    IsMulCommutative ↥(Subgroup.centralizer ({z} : Set G)) ∧
      Odd (Nat.card ↥(Subgroup.centralizer ({z} : Set G))) ∧
      (∀ z' ∈ Subgroup.centralizer ({z} : Set G), z' ≠ 1 →
        (∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = z') ∧
          Subgroup.centralizer ({z'} : Set G) = Subgroup.centralizer ({z} : Set G)) := by
  have hcommH : ∀ u ∈ involutions (H : Set G), ∀ v ∈ involutions (H : Set G), u * v = v * u :=
    invH_commute_z h h2
  have hcomm := Work.ThmF.ChV12.involution_commute_conj (G := G) hcommH
  -- oddness of `C_G(w)` for any strongly real `w` with `w² ≠ 1`
  have hodd_sr : ∀ w : G, w * w ≠ 1 →
      (∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = w) →
      Odd (Nat.card ↥(Subgroup.centralizer ({w} : Set G))) := by
    intro w hw2 hwsr
    obtain ⟨u', hu'Q0, hu'1, g', hg'⟩ :=
      Work.ThmF.ChV12.exists_conj_eq_inv_mul_t (G := G) h.stronglyEmbedded h.twoTransitive
        h.invol h.not_mem hcomm hw2 hwsr
    have hu'inv : u' ∈ involutions (H : Set G) := by
      rcases Work.ThmF.mem_Q0_iff.mp hu'Q0 with ⟨h1, h2'⟩ | h1
      · exact ⟨h1, h2'⟩
      · exact absurd h1 hu'1
    exact Work.ThmF.ChV12.odd_card_centralizer_of_conj_ut h.stronglyEmbedded h.invol h.not_mem
      hu'inv hw2 ⟨g', hg'⟩
  have hodd_z : Odd (Nat.card ↥(Subgroup.centralizer ({z} : Set G))) := hodd_sr z hz2 hsr
  obtain ⟨u, huQ0, hu1, g, hg⟩ :=
    Work.ThmF.ChV12.exists_conj_eq_inv_mul_t (G := G) h.stronglyEmbedded h.twoTransitive
      h.invol h.not_mem hcomm hz2 hsr
  have hu_inv : u ∈ involutions (H : Set G) := by
    rcases Work.ThmF.mem_Q0_iff.mp huQ0 with ⟨h1, h2'⟩ | h1
    · exact ⟨h1, h2'⟩
    · exact absurd h1 hu1
  have hu_sq : u * u = 1 := by
    have hpu := pow_orderOf_eq_one u
    rw [hu_inv.2, pow_two] at hpu
    exact hpu
  have ht_sq : t * t = 1 := by
    have hpt := pow_orderOf_eq_one t
    rw [h.invol, pow_two] at hpt
    exact hpt
  set α : G := g⁻¹ * u * g with hα
  have hα_sq : α * α = 1 := by
    rw [hα]
    calc (g⁻¹ * u * g) * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g := by group
      _ = 1 := by rw [hu_sq]; group
  have hα_inv : α⁻¹ = α := inv_eq_of_mul_eq_one_right hα_sq
  have hαz : α * z * α⁻¹ = z⁻¹ := by
    rw [hα]
    calc (g⁻¹ * u * g) * z * (g⁻¹ * u * g)⁻¹
        = g⁻¹ * (u * (g * z * g⁻¹) * u⁻¹) * g := by group
      _ = g⁻¹ * (u * (u * t) * u⁻¹) * g := by rw [hg]
      _ = g⁻¹ * (u * t)⁻¹ * g := by
            rw [show u * (u * t) * u⁻¹ = (u * t)⁻¹ from by
              rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hu_sq,
                inv_eq_of_mul_eq_one_right ht_sq]
              calc u * (u * t) * u = (u * u) * t * u := by group
                _ = t * u := by rw [hu_sq, one_mul]]
      _ = (g⁻¹ * (u * t) * g)⁻¹ := by group
      _ = (g⁻¹ * (g * z * g⁻¹) * g)⁻¹ := by rw [← hg]
      _ = z⁻¹ := by group
  -- fixed-point-freeness of conjugation by `α` on `C_G(w)` when `|C_G(w)|` is odd
  have hfpf : ∀ w : G, Odd (Nat.card ↥(Subgroup.centralizer ({w} : Set G))) →
      ∀ y : G, y ∈ Subgroup.centralizer ({w} : Set G) → α * y * α⁻¹ = y → y = 1 := by
    intro w hoddw y hy hyfix
    have hyα : α * y = y * α := by
      calc α * y = (α * y * α⁻¹) * α := by group
        _ = y * α := by rw [hyfix]
    have h1 : y * (g⁻¹ * u * g) = (g⁻¹ * u * g) * y := by
      have h' := hyα.symm
      rw [hα] at h'
      exact h'
    have hgyu : (g * y * g⁻¹) * u = u * (g * y * g⁻¹) := by
      calc (g * y * g⁻¹) * u = g * (y * (g⁻¹ * u * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * u * g) * y) * g⁻¹ := by rw [h1]
        _ = u * (g * y * g⁻¹) := by group
    have hgyQ : g * y * g⁻¹ ∈ Q :=
      centralizer_le_Q_of_mem_involutions h hZ h2 hu_inv
        (Subgroup.mem_centralizer_singleton_iff.mpr hgyu)
    obtain ⟨e, he⟩ := h2.exists_card_eq
    have hdvdQ : orderOf y ∣ 2 ^ e := by
      have hord : orderOf (g * y * g⁻¹) = orderOf y := by
        rw [show g * y * g⁻¹ = MulAut.conj g y from by rw [MulAut.conj_apply]]
        exact MulEquiv.orderOf_eq (MulAut.conj g) y
      have hdvd := Subgroup.orderOf_dvd_natCard Q hgyQ
      rw [he, hord] at hdvd
      exact hdvd
    have hdvdW : orderOf y ∣ Nat.card ↥(Subgroup.centralizer ({w} : Set G)) :=
      Subgroup.orderOf_dvd_natCard _ hy
    have hoddy : Odd (orderOf y) := hoddw.of_dvd_nat hdvdW
    have hcop : Nat.Coprime (orderOf y) (2 ^ e) :=
      Nat.Coprime.pow_right e (Odd.coprime_two_right hoddy)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl hdvdQ)
  have hzinv : ∀ x ∈ Subgroup.centralizer ({z} : Set G), α * x * α⁻¹ = x⁻¹ :=
    (inv_of_involution_of_fpf hα_sq hαz (hfpf z hodd_z)).1
  have hzabel : IsMulCommutative ↥(Subgroup.centralizer ({z} : Set G)) :=
    (inv_of_involution_of_fpf hα_sq hαz (hfpf z hodd_z)).2
  have hzA : z ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  refine ⟨hzabel, hodd_z, ?_⟩
  intro z' hz' hz'ne
  have hodd_z'_ord : Odd (orderOf z') :=
    hodd_z.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hz')
  have hz'2 : z' * z' ≠ 1 := by
    intro hsq
    have hdvd : orderOf z' ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]; simpa [pow_two] using hsq
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2'
    · exact hz'ne (orderOf_eq_one_iff.mp h1)
    · rw [h2'] at hodd_z'_ord
      exact absurd hodd_z'_ord (by rw [Nat.not_odd_iff_even]; exact even_two)
  have hz'sr : ∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = z' := by
    refine ⟨α, α * z', hα_sq, ?_, ?_⟩
    · have h1 : α * z' * α = z'⁻¹ := by
        have hh := hzinv z' hz'
        rwa [hα_inv] at hh
      calc (α * z') * (α * z') = (α * z' * α) * z' := by group
        _ = z'⁻¹ * z' := by rw [h1]
        _ = 1 := by group
    · calc α * (α * z') = (α * α) * z' := by group
        _ = z' := by rw [hα_sq, one_mul]
  have hodd_z' : Odd (Nat.card ↥(Subgroup.centralizer ({z'} : Set G))) := hodd_sr z' hz'2 hz'sr
  have hαz' : α * z' * α⁻¹ = z'⁻¹ := hzinv z' hz'
  have hz'abel : IsMulCommutative ↥(Subgroup.centralizer ({z'} : Set G)) :=
    (inv_of_involution_of_fpf hα_sq hαz' (hfpf z' hodd_z')).2
  have hzC : z ∈ Subgroup.centralizer ({z'} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val
      (mul_comm' (M := ↥(Subgroup.centralizer ({z} : Set G))) ⟨z', hz'⟩ ⟨z, hzA⟩)).symm
  have hle1 : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer ({z'} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val
      (mul_comm' (M := ↥(Subgroup.centralizer ({z} : Set G))) ⟨z', hz'⟩ ⟨x, hx⟩)).symm
  have hle2 : Subgroup.centralizer ({z'} : Set G) ≤ Subgroup.centralizer ({z} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (congrArg Subtype.val
      (mul_comm' (M := ↥(Subgroup.centralizer ({z'} : Set G))) ⟨z, hzC⟩ ⟨x, hx⟩)).symm
  exact ⟨hz'sr, le_antisymm hle2 hle1⟩

end Work.ZassenhausSuzuki
