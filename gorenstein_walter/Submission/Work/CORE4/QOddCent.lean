import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.Defs19
import Submission.Work.CORE4.LayerFactsProper
import Submission.Work.CORE4.A7OrderThreeCentralizer
import Submission.Work.CORE4.QOddCentCard
import Submission.Work.CORE4.QOddCentMapCard
import Submission.Work.CORE4.QOddCentShapeCard

open scoped MatrixGroups

set_option linter.style.haveILetI false

namespace Work.CORE4

open Work.GW2

/-! ## General helpers used by the model leaf `QOddCent` -/

/-- If `V` has order `4` and `Z(Q)` has odd order, then `V ∩ Z(Q) = 1`: a subgroup of `V` has
order dividing `4`, a subgroup of `Z(Q)` has odd order, and the only odd divisor of `4` is `1`. -/
theorem qoc_inf_center_eq_bot {Q : Type*} [Group Q] (V : Subgroup Q)
    (hV4 : Nat.card V = 4) (hodd : Odd (Nat.card (Subgroup.center Q))) :
    V ⊓ Subgroup.center Q = ⊥ := by
  set d := Nat.card ↥(V ⊓ Subgroup.center Q) with hd
  have hdvd4 : d ∣ 4 := by
    have h := Subgroup.card_dvd_of_le (inf_le_left : V ⊓ Subgroup.center Q ≤ V)
    rwa [hV4] at h
  have hdvdodd : d ∣ Nat.card (Subgroup.center Q) := Subgroup.card_dvd_of_le inf_le_right
  have hodd' : Odd d := Odd.of_dvd_nat hodd hdvdodd
  have hcop : Nat.Coprime d 2 := hodd'.coprime_two_right
  have hdvd2 : d ∣ 2 :=
    hcop.dvd_of_dvd_mul_left (by rw [show (2 : ℕ) * 2 = 4 by norm_num]; exact hdvd4)
  exact (Subgroup.card_eq_one).mp (hcop.eq_one_of_dvd hdvd2)

/-- An element centralizing a subgroup has image centralizing the image subgroup. -/
theorem qoc_mem_centralizer_map {G H : Type*} [Group G] [Group H] (f : G →* H) {x : G}
    {K : Subgroup G} (hx : x ∈ Subgroup.centralizer (K : Set G)) :
    f x ∈ Subgroup.centralizer ((K.map f : Subgroup H) : Set H) := by
  rw [Subgroup.coe_map]
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  rintro y ⟨s, hs, rfl⟩
  rw [← map_mul, ← map_mul, hx s hs]

/-- A four-group meeting the kernel of `f` trivially maps onto a four-group. -/
theorem qoc_isFourGroup_map {G H : Type*} [Group G] [Group H] (f : G →* H) (K : Subgroup G)
    (h : K ⊓ f.ker = ⊥) (hK : IsFourGroup K) : IsFourGroup (K.map f) := by
  refine ⟨?_, ?_⟩
  · rw [QOddCentMapCard f K h, hK.1]
  · rintro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨k, hk, rfl⟩ := hy
    rw [← map_pow, hK.2 k hk, map_one]

/-- A multiplicative equivalence carries four-groups to four-groups. -/
theorem qoc_isFourGroup_mapEquiv {G H : Type*} [Group G] [Group H] (φ : G ≃* H)
    {V : Subgroup G} (hV : IsFourGroup V) : IsFourGroup (V.map φ.toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · rw [Subgroup.card_map_of_injective φ.injective]; exact hV.1
  · rintro _ ⟨v, hv, rfl⟩
    show φ.toMonoidHom v ^ 2 = 1
    rw [← map_pow, hV.2 v hv, map_one]

/-- **Design-19 model leaf `QOddCent`** (no §4 data): if `Q/Z(Q)` is `A₇` or `L₂(q)`, `|Z(Q)|` is
odd, `R ≤ Q` is quasisimple with `R/Z(R)` of the same shape, `V ≤ R` is a four-group and
`x ∈ C_Q(R)` with `x^m ∈ Z(Q)` for an odd `m`, then `x ∈ Z(Q)`.

Statement verbatim in `Defs19.lean` (`Work.GW2.C19.QOddCentProp`).

Route (bars = images in `Q̄ := Q/Z(Q)`; since `V ∩ Z(Q) = 1`, `V̄ ≅ V` is a four-group, and since
`x̄^m = 1` with `m` odd, `x̄` has odd order):
* `Q̄ ≅ L₂(q)`: `x̄ ∈ C(V̄) = V̄` (`I.toolkit.l2four`), a 2-group, so `x̄ = 1`;
* `Q̄ ≅ A₇`: `x̄ ∈ C(v̄)` for an involution `v̄ ∈ V̄`, so `|x̄| ∣ 3` (`I.toolkit.a7`: centralizer of
  an involution has order 24).  If `|x̄| = 3`, then `R̄ ≤ C(x̄)`, whose order is at most 36
  (`Work.CORE4.A7OrderThreeCentralizer`), so `|R̄| ≤ 36`; but `R/Z(R)` is a quotient of `R̄`
  (`R ∩ Z(Q) ≤ Z(R)`), so `|R/Z(R)| ≤ |R̄| ≤ 36`, contradicting `|R/Z(R)| ≥ 60`
  (`Work.CORE4.QOddCentShapeCard`).
GAP-checked in `_design_gw/gw19_qc.g` (A₇, 3·A₇, 3·A₆, `L₂(q)` for odd `q ≤ 31`). -/
theorem QOddCent (I : Work.GW2.C4Inputs) : Work.GW2.C19.QOddCentProp I := by
  intro Q _ _ hshape hodd R hQuasi hRshape V hVR hV4 x hxR hxm
  classical
  by_contra hxZ
  -- The quotient map `Q →* Q/Z(Q)`.
  let π : Q →* Q ⧸ Subgroup.center Q := QuotientGroup.mk' (Subgroup.center Q)
  have hπker : π.ker = Subgroup.center Q := QuotientGroup.ker_mk' _
  -- `x̄ ≠ 1` and `x̄` has odd order.
  have hxne : π x ≠ 1 := by
    intro h1
    refine hxZ ?_
    have h2 : (x : Q ⧸ Subgroup.center Q) = 1 := by
      rw [← QuotientGroup.mk'_apply (Subgroup.center Q) x]
      exact h1
    exact (QuotientGroup.eq_one_iff x).mp h2
  have hVbot : V ⊓ Subgroup.center Q = ⊥ := qoc_inf_center_eq_bot V hV4.1 hodd
  have hVbotπ : V ⊓ π.ker = ⊥ := by rw [hπker]; exact hVbot
  obtain ⟨m, hmodd, hmx⟩ := hxm
  have hmker : x ^ m ∈ π.ker := by rw [hπker]; exact hmx
  have hxq_odd : Odd (orderOf (π x)) := by
    refine Odd.of_dvd_nat hmodd (orderOf_dvd_iff_pow_eq_one.mpr ?_)
    rw [← map_pow]
    exact MonoidHom.mem_ker.mp hmker
  -- `x̄` centralizes the image of `R`.
  have hxq_centR :
      π x ∈ Subgroup.centralizer ((R.map π : Subgroup (Q ⧸ Subgroup.center Q)) : Set _) :=
    qoc_mem_centralizer_map π hxR
  rcases hshape with hA7 | ⟨p, k, hp, ho, h5, ⟨e⟩⟩
  · -- Case `Q̄ ≅ A₇`.
    obtain ⟨e⟩ := hA7
    -- An involution `v̄ ∈ V̄` and its image in `A₇`.
    have hVne : V ≠ ⊥ := by
      intro h
      have h1 : Nat.card V = 1 := (Subgroup.card_eq_one).mpr h
      rw [hV4.1] at h1
      exact absurd h1 (by norm_num)
    obtain ⟨v, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
    have hvq_ne : π (v : Q) ≠ 1 := by
      intro h1
      have hmem : (v : Q) ∈ π.ker := MonoidHom.mem_ker.mpr h1
      have h2 : (v : Q) ∈ V ⊓ π.ker := ⟨v.2, hmem⟩
      rw [hVbotπ] at h2
      exact hv1 (Subtype.ext (Subgroup.mem_bot.mp h2))
    have hvq_ord : orderOf (π (v : Q)) = 2 := by
      refine orderOf_eq_prime ?_ hvq_ne
      rw [← map_pow, hV4.2 (v : Q) v.2, map_one]
    have hv'_ord : orderOf (e (π (v : Q))) = 2 := by
      rw [MulEquiv.orderOf_eq e]; exact hvq_ord
    have h24 :
        Nat.card ↥(Subgroup.centralizer ({(e (π (v : Q)))} : Set (alternatingGroup (Fin 7)))) =
          24 :=
      I.toolkit.a7.2.2.1 _ hv'_ord
    have hcomm : π (v : Q) * π x = π x * π (v : Q) :=
      (Subgroup.mem_centralizer_iff.mp hxq_centR) (π (v : Q))
        (Subgroup.mem_map_of_mem π (hVR v.2))
    have hv'_cent :
        e (π x) ∈ Subgroup.centralizer ({(e (π (v : Q)))} : Set (alternatingGroup (Fin 7))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      show e (π (v : Q)) * e (π x) = e (π x) * e (π (v : Q))
      rw [← e.map_mul, ← e.map_mul, hcomm]
    -- `|x̄| ∣ 24`, and odd, so `|x̄| ∣ 3`.
    have hdvd24 : orderOf (π x) ∣ 24 := by
      have h := Subgroup.orderOf_dvd_natCard
        (Subgroup.centralizer ({(e (π (v : Q)))} : Set (alternatingGroup (Fin 7)))) hv'_cent
      rw [MulEquiv.orderOf_eq e, h24] at h
      exact h
    have hdvd3 : orderOf (π x) ∣ 3 := by
      have hcop : Nat.Coprime (orderOf (π x)) 8 := by
        simpa using (hxq_odd.coprime_two_right).pow_right 3
      exact hcop.dvd_of_dvd_mul_left (by rw [show (8 : ℕ) * 3 = 24 by norm_num]; exact hdvd24)
    have hord3 : orderOf (π x) = 3 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd3 with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hxne
      · exact h
    -- `R̄ ≤ C_{A₇}(x̄)`, of order at most 36.
    have hcent_le :
        Nat.card ↥(Subgroup.centralizer ({(e (π x))} : Set (alternatingGroup (Fin 7)))) ≤ 36 :=
      A7OrderThreeCentralizer (e (π x)) (by rw [MulEquiv.orderOf_eq e]; exact hord3)
    have hRq_le : (R.map π).map e.toMonoidHom ≤
        Subgroup.centralizer ({(e (π x))} : Set (alternatingGroup (Fin 7))) := by
      intro y hy
      rw [Subgroup.mem_map] at hy
      obtain ⟨z, hz, rfl⟩ := hy
      have hz' : z * π x = π x * z := (Subgroup.mem_centralizer_iff.mp hxq_centR) z hz
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      show e (π x) * e z = e z * e (π x)
      rw [← e.map_mul, ← e.map_mul]
      congr 1
      exact hz'.symm
    have hcardRq : Nat.card ↥(R.map π) ≤ 36 := by
      have h1 := Subgroup.card_le_of_le hRq_le
      have h2 : Nat.card ↥((R.map π).map e.toMonoidHom) = Nat.card ↥(R.map π) :=
        Subgroup.card_map_of_injective e.injective
      rw [h2] at h1
      exact le_trans h1 hcent_le
    -- `60 ≤ |R/Z(R)| ≤ |R̄| ≤ 36`.
    have h60 : 60 ≤ Nat.card (↥R ⧸ Subgroup.center ↥R) :=
      QOddCentShapeCard hRshape I.toolkit.a7.1
    have hle : Nat.card (↥R ⧸ Subgroup.center ↥R) ≤ Nat.card ↥(R.map π) := QOddCentCard R
    omega
  · -- Case `Q̄ ≅ L₂(q)`.
    haveI : Fact p.Prime := hp
    have hVq4 : IsFourGroup (V.map π) := qoc_isFourGroup_map π V hVbotπ hV4
    have hV4a : IsFourGroup ((V.map π).map e.toMonoidHom) := qoc_isFourGroup_mapEquiv e hVq4
    have hl2 := (I.toolkit.l2four p k ho h5).1
    have hcent : Subgroup.centralizer (((V.map π).map e.toMonoidHom :
          Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) : Set _) =
        (V.map π).map e.toMonoidHom := hl2 _ hV4a
    have hVmem :
        π x ∈ Subgroup.centralizer ((V.map π : Subgroup (Q ⧸ Subgroup.center Q)) : Set _) :=
      Subgroup.centralizer_le (Subgroup.map_mono hVR) hxq_centR
    have hx'cent : e (π x) ∈ Subgroup.centralizer (((V.map π).map e.toMonoidHom :
          Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) : Set _) :=
      qoc_mem_centralizer_map e.toMonoidHom hVmem
    have hx'mem : e (π x) ∈ (V.map π).map e.toMonoidHom := by
      rw [← hcent]; exact hx'cent
    -- `x̄ ∈ V̄` is a `2`-element of odd order, hence trivial.
    have hdvd4 : orderOf (e (π x)) ∣ 4 := by
      have h := Subgroup.orderOf_dvd_natCard ((V.map π).map e.toMonoidHom) hx'mem
      rwa [hV4a.1] at h
    have hodd' : Odd (orderOf (e (π x))) := by rw [MulEquiv.orderOf_eq e]; exact hxq_odd
    have hcop : Nat.Coprime (orderOf (e (π x))) 2 := hodd'.coprime_two_right
    have hdvd2 : orderOf (e (π x)) ∣ 2 :=
      hcop.dvd_of_dvd_mul_left (by rw [show (2 : ℕ) * 2 = 4 by norm_num]; exact hdvd4)
    have h1 : e (π x) = 1 := orderOf_eq_one_iff.mp (hcop.eq_one_of_dvd hdvd2)
    exact hxne (e.injective (by rw [h1, map_one]))

end Work.CORE4
