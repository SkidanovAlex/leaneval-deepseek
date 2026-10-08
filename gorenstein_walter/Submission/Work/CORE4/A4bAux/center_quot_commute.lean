import Mathlib

namespace Work.CORE4.A4bAux

theorem center_quot_commute {H : Type*} [Group H] [Finite H]
    (hZodd : Odd (Nat.card ↥(Subgroup.center H))) {s e : H} (hs : s * s = 1)
    (h : QuotientGroup.mk' (Subgroup.center H) e * QuotientGroup.mk' (Subgroup.center H) s =
         QuotientGroup.mk' (Subgroup.center H) s * QuotientGroup.mk' (Subgroup.center H) e) :
    e * s = s * e := by
  -- In the quotient H/Z, e and s commute.  Hence the commutator
  -- d = s e s⁻¹ e⁻¹ = (s e)(e s)⁻¹ lies in the center Z.
  have h1 : QuotientGroup.mk' (Subgroup.center H) (e * s) =
      QuotientGroup.mk' (Subgroup.center H) (s * e) := by
    rw [map_mul, map_mul]; exact h
  set d : H := s * e * s⁻¹ * e⁻¹ with hd_def
  have hd_eq : d = (s * e) * (e * s)⁻¹ := by rw [hd_def]; group
  have hd_ker : d ∈ (QuotientGroup.mk' (Subgroup.center H)).ker := by
    rw [MonoidHom.mem_ker, hd_eq, map_mul, map_inv, h1, mul_inv_cancel]
  have hdZ : d ∈ Subgroup.center H := by
    rw [← QuotientGroup.ker_mk' (Subgroup.center H)]
    exact hd_ker
  have hdc : ∀ g : H, g * d = d * g := fun g => (Subgroup.mem_center_iff.mp hdZ) g
  -- Since s e s⁻¹ = d e and d is central, conjugating by s gives d² e = e,
  -- while s (s e s⁻¹) s⁻¹ = e because s² = 1.  Hence d² = 1.
  have hde : s * e * s⁻¹ = d * e := by rw [hd_def]; group
  have hs_inv2 : s⁻¹ * s⁻¹ = 1 := by rw [← mul_inv_rev, hs, inv_one]
  have heq1 : s * (s * e * s⁻¹) * s⁻¹ = e := by
    have hA : s * (s * e * s⁻¹) * s⁻¹ = (s * s) * e * (s⁻¹ * s⁻¹) := by group
    rw [hA, hs, hs_inv2, one_mul, mul_one]
  have hconjd : s * d * s⁻¹ = d := by rw [hdc s]; group
  have hconj : s * (s * e * s⁻¹) * s⁻¹ = d * (d * e) := by
    calc s * (s * e * s⁻¹) * s⁻¹
        = s * (d * e) * s⁻¹ := by rw [hde]
      _ = (s * d * s⁻¹) * (s * e * s⁻¹) := by group
      _ = d * (d * e) := by rw [hconjd, hde]
  have hd2e : d * d * e = e := by
    have hh : d * (d * e) = e := by rw [← hconj, heq1]
    rw [← mul_assoc] at hh
    exact hh
  have hd2 : d ^ 2 = 1 := by
    rw [pow_two]
    exact mul_right_cancel (by rw [hd2e, one_mul])
  -- d lies in the center Z, so its order divides both 2 and the odd number
  -- |Z|; therefore d = 1.
  let z : ↥(Subgroup.center H) := ⟨d, hdZ⟩
  have hz2 : z ^ 2 = 1 := by
    rw [pow_two]
    exact Subtype.ext (by simpa [z, pow_two] using hd2)
  have hzo_dvd : orderOf z ∣ Nat.card ↥(Subgroup.center H) := orderOf_dvd_natCard z
  have hzo2 : orderOf z ∣ 2 := (orderOf_dvd_iff_pow_eq_one).mpr hz2
  have hcop : Nat.Coprime (orderOf z) (Nat.card ↥(Subgroup.center H)) :=
    Nat.Coprime.coprime_dvd_left hzo2 (Nat.coprime_two_left.mpr hZodd)
  have hzo1 : orderOf z = 1 := hcop.eq_one_of_dvd hzo_dvd
  have hz1 : z = 1 := orderOf_eq_one_iff.mp hzo1
  have hd1 : d = 1 := by
    have hh := congrArg (fun x : ↥(Subgroup.center H) => (x : H)) hz1
    simpa [z] using hh
  -- d = 1 means s e s⁻¹ = e, i.e. s e = e s.
  have hse : s * e * s⁻¹ = e := by rw [hde, hd1, one_mul]
  have hfin : s * e = e * s := by
    calc s * e = (s * e * s⁻¹) * s := by group
      _ = e * s := by rw [hse]
  exact hfin.symm

end Work.CORE4.A4bAux
