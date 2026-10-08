import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.lemma16_mod_two

namespace Work.BG

/-- Every element of `U` has odd order: `H₀` has `t` as its only involution
(`C.inv_H0`) and `t ∉ U` (`C.t_not_mem_U`), so no element of `U` can have
even order. -/
theorem orderOf_odd_of_mem_U {G : Type} [Group G] [Finite G] (C : Work.BG.Sec2Ctx G)
    {u : G} (hu : u ∈ C.P.U) : Odd (orderOf u) := by
  have huH0 : u ∈ C.P.H0 := C.P.U_le_H0 hu
  by_contra hcon
  rw [Nat.not_odd_iff_even] at hcon
  obtain ⟨k, hk⟩ := hcon
  -- `u^k` is an involution living in `U ≤ H₀`
  have hw2 : (u ^ k) ^ 2 = 1 := by
    rw [← pow_mul, Nat.mul_two, ← hk, pow_orderOf_eq_one]
  have hwne : u ^ k ≠ 1 := by
    intro h1
    have hdvd : orderOf u ∣ k := (orderOf_dvd_iff_pow_eq_one).mpr h1
    have hkpos : 0 < k := by
      by_contra hk0
      have hk0' : k = 0 := Nat.eq_zero_of_not_pos hk0
      have hpos := orderOf_pos u
      omega
    have hle : orderOf u ≤ k := Nat.le_of_dvd hkpos hdvd
    omega
  have hwU : u ^ k ∈ C.P.U := C.P.U.pow_mem hu k
  have hwH0 : u ^ k ∈ C.P.H0 := C.P.U_le_H0 hwU
  rcases C.inv_H0 _ hwH0 hw2 with h1 | h1
  · exact hwne h1
  · exact C.t_not_mem_U (by rw [← h1]; exact hwU)

/-- **Bender–Glauberman 1981, Lemma 1.6** for the §2 context: `t` is the involution of
`H₀`, `t` is central in `H ⊇ H₀ ⊇ U`, and `u ∈ U` has odd order; hence for every
`χ ∈ ℤ[Irr G]`, `χ(t·u) ≡ χ(u) (mod 2)`. -/
theorem s02_char16_t_mul {G : Type} [Group G] [Finite G] (C : Work.BG.Sec2Ctx G) {u : ↥C.P.H0}
    (hu : (u : G) ∈ C.P.U) (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ)
    (hχ : χ ∈ OddOrder.RepresentationTheory.ZIrr G) :
    Work.BG.AlgIntModTwo (χ ((C.t : G) * (u : G))) (χ (u : G)) := by
  have huH0 : (u : G) ∈ C.P.H0 := C.P.U_le_H0 hu
  -- `t` is an involution in `G`
  have ht : (C.t : G) * (C.t : G) = 1 := by
    have h : ((C.t : G)) ^ 2 = 1 := by
      simpa using congrArg (fun x : ↥C.P.H0 => (x : G)) C.t_sq
    simpa [pow_two] using h
  -- `t` commutes with `u`
  have hcomm : (C.t : G) * (u : G) = (u : G) * (C.t : G) :=
    (C.t_comm_H (u : G) (C.P.H0_le_H huH0)).symm
  -- `u ∈ U` has odd order
  have hodd : Odd (orderOf (u : G)) := orderOf_odd_of_mem_U C hu
  exact Work.BG.lemma16_mod_two (C.t : G) (u : G) ht hodd hcomm χ hχ

end Work.BG
