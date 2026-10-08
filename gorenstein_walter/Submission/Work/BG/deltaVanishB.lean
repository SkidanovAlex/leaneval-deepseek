import Mathlib
import Submission.Work.BG.Thm43Defs
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.s02_bsValueAtT
import Submission.Work.BG.H0Conj
import Submission.Work.BG.s02_char16_t_mul
import Submission.Work.BG.two_dvd_orderOf_of_isPGroup_quotient
import Submission.Work.BG.s02_quot_data

/-!
# Area BG: Bender–Glauberman 1981, Lemma 4.2 (a) — `δ_ν` vanishes on `B`

`Work.GW2.C23.DeltaVanishBProp D C` is Bender–Glauberman's Lemma 4.2 (a) (p. 212) in the
`|S| = 4` case: for `ν ∈ 𝒮'` and `b ∈ B = C_U(t₁) ∩ C_U(t₂)`, the virtual character
`δ_ν := (ν - λ₂ν)^G` (BG's `δ_ν = (ν - λ₂ν)*`, `Work.GW2.C16.delta`) takes the value `0`
at `b`.

The mathematics is the §2 remark that a difference of two `Λ`-equivalent characters of `H₀`
vanishes on `U`: here `ν` and `λ₂ν` have the same degree and `λ₂` is trivial on `U`
(`Lambda.apply_eq_one_of_mem_U`), so `θ := ν - λ₂ν` is supported in `T = H₀ ∖ U`. The
induction formula

  `Ind_{H₀}^G θ (g) = |H₀|⁻¹ ∑_{x ∈ G} θ̇ (x⁻¹ g x)`

then gives `0` at `g = b ∈ B ≤ U`: a non-zero summand needs `x⁻¹ b x ∈ T`, but conjugates
have equal order, `x⁻¹ b x ∈ H₀ ∖ U` has even order (`two_dvd_orderOf_of_isPGroup_quotient`
with `H₀/U` a 2-group), while `b ∈ U` has odd order (`orderOf_odd_of_mem_U`). Equivalently,
no `G`-conjugate of an element of `U` lies in `T`
(`Work.BG.conj_mem_U_of_mem_U`), so `b ∉ conjugatesIntoSet H₀ T`, and the support/induction
vanishing lemma `ClassFunction.induce_eq_zero_of_not_conjugatesIntoSet` applies.

Note that neither the hypothesis `ν ∈ 𝒮'` nor `D.n = 2` is used: the argument only needs
`θ` supported in `T` and `b ∈ U`, and works verbatim for arbitrary `ν ∈ Irr(H₀)`.
-/

namespace Work.BG

open OddOrder.RepresentationTheory

variable {G : Type} [Group G] [Finite G]

/-- A `G`-conjugate of an element of `U` that lies in `H₀` again lies in `U`.

Otherwise `x⁻¹ u x ∈ H₀ ∖ U` would be an element of `H₀` of even order, while it has the
same order as `u ∈ U`, which is odd (`orderOf_odd_of_mem_U`); evenness comes from `H₀/U`
being a `2`-group (`two_dvd_orderOf_of_isPGroup_quotient`). -/
theorem conj_mem_U_of_mem_U (C : Sec2Ctx G) {u : G} (hu : u ∈ C.P.U) (x : G)
    (hx : x⁻¹ * u * x ∈ C.P.H0) : x⁻¹ * u * x ∈ C.P.U := by
  by_contra hnot
  have hxN : (⟨x⁻¹ * u * x, hx⟩ : ↥C.P.H0) ∉ C.P.U.subgroupOf C.P.H0 := by
    rw [Subgroup.mem_subgroupOf]
    exact hnot
  have h2dvd : 2 ∣ orderOf (x⁻¹ * u * x) :=
    two_dvd_orderOf_of_isPGroup_quotient C.P.H0 C.P.U C.P.U_le_H0
      (quotGroup_isPGroup_two C) hx hxN
  have hconj : orderOf (x⁻¹ * u * x) = orderOf u := by
    have h := MulEquiv.orderOf_eq (MulAut.conj x⁻¹) u
    rwa [MulAut.conj_apply, inv_inv] at h
  have hodd : Odd (orderOf u) := orderOf_odd_of_mem_U C hu
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (hconj ▸ h2dvd))

/-- **Induction from `H₀` kills class functions supported in `T = H₀ ∖ U` at all of `U`.**  A
non-zero summand of the induction formula at `b ∈ U` would need a conjugate `x⁻¹ b x ∈ T`, but
conjugates of elements of `U` that lie in `H₀` lie in `U` (`conj_mem_U_of_mem_U`). -/
theorem induce_eq_zero_of_mem_U_of_support (C : Sec2Ctx G) [Fintype G]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥C.P.H0 : ℂ)]
    {θ : ClassFunction ↥C.P.H0 ℂ} (hθ : θ.support ⊆ {h : ↥C.P.H0 | (h : G) ∉ C.P.U})
    {b : G} (hb : b ∈ C.P.U) :
    ClassFunction.induce C.P.H0 θ b = 0 := by
  refine ClassFunction.induce_eq_zero_of_not_conjugatesIntoSet (H := C.P.H0)
    (A := {h : ↥C.P.H0 | (h : G) ∉ C.P.U}) hθ ?_
  rintro ⟨x, hx, hA⟩
  exact hA (conj_mem_U_of_mem_U C hb x hx)

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 Work.GW2.C23 in
theorem deltaVanishB {G : Type} [Group G] [Finite G] [Fintype G] [Invertible (Nat.card G : ℂ)]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) [Invertible (Nat.card ↥C.P.H0 : ℂ)] :
    Work.GW2.C23.DeltaVanishBProp D C := by
  intro hc hn β₂ hβ ν hνS b hb
  -- `b ∈ B ≤ U` (and `C.P.U = D.U` by compatibility)
  have hbU : b ∈ C.P.U := hc.U_eq.symm ▸ (inf_le_left.trans inf_le_left : D.B ≤ D.U) hb
  -- `δ_ν = Ind_{H₀}^G θ` with `θ := ν - λ₂ν`, supported in `T = H₀ ∖ U`
  show ClassFunction.induce C.P.H0 (ν - lamCF C β₂ * ν) b = 0
  refine induce_eq_zero_of_mem_U_of_support C ?_ hbU
  -- `λ₂` is trivial on `U`, hence `θ u = ν u - ν u = 0` for `u ∈ U`
  intro h hh
  rw [ClassFunction.mem_support] at hh
  by_contra hmem
  apply hh
  have h1 : lamCF C β₂ h = 1 :=
    Lambda.apply_eq_one_of_mem_U (P := C.P) (δ := lamCF C β₂) ⟨β₂, rfl⟩
      (Subgroup.mem_subgroupOf.mpr (not_not.mp hmem))
  simp only [ClassFunction.sub_apply, ClassFunction.mul_apply, h1, one_mul, sub_self]

end Work.BG
