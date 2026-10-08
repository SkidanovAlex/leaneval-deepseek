import Mathlib
import Submission.Work.BG.S02
import Submission.Work.BG.s02_lamDual
import Submission.Work.BG.s02_lamDualCyclic
import Submission.Work.BG.s02_lamSign
import Submission.Work.BG.lamCF_fixed_eq_neg_one
import Submission.Work.BG.s02_lamOrbit_ne
import Submission.Work.BG.nCases
import Submission.Work.BG.rem31IndexUin
import Submission.Work.BG.rem31StabCard
import Submission.Work.GLUE.Defs

/-!
# Area BG: a `Λ`-character with value `-1` at `t`, not fixed by `s`

For a §2 context `C` compatible with the Bender–Glauberman data `D` and with `|S| = 2n ≥ 8`
(`4 ≤ D.n`), there is a linear character `β` of `H₀/U` whose inflation `λ_β = lamCF C β`
takes the value `-1` at the central involution `t` and is **not** fixed by the involution
`s = t₁` acting by `ν ↦ ν^s = sconj C ν`.

## Argument

`Λ = (H₀/U →* ℂˣ)` is a finite cyclic group (`s02_lamDualCyclic`), of order
`|Λ| = |H₀/U| = |H₀ : U| = n = D.n ≥ 4` (`rem31LamDualCard` + `rem31IndexUin`).  Let `β` be a
*generator* of `Λ`.  Then

* `β (tU) ≠ 1`: otherwise `β ∈ ker (lamEvt C)`, and since `β` generates `Λ` the whole kernel
  is `⊤`; but `tU ≠ 1` and `s02_lamSign` supplies a character with value `-1` at `tU`, so
  evaluation at `tU` is not trivial.  As `tU` is an involution, `β (tU)² = 1`, so
  `β (tU) = -1` and hence `lamCF C β C.t = -1` (`lamCF_apply_t`).
* `β² ≠ 1`: `β` generates `Λ`, so `orderOf β = |Λ| = D.n ≥ 4`, whereas `β² = 1` would force
  `orderOf β ∣ 2`.

Finally, BG Lemma 2.1(b) (`sconj_lamCF`) gives `(λ_β)^s = λ_{β⁻¹}`, and `β ↦ λ_β` is
injective (`lamCF_injective`); so `(λ_β)^s = λ_β` would force `β⁻¹ = β`, i.e. `β² = 1`.
Hence `sconj C (lamCF C β) ≠ lamCF C β`.
-/

set_option linter.style.haveILetI false

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16 in
theorem exists_lamCF_t_neg_one_sconj_ne {G : Type} [Group G] [Finite G]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (hC : Work.GW2.C16.Compat D C)
    (hn : 4 ≤ D.n) :
    ∃ β : Work.BG.quotGroup C.P →* ℂˣ,
      Work.BG.lamCF C β C.t = -1 ∧ Work.BG.sconj C (Work.BG.lamCF C β) ≠ Work.BG.lamCF C β := by
  classical
  -- `Λ = (H₀/U →* ℂˣ)` is finite cyclic; take a generator `β`.
  haveI hcyc : IsCyclic (lamDual C) := (s02_lamDualCyclic C).2
  obtain ⟨β, hβgen⟩ := IsCyclic.exists_generator (α := lamDual C)
  -- `|Λ| = |H₀ : U| = n = D.n ≥ 4`.
  have hcard : Nat.card (lamDual C) = D.n := by
    rw [rem31LamDualCard C, rem31IndexUin D C hC]
  -- A generator of a finite group has order the order of the group.
  have hord : orderOf β = Nat.card (lamDual C) := by
    have htop : Subgroup.zpowers β = ⊤ := by
      rw [Subgroup.eq_top_iff']; exact hβgen
    rw [← Nat.card_zpowers β, htop, Subgroup.card_top]
  -- Hence `β` has order `≥ 4`, in particular `β² ≠ 1`.
  have hβ2 : β ^ 2 ≠ 1 := by
    intro h2
    have hdvd : orderOf β ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]; exact h2
    have hle : orderOf β ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    rw [hord, hcard] at hle
    omega
  -- `β (tU) ≠ 1`: otherwise every character would vanish at `tU`.
  have hne : β (tU C) ≠ 1 := by
    intro h1
    obtain ⟨γ, hγ⟩ := s02_lamSign C
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hβgen γ)
    have hγ1 : γ (tU C) = 1 := by
      rw [← hk, MonoidHom.zpow_apply, h1]
      simp
    have hbad : ((-1 : ℂˣ) : ℂ) = 1 := by rw [← hγ, hγ1]; rfl
    norm_num at hbad
  -- `tU` is an involution, so `β (tU)² = 1` and `β (tU) = -1`.
  have hval : β (tU C) = -1 := by
    have hsq : β (tU C) ^ 2 = 1 := by rw [← map_pow, tU_sq, map_one]
    rcases units_sq_eq_one_eq_one_or_eq_neg_one (β (tU C)) hsq with h | h
    · exact absurd h hne
    · exact h
  refine ⟨β, ?_, ?_⟩
  · rw [lamCF_apply_t, hval]; norm_num
  · -- `(λ_β)^s = λ_{β⁻¹}` and `β ↦ λ_β` injective: `s`-fixedness would force `β² = 1`.
    intro hfix
    have h1 : β⁻¹ = β :=
      LamCFFixed.lamCF_injective C ((LamCFFixed.sconj_lamCF C β).symm.trans hfix)
    have h2 : β ^ 2 = 1 := by
      rw [pow_two]
      calc β * β = β⁻¹ * β := by rw [h1]
        _ = 1 := inv_mul_cancel β
    exact hβ2 h2

end Work.BG
