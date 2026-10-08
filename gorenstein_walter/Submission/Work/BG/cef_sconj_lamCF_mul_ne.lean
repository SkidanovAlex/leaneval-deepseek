import Mathlib
import Submission.Work.BG.ThmABCCharDefs
import Submission.Work.BG.S02
import Submission.Work.BG.c3Identity
import Submission.Work.BG.lamCF_fixed_eq_neg_one
import Submission.Work.BG.c3TUIsSquare
import Submission.Work.BG.sconjLam
import Submission.Work.BG.s02_lamDual

namespace Work.BG

open OddOrder.RepresentationTheory Work.GW2 Work.BG Work.GW2.C16

variable {G : Type} [Group G] [Finite G]

/-- **Cancellation of the `Λ`-action on `κ`.**  If `κ` is trivial on `S₀ = D.S0` then
`λ_γ κ = λ_{γ'} κ` forces `γ = γ'`: evaluating on the elements of `S₀` (where `κ = 1`) shows
`λ_γ = λ_{γ'}` on `S₀`, and since `H₀/U` is the image of `S₀` (as `H₀ = U · S₀`) while all
`λ` are trivial on `U`, this gives `γ = γ'`.

Public copy of the `private` lemma of `Submission/Work/BG/c3Identity.lean`. -/
theorem cef_lamCF_mul_cancel (D : BGData G)
    (C : Sec2Ctx G) (hcompat : Compat D C) (κ : ClassFunction ↥C.P.H0 ℂ)
    (hκS0 : ∀ h : ↥C.P.H0, (h : G) ∈ D.S0 → κ h = 1)
    {γ γ' : quotGroup C.P →* ℂˣ} (h : lamCF C γ * κ = lamCF C γ' * κ) : γ = γ' := by
  -- the values of `λ_γ` and `λ_{γ'}` agree on `S₀`
  have hval' : ∀ s : ↥C.P.H0, (s : G) ∈ D.S0 → γ (quotMk C.P s) = γ' (quotMk C.P s) := by
    intro s hs
    have h' := congrArg (fun φ : ClassFunction ↥C.P.H0 ℂ => φ s) h
    simp only [ClassFunction.mul_apply] at h'
    rw [hκS0 s hs] at h'
    rw [lamCF_apply, lamCF_apply] at h'
    exact Units.ext (by simpa using h')
  -- conclude on all of `H₀/U`, using `H₀ = U · S₀`
  refine MonoidHom.ext fun z => ?_
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (C.P.U.subgroupOf C.P.H0) z
  obtain ⟨u, hu, s, hs, hus⟩ := LamCFFixed.H0_decomp D C hcompat x
  have hu1 : quotMk C.P u = 1 :=
    (QuotientGroup.eq_one_iff (N := C.P.U.subgroupOf C.P.H0) u).mpr hu
  have hπ : quotMk C.P x = quotMk C.P s := by rw [← hus, map_mul, hu1, one_mul]
  calc γ (quotMk C.P x) = γ (quotMk C.P s) := by rw [hπ]
    _ = γ' (quotMk C.P s) := hval' s hs
    _ = γ' (quotMk C.P x) := by rw [hπ]

/-- `κ₃ := λ_β κ` is not `s`-fixed, for an admissible linear `κ` (trivial on `S₀`, `s`-fixed)
and `β` with `λ_β(t) = -1`, provided `4 ≤ D.n`.  This is `Work.BG.sconj_lamCF_mul_ne` of
`Submission/Work/BG/c3Identity.lean` (there `private`), needed publicly here; the proof uses the
cancellation `λ_γ κ = λ_{γ'} κ → γ = γ'` (also private there, on `κ = 1` on `S₀` and
`H₀ = U·S₀`) and `Work.BG.c3TUIsSquare` (`tU` is a square in the cyclic `2`-group `H₀/U` of
order `4 ≤ D.n`). -/
theorem cef_sconj_lamCF_mul_ne {G : Type} [Group G] [Finite G]
    (D : Work.GW2.BGData G) (C : Work.BG.Sec2Ctx G) (hComp : Work.GW2.C16.Compat D C)
    (hn : 4 ≤ D.n) (κ : OddOrder.RepresentationTheory.ClassFunction ↥C.P.H0 ℂ)
    (hκS0 : ∀ h : ↥C.P.H0, (h : G) ∈ D.S0 → κ h = 1)
    (hκsconj : Work.BG.sconj C κ = κ)
    (β : Work.BG.quotGroup C.P →* ℂˣ) (hβt : Work.BG.lamCF C β C.t = -1) :
    Work.BG.sconj C (Work.BG.lamCF C β * κ) ≠ Work.BG.lamCF C β * κ := by
  intro hfix
  have hA : sconj C (lamCF C β * κ) = lamCF C β⁻¹ * κ := by
    rw [sconjLam C β κ, hκsconj]
  have h1 : lamCF C β⁻¹ * κ = lamCF C β * κ := by rw [← hA]; exact hfix
  have h2 : β⁻¹ = β := cef_lamCF_mul_cancel D C hComp κ hκS0 h1
  have h3 : β * β = 1 := by
    calc β * β = β⁻¹ * β := by rw [h2]
      _ = 1 := inv_mul_cancel β
  obtain ⟨x, hx⟩ := c3TUIsSquare D C hComp hn
  have h4 : β (tU C) = 1 := by
    have h' : β x * β x = 1 := by
      have hh := congrArg (fun f : quotGroup C.P →* ℂˣ => f x) h3
      simpa [MonoidHom.mul_apply] using hh
    have h5 : tU C = x * x := by rw [← hx, pow_two]
    rw [h5, map_mul]
    exact h'
  have h6 : ((β (tU C) : ℂˣ) : ℂ) = 1 := by rw [h4]; rfl
  rw [lamCF_apply_t] at hβt
  rw [h6] at hβt
  norm_num at hβt

end Work.BG
