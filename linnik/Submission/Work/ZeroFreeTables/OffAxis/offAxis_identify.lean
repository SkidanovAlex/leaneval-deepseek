/-
# ZeroFreeTables/OffAxis — `offAxis_identify`

**OA6** of `OFFAXIS_ROUTE_LEAD.md` §3.2 (fact (B) at rectangle height `L`).

The off-axis assembly numbers the `λ₁`-minimiser at a *rectangle height* `L ≥ 50`
(`IsRectStrip L χ' ρ'`: minimiser over `|Im| ≤ L`, plus the zero-free strip `(L, 10L]`
coming from Jutila / HB Lemma 6.1), while the contract hands us the *frozen* wide
minimiser at height `50` (`LinnikContract2.IsMin1 χ₁ ρ₁`).  This lemma identifies the two
below the `λ₀` cut `0.695`: if `λ(ρ₁) < 0.695` and `ρ₁` is listed by the height-`L`
bookkeeping, then `ρ₁` is itself the minimiser at height `L`, i.e. `IsRectMin L χ₁ ρ₁`.

Proof (HB's "fact (B)").

* `ρ₁` is in the short region: `|Im ρ₁| ≤ 50 ≤ L` (from `IsMin1`) — so the membership
  clause of `IsRectMin L` is inherited.
* The strip minimality `hR.2.1` gives `λ(ρ') ≤ λ(ρ₁)`; assume strict inequality and derive
  a contradiction with the height-`L` bounds.  Since `λ` depends only on `Re`, both `ρ'`
  and `conj ρ'` then have `λ ≠ λ(ρ₁)`.
  - `χ₁ ∉ {χ', χ'⁻¹}`: `Lam2BoundH L χ' (0.701)` at `ρ₁` gives `λ₁ ≥ 0.701`.
  - `χ₁ = χ'`: `Lam0BoundH L χ' ρ' (0.695)` at `ρ₁` gives `λ₁ ≥ 0.695`
    (the exceptional-zero guard `χ'^2 = 1 → ρ₁ ≠ conj ρ'` holds because
    `λ(conj ρ') = λ(ρ') ≠ λ(ρ₁)`).
  - `χ₁ = χ'⁻¹`: `conj ρ₁` is a zero of `χ'` (`A7.zeroMult_conj_inv`), with the same
    height and `λ`; `Lam0BoundH L χ' ρ' (0.695)` at `conj ρ₁` gives `λ₁ ≥ 0.695`.
  Each of these contradicts `λ₁ < 0.695` (resp. `< 0.701`).  Hence `λ(ρ') = λ(ρ₁)`.
* Minimality over `|Im| ≤ 10L`: a zero `u` with `|Im u| ≤ L` has `λ(u) ≥ λ(ρ') = λ(ρ₁)`
  by `hR.2.1`, while `L < |Im u| ≤ 10L` puts `u` in the zero-free strip, `λ(u) > 2 > λ₁`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.Defs
import Submission.Work.A7.zeroMult_conj_inv
import Submission.Work.LinnikContract2.API

open DirichletCharacter Complex

namespace Work.ZeroFreeTables.OffAxis

open Work.LinnikContract

/-- `λ(ρ) = (1 - Re ρ) log q` depends only on `Re ρ`, so it is invariant under conjugation:
`λ(conj ρ) = λ(ρ)`.  This is what makes `ρ'` and `conj ρ'` interchangeable in the
identification argument. -/
theorem lamOf_conj (q : ℕ) (ρ : ℂ) : lamOf q (starRingEnd ℂ ρ) = lamOf q ρ := by
  simp [lamOf]

/-- **Fact (B) at height `L`.**  If `λ(ρ₁) < 0.695` and `ρ₁` is covered by the height-`L`
rectangle bookkeeping `IsRectStrip L χ' ρ'` (minimality over `|Im| ≤ L` plus the zero-free
strip `(L, 10L]`), then the frozen wide minimiser `ρ₁` is also the minimiser at height `L`:
`IsRectMin L χ₁ ρ₁`.

The two height-`L` inputs are the `λ₀` bound for `χ'` (`0.695`, excluding `ρ'` and `conj ρ'`)
and the `λ₂` bound for the characters other than `χ'^{±1}` (`0.701`); both exceed `0.695`,
so the strict inequality `λ(ρ') < λ(ρ₁) < 0.695` is refuted in every character case. -/
theorem offAxis_identify {q : ℕ} [NeZero q] {L : ℝ} (hL : 50 ≤ L)
    {χ₁ χ' : DirichletCharacter ℂ q} {ρ₁ ρ' : ℂ}
    (hm : Work.LinnikContract2.IsMin1 χ₁ ρ₁) (hR : Work.ZeroFreeTables.IsRectStrip L χ' ρ')
    (h0 : Work.ZeroFreeTables.Lam0BoundH L χ' ρ' (695/1000))
    (h2 : Work.ZeroFreeTables.Lam2BoundH L χ' (701/1000))
    (hlam : Work.LinnikContract.lamOf q ρ₁ < 695/1000) :
    Work.ZeroFreeTables.IsRectMin L χ₁ ρ₁ := by
  -- `ρ₁` lies in the short region `|Im| ≤ L`: `IsMin1` gives `|Im ρ₁| ≤ 50`.
  have hZ1 : IsZAt L χ₁ ρ₁ := ⟨hm.1.1, hm.1.2.1, hm.1.2.2.trans hL⟩
  -- The height-`L` minimiser `ρ'` has `λ(ρ') ≤ λ(ρ₁)`.
  have hle : lamOf q ρ' ≤ lamOf q ρ₁ := hR.2.1 χ₁ ρ₁ hZ1
  -- Identify the two `λ`'s.
  have hEq : lamOf q ρ' = lamOf q ρ₁ := by
    by_contra hne
    have hlt : lamOf q ρ' < lamOf q ρ₁ := lt_of_le_of_ne hle hne
    have hρ_ne : ρ₁ ≠ ρ' := fun h => hne (by rw [h])
    have hconj_ne : ρ₁ ≠ starRingEnd ℂ ρ' := by
      intro h
      exact hne (by rw [h, lamOf_conj])
    by_cases hχ : χ₁ = χ'
    · -- `χ₁ = χ'`: the `λ₀` bound at `ρ₁` forces `λ₁ ≥ 0.695`.
      have hZ : Work.ZeroFreeTables.IsZAt L χ' ρ₁ := hχ ▸ hZ1
      have hc := h0.2 ρ₁ hZ hρ_ne (fun _ => hconj_ne)
      linarith
    · by_cases hχ2 : χ₁ = χ'⁻¹
      · -- `χ₁ = χ'⁻¹`: `conj ρ₁` is a zero of `χ'` of the same height and `λ`.
        have hkey : zeroMult χ' (starRingEnd ℂ ρ₁) = zeroMult χ₁ ρ₁ := by
          have h1 := Work.A7.zeroMult_conj_inv (χ'⁻¹) ρ₁
          rw [inv_inv] at h1
          rw [h1, ← hχ2]
        have hmult : zeroMult χ' (starRingEnd ℂ ρ₁) ≠ 0 := by
          rw [hkey]; exact hm.1.2.1
        have hχ'1 : χ' ≠ 1 := by
          intro h
          exact hm.1.1 (by rw [hχ2, h, inv_one])
        have hZc : Work.ZeroFreeTables.IsZAt L χ' (starRingEnd ℂ ρ₁) :=
          ⟨hχ'1, hmult, by simpa using hZ1.2.2⟩
        have hne1 : starRingEnd ℂ ρ₁ ≠ ρ' := by
          intro h
          exact hne (by rw [← h, lamOf_conj])
        have hne2 : χ' ^ 2 = 1 → starRingEnd ℂ ρ₁ ≠ starRingEnd ℂ ρ' := by
          intro _
          exact fun h => hρ_ne (star_injective (by simpa [Complex.star_def] using h))
        have hc := h0.2 (starRingEnd ℂ ρ₁) hZc hne1 hne2
        rw [lamOf_conj] at hc
        linarith
      · -- `χ₁ ∉ {χ', χ'⁻¹}`: the `λ₂` bound at `ρ₁` forces `λ₁ ≥ 0.701`.
        have hc := h2 χ₁ ρ₁ hZ1 hχ hχ2
        linarith
  refine ⟨hZ1, ?_⟩
  intro χ u hu
  by_cases him : |u.im| ≤ L
  · -- inside the short region: use the height-`L` minimality of `ρ'`
    exact hEq ▸ hR.2.1 χ u ⟨hu.1, hu.2.1, him⟩
  · -- inside the strip `(L, 10L]`: `λ(u) > 2 > λ₁`
    have hs := hR.2.2 χ u hu (lt_of_not_ge him)
    rw [← hEq]
    linarith

end Work.ZeroFreeTables.OffAxis
