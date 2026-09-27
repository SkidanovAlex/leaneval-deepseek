import Mathlib
import Submission.Work.EKLC6Core.InjRadius
import Submission.Work.EKLC6Core.smul_conj_mem_V
import Submission.Work.EKLC6Core.injCap_smul_arith

/-!
# `Work.EKLC6Core.injCap_smul_le` — the capped injectivity radius is stable under small moves

`injCap x = min (injS x) (1/2)` is the capped injectivity radius of `x ∈ X₃ = SL₃(ℝ)/SL₃(ℤ)`:
the supremal `ρ` such that the orbit map `v ↦ v • x` is injective on the entrywise displacement
neighbourhood `V ρ = {v : SL₃(ℝ) | |v i j - 1 i j| < ρ}`.

`Work.EKLC6Core.injCap_mem_V_le` gives the *lower* semicontinuity,

    `injCap x / 16 ≤ injCap (w • x)`  for `w ∈ V a`, `a ≤ injCap x / 8`,

which is what makes the "good balls" around a countable dense set cover `X₃`.  The present file
proves the matching *upper* bound, so that `injCap` is comparable (within a factor `4`) along a
small move:

    `injCap (w • x) ≤ 4 * injCap x`.

## The argument

Write `I = injCap x`.  If `1/8 ≤ I` then `4 I ≥ 1/2 ≥ injCap (w • x)` is trivial because `injCap`
is capped at `1/2`.  So assume `I < 1/8`; then `injCap x = injS x = I`.

*Injectivity transfers backwards* under the conjugation by `w`: if `v₁, v₂ ∈ V ρ'` satisfy
`v₁ • x = v₂ • x`, then `(w vᵢ w⁻¹) • (w • x) = w • (vᵢ • x)` for `i = 1, 2`, so injectivity of
`V ρ` at `w • x` forces `v₁ = v₂` as soon as `w · V ρ' · w⁻¹ ⊆ V ρ`.  The entrywise estimate
`Work.EKLC6Core.smul_conj_mem_V` (two applications of `V s · V t ⊆ V (s + t + 3 s t)` together
with `w⁻¹ ∈ V (10 a)`) gives

    `v ∈ V ρ'  ⟹  w v w⁻¹ ∈ V (ρ' (1 + 33 a + 90 a²) + (11 a + 30 a²))`,

hence `InjAt (w • x) ρ  ⟹  InjAt x ((ρ - (11a + 30a²))/(1 + 33a + 90a²))`
(`InjAt.smul_conj_transfer`).

Now suppose `4 I < injS (w • x)`.  Pick `ρ` with `4I < ρ < min (injS (w • x)) 1`; then `V ρ` acts
injectively at `w • x`, so `V ρ'` acts injectively at `x` for
`ρ' = (ρ - (11a + 30a²))/(1 + 33a + 90a²) ≤ 1`.  Since `a ≤ I/8` and `I < 1/8`, the elementary
estimate `Work.EKLC6Core.injCap_smul_arith` gives

    `(1 + 33 a + 90 a²) I + (11 a + 30 a²) < 4 I`,

so `ρ > 4I` implies `ρ' > I`.  But a capped radius at which the orbit map of `x` is injective is
at most `injS x = I` — a contradiction.  Hence `injS (w • x) ≤ 4 I`, and
`injCap (w • x) ≤ injS (w • x)` finishes.
-/

namespace Work.EKLC6Core

open Work.EKLContract

noncomputable section

/-! ## Auxiliary estimate -/

/-- A *capped* radius at which the orbit map of `x` is injective is at most `injS x`. -/
private theorem le_injS_of_injAt {x : X3} {γ : ℝ} (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (h : InjAt x γ) : γ ≤ injS x :=
  le_csSup (injSet_bddAbove x) ⟨hγ, hγ1, h⟩

/-! ## The backward transfer of injectivity -/

/-- **Injectivity of the orbit map transfers backwards under conjugation.**  If `V ρ` acts
injectively at `w • x` and `w ∈ V a`, then `V ρ'` acts injectively at `x` as soon as
`ρ' (1 + 33 a + 90 a²) + (11 a + 30 a²) ≤ ρ`.

Indeed `v₁ • x = v₂ • x` gives `w vᵢ w⁻¹ • (w • x) = w • (vᵢ • x)`, and `vᵢ ∈ V ρ'` makes
`w vᵢ w⁻¹ ∈ V ρ` by `Work.EKLC6Core.smul_conj_mem_V`; injectivity at `w • x` then yields
`w v₁ w⁻¹ = w v₂ w⁻¹`, whence `v₁ = v₂`. -/
theorem InjAt.smul_conj_transfer {x : X3} {a ρ ρ' : ℝ} {w : SL3}
    (h : InjAt (w • x) ρ) (hw : w ∈ V a) (ha : 0 < a) (ha1 : a ≤ 1 / 2) (hρ' : 0 ≤ ρ')
    (hineq : ρ' * (1 + 33 * a + 90 * a ^ 2) + (11 * a + 30 * a ^ 2) ≤ ρ) : InjAt x ρ' := by
  intro v₁ v₂ h₁ h₂ hxy
  have hmem : ∀ v : SL3, v ∈ V ρ' → w * v * w⁻¹ ∈ V ρ := fun v hv =>
    Work.Misiurewicz.V_mono hineq (smul_conj_mem_V ha ha1 hρ' hw hv)
  have hkey : ∀ v : SL3, (w * v * w⁻¹) • (w • x) = w • (v • x) := by
    intro v
    rw [mul_smul, inv_smul_smul, mul_smul]
  have hu : (w * v₁ * w⁻¹) • (w • x) = (w * v₂ * w⁻¹) • (w • x) := by
    rw [hkey v₁, hkey v₂, hxy]
  have hconj : w * v₁ * w⁻¹ = w * v₂ * w⁻¹ := h _ _ (hmem v₁ h₁) (hmem v₂ h₂) hu
  have hc := congrArg (fun t : SL3 => w⁻¹ * t * w) hconj
  simpa [mul_assoc] using hc

/-! ## The main estimate -/

theorem injCap_smul_le {x : Work.EKLContract.X3} {a : ℝ} (ha : 0 < a) (ha2 : a ≤ 1 / 2)
    (ha8 : a ≤ Work.EKLC6Core.injCap x / 8) {w : Work.EKLContract.SL3}
    (hw : w ∈ Work.EKLContract.V a) :
    Work.EKLC6Core.injCap (w • x) ≤ 4 * Work.EKLC6Core.injCap x := by
  by_cases hsmall : injCap x < 1 / 8
  · -- small case: `injS x = injCap x`, and `injS (w • x) ≤ 4 injCap x`
    have hIpos : 0 < injCap x := injCap_pos x
    have hinjS_le : injS x ≤ 1 / 2 := by
      by_contra hcon
      have hmin : injCap x = 1 / 2 := by
        rw [injCap, min_eq_right (le_of_lt (not_le.mp hcon))]
      linarith
    have hinjS_eq : injS x = injCap x := by rw [injCap, min_eq_left hinjS_le]
    have harith : (1 + 33 * a + 90 * a ^ 2) * injCap x + (11 * a + 30 * a ^ 2)
        < 4 * injCap x := injCap_smul_arith hIpos hsmall ha ha8
    have hcpos : 0 < 1 + 33 * a + 90 * a ^ 2 := by positivity
    have hcone : 1 ≤ 1 + 33 * a + 90 * a ^ 2 := by nlinarith [ha]
    have hepos : 0 ≤ 11 * a + 30 * a ^ 2 := by positivity
    have hS : injS (w • x) ≤ 4 * injCap x := by
      by_contra hcon
      rw [not_le] at hcon
      have h4I1 : 4 * injCap x < 1 := by linarith
      have h4Imin : 4 * injCap x < min (injS (w • x)) 1 := lt_min hcon h4I1
      set ρ : ℝ := (4 * injCap x + min (injS (w • x)) 1) / 2 with hρdef
      have hρgt : 4 * injCap x < ρ := by rw [hρdef]; linarith
      have hρlt : ρ < injS (w • x) := by
        rw [hρdef]; linarith [min_le_left (injS (w • x)) 1]
      have hρle1 : ρ ≤ 1 := by
        rw [hρdef]; linarith [min_le_right (injS (w • x)) 1]
      have hρpos : 0 < ρ := by linarith
      have hInj : InjAt (w • x) ρ := injAt_of_lt_injS hρpos hρlt
      set ρ' : ℝ := (ρ - (11 * a + 30 * a ^ 2)) / (1 + 33 * a + 90 * a ^ 2) with hρ'def
      have hineq : ρ' * (1 + 33 * a + 90 * a ^ 2) + (11 * a + 30 * a ^ 2) ≤ ρ := by
        rw [hρ'def, div_mul_cancel₀ _ (ne_of_gt hcpos)]
        exact le_of_eq (sub_add_cancel ρ (11 * a + 30 * a ^ 2))
      have hle1' : ρ' ≤ 1 := by
        rw [hρ'def, div_le_iff₀ hcpos]
        nlinarith [hρle1, hepos, hcone]
      have hgt₀ : injCap x < (4 * injCap x - (11 * a + 30 * a ^ 2))
          / (1 + 33 * a + 90 * a ^ 2) := by
        rw [lt_div_iff₀ hcpos]
        nlinarith [harith]
      have hmono : (4 * injCap x - (11 * a + 30 * a ^ 2)) / (1 + 33 * a + 90 * a ^ 2) ≤ ρ' := by
        rw [hρ'def]
        exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hcpos)
      have hgt : injCap x < ρ' := lt_of_lt_of_le hgt₀ hmono
      have hpos' : 0 < ρ' := lt_trans hIpos hgt
      have hInjx : InjAt x ρ' :=
        InjAt.smul_conj_transfer hInj hw ha ha2 (le_of_lt hpos') hineq
      have hSx : ρ' ≤ injS x := le_injS_of_injAt hpos' hle1' hInjx
      rw [hinjS_eq] at hSx
      linarith
    calc injCap (w • x) ≤ injS (w • x) := injCap_le_injS _
      _ ≤ 4 * injCap x := hS
  · -- large case: `4 * injCap x ≥ 1/2` and `injCap` is capped at `1/2`
    push_neg at hsmall
    calc injCap (w • x) ≤ 1 / 2 := injCap_le_half _
      _ ≤ 4 * injCap x := by linarith

end

end Work.EKLC6Core
