import ChallengeDeps
import Submission.Work.BoseB7AK.W1rows.W1hat_abs_le
import Submission.Work.BoseBogFS.View
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.abs_W1_le_viewFS`

FS `eq:WSestimate` **for the cut-off kernel of the corrected view**:
under `RViewFS`,

    |Ŵ₁(k)| ≤ 16π·a(v)     for every mode label `k`,

where `E.W1 = ζ_Λ · chat (W1fun v h (ℓ v μ)) ∘ F.kmom` is the view's UV-cut kernel
(`RViewFS`'s 15th conjunct: `E.W1 k = uvCut fu Λ (F.kmom k) * Ŵ₁(F.kmom k)`).

The cut-off factor `ζ_Λ` is bounded by `1` in absolute value (`abs_uvCut_le_one`,
from the `LowCut` structure), so the claim reduces to the **uncut** FS estimate
`Work.BoseB7AK.W1rows.W1hat_abs_le`, which is the `L¹`-domination of the Fourier
transform plus the real-space mass bound `∫|wScaled ℓ (g₀ v h)| ≤ 16π·(a v)`.
The positivity of the healing length `ℓ v μ` — the only hypothesis `W1hat_abs_le`
needs beyond the standing ones — follows from the dilute-regime hypothesis
`R ≤ ℓ·χR0`, `R > 0` and `0 < χR0`.

**Scope note.**  `open scoped Real` is required for the symbol `π` of the statement:
the project sets `autoImplicit = false`, so without it `π` is an unknown identifier
(the statement does not even elaborate).  With the scope open, `π = Real.pi`, which is
the constant of FS `eq:WSestimate` (`16π·a v`), matching `W1hat_abs_le`.
-/

open scoped Real

namespace Work.BoseBogFS

/-- The UV cut-off factor `ζ_Λ(k) = f_u(‖k‖/Λ)` (`formula uvCut`) is bounded by `1` in
absolute value: for a `LowCut`, `f_u = 1` on `(-∞,1]`, `f_u = 0` on `[2,∞)`, antitone in
between.  No hypothesis on the sign of `Λ` is needed. -/
lemma abs_uvCut_le_one (fu : Work.BoseBoxFix.LowCut) (Λ : ℝ)
    (k : EuclideanSpace ℝ (Fin 3)) : |uvCut fu Λ k| ≤ 1 := by
  have h1 : fu.f (‖k‖ / Λ) ≤ 1 := by
    rcases lt_or_ge (‖k‖ / Λ) 1 with h | h
    · rw [fu.one _ h.le]
    · have := fu.anti h
      rwa [fu.one 1 le_rfl] at this
  have h0 : 0 ≤ fu.f (‖k‖ / Λ) := by
    rcases lt_or_ge (‖k‖ / Λ) 2 with h | h
    · have := fu.anti h.le
      rwa [fu.zero 2 le_rfl] at this
    · rw [fu.zero _ h]
  rw [uvCut, abs_of_nonneg h0]
  exact h1

theorem abs_W1_le_viewFS {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ}
    {F : Work.BoseB7.FockData Mode} {T : Work.BoseB7A.TildeData F} {E : Work.BoseB7.Q3Env Mode}
    {gHat0 : ℝ} (hview : Work.BoseBogFS.RViewFS v h μ F T E gHat0)
    (hv : ∀ x, 0 ≤ v x) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hRℓ : R ≤ Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0) :
    ∀ k : Mode, |E.W1 k| ≤ 16 * π * _root_.BoseGases.a v := by
  -- the 15th conjunct of `RViewFS` pins `E.W1` to the UV-cut Fourier transform of
  -- FS's renormalised kernel `W₁ = wScaled ℓ (g₀ v h)` at the momentum `F.kmom k`
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hW1, -⟩ := hview
  obtain ⟨fu, Λ, -, hW1eq⟩ := hW1
  -- the healing length is positive: `0 < R ≤ ℓ v μ · χR0` and `0 < χR0`
  have hRchi : 0 < Work.BoseFixR.ell v μ * Submission.BoseGases.chiR0 := lt_of_lt_of_le hR hRℓ
  have hℓpos : 0 < Work.BoseFixR.ell v μ := by
    by_contra hneg
    push Not at hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg (le_of_lt Submission.BoseGases.chiR0_pos)
    linarith
  intro k
  rw [hW1eq]
  -- the cut-off contributes at most a factor `1`
  calc |uvCut fu Λ (F.kmom k)
          * Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) (F.kmom k)|
      = |uvCut fu Λ (F.kmom k)|
          * |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) (F.kmom k)| :=
        abs_mul _ _
    _ ≤ 1 * |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) (F.kmom k)| :=
        mul_le_mul_of_nonneg_right (abs_uvCut_le_one fu Λ (F.kmom k)) (abs_nonneg _)
    _ = |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h (Work.BoseFixR.ell v μ)) (F.kmom k)| :=
        one_mul _
    _ ≤ 16 * π * _root_.BoseGases.a v :=
        Work.BoseB7AK.W1rows.W1hat_abs_le hR hℓpos hv hvrad hv_supp h hRℓ (F.kmom k)

end Work.BoseBogFS
