import ChallengeDeps
import Submission.Work.BoseB1Cube.gammaSmallAt
import Submission.Work.BoseFixB1S.sbCut_cube_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.sbCut_cube_le_mu_gamma`

**The cube of FS's spectral cut-off is dominated by `μ·Γ_B` at any diluteness
`t = μ(a v)³ ≤ 1`.**

Writing `t := μ(a v)³` for the diluteness and
`A := a v` (`Work.BoseB1S.sbCut_eq_inv_mul`), FS's small-box spectral cut-off is

    sbCut μ A = A⁻¹·(t)^{156/323} ,   hence   (sbCut μ A)³ = A⁻³·t^{468/323} .

Multiplying by `A³ = t/μ` turns the `A⁻³` into `μ/t`:

    (sbCut μ A)³ = (μ/t)·t^{468/323} = μ·t^{145/323} .

On the other hand (`gammaSmallAt.PBΓ_eq_rpow`)

    PBΓ v μ = K_B³·t^{1/2} = t^{1/2 - 18/323} = t^{287/646} ,

so the inequality `(sbCut μ A)³ ≤ μ·PBΓ v μ` is, after cancelling `μ > 0`,

    t^{145/323} ≤ t^{287/646} ,   i.e.  t^{290/646} ≤ t^{287/646} ,

which holds for `0 < t ≤ 1` because the map `c ↦ t^{c}` is **antitone** there
(`Work.BoseBox.fsXp_le_fsXp`, in the `fsXp` normalisation `c/323`).  The gap
between the two exponents is exactly `3/646`: this is a genuine (small) margin
at `t = 1`, where both sides equal `μ`, and it grows polynomially as `t → 0`.
-/

namespace Work.BoseB1Cube

open Work.BoseBox

/-- **The exact cube of FS's spectral cut-off, in `μ`-normalised form.**  With
`A = a v` and `t = μA³` one has `A⁻³·t^{468/323} = μ·t^{145/323}`, i.e.
`(sbCut μ A)³ = μ·fsXp t 145` (`fsXp t c = t^{c/323}`).

This is `sbCutCubeMul` with the harmless factor `A` divided out. -/
lemma sbCut_cube_eq_mu_mul {A μ : ℝ} (hA : 0 < A) (hμ : 0 < μ) :
    (Work.BoseFixB1.sbCut μ A) ^ 3 = μ * fsXp (μ * A ^ 3) 145 := by
  have ht : (0 : ℝ) < μ * A ^ 3 := by positivity
  -- `t^{468/323} = t·t^{145/323}` because `468 = 323 + 145` and `t^{323/323} = t`
  have hf : fsXp (μ * A ^ 3) 468 = (μ * A ^ 3) * fsXp (μ * A ^ 3) 145 := by
    rw [show (468 : ℝ) = 323 + 145 by norm_num, ← fsXp_mul ht 323 145,
      ← delta_eq_fsXp ht.le]
  rw [Work.BoseFixB1S.sbCut_eq_inv_mul hA hμ, mul_pow]
  rw [fsXp_pow ht.le 156 3]
  norm_num
  rw [hf]
  field_simp

/-- **`Γ_B` in the `fsXp` normalisation**: `PBΓ v μ = fsXp t (287/2)`, i.e.
`= t^{287/646}`; indeed `1/2 - 18/323 = 287/646`. -/
lemma PBΓ_eq_fsXp {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v)
    {μ : ℝ} (hμ : 0 < μ) :
    Work.BoseFixB1B.PBΓ v μ = fsXp (μ * (_root_.BoseGases.a v) ^ 3) (287 / 2) := by
  have hexp : (1 : ℝ) / 2 - 18 / 323 = (287 / 2) / 323 := by norm_num
  rw [PBΓ_eq_rpow hav hμ, hexp]
  rfl

/-- **The requested lemma.**  At any diluteness `μ(a v)³ ≤ 1` the cube of FS's
spectral cut-off is at most `μ·Γ_B`:

    (sbCut μ (a v))³ = μ·t^{145/323} ≤ μ·t^{287/646} = μ·PBΓ v μ .

The comparison is `fsXp_le_fsXp` with exponents `145/323` and `287/646`. -/
theorem sbCut_cube_le_mu_gamma {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v)
    {μ : ℝ} (hμ : 0 < μ) (hdil : μ * (_root_.BoseGases.a v) ^ 3 ≤ 1) :
    (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
      ≤ μ * Work.BoseFixB1B.PBΓ v μ := by
  have ht : (0 : ℝ) < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  calc (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) ^ 3
      = μ * fsXp (μ * (_root_.BoseGases.a v) ^ 3) 145 :=
        sbCut_cube_eq_mu_mul hav hμ
    _ ≤ μ * fsXp (μ * (_root_.BoseGases.a v) ^ 3) (287 / 2) :=
        mul_le_mul_of_nonneg_left (fsXp_le_fsXp ht hdil (by norm_num)) hμ.le
    _ = μ * Work.BoseFixB1B.PBΓ v μ := by rw [PBΓ_eq_fsXp hav hμ]

end Work.BoseB1Cube
