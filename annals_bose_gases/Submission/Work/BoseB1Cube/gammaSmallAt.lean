import ChallengeDeps
import Submission.Work.BoseFixB1.boxMass_pos_of_goodSet
import Submission.Work.BoseFixB1B.rungDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.gammaSmallAt`

The scalar row `Γ_B = K_B³(μ(a v)³)^{1/2} → 0` as the diluteness `μ(a v)³ → 0`.

At FS's parameter choice (`fsParams`, `eq:Xparameter`/`eq:Xchoice`) the block
`K_B` is the monomial `(μa³)^{-6/323}`, so

    Γ_B(μ) = PBΓ v μ = K_B³·(μ(a v)³)^{1/2} = (μ(a v)³)^{1/2 − 18/323} ,

a **positive** power `c = 1/2 − 18/323 = 143.5/323 > 0` of the diluteness.  Hence
`Γ_B ≤ δ` for every admissible `μ` once `μ(a v)³ ≤ min 1 δ^{1/c}`; the extra
hypothesis `ParamsOK` carried by `Adm` is not used (our `ε₀` only makes the
admissible set smaller).

The lemma is the "for every `δ > 0` the bookkeeping term `Γ_B` is below `δ`"
row that a consumer needs in order to absorb `Γ_B` into an arbitrary prescribed
error once the diluteness is small enough.
-/

namespace Work.BoseB1Cube

open scoped Real Topology BigOperators

/-- **The exact value of the bookkeeping term** `Γ_B = PBΓ v μ`: at FS's
parameters `K_B = (μ(a v)³)^{-6/323}`, hence

    PBΓ v μ = (μ(a v)³)^{1/2 − 18/323} .

(The exponent is `1/2 − 18/323`; note `1/2 − 18/323 = 143.5/323 > 0`.) -/
theorem PBΓ_eq_rpow {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v)
    {μ : ℝ} (hμ : 0 < μ) :
    Work.BoseFixB1B.PBΓ v μ = (μ * (_root_.BoseGases.a v) ^ 3) ^ ((1 : ℝ) / 2 - 18 / 323) := by
  set t : ℝ := μ * (_root_.BoseGases.a v) ^ 3 with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have h1 : Work.BoseFixB1B.PBΓ v μ = (t ^ ((-6 : ℝ) / 323)) ^ 3 * t ^ (1 / 2 : ℝ) := by
    simp only [Work.BoseFixB1B.PBΓ, Work.BoseFixB1B.PBKB, Work.FockBridge.dlGamma,
      Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp, ht]
  have h2 : (t ^ ((-6 : ℝ) / 323)) ^ 3 = t ^ (((-6 : ℝ) / 323) * 3) := by
    calc (t ^ ((-6 : ℝ) / 323)) ^ 3 = (t ^ ((-6 : ℝ) / 323)) ^ (3 : ℝ) :=
          (Real.rpow_natCast _ 3).symm
      _ = t ^ (((-6 : ℝ) / 323) * 3) := (Real.rpow_mul htpos.le _ _).symm
  rw [h1, h2, ← Real.rpow_add htpos]
  congr 1
  norm_num

/-- **`Γ_B` is arbitrarily small for small diluteness.**  For every `δ > 0` there
is `ε₀ > 0` such that `Γ_B(μ) = PBΓ v μ ≤ δ` for every admissible `μ`
(`0 < μ` and `μ(a v)³ ≤ ε₀`; the `ParamsOK` clause of `Adm` is unused). -/
theorem gammaSmallAt {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v) (δ : ℝ) (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ {μ : ℝ}, Work.BoseBoxFix.Adm v ε₀ μ →
      Work.BoseFixB1B.PBΓ v μ ≤ δ := by
  set c : ℝ := (1 : ℝ) / 2 - 18 / 323 with hcdef
  have hcpos : 0 < c := by rw [hcdef]; norm_num
  have hε0pos : 0 < min 1 (δ ^ (1 / c)) := lt_min one_pos (Real.rpow_pos_of_pos hδ _)
  refine ⟨min 1 (δ ^ (1 / c)), hε0pos, ?_⟩
  intro μ hAdm
  obtain ⟨hμpos, hμa3le, -⟩ := hAdm
  have htpos : 0 < μ * (_root_.BoseGases.a v) ^ 3 := by positivity
  rw [PBΓ_eq_rpow hav hμpos]
  calc (μ * (_root_.BoseGases.a v) ^ 3) ^ c
      ≤ (min 1 (δ ^ (1 / c))) ^ c := Real.rpow_le_rpow htpos.le hμa3le hcpos.le
    _ ≤ (δ ^ (1 / c)) ^ c := Real.rpow_le_rpow (le_of_lt hε0pos) (min_le_right _ _) hcpos.le
    _ = δ := by
        rw [← Real.rpow_mul hδ.le]
        rw [div_mul_cancel₀ (1 : ℝ) (ne_of_gt hcpos), Real.rpow_one]

end Work.BoseB1Cube
