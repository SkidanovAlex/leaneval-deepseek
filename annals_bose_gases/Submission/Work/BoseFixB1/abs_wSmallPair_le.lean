import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.SmallBoxSliding.abs_wSmall1Pair_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1

/-- **Pointwise domination of the localised kernel `wSmallPair`** for an
arbitrary numerator `f` supported inside `ball 0 R` (with `R ≤ (ℓd)/16` and
`R ≤ ℓ·chiR0`).

The localised kernel factors as
`χ_{B(u)}(x)·(f(x−y)/((χ_M⋆χ_M)((x−y)/(ℓd))·(χ⋆χ)((x−y)/ℓ)))·χ_{B(u)}(y)`;
bounding the `x`-cutoff by `chiSupAbs · chiSmall M ((ℓd)⁻¹•x − u)`, the
`y`-cutoff by `chiSupAbs · chiSmallDecay M`, the `(ℓd)`-denominator below by
`smallConvLower M` (viable on the support of `f`) and the `ℓ`-denominator
below by `1/2` (viable since `R ≤ ℓ·chiR0`) gives the stated bound. -/
theorem abs_wSmallPair_le {M : ℕ} (hM : 1 ≤ M) {ℓ d R : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hfsupp : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → f z = 0)
    (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u x y : EuclideanSpace ℝ (Fin 3)) :
    |Submission.BoseGases.wSmallPair M ℓ d u f x y| ≤
      (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) *
        ((2 / Work.SmallBoxSliding.smallConvLower M) *
          (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) * |f (x - y)|) := by
  have hcpos : 0 < ℓ * d := mul_pos hℓ hd
  have hDnn : 0 ≤ Submission.BoseGases.chiSmallDecay M :=
    Submission.BoseGases.chiSmallDecay_nonneg M
  have hSpos : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hx : |Submission.BoseGases.chiSmallB M ℓ d u x| ≤
      Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) :=
    Work.SmallBoxSliding.abs_chiSmallB_le (M := M) (ℓ := ℓ) (d := d) hM u x
  have hy : |Submission.BoseGases.chiSmallB M ℓ d u y| ≤
      Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
    refine le_trans (Work.SmallBoxSliding.abs_chiSmallB_le (M := M) (ℓ := ℓ) (d := d) hM u y) ?_
    have hb2 : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • y - u)
        ≤ Submission.BoseGases.chiSmallDecay M := by
      have hb' := Submission.BoseGases.chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • y - u)
      rwa [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at hb'
    exact mul_le_mul_of_nonneg_left hb2 Submission.BoseGases.chiSupAbs_nonneg
  have hD2 : |Submission.BoseGases.wSmallScaled M (ℓ * d) f (x - y)| ≤
      |f (x - y)| / Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.abs_wSmallScaled_le (M := M) (c := ℓ * d) (R := R) hM hcpos hfsupp hR (x - y)
  have hmid : |Submission.BoseGases.wSmallScaled M (ℓ * d) f (x - y)
      / Submission.BoseGases.convScale ℓ (x - y)| ≤
        2 * (|f (x - y)| / Work.SmallBoxSliding.smallConvLower M) := by
    by_cases hnorm : ‖x - y‖ ≤ R
    · have hinv : |(Submission.BoseGases.convScale ℓ (x - y))⁻¹| ≤ 2 :=
        Submission.BoseGases.abs_inv_convScale_le_two (ℓ := ℓ) (R := R) hℓ hRχ hnorm
      rw [div_eq_mul_inv, abs_mul]
      calc
        |Submission.BoseGases.wSmallScaled M (ℓ * d) f (x - y)|
              * |(Submission.BoseGases.convScale ℓ (x - y))⁻¹|
            ≤ (|f (x - y)| / Work.SmallBoxSliding.smallConvLower M) * 2 :=
              mul_le_mul hD2 hinv (abs_nonneg _) (div_nonneg (abs_nonneg _) (le_of_lt hSpos))
        _ = 2 * (|f (x - y)| / Work.SmallBoxSliding.smallConvLower M) := by ring
    · have hz0 : f (x - y) = 0 := hfsupp (x - y) (le_of_lt (lt_of_not_ge hnorm))
      have hw0 : Submission.BoseGases.wSmallScaled M (ℓ * d) f (x - y) = 0 := by
        dsimp [Submission.BoseGases.wSmallScaled]
        rw [hz0]
        ring
      rw [hw0, hz0, zero_div, abs_zero]
      simp
  have hB0 : 0 ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg hDnn
  have hA0 : 0 ≤ Submission.BoseGases.chiSupAbs
      * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) :=
    mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmall_nonneg M _)
  have hm0 : 0 ≤ 2 * (|f (x - y)| / Work.SmallBoxSliding.smallConvLower M) :=
    mul_nonneg (by norm_num) (div_nonneg (abs_nonneg _) (le_of_lt hSpos))
  calc
    |Submission.BoseGases.wSmallPair M ℓ d u f x y|
        = |Submission.BoseGases.chiSmallB M ℓ d u x|
            * |Submission.BoseGases.wSmallScaled M (ℓ * d) f (x - y)
                / Submission.BoseGases.convScale ℓ (x - y)|
            * |Submission.BoseGases.chiSmallB M ℓ d u y| := by
          unfold Submission.BoseGases.wSmallPair
          rw [abs_mul, abs_mul]
    _ ≤ (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
          * (2 * (|f (x - y)| / Work.SmallBoxSliding.smallConvLower M))
          * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M) :=
          mul_le_mul (mul_le_mul hx hmid (abs_nonneg _) hA0) hy (abs_nonneg _)
            (mul_nonneg hA0 hm0)
    _ = (Submission.BoseGases.chiSupAbs
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u))
          * ((2 / Work.SmallBoxSliding.smallConvLower M)
              * (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
              * |f (x - y)|) := by ring

end Work.BoseFixB1
