import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1B

/-!
# Support of the repointed sliding cutoff `chiSmallB` in `dlBox`

`Submission.BoseGases.chiSmallB M ℓ d u x = chiScale ℓ x · chiSmall M ((ℓd)⁻¹ • x − u)`
is the two-factor localising cutoff of the sliding small box
`dlBox ℓ d u = acube ℓ ∩ ((ℓd)•u + acube (ℓd))` (FS `eq:chiBdefinition`).

Both factors are supported in the corresponding cube:

* the `ℓ`-scale factor `chiScale ℓ x = χ(x/ℓ)` vanishes unless `x ∈ acube ℓ`
  (`Submission.BoseGases.chiScale_mem_acube`, from the ball support of the corpus bump);
* the `ℓd`-scale cosine factor `chiSmall M ((ℓd)⁻¹ • x − u)` vanishes unless
  `x − (ℓd)•u ∈ acube (ℓd)`
  (`Submission.BoseGases.chiSmall_scale_support_mem_abs_le`, the scaled face support of
  the explicit cosine bump `ζζζ^M`).

Hence the product is supported in `dlBox ℓ d u`.
-/

/-- **Support of the repointed cutoff**: `chiSmallB M ℓ d u x ≠ 0` forces `x ∈ dlBox ℓ d u`. -/
theorem fj_chiSmallB_support {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) (x : EuclideanSpace ℝ (Fin 3))
    (hx : Submission.BoseGases.chiSmallB M ℓ d u x ≠ 0) :
    x ∈ Submission.BoseGases.dlBox ℓ d u := by
  have hc : 0 < ℓ * d := mul_pos hℓ hd
  have hfac : Submission.BoseGases.chiSmallB M ℓ d u x
      = Submission.BoseGases.chiScale ℓ x
        * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) := rfl
  -- each factor of the product is nonzero
  have hbig : Submission.BoseGases.chiScale ℓ x ≠ 0 := fun h => hx (by rw [hfac, h, zero_mul])
  have hsmall : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) ≠ 0 :=
    fun h => hx (by rw [hfac, h, mul_zero])
  rw [Submission.BoseGases.mem_dlBox_iff]
  refine ⟨Submission.BoseGases.chiScale_mem_acube hℓ hbig, ?_⟩
  rw [Submission.BoseGases.mem_acube_iff]
  intro j
  rw [Set.mem_Icc]
  -- the small-box factor is `chiSmall M ((ℓd)⁻¹ • (x − (ℓd)•u))`
  have hsmul : (ℓ * d)⁻¹ • (x - (ℓ * d) • u) = (ℓ * d)⁻¹ • x - u := by
    rw [smul_sub, smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
  have hz : Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • (x - (ℓ * d) • u)) ≠ 0 := by
    rwa [hsmul]
  have h := Submission.BoseGases.chiSmall_scale_support_mem_abs_le hM (c := ℓ * d)
    hc (x := x - (ℓ * d) • u) hz j
  obtain ⟨h1, h2⟩ := abs_le.mp h
  constructor <;> linarith

end Work.BoseFixB1B
