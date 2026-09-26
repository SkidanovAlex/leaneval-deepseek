import Mathlib
import Submission.Work.Collar3D.PushOff.Defs

/-!
# The flat model chart of the disc collar is a homeomorphism

The chart of the flat model disc
`Work.Collar3D.discChartFun : {p : ℝ³} → ℂ × ℝ`, `p ↦ (p 0 + p 1 · i, p 2)`, is the identity of
`ℝ³` read in the coordinates `(Re, Im, height)`; its inverse is written down explicitly
(`discChartInvR3`, `discChartInv`), the two compositions are computed
(`discChartFun_discChartInv`, `discChartInv_discChartFun`) and both maps are continuous
(`continuous_discChartFun`, `continuous_discChartInv`).  The homeomorphism
`Work.Collar3D.Model.discChartHomeo` is assembled from the resulting `Equiv`.

As the statement demands, the underlying function of the homeomorphism is *literally* the chart
`discChartFun`, so the proof that the two agree is `rfl`.
-/

namespace Work.Collar3D.Model

noncomputable section

open Classical

/-- The inverse of the flat model chart, `(z, t) ↦ (z.re, z.im, t)`, as a point of `ℝ³`. -/
def discChartInvR3 (q : ℂ × ℝ) : R3 :=
  WithLp.toLp 2 ![q.1.re, q.1.im, q.2]

@[simp] theorem discChartInvR3_zero (q : ℂ × ℝ) : discChartInvR3 q 0 = q.1.re := by
  simp [discChartInvR3, WithLp.ofLp_toLp]

@[simp] theorem discChartInvR3_one (q : ℂ × ℝ) : discChartInvR3 q 1 = q.1.im := by
  simp [discChartInvR3, WithLp.ofLp_toLp]

@[simp] theorem discChartInvR3_two (q : ℂ × ℝ) : discChartInvR3 q 2 = q.2 := by
  simp [discChartInvR3, WithLp.ofLp_toLp]

/-- The inverse of the flat model chart, as a point of the full set `Set.univ ⊆ ℝ³`. -/
def discChartInv (q : ℂ × ℝ) : (Set.univ : Set R3) :=
  ⟨discChartInvR3 q, Set.mem_univ _⟩

@[simp] theorem discChartInv_coe (q : ℂ × ℝ) :
    ((discChartInv q : (Set.univ : Set R3)) : R3) = discChartInvR3 q := rfl

/-- The inverse of the flat model chart is continuous. -/
theorem continuous_discChartInvR3 : Continuous discChartInvR3 := by
  unfold discChartInvR3
  apply (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin 3 => ℝ)).comp
  apply continuous_pi
  intro i
  fin_cases i <;> simp <;> fun_prop

/-- The inverse of the flat model chart is continuous as a map into `Set.univ`. -/
theorem continuous_discChartInv : Continuous discChartInv :=
  continuous_discChartInvR3.subtype_mk (fun _ => Set.mem_univ _)

/-- The flat model chart `p ↦ (p 0 + p 1 · i, p 2)` is continuous. -/
theorem continuous_discChartFun : Continuous fun p => discChartFun p := by
  refine Continuous.prodMk ?_ ?_
  · fun_prop
  · fun_prop

/-- The chart is a left inverse of `discChartInv`: it is onto `ℂ × ℝ`. -/
theorem discChartFun_discChartInv (q : ℂ × ℝ) : discChartFun (discChartInv q) = q := by
  refine Prod.ext ?_ ?_
  · simp only [discChartFun_fst, discChartInv_coe, discChartInvR3_zero, discChartInvR3_one]
    exact Complex.re_add_im q.1
  · simp only [discChartFun_snd, discChartInv_coe, discChartInvR3_two]

/-- The chart is a right inverse of `discChartInv`: it is injective. -/
theorem discChartInv_discChartFun (p : (Set.univ : Set R3)) :
    discChartInv (discChartFun p) = p := by
  apply Subtype.ext
  rw [discChartInv_coe, WithLp.ext_iff]
  funext i
  fin_cases i <;> simp [discChartInvR3, WithLp.ofLp_toLp]

/-- **The flat model chart is a homeomorphism**: the map
`p ↦ (p 0 + p 1 · i, p 2)` of the whole of `ℝ³` onto `ℂ × ℝ` is a homeomorphism (the identity in
suitable coordinates), with inverse `(z, t) ↦ (z.re, z.im, t)`. -/
theorem discChartHomeo :
    ∃ Φ : (Set.univ : Set R3) ≃ₜ ℂ × ℝ, ∀ p, Φ p = discChartFun p := by
  refine ⟨Homeomorph.mk
    (Equiv.mk discChartFun discChartInv discChartInv_discChartFun discChartFun_discChartInv)
    continuous_discChartFun continuous_discChartInv, fun p => rfl⟩

end

end Work.Collar3D.Model
