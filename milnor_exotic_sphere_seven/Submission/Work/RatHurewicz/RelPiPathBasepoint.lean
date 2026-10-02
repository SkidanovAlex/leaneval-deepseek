import Submission.Work.RatHurewicz.RelPiPathDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The base points of the homotopy fibres of `A ↪ Y` along a path in `A`

For `η : Path a₀ a` in `↥A`, the comparison map `relPathPhi a₀ a η` sends the base point
`bp_a = (a, const)` of `E_a` to `(a, ηy ≫ const)` in `E_{a₀}`, which is *not* the base point
`bp_{a₀} = (a₀, const)` of `E_{a₀}`; the two points are however joined by a path in `E_{a₀}`:
concatenate the path `t ↦ (η t, s ↦ ηy (clampI (s * t)))` (the initial segments of `η`) with the
path induced by the homotopy `Path.Homotopic.trans_refl ηy : ηy ≫ const ~ ηy`.
-/

open scoped Topology Topology.Homotopy unitInterval
open ContinuousMap
open Work.StemsB

namespace Work.RatHurewicz

noncomputable section

variable {Y : Type} [TopologicalSpace Y] {A : Set Y}

/-! ## Points of the homotopy fibre determined by a path -/

/-- The point `(a', γ)` of the homotopy fibre of `setIncl A` at `a₀` determined by a path
`γ : Path (i a₀) (i a')`. -/
def fibrePoint {a₀ a' : ↥A} (γ : Path (setIncl A a₀) (setIncl A a')) :
    homotopyFibre (setIncl A) a₀ :=
  ⟨(a', ⟨γ.toContinuousMap, γ.source'⟩), γ.target'⟩

@[simp]
theorem fibrePoint_fst {a₀ a' : ↥A} (γ : Path (setIncl A a₀) (setIncl A a')) :
    (fibrePoint γ).1.1 = a' := rfl

@[simp]
theorem fibrePoint_snd {a₀ a' : ↥A} (γ : Path (setIncl A a₀) (setIncl A a')) :
    fibrePath (fibrePoint γ) = γ := rfl

theorem fibrePoint_basepoint (a₀ : ↥A) :
    fibrePoint (Path.refl (setIncl A a₀)) = homotopyFibreBasepoint (setIncl A) a₀ := rfl

theorem relPathPhi_basepoint_apply (a₀ a : ↥A) (η : Path a₀ a) :
    relPathPhi a₀ a η (homotopyFibreBasepoint (setIncl A) a) =
      fibrePoint ((setInclPath a₀ a η).trans (Path.refl (setIncl A a))) := rfl

/-! ## The initial segments of `η` as a path in the homotopy fibre -/

/-- The initial segment of `ηy` up to `t`, as a path from `i a₀` to `i (η t)`. -/
def segPath (a₀ a : ↥A) (η : Path a₀ a) (t : I) : Path (setIncl A a₀) (setIncl A (η t)) where
  toContinuousMap :=
    ⟨fun s => (setInclPath a₀ a η) (clampI ((s : ℝ) * (t : ℝ))),
      (setInclPath a₀ a η).continuous.comp
        (continuous_clampI.comp (continuous_subtype_val.mul continuous_const))⟩
  source' := by
    show (setInclPath a₀ a η) (clampI ((0 : ℝ) * (t : ℝ))) = setIncl A a₀
    rw [zero_mul, clampI_zero]
    exact Path.source _
  target' := by
    show (setInclPath a₀ a η) (clampI ((1 : ℝ) * (t : ℝ))) = setIncl A (η t)
    rw [one_mul, clampI_coe_I]
    exact setInclPath_apply a₀ a η t

/-- The initial segments of `η`, as a continuous map `I → E_{a₀}`. -/
def basepointSegMap (a₀ a : ↥A) (η : Path a₀ a) : C(I, homotopyFibre (setIncl A) a₀) where
  toFun t := fibrePoint (segPath a₀ a η t)
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.prodMk ?_ ?_
    · exact η.continuous
    · refine Continuous.subtype_mk ?_ _
      exact continuous_of_continuous_uncurry _
        ((setInclPath a₀ a η).continuous.comp
          (continuous_clampI.comp
            ((continuous_subtype_val.comp continuous_snd).mul
              (continuous_subtype_val.comp continuous_fst))))

@[simp]
theorem basepointSegMap_apply_zero (a₀ a : ↥A) (η : Path a₀ a) :
    basepointSegMap a₀ a η 0 = homotopyFibreBasepoint (setIncl A) a₀ := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact η.source'
  · refine Subtype.ext (ContinuousMap.ext fun s => ?_)
    show (setInclPath a₀ a η) (clampI ((s : ℝ) * (((0 : I)) : ℝ))) = setIncl A a₀
    rw [show (((0 : I)) : ℝ) = 0 from rfl, mul_zero, clampI_zero]
    exact Path.source _

@[simp]
theorem basepointSegMap_apply_one (a₀ a : ↥A) (η : Path a₀ a) :
    basepointSegMap a₀ a η 1 = fibrePoint (setInclPath a₀ a η) := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · exact η.target'
  · refine Subtype.ext (ContinuousMap.ext fun s => ?_)
    show (setInclPath a₀ a η) (clampI ((s : ℝ) * (((1 : I)) : ℝ))) = (setInclPath a₀ a η) s
    rw [show (((1 : I)) : ℝ) = 1 from rfl, mul_one, clampI_coe_I]

/-- The path of initial segments, from the base point of `E_{a₀}` to the point determined by
`ηy`. -/
def basepointPath (a₀ a : ↥A) (η : Path a₀ a) :
    Path (homotopyFibreBasepoint (setIncl A) a₀) (fibrePoint (setInclPath a₀ a η)) where
  toContinuousMap := basepointSegMap a₀ a η
  source' := basepointSegMap_apply_zero a₀ a η
  target' := basepointSegMap_apply_one a₀ a η

theorem joined_basepoint_fibrePoint (a₀ a : ↥A) (η : Path a₀ a) :
    Joined (homotopyFibreBasepoint (setIncl A) a₀) (fibrePoint (setInclPath a₀ a η)) :=
  ⟨basepointPath a₀ a η⟩

/-! ## Homotopies of paths give paths in the homotopy fibre -/

/-- The path in the homotopy fibre induced by a homotopy of paths with the same endpoints. -/
def homotopyFibrePath {a₀ a' : ↥A} {γ γ' : Path (setIncl A a₀) (setIncl A a')}
    (F : γ'.Homotopy γ) : C(I, homotopyFibre (setIncl A) a₀) where
  toFun t :=
    ⟨(a', (⟨⟨fun s => F (t, s),
        F.continuous.comp (continuous_const.prodMk continuous_id)⟩,
      by
        show F (t, 0) = setIncl A a₀
        exact F.source t⟩ : PathSpace Y (setIncl A a₀))),
      by
        show F (t, 1) = setIncl A a'
        exact F.target t⟩
  continuous_toFun := by
    refine Continuous.subtype_mk ?_ _
    refine Continuous.prodMk ?_ ?_
    · exact continuous_const
    · refine Continuous.subtype_mk ?_ _
      refine continuous_of_continuous_uncurry _ ?_
      exact F.continuous

@[simp]
theorem homotopyFibrePath_apply_zero {a₀ a' : ↥A} {γ γ' : Path (setIncl A a₀) (setIncl A a')}
    (F : γ'.Homotopy γ) : homotopyFibrePath F 0 = fibrePoint γ' := by
  refine Subtype.ext (Prod.ext rfl ?_)
  refine Subtype.ext (ContinuousMap.ext fun s => ?_)
  show F (0, s) = γ' s
  exact F.map_zero_left s

@[simp]
theorem homotopyFibrePath_apply_one {a₀ a' : ↥A} {γ γ' : Path (setIncl A a₀) (setIncl A a')}
    (F : γ'.Homotopy γ) : homotopyFibrePath F 1 = fibrePoint γ := by
  refine Subtype.ext (Prod.ext rfl ?_)
  refine Subtype.ext (ContinuousMap.ext fun s => ?_)
  show F (1, s) = γ s
  exact F.map_one_left s

/-- A homotopy of paths with the same endpoints induces a path in the homotopy fibre. -/
theorem joined_fibrePoint_of_homotopic {a₀ a' : ↥A} {γ γ' : Path (setIncl A a₀) (setIncl A a')}
    (h : γ'.Homotopic γ) : Joined (fibrePoint γ') (fibrePoint γ) := by
  obtain ⟨F⟩ := h
  exact ⟨{ toContinuousMap := homotopyFibrePath F
           source' := homotopyFibrePath_apply_zero F
           target' := homotopyFibrePath_apply_one F }⟩

/-! ## The base point statement -/

theorem joined_relPathPhi_basepoint (a₀ a : ↥A) (η : Path a₀ a) :
    Joined (homotopyFibreBasepoint (setIncl A) a₀)
      (relPathPhi a₀ a η (homotopyFibreBasepoint (setIncl A) a)) := by
  refine (joined_basepoint_fibrePoint a₀ a η).trans (?_)
  rw [relPathPhi_basepoint_apply a₀ a η]
  exact joined_fibrePoint_of_homotopic
    (Path.Homotopic.trans_refl (setInclPath a₀ a η)).symm

end

end Work.RatHurewicz
