import Mathlib
import Submission.Work.StemsB.isSerreFibration_evalOne

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The loop `α * α⁻¹` is null-homotopic, explicitly and continuously in `α`

For the first page of the Serre spectral sequence of the path–loop fibration, one needs the
trivialisation of the fibration over a cell to be a map *over the base*; in that form the composite
of the two trivialisation maps is `δ ↦ δ * η * η⁻¹`.  The loop `α * α⁻¹` has an elementary
**explicit null-homotopy rel the basepoint**, and — crucially for the spectral sequence — the whole
family of these null-homotopies depends continuously on the path `α`:

  `transSymmFun r α t = if 2t ≤ 1 then α (2t(1-r)) else α (2(1-t)(1-r))`,

which is `α * α⁻¹` for `r = 0`, the constant path at the start of `α` for `r = 1`, and fixes that
point for every `r`.

## Main declarations

* `Work.StemsB.transSymmFun`, `Work.StemsB.continuous_transSymmFun` — the explicit function and its
  joint continuity.
* `Work.StemsB.transSymmFamily` — the `Path`-valued family.
* `Work.StemsB.transSymm_homotopic` — the packaged `Homotopic` statement.
-/

open scoped Topology unitInterval

namespace Work.StemsB

noncomputable section

variable {X : Type} [TopologicalSpace X] {b b' : X}

/-- The underlying function of the explicit null-homotopy of `α * α⁻¹`: at level `r` the path `α`
is traced out and back on the (reparametrised) interval `[0, 1-r]`. -/
def transSymmFun (r : I) (α : Path b b') (t : I) : X :=
  if ((2 : ℝ) * (t : ℝ) ≤ 1) then
    (α : C(I, X)) (clampI ((2 : ℝ) * (t : ℝ) * (1 - (r : ℝ))))
  else
    (α : C(I, X)) (clampI ((2 : ℝ) * (1 - (t : ℝ)) * (1 - (r : ℝ))))

theorem continuous_transSymmFun :
    Continuous fun w : (I × Path b b') × I => transSymmFun w.1.1 w.1.2 w.2 := by
  unfold transSymmFun
  refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
  · have hα : Continuous fun w : (I × Path b b') × I => (w.1.2 : C(I, X)) :=
      (show Continuous (fun y : Path b b' => (y : C(I, X))) from
        continuous_induced_dom).comp (continuous_snd.comp continuous_fst)
    have ht : Continuous fun w : (I × Path b b') × I =>
        clampI ((2 : ℝ) * (w.2 : ℝ) * (1 - (w.1.1 : ℝ))) :=
      continuous_clampI.comp (by fun_prop)
    exact continuous_eval.comp (hα.prodMk ht)
  · have hα : Continuous fun w : (I × Path b b') × I => (w.1.2 : C(I, X)) :=
      (show Continuous (fun y : Path b b' => (y : C(I, X))) from
        continuous_induced_dom).comp (continuous_snd.comp continuous_fst)
    have ht : Continuous fun w : (I × Path b b') × I =>
        clampI ((2 : ℝ) * (1 - (w.2 : ℝ)) * (1 - (w.1.1 : ℝ))) :=
      continuous_clampI.comp (by fun_prop)
    exact continuous_eval.comp (hα.prodMk ht)
  · fun_prop
  · fun_prop
  · intro w hw
    show (w.1.2 : C(I, X)) (clampI ((2 : ℝ) * (w.2 : ℝ) * (1 - (w.1.1 : ℝ))))
      = (w.1.2 : C(I, X)) (clampI ((2 : ℝ) * (1 - (w.2 : ℝ)) * (1 - (w.1.1 : ℝ))))
    have h : (2 : ℝ) * (w.2 : ℝ) = 1 := by linarith [hw]
    have h2 : (w.2 : ℝ) = 1 / 2 := by linarith [h]
    rw [h, h2]
    norm_num

theorem transSymmFun_zero_arg (r : I) (α : Path b b') : transSymmFun r α 0 = b := by
  have harg : (2 : ℝ) * (((0 : I)) : ℝ) * (1 - (r : ℝ)) = 0 := by
    rw [show (((0 : I)) : ℝ) = 0 from rfl]; ring
  rw [transSymmFun,
    if_pos (by rw [show (((0 : I)) : ℝ) = 0 from rfl]; norm_num), harg, clampI_zero]
  exact α.source'

theorem transSymmFun_one_arg (r : I) (α : Path b b') : transSymmFun r α 1 = b := by
  have harg : (2 : ℝ) * (1 - (((1 : I)) : ℝ)) * (1 - (r : ℝ)) = 0 := by
    rw [show (((1 : I)) : ℝ) = 1 from rfl]; ring
  rw [transSymmFun,
    if_neg (by rw [show (((1 : I)) : ℝ) = 1 from rfl]; norm_num), harg, clampI_zero]
  exact α.source'

theorem transSymmFun_zero_r (α : Path b b') (t : I) :
    transSymmFun 0 α t = (α.trans α.symm) t := by
  rw [transSymmFun]
  by_cases h : (2 : ℝ) * (t : ℝ) ≤ 1
  · rw [if_pos h, Path.trans_apply, dif_pos (by linarith)]
    refine congrArg (fun u : I => (α : C(I, X)) u) (Subtype.ext ?_)
    have hmem : (2 : ℝ) * (t : ℝ) * (1 - (((0 : I)) : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
      rw [show (((0 : I)) : ℝ) = 0 from rfl, sub_zero, mul_one]
      exact ⟨by linarith [t.2.1], h⟩
    rw [clampI_of_mem hmem]
    push_cast
    ring
  · rw [if_neg h, Path.trans_apply, dif_neg (by linarith)]
    refine congrArg (fun u : I => (α : C(I, X)) u) (Subtype.ext ?_)
    have h3 : (1 : ℝ) ≤ 2 * (t : ℝ) := by linarith [not_le.mp h]
    have hmem : (2 : ℝ) * (1 - (t : ℝ)) * (1 - (((0 : I)) : ℝ)) ∈ Set.Icc (0 : ℝ) 1 := by
      rw [show (((0 : I)) : ℝ) = 0 from rfl, sub_zero, mul_one]
      constructor <;> nlinarith [t.2.1, t.2.2, h3]
    rw [clampI_of_mem hmem]
    rw [unitInterval.coe_symm_eq]
    push_cast
    ring

theorem transSymmFun_one_r (α : Path b b') (t : I) : transSymmFun 1 α t = b := by
  rw [transSymmFun]
  by_cases h : (2 : ℝ) * (t : ℝ) ≤ 1
  · have harg : (2 : ℝ) * (t : ℝ) * (1 - (((1 : I)) : ℝ)) = 0 := by
      rw [show (((1 : I)) : ℝ) = 1 from rfl]; ring
    rw [if_pos h, harg, clampI_zero]
    exact α.source'
  · have harg : (2 : ℝ) * (1 - (t : ℝ)) * (1 - (((1 : I)) : ℝ)) = 0 := by
      rw [show (((1 : I)) : ℝ) = 1 from rfl]; ring
    rw [if_neg h, harg, clampI_zero]
    exact α.source'

/-- The explicit null-homotopy of `α * α⁻¹`, as a `Path b b`-valued family. -/
def transSymmFamily (w : I × Path b b') : Path b b where
  toContinuousMap :=
    ⟨fun t => transSymmFun w.1 w.2 t,
      (continuous_transSymmFun (b := b) (b' := b')).comp
        (((continuous_const : Continuous fun _ : I => w)).prodMk
          (continuous_id : Continuous fun t : I => t))⟩
  source' := transSymmFun_zero_arg w.1 w.2
  target' := transSymmFun_one_arg w.1 w.2

theorem continuous_transSymmFamily :
    Continuous (transSymmFamily (b := b) (b' := b')) :=
  Path.continuous_uncurry_iff.mp continuous_transSymmFun

/-- **The loop `α * α⁻¹` is homotopic to the constant path, explicitly and continuously in `α`.** -/
theorem transSymm_homotopic :
    ContinuousMap.Homotopic
      (ContinuousMap.mk (fun α : Path b b' => α.trans α.symm)
        (Path.continuous_trans.comp (continuous_id.prodMk Path.continuous_symm)))
      (ContinuousMap.mk (fun _ : Path b b' => Path.refl b) continuous_const) :=
  ⟨{ toFun := fun w => transSymmFamily w
     continuous_toFun := continuous_transSymmFamily
     map_zero_left := by
       intro α
       apply Path.ext
       funext t
       exact transSymmFun_zero_r α t
     map_one_left := by
       intro α
       apply Path.ext
       funext t
       exact transSymmFun_one_r α t }⟩

end

end Work.StemsB
