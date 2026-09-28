import Mathlib
import Submission.Work.StemsB.SerreSphereDefs
import Submission.Work.StemsB.PathFieldTriv
import Submission.Work.StemsB.isSerreFibration_evalOne

/-!
# Fibrewise triviality of the path–loop fibration over a set with a path field

The bottleneck of both Step I of the sphere-specific route (`Submission/Work/StemsB/`) and of the
Wang-sequence route (same directory) is the structure `Work.StemsB.FibrewiseTrivial p W d₀` for the
**path–loop fibration** `p = evalOne X x₀ : PathSpace X x₀ → X`.  Every downstream file assumes it,
none produces it.

This file defines the explicit trivialisation and the two *fibrewise* homotopies that make it work:

* `trivFun` — the trivialisation, `q ↦ (q(1), q * rev sg_{q(1)})`, over a set `W` with a path field
  `sg : ↥W × I → X`, `sg (w,0) = d₀`, `sg (w,1) = w`;
* `sectFun` — its section `(w, δ) ↦ δ * sg_w`;
* `squeezeH` — the homotopy `id ≃ sect ∘ triv`, keeping the base point `q(1)` fixed;
* `squeezeK` — the homotopy `id ≃ triv ∘ sect` on `↥W × p⁻¹(d₀)`, keeping the first coordinate fixed.

Both homotopies are the classical *reparametrisation* homotopies: the path
`(γ * rev sg) * sg` is `γ` followed by a loop at `γ(1)`, which squeezes to `γ` as the loop collapses.
The collapse is done in two steps so that the homotopy is *uniformly* continuous: the branch points
`hA t = 1 - 3t/4` and `hB t = 1 - t/2` move to `1` as `t → 0` (from the identity at `t = 0` to the
nested concatenation at `t = 1`), and the "loop" part is damped by the factor `t` (resp. `1 - t`).

The formulas are witnesses, not statements: the statements of the lemmas live in
`StepI/SqueezeContH.lean`, `StepI/SqueezeContK.lean` and `StepI/TrivSectCont.lean`.
-/

open scoped Topology unitInterval

namespace Work.Stems.StepI

open Work.StemsB

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X} {W : Set X} {d₀ : X}

/-! ## The reparametrisation parameters -/

/-- The first branch point of the squeeze, as a function of the homotopy parameter `t`:
`hA t = 1 - 3t/4`.  At `t = 1` (the nested concatenation) it is `1/4`, at `t = 0` (the identity)
it is `1`. -/
def hA (t : ℝ) : ℝ := 1 - 3 * t / 4

/-- The second branch point: `hB t = 1 - t/2`.  At `t = 1` it is `1/2`, at `t = 0` it is `1`. -/
def hB (t : ℝ) : ℝ := 1 - t / 2

theorem continuous_hA : Continuous hA := by unfold hA; fun_prop

theorem continuous_hB : Continuous hB := by unfold hB; fun_prop

@[simp] theorem hA_zero : hA 0 = 1 := by unfold hA; norm_num

@[simp] theorem hA_one : hA 1 = 1 / 4 := by unfold hA; norm_num

@[simp] theorem hB_zero : hB 0 = 1 := by unfold hB; norm_num

@[simp] theorem hB_one : hB 1 = 1 / 2 := by unfold hB; norm_num

theorem hA_pos {t : ℝ} (ht : t ≤ 1) : 0 < hA t := by unfold hA; linarith

theorem hA_le_hB {t : ℝ} (ht : 0 ≤ t) : hA t ≤ hB t := by unfold hA hB; linarith

theorem hB_le_one {t : ℝ} (ht : 0 ≤ t) : hB t ≤ 1 := by unfold hB; linarith

theorem hA_le_one {t : ℝ} (ht : 0 ≤ t) : hA t ≤ 1 := by unfold hA; linarith

theorem hA_lt_one {t : ℝ} (ht : 0 < t) : hA t < 1 := by unfold hA; linarith

theorem hB_lt_one {t : ℝ} (ht : 0 < t) : hB t < 1 := by unfold hB; linarith

theorem one_sub_hB_pos {t : ℝ} (ht : 0 < t) : 0 < 1 - hB t := by unfold hB; linarith

theorem hB_sub_hA (t : ℝ) : hB t - hA t = t / 4 := by unfold hA hB; ring

/-! ## The underlying data of a point of `p⁻¹W` -/

/-- The point of `W` under a point of `p⁻¹W`. -/
def wOf (z : ↥((evalOne X x₀) ⁻¹' W)) : ↥W := ⟨(evalOne X x₀) z.1, z.2⟩

@[simp] theorem wOf_coe (z : ↥((evalOne X x₀) ⁻¹' W)) :
    (wOf z : X) = (evalOne X x₀) z.1 := rfl

theorem continuous_wOf : Continuous (wOf (x₀ := x₀) (W := W)) :=
  Continuous.subtype_mk ((evalOne X x₀).continuous.comp continuous_subtype_val) _

/-- The underlying path of a point of `p⁻¹W`. -/
def cmOf (z : ↥((evalOne X x₀) ⁻¹' W)) : C(I, X) := z.1.1

@[simp] theorem cmOf_apply (z : ↥((evalOne X x₀) ⁻¹' W)) (s : I) : cmOf z s = z.1.1 s := rfl

theorem continuous_cmOf : Continuous (cmOf (x₀ := x₀) (W := W)) := by
  unfold cmOf
  exact continuous_subtype_val.comp continuous_subtype_val

@[simp] theorem cmOf_zero (z : ↥((evalOne X x₀) ⁻¹' W)) : cmOf z 0 = x₀ := z.1.2

@[simp] theorem cmOf_one (z : ↥((evalOne X x₀) ⁻¹' W)) : cmOf z 1 = (wOf z : X) := rfl

/-- The underlying path of a point of the fibre `p⁻¹{d₀}`. -/
def fibCM (y : ↥((evalOne X x₀) ⁻¹' {d₀})) : C(I, X) := y.1.1

@[simp] theorem fibCM_apply (y : ↥((evalOne X x₀) ⁻¹' {d₀})) (s : I) : fibCM y s = y.1.1 s := rfl

theorem continuous_fibCM : Continuous (fibCM (x₀ := x₀) (d₀ := d₀)) := by
  unfold fibCM
  exact continuous_subtype_val.comp continuous_subtype_val

@[simp] theorem fibCM_zero (y : ↥((evalOne X x₀) ⁻¹' {d₀})) : fibCM y 0 = x₀ := y.1.2

@[simp] theorem fibCM_one (y : ↥((evalOne X x₀) ⁻¹' {d₀})) : fibCM y 1 = d₀ := y.2

/-- The path field at a point of `W`. -/
def sigOf (sg : C(↥W × I, X)) (w : ↥W) : C(I, X) :=
  ⟨fun t => sg (w, t), sg.continuous.comp (continuous_const.prodMk continuous_id)⟩

@[simp] theorem sigOf_apply (sg : C(↥W × I, X)) (w : ↥W) (t : I) : sigOf sg w t = sg (w, t) := rfl

theorem sigOf_zero (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀) (w : ↥W) :
    sigOf sg w 0 = d₀ := hsg0 w

theorem sigOf_one (sg : C(↥W × I, X)) (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X)) (w : ↥W) :
    sigOf sg w 1 = (w : X) := hsg1 w

/-! ## The trivialisation and its section -/

/-- **The trivialisation**, as a path: `q ↦ q * rev sg_{q(1)}`. -/
def trivFun (sg : C(↥W × I, X)) (z : ↥((evalOne X x₀) ⁻¹' W)) (s : I) : X :=
  if (2 : ℝ) * (s : ℝ) ≤ 1 then cmOf z (clampI (2 * (s : ℝ)))
  else sg (wOf z, clampI (2 - 2 * (s : ℝ)))

/-- **The section of the trivialisation**: `(w, δ) ↦ δ * sg_w`. -/
def sectFun (sg : C(↥W × I, X)) (y : ↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) (s : I) : X :=
  if (2 : ℝ) * (s : ℝ) ≤ 1 then fibCM y.2 (clampI (2 * (s : ℝ)))
  else sg (y.1, clampI (2 * (s : ℝ) - 1))

theorem trivFun_zero (sg : C(↥W × I, X)) (z : ↥((evalOne X x₀) ⁻¹' W)) :
    trivFun sg z 0 = x₀ := by
  rw [trivFun, if_pos (by norm_num)]
  rw [show (2 : ℝ) * (((0 : I)) : ℝ) = 0 by norm_num, clampI_zero, cmOf_zero]

theorem trivFun_one (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (z : ↥((evalOne X x₀) ⁻¹' W)) : trivFun sg z 1 = d₀ := by
  rw [trivFun, if_neg (by norm_num)]
  rw [show (2 : ℝ) - 2 * ((1 : I) : ℝ) = 0 by norm_num, clampI_zero]
  exact hsg0 (wOf z)

theorem sectFun_zero (sg : C(↥W × I, X)) (y : ↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) :
    sectFun sg y 0 = x₀ := by
  rw [sectFun, if_pos (by norm_num)]
  rw [show (2 : ℝ) * (((0 : I)) : ℝ) = 0 by norm_num, clampI_zero, fibCM_zero]

theorem sectFun_one (sg : C(↥W × I, X)) (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X))
    (y : ↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) : sectFun sg y 1 = (y.1 : X) := by
  rw [sectFun, if_neg (by norm_num)]
  rw [show (2 : ℝ) * ((1 : I) : ℝ) - 1 = 1 by norm_num, clampI_one]
  exact hsg1 y.1

/-! ## The composites, in the shape the homotopies end at -/

/-- `sect` after `triv`: `(γ * rev sg) * sg`. -/
def compFun (sg : C(↥W × I, X)) (w : ↥W) (γ : C(I, X)) (s : I) : X :=
  if (2 : ℝ) * (s : ℝ) ≤ 1 then
    (if (4 : ℝ) * (s : ℝ) ≤ 1 then γ (clampI (4 * (s : ℝ)))
      else sg (w, clampI (2 - 4 * (s : ℝ))))
  else sg (w, clampI (2 * (s : ℝ) - 1))

/-- `triv` after `sect`: `(δ * sg) * rev sg`. -/
def compFunK (sg : C(↥W × I, X)) (w : ↥W) (δ : C(I, X)) (s : I) : X :=
  if (2 : ℝ) * (s : ℝ) ≤ 1 then
    (if (4 : ℝ) * (s : ℝ) ≤ 1 then δ (clampI (4 * (s : ℝ)))
      else sg (w, clampI (4 * (s : ℝ) - 1)))
  else sg (w, clampI (2 - 2 * (s : ℝ)))

theorem compFun_zero (sg : C(↥W × I, X)) (w : ↥W) (γ : C(I, X)) :
    compFun sg w γ 0 = γ 0 := by
  rw [compFun, if_pos (by norm_num), if_pos (by norm_num)]
  rw [show (4 : ℝ) * (((0 : I)) : ℝ) = 0 by norm_num, clampI_zero]

theorem compFun_one (sg : C(↥W × I, X)) (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X))
    (w : ↥W) (γ : C(I, X)) (hγ : γ 1 = (w : X)) : compFun sg w γ 1 = (w : X) := by
  rw [compFun, if_neg (by norm_num)]
  rw [show (2 : ℝ) * ((1 : I) : ℝ) - 1 = 1 by norm_num, clampI_one]
  exact hsg1 w

theorem compFunK_zero (sg : C(↥W × I, X)) (w : ↥W) (δ : C(I, X)) :
    compFunK sg w δ 0 = δ 0 := by
  rw [compFunK, if_pos (by norm_num), if_pos (by norm_num)]
  rw [show (4 : ℝ) * (((0 : I)) : ℝ) = 0 by norm_num, clampI_zero]

theorem compFunK_one (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (w : ↥W) (δ : C(I, X)) : compFunK sg w δ 1 = d₀ := by
  rw [compFunK, if_neg (by norm_num)]
  rw [show (2 : ℝ) - 2 * ((1 : I) : ℝ) = 0 by norm_num, clampI_zero]
  exact hsg0 w

/-! ## The two homotopy families -/

/-- **The squeeze homotopy** from `id` (at `t = 0`) to `sect ∘ triv` (at `t = 1`): for a path
`γ` ending at `w`, the path `(γ * rev sg_w) * sg_w` squeezes to `γ`.  The parameter `t` runs from
`0` (the identity) to `1` (the nested concatenation). -/
def squeezeH (sg : C(↥W × I, X)) (z : ↥((evalOne X x₀) ⁻¹' W)) (t s : ℝ) : X :=
  if s ≤ hA t then cmOf z (clampI (s / hA t))
  else if s ≤ hB t then sg (wOf z, clampI (1 - t * ((s - hA t) / (hB t - hA t))))
  else sg (wOf z, clampI (1 - t * (1 - ((s - hB t) / (1 - hB t)))))

/-- **The squeeze homotopy** from `id` (at `t = 0`) to `triv ∘ sect` (at `t = 1`): for a path
`δ : x₀ → d₀`, the path `(δ * sg_w) * rev sg_w` squeezes to `δ`. -/
def squeezeK (sg : C(↥W × I, X)) (w : ↥W) (δ : C(I, X)) (t s : ℝ) : X :=
  if s ≤ hA t then δ (clampI (s / hA t))
  else if s ≤ hB t then sg (w, clampI (t * ((s - hA t) / (hB t - hA t))))
  else sg (w, clampI (t * (1 - ((s - hB t) / (1 - hB t)))))

/-- The uncurried first homotopy, with the slice variable `q.2` and the homotopy parameter `q.1.2`. -/
def squeezeHUnc (sg : C(↥W × I, X)) (q : (↥((evalOne X x₀) ⁻¹' W) × I) × I) : X :=
  squeezeH sg q.1.1 (q.1.2 : ℝ) (q.2 : ℝ)

/-- The uncurried second homotopy. -/
def squeezeKUnc (sg : C(↥W × I, X)) (q : ((↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) × I) × I) : X :=
  squeezeK sg q.1.1.1 (fibCM q.1.1.2) (q.1.2 : ℝ) (q.2 : ℝ)

/-! ## The trivialisation and the section as continuous maps (with the base point fixed) -/

theorem continuous_trivFun_fixed (sg : C(↥W × I, X))
    (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X)) (z : ↥((evalOne X x₀) ⁻¹' W)) :
    Continuous fun s : I => trivFun sg z s := by
  unfold trivFun
  refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
  · exact (cmOf z).continuous.comp (continuous_clampI.comp (by fun_prop))
  · exact sg.continuous.comp (((continuous_const : Continuous fun _ : I => wOf z)).prodMk
      (continuous_clampI.comp (by fun_prop)))
  · fun_prop
  · fun_prop
  · intro s hs
    rw [hs, show (2 : ℝ) - 1 = 1 by norm_num, clampI_one, cmOf_one, hsg1]

theorem continuous_sectFun_fixed (sg : C(↥W × I, X))
    (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀) (y : ↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) :
    Continuous fun s : I => sectFun sg y s := by
  unfold sectFun
  refine Continuous.if_le ?_ ?_ ?_ ?_ ?_
  · exact (fibCM y.2).continuous.comp (continuous_clampI.comp (by fun_prop))
  · exact sg.continuous.comp (((continuous_const : Continuous fun _ : I => y.1)).prodMk
      (continuous_clampI.comp (by fun_prop)))
  · fun_prop
  · fun_prop
  · intro s hs
    rw [hs, clampI_one, show (1 : ℝ) - 1 = 0 by norm_num, clampI_zero, fibCM_one, hsg0]

/-- The trivialisation as a path, packaged as a continuous map. -/
def trivCM (sg : C(↥W × I, X)) (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X))
    (z : ↥((evalOne X x₀) ⁻¹' W)) : C(I, X) :=
  ⟨fun s => trivFun sg z s, continuous_trivFun_fixed sg hsg1 z⟩

@[simp] theorem trivCM_apply (sg : C(↥W × I, X)) (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X))
    (z : ↥((evalOne X x₀) ⁻¹' W)) (s : I) : trivCM sg hsg1 z s = trivFun sg z s := rfl

theorem trivCM_zero (sg : C(↥W × I, X)) (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X))
    (z : ↥((evalOne X x₀) ⁻¹' W)) : trivCM sg hsg1 z 0 = x₀ := trivFun_zero sg z

theorem trivCM_one (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X)) (z : ↥((evalOne X x₀) ⁻¹' W)) :
    trivCM sg hsg1 z 1 = d₀ := trivFun_one sg hsg0 z

/-- The section as a path, packaged as a continuous map. -/
def sectCM (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (y : ↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) : C(I, X) :=
  ⟨fun s => sectFun sg y s, continuous_sectFun_fixed sg hsg0 y⟩

@[simp] theorem sectCM_apply (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (y : ↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) (s : I) : sectCM sg hsg0 y s = sectFun sg y s := rfl

theorem sectCM_zero (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (y : ↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) : sectCM sg hsg0 y 0 = x₀ := sectFun_zero sg y

theorem sectCM_one (sg : C(↥W × I, X)) (hsg0 : ∀ w : ↥W, sg (w, 0) = d₀)
    (hsg1 : ∀ w : ↥W, sg (w, 1) = (w : X)) (y : ↥W × ↥((evalOne X x₀) ⁻¹' {d₀})) :
    sectCM sg hsg0 y 1 = (y.1 : X) := sectFun_one sg hsg1 y

end

end Work.Stems.StepI
