import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLContract.Lemmas.Gamma3Facts
import Submission.Work.EKLContract.Lemmas.mkX_mul
import Submission.Work.EKLContract.Lemmas.mkX_one_short
import Submission.Work.EKLComp.LeafDefs

/-!
# Leafwise measures for a horospherical subgroup: the geometric set-up

This module collects the *geometric* vocabulary in which the existence of leafwise measures
(`Work.EKLContract.IsLeafwise`) for a horospherical subgroup `U ≤ SL₃(ℝ)` is stated and proved.
The plan is Pisa Thm 6.3 (Einsiedler–Lindenstrauss, *Diagonal actions on locally homogeneous
spaces*, §5–6), instantiated at `X₃ = SL₃(ℝ)/SL₃(ℤ)`.

The construction in Pisa §5–6 is *topological and measure theoretic only*: it uses

* a locally compact second countable space `X` (here `X₃`),
* a locally compact second countable group `T` (here `U`) acting continuously and *locally freely*
  on `X`, with a "ball structure" `r ↦ B_r` (here the entry balls `Uball U r`, whose closures
  `Ucl U r` are compact),
* a Radon measure `μ` whose stabilisers are trivial a.e. (here a probability measure on `X₃`),

and no differential geometry.  The only arithmetic input is the quantitative discreteness of
`Γ₃ = SL₃(ℤ)` (`V 1 ∩ Γ₃ = {1}`), from which local freeness on compacta follows.

## Main definitions

* `Xball x r` — the gauge ball `{g • x : g ∈ V r}`: this replaces the metric balls of Pisa §6.1
  ("`y` is within distance `r` of `z`" means `y ∈ Xball z r`).
* `Xpla U x r` — the `U`-plaque `{u • x : u ∈ Uball U r}` through `x`.
* `InjOnBall U x r` — `u ↦ u • x` is injective on `Uball U r`.
* `FineAtoms m m' Y` — the atoms of `m` and `m'` restricted to `Y` are countably equivalent
  (Pisa Def. 5.15): the hypothesis of the proportionality theorem for conditional measures.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false

noncomputable section

namespace Work.EKLC7

open Work.EKLContract

/-! ## 1. The gauge on `SL₃(ℝ)` -/

theorem one_mem_V {δ : ℝ} (hδ : 0 < δ) : (1 : SL3) ∈ V δ := by
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_one]
  simp only [Matrix.one_apply, sub_self, abs_zero]
  exact hδ

theorem V_mono {δ δ' : ℝ} (h : δ ≤ δ') : V δ ⊆ V δ' := fun g hg i j => lt_of_lt_of_le (hg i j) h

/-! ## 2. Gauge balls in `X₃` -/

/-- The gauge ball of radius `r` around `x ∈ X₃`: the image of `V r` under the action.  This is the
replacement for metric balls: it is a neighbourhood of `x` (for `r > 0`), the family is nested,
and `y ∈ Xball z r` means "`y` is within distance `r` of `z`". -/
def Xball (x : X3) (r : ℝ) : Set X3 := (fun g : SL3 => g • x) '' V r

/-- The image of the closed entry-ball of radius `r` under the orbit map: a compact "closed gauge
ball" around `x`. -/
def XballCl (x : X3) (r : ℝ) : Set X3 :=
  (fun g : SL3 => g • x) '' {g | ∀ i j, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j -
    (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ r}

theorem Xball_mono {x : X3} {r r' : ℝ} (h : r ≤ r') : Xball x r ⊆ Xball x r' :=
  Set.image_mono (V_mono h)

theorem mem_Xball_self {x : X3} {r : ℝ} (hr : 0 < r) : x ∈ Xball x r :=
  ⟨1, one_mem_V hr, one_smul _ _⟩

/-- The `U`-plaque of radius `r` through `x`: `{u • x : u ∈ U, ‖u - 1‖ < r}`. -/
def Xpla (U : Subgroup SL3) (x : X3) (r : ℝ) : Set X3 :=
  (fun g : SL3 => g • x) '' (Work.EKLComp.Uball U r)

theorem Xpla_mono {U : Subgroup SL3} {x : X3} {r r' : ℝ} (h : r ≤ r') :
    Xpla U x r ⊆ Xpla U x r' :=
  Set.image_mono (Work.EKLComp.Uball_mono h)

/-- **Injectivity on a ball.**  The orbit map `u ↦ u • x` is injective on the ball `Uball U r`. -/
def InjOnBall (U : Subgroup SL3) (x : X3) (r : ℝ) : Prop :=
  ∀ u₁ ∈ Work.EKLComp.Uball U r, ∀ u₂ ∈ Work.EKLComp.Uball U r, u₁ • x = u₂ • x → u₁ = u₂

/-! ## 3. Countably equivalent atoms (Pisa Def. 5.15) -/

/-- The atom of a σ-algebra `m` at `x`, for an arbitrary measurable space. -/
def atomG {α : Type*} [MeasurableSpace α] (m : MeasurableSpace α) (x : α) : Set α :=
  ⋂₀ {s | MeasurableSet[m] s ∧ x ∈ s}

theorem atomG_eq_atom (m : MeasurableSpace X3) (x : X3) : atomG m x = atom m x := rfl

theorem mem_atomG {α : Type*} [MeasurableSpace α] (m : MeasurableSpace α) (x : α) :
    x ∈ atomG m x := by
  refine Set.mem_sInter.mpr ?_
  rintro s ⟨_, hx⟩
  exact hx

/-- Pisa Def. 5.15: the atoms of `m` on `Y` are covered by countably many atoms of `m'`, and
conversely. -/
def FineAtoms {α : Type*} [MeasurableSpace α] (m m' : MeasurableSpace α) (Y : Set α) : Prop :=
  (∀ x ∈ Y, ∃ s : Set (Set α), s.Countable ∧ (∀ t ∈ s, ∃ y : α, t = atomG m' y) ∧
      atomG m x ∩ Y ⊆ ⋃₀ s) ∧
  (∀ x ∈ Y, ∃ s : Set (Set α), s.Countable ∧ (∀ t ∈ s, ∃ y : α, t = atomG m y) ∧
      atomG m' x ∩ Y ⊆ ⋃₀ s)

end Work.EKLC7
