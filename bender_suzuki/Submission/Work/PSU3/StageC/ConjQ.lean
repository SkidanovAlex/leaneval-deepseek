/-
# `Work.PSU3.StageC.ConjQ` — conjugation of `Q` by the frame's `KW`

The vocabulary shared by the Stage C computation of `f` on the `ω`-coset
(`Work.PSU3.StageC.f_formula_on_omega_coset`):

* `conjQ hS fr d x` — the right action `x ↦ d⁻¹ x d` of `d ∈ KW ≤ D ≤ H` on `x ∈ Q`
  (`conjQ_coe`), with `e (conjQ d x) = SZ.torusAct (κ d) (e x)` (`e_conjQ`);
* the composition rule `conjQ d₁ (conjQ d₂ x) = conjQ (d₂ d₁) x`;
* H3 in this vocabulary: for `d' ∈ KW` with `(d' : G) = t d t`,
  `fcan (conjQ d x) = conjQ d' (fcan x)` (and the same for `gcan`);
* elements of `W` are centralised by `t`.

Nothing here is specific to `ω`.
-/
import Mathlib
import Submission.Work.PSU3.StageC.FSuz
import Submission.Work.PSU3.FMap.torusAct_mul
import Submission.Work.PSU3.FMap.torusAct_bijective

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness
open Work.PSU3.StageB

namespace Work.PSU3.StageC

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- The right action of `d ∈ fr.KW ≤ H` on `x ∈ Q`: `x ↦ d⁻¹ x d`. -/
noncomputable def conjQ (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (d : fr.KW) (x : Q) : Q :=
  ⟨(d : G)⁻¹ * (x : G) * (d : G), by
    have h := Work.RankOneUniqueness.conj_mem_of_mem hS.split
      (H.inv_mem ((Work.RankOneUniqueness.twoPoint_le_left H t) (fr.KW_le d.2))) x.2
    simpa using h⟩

@[simp] theorem conjQ_coe (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (d : fr.KW) (x : Q) :
    ((conjQ hS fr d x : Q) : G) = (d : G)⁻¹ * (x : G) * (d : G) := rfl

theorem conjQ_mul (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (d : fr.KW) (x y : Q) :
    conjQ hS fr d (x * y) = conjQ hS fr d x * conjQ hS fr d y := by
  apply Subtype.ext
  simp only [conjQ_coe, Subgroup.coe_mul]
  group

theorem conjQ_one (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (d : fr.KW) : conjQ hS fr d 1 = 1 := by
  apply Subtype.ext
  simp only [conjQ_coe, Subgroup.coe_one]
  group

theorem conjQ_conjQ (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (d₁ d₂ : fr.KW) (x : Q) :
    conjQ hS fr d₁ (conjQ hS fr d₂ x) = conjQ hS fr (d₂ * d₁) x := by
  apply Subtype.ext
  simp only [conjQ_coe, Subgroup.coe_mul]
  group

/-- The conjugation rule of the fine coordinates `e`. -/
theorem e_conjQ (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    (e : Q ≃* SZ (Work.PSU3.E n))
    (heq : ∀ (d : fr.KW) (x y : Q), (y : G) = (d : G)⁻¹ * x * d →
      e y = SZ.torusAct (fr.κ d) (e x))
    (d : fr.KW) (x : Q) : e (conjQ hS fr d x) = SZ.torusAct (fr.κ d) (e x) :=
  heq d x (conjQ hS fr d x) rfl

/-- An element of `W` commutes with `t`. -/
theorem t_conj_of_mem_W (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {d : fr.KW} (hd : (d : G) ∈ Work.ThmF.W H t) : t * (d : G) * t = (d : G) := by
  have ht : t * t = 1 := t_mul_self hS
  have hmem : (d : G) ∈ centD H t := Work.ThmF.W_le_centD H t hd
  have hct : t * (d : G) = (d : G) * t :=
    (Subgroup.mem_centralizer_iff.mp hmem.2) t (by simp)
  rw [hct, mul_assoc, ht, mul_one]

/-- H3 for `fcan`, in the `conjQ` vocabulary: if `(d' : G) = t d t` then
`fcan (conjQ d x) = conjQ d' (fcan x)`. -/
theorem fcan_conjQ_eq (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {d d' : fr.KW} (hd' : (d' : G) = t * (d : G) * t) {x : Q} (hx : (x : G) ≠ 1) :
    fcan hS.split (conjQ hS fr d x) = conjQ hS fr d' (fcan hS.split x) := by
  obtain ⟨xa, hxa, hf, -, -⟩ :=
    Work.PSU3.StageB.canon_conj_fun hS.split hx (⟨d, fr.KW_le d.2⟩ : ↥(twoPoint H t))
  have hxaeq : xa = conjQ hS fr d x := by
    apply Subtype.ext
    rw [hxa]
    simp only [conjQ_coe, Subgroup.coe_mk]
  rw [← hxaeq]
  apply Subtype.ext
  rw [conjQ_coe, hd', hf]

/-- H3 for `gcan`, in the `conjQ` vocabulary. -/
theorem gcan_conjQ_eq (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {d d' : fr.KW} (hd' : (d' : G) = t * (d : G) * t) {x : Q} (hx : (x : G) ≠ 1) :
    gcan hS.split (conjQ hS fr d x) = conjQ hS fr d' (gcan hS.split x) := by
  obtain ⟨xa, hxa, -, hg, -⟩ :=
    Work.PSU3.StageB.canon_conj_fun hS.split hx (⟨d, fr.KW_le d.2⟩ : ↥(twoPoint H t))
  have hxaeq : xa = conjQ hS fr d x := by
    apply Subtype.ext
    rw [hxa]
    simp only [conjQ_coe, Subgroup.coe_mk]
  rw [← hxaeq]
  apply Subtype.ext
  rw [conjQ_coe, hd', hg]

/-- H4 in the `conjQ` vocabulary: `hcan (conjQ d x) = (t d t)⁻¹ hcan x · d`. -/
theorem hcan_conjQ_eq (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {d d' : fr.KW} (hd' : (d' : G) = t * (d : G) * t) {x : Q} (hx : (x : G) ≠ 1) :
    (hcan hS.split (conjQ hS fr d x) : G) =
      (d' : G)⁻¹ * (hcan hS.split x : G) * (d : G) := by
  obtain ⟨xa, hxa, -, -, hh⟩ :=
    Work.PSU3.StageB.canon_conj_fun hS.split hx (⟨d, fr.KW_le d.2⟩ : ↥(twoPoint H t))
  have hxaeq : xa = conjQ hS fr d x := by
    apply Subtype.ext
    rw [hxa]
    simp only [conjQ_coe, Subgroup.coe_mk]
  rw [← hxaeq, hh, hd']

/-- Conjugating an element of `Q₀` by a `KW`-element that fixes `Q₀` pointwise. -/
theorem conjQ_zcQ (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {d : fr.KW} (hd : ∀ y : Work.PSU3.E n, σE y = y → (d : G)⁻¹ * fr.zc y * (d : G) = fr.zc y)
    (y : Work.PSU3.E n) (hy : σE y = y) :
    conjQ hS fr d (zcQ fr y hy) = zcQ fr y hy := by
  apply Subtype.ext
  simpa only [conjQ_coe, zcQ_coe] using hd y hy

/-- If `d` fixes `Q₀` pointwise then so does `d⁻¹`. -/
theorem fix_inv {fr : Work.PSU3.CoarseFrame H Q t n} {d : fr.KW}
    (hd : ∀ y : Work.PSU3.E n, σE y = y → (d : G)⁻¹ * fr.zc y * (d : G) = fr.zc y) :
    ∀ y : Work.PSU3.E n, σE y = y →
      ((d⁻¹ : fr.KW) : G)⁻¹ * fr.zc y * ((d⁻¹ : fr.KW) : G) = fr.zc y := by
  intro y hy
  have h := hd y hy
  have h2 : ((d⁻¹ : fr.KW) : G) = (d : G)⁻¹ := rfl
  rw [h2, inv_inv]
  calc (d : G) * fr.zc y * (d : G)⁻¹
      = (d : G) * ((d : G)⁻¹ * fr.zc y * (d : G)) * (d : G)⁻¹ := by rw [h]
    _ = fr.zc y := by group

/-- `ζ` fixes `Q₀` pointwise. -/
theorem zeta_fix (fr : Work.PSU3.CoarseFrame H Q t n) :
    ∀ y : Work.PSU3.E n, σE y = y → (fr.ζ : G)⁻¹ * fr.zc y * (fr.ζ : G) = fr.zc y :=
  fun y hy => fr.act_zc_ζ y hy

end Work.PSU3.StageC
