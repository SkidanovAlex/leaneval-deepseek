import Mathlib
import Submission.Work.Drive.Whitney.modelPush
import Submission.Work.Drive.PushDisc.landingAssembly

/-!
# M5: the model chart of the Whitney move, and the clause set

`Work.Drive.Whitney.modelPush` (M1) is the *model* move: in the coordinates
`(x,y,u,v) ∈ ℝ × ℝ × E × E` (`E = EuclideanSpace ℝ (Fin k)`) of the model, with the model sheets
`A = {(x,0,u,0)}` and `B = {(x, c x, 0, v)}`, the vertical shear
`ψ (x,y,u,v) = (x, y - 2 * m x * l (‖v‖²), u, v)` is an explicit diffeomorphism whose *moved* points
of `B` are off both `A` and `B` — the "drop direction in which the partner branch is absent".

This module turns M1 into the clause set `Work.Whitney.HasAmbientPushData` under a single geometric
hypothesis, `Work.Drive.Whitney.ModelChartData`: the existence of the *model chart* of the Whitney
move at the two opposite-signed double points.  That hypothesis is M4 of the classical route
(`Drive/NOTES_milnor_model_route.md`): a `C^∞` diffeomorphism `Φ` of `ℝ^{2n}` onto the model space,
carrying a neighbourhood of the two arcs to the model sheets `A`, `B` and the bigon arcs to the
model arcs, with the sheet-2 arc parametrised by a chart `σ` of `M`, together with the two
*stability* conditions which the model chart has to satisfy:

* (`hsheets`) the model slab `{|x| < 3/2, ‖v‖ < 1}` contains no point of `f '' M` other than the two
  model sheets — this is the isolation radius around the chart, transported;
* (`Oo`, `hOfix`, `hOfront`) an open set of model points on which the amplitude vanishes *stably*,
  containing the image of the frontier of `W₀` — in the model this is the union of the neighbourhood
  of the "ends" `{|x| = 3/2}` (where `m = 0`) and of the "wall" `{‖v‖ = 1}` (where `l = 0`).

Everything else — the finger `W₀`, the push `ψ = Φ⁻¹ ∘ mψ ∘ Φ`, its inverse, the identity set, the
placement clause and the non-attainment of the two double values — is *proved here* from M1.

## Main results

* `Work.Drive.Whitney.ModelData.push`: M1 restated for the named model maps `mpsi`, `msigma`.
* `Work.Drive.Whitney.hasAmbientPushData_of_modelChartData`: M4 (as `ModelChartData`) ⟹ the clause
  set `Work.Whitney.HasAmbientPushData`.
* `Work.Drive.Whitney.hasPushSignedSmooth_of_modelChartDataAll`: consequently the target
  `Work.Drive.HasPushSignedSmooth n M` follows from the existence of the model chart for every
  configuration of the target.
-/

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Work.Drive.Whitney

open scoped Manifold ContDiff
open Set Metric

variable {k : ℕ}

set_option linter.unusedVariables false

/-- The model space of the Whitney move: `(x,y,u,v)` with `x, y : ℝ` and `u, v ∈ ℝ^k`. -/
abbrev Mdl (k : ℕ) := ℝ × ℝ × EuclideanSpace ℝ (Fin k) × EuclideanSpace ℝ (Fin k)

/-- The model shear of M1, as a named map. -/
noncomputable def mpsi (m l : ℝ → ℝ) (ξ : Mdl k) : Mdl k :=
  (ξ.1, ξ.2.1 - 2 * m ξ.1 * l (‖ξ.2.2.2‖ ^ 2), ξ.2.2.1, ξ.2.2.2)

/-- Its inverse. -/
noncomputable def msigma (m l : ℝ → ℝ) (ξ : Mdl k) : Mdl k :=
  (ξ.1, ξ.2.1 + 2 * m ξ.1 * l (‖ξ.2.2.2‖ ^ 2), ξ.2.2.1, ξ.2.2.2)

/-- The model sheet `A = {(x,0,u,0)}`. -/
def sheetA : Set (Mdl k) := {ξ | ξ.2.1 = 0 ∧ ξ.2.2.2 = 0}

/-- The model sheet `B = {(x, c x, 0, v)}`. -/
def sheetB (c : ℝ → ℝ) : Set (Mdl k) := {ξ | ξ.2.2.1 = 0 ∧ ξ.2.1 = c ξ.1}

/-- The model region in which the shear moves points: `{|x| < 3/2}` and `{‖v‖ < 1}`. -/
def slabK : Set (Mdl k) := {ξ | |ξ.1| < 3 / 2 ∧ ‖ξ.2.2.2‖ < 1}

/-- The fixed set of the model shear. -/
def fixedSet (m l : ℝ → ℝ) : Set (Mdl k) := {ξ | m ξ.1 * l (‖ξ.2.2.2‖ ^ 2) = 0}

/-- **The hypotheses of the model (M1) on the three model functions.** -/
structure ModelData (k : ℕ) (c m l : ℝ → ℝ) : Prop where
  hc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) c
  hm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) m
  hl : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) l
  hc1 : c 1 = 0
  hcm1 : c (-1) = 0
  hcpos : ∀ x : ℝ, -1 < x → x < 1 → 0 < c x
  hcneg : ∀ x : ℝ, 1 < |x| → c x < 0
  hmbig : ∀ x : ℝ, |x| ≤ 1 → max 0 (c x) + 1 ≤ m x
  hmsmall : ∀ x : ℝ, 3 / 2 ≤ |x| → m x = 0
  hmnn : ∀ x : ℝ, 0 ≤ m x
  hl0 : l 0 = 1
  hlsmall : ∀ t : ℝ, 1 ≤ t → l t = 0
  hlnn : ∀ t : ℝ, 0 ≤ l t

/-- **M1, restated for the named model maps.** -/
theorem ModelData.push {k : ℕ} {c m l : ℝ → ℝ} (D : ModelData k c m l) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (mpsi (k := k) m l) ∧
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (msigma (k := k) m l) ∧
    (∀ ξ : Mdl k, msigma m l (mpsi m l ξ) = ξ) ∧
    (∀ ξ : Mdl k, mpsi m l (msigma m l ξ) = ξ) ∧
    (∀ ξ : Mdl k, mpsi m l ξ = ξ ↔ m ξ.1 * l (‖ξ.2.2.2‖ ^ 2) = 0) ∧
    (∀ (x : ℝ) (v : EuclideanSpace ℝ (Fin k)),
      mpsi m l (x, c x, 0, v) = (x, c x - 2 * m x * l (‖v‖ ^ 2), 0, v)) ∧
    (∀ (x : ℝ) (v : EuclideanSpace ℝ (Fin k)), m x ≠ 0 → l (‖v‖ ^ 2) ≠ 0 →
      mpsi m l (x, c x, 0, v) ∉ sheetA ∧ mpsi m l (x, c x, 0, v) ∉ sheetB c) := by
  have h := (modelPush (k := k) c m l D.hc D.hm D.hl D.hc1 D.hcm1 D.hcpos D.hcneg D.hmbig
    D.hmsmall D.hmnn D.hl0 D.hlsmall D.hlnn).2
  obtain ⟨hψ, hσ, h1, h2, h3, h4, h5⟩ := h
  exact ⟨hψ, hσ, h1, h2, h3, h4, h5⟩

/-- The model double point at `x = -1` (`f p₂`, and also `f p₁`). -/
def modelLeft : Mdl k := ((-1 : ℝ), 0, 0, 0)

/-- The model double point at `x = 1` (`f q₂`, and also `f q₁`). -/
def modelRight : Mdl k := ((1 : ℝ), 0, 0, 0)

/-- **The model shear moves the double point off both model double values.** -/
theorem ModelData.push_ne_left {k : ℕ} {c m l : ℝ → ℝ} (D : ModelData k c m l) {ξ : Mdl k} (hξ : ξ ∈ sheetB c) :
    mpsi m l ξ ≠ modelLeft (k := k) := by
  intro h
  have h1 : ξ.1 = -1 := by
    simpa [modelLeft, mpsi] using congrArg (fun z : Mdl k => z.1) h
  have h4 : ξ.2.2.2 = (0 : EuclideanSpace ℝ (Fin k)) := by
    simpa [modelLeft, mpsi] using congrArg (fun z : Mdl k => z.2.2.2) h
  have h2 : ξ.2.1 - 2 * m ξ.1 * l (‖ξ.2.2.2‖ ^ 2) = 0 := by
    simpa [modelLeft, mpsi] using congrArg (fun z : Mdl k => z.2.1) h
  have hξ1 : ξ.2.1 = 0 := by
    have hb := hξ.2
    rw [h1, D.hcm1] at hb
    exact hb
  have hl1 : l (‖(0 : EuclideanSpace ℝ (Fin k))‖ ^ 2) = 1 := by simp [D.hl0]
  rw [h4, hl1, h1, hξ1] at h2
  have hm : m (-1) ≠ 0 := by
    have hb := D.hmbig (-1) (by norm_num)
    rw [D.hcm1, max_eq_right le_rfl] at hb
    linarith
  exact hm (by linarith [h2])

/-- **The model shear moves the double point off both model double values** (second one). -/
theorem ModelData.push_ne_right {k : ℕ} {c m l : ℝ → ℝ} (D : ModelData k c m l) {ξ : Mdl k} (hξ : ξ ∈ sheetB c) :
    mpsi m l ξ ≠ modelRight (k := k) := by
  intro h
  have h1 : ξ.1 = 1 := by
    simpa [modelRight, mpsi] using congrArg (fun z : Mdl k => z.1) h
  have h4 : ξ.2.2.2 = (0 : EuclideanSpace ℝ (Fin k)) := by
    simpa [modelRight, mpsi] using congrArg (fun z : Mdl k => z.2.2.2) h
  have h2 : ξ.2.1 - 2 * m ξ.1 * l (‖ξ.2.2.2‖ ^ 2) = 0 := by
    simpa [modelRight, mpsi] using congrArg (fun z : Mdl k => z.2.1) h
  have hξ1 : ξ.2.1 = 0 := by
    have hb := hξ.2
    rw [h1, D.hc1] at hb
    exact hb
  have hl1 : l (‖(0 : EuclideanSpace ℝ (Fin k))‖ ^ 2) = 1 := by simp [D.hl0]
  rw [h4, hl1, h1, hξ1] at h2
  have hm : m 1 ≠ 0 := by
    have hb := D.hmbig 1 (by norm_num)
    rw [D.hc1, max_eq_right le_rfl] at hb
    linarith
  exact hm (by linarith [h2])

/-- The model slab contains the pushed image of a point of `B` in the `{|x| < 3/2}` region. -/
theorem ModelData.push_mem_slab {k : ℕ} {c m l : ℝ → ℝ} (D : ModelData k c m l) {ξ : Mdl k} (hslab : ξ ∈ slabK) :
    mpsi m l ξ ∈ slabK := by
  obtain ⟨h1, h2⟩ := hslab
  refine ⟨by simpa [mpsi] using h1, ?_⟩
  simpa [mpsi] using h2


/-- The explicit model constants: `c x = 1 - x²` (vanishing exactly at `±1`), a bump `m` which is
`2` on `[-1,1]` and vanishes for `|x| ≥ 3/2`, and a bump `l` at `0` supported in `[0,1/2]`. -/
theorem ModelData.modelSelf (k : ℕ) :
    ModelData k (fun x => 1 - x ^ 2) (fun x => 2 * Real.smoothTransition (9 / 4 - x ^ 2))
      (fun t => Real.smoothTransition (1 - 2 * t)) := by
  classical
  have hsmooth_m : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : ℝ => 2 * Real.smoothTransition (9 / 4 - x ^ 2)) :=
    contDiff_const.mul ((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp
      (contDiff_const.sub (contDiff_id.pow 2)))
  have hsmooth_l : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun t : ℝ => Real.smoothTransition (1 - 2 * t)) :=
    (Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).comp
      (contDiff_const.sub (contDiff_const.mul contDiff_id))
  refine ⟨?_, hsmooth_m, hsmooth_l, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact contDiff_const.sub (contDiff_id.pow 2)
  · norm_num
  · norm_num
  · intro x h1 h2
    have h : x ^ 2 < 1 := by nlinarith
    linarith
  · intro x hx
    have h : 1 < x ^ 2 := by
      have h2 : 1 < |x| ^ 2 := by nlinarith [abs_nonneg x]
      rwa [sq_abs] at h2
    linarith
  · intro x hx
    have hsq : x ^ 2 ≤ 1 := by
      have h2 : |x| ^ 2 ≤ 1 := by nlinarith [abs_nonneg x]
      rwa [sq_abs] at h2
    have h1 : 1 ≤ 9 / 4 - x ^ 2 := by linarith
    rw [Real.smoothTransition.one_of_one_le h1]
    have hmax : max 0 (1 - x ^ 2) = 1 - x ^ 2 := max_eq_right (by nlinarith [sq_nonneg x])
    rw [hmax]
    nlinarith [sq_nonneg x]
  · intro x hx
    have h2 : (3 / 2 : ℝ) ^ 2 ≤ |x| ^ 2 := by nlinarith [abs_nonneg x]
    have h3 : (9 / 4 : ℝ) ≤ x ^ 2 := by
      rw [sq_abs x] at h2
      linarith
    rw [Real.smoothTransition.zero_of_nonpos (x := 9 / 4 - x ^ 2) (by linarith), mul_zero]
  · intro x
    exact mul_nonneg (by norm_num) (Real.smoothTransition.nonneg _)
  · rw [Real.smoothTransition.one_of_one_le (show (1 : ℝ) ≤ 1 - 2 * 0 by norm_num)]
  · intro t ht
    exact Real.smoothTransition.zero_of_nonpos (x := 1 - 2 * t) (by linarith)
  · intro t
    exact Real.smoothTransition.nonneg _

/-- **The model constants exist.** -/
theorem ModelData.exists (k : ℕ) : ∃ (c m l : ℝ → ℝ), ModelData k c m l :=
  ⟨_, _, _, ModelData.modelSelf k⟩

/-- For the explicit model constants, the amplitude `l` vanishes on `{t ≥ 1/2}`. -/
theorem modelSelf_l_eq_zero {t : ℝ} (ht : 1 / 2 ≤ t) :
    Real.smoothTransition (1 - 2 * t) = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

end Work.Drive.Whitney

namespace Work.Drive.Whitney

open scoped Manifold ContDiff
open Set Metric

/-- **The model chart of the Whitney move (M4).**  All the geometric content of the Whitney move
beyond M1: a `C^∞` diffeomorphism `Φ` of the ambient space `ℝ^{2n}` onto the model space
`ℝ × ℝ × E × E` (`k = n - 1`), the model functions `c, m, l`, a chart `σ` of `M` along the sheet-two
arc, and the two stability conditions (`hsheets`, `Oo`/`hOfix`/`hOfront`).

`Φ` carries the sheet-two arc of the bigon to the model arc `{(x, c x, 0, 0)}`, the sheet-one arc to
`{(x, 0, u, 0)}`, and the two double points to `modelLeft = (-1,0,0,0)` and
`modelRight = (1,0,0,0)`.  -/
structure ModelChartData (n : ℕ) {M : Type*} [TopologicalSpace M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M) where
  /-- the model dimension `k = n - 1` -/
  k : ℕ
  hk : n = k + 1
  c : ℝ → ℝ
  m : ℝ → ℝ
  l : ℝ → ℝ
  hmodel : ModelData k c m l
  /-- the chart of the ambient space onto the model -/
  Φ : EuclideanSpace ℝ (Fin (2 * n)) → Mdl k
  /-- its inverse -/
  Θ : Mdl k → EuclideanSpace ℝ (Fin (2 * n))
  hΦsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ
  hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ
  hΘΦ : ∀ y, Θ (Φ y) = y
  hΦΘ : ∀ ξ, Φ (Θ ξ) = ξ
  /-- the chart of `M` along the sheet-two arc -/
  σ : ℝ × EuclideanSpace ℝ (Fin k) → M
  hσ : ∀ p : ℝ × EuclideanSpace ℝ (Fin k), |p.1| < 3 / 2 → ‖p.2‖ < 1 →
    f (σ p) = Θ (p.1, c p.1, 0, p.2)
  hp₂ : σ ((-1 : ℝ), 0) = p₂
  hq₂ : σ ((1 : ℝ), 0) = q₂
  hW₀o : IsOpen (σ '' {p : ℝ × EuclideanSpace ℝ (Fin k) | |p.1| < 3 / 2 ∧ ‖p.2‖ < 1})
  hW₀W : σ '' {p : ℝ × EuclideanSpace ℝ (Fin k) | |p.1| < 3 / 2 ∧ ‖p.2‖ < 1} ⊆ W
  /-- an open set of model points on which the amplitude vanishes stably -/
  Oo : Set (Mdl k)
  hOo : IsOpen Oo
  hOfix : ∀ ξ ∈ Oo, m ξ.1 * l (‖ξ.2.2.2‖ ^ 2) = 0
  hOfront : f '' frontier (σ '' {p : ℝ × EuclideanSpace ℝ (Fin k) |
    |p.1| < 3 / 2 ∧ ‖p.2‖ < 1}) ⊆ Θ '' Oo
  /-- **the isolation condition**: in the model slab the image of `f` meets only the two sheets -/
  hsheets : ∀ ξ : Mdl k, |ξ.1| < 3 / 2 → ‖ξ.2.2.2‖ < 1 →
    Θ ξ ∈ f '' (Set.univ : Set M) → ξ ∈ sheetA ∪ sheetB c

/-- **M5: the model chart gives the clause set.**  From M4's `ModelChartData` (and the target's
clause-free hypotheses `hclean`, `hsep`, `hfp`, `hfq`, `hp₁p₂`, `hq₁q₂`) the ambient push data of the
Whitney move exists: the finger is the `σ`-chart of the sheet-two arc over the model slab, and the
push is the model shear (M1) transported by `Φ`. -/
theorem hasAmbientPushData_of_modelChartData {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → EuclideanSpace ℝ (Fin (2 * n))) (W : Set M) (p₁ p₂ q₁ q₂ : M)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hp₁p₂ : p₁ ≠ p₂) (hq₁q₂ : q₁ ≠ q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (D : ModelChartData n f W p₁ p₂ q₁ q₂) :
    Work.Whitney.HasAmbientPushData f W p₁ p₂ q₁ q₂ := by
  classical
  obtain ⟨k, _hk, c, m, l, hmodel, Φ, Θ, hΦsm, hΘsm, hΘΦ, hΦΘ, σ, hσ, hp₂, hq₂, hW₀o, hW₀W,
    Oo, hOo, hOfix, hOfront, hsheets⟩ := D
  obtain ⟨hψsm_model, hσsm_model, hσψ', hψσ', hid, hBpush, hoff⟩ := hmodel.push
  -- the diffeomorphism and its inverse
  let H : (Mdl k) ≃ₜ EuclideanSpace ℝ (Fin (2 * n)) :=
    { toFun := Θ, invFun := Φ, left_inv := hΦΘ, right_inv := hΘΦ
      continuous_toFun := hΘsm.continuous, continuous_invFun := hΦsm.continuous }
  have hΘinj : Function.Injective Θ := H.injective
  let reg : Set (ℝ × EuclideanSpace ℝ (Fin k)) := {p | |p.1| < 3 / 2 ∧ ‖p.2‖ < 1}
  let W₀ : Set M := σ '' reg
  let Psi : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun y => Θ (mpsi m l (Φ y))
  let Sig : EuclideanSpace ℝ (Fin (2 * n)) → EuclideanSpace ℝ (Fin (2 * n)) :=
    fun y => Θ (msigma m l (Φ y))
  let O : Set (EuclideanSpace ℝ (Fin (2 * n))) := Θ '' Oo
  -- basic membership of the two double points
  have hmemreg : ((-1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) ∈ reg := by
    refine ⟨by norm_num [reg], ?_⟩; simp
  have hmemreg' : ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) ∈ reg := by
    refine ⟨by norm_num [reg], ?_⟩; simp
  have hmemreg0 : ((0 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) ∈ reg := by
    refine ⟨by norm_num [reg], ?_⟩; simp
  have hp₂W₀ : p₂ ∈ W₀ := ⟨_, hmemreg, hp₂⟩
  have hq₂W₀ : q₂ ∈ W₀ := ⟨_, hmemreg', hq₂⟩
  have hleft : f p₂ = Θ (modelLeft (k := k)) := by
    rw [← hp₂, hσ ((-1 : ℝ), 0) (by norm_num [reg]) (by simp), modelLeft]
    simp [hmodel.hcm1]
  have hright : f q₂ = Θ (modelRight (k := k)) := by
    rw [← hq₂, hσ ((1 : ℝ), 0) (by norm_num [reg]) (by simp), modelRight]
    simp [hmodel.hc1]
  -- the sheet-two membership of the model image of a point of the finger
  have hsheetB : ∀ p ∈ reg, Φ (f (σ p)) ∈ sheetB c := by
    intro p hp
    have h : Φ (f (σ p)) = (p.1, c p.1, 0, p.2) := by
      rw [hσ p hp.1 hp.2, hΦΘ]
    rw [h]
    exact ⟨rfl, rfl⟩
  have hslab : ∀ p ∈ reg, Φ (f (σ p)) ∈ slabK := by
    intro p hp
    have h : Φ (f (σ p)) = (p.1, c p.1, 0, p.2) := by
      rw [hσ p hp.1 hp.2, hΦΘ]
    rw [h]
    exact ⟨hp.1, hp.2⟩
  -- the two double points are not in the finger
  have hp₁W₀ : p₁ ∉ W₀ := by
    rintro ⟨p, hpreg, hpx⟩
    have h1 : Θ (p.1, c p.1, 0, p.2) = Θ (modelLeft (k := k)) := by
      rw [← hσ p hpreg.1 hpreg.2, hpx, hfp, hleft]
    have h2 : (p.1, c p.1, 0, p.2) = (modelLeft (k := k)) := hΘinj h1
    have hp : p = ((-1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) := by
      have h3 : p.1 = (-1 : ℝ) := by
        have := congrArg (fun ξ : Mdl k => ξ.1) h2; simpa [modelLeft] using this
      have h4 : p.2 = (0 : EuclideanSpace ℝ (Fin k)) := by
        have := congrArg (fun ξ : Mdl k => ξ.2.2.2) h2; simpa [modelLeft] using this
      exact Prod.ext h3 h4
    exact hp₁p₂ (hpx.symm.trans (by rw [hp]; exact hp₂))
  have hq₁W₀ : q₁ ∉ W₀ := by
    rintro ⟨p, hpreg, hpx⟩
    have h1 : Θ (p.1, c p.1, 0, p.2) = Θ (modelRight (k := k)) := by
      rw [← hσ p hpreg.1 hpreg.2, hpx, hfq, hright]
    have h2 : (p.1, c p.1, 0, p.2) = (modelRight (k := k)) := hΘinj h1
    have hp : p = ((1 : ℝ), (0 : EuclideanSpace ℝ (Fin k))) := by
      have h3 : p.1 = (1 : ℝ) := by
        have := congrArg (fun ξ : Mdl k => ξ.1) h2; simpa [modelRight] using this
      have h4 : p.2 = (0 : EuclideanSpace ℝ (Fin k)) := by
        have := congrArg (fun ξ : Mdl k => ξ.2.2.2) h2; simpa [modelRight] using this
      exact Prod.ext h3 h4
    exact hq₁q₂ (hpx.symm.trans (by rw [hp]; exact hq₂))
  have hOo' : IsOpen O := H.isOpenMap Oo hOo
  -- the push is the identity off the fixed set
  have hOid : ∀ y ∈ O, Psi y = y := by
    rintro y ⟨ξ, hξO, rfl⟩
    have hmp : mpsi m l ξ = ξ := (hid ξ).mpr (hOfix ξ hξO)
    show Θ (mpsi m l (Φ (Θ ξ))) = Θ ξ
    rw [hΦΘ, hmp]
  have hσψ : ∀ y, Sig (Psi y) = y := by
    intro y
    show Θ (msigma m l (Φ (Θ (mpsi m l (Φ y))))) = y
    rw [hΦΘ, hσψ', hΘΦ]
  have hψσ : ∀ y, Psi (Sig y) = y := by
    intro y
    show Θ (mpsi m l (Φ (Θ (msigma m l (Φ y))))) = y
    rw [hΦΘ, hψσ', hΘΦ]
  have hPsi_sm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) Psi :=
    (hΘsm.comp (hψsm_model.comp hΦsm)).contMDiff
  have hSig_sm : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) Sig :=
    (hΘsm.comp (hσsm_model.comp hΦsm)).contMDiff
  -- the placement clause
  have hland : ∀ x ∈ W₀, Psi (f x) ≠ f x →
      Psi (f x) ∈ f '' W₀ ∪ (f '' (Set.univ : Set M))ᶜ := by
    rintro x ⟨p, hpreg, hpx⟩ hmov
    refine Or.inr ?_
    intro hmem
    have hξ : Φ (f x) = (p.1, c p.1, 0, p.2) := by
      rw [← hpx, hσ p hpreg.1 hpreg.2, hΦΘ]
    have hsl : Φ (f x) ∈ slabK := by rw [hξ]; exact ⟨hpreg.1, hpreg.2⟩
    have hmem' : Θ (mpsi m l (Φ (f x))) ∈ f '' (Set.univ : Set M) := by
      simpa [Psi] using hmem
    have hslab' : mpsi m l (Φ (f x)) ∈ slabK := hmodel.push_mem_slab hsl
    have hsheetunion := hsheets (mpsi m l (Φ (f x))) hslab'.1 hslab'.2 hmem'
    have hprod' : m p.1 * l (‖p.2‖ ^ 2) ≠ 0 := by
      intro h
      have hfix : mpsi m l (Φ (f x)) = Φ (f x) := (hid (Φ (f x))).mpr (by rw [hξ]; exact h)
      have hmov_eq : Psi (f x) = f x := by
        show Θ (mpsi m l (Φ (f x))) = f x
        rw [hfix, hΘΦ]
      exact hmov hmov_eq
    have hmx : m p.1 ≠ 0 := fun h => hprod' (by rw [h, zero_mul])
    have hlv : l (‖p.2‖ ^ 2) ≠ 0 := fun h => hprod' (by rw [h, mul_zero])
    have hoff' := hoff p.1 p.2 hmx hlv
    rw [← hξ] at hoff'
    exact hsheetunion.elim (fun h => hoff'.1 h) (fun h => hoff'.2 h)
  -- the two double values are not attained
  have hnonat : ∀ x ∈ W₀, Psi (f x) ≠ f p₂ ∧ Psi (f x) ≠ f q₂ := by
    rintro x ⟨p, hpreg, hpx⟩
    have hξ : Φ (f x) = (p.1, c p.1, 0, p.2) := by
      rw [← hpx, hσ p hpreg.1 hpreg.2, hΦΘ]
    have hB : Φ (f x) ∈ sheetB c := by rw [hξ]; exact ⟨rfl, rfl⟩
    constructor
    · intro hcon
      have h1 : Θ (mpsi m l (Φ (f x))) = Θ (modelLeft (k := k)) := by
        rw [← hleft]
        simpa [Psi] using hcon
      exact hmodel.push_ne_left hB (hΘinj h1)
    · intro hcon
      have h1 : Θ (mpsi m l (Φ (f x))) = Θ (modelRight (k := k)) := by
        rw [← hright]
        simpa [Psi] using hcon
      exact hmodel.push_ne_right hB (hΘinj h1)
  exact Work.Drive.PushDisc.hasAmbientPushData_of_landing f W p₁ p₂ q₁ q₂ hfp hfq hclean hsep
    W₀ hW₀o hW₀W hp₂W₀ hq₂W₀ hp₁W₀ hq₁W₀ O hOo' hOfront Psi Sig hOid hσψ hψσ hPsi_sm hSig_sm
    hland hnonat

end Work.Drive.Whitney

namespace Work.Drive.Whitney

open scoped Manifold ContDiff
open Set Metric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [CompactSpace M] [SecondCountableTopology M]

/-- **The model chart exists for every configuration of the target** (M4 of the classical route,
quantified over the target's hypotheses).  This is the *single* remaining geometric input of the
compact `n ≥ 3` case in the model-chart form; it is the content of Milnor ("Lectures on the
h-cobordism theorem") §6, steps 1–4: the Whitney disc, the framing of the normal bundle over it
(where `OppositeType` is spent), and the straightening of the two sheets along the disc. -/
def ModelChartDataAll (n : ℕ) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [CompactSpace M] [SecondCountableTopology M] : Prop :=
  ∀ (hn : 3 ≤ n) (f : M → EuclideanSpace ℝ (Fin (2 * n)))
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (himm : ∀ y, Function.Injective (mfderiv
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f y))
    (W : Set M) (hWopen : IsOpen W) (hWcpt : IsCompact (closure W))
    (p₁ p₂ q₁ q₂ : M)
    (hW₁ : p₁ ∈ W) (hW₂ : p₂ ∈ W) (hW₃ : q₁ ∈ W) (hW₄ : q₂ ∈ W)
    (hp₁p₂ : p₁ ≠ p₂) (hq₁q₂ : q₁ ≠ q₂)
    (hp₁q₁ : p₁ ≠ q₁) (hp₁q₂ : p₁ ≠ q₂) (hp₂q₁ : p₂ ≠ q₁) (hp₂q₂ : p₂ ≠ q₂)
    (hfp : f p₁ = f p₂) (hfq : f q₁ = f q₂)
    (hclean : ∀ y z : M, y ∈ W → z ∈ W → f y = f z →
      y = z ∨ (y = p₁ ∧ z = p₂) ∨ (y = p₂ ∧ z = p₁) ∨ (y = q₁ ∧ z = q₂) ∨
        (y = q₂ ∧ z = q₁))
    (hsep : ∀ y z : M, y ∈ W → z ∉ W → f y ≠ f z)
    (htransP : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f p₂).range = ⊤)
    (htransQ : (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₁).range ⊔
      (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (2 * n)))) f q₂).range = ⊤)
    (γ₁ γ₂ : ℝ → M) (hγ₁ : Continuous γ₁) (hγ₂ : Continuous γ₂)
    (hγ₁0 : γ₁ 0 = p₁) (hγ₁1 : γ₁ 1 = q₁) (hγ₂0 : γ₂ 0 = p₂) (hγ₂1 : γ₂ 1 = q₂)
    (hγW₁ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₁ t ∈ W)
    (hγW₂ : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → γ₂ t ∈ W)
    (hγ₁inj : Set.InjOn γ₁ (Set.Icc (0 : ℝ) 1))
    (hγ₂inj : Set.InjOn γ₂ (Set.Icc (0 : ℝ) 1))
    (hγ₁smooth : ContMDiff 𝓘(ℝ, ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ₁)
    (hγ₂smooth : ContMDiff 𝓘(ℝ, ℝ) (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) γ₂)
    (hγ₁imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv 𝓘(ℝ, ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₁ t))
    (hγ₂imm : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      Function.Injective (mfderiv 𝓘(ℝ, ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) γ₂ t))
    (hγdisj : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      γ₁ s = γ₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hγend : ∀ s : ℝ, s ∈ Set.Icc (0 : ℝ) 1 → ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 →
      f (γ₁ s) = f (γ₂ t) → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1))
    (hsign : Work.Whitney.OppositeType f γ₁ γ₂ p₁ p₂ q₁ q₂),
    Nonempty (ModelChartData n f W p₁ p₂ q₁ q₂)

/-- **The target from the model chart.**  The whole compact `n ≥ 3` case of the signed smooth push
follows from the existence of the model chart for every configuration. -/
theorem hasPushSignedSmooth_of_modelChartDataAll (h : ModelChartDataAll n M) :
    Work.Drive.HasPushSignedSmooth n M := by
  intro hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂ hp₁q₁ hp₁q₂
    hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1 hγW₁ hγW₂
    hγ₁inj hγ₂inj hγ₁smooth hγ₂smooth hγ₁imm hγ₂imm hγdisj hγend hsign
  obtain ⟨D⟩ := h hn f hf himm W hWopen hWcpt p₁ p₂ q₁ q₂ hW₁ hW₂ hW₃ hW₄ hp₁p₂ hq₁q₂ hp₁q₁
    hp₁q₂ hp₂q₁ hp₂q₂ hfp hfq hclean hsep htransP htransQ γ₁ γ₂ hγ₁ hγ₂ hγ₁0 hγ₁1 hγ₂0 hγ₂1
    hγW₁ hγW₂ hγ₁inj hγ₂inj hγ₁smooth hγ₂smooth hγ₁imm hγ₂imm hγdisj hγend hsign
  exact hasAmbientPushData_of_modelChartData f W p₁ p₂ q₁ q₂ hfp hfq hp₁p₂ hq₁q₂ hclean hsep D

end Work.Drive.Whitney
