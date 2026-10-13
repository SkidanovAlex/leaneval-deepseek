import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.signConst_decomposition
import Submission.Work.WilG4a.fiber_endpoints
import Submission.Work.WilG4a.affine_comb_graph_mem
import Submission.Work.WilG4a.affine_reparam_bound
import Submission.Work.WilG4a.ite_graph_mem
import Submission.Work.WilG4a.ChartUnion
import Submission.Work.WilG4a.Bounds
import Submission.Work.WilG4a.mvpoly_eval_mono
import Submission.Work.WilG4a.locGoodDefs
import Submission.Work.WilG4a.locGoodSet_mem
import Submission.Work.WilG4a.locFallbackChart
import Submission.Work.WilG4a.f1affine1_of_signConst
import Submission.Work.WilG4a.cell_charts_with_fallback
import Submission.Work.WilG4a.f1affine1_of_parts_ge
import Submission.Work.WilG4a.trivial_fallback
import Submission.Work.WilG4a.f1affine_of_f1affine1
import Submission.Work.WilG4a.F1AffineW
import Submission.Work.WilG4a.CD.badLocus_interior_eq_empty
import Submission.Work.WilG4a.CD.slice_bad_finite

set_option autoImplicit false
noncomputable section

namespace Work.WilG4a

open Classical
open WilkiesDesign

/-! ## Structural facts about the joint smooth locus

These are the propositional (non-`Ω`) facts that any proof of the induction step consumes:
a cell with nonempty interior has no bad point (so all members are `C^{r+2}` on it), the joint
bad *fibre* over a parameter is finite, and the joint `C^{r+2}` locus is open. -/

/-- **A thick cell is good.**  A cell of the sign-const decomposition with nonempty interior is
disjoint from every bad locus, so at each of its points every member is `C^{r+2}`. -/
theorem thick_cell_smooth {p k r : ℕ} {F : Fin k → (Fin p → ℝ) → ℝ → ℝ}
    {κ : Set (Fin (p + 1) → ℝ)}
    (hint : (interior κ).Nonempty)
    (hE : ∀ (i : Fin k) (j : ℕ), j ≤ r + 2 →
      Disjoint κ (badLocus (F i) j) ∨ κ ⊆ badLocus (F i) j)
    (hbad : ∀ i : Fin k, interior (badLocus (F i) (r + 2)) = ∅) :
    ∀ z ∈ κ, ∀ i : Fin k, ContDiffAt ℝ (r + 2) (famFun (F i)) z := by
  intro z hz i
  rcases hE i (r + 2) le_rfl with hdisj | hsub
  · have : z ∉ badLocus (F i) (r + 2) := fun h => (Set.disjoint_left.mp hdisj) hz h
    rw [CD.badLocus_eq_compl_contDiffAt] at this
    simpa using this
  · exfalso
    obtain ⟨w, hw⟩ := hint
    have : w ∈ interior (badLocus (F i) (r + 2)) := interior_mono hsub hw
    rw [hbad i] at this
    exact this

/-- The joint bad fibre of a family over a parameter is finite: each member's slice has only
finitely many points where it fails to be `C^{r+2}`. -/
theorem joint_bad_fibre_finite (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    {p F0 D r k : ℕ} (F : Fin k → (Fin p → ℝ) → ℝ → ℝ)
    (hf : ∀ i, graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) (l : Fin p → ℝ) :
    {x : ℝ | ∃ i : Fin k, ¬ ContDiffAt ℝ (r + 2) (fun y : ℝ => F i l y) x}.Finite := by
  have hset : {x : ℝ | ∃ i : Fin k, ¬ ContDiffAt ℝ (r + 2) (fun y : ℝ => F i l y) x}
      = ⋃ i : Fin k, {x : ℝ | ¬ ContDiffAt ℝ (r + 2) (fun y : ℝ => F i l y) x} := by
    ext x
    simp
  rw [hset]
  exact Set.finite_iUnion (fun i => CD.slice_bad_finite S hcd hder (F i) (hf i) l (r + 2))

/-- The joint `C^{r+2}` locus of a family is open. -/
theorem joint_smooth_open {p r k : ℕ} (F : Fin k → (Fin p → ℝ) → ℝ → ℝ) :
    IsOpen {z : Fin (p + 1) → ℝ | ∀ i : Fin k, ContDiffAt ℝ (r + 2) (famFun (F i)) z} := by
  rw [show {z : Fin (p + 1) → ℝ | ∀ i : Fin k, ContDiffAt ℝ (r + 2) (famFun (F i)) z}
      = ⋂ i : Fin k, {z : Fin (p + 1) → ℝ | ContDiffAt ℝ (r + 2) (famFun (F i)) z} from by
    ext z; simp]
  exact isOpen_iInter_of_finite (fun i => CD.isOpen_contDiffAt_famFun (F i) (r + 2))

/-!
## The corrected target `F1AffineW` (lead's restatement)

The frozen `F1Affine`/`F1Affine1` demand `0 < β l` at *every* `l ∈ Λ`, which is false for
families whose kinks sweep across `I` (the project lead's audit, `sources/wilkiesG4/`).  The
corrected statement `Work.WilG4a.F1AffineW` (lead file `F1AffineW.lean`) allows `β l = 0` — a
constant chart, exactly the device the paper uses for the degenerate cells — while still
requiring the `ε`-cover to be achieved by charts with `β > 0`, and keeping the image inside
`(0,1)`.

The proof below is:

* `Work.WilG4a.f1affine1_ge_all` (`f1affine1_of_parts_ge.lean`), the corrected statement in
  `ℝ`-coordinates (`β ≥ 0`, no image condition), proved from the established parts
  `trivial_global_chart_ge`, `cell_charts_with_fallback_ge`, `near_nondegen_fibre_at`,
  `eval_add_const_bound`;
* a **repair** of the per-chart conditions: replacing `(α, β)` by its gluing with the trivial
  chart `(1/2, 0)` along the case set `{l | 0 < β l}` makes the image condition automatic
  (where `β > 0` the image is `(α l, α l + β l) ⊆ (0,1)` from `0 ≤ α`, `α + β ≤ 1`; where
  `β l = 0` the chart *is* `(1/2, 0)`), at the cost of one `ite` gluing per coefficient — a
  constant `Ω`-cost, independent of `D, r, k`;
* the coordinate transfer `Fin 1 → ℝ ↦ ℝ` of `f1affine_of_f1affine1.lean`.

### Follow-up: the restatements downstream

The old (false) `F1Affine1`-shaped `f1affine1_all` was consumed by
`Submission/Work/WilG4a/Base.lean` (`G4_base_proved : FLem S p 1 ∧ F1Affine S p`); since the
frozen `F1Affine` is the false statement, that file can no longer be compiled and must be
re-wired in a follow-up (its `FLem` half needs the `β ≥ 0` variant of `fleem1_of_parts`, which
consumes `∀ q, F1Affine1 S q` and has to be relaxed to `F1AffineW` in the same way as
`f1affine1_of_parts` was relaxed here).  Nothing else in the workspace imports `Base.lean`.

The `Work.WilG4c` files that mention `F1Affine` (`ChartsH1`, `G4step`, `StepH1Out`, …) take the
frozen statement as a *hypothesis*, so they remain valid as conditional statements.
-/

/-! ## The `W` per-chart conditions in `ℝ`-coordinates -/

/-- The corrected per-chart conditions in `ℝ`-coordinates: `Chart1Ge` with the additional
requirement that the chart maps `I` into `I`. -/
def Chart1W (S : SOMin) (p : ℕ) (a bD : ℕ) (Λ : Set (Fin p → ℝ)) (k r : ℕ)
    (F : Fin k → (Fin p → ℝ) → ℝ → ℝ) (α β : (Fin p → ℝ) → ℝ) : Prop :=
  WilkiesDesign.graphOf α ∈ S.Ω a bD (p + 1) ∧
  WilkiesDesign.graphOf β ∈ S.Ω a bD (p + 1) ∧
  ∀ l ∈ Λ, 0 ≤ β l ∧ 0 ≤ α l ∧ α l + β l ≤ 1 ∧
    (∀ t ∈ I, α l + β l * t ∈ I) ∧
    ∀ i, ContDiffOn ℝ r (fun t : ℝ => F i l (α l + β l * t)) I ∧
      ∀ m ≤ r, ∀ t ∈ I, |iteratedDeriv m (fun t : ℝ => F i l (α l + β l * t)) t| ≤ 1

/-- The corrected target in `ℝ`-coordinates (`F1AffineGe` with the `W` per-chart conditions). -/
def F1AffineW1 (S : SOMin) (p : ℕ) : Prop :=
  ∀ F0 : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
    ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
    ∀ (Λ : Set (Fin p → ℝ)) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ),
      (∀ i, graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) →
      (∀ i, ∀ l ∈ Λ, ∀ x ∈ I, F i l x ∈ I) →
      ∃ Φ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ)),
        (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
        (∀ αβ ∈ Φ, Chart1W S p a (MvPolynomial.eval ![D, r] b) Λ k r F αβ.1 αβ.2) ∧
        (∀ l ∈ Λ, ∀ x ∈ I, ∃ αβ ∈ Φ, 0 < αβ.2 l ∧ ∃ t ∈ I,
          |αβ.1 l + αβ.2 l * t - x| < ε)

/-! ## The repair: gluing the charts with the trivial chart along `0 < β l` -/

/-- The case set of the repair: the parameters where the chart is non-degenerate. -/
def glueCase {p : ℕ} (β : (Fin p → ℝ) → ℝ) : Set (Fin p → ℝ) := {l | 0 < β l}

/-- The repaired `α`: glued with the constant `1/2` where `β` vanishes. -/
def glueA {p : ℕ} (α β : (Fin p → ℝ) → ℝ) : (Fin p → ℝ) → ℝ :=
  iteFun (glueCase β) α (fun _ => (1 / 2 : ℝ))

/-- The repaired `β`: glued with the constant `0` where `β` vanishes. -/
def glueB {p : ℕ} (β : (Fin p → ℝ) → ℝ) : (Fin p → ℝ) → ℝ :=
  iteFun (glueCase β) β (fun _ => (0 : ℝ))

@[simp] theorem glueCase_mem {p : ℕ} {β : (Fin p → ℝ) → ℝ} {l : Fin p → ℝ} :
    l ∈ glueCase β ↔ 0 < β l := Iff.rfl

@[simp] theorem glueA_of_pos {p : ℕ} {α β : (Fin p → ℝ) → ℝ} {l : Fin p → ℝ} (h : 0 < β l) :
    glueA α β l = α l := by
  simp [glueA, iteFun, glueCase, h]

@[simp] theorem glueA_of_nonpos {p : ℕ} {α β : (Fin p → ℝ) → ℝ} {l : Fin p → ℝ}
    (h : ¬ 0 < β l) : glueA α β l = 1 / 2 := by
  simp [glueA, iteFun, glueCase, h]

@[simp] theorem glueB_of_pos {p : ℕ} {β : (Fin p → ℝ) → ℝ} {l : Fin p → ℝ} (h : 0 < β l) :
    glueB β l = β l := by
  simp [glueB, iteFun, glueCase, h]

@[simp] theorem glueB_of_nonpos {p : ℕ} {β : (Fin p → ℝ) → ℝ} {l : Fin p → ℝ}
    (h : ¬ 0 < β l) : glueB β l = 0 := by
  simp [glueB, iteFun, glueCase, h]

theorem glueA_eq_iteFun {p : ℕ} (α β : (Fin p → ℝ) → ℝ) :
    glueA α β = iteFun (glueCase β) α (fun _ => (1 / 2 : ℝ)) := rfl

theorem glueB_eq_iteFun {p : ℕ} (β : (Fin p → ℝ) → ℝ) :
    glueB β = iteFun (glueCase β) β (fun _ => (0 : ℝ)) := rfl

/-- **Pointwise part of the repair.**  If `(α, β)` satisfies the (β ≥ 0) chart conditions at
every `l ∈ Λ` and the family takes its values in `I`, then the glued pair `(glueA α β, glueB β)`
satisfies the pointwise `W` conditions: `β ≥ 0`, `α ≥ 0`, `α + β ≤ 1`, the image of `I` lies in
`I`, and every composite is `C^r` with unit derivative bounds. -/
theorem glue_chart_conditions {p k r : ℕ} {F : Fin k → (Fin p → ℝ) → ℝ → ℝ}
    {α β : (Fin p → ℝ) → ℝ} {Λ : Set (Fin p → ℝ)}
    (hI : ∀ i, ∀ l ∈ Λ, ∀ x ∈ I, F i l x ∈ I)
    (h : ∀ l ∈ Λ, 0 ≤ β l ∧ 0 ≤ α l ∧ α l + β l ≤ 1 ∧
      ∀ i, ContDiffOn ℝ r (fun t : ℝ => F i l (α l + β l * t)) I ∧
        ∀ m ≤ r, ∀ t ∈ I, |iteratedDeriv m (fun t : ℝ => F i l (α l + β l * t)) t| ≤ 1) :
    ∀ l ∈ Λ, 0 ≤ glueB β l ∧ 0 ≤ glueA α β l ∧ glueA α β l + glueB β l ≤ 1 ∧
      (∀ t ∈ I, glueA α β l + glueB β l * t ∈ I) ∧
      ∀ i, ContDiffOn ℝ r (fun t : ℝ => F i l (glueA α β l + glueB β l * t)) I ∧
        ∀ m ≤ r, ∀ t ∈ I,
          |iteratedDeriv m (fun t : ℝ => F i l (glueA α β l + glueB β l * t)) t| ≤ 1 := by
  intro l hl
  by_cases hβ : 0 < β l
  · obtain ⟨h0β, h0α, hsum, hcond⟩ := h l hl
    rw [glueA_of_pos hβ, glueB_of_pos hβ]
    refine ⟨h0β, h0α, hsum, fun t ht => ⟨?_, ?_⟩, hcond⟩
    · have := mul_pos hβ ht.1
      linarith
    · have := mul_lt_mul_of_pos_left ht.2 hβ
      linarith
  · obtain ⟨h0β, -, -, -⟩ := h l hl
    have hβ0 : β l = 0 := le_antisymm (le_of_not_gt hβ) h0β
    rw [glueA_of_nonpos hβ, glueB_of_nonpos hβ]
    refine ⟨le_rfl, by norm_num, by norm_num, fun t ht => by norm_num, fun i => ?_⟩
    have hconst : (fun t : ℝ => F i l ((1 / 2 : ℝ) + 0 * t)) = fun _ : ℝ => F i l (1 / 2) := by
      funext t; norm_num
    have hhalf : (1 / 2 : ℝ) ∈ I := by norm_num [I]
    rw [hconst]
    refine ⟨contDiffOn_const, fun m hm t ht => ?_⟩
    rw [iteratedDeriv_const]
    split_ifs with hm0
    · rcases Set.mem_Ioo.mp (hI i l hl (1 / 2) hhalf) with ⟨h1, h2⟩
      rw [abs_le]
      exact ⟨by linarith, by linarith⟩
    · norm_num

/-- **`Ω`-membership part of the repair.**  Given the graphs of `α` and `β` at a common format
`F_in` and degree `D`, the graphs of the glued coefficients are `Ω`-definable at a format and
degree depending only on `F_in` and `D` (through a polynomial in `D` and `r`). -/
theorem glue_graph_mem (S : WilkiesDesign.SOMin) (p F_in : ℕ) (hF : p + 3 ≤ F_in) :
    ∃ (aW : ℕ) (bW : MvPolynomial (Fin 2) ℕ),
      ∀ (D r : ℕ) {α β : (Fin p → ℝ) → ℝ},
        WilkiesDesign.graphOf α ∈ S.Ω F_in D (p + 1) →
        WilkiesDesign.graphOf β ∈ S.Ω F_in D (p + 1) →
          WilkiesDesign.graphOf (glueA α β) ∈ S.Ω aW (MvPolynomial.eval ![D, r] bW) (p + 1) ∧
          WilkiesDesign.graphOf (glueB β) ∈ S.Ω aW (MvPolynomial.eval ![D, r] bW) (p + 1) := by
  classical
  -- the `ite` gluing, at the case-set format `F_in + 2`
  obtain ⟨aW, bW, hW⟩ := ite_graph_mem S p (F_in + 2)
  -- the degree of the gluing is `3 * D + 200 ≥ max(2 * D + 103, 3 * D + 200)`; the polynomial
  -- `C 3 * X 0 + C 200` realises `D ↦ 3 * D + 200`
  obtain ⟨bW', hbW'⟩ :=
    exists_eval_comp bW (MvPolynomial.C 3 * MvPolynomial.X 0 + MvPolynomial.C 200 :
      MvPolynomial (Fin 2) ℕ)
  refine ⟨aW, bW', ?_⟩
  intro D r α β hα hβ
  -- the case set `{l | 0 < β l}` is the projection of `graphOf β ∩ {0 < z_last}`
  have hpos : {z : Fin (p + 1) → ℝ | 0 < z (Fin.last p)} ∈ S.Ω F_in 3 (p + 1) := by
    have h := WilG1.Calc.pos_mem (S := S) (2 * D + 100)
      (MvPolynomial.X (Fin.last p) : MvPolynomial (Fin (p + 1)) ℝ)
    have hset : {x : Fin (p + 1) → ℝ | 0 < MvPolynomial.eval x
        (MvPolynomial.X (Fin.last p) : MvPolynomial (Fin (p + 1)) ℝ)}
        = {z : Fin (p + 1) → ℝ | 0 < z (Fin.last p)} := by
      ext z; simp
    rw [hset] at h
    have h3 : ((Polynomial.C
        ((MvPolynomial.X (Fin.last p) : MvPolynomial (Fin (p + 1)) ℝ).totalDegree + 2)).eval
          (2 * D + 100)) = 3 := by
      rw [MvPolynomial.totalDegree_X]
      norm_num
    rw [h3] at h
    exact mono_F_le S h (by omega)
  have hβ' : WilkiesDesign.graphOf β ∈ S.Ω F_in (2 * D + 100) (p + 1) :=
    mono_D_le S hβ (by omega)
  have hinter : (⋂ i : Fin 2, (if i = 0 then {z : Fin (p + 1) → ℝ | 0 < z (Fin.last p)}
      else WilkiesDesign.graphOf β)) ∈
      S.Ω (F_in + 1) (3 + (2 * D + 100)) (p + 1) := by
    have h := S.inter (F := F_in) (n := p + 1) (k := 2)
      (D := fun i : Fin 2 => if i = 0 then 3 else 2 * D + 100)
      (A := fun i : Fin 2 => if i = 0 then {z : Fin (p + 1) → ℝ | 0 < z (Fin.last p)}
        else WilkiesDesign.graphOf β)
      (by
        intro i
        fin_cases i
        · simpa using hpos
        · simpa using hβ')
    have hsum : (∑ i : Fin 2, (if i = 0 then 3 else 2 * D + 100)) = 3 + (2 * D + 100) := by
      rw [Fin.sum_univ_two]; simp
    rwa [hsum] at h
  have hsetid : glueCase β = WilkiesDesign.projLast
      (WilkiesDesign.graphOf β ∩ {z : Fin (p + 1) → ℝ | 0 < z (Fin.last p)}) := by
    ext l
    constructor
    · intro hl
      exact ⟨β l, by simp [WilkiesDesign.graphOf], by simpa using hl⟩
    · rintro ⟨t, ht, h0⟩
      have ht' : t = β l := by simpa [WilkiesDesign.graphOf] using ht
      have h0' : 0 < t := by simpa using h0
      rw [ht'] at h0'
      simpa [glueCase] using h0'
  have hset2 : (⋂ i : Fin 2, (if i = 0 then {z : Fin (p + 1) → ℝ | 0 < z (Fin.last p)}
      else WilkiesDesign.graphOf β))
      = WilkiesDesign.graphOf β ∩ {z : Fin (p + 1) → ℝ | 0 < z (Fin.last p)} := by
    ext z
    simp only [Set.mem_iInter, Fin.forall_fin_two, Set.mem_inter_iff]
    tauto
  have hP0 : WilkiesDesign.projLast
      (⋂ i : Fin 2, (if i = 0 then {z : Fin (p + 1) → ℝ | 0 < z (Fin.last p)}
        else WilkiesDesign.graphOf β)) ∈ S.Ω (F_in + 1 + 1) (3 + (2 * D + 100)) p := by
    exact S.proj (F := F_in + 1) (n := p) (D := 3 + (2 * D + 100)) hinter
  have hP : glueCase β ∈ S.Ω (F_in + 2) (3 * D + 200) p := by
    have h := hP0
    rw [hset2, ← hsetid] at h
    refine mono_FD_le S h (by omega) ?_
    omega
  -- the two branches, raised to the common degree of the gluing
  have hα' : WilkiesDesign.graphOf α ∈ S.Ω (F_in + 2) (3 * D + 200) (p + 1) :=
    mono_FD_le S hα (by omega) (by omega)
  have hc1 : WilkiesDesign.graphOf (fun _ : Fin p → ℝ => (1 / 2 : ℝ)) ∈
      S.Ω (F_in + 2) (3 * D + 200) (p + 1) :=
    mono_FD_le S (graphOf_const_mem S p (1 / 2)) (by omega) (by omega)
  have hc0 : WilkiesDesign.graphOf (fun _ : Fin p → ℝ => (0 : ℝ)) ∈
      S.Ω (F_in + 2) (3 * D + 200) (p + 1) :=
    mono_FD_le S (graphOf_const_mem S p 0) (by omega) (by omega)
  have hmem1 : WilkiesDesign.graphOf (glueA α β) ∈
      S.Ω aW (MvPolynomial.eval ![3 * D + 200, r] bW) (p + 1) := by
    have := hW (D := 3 * D + 200) (r := r) hP hα' hc1
    rwa [← glueA_eq_iteFun] at this
  have hmem2 : WilkiesDesign.graphOf (glueB β) ∈
      S.Ω aW (MvPolynomial.eval ![3 * D + 200, r] bW) (p + 1) := by
    have := hW (D := 3 * D + 200) (r := r) hP (mono_FD_le S hβ (by omega) (by omega)) hc0
    rwa [← glueB_eq_iteFun] at this
  have hg : (MvPolynomial.C 3 * MvPolynomial.X 0 + MvPolynomial.C 200 :
      MvPolynomial (Fin 2) ℕ).eval ![D, r] = 3 * D + 200 := by
    simp [MvPolynomial.eval_add, MvPolynomial.eval_mul]
  refine ⟨?_, ?_⟩
  · rw [← hbW' D r, hg]
    exact hmem1
  · rw [← hbW' D r, hg]
    exact hmem2

/-! ## The corrected target in `ℝ`-coordinates -/

/-- `F1AffineW1` follows from `F1AffineGe` by the repair above.  The repaired family is the image
of the `F1AffineGe` family under the glue map, so the cardinality bound is untouched, and at a
parameter with `β l > 0` the repaired chart *is* the original one, so the cover is unchanged. -/
theorem F1AffineW1_of_F1AffineGe (S : WilkiesDesign.SOMin) (p : ℕ) (h : F1AffineGe S p) :
    F1AffineW1 S p := by
  intro F0
  obtain ⟨a, b, c, hc⟩ := h F0
  -- format at which the case set is formed
  set F_in : ℕ := max a (p + 2) + 2 with hF_in
  -- degree `D ↦ D + 3` (so that the case set's degree `3` is available)
  set b₁ : MvPolynomial (Fin 2) ℕ := b + MvPolynomial.C 3 with hb₁
  obtain ⟨aW, bW, hW⟩ := glue_graph_mem S p F_in (by simp only [hF_in]; omega)
  -- fold the degree shift `D ↦ D + 3` into the output degree polynomial
  obtain ⟨bW₂, hbW₂⟩ := exists_eval_comp bW b₁
  refine ⟨aW, bW₂, c, ?_⟩
  intro D r k ε hε hε1 Λ F hFΩ hFI
  obtain ⟨Φ, hcard, hchart, hcover⟩ := hc D r k ε hε hε1 Λ F hFΩ hFI
  refine ⟨Φ.image (fun αβ => (glueA αβ.1 αβ.2, glueB αβ.2)), ?_, ?_, ?_⟩
  · exact le_trans (by exact_mod_cast Finset.card_image_le) hcard
  · intro αβ' hαβ'
    obtain ⟨αβ, hαβ, hEq⟩ := Finset.mem_image.mp hαβ'
    rw [← hEq]
    obtain ⟨hα, hβ, hpt⟩ := hchart αβ hαβ
    have hα' : WilkiesDesign.graphOf αβ.1 ∈ S.Ω F_in (MvPolynomial.eval ![D, r] b₁) (p + 1) :=
      mono_FD_le S hα (by simp only [hF_in]; omega) (by
        simp only [hb₁, MvPolynomial.eval_add, MvPolynomial.eval_C]
        omega)
    have hβ' : WilkiesDesign.graphOf αβ.2 ∈ S.Ω F_in (MvPolynomial.eval ![D, r] b₁) (p + 1) :=
      mono_FD_le S hβ (by simp only [hF_in]; omega) (by
        simp only [hb₁, MvPolynomial.eval_add, MvPolynomial.eval_C]
        omega)
    obtain ⟨hgr1, hgr2⟩ := hW (D := MvPolynomial.eval ![D, r] b₁) (r := r) hα' hβ'
    refine ⟨?_, ?_, glue_chart_conditions hFI hpt⟩
    · show WilkiesDesign.graphOf (glueA αβ.1 αβ.2) ∈
        S.Ω aW (MvPolynomial.eval ![D, r] bW₂) (p + 1)
      rw [← hbW₂ D r]
      exact hgr1
    · show WilkiesDesign.graphOf (glueB αβ.2) ∈
        S.Ω aW (MvPolynomial.eval ![D, r] bW₂) (p + 1)
      rw [← hbW₂ D r]
      exact hgr2
  · intro l hl x hx
    obtain ⟨αβ, hαβ, hβpos, t, ht, hlt⟩ := hcover l hl x hx
    refine ⟨(glueA αβ.1 αβ.2, glueB αβ.2), Finset.mem_image.mpr ⟨αβ, hαβ, rfl⟩, ?_, t, ht, ?_⟩
    · show 0 < glueB αβ.2 l
      rw [glueB_of_pos hβpos]; exact hβpos
    · show |glueA αβ.1 αβ.2 l + glueB αβ.2 l * t - x| < ε
      rw [glueA_of_pos hβpos, glueB_of_pos hβpos]
      exact hlt

/-! ## The coordinate transfer to the lead's statement -/

/-- The `ℝ`-coordinate corrected statement implies the lead's `F1AffineW` (in
`Fin 1 → ℝ`-coordinates): the two differ only in the coding of the single variable, and the
bridge is the linear isometry `fin1LIE` of `f1affine_of_f1affine1.lean`. -/
theorem F1AffineW_of_F1AffineW1 (S : WilkiesDesign.SOMin) (p : ℕ) (h : F1AffineW1 S p) :
    F1AffineW S p := by
  intro F0
  obtain ⟨a, b, c, hc⟩ := h F0
  refine ⟨a, b, c, ?_⟩
  intro D r k ε hε0 hε1 Λ F hgraph hI
  let F' : Fin k → (Fin p → ℝ) → ℝ → ℝ := fun i l x => F i l (fun _ => x)
  have hgraph' : ∀ i, graphFam (F' i) ∈ S.Ω F0 D (p + 1 + 1) := by
    intro i
    rw [graphFam_eq_famGraph]
    exact hgraph i
  have hI' : ∀ i, ∀ l ∈ Λ, ∀ x ∈ I, F' i l x ∈ I := by
    intro i l hl x hx
    exact hI i l hl (fun _ => x) (by intro j; exact hx)
  obtain ⟨Φ, hcard, hchart, hcover⟩ := hc D r k ε hε0 hε1 Λ F' hgraph' hI'
  refine ⟨Φ, hcard, ?_, ?_⟩
  · intro αβ hαβ
    obtain ⟨hg1, hg2, hl⟩ := hchart αβ hαβ
    refine ⟨hg1, hg2, ?_⟩
    intro l hlΛ
    obtain ⟨hβ, hα, hsum, himg, hcond⟩ := hl l hlΛ
    refine ⟨hβ, hα, hsum, ?_, ?_⟩
    · intro t ht
      exact himg t ht
    · intro i
      obtain ⟨hcd, hbnd⟩ := hcond i
      constructor
      · -- smoothness along the affine chart
        have := contDiffOn_comp_fin1LIE hcd
        simpa [Function.comp_def, F'] using this
      · -- derivative bound along the affine chart
        intro m hm t ht
        have ht0 : t 0 ∈ I := ht 0
        have hb := hbnd m hm (t 0) ht0
        rw [show (fun t : Fin 1 → ℝ => F i l (fun _ => αβ.1 l + αβ.2 l * t 0))
            = (fun s : ℝ => F' i l (αβ.1 l + αβ.2 l * s)) ∘ ⇑fin1LIE from rfl,
          norm_iteratedFDeriv_comp_fin1LIE]
        exact hb
  · intro l hl x hx
    exact hcover l hl x hx

/-! ## The target -/

/-- `F1Affine1` in every parameter dimension — in the corrected (`F1AffineW`) form: from
`hL1` (the sign-constant cell decomposition), `hG3a` and `hG3b`, the affine family lemma holds
with `β ≥ 0` charts whose image lies in `(0,1)`, the `ε`-cover being achieved by charts with
`β > 0`.

Proof: `f1affine1_ge_all` proves the `β ≥ 0` form in `ℝ`-coordinates from the sign-constant
decomposition (indeed from the cell-based construction and the Whitney-cover inputs alone), the
repair `F1AffineW1_of_F1AffineGe` glues each chart with the trivial chart along `{l | 0 < β l}`
(which makes the image condition automatic at an `Ω`-cost independent of `D, r, k`), and
`F1AffineW_of_F1AffineW1` transfers to the `Fin 1 → ℝ` coordinates. -/
theorem f1affine1_all (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (hL1 : ∀ (p F0 : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (cc : MvPolynomial (Fin 3) ℝ), ∀ (D r k : ℕ) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ), (∀ i, Work.WilG4a.graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) → ∃ (m : ℕ), (m : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ)] cc ∧ ∃ (κ : Fin m → Set (Fin (p + 1) → ℝ)), (∀ σ, κ σ ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1)) ∧ (∀ z : Fin (p + 1) → ℝ, ∃ σ, z ∈ κ σ) ∧ (∀ σ σ' : Fin m, σ ≠ σ' → Disjoint (κ σ) (κ σ')) ∧ (∀ σ (l : Fin p → ℝ), (∃ x : ℝ, Fin.snoc l x ∈ κ σ) → (∃ x : ℝ, Work.WilG4a.fibre (κ σ) l = {x}) ∨ (∃ a b : EReal, Work.WilG4a.fibre (κ σ) l = {y : ℝ | a < (y : EReal) ∧ (y : EReal) < b})) ∧ (∀ (σ : Fin m) (i : Fin k) (j : ℕ), j ≤ r + 2 → Disjoint (κ σ) (Work.WilG4a.badLocus (F i) j) ∨ κ σ ⊆ Work.WilG4a.badLocus (F i) j) ∧ (∀ (σ : Fin m) (i : Fin k) (j : ℕ), j ≤ r + 2 → Disjoint (κ σ) (Work.WilG4a.derivZeroSet (F i) j) ∨ κ σ ⊆ Work.WilG4a.derivZeroSet (F i) j) ∧ (∀ (σ : Fin m) (i : Fin k) (j : ℕ), j ≤ r + 1 → ∀ (l : Fin p → ℝ) (u v : ℝ), u < v → Set.Ioo u v ⊆ Work.WilG4a.fibre (κ σ) l → Disjoint (κ σ) (Work.WilG4a.badLocus (F i) (r + 2)) → (Disjoint (κ σ) (Work.WilG4a.derivZeroSet (F i) j) ∨ κ σ ⊆ Work.WilG4a.derivZeroSet (F i) j) → (∀ x ∈ Set.Ioo u v, ContDiffAt ℝ (r + 2) (fun y : ℝ => F i l y) x) ∧ ((∀ x ∈ Set.Ioo u v, 0 ≤ iteratedDeriv j (fun y : ℝ => F i l y) x) ∨ (∀ x ∈ Set.Ioo u v, iteratedDeriv j (fun y : ℝ => F i l y) x ≤ 0)))) (hG3a : ∀ (r : ℕ) (f : ℝ → ℝ), ContDiffOn ℝ (r + 1) f (Set.Ioo 0 1) → (∀ x ∈ Set.Ioo (0 : ℝ) 1, f x ∈ Set.Ioo (0 : ℝ) 1) → (∀ j ≤ r + 1, (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ iteratedDerivWithin j f (Set.Ioo 0 1) x) ∨ (∀ x ∈ Set.Ioo (0 : ℝ) 1, iteratedDerivWithin j f (Set.Ioo 0 1) x ≤ 0)) → ∀ M : ℝ, 1 < M → ∀ j ≤ r, ∀ x ∈ Set.Ioo (0 : ℝ) 1, (j : ℝ) / M < x → x < 1 - j / M → |iteratedDerivWithin j f (Set.Ioo 0 1) x| < M ^ j) (hG3b : ∀ (r : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∃ s : Finset (ℝ × ℝ), (s.card : ℝ) ≤ 8 * (r + 1) * (-Real.log ε + 2) ∧ (∀ p ∈ s, 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1 ∧ (p.2 - p.1) * (r + 1) ≤ min p.1 (1 - p.2)) ∧ (Set.Icc ε (1 - ε) ⊆ (⋃ p ∈ s, Set.Icc p.1 p.2))) : ∀ p : ℕ, Work.WilG4a.F1AffineW S p :=
  fun p => F1AffineW_of_F1AffineW1 S p
    (F1AffineW1_of_F1AffineGe S p
      (f1affine1_ge_all S hcd hder hL1 hG3a hG3b p))

end Work.WilG4a
