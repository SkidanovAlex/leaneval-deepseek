import Mathlib
import Submission.Work.WilE9G.Sard.FlatDefs
import Submission.Work.WilE9G.Sard.engineFlat
import Submission.Work.WilE9G.Sard.levelSetReductionH
import Submission.Work.WilE9G.Sard.straightenReductionH
import Submission.Work.WilE9G.Sard.baseCaseLt
import Submission.Work.WilE9G.Sard.baseCaseEq
import Submission.Work.WilE9G.Sard.glueNull

/-!
# Sard's theorem for real-analytic maps

For a map `f : ℝⁿ → ℝᵐ` which is real-analytic on an open set `U`, the image of the critical
set `{x | fderiv ℝ f x not surjective} ∩ U` is Lebesgue-null.

The organisation, by strong induction on the target dimension `m`:

* `SardSt d j m` — the recursion state: for `F : ℝ^d → ℝ^m` and a set `A ⊆ flatCrit F j`
  (points where `F` is critical and its derivatives of orders `1, …, j-1` vanish) on which `F`
  is analytic, the values of `F` on `A` are *locally* null.
* `SardGB m` — the bounded (global) form: `volume (F '' (critSet F ∩ B)) = 0` for bounded `B`.
* Inside a fixed target dimension the recursion is on the pair (source dimension `d`, flatness
  level `j`), measured by `d - j`: the "deep" branch (`D^j F = 0` on the set) increases `j`, the
  "strict" branch (`D^j F ≠ 0` at the point) strictly decreases `d` (`levelSetReductionH`).
* The rank-positive case (`j = 1`, `d > m`, `fderiv ≠ 0`) is `straightenReductionH`, whose
  Fubini step uses the induction hypothesis for target `m - 1` in bounded form (`SardGB`).
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

open MeasureTheory
open scoped Topology

namespace Work.WilE9G.Sard

/-- The recursion state: the values of `F` on `A ⊆ flatCrit F j` are locally Lebesgue-null.

Here `flatCrit F j = flatSetV F (j-1) ∩ critSet F`: `A` consists of critical points of `F` at
which the derivatives of `F` of orders `1, …, j-1` vanish, and `F` is analytic at every point of
`A`. -/
def SardSt (d j m : ℕ) : Prop :=
  ∀ (F : (Fin d → ℝ) → (Fin m → ℝ)) (A : Set (Fin d → ℝ)), A ⊆ flatCrit F j →
    (∀ x ∈ A, AnalyticAt ℝ F x) → ∀ x₀ ∈ A,
      ∃ δ > 0, MeasureTheory.volume (F '' (A ∩ Metric.ball x₀ δ)) = 0

/-- The bounded ("global") form at target dimension `m`. -/
def SardGB (m : ℕ) : Prop :=
  ∀ (d : ℕ) (F : (Fin d → ℝ) → (Fin m → ℝ)) (B : Set (Fin d → ℝ)), Bornology.IsBounded B →
    (∀ x ∈ B, AnalyticAt ℝ F x) → MeasureTheory.volume (F '' (critSet F ∩ B)) = 0

lemma flatCrit_one_eq {d m : ℕ} (F : (Fin d → ℝ) → (Fin m → ℝ)) : flatCrit F 1 = critSet F := by
  have h : (1 : ℕ) - 1 = 0 := rfl
  rw [flatCrit, h, flatSetV_zero, Set.univ_inter]

/-- The set of points at which `F` is analytic is open. -/
lemma isOpen_analyticAt_set {d m : ℕ} (F : (Fin d → ℝ) → (Fin m → ℝ)) :
    IsOpen {x | AnalyticAt ℝ F x} :=
  isOpen_analyticAt ℝ F

/-- From the local statement for a set `A` to the global statement over any `B`. -/
lemma volume_image_inter_eq_zero_of_local {d m : ℕ} (F : (Fin d → ℝ) → (Fin m → ℝ))
    (A : Set (Fin d → ℝ))
    (h : ∀ x ∈ A, ∃ δ > 0, MeasureTheory.volume (F '' (A ∩ Metric.ball x δ)) = 0)
    (B : Set (Fin d → ℝ)) : MeasureTheory.volume (F '' (A ∩ B)) = 0 := by
  refine glueNull F (A ∩ B) ?_
  intro x hx
  obtain ⟨δ, hδ, hvol⟩ := h x hx.1
  refine ⟨Metric.ball x δ, Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ), ?_⟩
  have hle : MeasureTheory.volume (F '' ((A ∩ B) ∩ Metric.ball x δ))
      ≤ MeasureTheory.volume (F '' (A ∩ Metric.ball x δ)) :=
    measure_mono (Set.image_mono fun y hy => ⟨hy.1.1, hy.2⟩)
  rw [hvol] at hle
  exact nonpos_iff_eq_zero.mp hle

/-- The bounded form follows from the local form at level `1`. -/
lemma sardGB_of_sardSt (m : ℕ) (h : ∀ d, SardSt d 1 m) : SardGB m := by
  intro d F B hB han
  have hA : critSet F ∩ B ⊆ flatCrit F 1 := by
    rw [flatCrit_one_eq]
    exact Set.inter_subset_left
  have han' : ∀ x ∈ critSet F ∩ B, AnalyticAt ℝ F x := fun x hx => han x hx.2
  have hloc : ∀ x ∈ critSet F ∩ B,
      ∃ δ > 0, MeasureTheory.volume (F '' ((critSet F ∩ B) ∩ Metric.ball x δ)) = 0 :=
    fun x hx => h d F (critSet F ∩ B) hA han' x hx
  simpa using volume_image_inter_eq_zero_of_local F (critSet F ∩ B) hloc Set.univ

/-- Target dimension `0`: the target is a point, so every map is surjective onto it. -/
lemma sardSt_zero_m (d j : ℕ) : SardSt d j 0 := by
  intro F A hA han x₀ hx
  have hcrit : ∀ x : Fin d → ℝ, Function.Surjective (fderiv ℝ F x) :=
    fun x y => ⟨0, Subsingleton.elim _ _⟩
  have hAempty : A = ∅ := by
    refine Set.Subset.antisymm (fun x hx' => ?_) (Set.empty_subset A)
    exact absurd (hcrit x) (hA hx').2
  exact ⟨1, one_pos, by rw [hAempty, Set.empty_inter, Set.image_empty, measure_empty]⟩

/-- The case `d ≤ m` at level `1` (the equal-dimensional and codimension-free cases). -/
lemma sardSt_one_le (d m : ℕ) (hmpos : 0 < m) (hdm : d ≤ m) : SardSt d 1 m := by
  intro F A hA han x₀ hx
  refine ⟨1, one_pos, ?_⟩
  have han' : ∀ x ∈ A ∩ Metric.ball x₀ 1, AnalyticAt ℝ F x := fun x hx' => han x hx'.1
  rcases lt_or_eq_of_le hdm with hlt | heq
  · exact baseCaseLt hlt hmpos F (A ∩ Metric.ball x₀ 1) han'
  · subst heq
    have hW : IsOpen {x : Fin d → ℝ | AnalyticAt ℝ F x} := isOpen_analyticAt_set F
    have hFan : AnalyticOn ℝ F {x | AnalyticAt ℝ F x} := fun x hx' => hx'.analyticWithinAt
    refine baseCaseEq F {x | AnalyticAt ℝ F x} hW hFan (A ∩ Metric.ball x₀ 1)
      (fun x hx' => han x hx'.1) ?_
    intro x hx'
    rw [← flatCrit_one_eq]
    exact hA hx'.1

/-- The recursion, for a fixed target dimension `m`, given the induction hypothesis for all
smaller target dimensions. -/
theorem sardSt_of_target (m : ℕ) (IHm : ∀ m' < m, ∀ d, SardSt d 1 m') :
    ∀ d j, 1 ≤ j → SardSt d j m := by
  suffices key : ∀ N d j, 1 ≤ j → d - j ≤ N → SardSt d j m from
    fun d j hj => key (d - j) d j hj le_rfl
  intro N
  induction N with
  | zero =>
    intro d j hj1 hdj
    by_cases hm : m = 0
    · subst hm
      exact sardSt_zero_m d j
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      by_cases hj2 : 2 ≤ j
      · have hjm : d ≤ j * m := by
          have h1 : d ≤ j := by omega
          calc d ≤ j := h1
            _ = j * 1 := (Nat.mul_one j).symm
            _ ≤ j * m := Nat.mul_le_mul_left j hmpos
        intro F A hA han x₀ hx
        exact ⟨1, one_pos, engineFlat hj2 hmpos hjm F (A ∩ Metric.ball x₀ 1)
          (Metric.isBounded_ball.subset Set.inter_subset_right)
          (fun x hx' => han x hx'.1)
          (Set.inter_subset_left.trans (hA.trans (flatCrit_subset_flatSetV F j)))⟩
      · have hj1' : j = 1 := by omega
        subst hj1'
        exact sardSt_one_le d m hmpos (by omega)
  | succ N ih =>
    intro d j hj1 hdj
    by_cases hm : m = 0
    · subst hm
      exact sardSt_zero_m d j
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      by_cases hj2 : 2 ≤ j
      · by_cases hjm : d ≤ j * m
        · intro F A hA han x₀ hx
          exact ⟨1, one_pos, engineFlat hj2 hmpos hjm F (A ∩ Metric.ball x₀ 1)
            (Metric.isBounded_ball.subset Set.inter_subset_right)
            (fun x hx' => han x hx'.1)
            (Set.inter_subset_left.trans (hA.trans (flatCrit_subset_flatSetV F j)))⟩
        · intro F A hA han x₀ hx
          have hjm' : j * m < d := not_le.mp hjm
          have hjd : j < d := by
            have hle : j ≤ j * m := by
              calc j = j * 1 := (Nat.mul_one j).symm
                _ ≤ j * m := Nat.mul_le_mul_left j hmpos
            omega
          -- the two pieces of `A`
          set A₁ : Set (Fin d → ℝ) := A ∩ {x | iteratedFDeriv ℝ j F x = 0} with hA₁
          set A₂ : Set (Fin d → ℝ) := A ∩ {x | iteratedFDeriv ℝ j F x ≠ 0} with hA₂
          have hAf : A ⊆ flatSetV F (j - 1) := hA.trans (flatCrit_subset_flatSetV F j)
          have hA₁fc : A₁ ⊆ flatCrit F (j + 1) := by
            intro x hx
            refine ⟨?_, (hA hx.1).2⟩
            intro i hi hij
            by_cases hijj : i ≤ j - 1
            · exact hAf hx.1 i hi hijj
            · have : i = j := by omega
              rw [this]
              exact hx.2
          have hdeep : ∀ x ∈ A₁, ∃ δ > 0,
              MeasureTheory.volume (F '' (A₁ ∩ Metric.ball x δ)) = 0 :=
            fun x hx => ih d (j + 1) (by omega) (by omega) F A₁ hA₁fc
              (fun y hy => han y hy.1) x hx
          have h1glob : ∀ B : Set (Fin d → ℝ),
              MeasureTheory.volume (F '' (A₁ ∩ B)) = 0 :=
            fun B => volume_image_inter_eq_zero_of_local F A₁ hdeep B
          have h2loc : ∀ x ∈ A₂, ∃ δ > 0,
              MeasureTheory.volume (F '' (A₂ ∩ Metric.ball x δ)) = 0 := by
            intro x hx
            refine levelSetReductionH hj2 (fun d' hd' F' A' hA' han' x₀ hx₀ =>
              ih d' j (by omega) (by omega) F' A' hA' han' x₀ hx₀) F A₂ ?_ ?_ ?_ x hx hx.2
            · exact Set.inter_subset_left.trans hAf
            · exact Set.inter_subset_left.trans (hA.trans (flatCrit_subset_critSet F j))
            · exact fun y hy => han y hy.1
          have h2glob : ∀ B : Set (Fin d → ℝ),
              MeasureTheory.volume (F '' (A₂ ∩ B)) = 0 :=
            fun B => volume_image_inter_eq_zero_of_local F A₂ h2loc B
          refine ⟨1, one_pos, ?_⟩
          have hsub : A ∩ Metric.ball x₀ 1 ⊆ (A₁ ∩ Metric.ball x₀ 1) ∪ (A₂ ∩ Metric.ball x₀ 1) := by
            intro y hy
            rcases hy with ⟨hyA, hyb⟩
            by_cases hd : iteratedFDeriv ℝ j F y = 0
            · exact Or.inl ⟨⟨hyA, hd⟩, hyb⟩
            · exact Or.inr ⟨⟨hyA, hd⟩, hyb⟩
          refine measure_mono_null ?_
            (measure_union_null (h1glob (Metric.ball x₀ 1)) (h2glob (Metric.ball x₀ 1)))
          rw [← Set.image_union]
          exact Set.image_mono hsub
      · have hj1' : j = 1 := by omega
        subst hj1'
        by_cases hdm : d ≤ m
        · exact sardSt_one_le d m hmpos hdm
        · have hGB : SardGB (m - 1) :=
            sardGB_of_sardSt (m - 1) (IHm (m - 1) (by omega))
          intro F A hA han x₀ hx
          have hAf : A ⊆ critSet F := by
            intro x hx'
            rw [← flatCrit_one_eq]
            exact hA hx'
          set A₁ : Set (Fin d → ℝ) := A ∩ {x | fderiv ℝ F x = 0} with hA₁
          set A₂ : Set (Fin d → ℝ) := A ∩ {x | fderiv ℝ F x ≠ 0} with hA₂
          have hA₁fc : A₁ ⊆ flatCrit F 2 := by
            intro x hx'
            refine ⟨?_, hAf hx'.1⟩
            intro i hi hij
            have hi1 : i = 1 := by omega
            rw [hi1]
            exact iteratedFDeriv_one_eq_zero_of_fderiv_eq_zero hx'.2
          have h1glob : ∀ B : Set (Fin d → ℝ),
              MeasureTheory.volume (F '' (A₁ ∩ B)) = 0 :=
            fun B => volume_image_inter_eq_zero_of_local F A₁
              (fun x hx' => ih d 2 (by omega) (by omega) F A₁ hA₁fc
                (fun y hy => han y hy.1) x hx') B
          have h2glob : ∀ B : Set (Fin d → ℝ),
              MeasureTheory.volume (F '' (A₂ ∩ B)) = 0 :=
            fun B => volume_image_inter_eq_zero_of_local F A₂
              (fun x hx' => straightenReductionH (by omega) hGB F A₂
                (Set.inter_subset_left.trans hAf) (fun y hy => han y hy.1) x hx' hx'.2) B
          refine ⟨1, one_pos, ?_⟩
          have hsub : A ∩ Metric.ball x₀ 1 ⊆ (A₁ ∩ Metric.ball x₀ 1) ∪ (A₂ ∩ Metric.ball x₀ 1) := by
            intro y hy
            rcases hy with ⟨hyA, hyb⟩
            by_cases hd : fderiv ℝ F y = 0
            · exact Or.inl ⟨⟨hyA, hd⟩, hyb⟩
            · exact Or.inr ⟨⟨hyA, hd⟩, hyb⟩
          refine measure_mono_null ?_
            (measure_union_null (h1glob (Metric.ball x₀ 1)) (h2glob (Metric.ball x₀ 1)))
          rw [← Set.image_union]
          exact Set.image_mono hsub

/-- The recursion assembled: the local statement at flatness level `1`, all source dimensions,
all target dimensions. -/
theorem sardSt_all : ∀ m d, SardSt d 1 m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m IHm =>
    intro d
    exact sardSt_of_target m (fun m' hm' d' => IHm m' hm' d') d 1 le_rfl

theorem sardAnalyticGeneral {n m : ℕ} (f : (Fin n → ℝ) → (Fin m → ℝ)) {U : Set (Fin n → ℝ)}
    (hU : IsOpen U) (hf : AnalyticOn ℝ f U) :
    MeasureTheory.volume (f '' ({x | ¬ Function.Surjective (fderiv ℝ f x)} ∩ U)) = 0 := by
  have hSt : SardSt n 1 m := sardSt_all m n
  have hA : {x : Fin n → ℝ | ¬ Function.Surjective (fderiv ℝ f x)} ∩ U ⊆ flatCrit f 1 := by
    rw [flatCrit_one_eq]
    exact Set.inter_subset_left
  have han : ∀ x ∈ {x : Fin n → ℝ | ¬ Function.Surjective (fderiv ℝ f x)} ∩ U,
      AnalyticAt ℝ f x := fun x hx => hf.analyticAt (hU.mem_nhds hx.2)
  refine glueNull f ({x : Fin n → ℝ | ¬ Function.Surjective (fderiv ℝ f x)} ∩ U) ?_
  intro x hx
  obtain ⟨δ, hδ, hvol⟩ := hSt f ({x : Fin n → ℝ | ¬ Function.Surjective (fderiv ℝ f x)} ∩ U)
    hA han x hx
  exact ⟨Metric.ball x δ, Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ), hvol⟩

end Work.WilE9G.Sard
