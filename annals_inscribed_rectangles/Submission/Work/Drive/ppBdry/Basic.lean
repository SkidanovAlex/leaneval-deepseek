import Mathlib
import Submission.Work.Drive.ppParity.Defs
import Submission.Work.Drive.ppParity.Bdry

/-!
# The charted pair map at the meet-value charts: smoothness and zeros

For a meet `x` of the pair `(E, E')` with `(V, W)`, the chart pair used by
`Work.Drive.PPRegAt E E' V W x` consists of the two *values* of the chains at `x`,
`q := E (ftS x) (ftU x)`, `q' := E' (ftS x) (ftU x)`, so the charted map `ppDiff q q' E E' V W` is a
map of a *fixed* chart pair, smooth on the open set `ppRegion q q'` where all four values lie in the
two chart sources.
-/

namespace Work.Drive
namespace PPB

open scoped Manifold ContDiff Topology
open Manifold Set

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

noncomputable section

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] [IsManifold (𝓡 4) Ctop M]

/-- The (s,u)-block map `x ↦ E (ftS x) (ftU x)` of the nine-box. -/
def pE (E : ℝ → EuclideanSpace ℝ (Fin 2) → M) :
    EuclideanSpace ℝ (Fin 9) → M := fun x => E (ftS x) (ftU x)

/-- The `y`-block map `x ↦ V (ftY x)`. -/
def pV (V : EuclideanSpace ℝ (Fin 3) → M) :
    EuclideanSpace ℝ (Fin 9) → M := fun x => V (ftY x)

/-- The `z`-block map `x ↦ W (ftZ x)`. -/
def pW (W : EuclideanSpace ℝ (Fin 3) → M) :
    EuclideanSpace ℝ (Fin 9) → M := fun x => W (ftZ x)

lemma pE_apply (E : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (x : EuclideanSpace ℝ (Fin 9)) : pE E x = E (ftS x) (ftU x) := rfl

lemma pV_apply (V : EuclideanSpace ℝ (Fin 3) → M)
    (x : EuclideanSpace ℝ (Fin 9)) : pV V x = V (ftY x) := rfl

lemma pW_apply (W : EuclideanSpace ℝ (Fin 3) → M)
    (x : EuclideanSpace ℝ (Fin 9)) : pW W x = W (ftZ x) := rfl

lemma ppDiff_apply (p p' : M) (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M) (y : EuclideanSpace ℝ (Fin 9)) :
    ppDiff p p' E E' V W y =
      pair44 (chr p (pE E y) - chr p (pV V y)) (chr p' (pE E' y) - chr p' (pW W y)) := rfl

lemma ppDiff_eq_formula (p p' : M) (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M) :
    ppDiff p p' E E' V W = fun y =>
      pair44 (chr p (pE E y) - chr p (pV V y)) (chr p' (pE E' y) - chr p' (pW W y)) := rfl

/-! ## The block maps are smooth -/

lemma contDiff_ftSU :
    ContDiff ℝ Ctop (fun x : EuclideanSpace ℝ (Fin 9) => (ftS x, ftU x)) := by
  refine ContDiff.prodMk ?_ ?_
  · show ContDiff ℝ Ctop (fun x : EuclideanSpace ℝ (Fin 9) => x 0)
    fun_prop
  · show ContDiff ℝ Ctop
      (fun x : EuclideanSpace ℝ (Fin 9) => WithLp.toLp 2 (fun i : Fin 2 => x ⟨1 + i.val, by omega⟩))
    fun_prop

lemma contMDiff_ftSU :
    ContMDiff (𝓡 9) (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : EuclideanSpace ℝ (Fin 9) => (ftS x, ftU x)) :=
  (contMDiff_iff_contDiff (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 9))
    (E' := ℝ × EuclideanSpace ℝ (Fin 2))).mpr contDiff_ftSU

lemma contDiff_ftY :
    ContDiff ℝ Ctop (fun x : EuclideanSpace ℝ (Fin 9) => ftY x) := by
  show ContDiff ℝ Ctop
    (fun x : EuclideanSpace ℝ (Fin 9) => WithLp.toLp 2 (fun i : Fin 3 => x ⟨3 + i.val, by omega⟩))
  fun_prop

lemma contDiff_ftZ :
    ContDiff ℝ Ctop (fun x : EuclideanSpace ℝ (Fin 9) => ftZ x) := by
  show ContDiff ℝ Ctop
    (fun x : EuclideanSpace ℝ (Fin 9) => WithLp.toLp 2 (fun i : Fin 3 => x ⟨6 + i.val, by omega⟩))
  fun_prop

lemma contMDiff_ftY :
    ContMDiff (𝓡 9) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 9) => ftY x) :=
  (contMDiff_iff_contDiff (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 9))
    (E' := EuclideanSpace ℝ (Fin 3))).mpr contDiff_ftY

lemma contMDiff_ftZ :
    ContMDiff (𝓡 9) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : EuclideanSpace ℝ (Fin 9) => ftZ x) :=
  (contMDiff_iff_contDiff (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 9))
    (E' := EuclideanSpace ℝ (Fin 3))).mpr contDiff_ftZ

lemma contMDiff_pE (E : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E)) :
    ContMDiff (𝓡 9) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (pE E) :=
  hE.comp contMDiff_ftSU

lemma contMDiff_pV (V : EuclideanSpace ℝ (Fin 3) → M)
    (hV : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) V) :
    ContMDiff (𝓡 9) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (pV V) :=
  hV.comp contMDiff_ftY

lemma contMDiff_pW (W : EuclideanSpace ℝ (Fin 3) → M)
    (hW : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    ContMDiff (𝓡 9) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (pW W) :=
  hW.comp contMDiff_ftZ

/-! ## The chart compositions -/

/-- The chart at `p` composed with a smooth map into `M` is smooth where the values lie in the
source of the chart. -/
lemma contDiffOn_chart_comp {f : EuclideanSpace ℝ (Fin 9) → M} (p : M)
    (hf : ContMDiff (𝓡 9) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ContDiffOn ℝ Ctop (fun x => chr p (f x)) (f ⁻¹' (chr p).source) := by
  have hchart : ContMDiffOn (𝓡 4) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (chr p) (chr p).source := by
    have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    simpa [chr] using h
  have h := hchart.comp (hf.contMDiffOn (s := f ⁻¹' (chr p).source)) (fun x hx => hx)
  have h' := (contMDiffOn_iff_contDiffOn (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 9))
    (E' := EuclideanSpace ℝ (Fin 4)) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
    (f := fun x => chr p (f x)) (s := f ⁻¹' (chr p).source)).mp h
  simpa [Function.comp_def] using h'

/-- `pair44` of two `C^∞` maps is `C^∞`. -/
lemma contDiffOn_pair44 {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    {s : Set α} {u v : α → EuclideanSpace ℝ (Fin 4)}
    (hu : ContDiffOn ℝ Ctop u s) (hv : ContDiffOn ℝ Ctop v s) :
    ContDiffOn ℝ Ctop (fun x => pair44 (u x) (v x)) s := by
  rw [contDiffOn_piLp]
  intro i
  by_cases hi : i.val < 4
  · have h : (fun x => pair44 (u x) (v x) i) = fun x => u x ⟨i.val, hi⟩ := by
      funext x
      exact PMB.pair44_apply_lt (u x) (v x) hi
    rw [h]
    exact (by fun_prop : ContDiffOn ℝ Ctop
      (fun f : EuclideanSpace ℝ (Fin 4) => f ⟨i.val, hi⟩) Set.univ).comp hu (fun x _ => trivial)
  · have h : (fun x => pair44 (u x) (v x) i)
        = fun x => v x ⟨i.val - 4, PMB.fin_sub_four_lt i hi⟩ := by
      funext x
      exact PMB.pair44_apply_ge (u x) (v x) hi
    rw [h]
    exact (by fun_prop : ContDiffOn ℝ Ctop
      (fun f : EuclideanSpace ℝ (Fin 4) => f ⟨i.val - 4, PMB.fin_sub_four_lt i hi⟩) Set.univ).comp hv
      (fun x _ => trivial)

/-- **Smoothness of the charted pair map on its region.** -/
theorem contDiffOn_ppDiff (p p' : M) (E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (V W : EuclideanSpace ℝ (Fin 3) → M)
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E))
    (hE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4)))
      ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E'))
    (hV : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) W) :
    ContDiffOn ℝ Ctop (ppDiff p p' E E' V W) (ppRegion p p' E E' V W) := by
  have h1 : ContDiffOn ℝ Ctop (fun x : EuclideanSpace ℝ (Fin 9) => chr p (pE E x))
      (ppRegion p p' E E' V W) :=
    (contDiffOn_chart_comp p (contMDiff_pE E hE)).mono (fun x hx => hx.1)
  have h2 : ContDiffOn ℝ Ctop (fun x : EuclideanSpace ℝ (Fin 9) => chr p (pV V x))
      (ppRegion p p' E E' V W) :=
    (contDiffOn_chart_comp p (contMDiff_pV V hV)).mono (fun x hx => hx.2.1)
  have h3 : ContDiffOn ℝ Ctop (fun x : EuclideanSpace ℝ (Fin 9) => chr p' (pE E' x))
      (ppRegion p p' E E' V W) :=
    (contDiffOn_chart_comp p' (contMDiff_pE E' hE')).mono (fun x hx => hx.2.2.1)
  have h4 : ContDiffOn ℝ Ctop (fun x : EuclideanSpace ℝ (Fin 9) => chr p' (pW W x))
      (ppRegion p p' E E' V W) :=
    (contDiffOn_chart_comp p' (contMDiff_pW W hW)).mono (fun x hx => hx.2.2.2)
  rw [ppDiff_eq_formula]
  exact contDiffOn_pair44 (h1.sub h2) (h3.sub h4)

end

end PPB
end Work.Drive
