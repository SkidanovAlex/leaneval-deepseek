import Mathlib
import Submission.Work.Drive.ppParity.Defs
import Submission.Work.Drive.ppParity.Shift

/-!
# Smoothness of the charted, intrinsically perturbed plane chain

This is the smoothness input of the lead's **S3** (`Submission/Work/Drive/NOTES_LEAD_residency.md`)
for the *single* chain `Et τ s u = Ξ (w s • B τ) (E s u)` of the intrinsic perturbation: the map

> `q ↦ chr c (ppShift Ξ w (B q.1) E (ftS q.2) (ftU q.2))`

is `C^∞` at every pair `q = (0, x)` whose value `E (ftS x) (ftU x)` lies in the source of the chart
at `c`.  It is the single-chain companion of
`Work.Drive.ppParity.contDiffAt_ppDiff_family2` (which treats both blocks of the pair map): the only
smoothness that is used is joint smoothness of `Ξ` on `ℝ⁴ × M`, `C^∞`-ness of `w`, `C^∞`-ness of the
uncurried chain `E`, and the smoothness of the chart on its source — consumed exactly once, at the
image point of `q = (0, x)`.

No regularity of `Ξ` at `0`, of `B`, or of `w` at `0` beyond `C^∞` is assumed; the collar transfers of
`Shift.lean` supply the vanishing.
-/

namespace Work.Drive.ppParity

open scoped Manifold ContDiff Topology
open Manifold Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

local notation "C∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- The domain of the chain map: the parameter `ℝ⁸` of the plane perturbation together with the
`9`-box point of the chain. -/
local notation "Dom" => EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9)

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
  [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-! ## The chart of the point is smooth on its source -/

private lemma contMDiffOn_chr (p : M) :
    ContMDiffOn (𝓡 4) (𝓡 4) C∞ (Work.Drive.chr p) (Work.Drive.chr p).source := by
  have h := contMDiffOn_extChartAt (I := 𝓡 4) (x := p) (n := C∞)
  simpa [Work.Drive.chr] using h

/-- **A smooth manifold-valued map composed with the chart at `p` is smooth** at every point whose
value lies in the chart source. -/
private lemma contDiffAt_chr_comp {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {f : Z → M} (hf : ContMDiff (𝓘(ℝ, Z)) (𝓡 4) C∞ f) (p : M) (z₀ : Z)
    (hreg : f z₀ ∈ (Work.Drive.chr p).source) :
    ContDiffAt ℝ C∞ (fun z => Work.Drive.chr p (f z)) z₀ := by
  have h1 : ContMDiffAt (𝓡 4) (𝓡 4) C∞ (Work.Drive.chr p) (f z₀) :=
    (contMDiffOn_chr p).contMDiffAt ((Work.Drive.chr p).open_source.mem_nhds hreg)
  exact contMDiffAt_iff_contDiffAt.mp (h1.comp z₀ hf.contMDiffAt)

/-! ## The coordinate projections of the `9`-box are smooth -/

private lemma contMDiff_ftSU : ContMDiff (𝓘(ℝ, Dom))
    (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2))) C∞
    (fun q : Dom => (Work.Drive.ftS q.2, Work.Drive.ftU q.2)) := by
  refine contMDiff_iff_contDiff.mpr ?_
  refine ContDiff.prodMk ?_ ?_
  · show ContDiff ℝ C∞ (fun q : Dom => q.2 0)
    fun_prop
  · show ContDiff ℝ C∞
      (fun q : Dom => WithLp.toLp 2 (fun i : Fin 2 => q.2 ⟨1 + i.val, by omega⟩))
    fun_prop

/-! ## The `Ξ`-composed chain -/

/-- **The chart-perturbed chain is a smooth manifold map on the parameter space.**  The two arguments
of `Ξ` are the smooth block map `a` and the smooth chain `q ↦ E (ftS q.2) (ftU q.2)`; the composition
is smooth because `Ξ` is smooth on the product `ℝ⁴ × M`. -/
private lemma contMDiff_comp_Ξ
    (Ξ : EuclideanSpace ℝ (Fin 4) → M → M)
    (hΞsm : ContMDiff ((𝓡 4).prod (𝓡 4)) (𝓡 4) C∞
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    (a : Dom → EuclideanSpace ℝ (Fin 4)) (ha : ContMDiff (𝓘(ℝ, Dom)) (𝓡 4) C∞ a)
    (E : ℝ → EuclideanSpace ℝ (Fin 2) → M)
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2))) (𝓡 4) C∞
      (Function.uncurry E)) :
    ContMDiff (𝓘(ℝ, Dom)) (𝓡 4) C∞
      (fun q : Dom => Ξ (a q) (E (Work.Drive.ftS q.2) (Work.Drive.ftU q.2))) := by
  have hb : ContMDiff (𝓘(ℝ, Dom)) (𝓡 4) C∞
      (fun q : Dom => E (Work.Drive.ftS q.2) (Work.Drive.ftU q.2)) := by
    simpa [Function.comp_def, Function.uncurry] using hE.comp contMDiff_ftSU
  simpa [Function.comp_def] using hΞsm.comp (ha.prodMk hb)

/-- The scalar-weighted parameter block `q ↦ w (ftS q.2) • B q.1` is smooth. -/
private lemma contMDiff_weight_B
    (B : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (w : ℝ → ℝ) (hw : ContDiff ℝ C∞ w) :
    ContMDiff (𝓘(ℝ, Dom)) (𝓡 4) C∞ (fun q : Dom => w (Work.Drive.ftS q.2) • B q.1) := by
  refine contMDiff_iff_contDiff.mpr ?_
  have h1 : ContDiff ℝ C∞ (fun q : Dom => w (Work.Drive.ftS q.2)) :=
    hw.comp (by
      show ContDiff ℝ C∞ (fun q : Dom => q.2 0)
      fun_prop)
  have h2 : ContDiff ℝ C∞ (fun q : Dom => B q.1) :=
    B.contDiff.comp (by fun_prop : ContDiff ℝ C∞ (fun q : Dom => q.1))
  exact h1.smul h2

/-! ## The theorem -/

theorem contDiffAt_chr_ppShift
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {Ξ : EuclideanSpace ℝ (Fin 4) → M → M}
    (hΞ : ContMDiff ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    (hΞ0 : ∀ p : M, Ξ 0 p = p)
    {w : ℝ → ℝ} (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    {E : ℝ → EuclideanSpace ℝ (Fin 2) → M}
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (Function.uncurry E))
    (B : EuclideanSpace ℝ (Fin 8) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    {c : M} {x : EuclideanSpace ℝ (Fin 9)}
    (hsrc : E (Work.Drive.ftS x) (Work.Drive.ftU x) ∈ (Work.Drive.chr c).source) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
        Work.Drive.chr c (Work.Drive.ppShift Ξ w (B q.1) E (Work.Drive.ftS q.2) (Work.Drive.ftU q.2)))
      (0, x) := by
  have hsm : ContMDiff (𝓘(ℝ, Dom)) (𝓡 4) C∞
      (fun q : Dom => Ξ (w (Work.Drive.ftS q.2) • B q.1)
        (E (Work.Drive.ftS q.2) (Work.Drive.ftU q.2))) :=
    contMDiff_comp_Ξ Ξ hΞ _ (contMDiff_weight_B B w hw) E hE
  have hreg : (fun q : Dom => Ξ (w (Work.Drive.ftS q.2) • B q.1)
        (E (Work.Drive.ftS q.2) (Work.Drive.ftU q.2))) (0, x) ∈ (Work.Drive.chr c).source := by
    show Ξ (w (Work.Drive.ftS x) • B (0 : EuclideanSpace ℝ (Fin 8)))
      (E (Work.Drive.ftS x) (Work.Drive.ftU x)) ∈ (Work.Drive.chr c).source
    simpa only [B.map_zero, smul_zero, hΞ0] using hsrc
  have hmain : ContDiffAt ℝ C∞
      (fun q : Dom => Work.Drive.chr c (Ξ (w (Work.Drive.ftS q.2) • B q.1)
        (E (Work.Drive.ftS q.2) (Work.Drive.ftU q.2)))) (0, x) :=
    contDiffAt_chr_comp hsm c (0, x) hreg
  simpa only [Work.Drive.ppShift] using hmain

end

end Work.Drive.ppParity
