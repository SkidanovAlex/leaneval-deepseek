import Mathlib
import Submission.Work.Drive.ppParity.Defs
import Submission.Work.Drive.ppParity.Shift

/-!
# Joint smoothness of the intrinsically perturbed pair map `ppDiff`

This is the smoothness input of the lead's **S3** (`Submission/Work/Drive/NOTES_LEAD_residency.md`)
for the pair map of the transport: the perturbed pair map

> `q ↦ ppDiff p p' (ppShift Ξ w (unpackFst q.1) E) (ppShift Ξ w (unpackSnd q.1) E') V W q.2`

is `C^∞` at every pair `(τ₀, y₀)` whose four values lie in the two charts' sources (`hsrc`).

The proof is pure chain rule: the four charted blocks are the chart `chr p` (resp. `chr p'`)
composed with the smooth manifold maps `q ↦ Ξ (w (ftS q.2) • unpackFst q.1) (E (ftS q.2) (ftU q.2))`
and `q ↦ V (ftY q.2)` (resp. with the `E'`, `W` counterparts) — the *self-centred* charts are
irrelevant here, only the two chart memberships of `hsrc` are used, and they are consumed exactly
once each, through the `𝓝`-membership of the chart source at the relevant image point.  The packing
`pair44` is handled coordinatewise.

The perturbation `Ξ` enters as a two-variable smooth map `(v, x) ↦ Ξ v x` of the manifold-with-corners
product `ℝ⁴ × M`, and the weight `w`, the parameter `unpackFst q.1`/`unpackSnd q.1` and the two chains
`E`, `E'` compose into its two arguments; no regularity of `Ξ` at `0` or of `w` at `0` is assumed (the
collar transfers of `Shift.lean` supply the vanishing, not this file).
-/

namespace Work.Drive.ppParity

open scoped Manifold ContDiff Topology
open Manifold Set

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

local notation "C∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)

/-- The domain of the pair map: the parameter `ℝ⁸` of the two-plane perturbation together with the
`9`-box point of the pair meet. -/
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
value lies in the chart source (`𝓡 4 = modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))`). -/
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
  · show ContDiff ℝ C∞ (fun q : Dom => WithLp.toLp 2 (fun i : Fin 2 => q.2 ⟨1 + i.val, by omega⟩))
    fun_prop

private lemma contMDiff_ftY : ContMDiff (𝓘(ℝ, Dom)) (𝓡 3) C∞
    (fun q : Dom => Work.Drive.ftY q.2) := by
  refine contMDiff_iff_contDiff.mpr ?_
  show ContDiff ℝ C∞ (fun q : Dom => WithLp.toLp 2 (fun i : Fin 3 => q.2 ⟨3 + i.val, by omega⟩))
  fun_prop

private lemma contMDiff_ftZ : ContMDiff (𝓘(ℝ, Dom)) (𝓡 3) C∞
    (fun q : Dom => Work.Drive.ftZ q.2) := by
  refine contMDiff_iff_contDiff.mpr ?_
  show ContDiff ℝ C∞ (fun q : Dom => WithLp.toLp 2 (fun i : Fin 3 => q.2 ⟨6 + i.val, by omega⟩))
  fun_prop

/-! ## The two `Ξ`-composed chains -/

/-- **The chart-perturbed chain is a smooth manifold map on the parameter space.**  The two arguments
of `Ξ` are the smooth scalar-weighted block map `a` and the smooth chain `q ↦ E (ftS q.2) (ftU q.2)`;
the composition is smooth because `Ξ` is smooth on the product `ℝ⁴ × M`. -/
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

private lemma contMDiff_weight_fst (w : ℝ → ℝ) (hw : ContDiff ℝ C∞ w) :
    ContMDiff (𝓘(ℝ, Dom)) (𝓡 4) C∞
      (fun q : Dom => w (Work.Drive.ftS q.2) • Work.Drive.unpackFst q.1) := by
  refine contMDiff_iff_contDiff.mpr ?_
  have h1 : ContDiff ℝ C∞ (fun q : Dom => w (Work.Drive.ftS q.2)) :=
    hw.comp (by
      show ContDiff ℝ C∞ (fun q : Dom => q.2 0)
      fun_prop)
  have h2 : ContDiff ℝ C∞ (fun q : Dom => Work.Drive.unpackFst q.1) :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := C∞) Work.Drive.unpackFst).comp
      (by fun_prop : ContDiff ℝ C∞ (fun q : Dom => q.1))
  exact h1.smul h2

private lemma contMDiff_weight_snd (w : ℝ → ℝ) (hw : ContDiff ℝ C∞ w) :
    ContMDiff (𝓘(ℝ, Dom)) (𝓡 4) C∞
      (fun q : Dom => w (Work.Drive.ftS q.2) • Work.Drive.unpackSnd q.1) := by
  refine contMDiff_iff_contDiff.mpr ?_
  have h1 : ContDiff ℝ C∞ (fun q : Dom => w (Work.Drive.ftS q.2)) :=
    hw.comp (by
      show ContDiff ℝ C∞ (fun q : Dom => q.2 0)
      fun_prop)
  have h2 : ContDiff ℝ C∞ (fun q : Dom => Work.Drive.unpackSnd q.1) :=
    (ContinuousLinearMap.contDiff (𝕜 := ℝ) (n := C∞) Work.Drive.unpackSnd).comp
      (by fun_prop : ContDiff ℝ C∞ (fun q : Dom => q.1))
  exact h1.smul h2

/-! ## The packing `pair44` is smooth, coordinatewise -/

private lemma pair44_apply_lt (a b : EuclideanSpace ℝ (Fin 4)) {i : Fin 8} (h : i.val < 4) :
    Work.Drive.pair44 a b i = a ⟨i.val, h⟩ := by
  simp only [Work.Drive.pair44, WithLp.ofLp_toLp]
  rw [dif_pos h]

private lemma pair44_apply_ge (a b : EuclideanSpace ℝ (Fin 4)) {i : Fin 8} (h : ¬ i.val < 4) :
    Work.Drive.pair44 a b i = b ⟨i.val - 4, by omega⟩ := by
  simp only [Work.Drive.pair44, WithLp.ofLp_toLp]
  rw [dif_neg h]

private lemma fin_sub_four_lt (i : Fin 8) (h : ¬ i.val < 4) : i.val - 4 < 4 := by omega

private lemma contDiffAt_pair44 {u v : Dom → EuclideanSpace ℝ (Fin 4)} {z₀ : Dom}
    (hu : ContDiffAt ℝ C∞ u z₀) (hv : ContDiffAt ℝ C∞ v z₀) :
    ContDiffAt ℝ C∞ (fun x => Work.Drive.pair44 (u x) (v x)) z₀ := by
  rw [contDiffAt_piLp]
  intro i
  by_cases hi : i.val < 4
  · have h : (fun x => (Work.Drive.pair44 (u x) (v x)).ofLp i) = fun x => u x ⟨i.val, hi⟩ := by
      funext x; exact pair44_apply_lt (u x) (v x) hi
    rw [h]
    exact (by fun_prop : ContDiffAt ℝ C∞
      (fun f : EuclideanSpace ℝ (Fin 4) => f ⟨i.val, hi⟩) (u z₀)).comp z₀ hu
  · have h : (fun x => (Work.Drive.pair44 (u x) (v x)).ofLp i) =
        fun x => v x ⟨i.val - 4, fin_sub_four_lt i hi⟩ := by
      funext x; exact pair44_apply_ge (u x) (v x) hi
    rw [h]
    exact (by fun_prop : ContDiffAt ℝ C∞
      (fun f : EuclideanSpace ℝ (Fin 4) => f ⟨i.val - 4, fin_sub_four_lt i hi⟩) (v z₀)).comp z₀ hv

/-! ## The theorem -/

theorem contDiffAt_ppDiff_family2
    {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {E E' : ℝ → EuclideanSpace ℝ (Fin 2) → M} {V W : EuclideanSpace ℝ (Fin 3) → M}
    (Ξ : EuclideanSpace ℝ (Fin 4) → M → M)
    (hΞsm : ContMDiff ((modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 4) × M => Ξ q.1 q.2))
    (w : ℝ → ℝ) (hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) w)
    (hE : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E))
    (hE' : ContMDiff (modelWithCornersSelf ℝ (ℝ × EuclideanSpace ℝ (Fin 2)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Function.uncurry E'))
    (hV : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (hW : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (p p' : M) (τ₀ : EuclideanSpace ℝ (Fin 8)) {y₀ : EuclideanSpace ℝ (Fin 9)}
    (hsrc : Work.Drive.ppShift Ξ w (Work.Drive.unpackFst τ₀) E (Work.Drive.ftS y₀) (Work.Drive.ftU y₀)
        ∈ (Work.Drive.chr p).source ∧
      V (Work.Drive.ftY y₀) ∈ (Work.Drive.chr p).source ∧
      Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd τ₀) E' (Work.Drive.ftS y₀) (Work.Drive.ftU y₀)
        ∈ (Work.Drive.chr p').source ∧
      W (Work.Drive.ftZ y₀) ∈ (Work.Drive.chr p').source) :
    ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun q : EuclideanSpace ℝ (Fin 8) × EuclideanSpace ℝ (Fin 9) =>
        Work.Drive.ppDiff p p' (Work.Drive.ppShift Ξ w (Work.Drive.unpackFst q.1) E)
          (Work.Drive.ppShift Ξ w (Work.Drive.unpackSnd q.1) E') V W q.2)
      (τ₀, y₀) := by
  have hfst : ContMDiff (𝓘(ℝ, Dom)) (𝓡 4) C∞
      (fun q : Dom => Ξ (w (Work.Drive.ftS q.2) • Work.Drive.unpackFst q.1)
        (E (Work.Drive.ftS q.2) (Work.Drive.ftU q.2))) :=
    contMDiff_comp_Ξ Ξ hΞsm _ (contMDiff_weight_fst w hw) E hE
  have hsnd : ContMDiff (𝓘(ℝ, Dom)) (𝓡 4) C∞
      (fun q : Dom => Ξ (w (Work.Drive.ftS q.2) • Work.Drive.unpackSnd q.1)
        (E' (Work.Drive.ftS q.2) (Work.Drive.ftU q.2))) :=
    contMDiff_comp_Ξ Ξ hΞsm _ (contMDiff_weight_snd w hw) E' hE'
  have h1 : ContDiffAt ℝ C∞
      (fun q : Dom => Work.Drive.chr p (Ξ (w (Work.Drive.ftS q.2) • Work.Drive.unpackFst q.1)
        (E (Work.Drive.ftS q.2) (Work.Drive.ftU q.2)))) (τ₀, y₀) :=
    contDiffAt_chr_comp hfst p (τ₀, y₀) hsrc.1
  have h2 : ContDiffAt ℝ C∞
      (fun q : Dom => Work.Drive.chr p (V (Work.Drive.ftY q.2))) (τ₀, y₀) :=
    contDiffAt_chr_comp (hV.comp contMDiff_ftY) p (τ₀, y₀) hsrc.2.1
  have h3 : ContDiffAt ℝ C∞
      (fun q : Dom => Work.Drive.chr p' (Ξ (w (Work.Drive.ftS q.2) • Work.Drive.unpackSnd q.1)
        (E' (Work.Drive.ftS q.2) (Work.Drive.ftU q.2)))) (τ₀, y₀) :=
    contDiffAt_chr_comp hsnd p' (τ₀, y₀) hsrc.2.2.1
  have h4 : ContDiffAt ℝ C∞
      (fun q : Dom => Work.Drive.chr p' (W (Work.Drive.ftZ q.2))) (τ₀, y₀) :=
    contDiffAt_chr_comp (hW.comp contMDiff_ftZ) p' (τ₀, y₀) hsrc.2.2.2
  have hmain : ContDiffAt ℝ C∞ (fun q : Dom => Work.Drive.pair44
      (Work.Drive.chr p (Ξ (w (Work.Drive.ftS q.2) • Work.Drive.unpackFst q.1)
          (E (Work.Drive.ftS q.2) (Work.Drive.ftU q.2))) - Work.Drive.chr p (V (Work.Drive.ftY q.2)))
      (Work.Drive.chr p' (Ξ (w (Work.Drive.ftS q.2) • Work.Drive.unpackSnd q.1)
          (E' (Work.Drive.ftS q.2) (Work.Drive.ftU q.2))) - Work.Drive.chr p'
            (W (Work.Drive.ftZ q.2)))) (τ₀, y₀) :=
    contDiffAt_pair44 (h1.sub h2) (h3.sub h4)
  simpa only [Work.Drive.ppDiff, Work.Drive.ppShift] using hmain

end

end Work.Drive.ppParity
