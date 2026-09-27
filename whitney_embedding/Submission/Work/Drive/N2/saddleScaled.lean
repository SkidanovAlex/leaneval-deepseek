import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.saddleWindowBlock
import Submission.Work.Drive.N2.saddleChartDrawing_immersive
import Submission.Work.Drive.N2.saddlePsi_helpers
import Submission.Work.Drive.N2.goodDrawingOn_of_pieces
import Submission.Work.Drive.N2.saddleCollarFoot
import Submission.Work.Drive.N2.modelBall
import Submission.Work.Drive.N2.modelFlowDefs
import Submission.Work.Drive.N2.modelOrbitInvariant
import Submission.Work.Compat.MFDerivCongrV433

/-!
# The saddle window drawing with a general multiplier `lam`

This file records the *scaled* form of the saddle window block, which is the form the compact
`n = 2` construction actually consumes: the Morse chart coordinate `Z₀` of a saddle satisfies
`f = c + Re (Z₀²)`, but the model `saddlePsi η δ` is *not* adapted to `Z₀` — its collar sits at
`|Im (·)²| ∈ [2 - 2δ, 2]`, i.e. at `‖·‖ ≈ 1.4`, whereas the model ball of the flow, `‖Z₀‖ < ρ/8`,
can be arbitrarily large.  The fix is to use the *scaled* coordinate `Z := Z₀/λ` (so that
`f = c + lam · Re (Z²)` with `lam = λ²`), which moves the collar to `‖Z₀‖ ≈ 1.4·λ`.

Everything here is stated with a general `lam ≠ 0`:

* `saddleRegion U Z c₀` — the model region, the strip `|Im (Z ·)²| < c₀` inside `U`;
* `saddleWindow_drawing_lam` — the two-piece assembly (model on the region, picture of the anchor
  level off it) `GoodDrawingOn f (c - lam η, c + lam η)`; the two seam rows (`hfront`, `hcross`) and
  the transport landing row (`hfootval`) are hypotheses.

The *unscaled* specialisations (`lam = 1`) are the proved results of `levelSeparatingMap.lean`
(`saddleWindowAssembly_offD`, `saddleWindowSeam`).
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Filter

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

/-- The model region of the saddle window: the strip `|Im (Z ·)²| < c₀` inside the chart ball `U`. -/
def saddleRegion (U : Set M) (Z : M → ℂ) (c₀ : ℝ) : Set M :=
  {y : M | y ∈ U ∧ |((Z y) ^ 2).im| < c₀}

lemma isOpen_saddleRegion {U : Set M} (hU : IsOpen U) {Z : M → ℂ} {c₀ : ℝ}
    (hZsm : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z U) :
    IsOpen (saddleRegion U Z c₀) := by
  rw [isOpen_iff_mem_nhds]
  intro y hy
  obtain ⟨hyU, hylt⟩ := hy
  have hZc : ContinuousAt Z y := (hZsm.contMDiffAt (hU.mem_nhds hyU)).continuousAt
  have hφ : Continuous fun z : ℂ => |(z ^ 2).im| := by fun_prop
  have hc : ContinuousAt (fun y : M => |((Z y) ^ 2).im|) y :=
    ContinuousAt.comp (f := Z) (g := fun z : ℂ => |(z ^ 2).im|) hφ.continuousAt hZc
  filter_upwards [hU.mem_nhds hyU, hc (isOpen_Iio.mem_nhds hylt)] with y' hyU' hy'
  exact ⟨hyU', hy'⟩

/-- The derivative of `ζ ↦ lam * (ζ²).re` at `z`, evaluated at `w`, in coordinates. -/
lemma fderiv_smul_sq_re_apply (lam : ℝ) (z w : ℂ) :
    (fderiv ℝ (fun ζ : ℂ => lam * (ζ ^ 2).re) z) w = lam * ((2 * z * w).re) := by
  have hdiff : DifferentiableAt ℝ (fun ζ : ℂ => (ζ ^ 2).re) z := by fun_prop
  have hfs : fderiv ℝ (fun ζ : ℂ => lam * (ζ ^ 2).re) z
      = lam • fderiv ℝ (fun ζ : ℂ => (ζ ^ 2).re) z := by
    rw [show (fun ζ : ℂ => lam * (ζ ^ 2).re) = lam • (fun ζ : ℂ => (ζ ^ 2).re) from rfl,
      fderiv_const_smul hdiff]
  rw [hfs, smul_apply, smul_eq_mul, fderiv_sq_re_apply]

/-- **The scaled kernel lemma.**  A vector `w` killed both by the differential of
`ζ ↦ lam · (ζ²).re` and by the differential of the model picture `cE3 ∘ saddlePsi η δ` is zero. -/
lemma saddleKernel_scaled {η δ lam : ℝ} (hδ : 0 < δ) (hδ₂ : δ < 1 / 2) (hlam : lam ≠ 0)
    (z w : ℂ)
    (h1 : (fderiv ℝ (fun ζ : ℂ => lam * (ζ ^ 2).re) z) w = 0)
    (h2 : (fderiv ℝ (fun ζ : ℂ => cE3 (saddlePsi η δ ζ)) z) w = 0) : w = 0 := by
  have h1' : lam * ((2 * z * w).re) = 0 := by
    rw [← fderiv_smul_sq_re_apply]
    exact h1
  have hre : (2 * z * w).re = 0 := (mul_eq_zero.mp h1').resolve_left hlam
  have h2' : (fderiv ℝ (fun ζ : ℂ => (ζ ^ 2).re) z) w = 0 := by
    rw [fderiv_sq_re_apply]
    exact hre
  exact saddleKernel_triv hδ hδ₂ z w h2' h2

open Classical in
/-- **The saddle window drawing, with a general multiplier `lam`.**

`gm := cE3 ∘ saddlePsi η δ ∘ Z` is drawn on the model region `D = saddleRegion U Z c₀`, and the
transported picture `gb := A₀ ∘ foot` off it; the hybrid is a good drawing of the value band
`(c - lam η, c + lam η)`.

The hypotheses are exactly the obligations of the two pieces and of the seam:

* `hlev`: the normal form `f = c + lam · Re (Z ·)²` (this is what the scaled chart coordinate
  supplies);
* `hA₀inj`, `hA₀imm`: the anchor picture `A₀` is injective and `ker df`-immersive **at the feet**
  of the off-region band points (the only points at which the assembly consumes them);
* `hfootval`: the landing row of the transport off the model region (the legality);
* `hfront`: the two pieces agree to all orders at the interface points of the band;
* `hcross`: no point of `D` and point off `D` with a common band value are drawn to the same point. -/
theorem saddleWindow_drawing_lam {f : M → ℝ} {c η δ c₀ lam : ℝ}
    (hη : 0 < η) (hη' : η < 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hlam : lam ≠ 0)
    (hc₀ : 2 - 2 * δ < c₀) (hc₀' : c₀ < 2)
    {U : Set M} (hU : IsOpen U) {Z : M → ℂ}
    (hZsm : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z U)
    (hZinj : Set.InjOn Z U)
    (hZimm : ∀ x ∈ U, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z x))
    (hlev : ∀ x ∈ U, f x = c + lam * ((Z x) ^ 2).re)
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {A₀ : M → EuclideanSpace ℝ (Fin 3)}
    (hA₀ : ∀ x : M, ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A₀ x)
    {foot : M → M} (hfoot : ∀ x : M, ContMDiffAt (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) foot x)
    (hfootinj : ∀ x y : M, f x = f y → foot x = foot y → x = y)
    (hfootimm : ∀ x : M, ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 → mfderiv (𝓡 2) (𝓡 2) foot x v = 0 → v = 0)
    (hA₀inj : ∀ x y : M, x ∉ saddleRegion U Z c₀ → y ∉ saddleRegion U Z c₀ →
      f x ∈ Set.Ioo (c - lam * η) (c + lam * η) → f y ∈ Set.Ioo (c - lam * η) (c + lam * η) →
      f x = f y → A₀ (foot x) = A₀ (foot y) → x = y)
    (hA₀imm : ∀ x : M, x ∉ saddleRegion U Z c₀ →
      f x ∈ Set.Ioo (c - lam * η) (c + lam * η) → ∀ v : TangentSpace (𝓡 2) (foot x),
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (foot x) v = 0 →
      mfderiv (𝓡 2) (𝓡 3) A₀ (foot x) v = 0 → v = 0)
    (hfrU : ∀ x : M, x ∈ frontier (saddleRegion U Z c₀) →
      f x ∈ Set.Ioo (c - lam * η) (c + lam * η) → x ∈ U)
    (hfootval : ∀ x : M, x ∉ saddleRegion U Z c₀ →
      f x ∈ Set.Ioo (c - lam * η) (c + lam * η) → f (foot x) = c - lam * η)
    (hfront : ∀ x : M, x ∈ frontier (saddleRegion U Z c₀) →
      f x ∈ Set.Ioo (c - lam * η) (c + lam * η) →
      (fun y : M => cE3 (saddlePsi η δ (Z y))) =ᶠ[𝓝 x] (fun y : M => A₀ (foot y)))
    (hcross : ∀ x : M, x ∈ saddleRegion U Z c₀ →
      f x ∈ Set.Ioo (c - lam * η) (c + lam * η) →
      ∀ y : M, y ∉ saddleRegion U Z c₀ →
      f y ∈ Set.Ioo (c - lam * η) (c + lam * η) → f x = f y →
      cE3 (saddlePsi η δ (Z x)) ≠ A₀ (foot y)) :
    GoodDrawingOn f (Set.Ioo (c - lam * η) (c + lam * η))
      (fun x : M => if x ∈ saddleRegion U Z c₀ then cE3 (saddlePsi η δ (Z x))
        else A₀ (foot x)) := by
  have hn : ∞ ≠ (0 : WithTop ℕ∞) := by simp
  have hδ₂ : δ < 1 / 2 := by linarith
  set D : Set M := saddleRegion U Z c₀ with hDdef
  have hDopen : IsOpen D := isOpen_saddleRegion hU hZsm
  have hm_sm : ∀ x ∈ U, ContMDiffAt (𝓡 2) (𝓡 3) ∞ (fun y : M => cE3 (saddlePsi η δ (Z y))) x := by
    intro x hxU
    have hZx : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ∞ Z x := hZsm.contMDiffAt (hU.mem_nhds hxU)
    have hΨx : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ∞ (saddlePsi η δ) (Z x) :=
      (contDiff_saddlePsi η δ hδ hδ₂).contMDiff.contMDiffAt
    exact (cE3.contMDiff.contMDiffAt).comp x (hΨx.comp x hZx)
  have hm_inj : ∀ x ∈ U, ∀ y ∈ U, f x = f y →
      cE3 (saddlePsi η δ (Z x)) = cE3 (saddlePsi η δ (Z y)) → x = y := by
    intro x hxU y hyU hf hg
    have hΨ : saddlePsi η δ (Z x) = saddlePsi η δ (Z y) := cE3_injective hg
    have hre : ((Z x) ^ 2).re = ((Z y) ^ 2).re := by
      have h := hf
      rw [hlev x hxU, hlev y hyU] at h
      exact mul_left_cancel₀ hlam (by linarith)
    exact hZinj hxU hyU (saddlePsi_injOn_level hδ (by linarith) hre hΨ)
  -- the immersion row of the model piece, in the scaled form
  have hmimmU : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 →
      mfderiv (𝓡 2) (𝓡 3) (fun y : M => cE3 (saddlePsi η δ (Z y))) x v = 0 → v = 0 := by
    intro x hxU v h1 h2
    have hZx : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℂ) Z x :=
      (hZsm.contMDiffAt (hU.mem_nhds hxU)).mdifferentiableAt hn
    have hqc : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) (fun ζ : ℂ => c + lam * (ζ ^ 2).re) (Z x) :=
      (mdifferentiableAt_iff_differentiableAt (𝕜 := ℝ)).mpr (by fun_prop)
    have hfeq : f =ᶠ[𝓝 x] (fun y : M => c + lam * ((Z y) ^ 2).re) := by
      filter_upwards [hU.mem_nhds hxU] with y hy
      exact hlev y hy
    have h1p : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (fun y : M => c + lam * ((Z y) ^ 2).re) x v = 0 := by
      rw [← hfeq.mfderiv_eq_v433]; exact h1
    have h1' : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) ((fun ζ : ℂ => c + lam * (ζ ^ 2).re) ∘ Z) x v = 0 := h1p
    have e1 := mfderiv_comp_apply (f := Z) (g := fun ζ : ℂ => c + lam * (ζ ^ 2).re) x hqc hZx v
    have h1'' : (fderiv ℝ (fun ζ : ℂ => lam * (ζ ^ 2).re) (Z x))
        (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z x v) = 0 := by
      rw [e1] at h1'
      rw [mfderiv_eq_fderiv, fderiv_const_add] at h1'
      exact h1'
    have hgc : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓡 3) (fun ζ : ℂ => cE3 (saddlePsi η δ ζ)) (Z x) := by
      have hC : ContDiff ℝ ∞ (fun ζ : ℂ => cE3 (saddlePsi η δ ζ)) :=
        cE3.contDiff.comp (contDiff_saddlePsi η δ hδ hδ₂)
      exact (hC.contMDiff.contMDiffAt).mdifferentiableAt hn
    have h2' : mfderiv (𝓡 2) (𝓡 3) ((fun ζ : ℂ => cE3 (saddlePsi η δ ζ)) ∘ Z) x v = 0 := h2
    have e2 := mfderiv_comp_apply (f := Z)
      (g := fun ζ : ℂ => cE3 (saddlePsi η δ ζ)) x hgc hZx v
    have h2'' : (fderiv ℝ (fun ζ : ℂ => cE3 (saddlePsi η δ ζ)) (Z x))
        (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z x v) = 0 := by
      rw [e2] at h2'
      rw [mfderiv_eq_fderiv] at h2'
      exact h2'
    have hwzero : (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z x) v = (0 : TangentSpace 𝓘(ℝ, ℂ) (Z x)) :=
      saddleKernel_scaled hδ hδ₂ hlam (Z x) (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z x v) h1'' h2''
    have hv : (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z x) v
        = (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z x) (0 : TangentSpace (𝓡 2) x) := by
      rw [map_zero]
      exact hwzero
    exact hZimm x hxU hv
  -- the immersion row of the model piece on the model region
  have hmimm' : ∀ x ∈ D, f x ∈ Set.Ioo (c - lam * η) (c + lam * η) →
      ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 →
      mfderiv (𝓡 2) (𝓡 3) (fun y : M => cE3 (saddlePsi η δ (Z y))) x v = 0 → v = 0 := by
    intro x hxD _ v h1 h2
    exact hmimmU x hxD.1 v h1 h2
  -- the transported piece
  have hbsm : ∀ x : M, x ∉ D → f x ∈ Set.Ioo (c - lam * η) (c + lam * η) →
      ContMDiffAt (𝓡 2) (𝓡 3) ∞ (fun y : M => A₀ (foot y)) x :=
    fun x _ _ => (hA₀ (foot x)).comp x (hfoot x)
  have hbimm : ∀ x : M, x ∉ D → f x ∈ Set.Ioo (c - lam * η) (c + lam * η) →
      ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 →
      mfderiv (𝓡 2) (𝓡 3) (fun y : M => A₀ (foot y)) x v = 0 → v = 0 := by
    intro x hxD hxA v h1 h2
    have hfootdiff : MDifferentiableAt (𝓡 2) (𝓡 2) foot x := (hfoot x).mdifferentiableAt hn
    have hAdiff : MDifferentiableAt (𝓡 2) (𝓡 3) A₀ (foot x) :=
      (hA₀ (foot x)).mdifferentiableAt hn
    have hfdiff : MDifferentiableAt (𝓡 2) 𝓘(ℝ, ℝ) f (foot x) := hf.mdifferentiableAt hn
    by_cases hxfr : x ∈ frontier D
    · have hge := hfront x hxfr hxA
      have h2' : mfderiv (𝓡 2) (𝓡 3) (fun y : M => cE3 (saddlePsi η δ (Z y))) x v = 0 := by
        rw [hge.mfderiv_eq_v433]; exact h2
      exact hmimmU x (hfrU x hxfr hxA) v h1 h2'
    · have hxcl : x ∉ closure D := by
        intro hcl
        exact hxfr ⟨hcl, by rw [hDopen.interior_eq]; exact hxD⟩
      have hgerm : (f ∘ foot) =ᶠ[𝓝 x] (fun _ : M => c - lam * η) := by
        filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hxcl,
          hf.continuous.continuousAt (isOpen_Ioo.mem_nhds hxA)] with y hy hyb
        exact hfootval y (fun hyD => hy (subset_closure hyD)) hyb
      have hzero0 : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) (f ∘ foot) x = 0 := by
        rw [hgerm.mfderiv_eq_v433]; exact mfderiv_const
      have hcompF := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓘(ℝ, ℝ))
        (f := foot) (g := f) (x := x) hfdiff hfootdiff v
      have hzero : mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (foot x) (mfderiv (𝓡 2) (𝓡 2) foot x v) = 0 := by
        rw [← hcompF, hzero0]; exact ContinuousLinearMap.zero_apply v
      have hcompA := mfderiv_comp_apply (I := 𝓡 2) (I' := 𝓡 2) (I'' := 𝓡 3)
        (f := foot) (g := A₀) (x := x) hAdiff hfootdiff v
      have hAzero : mfderiv (𝓡 2) (𝓡 3) A₀ (foot x) (mfderiv (𝓡 2) (𝓡 2) foot x v) = 0 := by
        rw [← hcompA]; exact h2
      exact hfootimm x v h1 (hA₀imm x hxD hxA (mfderiv (𝓡 2) (𝓡 2) foot x v) hzero hAzero)
  have hbinj : ∀ x : M, x ∉ D → ∀ y : M, y ∉ D →
      f x ∈ Set.Ioo (c - lam * η) (c + lam * η) → f y ∈ Set.Ioo (c - lam * η) (c + lam * η) →
      f x = f y → A₀ (foot x) = A₀ (foot y) → x = y := by
    intro x hxD y hyD hxA hyA hfxy hg
    exact hA₀inj x y hxD hyD hxA hyA hfxy hg
  refine goodDrawingOn_of_pieces f (Set.Ioo (c - lam * η) (c + lam * η)) D hDopen
    (fun y : M => cE3 (saddlePsi η δ (Z y))) (fun y : M => A₀ (foot y))
    (fun x hxD hxA => hm_sm x (by rw [hDdef] at hxD; exact hxD.1))
    hbsm hfront
    (fun x hxD hxA v h1 h2 => hmimm' x hxD hxA v h1 h2)
    hbimm
    (fun x hxD y hyD hxA hyA hfxy hg =>
      hm_inj x (by rw [hDdef] at hxD; exact hxD.1) y (by rw [hDdef] at hyD; exact hyD.1)
        hfxy hg)
    hbinj
    (fun x hxD y hyD hxA hyA hfxy => hcross x hxD hxA y hyD hyA hfxy)

end Work.Drive.N2

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Filter

/-- The imaginary part of the square scales by the square of the (real) factor. -/
lemma im_sq_ofReal_mul (s : ℝ) (w : ℂ) :
    (((s : ℂ) * w) ^ 2).im = s ^ 2 * (w ^ 2).im := by
  have h1 : ((s : ℂ) * w) ^ 2 = ((s ^ 2 : ℝ) : ℂ) * (w ^ 2) := by
    rw [mul_pow, ← Complex.ofReal_pow]
  rw [h1, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

/-- **The seam identity of the saddle window.**

Let `φ` be a saddle chart whose complex coordinate `Z` is a real multiple `s • W` of the chart
coordinate `W` (this is the scaling that moves the model's collar to the right radius), and let `Φ`
be a flow whose chart coordinates solve the saddle model ODE and whose level function obeys
`f = c + lam · Re (Z ·)²` on the source (`lam > 0`).  If `x` is a collar point of the model, its
trajectory up to the anchor level `c - lam η` stays in the chart source, and `f (Φ (t, x)) = c - lam η`
(the landing row of the transport), then the transported point has exactly the chart coordinate that
the model assigns to `x`:

    Z (Φ (t, x)) = saddlePsi η δ (Z x).

This is the identity that makes the model piece and the transported piece agree at the frontier of the
model region (the `hfront` row of `Work.Drive.N2.saddleWindow_drawing_lam`). -/
theorem saddlePsi_foot_eq {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {Φ : ℝ × M → M} (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (Z : M → ℂ) {s c η δ r lam t : ℝ}
    (hs : s ≠ 0) (hlam : 0 < lam)
    (hZ : ∀ m : M, Z m = (s : ℂ) * ((φ m 0 : ℂ) + (φ m 1 : ℂ) * Complex.I))
    (hη : 0 < η) (hη' : η < 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1 / 10)
    (hODE : ∀ (y : M) (τ : ℝ),
      (∀ u ∈ Set.Icc (min 0 τ) (max 0 τ), Φ (u, y) ∈ φ.source) →
      HasDerivAt (fun σ : ℝ => φ (Φ (σ, y)) 0)
        (chartMult r (‖φ (Φ (τ, y))‖ ^ 2) * ((1 : ℝ) * φ (Φ (τ, y)) 0)) τ ∧
      HasDerivAt (fun σ : ℝ => φ (Φ (σ, y)) 1)
        (chartMult r (‖φ (Φ (τ, y))‖ ^ 2) * ((-1 : ℝ) * φ (Φ (τ, y)) 1)) τ)
    (hΦ0 : ∀ y : M, Φ (0, y) = y)
    (hΦcomp : ∀ (a b : ℝ) (y : M), Φ (a, Φ (b, y)) = Φ (a + b, y))
    (hΦcont : Continuous Φ)
    (hZcont : ContinuousOn Z φ.source)
    (hlev : ∀ y ∈ φ.source, f y = c + lam * ((Z y) ^ 2).re)
    (hmono : ∀ y : M, MonotoneOn (fun τ : ℝ => f (Φ (τ, y))) (Set.Ici 0))
    {x : M} {t : ℝ} (ht : t ≤ 0)
    (hconf : ∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, x) ∈ φ.source)
    (hcol : Z x ∈ saddleCollar η δ)
    (hxband : f x ∈ Set.Ioo (c - lam * η) (c + lam * η))
    (hfoot : f (Φ (t, x)) = c - lam * η) :
    Z (Φ (t, x)) = saddlePsi η δ (Z x) := by
  have hδ₂ : δ < 1 / 2 := by linarith
  have hlamne : lam ≠ 0 := ne_of_gt hlam
  -- the chart coordinate and the orbit invariant in it
  set W : M → ℂ := fun m => (φ m 0 : ℂ) + (φ m 1 : ℂ) * Complex.I with hWdef
  have hsub : Set.Icc (min 0 t) (max 0 t) = Set.Icc t 0 := by
    rw [min_eq_right ht, max_eq_left ht]
  have hconf' : ∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, x) ∈ φ.source := hconf
  have hinvW : ((W (Φ (t, x))) ^ 2).im = ((W x) ^ 2).im :=
    im_sq_eq_of_flow_chartODE Φ φ W (fun m => rfl) r hODE hΦ0 x t hconf'
  have hsq : ∀ m : M, ((Z m) ^ 2).im = s ^ 2 * ((W m) ^ 2).im := by
    intro m
    rw [hWdef, hZ m]
    exact im_sq_ofReal_mul s _
  have hinv : ∀ u ∈ Set.Icc t 0, ((Z (Φ (u, x))) ^ 2).im = ((Z x) ^ 2).im := by
    intro u hu
    have hsubu : Set.Icc (min 0 u) (max 0 u) ⊆ Set.Icc (min 0 t) (max 0 t) := by
      intro w hw
      obtain ⟨hw1, hw2⟩ := hw
      constructor
      · rcases le_total 0 u with h | h
        · rw [min_eq_left h] at hw1
          exact le_trans (min_le_left 0 t) hw1
        · rw [min_eq_right h] at hw1
          exact le_trans (by rw [min_eq_right ht]; exact hu.1) hw1
      · rcases le_total 0 u with h | h
        · rw [max_eq_right h] at hw2
          exact le_trans hw2 (le_trans hu.2 (le_max_left 0 t))
        · rw [max_eq_left h] at hw2
          exact le_trans hw2 (le_max_left 0 t)
    have himW : ((W (Φ (u, x))) ^ 2).im = ((W x) ^ 2).im :=
      im_sq_eq_of_flow_chartODE Φ φ W (fun m => rfl) r hODE hΦ0 x u
        (fun v hv => hconf v (hsubu hv))
    rw [hsq (Φ (u, x)), hsq x, himW]
  have hinvt : ((Z (Φ (t, x))) ^ 2).im = ((Z x) ^ 2).im := by
    rw [hsq (Φ (t, x)), hsq x, hinvW]
  -- the value range of the journey
  have hfrange : ∀ u ∈ Set.Icc t 0, f (Φ (u, x)) ∈ Set.Icc (c - lam * η) (c + lam * η) := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hu
    have hs1 : (0 : ℝ) ≤ u - t := by linarith
    have hs2 : u - t ≤ -t := by linarith
    have hmono' := hmono (Φ (t, x))
    have hlow : f (Φ ((u - t), Φ (t, x))) ≥ f (Φ (0, Φ (t, x))) :=
      hmono' (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs1) hs1
    have hup : f (Φ ((u - t), Φ (t, x))) ≤ f (Φ (-t, Φ (t, x))) :=
      hmono' (Set.mem_Ici.mpr hs1) (Set.mem_Ici.mpr (by linarith : (0 : ℝ) ≤ -t)) hs2
    have e1 : Φ (0, Φ (t, x)) = Φ (t, x) := hΦ0 _
    have e2 : Φ ((u - t), Φ (t, x)) = Φ (u, x) := by
      rw [hΦcomp, show u - t + t = u from by ring]
    have e3 : Φ (-t, Φ (t, x)) = Φ (0, x) := by
      rw [hΦcomp, show -t + t = (0 : ℝ) from by ring]
    rw [e1, hfoot] at hlow
    rw [e2] at hlow
    rw [e2] at hup
    rw [e3, hΦ0 x] at hup
    exact ⟨hlow, by linarith [hup, hxband.2]⟩
  -- the trajectory stays in the collar of the model
  have htrajcol : ∀ u ∈ Set.Icc t 0, Z (Φ (u, x)) ∈ saddleCollar η δ := by
    intro u hu
    have hsrc : Φ (u, x) ∈ φ.source := by
      refine hconf u ?_
      rw [Set.mem_Icc] at hu ⊢
      rw [min_eq_right ht, max_eq_left ht]
      exact hu
    have him := hinv u hu
    refine ⟨?_, ?_, ?_⟩
    · have h := hlev (Φ (u, x)) hsrc
      have hre : ((Z (Φ (u, x))) ^ 2).re = (f (Φ (u, x)) - c) / lam := by
        rw [h, add_sub_cancel_left, mul_div_cancel_left₀ _ hlamne]
      rw [hre, abs_div, abs_of_pos hlam, div_le_iff₀ hlam]
      have hv := hfrange u hu
      simp only [Set.mem_Icc] at hv
      rw [abs_le]
      exact ⟨by linarith [hv.1], by linarith [hv.2]⟩
    · rw [him]; exact hcol.2.1
    · rw [him]; exact hcol.2.2
  -- the square of the transported point
  have hfootsrc : Φ (t, x) ∈ φ.source := by
    refine hconf t ?_
    exact ⟨min_le_right 0 t, le_max_right 0 t⟩
  have hfootre : ((Z (Φ (t, x))) ^ 2).re = -η := by
    have h := hlev (Φ (t, x)) hfootsrc
    rw [hfoot] at h
    have h2 : lam * ((Z (Φ (t, x))) ^ 2).re = lam * (-η) := by linarith
    exact mul_left_cancel₀ hlamne h2
  have hzsq : ((Z (Φ (t, x))) ^ 2) = (-(η : ℂ)) + (((Z x) ^ 2).im : ℂ) * Complex.I := by
    refine Complex.ext ?_ ?_
    · simpa using hfootre
    · simpa using hinvt
  have hPsi_col : (saddlePsi η δ (Z x)) ^ 2
      = (-(η : ℂ)) + (((Z x) ^ 2).im : ℂ) * Complex.I :=
    (saddlePsi_collar hη hη' hδ hδ' hcol.1 hcol.2.1 hcol.2.2).1
  have hsqeq : (saddlePsi η δ (Z x)) ^ 2 = (Z (Φ (t, x))) ^ 2 := by
    rw [hPsi_col, hzsq]
  -- the model fixes the transported point's coordinate
  have hPsi_foot : saddlePsi η δ (Z (Φ (t, x))) = Z (Φ (t, x)) := by
    have hcol' := htrajcol t ⟨le_rfl, ht⟩
    have h2 := saddlePsi_collar hη hη' hδ hδ' hcol'.1 hcol'.2.1 hcol'.2.2
    have hzsq' : (Z (Φ (t, x))) ^ 2
        = (-(η : ℂ)) + (((Z (Φ (t, x))) ^ 2).im : ℂ) * Complex.I := by
      refine Complex.ext ?_ ?_
      · simpa using hfootre
      · simp
    have hsq2 : (saddlePsi η δ (Z (Φ (t, x)))) ^ 2 = (Z (Φ (t, x))) ^ 2 := by
      rw [h2.1, hzsq']
      simp [Complex.add_im, Complex.mul_im]
    have hfac : (saddlePsi η δ (Z (Φ (t, x))) - Z (Φ (t, x))) *
        (saddlePsi η δ (Z (Φ (t, x))) + Z (Φ (t, x))) = 0 := by
      have h' : (saddlePsi η δ (Z (Φ (t, x)))) ^ 2 - (Z (Φ (t, x))) ^ 2 = 0 := by
        rw [hsq2]; ring
      linear_combination h'
    rcases mul_eq_zero.mp hfac with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      have hneg : saddlePsi η δ (Z (Φ (t, x))) = -Z (Φ (t, x)) := eq_neg_of_add_eq_zero_left h
      have hpos := h2.2
      rw [hneg, neg_mul, Complex.neg_re] at hpos
      have hnn : ((Z (Φ (t, x))) * (starRingEnd ℂ) (Z (Φ (t, x)))).re = ‖Z (Φ (t, x))‖ ^ 2 := by
        rw [Complex.mul_conj]
        simp [Complex.ofReal_re, Complex.sq_norm]
      rw [hnn] at hpos
      linarith [sq_nonneg ‖Z (Φ (t, x))‖]
  -- collar constancy of the model along the trajectory
  have hconst : saddlePsi η δ (Z (Φ (t, x))) = saddlePsi η δ (Z x) := by
    have hpath : ContinuousOn (fun σ : ℝ => Φ (σ * t, x)) (Set.Icc (0 : ℝ) 1) :=
      (hΦcont.comp (by fun_prop : Continuous fun σ : ℝ => (σ * t, x))).continuousOn
    have hγcont : ContinuousOn (fun σ : ℝ => Z (Φ (σ * t, x))) (Set.Icc (0 : ℝ) 1) := by
      refine hZcont.comp hpath ?_
      intro σ hσ
      refine hconf (σ * t) ?_
      rw [min_eq_right ht, max_eq_left ht]
      obtain ⟨h1, h2⟩ := hσ
      constructor <;> nlinarith
    have hγC : ∀ σ ∈ Set.Icc (0 : ℝ) 1, Z (Φ (σ * t, x)) ∈ saddleCollar η δ := by
      intro σ hσ
      refine htrajcol (σ * t) ?_
      obtain ⟨h1, h2⟩ := hσ
      constructor <;> nlinarith
    have hγim : ∀ σ ∈ Set.Icc (0 : ℝ) 1,
        ((Z (Φ (σ * t, x))) ^ 2).im = ((Z (Φ ((0 : ℝ) * t, x))) ^ 2).im := by
      intro σ hσ
      have h1 : σ * t ∈ Set.Icc t 0 := by
        obtain ⟨h1, h2⟩ := hσ
        constructor <;> nlinarith
      have h2 : (0 : ℝ) * t ∈ Set.Icc t 0 := by
        rw [zero_mul]; exact ⟨ht, le_rfl⟩
      rw [hinv (σ * t) h1, hinv ((0 : ℝ) * t) h2]
    have := saddlePsi_collar_eq_of_continuousOn hη hη' hδ hδ' hγcont hγC hγim
    simpa [mul_one, zero_mul, hΦ0 x] using this
  rw [← hPsi_foot, hconst]

end Work.Drive.N2
