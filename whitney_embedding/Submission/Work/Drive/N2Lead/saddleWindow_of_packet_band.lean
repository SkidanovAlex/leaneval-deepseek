import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.N2.GoodDrawingFamily
import Submission.Work.Drive.N2.saddleScaled
import Submission.Work.Drive.N2Lead.saddlePsiWideCollar
import Submission.Work.Compat.MFDerivCongrV433

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter
open Work.Drive.N2

section BandEngine

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

open Classical in
/-- **The saddle-window assembly with the value band decoupled from the collar.**

This is `Work.Drive.N2.saddleWindow_drawing_lam` (`Submission/Work/Drive/N2/saddleScaled.lean`) with
an extra parameter `ηb` carrying the *value band* `(c - lam ηb, c + lam ηb)`: the collar
`saddleCollar η δ`, the model `saddlePsi η δ` and the anchor level `c - lam η` all stay at `η`.  The
band occurs in the statement only as the value set of the memberships, and the proof of
`saddleWindow_drawing_lam` never uses the band except through those hypotheses, so the proof is the
same text. -/
theorem saddleWindow_drawing_lam_band {f : M → ℝ} {c η δ c₀ lam ηb : ℝ}
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
      f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) → f y ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) →
      f x = f y → A₀ (foot x) = A₀ (foot y) → x = y)
    (hA₀imm : ∀ x : M, x ∉ saddleRegion U Z c₀ →
      f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) → ∀ v : TangentSpace (𝓡 2) (foot x),
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (foot x) v = 0 →
      mfderiv (𝓡 2) (𝓡 3) A₀ (foot x) v = 0 → v = 0)
    (hfrU : ∀ x : M, x ∈ frontier (saddleRegion U Z c₀) →
      f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) → x ∈ U)
    (hfootval : ∀ x : M, x ∉ saddleRegion U Z c₀ →
      f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) → f (foot x) = c - lam * η)
    (hfront : ∀ x : M, x ∈ frontier (saddleRegion U Z c₀) →
      f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) →
      (fun y : M => cE3 (saddlePsi η δ (Z y))) =ᶠ[𝓝 x] (fun y : M => A₀ (foot y)))
    (hcross : ∀ x : M, x ∈ saddleRegion U Z c₀ →
      f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) →
      ∀ y : M, y ∉ saddleRegion U Z c₀ →
      f y ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) → f x = f y →
      cE3 (saddlePsi η δ (Z x)) ≠ A₀ (foot y)) :
    GoodDrawingOn f (Set.Ioo (c - lam * ηb) (c + lam * ηb))
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
  have hmimm' : ∀ x ∈ D, f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) →
      ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 →
      mfderiv (𝓡 2) (𝓡 3) (fun y : M => cE3 (saddlePsi η δ (Z y))) x v = 0 → v = 0 := by
    intro x hxD _ v h1 h2
    exact hmimmU x hxD.1 v h1 h2
  -- the transported piece
  have hbsm : ∀ x : M, x ∉ D → f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) →
      ContMDiffAt (𝓡 2) (𝓡 3) ∞ (fun y : M => A₀ (foot y)) x :=
    fun x _ _ => (hA₀ (foot x)).comp x (hfoot x)
  have hbimm : ∀ x : M, x ∉ D → f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) →
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
      f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) → f y ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) →
      f x = f y → A₀ (foot x) = A₀ (foot y) → x = y := by
    intro x hxD y hyD hxA hyA hfxy hg
    exact hA₀inj x y hxD hyD hxA hyA hfxy hg
  refine goodDrawingOn_of_pieces f (Set.Ioo (c - lam * ηb) (c + lam * ηb)) D hDopen
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

/-- **The two anchor rows at the feet, with the band decoupled from the collar.**

`Work.Drive.N2.saddleWindow_anchorRows_of_foot` (`Submission/Work/Drive/N2/levelSeparatingMap.lean`)
with the value band parameter `ηb` decoupled from the collar size `η`: the helper is band-agnostic
(its `η` occurs only in the two `Set.Ioo (c - lam * η) (c + lam * η)` memberships), so this is the
same statement and the same proof with `η ↦ ηb` in the band spots. -/
theorem saddleWindow_anchorRows_of_foot_band {f : M → ℝ} {c c₀ lam a ηb : ℝ}
    {U : Set M} {Z : M → ℂ}
    {foot : M → M} {F : Set M} {A₀ : M → EuclideanSpace ℝ (Fin 3)}
    (hfootinj : ∀ x y : M, f x = f y → foot x = foot y → x = y)
    (hfootval : ∀ y : M, y ∉ saddleRegion U Z c₀ →
      f y ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) → f (foot y) = a)
    (hF : ∀ y : M, y ∉ saddleRegion U Z c₀ →
      f y ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) → foot y ∈ F)
    (hAinj : ∀ x ∈ F, ∀ y ∈ F, f x = a → f y = a → A₀ x = A₀ y → x = y)
    (hAimm : ∀ x ∈ F, f x = a → ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 →
      mfderiv (𝓡 2) (𝓡 3) A₀ x v = 0 → v = 0) :
    (∀ x y : M, x ∉ saddleRegion U Z c₀ → y ∉ saddleRegion U Z c₀ →
      f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) →
      f y ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) → f x = f y →
      A₀ (foot x) = A₀ (foot y) → x = y) ∧
    (∀ x : M, x ∉ saddleRegion U Z c₀ →
      f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) →
      ∀ v : TangentSpace (𝓡 2) (foot x),
        mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f (foot x) v = 0 →
        mfderiv (𝓡 2) (𝓡 3) A₀ (foot x) v = 0 → v = 0) := by
  refine ⟨?_, ?_⟩
  · intro x y hxD hyD hxA hyA hfxy hg
    exact hfootinj x y hfxy (hAinj (foot x) (hF x hxD hxA) (foot y) (hF y hyD hyA)
      (hfootval x hxD hxA) (hfootval y hyD hyA) hg)
  · intro x hxD hxA v hdf hdA
    exact hAimm (foot x) (hF x hxD hxA) (hfootval x hxD hxA) v hdf hdA

end BandEngine

open scoped Manifold ContDiff Topology in
open Classical in
/-- **The saddle window with a band wider than its collar** (Tier `D2a` of
`Submission/Work/Drive/N2Lead/NOTES_LEAD_coherentWindows.md` §4/§5).  This is
`Work.Drive.N2.saddleWindow_drawing_of_planarPicture` (`Submission/Work/Drive/N2/levelSeparatingMap.lean`)
with the *value band* parameter `ηb` decoupled from the *collar* size `η`: the same two-piece picture
(model `cE3 ∘ saddlePsi η δ ∘ Z` on the region `saddleRegion U Z c₀`, the transported anchor picture
`A ∘ foot` off it) is a good drawing on the wider band `(c - lam * ηb, c + lam * ηb) ⊇ (c - lam * η,
c + lam * η)`, so that the anchor level `c - lam * η` is interior to the band for `ηb > η` (the case
`ηb = 4η/3` is the one the saddle window of the certified-window design consumes).  Every hypothesis
mentioning the band is widened accordingly; the anchor-level rows (`hAinj`, `hAimm`, `hApin`,
`hApos`) stay at the level `c - lam * η`.  The intended proof is the *same text* as the existing
result: the band occurs only in the hypotheses and through `isOpen_Ioo.mem_nhds`, and the helper
`saddleWindow_anchorRows_of_foot` is equally band-agnostic, so copy both with `η ↦ ηb` in the band
spots (its helper `saddleWindow_anchorRows_of_foot` is in `Work.Drive.N2`; `GoodDrawingOn.mono` does
not give this, the direction is the other way).  The result goes in namespace `Work.Drive.N2Lead`. -/
theorem saddleWindow_of_packet_band {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {f : M → ℝ} {c η δ c₀ lam ηb : ℝ}
    (hη : 0 < η) (hη' : η < 1 / 10) (hδ : 0 < δ) (hδ' : δ < 1 / 10) (hlam : lam ≠ 0)
    (hc₀ : 2 - 2 * δ < c₀) (hc₀' : c₀ < 2) (hηb : η ≤ ηb)
    {U : Set M} (hU : IsOpen U) {Z : M → ℂ}
    (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    (hZsm : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z U)
    (hZinj : Set.InjOn Z U)
    (hZimm : ∀ x ∈ U, Function.Injective (mfderiv (𝓡 2) 𝓘(ℝ, ℂ) Z x))
    (hlev : ∀ x ∈ U, f x = c + lam * ((Z x) ^ 2).re)
    {foot : M → M} (hfoot : ∀ x : M, ContMDiffAt (𝓡 2) (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) foot x)
    (hfootinj : ∀ x y : M, f x = f y → foot x = foot y → x = y)
    (hfootimm : ∀ x : M, ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 →
      mfderiv (𝓡 2) (𝓡 2) foot x v = 0 → v = 0)
    (hfootval : ∀ y : M, y ∉ Work.Drive.N2.saddleRegion U Z c₀ →
      f y ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) → f (foot y) = c - lam * η)
    (hfrU : ∀ x : M, x ∈ frontier (Work.Drive.N2.saddleRegion U Z c₀) →
      f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) → x ∈ U)
    {θ : M → ℝ} (_hθsm : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) θ)
    (hθ01 : ∀ x : M, 0 ≤ θ x ∧ θ x ≤ 1)
    {A : M → EuclideanSpace ℝ (Fin 3)}
    (hAsm : ∀ x : M, ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) A x)
    (hAinj : ∀ x y : M, f x = c - lam * η → f y = c - lam * η → A x = A y → x = y)
    (hAimm : ∀ x : M, f x = c - lam * η → ∀ v : TangentSpace (𝓡 2) x,
      mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x v = 0 →
      mfderiv (𝓡 2) (𝓡 3) A x v = 0 → v = 0)
    (hApin : ∀ x : M, f x = c - lam * η → θ x = 1 →
      A x = Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ (Z x)))
    (hApos : ∀ x : M, f x = c - lam * η → θ x < 1 → 0 < (A x) 2)
    (hseam : ∀ y : M, f y ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) →
      Z y ∈ Work.Drive.N2.saddleCollar ηb δ →
      Z (foot y) = Work.Drive.N2.saddlePsi η δ (Z y))
    (hcolFr : ∀ x : M, x ∈ frontier (Work.Drive.N2.saddleRegion U Z c₀) →
      f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) →
      ∀ᶠ y in 𝓝 x, f y ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) →
        Z y ∈ Work.Drive.N2.saddleCollar ηb δ)
    (hfootFrint : ∀ x : M, x ∈ frontier (Work.Drive.N2.saddleRegion U Z c₀) →
      f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) →
      foot x ∈ interior (θ ⁻¹' {1}))
    (hlandFr : ∀ x : M, x ∈ frontier (Work.Drive.N2.saddleRegion U Z c₀) →
      f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) → ∀ᶠ y in 𝓝 x, f (foot y) = c - lam * η)
    (hbig : ∀ x : M, x ∉ Work.Drive.N2.saddleRegion U Z c₀ →
      f x ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) → θ (foot x) = 1 →
      c₀ ≤ |((Z (foot x)) ^ 2).im|) :
    Work.Drive.N2.GoodDrawingOn f (Set.Ioo (c - lam * ηb) (c + lam * ηb))
      (fun x : M => if x ∈ Work.Drive.N2.saddleRegion U Z c₀ then
        Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ (Z x))
      else A (foot x)) := by
  have hδ₂ : δ < 1 / 2 := by linarith
  have h2le : (0 : ℝ) ≤ 2 - 4 * δ := by linarith
  -- ## the two anchor rows at the feet
  have hAnch := saddleWindow_anchorRows_of_foot_band (ηb := ηb) (a := c - lam * η)
    (F := {x : M | f x = c - lam * η}) hfootinj hfootval (fun y hyD hyA => hfootval y hyD hyA)
    (fun x hx y hy _ _ h => hAinj x y hx hy h)
    (fun x hx _ v hdf hv => hAimm x hx v hdf hv)
  refine saddleWindow_drawing_lam_band (ηb := ηb) hη hη' hδ hδ' hlam hc₀ hc₀' hU hZsm hZinj hZimm
    hlev hf hAsm hfoot hfootinj hfootimm hAnch.1 hAnch.2 hfrU hfootval ?_ ?_
  · -- ## the front row
    intro x hxfr hxA
    have hfootV : ∀ᶠ y in 𝓝 x, foot y ∈ interior (θ ⁻¹' {1}) :=
      ((hfoot x).continuousAt).preimage_mem_nhds
        (isOpen_interior.mem_nhds (hfootFrint x hxfr hxA))
    have hband : ∀ᶠ y in 𝓝 x, f y ∈ Set.Ioo (c - lam * ηb) (c + lam * ηb) :=
      hf.continuous.continuousAt (isOpen_Ioo.mem_nhds hxA)
    filter_upwards [hband, hfootV, hlandFr x hxfr hxA, hcolFr x hxfr hxA] with y hyb hθy hlandy hcol
    have hθy1 : θ (foot y) = 1 := by
      have h1 : foot y ∈ θ ⁻¹' {1} := interior_subset hθy
      simpa using h1
    have hcoly : Z y ∈ Work.Drive.N2.saddleCollar ηb δ := hcol hyb
    have hpt : A (foot y) = Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ (Z (foot y))) :=
      hApin (foot y) hlandy hθy1
    have hseamy : Z (foot y) = Work.Drive.N2.saddlePsi η δ (Z y) := hseam y hyb hcoly
    have hidem : Work.Drive.N2.saddlePsi η δ (Work.Drive.N2.saddlePsi η δ (Z y))
        = Work.Drive.N2.saddlePsi η δ (Z y) :=
      Work.Drive.N2Lead.saddlePsi_idempotent_of_mem_collarWide hη hη' hηb hδ hδ'
        hcoly.1 hcoly.2.1 hcoly.2.2
    show Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ (Z y)) = A (foot y)
    rw [hpt, hseamy, hidem]
  · -- ## the cross row
    intro x hxD hxA y hyD hyA hfxy
    have hfy : f (foot y) = c - lam * η := hfootval y hyD hyA
    by_cases hθy : θ (foot y) = 1
    · -- the pinned foot: the algebra of the squares
      intro hcoll
      have h1 : Work.Drive.N2.saddlePsi η δ (Z x)
          = Work.Drive.N2.saddlePsi η δ (Z (foot y)) := by
        have h := hApin (foot y) hfy hθy
        exact Work.Drive.N2.cE3_injective (hcoll.trans h)
      have hs : (Work.Drive.N2.saddlePsi η δ (Z x)) ^ 2
          = (Work.Drive.N2.saddlePsi η δ (Z (foot y))) ^ 2 := by rw [h1]
      rw [Work.Drive.N2.saddlePsi_sq hδ h2le, Work.Drive.N2.saddlePsi_sq hδ h2le] at hs
      have him : ((Z x) ^ 2).im = ((Z (foot y)) ^ 2).im := by
        have h := congrArg Complex.im hs
        rwa [Work.Drive.N2.saddlePhi_im, Work.Drive.N2.saddlePhi_im] at h
      have hxlt : |((Z x) ^ 2).im| < c₀ := hxD.2
      have hyge : c₀ ≤ |((Z (foot y)) ^ 2).im| := hbig y hyD hyA hθy
      rw [him] at hxlt
      linarith
    · -- the unpinned foot: the third coordinate is positive
      intro hcoll
      have hθlt : θ (foot y) < 1 := lt_of_le_of_ne (hθ01 (foot y)).2 hθy
      have h3 : 0 < (A (foot y)) 2 := hApos (foot y) hfy hθlt
      have h2 : (Work.Drive.N2.cE3 (Work.Drive.N2.saddlePsi η δ (Z x))) 2 = 0 :=
        Work.Drive.N2.cE3_apply_two _
      rw [hcoll] at h2
      linarith

end Work.Drive.N2Lead
