import Mathlib
import Submission.Work.Drive.Morse
import Submission.Work.Drive.Push.localGraphFunction
import Submission.Work.Noncompact.CompressionTube.isLocalDiffeomorph_of_immersion
import Submission.Work.Drive.N2.mfderiv_ne_zero_of_flow

/-!
# The local lift of the level-circle angle

This file proves `Work.Drive.N2.exists_localLift`: around a point `γ s₀` of a `2π`-periodic
immersive parametrisation of a circle of the reference level `a` of a level flow `Φ`, there are an
open neighbourhood `D` and a smooth function `u` which computes, modulo `2π`, the parameter of the
crossing of the flow line with the circle.

## The idea

Consider the map `Ψ (t, s) = Φ (t, γ s)`.  Since `Φ` raises the level function `f` at unit speed on
the band (so `mfderiv f (γ s) (flow direction) = 1`) while `mfderiv f (γ s) (γ'(s)) = 0`, the two
tangent directions are independent everywhere, so `Ψ` is a local diffeomorphism
(`mfderiv Ψ p` is injective for every `p`).  Its local inverse `σ` at `p₀ = (0, s₀)` then gives
`u = σ.2`, and the uniqueness clause follows from the flow law: if `Φ (t, γ s) = Φ (t', γ s')` with
`|t - t'| < η` then the (reference level) points `γ s, γ s'` are joined by a flow segment of length
`< η`, which forces that length to be `0`, and then `γ` injectivity modulo `2π` finishes.

The only genuine input is the "unit speed in the flow direction" computation, which is extracted
from the level law `f (Φ (t, x)) = f x + t` by differentiating at a point of the reference level.
-/

set_option backward.isDefEq.respectTransparency false

/-!
# `exists_localLift` on the `N2pc` side

Verbatim copy of `Submission.Work.Drive.N2.exists_localLift` in which the auxiliary lemma
`injective_of_ne_zero` is renamed to `ll_injective_of_ne_zero` (and its one internal use updated).
The original name is declared again by the `N2pc` mirror `Submission.Work.Drive.N2pc.roundConfigPicture`,
so the two modules cannot be loaded in one file; the rename lets
`Submission.Work.Drive.N2.bandAngle_of_window` (and the `N2Lead` window-model lane behind it) share a
file with the movie assembly.  The statement proved (`exists_localLift`) is unchanged.
-/

namespace Work.Drive.N2

open Classical
open scoped Manifold ContDiff Topology
open Set Function

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- **A nonzero continuous linear map `ℝ →L[ℝ] N` is injective.** -/
lemma ll_injective_of_ne_zero {N : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
    {L : ℝ →L[ℝ] N} (hL : L ≠ 0) : Function.Injective L := by
  intro a b hab
  have h0 : L (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hL1 : L 1 ≠ 0 := by
    intro h
    refine hL (ContinuousLinearMap.ext fun x => ?_)
    have h3 : L (x • (1 : ℝ)) = x • L 1 := map_smul L x (1 : ℝ)
    rw [show x • (1 : ℝ) = x from by ring, h, smul_zero] at h3
    exact h3
  have h2 : (a - b) • L (1 : ℝ) = 0 := by
    have h3 : L ((a - b) • (1 : ℝ)) = (a - b) • L (1 : ℝ) := map_smul L (a - b) (1 : ℝ)
    rw [show (a - b) • (1 : ℝ) = a - b from by ring, h0] at h3
    exact h3.symm
  rcases smul_eq_zero.mp h2 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hL1

/-- **The flow direction raises `f` at unit speed at a point of the reference level.**
`X s` denotes the derivative at time `0` of the flow line through `γ s`. -/
lemma flowDir_scalar {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ f)
    {a η : ℝ} (hη : 0 < η) {Φ : ℝ × M → M}
    (hΦsm : ContMDiff (𝓘(ℝ,ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ)
    (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hlaw : ∀ (x : M) (t : ℝ), f x ∈ Set.Icc a (a + η) → f x + t ∈ Set.Icc a (a + η) →
      f (Φ (t, x)) = f x + t)
    {γ : ℝ → M} (hγlev : ∀ s, f (γ s) = a) (s : ℝ) :
    mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ s)
      (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (fun z : ℝ => Φ (z, γ s)) 0 1) = 1 := by
  have hfst : ContMDiff 𝓘(ℝ,ℝ) ((𝓘(ℝ,ℝ)).prod (𝓡 2)) ∞ (fun z : ℝ => (z, γ s)) :=
    contMDiff_id.prodMk contMDiff_const
  have hcd : ContMDiff 𝓘(ℝ,ℝ) (𝓡 2) ∞ (fun z : ℝ => Φ (z, γ s)) := hΦsm.comp hfst
  have hHcd : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) ∞ (fun z : ℝ => f (Φ (z, γ s))) := hf.comp hcd
  have hφdiff : DifferentiableAt ℝ (fun z : ℝ => f (Φ (z, γ s))) 0 :=
    (hHcd.contMDiffAt.mdifferentiableAt (by simp)).differentiableAt
  have hvan : ∀ z ∈ Set.Icc (0:ℝ) η, f (Φ (z, γ s)) = f (Φ (0, γ s)) + z := by
    intro z hz
    have hx : f (γ s) ∈ Set.Icc a (a + η) := by rw [hγlev]; exact ⟨le_rfl, by linarith [hz.2]⟩
    have hxt : f (γ s) + z ∈ Set.Icc a (a + η) := by
      rw [hγlev]; exact ⟨by linarith [hz.1], by linarith [hz.2]⟩
    have h := hlaw (γ s) z hx hxt
    rw [hγlev] at h
    rw [hΦ0, hγlev]
    exact h
  have hder1 : deriv (fun z : ℝ => f (Φ (z, γ s))) 0 = 1 :=
    deriv_eq_one_of_eqOn_Icc hη ⟨le_refl 0, hη.le⟩ hvan hφdiff
  have hchain : deriv (fun z : ℝ => f (Φ (z, γ s))) 0
      = mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ s)
          (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (fun z : ℝ => Φ (z, γ s)) 0 (1:ℝ)) := by
    rw [← fderiv_apply_one_eq_deriv, ← mfderiv_eq_fderiv]
    change (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (f ∘ fun z : ℝ => Φ (z, γ s)) 0) (1:ℝ)
      = (mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ s))
          ((mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (fun z : ℝ => Φ (z, γ s)) 0) (1:ℝ))
    rw [mfderiv_comp_apply_of_eq (0:ℝ) (hf.contMDiffAt.mdifferentiableAt (by simp))
      (hcd.contMDiffAt.mdifferentiableAt (by simp)) (hΦ0 (γ s)) (1:ℝ)]
  rw [← hchain, hder1]

/-- **The derivative of `f` along the level curve `γ` vanishes.** -/
lemma mfderiv_f_along_gamma_eq_zero {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ,ℝ) ∞ f)
    {a : ℝ} {γ : ℝ → M} (hγsm : ContMDiff 𝓘(ℝ,ℝ) (𝓡 2) ∞ γ) (hγlev : ∀ s, f (γ s) = a)
    (s w : ℝ) :
    mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ s) (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ s w) = 0 := by
  have hmdγ : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2) γ s := hγsm.contMDiffAt.mdifferentiableAt (by simp)
  have hmdf : MDifferentiableAt (𝓡 2) 𝓘(ℝ,ℝ) f (γ s) := hf.contMDiffAt.mdifferentiableAt (by simp)
  have h1 := mfderiv_comp_apply (f := γ) s hmdf hmdγ w
  have h2 : mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun u : ℝ => f (γ u)) s w = 0 := by
    have he : (fun u : ℝ => f (γ u)) = (fun _ => a) := funext (fun u => hγlev u)
    rw [he, mfderiv_const]
    rfl
  rw [← h1]
  exact h2

/-- **Two points of the reference level joined by a short flow segment coincide.**
If `γ d = Φ (δ, γ b)` with `|δ| < η` then `δ = 0`. -/
lemma flow_time_eq_zero_of_eq {f : M → ℝ} {a η : ℝ} {Φ : ℝ × M → M}
    (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦcomp : ∀ (s t : ℝ) (x : M), Φ (s, Φ (t, x)) = Φ (s + t, x))
    (hlaw : ∀ (x : M) (t : ℝ), f x ∈ Set.Icc a (a + η) → f x + t ∈ Set.Icc a (a + η) →
      f (Φ (t, x)) = f x + t)
    {γ : ℝ → M} (hγlev : ∀ s, f (γ s) = a)
    {δ b d : ℝ} (hδ : |δ| < η) (h : γ d = Φ (δ, γ b)) : δ = 0 := by
  obtain ⟨hδgt, hδlt⟩ := abs_lt.mp hδ
  rcases lt_trichotomy δ 0 with hd | hd | hd
  · have hx : f (γ d) ∈ Set.Icc a (a + η) := by rw [hγlev]; exact ⟨le_rfl, by linarith⟩
    have hxt : f (γ d) + (-δ) ∈ Set.Icc a (a + η) := by
      rw [hγlev]; exact ⟨by linarith, by linarith⟩
    have hh := hlaw (γ d) (-δ) hx hxt
    rw [hγlev] at hh
    have hcancel : Φ (-δ, γ d) = γ b := by
      rw [h, hΦcomp, neg_add_cancel, hΦ0]
    rw [hcancel] at hh
    rw [hγlev] at hh
    linarith
  · exact hd
  · have hx : f (γ b) ∈ Set.Icc a (a + η) := by rw [hγlev]; exact ⟨le_rfl, by linarith⟩
    have hxt : f (γ b) + δ ∈ Set.Icc a (a + η) := by
      rw [hγlev]; exact ⟨by linarith, by linarith⟩
    have hh := hlaw (γ b) δ hx hxt
    rw [hγlev] at hh
    rw [← h] at hh
    rw [hγlev] at hh
    linarith


/-- **The derivative of `(t, s) ↦ Φ (t, γ s)` at `(0, s)` is injective.**

(This is the linearised form of the statement that near the reference level the level flow is a
local diffeomorphism onto its image.) -/
local notation "𝔼" => EuclideanSpace ℝ (Fin 2)

lemma flowParam_injective_at_zero {f : M → ℝ} {Φ : ℝ × M → M} {γ : ℝ → M}
    (hΦsm : ContMDiff (𝓘(ℝ,ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ)
    (hγsm : ContMDiff 𝓘(ℝ,ℝ) (𝓡 2) ∞ γ)
    (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦcomp : ∀ (s t : ℝ) (x : M), Φ (s, Φ (t, x)) = Φ (s + t, x))
    (hX : ∀ s : ℝ, mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ s)
      (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (fun z : ℝ => Φ (z, γ s)) 0 1) = 1)
    (hγf : ∀ (s w : ℝ), mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ s)
      (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ s w) = 0)
    (hinjγ : ∀ s : ℝ, Function.Injective (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ s)) :
    ∀ s : ℝ, ∀ v : ℝ × ℝ,
      mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) (fun q : ℝ × ℝ => Φ (q.1, γ q.2)) ((0:ℝ), s) v = 0 → v = 0 := by
  intro s v hv
  let Ψ : ℝ × ℝ → M := fun q => Φ (q.1, γ q.2)
  have hv' : mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) Ψ ((0:ℝ), s) v = 0 := hv
  have hΨsm : ContMDiff 𝓘(ℝ,ℝ×ℝ) (𝓡 2) ∞ Ψ := by
    show ContMDiff 𝓘(ℝ,ℝ×ℝ) (𝓡 2) ∞ (fun q : ℝ × ℝ => Φ (q.1, γ q.2))
    have h1 : ContMDiff 𝓘(ℝ,ℝ×ℝ) 𝓘(ℝ,ℝ) ∞ (fun q : ℝ×ℝ => q.1) :=
      ContinuousLinearMap.contMDiff (ContinuousLinearMap.fst ℝ ℝ ℝ)
    have h2 : ContMDiff 𝓘(ℝ,ℝ×ℝ) (𝓡 2) ∞ (fun q : ℝ×ℝ => γ q.2) :=
      hγsm.comp (ContinuousLinearMap.contMDiff (ContinuousLinearMap.snd ℝ ℝ ℝ))
    exact hΦsm.comp (h1.prodMk h2)
  let W : 𝔼 := mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) Ψ ((0:ℝ), s) v
  let L0 : ℝ →L[ℝ] 𝔼 := mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (fun z : ℝ => Φ (z, γ s)) 0
  let X0 : 𝔼 := L0 1
  let Y : 𝔼 := mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ s v.2
  let Z : 𝔼 := L0 (-v.1)
  let Fd : 𝔼 →L[ℝ] ℝ := mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ s)
  have hW : W = 0 := hv'
  have hFdX : Fd X0 = 1 := hX s
  have hFdY : Fd Y = 0 := hγf s v.2
  have hZX : Z = (-v.1) • X0 := by
    show L0 (-v.1) = (-v.1) • L0 1
    have h := map_smul L0 (-v.1) (1:ℝ)
    rw [show (-v.1) • (1:ℝ) = -v.1 from by ring] at h
    exact h
  have hΦmd2 : MDifferentiableAt ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (𝓡 2) Φ ((0:ℝ), γ s) :=
    hΦsm.contMDiffAt.mdifferentiableAt (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
  have hPW : mfderiv ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (𝓡 2) Φ ((0:ℝ), γ s)
      ((1:ℝ), (0 : 𝔼)) = X0 := by
    have h := mfderiv_prod_eq_add_apply (f := Φ) (p := ((0:ℝ), γ s))
      (v := ((1:ℝ), (0 : 𝔼))) hΦmd2
    rw [h]
    show (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (fun z : ℝ => Φ (z, γ s)) 0) 1
        + (mfderiv (𝓡 2) (𝓡 2) (fun y : M => Φ (0, y)) (γ s)) (0 : 𝔼) = X0
    rw [show (mfderiv (𝓡 2) (𝓡 2) (fun y : M => Φ (0, y)) (γ s)) (0 : 𝔼) = 0 from map_zero _]
    rw [add_zero]
    rfl
  -- the direction (-v.1, 0)
  have hPhiZ : mfderiv ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (𝓡 2) Φ ((0:ℝ), γ s)
      ((-v.1, (0 : 𝔼)) : ℝ × 𝔼) = Z := by
    have h := mfderiv_prod_eq_add_apply (f := Φ) (p := ((0:ℝ), γ s))
      (v := ((-v.1, (0 : 𝔼)) : ℝ × 𝔼)) hΦmd2
    rw [h]
    show (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (fun z : ℝ => Φ (z, γ s)) 0) (-v.1)
        + (mfderiv (𝓡 2) (𝓡 2) (fun y : M => Φ (0, y)) (γ s)) (0 : 𝔼) = Z
    rw [show (mfderiv (𝓡 2) (𝓡 2) (fun y : M => Φ (0, y)) (γ s)) (0 : 𝔼) = 0 from map_zero _]
    rw [add_zero]
    rfl
  -- H q = (-q.1, Ψ q)
  let H : ℝ × ℝ → ℝ × M := fun q => (-q.1, Ψ q)
  have hHval : H ((0:ℝ), s) = ((0:ℝ), γ s) := by
    apply Prod.ext
    · show (-(0:ℝ)) = (0:ℝ)
      ring
    · show Ψ ((0:ℝ), s) = γ s
      show Φ ((0:ℝ), γ s) = γ s
      exact hΦ0 (γ s)
  have hHmd : MDifferentiableAt 𝓘(ℝ,ℝ×ℝ) ((𝓘(ℝ,ℝ)).prod (𝓡 2)) H ((0:ℝ), s) := by
    show MDifferentiableAt 𝓘(ℝ,ℝ×ℝ) ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (fun q : ℝ × ℝ => (-q.1, Ψ q)) ((0:ℝ), s)
    have ha : ContMDiffAt 𝓘(ℝ,ℝ×ℝ) 𝓘(ℝ,ℝ) ∞ (fun q : ℝ × ℝ => -q.1) ((0:ℝ), s) :=
      ContinuousLinearMap.contMDiffAt (-(ContinuousLinearMap.fst ℝ ℝ ℝ))
    have hb : ContMDiffAt 𝓘(ℝ,ℝ×ℝ) (𝓡 2) ∞ Ψ ((0:ℝ), s) := hΨsm.contMDiffAt
    exact (ha.prodMk hb).mdifferentiableAt (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
  have hHdv : mfderiv 𝓘(ℝ,ℝ×ℝ) ((𝓘(ℝ,ℝ)).prod (𝓡 2)) H ((0:ℝ), s) v
      = ((-v.1, W) : ℝ × 𝔼) := by
    have ha : ContMDiffAt 𝓘(ℝ,ℝ×ℝ) 𝓘(ℝ,ℝ) ∞ (fun q : ℝ × ℝ => -q.1) ((0:ℝ), s) :=
      ContinuousLinearMap.contMDiffAt (-(ContinuousLinearMap.fst ℝ ℝ ℝ))
    have hb : ContMDiffAt 𝓘(ℝ,ℝ×ℝ) (𝓡 2) ∞ Ψ ((0:ℝ), s) := hΨsm.contMDiffAt
    have hprod := mfderiv_prodMk (ha.mdifferentiableAt (show (∞ : WithTop ℕ∞) ≠ 0 by simp))
      (hb.mdifferentiableAt (show (∞ : WithTop ℕ∞) ≠ 0 by simp))
    have hApp : mfderiv 𝓘(ℝ,ℝ×ℝ) ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (fun q : ℝ × ℝ => (-q.1, Ψ q)) ((0:ℝ), s) v
        = ((mfderiv 𝓘(ℝ,ℝ×ℝ) 𝓘(ℝ,ℝ) (fun q : ℝ × ℝ => -q.1) ((0:ℝ), s)) v, W) := by
      rw [hprod]
      exact ContinuousLinearMap.prod_apply _ _ v
    have hneg : mfderiv 𝓘(ℝ,ℝ×ℝ) 𝓘(ℝ,ℝ) (fun q : ℝ × ℝ => -q.1) ((0:ℝ), s)
        = -(ContinuousLinearMap.fst ℝ ℝ ℝ) := by
      rw [mfderiv_eq_fderiv]
      exact ContinuousLinearMap.fderiv (-(ContinuousLinearMap.fst ℝ ℝ ℝ))
    show mfderiv 𝓘(ℝ,ℝ×ℝ) ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (fun q : ℝ × ℝ => (-q.1, Ψ q)) ((0:ℝ), s) v = ((-v.1, W) : ℝ × 𝔼)
    rw [hApp, hneg]
    rfl
  have hchain : mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) (fun q : ℝ × ℝ => Φ (-q.1, Ψ q)) ((0:ℝ), s) v
      = mfderiv ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (𝓡 2) Φ ((0:ℝ), γ s) ((-v.1, (0 : 𝔼)) : ℝ × 𝔼) := by
    have hΦmdH : MDifferentiableAt ((𝓘(ℝ,ℝ)).prod (𝓡 2)) (𝓡 2) Φ (H ((0:ℝ), s)) :=
      hΦsm.contMDiffAt.mdifferentiableAt (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
    have hcomp := mfderiv_comp_apply (f := H) ((0:ℝ), s) hΦmdH hHmd v
    rw [hHdv, hHval, hW] at hcomp
    exact hcomp
  -- G = (fun q => γ q.2)
  have hGfun : (fun q : ℝ × ℝ => Φ (-q.1, Ψ q)) = (fun q : ℝ × ℝ => γ q.2) := by
    funext q
    show Φ (-q.1, Φ (q.1, γ q.2)) = γ q.2
    rw [hΦcomp, neg_add_cancel, hΦ0]
  have hh2 : mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) (fun q : ℝ × ℝ => γ q.2) ((0:ℝ), s) v = Y := by
    have h2a : mfderiv 𝓘(ℝ,ℝ×ℝ) 𝓘(ℝ,ℝ) (fun q : ℝ × ℝ => q.2) ((0:ℝ), s)
        = ContinuousLinearMap.snd ℝ ℝ ℝ := by
      rw [mfderiv_eq_fderiv]
      exact ContinuousLinearMap.fderiv (ContinuousLinearMap.snd ℝ ℝ ℝ)
    have h2 : mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) (fun q : ℝ × ℝ => γ q.2) ((0:ℝ), s)
        = mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ s ∘SL ContinuousLinearMap.snd ℝ ℝ ℝ := by
      rw [← h2a]
      refine mfderiv_comp (f := fun q : ℝ × ℝ => q.2) (g := γ) ((0:ℝ), s) ?_ ?_
      · exact hγsm.contMDiffAt.mdifferentiableAt (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
      · exact (ContinuousLinearMap.contMDiffAt (ContinuousLinearMap.snd ℝ ℝ ℝ)).mdifferentiableAt
          (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
    rw [h2]
    rfl
  have hYZ : Y = Z := by
    have h1 : (show 𝔼 from mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) (fun q : ℝ × ℝ => Φ (-q.1, Ψ q)) ((0:ℝ), s) v) = Z := by
      rw [hchain, hPhiZ]
    have h2 : (show 𝔼 from mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) (fun q : ℝ × ℝ => Φ (-q.1, Ψ q)) ((0:ℝ), s) v) = Y := by
      have hfeq : mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) (fun q : ℝ × ℝ => Φ (-q.1, Ψ q)) ((0:ℝ), s)
          = mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) (fun q : ℝ × ℝ => γ q.2) ((0:ℝ), s) :=
        mfderiv_congr (x := ((0:ℝ), s)) hGfun
      exact (DFunLike.congr_fun hfeq v).trans hh2
    exact h2.symm.trans h1
  have hFdZ : Fd Z = 0 := by
    rw [← hYZ]
    exact hFdY
  have hv1 : v.1 = 0 := by
    have h1 : Fd Z = (-v.1) • Fd X0 := by
      rw [hZX, map_smul]
    rw [hFdX] at h1
    rw [hFdZ] at h1
    simpa using h1.symm
  have hv2 : v.2 = 0 := by
    have h0 : Y = 0 := by
      rw [hYZ, hZX, hv1, neg_zero, zero_smul]
    have hv2' : mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ s v.2 = 0 := h0
    exact ((hinjγ s).eq_iff (a := v.2) (b := 0)).mp (by rw [hv2', map_zero])
  exact Prod.ext hv1 hv2

lemma flowParam_injective {Φ : ℝ × M → M} {γ : ℝ → M}
    (hΦsm : ContMDiff (𝓘(ℝ,ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ)
    (hγsm : ContMDiff 𝓘(ℝ,ℝ) (𝓡 2) ∞ γ)
    (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦcomp : ∀ (s t : ℝ) (x : M), Φ (s, Φ (t, x)) = Φ (s + t, x))
    (hA : ∀ s : ℝ, ∀ v : ℝ × ℝ,
      mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) (fun q : ℝ × ℝ => Φ (q.1, γ q.2)) ((0:ℝ), s) v = 0 → v = 0) :
    ∀ p : ℝ × ℝ, Function.Injective
      (mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) (fun q : ℝ × ℝ => Φ (q.1, γ q.2)) p) := by
  intro p u w huw
  have h0 : mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) (fun q : ℝ × ℝ => Φ (q.1, γ q.2)) p (u - w) = 0 := by
    rw [map_sub, huw, sub_self]
  let Ψ : ℝ × ℝ → M := fun q => Φ (q.1, γ q.2)
  have h0' : mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) Ψ p (u - w) = 0 := h0
  have hΨsm : ContMDiff 𝓘(ℝ,ℝ×ℝ) (𝓡 2) ∞ Ψ := by
    show ContMDiff 𝓘(ℝ,ℝ×ℝ) (𝓡 2) ∞ (fun q : ℝ × ℝ => Φ (q.1, γ q.2))
    have h1 : ContMDiff 𝓘(ℝ,ℝ×ℝ) 𝓘(ℝ,ℝ) ∞ (fun q : ℝ×ℝ => q.1) :=
      ContinuousLinearMap.contMDiff (ContinuousLinearMap.fst ℝ ℝ ℝ)
    have h2 : ContMDiff 𝓘(ℝ,ℝ×ℝ) (𝓡 2) ∞ (fun q : ℝ×ℝ => γ q.2) :=
      hγsm.comp (ContinuousLinearMap.contMDiff (ContinuousLinearMap.snd ℝ ℝ ℝ))
    exact hΦsm.comp (h1.prodMk h2)
  -- transport
  let τ : ℝ × ℝ → ℝ × ℝ := fun q => (q.1 - p.1, q.2)
  have hfun : ((fun y : M => Φ (-p.1, y)) ∘ Ψ) = (Ψ ∘ τ) := by
    funext q
    show Φ (-p.1, Φ (q.1, γ q.2)) = Φ (q.1 - p.1, γ q.2)
    rw [hΦcomp]
    congr 1
    ring
  have hmd1 : MDifferentiableAt (𝓡 2) (𝓡 2) (fun y : M => Φ (-p.1, y)) (Ψ p) :=
    (hΦsm.comp (contMDiff_const.prodMk contMDiff_id)).contMDiffAt.mdifferentiableAt
      (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
  have hmd2 : MDifferentiableAt 𝓘(ℝ,ℝ×ℝ) (𝓡 2) Ψ p :=
    hΨsm.contMDiffAt.mdifferentiableAt (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
  have hmd2' : MDifferentiableAt 𝓘(ℝ,ℝ×ℝ) (𝓡 2) Ψ (τ p) :=
    hΨsm.contMDiffAt.mdifferentiableAt (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
  have hcomp1 : mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) ((fun y : M => Φ (-p.1, y)) ∘ Ψ) p
      = (mfderiv (𝓡 2) (𝓡 2) (fun y : M => Φ (-p.1, y)) (Ψ p)) ∘SL (mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) Ψ p) :=
    mfderiv_comp p hmd1 hmd2
  have hτfun : τ = (fun q : ℝ × ℝ => q + ((-(p.1), (0:ℝ)))) := by
    funext q
    show (q.1 - p.1, q.2) = q + (-(p.1), (0:ℝ))
    ext <;> simp [sub_eq_add_neg]
  have hτmd : MDifferentiableAt 𝓘(ℝ,ℝ×ℝ) 𝓘(ℝ,ℝ×ℝ) τ p := by
    rw [hτfun]
    exact (contMDiff_id.add contMDiff_const).contMDiffAt.mdifferentiableAt
      (show (∞ : WithTop ℕ∞) ≠ 0 by simp)
  have hτeq : mfderiv 𝓘(ℝ,ℝ×ℝ) 𝓘(ℝ,ℝ×ℝ) τ p = ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
    rw [hτfun, mfderiv_eq_fderiv]
    show fderiv ℝ (fun q : ℝ × ℝ => q + (-(p.1), (0:ℝ))) p = ContinuousLinearMap.id ℝ (ℝ × ℝ)
    rw [fderiv_add_const]
    exact fderiv_id
  have hτp : τ p = ((0:ℝ), p.2) := by
    show (p.1 - p.1, p.2) = ((0:ℝ), p.2)
    rw [sub_self]
  have hcomp2 : mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) (Ψ ∘ τ) p
      = (mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) Ψ (τ p)) ∘SL (mfderiv 𝓘(ℝ,ℝ×ℝ) 𝓘(ℝ,ℝ×ℝ) τ p) :=
    mfderiv_comp p hmd2' hτmd
  have hLcomp : (mfderiv (𝓡 2) (𝓡 2) (fun y : M => Φ (-p.1, y)) (Ψ p)) ∘SL (mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) Ψ p)
      = mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) Ψ ((0:ℝ), p.2) := by
    rw [← hcomp1]
    rw [show mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) ((fun y : M => Φ (-p.1, y)) ∘ Ψ) p
        = mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) (Ψ ∘ τ) p from mfderiv_congr (x := p) hfun]
    rw [hcomp2, hτeq, hτp]
    exact ContinuousLinearMap.ext (fun x => rfl)
  have h1 : mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) Ψ ((0:ℝ), p.2) (u - w) = 0 := by
    have h2 : (mfderiv (𝓡 2) (𝓡 2) (fun y : M => Φ (-p.1, y)) (Ψ p)) ((mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) Ψ p) (u - w))
        = (mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) Ψ ((0:ℝ), p.2)) (u - w) :=
      DFunLike.congr_fun hLcomp (u - w)
    rw [h0', map_zero] at h2
    exact h2.symm
  exact sub_eq_zero.mp (hA p.2 (u - w) h1)

open Classical
open scoped Manifold ContDiff Topology in
/-- **The local lift of the angle of a circle of the reference level.**

Let `γ : ℝ → M` be a `2π`-periodic immersive parametrisation of a circle of the reference level
`Λ = K ∩ f ⁻¹' {a}` (with `a` the reference level), lying in `K`, and let `Φ` be a level flow whose
level law holds on the band `[a, a+η]`.  Then around `γ s₀` there are an open neighbourhood `D` and
a smooth real function `u` which computes, modulo `2π`, the parameter of the crossing of the flow
line with the circle: `u w ≡ s (mod 2π)` whenever `|t| < η/2` and `w = Φ (t, γ s)`. -/
theorem exists_localLift {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f)
    {a η : ℝ} (hη : 0 < η)
    {K : Set M} (hKopen : IsOpen K) (hKWopen : IsOpen (f ⁻¹' Set.Ioo (a - η) (a + η) \ K))
    (hKsub : K ⊆ f ⁻¹' Set.Ioo (a - η) (a + η))
    (hreg : ∀ x : M, f x = a → ¬ Work.Drive.Morse.IsCritical f x)
    {Φ : ℝ × M → M} (hΦsm : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ)
    (hΦ0 : ∀ x : M, Φ (0, x) = x)
    (hΦcomp : ∀ (s t : ℝ) (x : M), Φ (s, Φ (t, x)) = Φ (s + t, x))
    (hlaw : ∀ (x : M) (t : ℝ), f x ∈ Set.Icc a (a + η) →
      f x + t ∈ Set.Icc a (a + η) → f (Φ (t, x)) = f x + t)
    {γ : ℝ → M} (hγsm : ContMDiff 𝓘(ℝ, ℝ) (𝓡 2) ∞ γ)
    (hγper : ∀ s, γ (s + 2 * Real.pi) = γ s)
    (hγinj : ∀ s s', γ s = γ s' → ∃ m : ℤ, s = s' + m * (2 * Real.pi))
    (hγlev : ∀ s, f (γ s) = a) (hγK : ∀ s, γ s ∈ K)
    (hγimm : ∀ s, mfderiv 𝓘(ℝ, ℝ) (𝓡 2) γ s ≠ 0)
    (s₀ : ℝ) :
    ∃ (u : M → ℝ) (D : Set M), IsOpen D ∧ γ s₀ ∈ D ∧
      ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ u D ∧
      (∀ w ∈ D, ∃ s t : ℝ, |t| < η / 2 ∧ w = Φ (t, γ s) ∧ u w = s) ∧
      (∀ w ∈ D, ∀ s t : ℝ, |t| < η / 2 → w = Φ (t, γ s) → ∃ m : ℤ, u w = s + m * (2 * Real.pi)) := by
  classical
  -- The flow direction raises `f` at unit speed at the reference level.
  have hX : ∀ s : ℝ, mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ s)
      (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (fun z : ℝ => Φ (z, γ s)) 0 1) = 1 :=
    fun s => flowDir_scalar hf hη hΦsm hΦ0 hlaw hγlev s
  -- The derivative of `f` along the level circle vanishes.
  have hγf : ∀ (s w : ℝ), mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (γ s)
      (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ s w) = 0 :=
    fun s w => mfderiv_f_along_gamma_eq_zero hf hγsm hγlev s w
  have hinjγ : ∀ s : ℝ, Function.Injective (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) γ s) :=
    fun s => ll_injective_of_ne_zero (N := EuclideanSpace ℝ (Fin 2)) (hγimm s)
  -- Injectivity of the derivative of the parametrisation `(t, s) ↦ Φ (t, γ s)`.
  have hA : ∀ s : ℝ, ∀ v : ℝ × ℝ,
      mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) (fun q : ℝ × ℝ => Φ (q.1, γ q.2)) ((0:ℝ), s) v = 0 → v = 0 :=
    flowParam_injective_at_zero hΦsm hγsm hΦ0 hΦcomp hX hγf hinjγ
  have hinj_all : ∀ p : ℝ × ℝ, Function.Injective
      (mfderiv 𝓘(ℝ,ℝ×ℝ) (𝓡 2) (fun q : ℝ × ℝ => Φ (q.1, γ q.2)) p) :=
    flowParam_injective hΦsm hγsm hΦ0 hΦcomp hA
  have hΨsm : ContMDiff 𝓘(ℝ,ℝ×ℝ) (𝓡 2) ∞ (fun q : ℝ × ℝ => Φ (q.1, γ q.2)) := by
    have h1 : ContMDiff 𝓘(ℝ,ℝ×ℝ) 𝓘(ℝ,ℝ) ∞ (fun q : ℝ×ℝ => q.1) :=
      ContinuousLinearMap.contMDiff (ContinuousLinearMap.fst ℝ ℝ ℝ)
    have h2 : ContMDiff 𝓘(ℝ,ℝ×ℝ) (𝓡 2) ∞ (fun q : ℝ×ℝ => γ q.2) :=
      hγsm.comp (ContinuousLinearMap.contMDiff (ContinuousLinearMap.snd ℝ ℝ ℝ))
    exact hΦsm.comp (h1.prodMk h2)
  have hdim : Module.finrank ℝ (ℝ × ℝ) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 2)) := by
    rw [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace]
    simp
  have hld : IsLocalDiffeomorph 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞
      (fun q : ℝ × ℝ => Φ (q.1, γ q.2)) :=
    Work.Noncompact.CompressionTube.isLocalDiffeomorph_of_mfderiv_injective hdim hΨsm hinj_all
  -- The local inverse around `p₀ = (0, s₀)`.
  set p₀ : ℝ × ℝ := ((0:ℝ), s₀) with hp₀
  have hldAt : IsLocalDiffeomorphAt 𝓘(ℝ, ℝ × ℝ) (𝓡 2) ∞
      (fun q : ℝ × ℝ => Φ (q.1, γ q.2)) p₀ := hld p₀
  let σ : M → ℝ × ℝ := fun w => hldAt.localInverse w
  have hσsm : ContMDiffOn (𝓡 2) (𝓘(ℝ,ℝ×ℝ)) ∞ σ hldAt.localInverse.source :=
    hldAt.contmdiffOn_localInverse
  let D : Set M := hldAt.localInverse.source ∩ σ ⁻¹' {q : ℝ × ℝ | |q.1| < η / 2}
  have hDopen : IsOpen D := by
    refine ContinuousOn.isOpen_inter_preimage hσsm.continuousOn hldAt.localInverse_open_source ?_
    exact isOpen_lt (continuous_abs.comp continuous_fst) continuous_const
  have hΨp₀ : (fun q : ℝ × ℝ => Φ (q.1, γ q.2)) p₀ = γ s₀ := by
    rw [hp₀]
    show Φ ((0:ℝ), γ s₀) = γ s₀
    exact hΦ0 (γ s₀)
  have hσ0 : σ (γ s₀) = p₀ := by
    have h := hldAt.localInverse_left_inv hldAt.localInverse_mem_target
    rw [← hΨp₀]
    exact h
  have hxD : γ s₀ ∈ D := by
    refine ⟨?_, ?_⟩
    · show γ s₀ ∈ hldAt.localInverse.source
      rw [← hΨp₀]
      exact hldAt.localInverse_mem_source
    · show |(σ (γ s₀)).1| < η / 2
      rw [hσ0]
      show |((0:ℝ), s₀).1| < η / 2
      rw [show ((0:ℝ), s₀).1 = (0:ℝ) from rfl, abs_zero]
      linarith
  refine ⟨fun w => (σ w).2, D, hDopen, hxD, ?_, ?_, ?_⟩
  · have hcomp : ContMDiffOn (𝓡 2) 𝓘(ℝ,ℝ) ∞ (fun w => (σ w).2) hldAt.localInverse.source :=
      (ContinuousLinearMap.contMDiff (ContinuousLinearMap.snd ℝ ℝ ℝ)).comp_contMDiffOn hσsm
    exact hcomp.mono (fun w hw => hw.1)
  · intro w hw
    obtain ⟨hw1, hw2⟩ := hw
    have hthis : Φ ((σ w).1, γ ((σ w).2)) = w := hldAt.localInverse_right_inv hw1
    exact ⟨(σ w).2, (σ w).1, hw2, hthis.symm, rfl⟩
  · intro w hw s t ht hweq
    obtain ⟨hw1, hw2⟩ := hw
    have hthis : Φ ((σ w).1, γ ((σ w).2)) = w := hldAt.localInverse_right_inv hw1
    have hkey : γ ((σ w).2) = Φ (t - (σ w).1, γ s) := by
      have h' : Φ (t, γ s) = Φ ((σ w).1, γ ((σ w).2)) := hweq.symm.trans hthis.symm
      have h2 := congrArg (fun z => Φ (-(σ w).1, z)) h'
      rw [hΦcomp, hΦcomp, neg_add_cancel, hΦ0] at h2
      rw [← h2]
      congr 1
      ring
    have hw2' : |(σ w).1| < η / 2 := by
      simpa using hw2
    have habs : |t - (σ w).1| < η := by
      have h3 : |t - (σ w).1| ≤ |t| + |(σ w).1| := by
        have := abs_sub_le t 0 (σ w).1
        simpa using this
      linarith
    have ht0 : t - (σ w).1 = 0 :=
      flow_time_eq_zero_of_eq hΦ0 hΦcomp hlaw hγlev habs hkey
    have ht' : t = (σ w).1 := by linarith
    have hγeq : γ s = γ ((σ w).2) := by
      have h' : Φ (t, γ s) = Φ (t, γ ((σ w).2)) := by
        calc Φ (t, γ s) = w := hweq.symm
          _ = Φ ((σ w).1, γ ((σ w).2)) := hthis.symm
          _ = Φ (t, γ ((σ w).2)) := by rw [← ht']
      have h2 := congrArg (fun z => Φ (-t, z)) h'
      rw [hΦcomp, hΦcomp] at h2
      simp only [neg_add_cancel, hΦ0] at h2
      exact h2
    obtain ⟨m, hm⟩ := hγinj ((σ w).2) s hγeq.symm
    exact ⟨m, hm⟩


end Work.Drive.N2
