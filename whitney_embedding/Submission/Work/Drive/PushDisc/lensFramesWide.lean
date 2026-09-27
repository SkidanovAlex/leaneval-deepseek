import Mathlib
import Submission.Work.Drive.PushDisc.milnorLens
import Submission.Work.Drive.PushDisc.lensFrames
import Submission.Work.Drive.PushDisc.epsWideLinInd
import Submission.Work.Drive.PushDisc.linIndDropLastBlock
import Submission.Work.Drive.Whitney.exists_complement_fromEdge

namespace Work.Drive.PushDisc

open scoped ContDiff

noncomputable section

variable {k : ℕ}

/-- A continuous family of `2k+2` vectors in a finite dimensional real normed space which is
independent on `[-1,1]` is independent on a slightly larger interval `[-1-ε, 1+ε]`. -/
theorem exists_eps_linIndWide {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {k : ℕ} (γ : ℝ → Fin (2 + k + k) → E) (hγ : Continuous γ)
    (h : ∀ x ∈ Set.Icc (-1 : ℝ) 1, LinearIndependent ℝ (γ x)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, |x| ≤ 1 + ε → LinearIndependent ℝ (γ x) := by
  have hopen : IsOpen {x : ℝ | LinearIndependent ℝ (γ x)} :=
    isOpen_setOfPred_linearIndependent.preimage hγ
  obtain ⟨δ, hδpos, hδsub⟩ :=
    (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_thickening_subset_open hopen h
  exact ⟨δ / 2, half_pos hδpos,
    fun x hx => hδsub (mem_thickening_Icc_of_abs_le δ hδpos hx)⟩

/-- Smoothness of an appended family of tuples. -/
theorem contDiff_finAppend {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : WithTop ℕ∞}
    {p q : ℕ} {A : E → Fin p → F} {B : E → Fin q → F}
    (hA : ContDiff 𝕜 n A) (hB : ContDiff 𝕜 n B) :
    ContDiff 𝕜 n (fun x => Fin.append (A x) (B x)) := by
  rw [contDiff_pi]
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have h1 : (fun x => Fin.append (A x) (B x) (Fin.castAdd q j)) = fun x => A x j := by
      funext x; rw [Fin.append_left]
    rw [h1]
    exact (contDiff_pi.mp hA) j
  · have h1 : (fun x => Fin.append (A x) (B x) (Fin.natAdd p j)) = fun x => B x j := by
      funext x; rw [Fin.append_right]
    rw [h1]
    exact (contDiff_pi.mp hB) j

/-- Continuity of an appended family of tuples. -/
theorem continuous_finAppend {E : Type*} [TopologicalSpace E]
    {F : Type*} [TopologicalSpace F] {p q : ℕ} {A : E → Fin p → F} {B : E → Fin q → F}
    (hA : Continuous A) (hB : Continuous B) :
    Continuous (fun x => Fin.append (A x) (B x)) := by
  rw [continuous_pi_iff]
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have h1 : (fun x => Fin.append (A x) (B x) (Fin.castAdd q j)) = fun x => A x j := by
      funext x; rw [Fin.append_left]
    rw [h1]
    exact (continuous_apply j).comp hA
  · have h1 : (fun x => Fin.append (A x) (B x) (Fin.natAdd p j)) = fun x => B x j := by
      funext x; rw [Fin.append_right]
    rw [h1]
    exact (continuous_apply j).comp hB

/-- Smoothness of the plane frame of a smooth pair of fields. -/
theorem contDiff_planeFrame {k : ℕ} {dx dy : ℝ × ℝ → Work.Drive.Whitney.Mdl k}
    (hdx : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dx)
    (hdy : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dy) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × ℝ => planeFrame k dx dy p) := by
  rw [contDiff_pi, Fin.forall_fin_two]
  exact ⟨by rw [show (fun p : ℝ × ℝ => planeFrame k dx dy p 0) = dx from rfl]; exact hdx,
    by rw [show (fun p : ℝ × ℝ => planeFrame k dx dy p 1) = dy from rfl]; exact hdy⟩

/-- **The two frames of the framing chart, on the wide lens.**

This is `Work.Drive.PushDisc.lensFrames` with the top-edge trace condition `W (x, arch x) = V x`
widened from `[-1,1]` to `[-X', X']` for some `X' > 1`.  The extra room is what the globalisation
of the framing chart needs: the plane tube `{|x| ≤ X'}` and the finger tube have to be swallowed by
a single neighbourhood of the lens, and the top edge of the lens is only `[-1,1]`.

The proof takes the narrow frames from `Work.Drive.PushDisc.lensFrames` (which spends the sign
hypothesis `hsign` on the `ℤ/2` framing obstruction of `Work.Drive.Whitney.exists_topCompletion` and
runs the fill `Work.Drive.Whitney.exists_injective_fill` over the lens).  The finger frame is then
re-transported down once more with `Work.Drive.Whitney.exists_complement_fromEdge`, this time with
the widened parameter `X' = 1 + ε`: the only hypothesis that changes is the independence of the
frame `[∂ₓ, ∂_y, U, V]` along the top edge, which holds on `[-1,1]` by the frame row of the narrow
solution and is spread to `[-1-ε, 1+ε]` by openness of linear independence
(`Work.Drive.PushDisc.exists_eps_linIndWide`). -/
theorem lensFramesWide {k : ℕ} (hk : 2 ≤ k)
    (dx dy : ℝ × ℝ → Work.Drive.Whitney.Mdl k)
    (hdx : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dx)
    (hdy : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) dy)
    (himm : ∀ p ∈ Work.Drive.PushDisc.lensK,
      LinearIndependent ℝ (Work.Drive.PushDisc.planeFrame k dx dy p))
    (V : ℝ → Fin k → Work.Drive.Whitney.Mdl k)
    (hV : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    (htop : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → LinearIndependent ℝ
      (Fin.append (Work.Drive.PushDisc.planeFrame k dx dy (x, Work.Drive.PushDisc.arch x)) (V x)))
    (hbot : ∀ x : ℝ, x ∈ Set.Icc (-1 : ℝ) 1 → LinearIndependent ℝ
      (Fin.append (Work.Drive.PushDisc.planeFrame k dx dy (x, 0)) (Work.Drive.PushDisc.iotaU k)))
    (hsign : ∃ T : Work.Drive.Whitney.Mdl k ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (2 + k + k)),
      0 < Work.Drive.PushDisc.frameDet (2 + k + k) T
            (Work.Drive.PushDisc.cornerFrame dx dy V (-1))
        * Work.Drive.PushDisc.frameDet (2 + k + k) T
            (Work.Drive.PushDisc.cornerFrame dx dy V 1)) :
    ∃ (X' : ℝ) (_ : 1 < X') (U W : ℝ × ℝ → Fin k → Work.Drive.Whitney.Mdl k),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) U ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W ∧
      (∀ x : ℝ, U (x, 0) = Work.Drive.PushDisc.iotaU k) ∧
      (∀ x : ℝ, |x| ≤ X' → W (x, Work.Drive.PushDisc.arch x) = V x) ∧
      (∀ p ∈ Work.Drive.PushDisc.lensK, LinearIndependent ℝ
        (Fin.append (Fin.append (Work.Drive.PushDisc.planeFrame k dx dy p) (U p)) (W p))) := by
  classical
  -- ## 1. the narrow frames
  obtain ⟨U, W0, hU_sm, hW0_sm, hU_bot, hW0_edge, hW0_ind⟩ :=
    lensFrames hk dx dy hdx hdy himm V hV htop hbot hsign
  -- ## 2. the linear identification with the Euclidean model space of the same dimension
  obtain ⟨T, hT⟩ := hsign
  let TE : Work.Drive.Whitney.Mdl k →ₗ[ℝ] lfE k :=
    (T : Work.Drive.Whitney.Mdl k ≃ₗ[ℝ] lfE k).toLinearMap
  have hTinj : Function.Injective TE := fun x y h => T.injective h
  have hTker : TE.ker = ⊥ := LinearMap.ker_eq_bot.mpr hTinj
  have hTE_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Work.Drive.Whitney.Mdl k => TE x) :=
    (LinearMap.toContinuousLinearMap TE).contDiff
  have hTEs_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : lfE k => T.symm y) :=
    (LinearMap.toContinuousLinearMap
      (T.symm : lfE k →ₗ[ℝ] Work.Drive.Whitney.Mdl k)).contDiff
  let pfE : ℝ × ℝ → Fin 2 → lfE k := fun p => TE ∘ planeFrame k dx dy p
  let UE : ℝ × ℝ → Fin k → lfE k := fun p => TE ∘ U p
  let VE : ℝ → Fin k → lfE k := fun x => TE ∘ V x
  have hpfE_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) pfE := by
    refine contDiff_pi.mpr (fun j => ?_)
    exact hTE_sm.comp ((contDiff_pi.mp (contDiff_planeFrame hdx hdy)) j)
  have hUE_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) UE := by
    refine contDiff_pi.mpr (fun j => ?_)
    exact hTE_sm.comp ((contDiff_pi.mp hU_sm) j)
  have hVE_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) VE := by
    refine contDiff_pi.mpr (fun j => ?_)
    exact hTE_sm.comp ((contDiff_pi.mp hV) j)
  let S2E : ℝ × ℝ → Fin (2 + k) → lfE k := fun p => Fin.append (pfE p) (UE p)
  have hS2E_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) S2E :=
    contDiff_finAppend hpfE_sm hUE_sm
  have hS2E_ind : ∀ p ∈ lensK, LinearIndependent ℝ (S2E p) := by
    intro p hp
    have h1 : LinearIndependent ℝ (Fin.append (planeFrame k dx dy p) (U p)) :=
      linIndDropLastBlock _ _ _ (hW0_ind p hp)
    have h2 := LinearIndependent.map' h1 TE hTker
    rw [← lf_append_comp TE (planeFrame k dx dy p) (U p)] at h2
    simpa only [S2E, pfE, UE] using h2
  -- ## 3. the frame row along the top edge, widened
  have harch_sm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) arch := by
    rw [show arch = fun x : ℝ => 1 - x ^ 2 from rfl]; fun_prop
  have hpair : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => (x, arch x)) :=
    contDiff_id.prodMk harch_sm
  have hedge1 : ∀ x : ℝ, |x| ≤ 1 → LinearIndependent ℝ
      (Fin.append (Fin.append (pfE (x, arch x)) (UE (x, arch x))) (VE x)) := by
    intro x hx
    have hxI : x ∈ Set.Icc (-1 : ℝ) 1 := Set.mem_Icc.mpr (abs_le.mp hx)
    have hxK : (x, arch x) ∈ lensK := by
      refine ⟨hx, ?_, le_rfl⟩
      have hle : x ^ 2 ≤ 1 := by
        have h' := abs_le.mp hx
        nlinarith [h'.1, h'.2]
      simp only [arch]; linarith
    have h1 := hW0_ind (x, arch x) hxK
    rw [hW0_edge x hxI] at h1
    have h2 := LinearIndependent.map' h1 TE hTker
    rw [← lf_append_comp TE (Fin.append (planeFrame k dx dy (x, arch x)) (U (x, arch x))) (V x),
      ← lf_append_comp TE (planeFrame k dx dy (x, arch x)) (U (x, arch x))] at h2
    simpa only [pfE, UE, VE] using h2
  have hcont : Continuous (fun x : ℝ =>
      Fin.append (Fin.append (pfE (x, arch x)) (UE (x, arch x))) (VE x)) := by
    refine continuous_finAppend ?_ hVE_sm.continuous
    refine continuous_finAppend ?_ ?_
    · rw [continuous_pi_iff]
      intro j
      show Continuous (fun x : ℝ => TE (planeFrame k dx dy (x, arch x) j))
      exact hTE_sm.continuous.comp ((continuous_apply j).comp
        (((contDiff_planeFrame hdx hdy).comp hpair).continuous))
    · have h : UE ∘ (fun x : ℝ => (x, arch x)) = fun x : ℝ => UE (x, arch x) := rfl
      rw [← h]
      exact hUE_sm.continuous.comp hpair.continuous
  obtain ⟨ε, hε, hedgeW⟩ := exists_eps_linIndWide
    (fun x : ℝ => Fin.append (Fin.append (pfE (x, arch x)) (UE (x, arch x))) (VE x)) hcont
    (fun x hx => hedge1 x (abs_le.mpr hx))
  -- ## 4. transporting the finger frame down with the widened parameter
  have hK : lensK = {p : ℝ × ℝ | |p.1| ≤ 1 + ε ∧ p.2 ∈ Set.Icc 0 (arch p.1)} := by
    ext p
    simp only [lensK, Set.mem_ofPred_eq, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by linarith [h1, hε.le], h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      have hge : 0 ≤ arch p.1 := le_trans h2 h3
      simp only [arch] at hge
      have hx2 : p.1 ^ 2 ≤ 1 := by linarith
      exact ⟨by rw [abs_le]; constructor <;> nlinarith [hx2], h2, h3⟩
  obtain ⟨WE, hWE_sm, hWE_edge, hWE_ind⟩ :=
    Work.Drive.Whitney.exists_complement_fromEdge (r := 2 + k) (k := k) arch harch_sm
      (X' := 1 + ε) S2E hS2E_sm lensK hK hS2E_ind VE hVE_sm hedgeW
  -- ## 5. the conclusion
  refine ⟨1 + ε, by linarith, U, fun p i => T.symm (WE p i), hU_sm, ?_, hU_bot, ?_, ?_⟩
  · refine contDiff_pi.mpr (fun i => ?_)
    exact hTEs_sm.comp ((contDiff_pi.mp hWE_sm) i)
  · intro x hx
    funext i
    have h1 : WE (x, arch x) i = TE (V x i) := by
      rw [congrFun (hWE_edge x hx) i]
      rfl
    show T.symm (WE (x, arch x) i) = V x i
    rw [h1]
    exact T.symm_apply_apply (V x i)
  · intro p hp
    have h1 := hWE_ind p hp
    have hcomp : Fin.append (Fin.append (pfE p) (UE p)) (WE p)
        = TE ∘ Fin.append (Fin.append (planeFrame k dx dy p) (U p))
            (fun i => T.symm (WE p i)) := by
      rw [← lf_append_comp TE (Fin.append (planeFrame k dx dy p) (U p))
          (fun i => T.symm (WE p i))]
      congr 1
      · rw [← lf_append_comp TE (planeFrame k dx dy p) (U p)]
      · funext i
        exact (T.apply_symm_apply (WE p i)).symm
    rw [hcomp] at h1
    exact LinearIndependent.of_comp TE h1

end

end Work.Drive.PushDisc
