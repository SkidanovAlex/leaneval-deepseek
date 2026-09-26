import Mathlib
import Submission.Work.Drive.Mono.Geom3Defs
import Submission.Work.Drive.Mono.BoxGenE
import Submission.Work.Drive.Mono.JunctionGenC
import Submission.Work.Drive.Mono.SlabCaps
import Submission.Work.Drive.Final.LTypes
import Submission.Work.Drive.Mono.Band.BandChartDefs
import Submission.Work.Drive.EpsForm.SweepGenericity
import Submission.Work.Drive.Mono.fibreMax_continuous
import Submission.Work.Drive.Mono.junctionGenC_of_arcs
import Submission.Work.Drive.Mono.fderiv_boxNorm_par_ne_zero
import Submission.Work.Drive.Mono.trace_locallyEuclidean_at_of_noEventAt
import Submission.Work.Drive.Mono.trace_localModel_of_not_event
import Submission.Work.Drive.Final.param_add_int_mul_two_pi
import Submission.Work.Drive.Final.fderiv_add_of_periodic

open Filter
open scoped Topology
open LeanEval.KnotTheory.PardonDistortion

namespace Work.Drive.Mono

theorem g3_gammaTransverse {ψ : Submission.Diffeo} {s u h : ℝ}
    {c v : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {N : ℕ}
    {γ : Fin N → ℝ → LeanEval.KnotTheory.PardonDistortion.R3} {η : ℝ}
    {nn : LeanEval.KnotTheory.PardonDistortion.R3}
    (hs : 0 < s)
    (hEF : Work.Drive.Mono.EdgeFree ψ s c σ u v h)
    (hbelt : ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ closure (Submission.PBox s c σ) → |Work.Drive.Final.slabFn c u v z| ≤ h →
      |z (σ 2) - c (σ 2)| < Submission.boxSide 2 * s)
    (hBG : Work.Drive.Mono.BoxGen ψ c σ s)
    (hη : 0 < η)
    (hγ : ∀ k : Fin N, ContDiffOn ℝ 3 (γ k) (Set.Icc (-η) η))
    (hγh : ∀ k : Fin N, ∀ t ∈ Set.Icc (-η) η, (γ k t) (σ 2) = c (σ 2) + u + t)
    (hbranch : ∀ k : Fin N, ∃ i : Fin 3, i ≠ 2 ∧ ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ∃ β : ℝ → ℝ × ℝ, ContDiffOn ℝ 3 β (Set.Icc (-η) η) ∧ ∀ t ∈ Set.Icc (-η) η,
        Work.BoxShrink.Pinch.par ψ (β t) = γ k t ∧
        (γ k t) (σ i) = c (σ i) + ε * Submission.boxSide i * s)
    (hcover : ∀ z : LeanEval.KnotTheory.PardonDistortion.R3,
      z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → Submission.boxNorm c σ z = s →
      |Work.Drive.Final.slabFn c u v z| ≤ h →
      (∀ j : Fin 3, j ≠ 2 → ∀ j' : Fin 3, j' ≠ 2 → j ≠ j' →
        ¬ (|z (σ j) - c (σ j)| = Submission.boxSide j * s ∧
           |z (σ j') - c (σ j')| = Submission.boxSide j' * s)) →
      ∃ k : Fin N, ∃ t ∈ Set.Ioo (-η) η, z = γ k t ∧ |t| ≤ 2 * h)
    (harcℓ : ∀ k : Fin N, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h →
      inner ℝ nn (deriv (γ k) t) ≠ 0)
    (hnn1 : ‖nn‖ = 1) (hℓ : ℓ = (innerSL ℝ) nn) :
    ∀ p : ℝ × ℝ, Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ p) = s →
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p)| ≤ h →
      fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0 ∧
      ∀ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p ≠
        t • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) p
      := by
  intro p hbn hslab
  -- ## The point `p` lies over the box sphere inside the slab
  have hz : Work.BoxShrink.Pinch.par ψ p ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier :=
    Work.BoxShrink.Pinch.par_mem_carrier ψ p
  have hcl : Work.BoxShrink.Pinch.par ψ p ∈ closure (Submission.PBox s c σ) :=
    Work.Drive.Mono.mem_closure_PBox_of_boxNorm_eq hs hbn
  -- ## The active box face at `p` is unique
  obtain ⟨i, ε, hε, hact, huniq⟩ :=
    Work.Drive.Mono.unique_activeFace_of_edgeFree hEF hz hbn hslab
  have hfacei : Work.Smooth.BoxGeneric.faceNorm c σ i (Work.BoxShrink.Pinch.par ψ p) = s := by
    rw [Work.Smooth.BoxGeneric.faceNorm_eq_abs_signedFace,
      Work.Smooth.BoxGeneric.signedFace_eq_of_faceLin_eq hε hact.1]
    rcases hε with h1 | h1
    · rw [h1, one_mul, abs_of_pos hs]
    · rw [h1, neg_one_mul, abs_neg, abs_of_pos hs]
  -- the active face is not the `σ 2` one (`hbelt`)
  have hi2 : i ≠ 2 := by
    intro hi
    have hb := hbelt _ hz hcl hslab
    rw [hi] at hfacei
    rw [Work.Smooth.BoxGeneric.faceNorm_apply, div_eq_iff (ne_of_gt (Submission.boxSide_pos 2))]
      at hfacei
    linarith
  -- the other faces are strictly below `s`
  have hstrict : ∀ k : Fin 3, k ≠ i →
      |Work.BoxShrink.Pinch.par ψ p (σ k) - c (σ k)| < Submission.boxSide k * s := by
    intro k hk
    have h1 := huniq k hk
    rw [Work.Smooth.BoxGeneric.faceNorm_apply, div_lt_iff₀ (Submission.boxSide_pos k)] at h1
    linarith
  -- no two coordinates of the box sphere are tight
  have hnoTwo : ∀ j : Fin 3, j ≠ 2 → ∀ j' : Fin 3, j' ≠ 2 → j ≠ j' →
      ¬ (|Work.BoxShrink.Pinch.par ψ p (σ j) - c (σ j)| = Submission.boxSide j * s ∧
         |Work.BoxShrink.Pinch.par ψ p (σ j') - c (σ j')| = Submission.boxSide j' * s) := by
    intro j _ j' _ hjj' hcon
    rcases eq_or_ne j i with hji | hji
    · subst hji
      have hlt := hstrict j' (Ne.symm hjj')
      rw [hcon.2] at hlt
      exact lt_irrefl _ hlt
    · have hlt := hstrict j hji
      rw [hcon.1] at hlt
      exact lt_irrefl _ hlt
  refine ⟨?_, ?_⟩
  · -- ## The derivative of the box norm does not vanish
    have hreg : fderiv ℝ (Work.Smooth.Morse.pullback ψ
        (Work.Smooth.BoxGeneric.faceLin c σ i ε)) p ≠ 0 := by
      have hRV := (Work.Smooth.Morse.isRegularValue_iff ψ
        (Work.Smooth.BoxGeneric.signedFace c σ i) (ε * s)).mp (hBG.1 i ε hε)
      intro h0
      have hL0 : fderiv ℝ (Work.Smooth.Morse.pullback ψ
          (Work.Smooth.BoxGeneric.signedFace c σ i)) p = 0 := by
        have hsplit := Work.Smooth.BoxGeneric.fderiv_pullback_faceLin ψ c σ i ε p
        rw [h0] at hsplit
        rcases hε with h1 | h1
        · rw [h1] at hsplit
          simpa using hsplit.symm
        · rw [h1] at hsplit
          simpa using hsplit.symm
      have hpull : Work.Smooth.Morse.pullback ψ
          (Work.Smooth.BoxGeneric.signedFace c σ i) p = ε * s :=
        Work.Smooth.BoxGeneric.signedFace_eq_of_faceLin_eq hε hact.1
      exact hRV p hpull hL0
    exact Work.Drive.Mono.fderiv_boxNorm_par_ne_zero (z := Work.BoxShrink.Pinch.par ψ p)
      hs hε rfl hact huniq hreg
  · -- ## The sweep height is transverse to the box sphere
    -- the arc through the point
    obtain ⟨k, t, htIoo, hzt, ht2h⟩ := hcover _ hz hbn hslab hnoTwo
    obtain ⟨ik, hik2, εk, hεk, β, hβdiff, hβprop⟩ := hbranch k
    have htIcc : t ∈ Set.Icc (-η) η := ⟨le_of_lt htIoo.1, le_of_lt htIoo.2⟩
    -- the arc's face is the active face
    have hik_eq : ik = i := by
      by_contra hne
      have hlt := huniq ik hne
      have heq : Work.Smooth.BoxGeneric.faceNorm c σ ik (Work.BoxShrink.Pinch.par ψ p) = s := by
        rw [Work.Smooth.BoxGeneric.faceNorm_apply, hzt, (hβprop t htIcc).2, add_sub_cancel_left]
        have hpos : 0 < Submission.boxSide ik * s :=
          mul_pos (Submission.boxSide_pos ik) hs
        rcases hεk with h1 | h1
        · rw [h1, one_mul, abs_of_pos hpos,
            div_eq_iff (ne_of_gt (Submission.boxSide_pos ik))]
          ring
        · rw [h1, neg_one_mul, neg_mul, abs_neg, abs_of_pos hpos,
            div_eq_iff (ne_of_gt (Submission.boxSide_pos ik))]
          ring
      linarith
    -- `β t` and `p` are the same parameter modulo the period lattice
    have hβtz : Work.BoxShrink.Pinch.par ψ (β t) = Work.BoxShrink.Pinch.par ψ p := by
      rw [(hβprop t htIcc).1, ← hzt]
    have hψeq : ψ (Work.Core.torusMap (β t).1 (β t).2) = ψ (Work.Core.torusMap p.1 p.2) := by
      simpa only [Work.BoxShrink.Pinch.par_def, Work.Smooth.Morse.param] using hβtz
    have htm : Work.Core.torusMap (β t).1 (β t).2 = Work.Core.torusMap p.1 p.2 :=
      Submission.Diffeo.injective ψ hψeq
    obtain ⟨⟨kZ, hkZ⟩, ⟨mZ, hmZ⟩⟩ :=
      (Work.Core.torusMap_eq_iff (β t).1 (β t).2 p.1 p.2).mp htm
    set cv : ℝ × ℝ := (((-kZ : ℤ) : ℝ) * (2 * Real.pi), ((-mZ : ℤ) : ℝ) * (2 * Real.pi))
      with hcv
    have hp_eq : p = β t + cv := by
      rw [hcv]
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_add, hkZ]; push_cast; ring
      · rw [Prod.snd_add, hmZ]; push_cast; ring
    have hperval : ∀ q : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ (q + cv) =
        Work.BoxShrink.Pinch.par ψ q := by
      intro q
      rw [hcv]
      rw [show q + (((-kZ : ℤ) : ℝ) * (2 * Real.pi), ((-mZ : ℤ) : ℝ) * (2 * Real.pi)) =
          (q.1 + ((-kZ : ℤ) : ℝ) * (2 * Real.pi),
            q.2 + ((-mZ : ℤ) : ℝ) * (2 * Real.pi)) from rfl]
      rw [Work.Drive.Final.param_add_int_mul_two_pi]
    have hperG : fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ
        (Work.BoxShrink.Pinch.par ψ q)) p =
        fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ
          (Work.BoxShrink.Pinch.par ψ q)) (β t) := by
      rw [hp_eq]
      exact Work.Drive.Final.fderiv_add_of_periodic
        (fun q : ℝ × ℝ => by rw [hperval q]) (β t)
    have hperH : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p =
        fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) (β t) := by
      rw [hp_eq]
      exact Work.Drive.Final.fderiv_add_of_periodic
        (fun q : ℝ × ℝ => by
          show ℓ (Work.BoxShrink.Pinch.par ψ (q + cv)) = ℓ (Work.BoxShrink.Pinch.par ψ q)
          rw [hperval q]) (β t)
    -- differentiability of `β` and of `γ k` at `t`
    have htmem : Set.Icc (-η) η ∈ 𝓝 t := Icc_mem_nhds htIoo.1 htIoo.2
    have hβ_d : DifferentiableAt ℝ β t :=
      ((hβdiff.contDiffAt htmem).differentiableAt (by norm_num))
    have hβ_hd : HasDerivAt β (deriv β t) t := hβ_d.hasDerivAt
    have hγk_d : DifferentiableAt ℝ (γ k) t :=
      (((hγ k).contDiffAt htmem).differentiableAt (by norm_num))
    have hγk_hd : HasDerivAt (γ k) (deriv (γ k) t) t := hγk_d.hasDerivAt
    -- differentiability of the two pulled-back functions at `β t`
    have hsweep_cd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (Work.Drive.EpsForm.sweepHeight ψ ℓ) :=
      Work.Smooth.Morse.pullback_contDiff ψ (ℓ.contDiff)
    have hH_d : DifferentiableAt ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) (β t) :=
      (hsweep_cd.differentiable (by simp)).differentiableAt
    have hFcd : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun q : ℝ × ℝ => Work.Smooth.BoxGeneric.faceLin c σ i ε
          (Work.BoxShrink.Pinch.par ψ q)) :=
      Work.Smooth.BoxGeneric.pullback_faceLin_contDiff ψ c σ i ε
    have hF_d : DifferentiableAt ℝ
        (fun q : ℝ × ℝ => Work.Smooth.BoxGeneric.faceLin c σ i ε
          (Work.BoxShrink.Pinch.par ψ q)) (β t) :=
      (hFcd.differentiable (by simp)).differentiableAt
    -- the derivative of the sweep height along `β`
    have hHval : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) (β t) (deriv β t) ≠ 0 := by
      intro h0
      have h1 : HasDerivAt (fun t' : ℝ => ℓ (γ k t')) (ℓ (deriv (γ k) t)) t :=
        (ContinuousLinearMap.hasFDerivAt ℓ).comp_hasDerivAt t hγk_hd
      have hlocs : (fun t' : ℝ => ℓ (γ k t')) =ᶠ[𝓝 t]
          (Work.Drive.EpsForm.sweepHeight ψ ℓ) ∘ β := by
        filter_upwards [htmem] with t' ht'
        simp only [Function.comp_apply]
        rw [show Work.Drive.EpsForm.sweepHeight ψ ℓ (β t') = ℓ (Work.BoxShrink.Pinch.par ψ (β t'))
          from rfl, (hβprop t' ht').1]
      have hcomp : HasDerivAt ((Work.Drive.EpsForm.sweepHeight ψ ℓ) ∘ β)
          (fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) (β t) (deriv β t)) t :=
        (hH_d.hasFDerivAt).comp_hasDerivAt t hβ_hd
      have hval : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) (β t) (deriv β t) =
          ℓ (deriv (γ k) t) := (hcomp.congr_of_eventuallyEq hlocs).unique h1
      rw [hval] at h0
      rw [hℓ] at h0
      exact harcℓ k t htIoo ht2h h0
    -- the derivative of the box norm along `β`
    have hGval : fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ
        (Work.BoxShrink.Pinch.par ψ q)) (β t) (deriv β t) = 0 := by
      have hnb : (fun x : R3 => Submission.boxNorm c σ x) =ᶠ[𝓝 (Work.BoxShrink.Pinch.par ψ p)]
          (fun x => Work.Smooth.BoxGeneric.faceLin c σ i ε x) :=
        Work.Smooth.BoxGeneric.LocalSurface.eventually_boxNorm_eq_faceLin hs hε hact huniq
      have htend : Filter.Tendsto (Work.BoxShrink.Pinch.par ψ) (𝓝 (β t))
          (𝓝 (Work.BoxShrink.Pinch.par ψ p)) := by
        rw [← hβtz]
        exact (Work.BoxShrink.Pinch.par_continuous ψ).continuousAt
      have hGeq : (fun q : ℝ × ℝ => Submission.boxNorm c σ (Work.BoxShrink.Pinch.par ψ q)) =ᶠ[𝓝 (β t)]
          (fun q : ℝ × ℝ => Work.Smooth.BoxGeneric.faceLin c σ i ε
            (Work.BoxShrink.Pinch.par ψ q)) :=
        hnb.comp_tendsto htend
      rw [Filter.EventuallyEq.fderiv_eq hGeq]
      -- `faceLin c σ i ε ∘ γ k` is constant, equal to `ε * εk * s`
      have hconst : (fun q : ℝ × ℝ => Work.Smooth.BoxGeneric.faceLin c σ i ε
          (Work.BoxShrink.Pinch.par ψ q)) ∘ β =ᶠ[𝓝 t] fun _ => ε * εk * s := by
        filter_upwards [htmem] with t' ht'
        simp only [Function.comp_apply]
        rw [(hβprop t' ht').1, Work.Smooth.BoxGeneric.faceLin_apply,
          Work.Smooth.BoxGeneric.signedFace_apply, ← hik_eq, (hβprop t' ht').2,
          add_sub_cancel_left]
        field_simp [ne_of_gt (Submission.boxSide_pos ik)]
      have hcompF : HasDerivAt ((fun q : ℝ × ℝ => Work.Smooth.BoxGeneric.faceLin c σ i ε
          (Work.BoxShrink.Pinch.par ψ q)) ∘ β)
          (fderiv ℝ (fun q : ℝ × ℝ => Work.Smooth.BoxGeneric.faceLin c σ i ε
            (Work.BoxShrink.Pinch.par ψ q)) (β t) (deriv β t)) t :=
        (hF_d.hasFDerivAt).comp_hasDerivAt t hβ_hd
      have hconst' : HasDerivAt ((fun q : ℝ × ℝ => Work.Smooth.BoxGeneric.faceLin c σ i ε
          (Work.BoxShrink.Pinch.par ψ q)) ∘ β) 0 t :=
        (hasDerivAt_const t (ε * εk * s)).congr_of_eventuallyEq hconst
      exact hcompF.unique hconst'
    -- conclusion
    intro t0 heq
    have heq' : fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) (β t) =
        t0 • fderiv ℝ (fun q : ℝ × ℝ => Submission.boxNorm c σ
          (Work.BoxShrink.Pinch.par ψ q)) (β t) := by
      rw [← hperH, ← hperG]
      exact heq
    have h2 := congrArg (fun L : ℝ × ℝ →L[ℝ] ℝ => L (deriv β t)) heq'
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul, hGval, mul_zero] at h2
    exact hHval h2


end Work.Drive.Mono
