import Mathlib
import Submission.Work.RPB.B5.Defs
import Submission.Work.RPB.B5.LagData
import Submission.Work.RPB.B5.lagData_per
import Submission.Work.RPB.B5.chartJets_levelPt_contDiff

/-!
# `collarPt` is `C⁸` on the whole slab

The collar point `collarPt Γc Ac τ σ t = levelPt (Γc τ σ t) σ (Ac τ σ t)` is smooth wherever
the reduced coordinate `Γc` and the phase `Ac` are.  The collar data is only *given* on the
half-space `t ≥ 0` (that is all the sibling construction `collar_exists` provides), but both
`Γc` and `Ac - t` are `2π`-periodic in `t`; periodicity upgrades the half-space smoothness to
smoothness at every point, hence

`(τ,σ,t) ↦ collarPt Γc Ac τ σ t` is `C⁸` on `[0,1] × ℝ × ℝ`.

The auxiliary lemma `contDiffWithinAt_third_periodic` is the (general) periodicity upgrade; it
is applied to `Γc` and to the periodic part `Ac - t` of the phase.
-/

set_option autoImplicit false

open Set

namespace Work.RPB.B5

open scoped ContDiff Topology

/-- **Periodicity in the third variable removes the half-space restriction.**

If `f : ℝ → ℝ → ℝ → X` is `C^n` on the slab `[0,1] × ℝ × [0,∞)` and `2π`-periodic in its last
argument, then `(τ,σ,t) ↦ f τ σ t` is `C^n` at every point whose first coordinate lies in
`[0,1]`, within the full slab `[0,1] × ℝ × ℝ`.

The proof shifts the third coordinate by a positive multiple `a = 2πk` of the period, chosen so
that the shifted point has `t + a > 0`; periodicity makes `f` agree with the shifted function,
the shift is smooth, and the shifted function is evaluated inside the half-space where `hsm`
applies. -/
theorem contDiffWithinAt_third_periodic {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (n : ℕ) (f : ℝ → ℝ → ℝ → X)
    (hsm : ContDiffOn ℝ n (fun z : ℝ × (ℝ × ℝ) => f z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ)))
    (hper : ∀ τ σ t, f τ σ (t + 2 * Real.pi) = f τ σ t)
    {τ₀ σ₀ t₀ : ℝ} (hτ : τ₀ ∈ Set.Icc (0 : ℝ) 1) :
    ContDiffWithinAt ℝ n (fun u : ℝ × (ℝ × ℝ) => f u.1 u.2.1 u.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) (τ₀, σ₀, t₀) := by
  obtain ⟨k, hk⟩ := exists_nat_gt (-t₀ / (2 * Real.pi))
  set a : ℝ := (k : ℝ) * (2 * Real.pi) with ha
  have hpi : 0 < 2 * Real.pi := by positivity
  have hapos : 0 < t₀ + a := by
    have h2 : -t₀ / (2 * Real.pi) * (2 * Real.pi) < (k : ℝ) * (2 * Real.pi) :=
      mul_lt_mul_of_pos_right hk hpi
    rw [div_mul_cancel₀ _ (ne_of_gt hpi)] at h2
    rw [ha]; linarith
  -- `f` is invariant under a shift of the third variable by `a`
  have hfper : ∀ τ σ t, f τ σ (t + a) = f τ σ t := by
    intro τ σ t
    have hp : Function.Periodic (fun s : ℝ => f τ σ s) (2 * Real.pi) := fun s => hper τ σ s
    have h3 := hp.nat_mul k
    rw [← ha] at h3
    exact h3 t
  have hshift : ContDiff ℝ n (fun u : ℝ × (ℝ × ℝ) => (u.1, (u.2.1, u.2.2 + a))) := by
    fun_prop
  -- the point lies in the (relatively) open window `t > -a`
  have hU : (Set.univ ×ˢ (Set.univ ×ˢ Set.Ioi (-a)) : Set (ℝ × (ℝ × ℝ)))
      ∈ 𝓝 (τ₀, σ₀, t₀) :=
    IsOpen.mem_nhds (isOpen_univ.prod (isOpen_univ.prod isOpen_Ioi))
      ⟨trivial, trivial, by rw [Set.mem_Ioi]; linarith⟩
  rw [← contDiffWithinAt_inter hU]
  -- it suffices to prove the claim on `S ∩ {t > -a}`, where the shift lands in the half-space
  have hmap : Set.MapsTo (fun u : ℝ × (ℝ × ℝ) => (u.1, (u.2.1, u.2.2 + a)))
      ((Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ : Set (ℝ × (ℝ × ℝ)))
        ∩ (Set.univ ×ˢ (Set.univ ×ˢ Set.Ioi (-a)) : Set (ℝ × (ℝ × ℝ))))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ)) := by
    rintro ⟨y1, y2, y3⟩ ⟨⟨h1, _, _⟩, ⟨_, _, h3⟩⟩
    rw [Set.mem_Ioi] at h3
    exact ⟨h1, trivial, by rw [Set.mem_Ici]; linarith⟩
  have hFT : ContDiffWithinAt ℝ n (fun z : ℝ × (ℝ × ℝ) => f z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ)) (τ₀, σ₀, t₀ + a) :=
    hsm.contDiffWithinAt ⟨hτ, trivial, by rw [Set.mem_Ici]; linarith⟩
  have hsh : ContDiffWithinAt ℝ n (fun u : ℝ × (ℝ × ℝ) => (u.1, (u.2.1, u.2.2 + a)))
      ((Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ : Set (ℝ × (ℝ × ℝ)))
        ∩ (Set.univ ×ˢ (Set.univ ×ˢ Set.Ioi (-a)) : Set (ℝ × (ℝ × ℝ)))) (τ₀, σ₀, t₀) :=
    hshift.contDiffAt.contDiffWithinAt
  have hcomp := hFT.comp (τ₀, σ₀, t₀) hsh hmap
  refine hcomp.congr ?_ ?_
  · rintro ⟨y1, y2, y3⟩ _
    show f y1 y2 y3 = f y1 y2 (y3 + a)
    exact (hfper y1 y2 y3).symm
  · show f τ₀ σ₀ t₀ = f τ₀ σ₀ (t₀ + a)
    exact (hfper τ₀ σ₀ t₀).symm

theorem collarPt_contDiffWithinAt (Γc : ℝ → ℝ → ℝ → ℂ) (Ac : ℝ → ℝ → ℝ → ℝ)
    (hΓsm : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => Γc z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ)))
    (hAsm : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => Ac z.1 z.2.1 z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ)))
    (hΓper : ∀ τ σ t, Γc τ σ (t + 2 * Real.pi) = Γc τ σ t)
    (hAper : ∀ τ σ t, Ac τ σ (t + 2 * Real.pi) = Ac τ σ t + 2 * Real.pi)
    {τ₀ σ₀ t₀ : ℝ} (hτ : τ₀ ∈ Set.Icc (0 : ℝ) 1) :
    ContDiffWithinAt ℝ 8
      (fun u : ℝ × (ℝ × ℝ) => Work.RPB.B5.collarPt Γc Ac u.1 u.2.1 u.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) (τ₀, (σ₀, t₀)) := by
  -- the reduced coordinate `Γc`
  have hΓ : ContDiffWithinAt ℝ 8 (fun u : ℝ × (ℝ × ℝ) => Γc u.1 u.2.1 u.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) (τ₀, (σ₀, t₀)) :=
    contDiffWithinAt_third_periodic 8 Γc hΓsm hΓper hτ
  -- the periodic part `Ac - t` of the phase
  have hAper' : ∀ τ σ t,
      Ac τ σ (t + 2 * Real.pi) - (t + 2 * Real.pi) = Ac τ σ t - t := by
    intro τ σ t
    rw [hAper]
    ring
  have hAsm' : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => Ac z.1 z.2.1 z.2.2 - z.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.Ici (0 : ℝ)) :=
    hAsm.sub (by fun_prop)
  have hA' : ContDiffWithinAt ℝ 8 (fun u : ℝ × (ℝ × ℝ) => Ac u.1 u.2.1 u.2.2 - u.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) (τ₀, (σ₀, t₀)) :=
    contDiffWithinAt_third_periodic 8 (fun τ σ t => Ac τ σ t - t) hAsm' hAper' hτ
  -- add back the linear part `t`
  have hAc : ContDiffWithinAt ℝ 8 (fun u : ℝ × (ℝ × ℝ) => Ac u.1 u.2.1 u.2.2)
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) (τ₀, (σ₀, t₀)) := by
    have hlin : ContDiffWithinAt ℝ 8 (fun u : ℝ × (ℝ × ℝ) => u.2.2)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) (τ₀, (σ₀, t₀)) := by fun_prop
    simpa using hA'.add hlin
  -- assemble the argument of `levelPt`
  have hΦ : ContDiffWithinAt ℝ 8
      (fun u : ℝ × (ℝ × ℝ) => (Γc u.1 u.2.1 u.2.2, (u.2.1, Ac u.1 u.2.1 u.2.2)))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) (τ₀, (σ₀, t₀)) := by
    have hσ : ContDiffWithinAt ℝ 8 (fun u : ℝ × (ℝ × ℝ) => u.2.1)
        (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ ×ˢ Set.univ) (τ₀, (σ₀, t₀)) := by fun_prop
    exact hΓ.prodMk (hσ.prodMk hAc)
  have hlev : ContDiffWithinAt ℝ 8 (fun p : ℂ × (ℝ × ℝ) => Work.RPV.levelPt p.1 p.2.1 p.2.2)
      Set.univ (Γc τ₀ σ₀ t₀, (σ₀, Ac τ₀ σ₀ t₀)) :=
    chartJets_levelPt_contDiff.contDiffAt.contDiffWithinAt
  have hcomp := hlev.comp (τ₀, (σ₀, t₀)) hΦ (Set.mapsTo_univ _ _)
  have heq : (fun u : ℝ × (ℝ × ℝ) => Work.RPB.B5.collarPt Γc Ac u.1 u.2.1 u.2.2)
      = ((fun p : ℂ × (ℝ × ℝ) => Work.RPV.levelPt p.1 p.2.1 p.2.2) ∘
          (fun u : ℝ × (ℝ × ℝ) => (Γc u.1 u.2.1 u.2.2, (u.2.1, Ac u.1 u.2.1 u.2.2)))) := by
    funext u
    simp only [Function.comp_apply, Work.RPB.B5.collarPt]
  rw [heq]
  exact hcomp

end Work.RPB.B5
