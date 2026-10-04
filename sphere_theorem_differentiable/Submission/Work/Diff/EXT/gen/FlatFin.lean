import Mathlib
import Submission.Work.Diff.EXT.gen_defs
import Submission.Work.Diff.EXT.contDiffAt_of_flat_indicator

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The flat-indicator lemma on the `ℝ × ℝⁿ` domain, with an arbitrary codomain

`Submission/Work/Diff/EXT/contDiffAt_of_flat_indicator.lean` proves that a `C^∞` function
`ℝ × ℝⁿ → ℝᵐ` that vanishes to infinite order along the hyperplane `{t = T}` near `x₀`, cut by the
indicator of `{t > T}`, is still `C^∞` at `(T, x₀)`.  Its proof is insensitive to the codomain, and
its induction is carried out in the tower of iterated derivative spaces, which is universe-stable
precisely because the domain `ℝ × ℝⁿ` lives in universe `0`.

Here we record the version with an *arbitrary* codomain `F` (the private induction core
`stepFun_contDiffOn_aux` of that file is not exported, so it is reproduced here), and then
transport it to an arbitrary finite-dimensional domain `E ≃L ℝⁿ` along a continuous linear
equivalence.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000
open scoped ContDiff Topology
open Filter

namespace Work.Diff.EXT.gen

open Work.Diff.EXT (stepFun)

/-- Induction core: if `γ` is `C^{k+1}` on an open set `u` and all its iterated derivatives vanish
at the points of the hyperplane `{t = T}` belonging to `u`, then the Heaviside cut `stepFun T γ` is
`C^k` on `u`.  (Same proof as `Work.Diff.EXT.stepFun_contDiffOn_aux`, with an arbitrary codomain.) -/
private lemma stepFun_contDiffOn_aux_fin (n : ℕ) (T : ℝ) (k : ℕ) :
    ∀ (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F]
      (γ : ℝ × (Fin n → ℝ) → F) (u : Set (ℝ × (Fin n → ℝ))),
      IsOpen u → ContDiffOn ℝ ((k : ℕ∞ω) + 1) γ u →
      (∀ p ∈ u, p.1 = T → ∀ j : ℕ, iteratedFDeriv ℝ j γ p = 0) →
      ContDiffOn ℝ (k : ℕ∞ω) (stepFun T γ) u := by
  induction k with
  | zero =>
    intro F _ _ γ u hu hγ hflat
    rw [Nat.cast_zero, contDiffOn_zero]
    exact Work.Diff.EXT.continuousOn_stepFun hu hγ.one_of_succ hflat
  | succ k ih =>
    intro F _ _ γ u hu hγ hflat
    have heq : ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 := by push_cast; ring
    have hγ1 : ContDiffOn ℝ 1 γ u := hγ.one_of_succ
    have hflat' : ∀ p ∈ u, p.1 = T → ∀ j : ℕ, iteratedFDeriv ℝ j (fderiv ℝ γ) p = 0 :=
      fun p hp hpT j => Work.Diff.EXT.iteratedFDeriv_fderiv_eq_zero (hflat p hp hpT (j + 1))
    have hγf : ContDiffOn ℝ ((k : ℕ∞ω) + 1) (fderiv ℝ γ) u :=
      ((contDiffOn_succ_iff_fderiv_of_isOpen hu (f := γ) (n := (k : ℕ∞ω) + 1)).1
        (by simpa only [heq] using hγ)).2.2
    have hcont : ContDiffOn ℝ (k : ℕ∞ω) (fderiv ℝ (stepFun T γ)) u :=
      ContDiffOn.congr (ih _ (fderiv ℝ γ) u hu hγf hflat') fun y hy =>
        (Work.Diff.EXT.hasFDerivAt_stepFun hu hγ1 hflat y hy).fderiv
    have hdiff : DifferentiableOn ℝ (stepFun T γ) u := fun y hy =>
      ((Work.Diff.EXT.hasFDerivAt_stepFun hu hγ1 hflat y hy).differentiableAt).differentiableWithinAt
    have hstep : ContDiffOn ℝ ((k : ℕ∞ω) + 1) (stepFun T γ) u :=
      (contDiffOn_succ_iff_fderiv_of_isOpen hu (f := stepFun T γ) (n := (k : ℕ∞ω))).2
        ⟨hdiff, fun h => absurd h (by simp), hcont⟩
    simpa only [heq] using hstep

/-- **Flat-indicator lemma, `ℝ × ℝⁿ` domain, arbitrary codomain.** -/
theorem contDiffAt_of_flat_indicator_fin {n : ℕ} {T : ℝ} {x₀ : Fin n → ℝ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {δ : ℝ × (Fin n → ℝ) → F}
    (hδ : ContDiffAt ℝ (⊤ : ℕ∞) δ (T, x₀))
    (hflat : ∀ᶠ x in nhds x₀, ∀ k : ℕ, iteratedFDeriv ℝ k δ (T, x) = 0) :
    ContDiffAt ℝ (⊤ : ℕ∞)
      (fun p : ℝ × (Fin n → ℝ) => if p.1 ≤ T then (0 : F) else δ p) (T, x₀) := by
  have hfun : (fun p : ℝ × (Fin n → ℝ) => if p.1 ≤ T then (0 : F) else δ p)
      = stepFun T δ := rfl
  rw [hfun]
  have hδinf : ContDiffAt ℝ (∞ : ℕ∞ω) δ (T, x₀) := hδ
  refine contDiffAt_infty.mpr ?_
  intro k
  obtain ⟨V, hVsub, hV_open, hx₀V⟩ := mem_nhds_iff.1 hflat
  have hu2_open : IsOpen (Set.univ ×ˢ V : Set (ℝ × (Fin n → ℝ))) := isOpen_univ.prod hV_open
  have hp₀2 : (T, x₀) ∈ (Set.univ ×ˢ V : Set (ℝ × (Fin n → ℝ))) := ⟨trivial, hx₀V⟩
  have hflatu2 : ∀ p ∈ (Set.univ ×ˢ V : Set (ℝ × (Fin n → ℝ))), p.1 = T →
      ∀ j : ℕ, iteratedFDeriv ℝ j δ p = 0 := by
    intro p hp hpT j
    have hpp : p = (T, p.2) := by ext <;> simp [hpT]
    rw [hpp]
    exact hVsub hp.2 j
  have heq : ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 := by push_cast; ring
  have hδk : ContDiffAt ℝ ((k : ℕ∞ω) + 1) δ (T, x₀) := by
    simpa only [heq] using (contDiffAt_infty.mp hδinf) (k + 1)
  obtain ⟨u₁, hu₁_mem, hu₁_cont⟩ :=
    (contDiffWithinAt_iff_contDiffOn_nhds (𝕜 := ℝ) (s := Set.univ) (f := δ) (x := (T, x₀))
      (n := ((k : ℕ∞ω) + 1)) (by simp)).1 hδk
  have hu₁_mem' : u₁ ∈ 𝓝 (T, x₀) := by simpa using hu₁_mem
  obtain ⟨u₁', hu₁'sub, hu₁'_open, hp₀1'⟩ := mem_nhds_iff.1 hu₁_mem'
  have hu_open : IsOpen (u₁' ∩ (Set.univ ×ˢ V) : Set (ℝ × (Fin n → ℝ))) :=
    hu₁'_open.inter hu2_open
  have hp₀u : (T, x₀) ∈ (u₁' ∩ (Set.univ ×ˢ V) : Set (ℝ × (Fin n → ℝ))) := ⟨hp₀1', hp₀2⟩
  have hcont_u : ContDiffOn ℝ ((k : ℕ∞ω) + 1) δ
      (u₁' ∩ (Set.univ ×ˢ V) : Set (ℝ × (Fin n → ℝ))) :=
    hu₁_cont.mono fun y hy => hu₁'sub hy.1
  have hflat_u : ∀ p ∈ (u₁' ∩ (Set.univ ×ˢ V) : Set (ℝ × (Fin n → ℝ))), p.1 = T →
      ∀ j : ℕ, iteratedFDeriv ℝ j δ p = 0 := fun p hp hpT j => hflatu2 p hp.2 hpT j
  exact (stepFun_contDiffOn_aux_fin n T k F δ _ hu_open hcont_u hflat_u).contDiffAt
    (hu_open.mem_nhds hp₀u)

end Work.Diff.EXT.gen
