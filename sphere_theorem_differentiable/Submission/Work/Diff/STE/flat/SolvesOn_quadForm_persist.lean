import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.posDef_of_uniform_close
import Submission.Work.Diff.STE.flat.torus_uniqueness

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Set Filter
open scoped Topology

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat

/-!
# Persistence of the uniform ellipticity of a solution of the flat DeTurck system

If the initial datum `u 0` of a jointly smooth `1`-periodic solution `u` of the flat DeTurck
Cauchy problem `∂ₜu = Φ(·, jet u)` satisfies the uniform quadratic-form lower bound
`lam * ‖v‖² ≤ ∑ᵢⱼ (reMat (u 0 x))ᵢⱼ vᵢ vⱼ` with `lam > 0`, then the same bound with constant
`lam / 2` holds for all `(t, x)` with `t` in a short initial interval `[0, τ)`, `τ ≤ T`.

The proof is the classical openess argument, in two steps:

* `posDef_of_uniform_close` (`Submission/Work/Diff/STE/flat/posDef_of_uniform_close.lean`): the
  ellipticity condition is *open* in the uniform norm on the torus — a datum uniformly `ε`-close to
  `u 0` is elliptic with constant `lam / 2`.
* The *uniform* closeness `∀ x, ‖u t x - u 0 x‖ ≤ ε` for small `t` is obtained from the joint
  continuity of the difference on `Ico 0 T × univ`: the function
  `(t,x) ↦ u t x - u 0 x` is continuous there, hence uniformly continuous on the compact set
  `[0, T/2] × [0,1]ⁿ`, which gives a *single* `δ > 0` valid at every point `x` of the fundamental
  cube; periodicity of `u t` and of `u 0` then transports the bound from the cube to all of `ℝⁿ`.
-/

/-- A `MatC`-valued `1`-periodic function that is bounded by `M` on the closed unit cube is bounded
by `M` everywhere (reduce to the cube by `Periodic1.apply_periodicRep`). -/
lemma norm_le_of_periodic1_matC {n : ℕ} {f : (Fin n → ℝ) → MatC n} (hf : Periodic1 f) {M : ℝ}
    (h : ∀ x ∈ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1), ‖f x‖ ≤ M) :
    ∀ x, ‖f x‖ ≤ M := by
  intro x
  rw [← Periodic1.apply_periodicRep hf x]
  exact h _ (fun i _ => periodicRep_mem x i)

theorem SolvesOn_quadForm_persist {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (T : ℝ) (hT : 0 < T) (lam : ℝ) (hlam : 0 < lam)
    (u : ℝ → Work.Diff.STE.Flat.Torus n)
    (hu : Work.Diff.STE.Flat.SolvesOn Φ T u)
    (hell : ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
      lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
        Work.Diff.STE.Flat.reMat (u 0 x) i j * v i * v j) :
    ∃ τ : ℝ, 0 < τ ∧ τ ≤ T ∧ ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
      (lam / 2) * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
        Work.Diff.STE.Flat.reMat (u t x) i j * v i * v j := by
  -- ## Step 1: the ellipticity condition is open in the uniform norm
  obtain ⟨ε, hεpos, hε⟩ := posDef_of_uniform_close (u 0) lam hlam hell
  -- ## Step 2: preparation
  set S : Set (ℝ × (Fin n → ℝ)) := Set.Ico (0 : ℝ) T ×ˢ Set.univ with hSdef
  set cube : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1) with hcubedef
  set F : ℝ × (Fin n → ℝ) → MatC n := fun p => u p.1 p.2 - u 0 p.2 with hFdef
  have h0mem : (0 : ℝ) ∈ Set.Ico (0 : ℝ) T := ⟨le_rfl, hT⟩
  -- the initial datum is continuous (it is the time slice at `0` of a jointly smooth function)
  have hu0cont : Continuous (fun x : Fin n → ℝ => u 0 x) :=
    continuous_pi (fun i => continuous_pi (fun j =>
      (contDiff_slice_of_contDiffOn (F := fun τ y => u τ y i j)
        (contDiffOn_entry_of_contDiffOn hu.1 i j) h0mem).continuous))
  have hFcont : ContinuousOn F S :=
    hu.1.continuousOn.sub (hu0cont.comp continuous_snd).continuousOn
  -- ## Step 3: uniform continuity of the difference on the compact set `[0, T/2] × [0,1]ⁿ`
  have hKcompact : IsCompact (Set.Icc (0 : ℝ) (T / 2) ×ˢ cube) :=
    isCompact_Icc.prod (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc))
  have hKsub : Set.Icc (0 : ℝ) (T / 2) ×ˢ cube ⊆ S :=
    fun p hp => ⟨⟨hp.1.1, lt_of_le_of_lt hp.1.2 (by linarith [hT])⟩, Set.mem_univ _⟩
  have hunif : UniformContinuousOn F (Set.Icc (0 : ℝ) (T / 2) ×ˢ cube) :=
    hKcompact.uniformContinuousOn_of_continuous (hFcont.mono hKsub)
  obtain ⟨δ, hδpos, hδ⟩ := Metric.uniformContinuousOn_iff.mp hunif ε hεpos
  -- ## Step 4: the conclusion on `[0, min δ (T/2))`
  refine ⟨min δ (T / 2), lt_min hδpos (by linarith [hT]),
    le_trans (min_le_right _ _) (by linarith [hT]), ?_⟩
  intro t ht x v
  have htδ : t < δ := lt_of_lt_of_le ht.2 (min_le_left _ _)
  have htT2 : t < T / 2 := lt_of_lt_of_le ht.2 (min_le_right _ _)
  have htT : t ∈ Set.Ico (0 : ℝ) T := ⟨ht.1, by linarith [htT2, hT]⟩
  -- the closeness of `u t` to `u 0`, first on the fundamental cube
  have hcube : ∀ y ∈ cube, ‖u t y - u 0 y‖ ≤ ε := by
    intro y hy
    have h₁ : (t, y) ∈ Set.Icc (0 : ℝ) (T / 2) ×ˢ cube := ⟨⟨ht.1, htT2.le⟩, hy⟩
    have h₂ : ((0 : ℝ), y) ∈ Set.Icc (0 : ℝ) (T / 2) ×ˢ cube :=
      ⟨⟨le_rfl, by linarith [hT]⟩, hy⟩
    have hd : dist ((t, y) : ℝ × (Fin n → ℝ)) ((0 : ℝ), y) < δ := by
      have hdt : dist ((t, y) : ℝ × (Fin n → ℝ)) ((0 : ℝ), y) = t := by
        rw [Prod.dist_eq, dist_self, max_eq_left (dist_nonneg), Real.dist_eq, sub_zero,
          abs_of_nonneg ht.1]
      rw [hdt]; exact htδ
    have h := hδ (t, y) h₁ (0, y) h₂ hd
    have hzero : F ((0 : ℝ), y) = 0 := by rw [hFdef]; simp
    rw [hzero, dist_zero_right] at h
    exact le_of_lt h
  -- ... and then everywhere, by periodicity of the difference
  have hperdiff : Periodic1 (fun y : Fin n → ℝ => u t y - u 0 y) := by
    intro i y
    show u t (y + Pi.single i 1) - u 0 (y + Pi.single i 1) = u t y - u 0 y
    rw [hu.2.1 t htT i y, hu.2.1 0 h0mem i y]
  have hall : ∀ y : Fin n → ℝ, ‖u t y - u 0 y‖ ≤ ε :=
    norm_le_of_periodic1_matC hperdiff hcube
  -- ## Step 5: openness of the ellipticity condition concludes
  exact hε (u t) (fun y => hall y) x v

end Work.Diff.STE.flat
