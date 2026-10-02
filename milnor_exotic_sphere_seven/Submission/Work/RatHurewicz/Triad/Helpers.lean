import Mathlib
import Submission.Work.RatHurewicz.Triad.Basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Elementary consequences of the compression hypotheses

* `compressRelBd_congr` — the compression property of a pair transfers from the standard cube
  `I^d` to any space homeomorphic to it, with the boundary transported along the homeomorphism.
  This is what allows the preparation theorem to apply the compression hypothesis on the cells of
  the subdivision of the cube.
* `admissible_mem_pathComponent` — an admissible map takes all its values in the path component of
  the base point; this is the hypothesis under which the strengthened compression property
  `CompressRelBd` (whose allowed boundary values are the points of `B ∩ C` reachable from `x₀`) may
  be applied.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz.Triad

noncomputable section

open Work.Stems.Cubical

/-- **Reparametrised compression.**  If the pair `(Y, A)` has the compression property in
dimension `d` with allowed boundary values in `Bd`, then the same holds for maps defined on any
space `W` homeomorphic to `I^d`, with the boundary of `I^d` transported to `eB`. -/
theorem compressRelBd_congr {Y : Type} [TopologicalSpace Y] {A Bd : Set Y} {d : ℕ}
    {W : Type} [TopologicalSpace W] (h : CompressRelBd A Bd d) (e : ICube d ≃ₜ W)
    (eB : Set W) (he : e '' Cube.boundary (Fin d) = eB)
    (f : C(W, Y)) (hf : ∀ x, x ∈ eB → f x ∈ Bd) :
    ∃ G : C(W × I, Y),
      (∀ x, G (x, 0) = f x) ∧
      (∀ x (hx : x ∈ eB) t, G (x, t) = f x) ∧
      (∀ x, G (x, 1) ∈ A) := by
  have hbd : ∀ u : ICube d, u ∈ Cube.boundary (Fin d) →
      (f.comp ⟨⇑e, e.continuous⟩) u ∈ Bd := by
    intro u hu
    exact hf (e u) (by rw [← he]; exact ⟨u, hu, rfl⟩)
  obtain ⟨G, hG0, hGbd, hG1⟩ := h (f.comp ⟨⇑e, e.continuous⟩) hbd
  refine ⟨⟨fun p => G (e.symm p.1, p.2), ?_⟩, ?_, ?_, ?_⟩
  · exact G.continuous.comp ((e.symm.continuous.comp continuous_fst).prodMk continuous_snd)
  · intro x
    show G (e.symm x, 0) = f x
    rw [hG0]
    show f (e (e.symm x)) = f x
    rw [e.apply_symm_apply]
  · intro x hx t
    show G (e.symm x, t) = f x
    have h1 : e.symm x ∈ Cube.boundary (Fin d) := by
      have hx' : x ∈ e '' Cube.boundary (Fin d) := by rwa [he]
      obtain ⟨u, hu, hue⟩ := hx'
      rw [← hue, e.symm_apply_apply]
      exact hu
    rw [hGbd (e.symm x) h1 t]
    show f (e (e.symm x)) = f x
    rw [e.apply_symm_apply]
  · intro x
    exact hG1 (e.symm x)

instance instPathConnectedSpaceUnitInterval : PathConnectedSpace unitInterval :=
  isPathConnected_iff_pathConnectedSpace.mp
    ((convex_Icc (0 : ℝ) 1).isPathConnected ⟨0, by norm_num⟩)

/-- **An admissible map takes its values in the path component of the base point.**  The cube
`I^{n+1}` is path connected and contains a point with value `x₀`. -/
theorem admissible_mem_pathComponent {X : Type} [TopologicalSpace X] {B C : Set X}
    {x₀ : ↥(B ∩ C)} {n : ℕ} {Φ : C(ICube (n + 1), X)}
    (hΦ : TriadAdmissible B C x₀ Φ) :
    ∀ z : ICube (n + 1), Φ z ∈ pathComponent (x₀ : X) := by
  have hpc : IsPathConnected (Set.range Φ) :=
    isPathConnected_range (Φ.continuous)
  have hx₀ : (x₀ : X) ∈ Set.range Φ :=
    ⟨Fin.snoc (fun _ : Fin n => (0 : unitInterval)) 0, hΦ.1 _⟩
  intro z
  exact hpc.subset_pathComponent hx₀ ⟨z, rfl⟩

@[simp] theorem initC_snoc {n : ℕ} (u : ICube n) (t : I) : initC n (Fin.snoc u t) = u := by
  funext i
  simp [initC]

theorem snoc_initC {n : ℕ} (z : ICube (n + 1)) :
    Fin.snoc (initC n z) (z (Fin.last n)) = z := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc]; rfl
  · rw [Fin.snoc_last]

end

end Work.RatHurewicz.Triad
