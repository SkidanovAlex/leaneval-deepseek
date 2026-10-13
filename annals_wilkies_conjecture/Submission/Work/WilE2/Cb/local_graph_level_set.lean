import Mathlib
import Submission.Work.WilE9G.Sard.Basic
import Submission.Work.WilE2.Ebc.local_graph_of_submersion_real

set_option autoImplicit false

noncomputable section

open Classical Filter Topology
open scoped Topology

namespace Work.WilE2.Cb

/-! ## A nonzero functional `ℝ →L[ℝ] ℝ` is invertible -/

/-- A continuous linear functional on `ℝ` that does not vanish at `1` is invertible. -/
theorem isInvertible_of_apply_one_ne_zero (φ : ℝ →L[ℝ] ℝ) (h : φ 1 ≠ 0) : φ.IsInvertible := by
  have hφ : φ = (φ 1) • ContinuousLinearMap.id ℝ ℝ := by
    apply ContinuousLinearMap.ext
    intro x
    rw [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    calc φ x = φ (x • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
      _ = x • φ 1 := by rw [map_smul]
      _ = (φ 1) * x := by rw [smul_eq_mul]; ring
  rw [hφ]
  refine ContinuousLinearMap.IsInvertible.of_inverse
    (g := (φ 1)⁻¹ • ContinuousLinearMap.id ℝ ℝ) ?_ ?_
  · apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ h, one_mul]
  · apply ContinuousLinearMap.ext
    intro x
    simp only [ContinuousLinearMap.comp_apply, smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ h, one_mul]

/-! ## Coordinate insertion / deletion as continuous linear maps

The linear change of variables underlying the implicit function theorem for a level set with
respect to the `i`-th coordinate is the identification
`(Fin (m+1) → ℝ) ≃ ℝ × (Fin m → ℝ)`, `x ↦ (x i, x ∘ Fin.succAbove i)`, with inverse
`(t, u) ↦ Fin.insertNth i t u`.  We record these two maps (and their inverses) as continuous
linear maps, together with the fact that `Fin.insertNth` reassembles a vector. -/

/-- `(t, u) ↦ Fin.insertNth i t u` as a continuous linear map. -/
noncomputable def insT (m : ℕ) (i : Fin (m + 1)) :
    (ℝ × (Fin m → ℝ)) →L[ℝ] (Fin (m + 1) → ℝ) :=
  Work.WilE9G.Sard.insCLM m i

theorem insT_apply {m : ℕ} (i : Fin (m + 1)) (t : ℝ) (u : Fin m → ℝ) :
    insT m i (t, u) = Fin.insertNth i t u := by
  rw [insT, Work.WilE9G.Sard.insCLM_apply]

/-- `(u, t) ↦ Fin.insertNth i t u`, the variables in the order matching `Function.uncurry`. -/
noncomputable def insT₂ (m : ℕ) (i : Fin (m + 1)) :
    ((Fin m → ℝ) × ℝ) →L[ℝ] (Fin (m + 1) → ℝ) :=
  (insT m i).comp ((ContinuousLinearMap.snd ℝ (Fin m → ℝ) ℝ).prod
    (ContinuousLinearMap.fst ℝ (Fin m → ℝ) ℝ))

theorem insT₂_apply {m : ℕ} (i : Fin (m + 1)) (u : Fin m → ℝ) (t : ℝ) :
    insT₂ m i (u, t) = Fin.insertNth i t u := by
  rw [insT₂, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply]
  show insT m i (t, u) = Fin.insertNth i t u
  rw [insT_apply]

/-- `x ↦ (x ∘ Fin.succAbove i, x i)` as a continuous linear map. -/
noncomputable def delT (m : ℕ) (i : Fin (m + 1)) :
    (Fin (m + 1) → ℝ) →L[ℝ] ((Fin m → ℝ) × ℝ) :=
  (ContinuousLinearMap.pi fun k : Fin m =>
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℝ) (i.succAbove k)).prod
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℝ) i)

theorem delT_apply {m : ℕ} (i : Fin (m + 1)) (x : Fin (m + 1) → ℝ) :
    delT m i x = (x ∘ Fin.succAbove i, x i) := by
  refine Prod.ext ?_ ?_
  · funext l
    simp only [delT, ContinuousLinearMap.prod_apply, ContinuousLinearMap.pi_apply,
      ContinuousLinearMap.proj_apply, Function.comp_apply]
  · simp only [delT, ContinuousLinearMap.prod_apply, ContinuousLinearMap.proj_apply]

/-- `Fin.insertNth` reassembles a vector from its `i`-th coordinate and the remaining ones. -/
theorem insertNth_self {m : ℕ} (i : Fin (m + 1)) (x : Fin (m + 1) → ℝ) :
    Fin.insertNth i (x i) (fun l => x (i.succAbove l)) = x := by
  funext j
  by_cases hj : j = i
  · subst hj; rw [Fin.insertNth_apply_same]
  · obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hj
    rw [← hz, Fin.insertNth_apply_succAbove]

/-! ## The implicit function theorem for a regular level set -/

theorem local_graph_level_set {m : ℕ} (F : (Fin (m+1) → ℝ) → ℝ) (hF : ContDiff ℝ 2 F)
    (i : Fin (m+1)) (x₀ : Fin (m+1) → ℝ) (h0 : F x₀ = 0)
    (hx : fderiv ℝ F x₀ (Pi.single i 1) ≠ 0) :
    ∃ (h : (Fin m → ℝ) → ℝ) (A : Set (Fin m → ℝ)),
      IsOpen A ∧ (x₀ ∘ Fin.succAbove i) ∈ A ∧ ContDiffOn ℝ 1 h A ∧
      h (x₀ ∘ Fin.succAbove i) = x₀ i ∧
      (∀ u ∈ A, F (Fin.insertNth i (h u) u) = 0) ∧
      ∃ B : Set (Fin (m+1) → ℝ), IsOpen B ∧ x₀ ∈ B ∧
        ∀ x ∈ B, F x = 0 →
          x = Fin.insertNth i (h (x ∘ Fin.succAbove i)) (x ∘ Fin.succAbove i) := by
  classical
  set u₀ : Fin m → ℝ := fun l => x₀ (i.succAbove l) with hu₀
  set g : (Fin m → ℝ) → ℝ → ℝ := fun u t => F (insT m i (t, u)) with hg
  -- `uncurry g = F ∘ insT₂`
  have hU : Function.uncurry g = F ∘ ⇑(insT₂ m i) := by
    funext p
    obtain ⟨u, t⟩ := p
    show g u t = F (insT₂ m i (u, t))
    rw [hg]
    show F (insT m i (t, u)) = F (insT₂ m i (u, t))
    simp only [insT_apply, insT₂_apply]
  -- smoothness at the base point
  have hgcd : ContDiffAt ℝ 1 (Function.uncurry g) (u₀, x₀ i) := by
    rw [hU]
    exact ((hF.comp (insT₂ m i).contDiff).contDiffAt).of_le (one_le_two : (1 : WithTop ℕ∞) ≤ 2)
  -- vanishing at the base point
  have hins : insT m i (x₀ i, u₀) = x₀ := by
    rw [insT_apply, hu₀]
    exact insertNth_self i x₀
  have hg0 : g u₀ (x₀ i) = 0 := by
    show F (insT m i (x₀ i, u₀)) = 0
    rw [hins, h0]
  -- invertibility of the partial differential in the second variable
  have hins₂ : insT₂ m i (u₀, x₀ i) = x₀ := by
    rw [insT₂_apply, hu₀]
    exact insertNth_self i x₀
  have hFd : HasFDerivAt F (fderiv ℝ F x₀) x₀ :=
    (((hF.contDiffAt (x := x₀)).of_le (one_le_two : (1 : WithTop ℕ∞) ≤ 2)).differentiableAt_one).hasFDerivAt
  have hfderiv : fderiv ℝ (Function.uncurry g) (u₀, x₀ i)
      = (fderiv ℝ F x₀) ∘L insT₂ m i := by
    have hFd' : HasFDerivAt F (fderiv ℝ F x₀) (insT₂ m i (u₀, x₀ i)) := by
      rw [hins₂]; exact hFd
    have h := (hFd'.comp (u₀, x₀ i) (insT₂ m i).hasFDerivAt).fderiv
    rw [hU]
    exact h
  have hkey : (((fderiv ℝ F x₀) ∘L insT₂ m i) ∘L
      ContinuousLinearMap.inr ℝ (Fin m → ℝ) ℝ) 1 = fderiv ℝ F x₀ (Pi.single i 1) := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.inr_apply]
    congr 1
    rw [insT₂_apply]
    funext j
    by_cases hj : j = i
    · subst hj; rw [Fin.insertNth_apply_same, Pi.single_eq_same]
    · obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hj
      rw [← hz, Fin.insertNth_apply_succAbove, Pi.single_eq_of_ne (Fin.succAbove_ne i z)]
      rfl
  have hinv : (fderiv ℝ (Function.uncurry g) (u₀, x₀ i) ∘L
      ContinuousLinearMap.inr ℝ (Fin m → ℝ) ℝ).IsInvertible := by
    rw [hfderiv]
    refine isInvertible_of_apply_one_ne_zero _ ?_
    rw [hkey]
    exact hx
  -- the implicit function
  obtain ⟨φ, A, B₁, hAo, hB₁o, hu₀A, hv₀B₁, hφcd, hφ0, hφeq, hφuniq⟩ :=
    Work.WilE2.Ebc.local_graph_of_submersion_real g u₀ (x₀ i) hgcd hg0 hinv
  refine ⟨φ, A, hAo, ?_, hφcd, ?_, ?_, ?_⟩
  · exact hu₀A
  · exact hφ0
  · intro u hu
    have h : F (insT m i (φ u, u)) = 0 := hφeq u hu
    rw [insT_apply] at h
    exact h
  · refine ⟨delT m i ⁻¹' (A ×ˢ B₁), ?_, ?_, ?_⟩
    · exact IsOpen.preimage (delT m i).continuous (hAo.prod hB₁o)
    · show delT m i x₀ ∈ A ×ˢ B₁
      rw [delT_apply, Set.mem_prod]
      exact ⟨hu₀A, hv₀B₁⟩
    · intro x hxB hx0
      have hdel : delT m i x ∈ A ×ˢ B₁ := hxB
      rw [delT_apply, Set.mem_prod] at hdel
      obtain ⟨huA, htB⟩ := hdel
      have hgx : g (fun l => x (i.succAbove l)) (x i) = 0 := by
        show F (insT m i (x i, fun l => x (i.succAbove l))) = 0
        rw [insT_apply, insertNth_self i x]
        exact hx0
      have huniq : x i = φ (fun l => x (i.succAbove l)) :=
        hφuniq (fun l => x (i.succAbove l)) huA (x i) htB hgx
      have huniq' : x i = φ (x ∘ Fin.succAbove i) := huniq
      rw [← huniq']
      exact (insertNth_self i x).symm

end Work.WilE2.Cb
