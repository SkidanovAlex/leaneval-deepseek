import Mathlib
import Submission.Work.ORLyndon.gordan_negative_separation

namespace Work.ORLyndon

open scoped BigOperators

set_option linter.unusedSectionVars false
set_option autoImplicit false

section Helpers

variable {α : Type*} [DecidableEq α]

/-- The linear functional `u ↦ ∑ y ∈ s, w y * u y` on `α → ℚ`. -/
noncomputable def weightFun (w : α → ℚ) (s : Finset α) : (α → ℚ) →ₗ[ℚ] ℚ :=
  ∑ y ∈ s, w y • LinearMap.proj y

lemma weightFun_apply (w : α → ℚ) (s : Finset α) (u : α → ℚ) :
    weightFun w s u = ∑ y ∈ s, w y * u y := by
  simp [weightFun, smul_eq_mul]

lemma weightFun_single (w : α → ℚ) (s : Finset α) {y : α} (hy : y ∈ s) :
    weightFun w s (Pi.single y 1) = w y := by
  rw [weightFun_apply, Finset.sum_eq_single y]
  · simp
  · intro b _ hby; rw [Pi.single_eq_of_ne hby]; simp
  · intro hy'; exact absurd hy hy'

end Helpers

section SumSubtype

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A sum over all of `ι` of a function vanishing at `i₀` equals the sum over the subtype
`{j // j ≠ i₀}`. -/
lemma sum_eq_sum_subtype_ne (i₀ : ι) (f : ι → ℚ) (hf : f i₀ = 0) :
    ∑ i, f i = ∑ j : {j : ι // j ≠ i₀}, f j.1 := by
  have hvan : ∀ x ∈ (Finset.univ : Finset ι),
      x ∉ Finset.univ.filter (fun y => y ≠ i₀) → f x = 0 := by
    intro x _ hx'
    by_contra hfx
    exact hx' (Finset.mem_filter.mpr ⟨Finset.mem_univ x, fun hxi => hfx (by rw [hxi, hf])⟩)
  rw [← Finset.sum_subset (Finset.filter_subset _ _) hvan]
  rw [Finset.sum_subtype (p := fun x => x ≠ i₀)
    (s := Finset.univ.filter (fun x => x ≠ i₀)) (h := fun x => by simp)]

end SumSubtype

theorem exposedVertex_separating_weight {α : Type*} [DecidableEq α] {ι : Type*} [Fintype ι]
    (s : Finset α) (e : α → ℚ) (p : ι → α → ℚ) (i₀ : ι)
    (hexp : ¬ ∃ (lam : ι → ℚ) (mu : ℚ),
      (∀ j, 0 ≤ lam j) ∧ lam i₀ = 0 ∧ (∑ j, lam j = 1) ∧
        ∀ y ∈ s, p i₀ y = (∑ j, lam j * p j y) + mu * e y) :
    ∃ φ : α → ℚ, (∑ y ∈ s, φ y * e y) = 0 ∧
      ∀ j, j ≠ i₀ → (∑ y ∈ s, φ y * p j y) < (∑ y ∈ s, φ y * p i₀ y) := by
  classical
  set P : {j : ι // j ≠ i₀} → Module.Dual ℚ (LinearMap.ker (weightFun e s)) :=
    fun j => (weightFun (p j.1) s - weightFun (p i₀) s).comp
      (LinearMap.ker (weightFun e s)).subtype with hP
  have hRed : ¬ ∃ mu : {j : ι // j ≠ i₀} → ℚ,
      (∀ j, 0 ≤ mu j) ∧ mu ≠ 0 ∧ ∑ j, mu j • P j = 0 := by
    rintro ⟨mu, hmu0, hmunz, hsum⟩
    set Psi : (α → ℚ) →ₗ[ℚ] ℚ :=
      ∑ j : {j : ι // j ≠ i₀}, mu j • (weightFun (p j.1) s - weightFun (p i₀) s) with hPsidf
    have hkerle : LinearMap.ker (weightFun e s) ≤ LinearMap.ker Psi := by
      intro u hu
      rw [LinearMap.mem_ker]
      have h1 : Psi u = (∑ j, mu j • P j) ⟨u, hu⟩ := by
        simp only [hPsidf, hP, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply,
          LinearMap.sub_apply, Submodule.subtype_apply, smul_eq_mul]
      rw [h1, hsum]
      simp
    have hspan : Psi ∈ Submodule.span ℚ (Set.range (fun _ : Unit => weightFun e s)) :=
      mem_span_of_iInf_ker_le_ker (L := fun _ : Unit => weightFun e s) (K := Psi)
        (by simpa using hkerle)
    rw [show Set.range (fun _ : Unit => weightFun e s) = {weightFun e s} from by simp] at hspan
    rw [Submodule.mem_span_singleton] at hspan
    obtain ⟨c, hc⟩ := hspan
    set k : ℚ := ∑ j : {j : ι // j ≠ i₀}, mu j with hkdef
    have hkpos : 0 < k := by
      rw [hkdef]
      refine Finset.sum_pos' (fun j _ => hmu0 j) ?_
      obtain ⟨j, hj⟩ : ∃ j, mu j ≠ 0 := by
        by_contra hc'
        exact hmunz (funext fun i => by by_contra hi; exact hc' ⟨i, hi⟩)
      exact ⟨j, Finset.mem_univ j, lt_of_le_of_ne (hmu0 j) (Ne.symm hj)⟩
    have hkne : k ≠ 0 := ne_of_gt hkpos
    have hrel : ∀ y ∈ s, ∑ j : {j : ι // j ≠ i₀}, mu j * (p j.1 y - p i₀ y) = c * e y := by
      intro y hy
      have h1 := congrArg (fun (f : (α → ℚ) →ₗ[ℚ] ℚ) => f (Pi.single y 1)) hc
      rw [LinearMap.smul_apply, smul_eq_mul, weightFun_single e s hy] at h1
      have h2 : Psi (Pi.single y 1) = ∑ j, mu j * (p j.1 y - p i₀ y) := by
        simp only [hPsidf, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.sub_apply,
          smul_eq_mul]
        apply Finset.sum_congr rfl
        intro j _
        rw [weightFun_single (p j.1) s hy, weightFun_single (p i₀) s hy]
      rw [h2] at h1
      exact h1.symm
    set lam : ι → ℚ := fun i => if h : i = i₀ then 0 else mu ⟨i, h⟩ / k with hlamdef
    have hlam_ne : ∀ j : {j : ι // j ≠ i₀}, lam j.1 = mu j / k := by
      intro j; simp only [hlamdef, dif_neg j.2, Subtype.eta]
    refine hexp ⟨lam, -(c / k), ?_, ?_, ?_, ?_⟩
    · intro i
      by_cases hi : i = i₀
      · subst hi; simp [hlamdef]
      · simp only [hlamdef, dif_neg hi]
        exact div_nonneg (hmu0 ⟨i, hi⟩) (le_of_lt hkpos)
    · simp [hlamdef]
    · rw [sum_eq_sum_subtype_ne i₀ lam (by simp [hlamdef])]
      have h1 : (∑ j : {j : ι // j ≠ i₀}, lam j.1) = ∑ j, mu j / k :=
        Finset.sum_congr rfl (fun j _ => hlam_ne j)
      rw [h1, ← Finset.sum_div, ← hkdef]
      exact div_self hkne
    · intro y hy
      have hlamy : (∑ i : ι, lam i * p i y) = ∑ j : {j : ι // j ≠ i₀}, (mu j / k) * p j.1 y := by
        rw [sum_eq_sum_subtype_ne i₀ (fun i => lam i * p i y)
          (by rw [show lam i₀ = 0 from by simp [hlamdef]]; ring)]
        exact Finset.sum_congr rfl (fun j _ => by rw [hlam_ne j])
      have hA : ∑ j : {j : ι // j ≠ i₀}, mu j * (p j.1 y - p i₀ y) = c * e y := hrel y hy
      have expand : ∑ j : {j : ι // j ≠ i₀}, mu j * (p j.1 y - p i₀ y)
          = (∑ j : {j : ι // j ≠ i₀}, mu j * p j.1 y) - k * p i₀ y := by
        calc ∑ j : {j : ι // j ≠ i₀}, mu j * (p j.1 y - p i₀ y)
            = ∑ j, (mu j * p j.1 y - mu j * p i₀ y) :=
              Finset.sum_congr rfl (fun j _ => by ring)
          _ = (∑ j, mu j * p j.1 y) - ∑ j, mu j * p i₀ y := Finset.sum_sub_distrib _ _
          _ = (∑ j, mu j * p j.1 y) - (∑ j, mu j) * p i₀ y := by rw [Finset.sum_mul]
          _ = (∑ j, mu j * p j.1 y) - k * p i₀ y := by rw [hkdef]
      have hmain : ∑ j : {j : ι // j ≠ i₀}, mu j * p j.1 y = k * p i₀ y + c * e y := by
        have := hA; rw [expand] at this; linarith
      have hsum2 : ∑ j : {j : ι // j ≠ i₀}, (mu j / k) * p j.1 y
          = (∑ j : {j : ι // j ≠ i₀}, mu j * p j.1 y) / k := by
        rw [Finset.sum_congr rfl (fun j _ => by rw [div_mul_eq_mul_div]), ← Finset.sum_div]
      rw [hlamy, hsum2, hmain]
      field_simp
      ring
  obtain ⟨u, hu⟩ := gordan_negative_separation P hRed
  refine ⟨(u : α → ℚ), ?_, ?_⟩
  · have h1 : (∑ y ∈ s, (u : α → ℚ) y * e y) = ∑ y ∈ s, e y * (u : α → ℚ) y :=
      Finset.sum_congr rfl (fun y _ => mul_comm _ _)
    rw [h1, ← weightFun_apply]
    exact LinearMap.mem_ker.mp u.2
  · intro j hj
    have hlt := hu ⟨j, hj⟩
    have hdiff : P ⟨j, hj⟩ u = (weightFun (p j) s - weightFun (p i₀) s) (u : α → ℚ) := by
      simp only [hP, LinearMap.comp_apply, Submodule.subtype_apply]
    rw [hdiff] at hlt
    have hw : (weightFun (p j) s - weightFun (p i₀) s) (u : α → ℚ)
        = (∑ y ∈ s, p j y * (u : α → ℚ) y) - (∑ y ∈ s, p i₀ y * (u : α → ℚ) y) := by
      rw [LinearMap.sub_apply, weightFun_apply, weightFun_apply]
    rw [hw] at hlt
    have h1 : (∑ y ∈ s, (u : α → ℚ) y * p j y) = ∑ y ∈ s, p j y * (u : α → ℚ) y :=
      Finset.sum_congr rfl (fun y _ => mul_comm _ _)
    have h2 : (∑ y ∈ s, (u : α → ℚ) y * p i₀ y) = ∑ y ∈ s, p i₀ y * (u : α → ℚ) y :=
      Finset.sum_congr rfl (fun y _ => mul_comm _ _)
    rw [h1, h2]
    linarith

end Work.ORLyndon
