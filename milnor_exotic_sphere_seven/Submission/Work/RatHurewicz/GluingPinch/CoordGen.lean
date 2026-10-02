import Mathlib
import Submission.Work.RatHurewicz.PsiKillsAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The general-`n` coordinate reparametrisation lemmas

Tools for computing the class of an *arrangement* of based cubes on cells of `I^n`, read in the
cells' own coordinates:

* `interp` — the linear interpolation `(1-t)a + t b` in `I`;
* `coordUpd i ψ` — replace the `i`-th coordinate by `ψ` applied to it;
* `cl_coordUpd` — if `ψ 0 = 0` and `ψ 1 = 1` then replacing the `i`-th coordinate by `ψ` does not
  change the class of a based cube (linear-interpolation homotopy, every slice a based cube);
* `cl_symmAt'` — the class of a cube reversed in one coordinate is the inverse.

Everything is stated for `GenLoop (Fin n)` with `n` arbitrary.
-/

open scoped unitInterval Topology
open Work.Stems.Cubical

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X] {x₀ : X}

/-- The linear interpolation `(1-t) a + t b` in `[0,1]`. -/
def interp (t a b : unitInterval) : unitInterval :=
  ⟨(1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ), by
    have ha := a.2
    have hb := b.2
    have ht := t.2
    constructor
    · have h1 : (0 : ℝ) ≤ 1 - (t : ℝ) := by linarith [ht.2]
      nlinarith [mul_nonneg h1 ha.1, mul_nonneg ht.1 hb.1]
    · have h1 : (0 : ℝ) ≤ 1 - (t : ℝ) := by linarith [ht.2]
      nlinarith [mul_le_mul_of_nonneg_left ha.2 h1, mul_le_mul_of_nonneg_left hb.2 ht.1]⟩

@[simp] theorem interp_coe (t a b : unitInterval) :
    ((interp t a b : unitInterval) : ℝ) = (1 - (t : ℝ)) * (a : ℝ) + (t : ℝ) * (b : ℝ) := rfl

@[simp] theorem interp_left (a b : unitInterval) : interp 0 a b = a := by
  apply Subtype.ext
  simp [interp_coe]

@[simp] theorem interp_right (a b : unitInterval) : interp 1 a b = b := by
  apply Subtype.ext
  simp [interp_coe]

@[simp] theorem interp_zero (t : unitInterval) : interp t 0 0 = 0 := by
  apply Subtype.ext
  simp [interp_coe]

@[simp] theorem interp_one (t : unitInterval) : interp t 1 1 = 1 := by
  apply Subtype.ext
  simp [interp_coe]

/-- Replace the `i`-th coordinate by `ψ` applied to it. -/
def coordUpd (n : ℕ) (i : Fin n) (ψ : C(unitInterval, unitInterval)) : C(IC n, IC n) where
  toFun u := Function.update u i (ψ (u i))
  continuous_toFun := continuous_id.update i (ψ.continuous.comp (continuous_apply i))

@[simp] theorem coordUpd_apply {n : ℕ} (i : Fin n) (ψ : C(unitInterval, unitInterval)) (u : IC n) :
    coordUpd n i ψ u = Function.update u i (ψ (u i)) := rfl

theorem coordUpd_apply_self {n : ℕ} (i : Fin n) (ψ : C(unitInterval, unitInterval)) (u : IC n) :
    coordUpd n i ψ u i = ψ (u i) := by
  simp [coordUpd_apply]

theorem coordUpd_apply_of_ne {n : ℕ} (i : Fin n) (ψ : C(unitInterval, unitInterval)) (u : IC n)
    {j : Fin n} (hj : j ≠ i) : coordUpd n i ψ u j = u j := by
  simp [coordUpd_apply, hj]

theorem coordUpd_mem_boundary {n : ℕ} (i : Fin n) (ψ : C(unitInterval, unitInterval))
    (h0 : ψ 0 = 0) (h1 : ψ 1 = 1) {u : IC n} (hu : u ∈ Cube.boundary (Fin n)) :
    coordUpd n i ψ u ∈ Cube.boundary (Fin n) := by
  obtain ⟨j, hj | hj⟩ := hu
  · by_cases hji : j = i
    · subst j
      refine ⟨i, Or.inl ?_⟩
      rw [coordUpd_apply, Function.update_apply, if_pos rfl, hj]
      exact h0
    · refine ⟨j, Or.inl ?_⟩
      rw [coordUpd_apply, Function.update_apply, if_neg hji]
      exact hj
  · by_cases hji : j = i
    · subst j
      refine ⟨i, Or.inr ?_⟩
      rw [coordUpd_apply, Function.update_apply, if_pos rfl, hj]
      exact h1
    · refine ⟨j, Or.inr ?_⟩
      rw [coordUpd_apply, Function.update_apply, if_neg hji]
      exact hj

/-- The interpolation between `ψ` and the identity, as a map `I^n × I → I^n`. -/
def coordHom (n : ℕ) (i : Fin n) (ψ : C(unitInterval, unitInterval)) : C(IC n × unitInterval, IC n)
    where
  toFun p := Function.update p.1 i (interp p.2 (ψ (p.1 i)) (p.1 i))
  continuous_toFun := by
    refine continuous_pi fun j => ?_
    by_cases hj : j = i
    · rw [hj]
      have hcont : Continuous fun p : IC n × unitInterval =>
          ((interp p.2 (ψ (p.1 i)) (p.1 i) : unitInterval) : ℝ) := by
        simp only [interp_coe]
        fun_prop
      simpa only [Function.update_apply, if_pos rfl, if_true] using hcont.subtype_mk _
    · have h1 : Continuous fun p : IC n × unitInterval => (p.1 j : unitInterval) :=
        (continuous_apply j).comp continuous_fst
      show Continuous fun p : IC n × unitInterval =>
        ((Function.update p.1 i (interp p.2 (ψ (p.1 i)) (p.1 i)) : IC n) j)
      simp only [Function.update_apply, if_neg hj]
      exact h1

@[simp] theorem coordHom_apply {n : ℕ} (i : Fin n) (ψ : C(unitInterval, unitInterval))
    (p : IC n × unitInterval) :
    coordHom n i ψ p = Function.update p.1 i (interp p.2 (ψ (p.1 i)) (p.1 i)) := rfl

@[simp] theorem coordHom_zero {n : ℕ} (i : Fin n) (ψ : C(unitInterval, unitInterval)) (u : IC n) :
    coordHom n i ψ (u, 0) = coordUpd n i ψ u := by
  funext j
  by_cases hj : j = i
  · subst j
    apply Subtype.ext
    simp [coordHom_apply, coordUpd_apply]
  · rw [coordHom_apply, coordUpd_apply, Function.update_apply, if_neg hj,
      Function.update_apply, if_neg hj]

@[simp] theorem coordHom_one {n : ℕ} (i : Fin n) (ψ : C(unitInterval, unitInterval)) (u : IC n) :
    coordHom n i ψ (u, 1) = u := by
  funext j
  by_cases hj : j = i
  · subst j
    apply Subtype.ext
    simp [coordHom_apply]
  · rw [coordHom_apply, Function.update_apply, if_neg hj]

theorem coordHom_mem_boundary {n : ℕ} (i : Fin n) (ψ : C(unitInterval, unitInterval))
    (h0 : ψ 0 = 0) (h1 : ψ 1 = 1) {u : IC n} (hu : u ∈ Cube.boundary (Fin n))
    (t : unitInterval) : coordHom n i ψ (u, t) ∈ Cube.boundary (Fin n) := by
  obtain ⟨j, hj | hj⟩ := hu
  · by_cases hji : j = i
    · subst j
      refine ⟨i, Or.inl ?_⟩
      rw [coordHom_apply, Function.update_apply, if_pos rfl]
      change interp t (ψ (u i)) (u i) = 0
      rw [hj, h0]
      exact interp_zero t
    · refine ⟨j, Or.inl ?_⟩
      rw [coordHom_apply, Function.update_apply, if_neg hji]
      exact hj
  · by_cases hji : j = i
    · subst j
      refine ⟨i, Or.inr ?_⟩
      rw [coordHom_apply, Function.update_apply, if_pos rfl]
      change interp t (ψ (u i)) (u i) = 1
      rw [hj, h1]
      exact interp_one t
    · refine ⟨j, Or.inr ?_⟩
      rw [coordHom_apply, Function.update_apply, if_neg hji]
      exact hj

/-- **Reparametrising one coordinate does not change the class** (for a reparametrisation fixing
the endpoints). -/
theorem cl_coordUpd {n : ℕ} [NeZero n] (i : Fin n) (ψ : C(unitInterval, unitInterval))
    (h0 : ψ 0 = 0) (h1 : ψ 1 = 1) (p : GenLoop (Fin n) X x₀) :
    cl n X x₀ ⟨p.1.comp (coordUpd n i ψ), fun u hu => p.2 _ (coordUpd_mem_boundary i ψ h0 h1 hu)⟩
      = cl n X x₀ p := by
  have h := genLoop_homotopic_comp_of_id n (coordUpd n i ψ)
    (fun u hu => coordUpd_mem_boundary i ψ h0 h1 hu) (coordHom n i ψ)
    (fun u => coordHom_zero i ψ u) (fun u => coordHom_one i ψ u)
    (fun u hu t => coordHom_mem_boundary i ψ h0 h1 hu t) p
  have hcl : (show HomotopyGroup (Fin n) X x₀ from
      Quotient.mk _ ⟨p.1.comp (coordUpd n i ψ),
        fun u hu => p.2 _ (coordUpd_mem_boundary i ψ h0 h1 hu)⟩)
      = (show HomotopyGroup (Fin n) X x₀ from Quotient.mk _ p) := Quotient.sound h
  simpa only [cl] using hcl

/-- **The reversal lemma**: the class of a based cube reversed in coordinate `i` is the inverse. -/
theorem cl_symmAt' {n : ℕ} [NeZero n] (i : Fin n) (p : GenLoop (Fin n) X x₀) :
    cl n X x₀ (GenLoop.symmAt i p) = (cl n X x₀ p)⁻¹ := by
  have h := HomotopyGroup.inv_spec (N := Fin n) (X := X) (x := x₀) (i := i) (p := p)
  simpa only [cl] using h.symm

end

end Work.RatHurewicz
