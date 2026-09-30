import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The saturated flag of `ℤⁿ` attached to an integer matrix

Given `z : Fin n → (Fin n → ℤ)`, viewed as `n` vectors of `ℤⁿ`, this file sets up the
`saturated` (pure) flag of `ℤⁿ` cut out by the partial `ℚ`-spans of the `z`'s.

* `castQ n : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℚ)` and `castR n : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℝ)`
  are the entrywise casting maps.
* `Wq z j` is the `ℚ`-span of `z 0, …, z j` inside `ℚⁿ`.
* `Wr z j` is the `ℝ`-span of `z 0, …, z j` inside `ℝⁿ`.
* `Ksat z j = ℤⁿ ∩ Wq z j` is the saturation (pure closure) of the `ℤ`-span of `z 0, …, z j`.

The point of the saturation is that `Ksat z j` is a *pure* sublattice of `ℤⁿ`, hence a direct
summand; the flag `Ksat z 0 ⊆ Ksat z 1 ⊆ ⋯ ⊆ Ksat z (n-1) = ℤⁿ` then admits an adapted `ℤ`-basis,
which is the content of `Work.BW.Minkowski2.exists_zbasis_adapted`.
-/

namespace Work.BW.Minkowski2

open Module

variable {n : ℕ}

/-- The `ℤ`-linear map `ℤⁿ → ℚⁿ` casting the entries. -/
noncomputable def castQ (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℚ) where
  toFun x := fun i => (x i : ℚ)
  map_add' x y := by ext i; simp
  map_smul' m x := by ext i; simp [zsmul_eq_mul]

/-- The `ℤ`-linear map `ℤⁿ → ℝⁿ` casting the entries. -/
noncomputable def castR (n : ℕ) : (Fin n → ℤ) →ₗ[ℤ] (Fin n → ℝ) where
  toFun x := fun i => (x i : ℝ)
  map_add' x y := by ext i; simp
  map_smul' m x := by ext i; simp [zsmul_eq_mul]

@[simp] theorem castQ_apply (x : Fin n → ℤ) (i : Fin n) : castQ n x i = (x i : ℚ) := rfl

@[simp] theorem castR_apply (x : Fin n → ℤ) (i : Fin n) : castR n x i = (x i : ℝ) := rfl

/-- The `ℚ`-span of `z 0, …, z j`. -/
noncomputable def Wq (z : Fin n → (Fin n → ℤ)) (j : ℕ) : Submodule ℚ (Fin n → ℚ) :=
  Submodule.span ℚ (Set.range (fun k : {k : Fin n // k.1 ≤ j} => fun i => (z k.1 i : ℚ)))

/-- The `ℝ`-span of `z 0, …, z j`. -/
noncomputable def Wr (z : Fin n → (Fin n → ℤ)) (j : ℕ) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ (Set.range (fun k : {k : Fin n // k.1 ≤ j} => fun i => (z k.1 i : ℝ)))

/-- The lattice `ℤⁿ ∩ ⟨z 0, …, z j⟩_ℚ`: the saturation of the `ℤ`-span of `z 0, …, z j`. -/
noncomputable def Ksat (z : Fin n → (Fin n → ℤ)) (j : ℕ) : Submodule ℤ (Fin n → ℤ) :=
  Submodule.comap (castQ n) ((Wq z j).restrictScalars ℤ)

theorem mem_Ksat {z : Fin n → (Fin n → ℤ)} {j : ℕ} {x : Fin n → ℤ} :
    x ∈ Ksat z j ↔ (fun i => (x i : ℚ)) ∈ Wq z j :=
  Submodule.mem_comap

theorem z_mem_Wq (z : Fin n → (Fin n → ℤ)) {j : ℕ} {k : Fin n} (hk : k.1 ≤ j) :
    (fun i => (z k i : ℚ)) ∈ Wq z j :=
  Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩

theorem z_mem_Wr (z : Fin n → (Fin n → ℤ)) {j : ℕ} {k : Fin n} (hk : k.1 ≤ j) :
    (fun i => (z k i : ℝ)) ∈ Wr z j :=
  Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩

theorem z_mem_Ksat (z : Fin n → (Fin n → ℤ)) {j : ℕ} {k : Fin n} (hk : k.1 ≤ j) :
    z k ∈ Ksat z j := by
  rw [mem_Ksat]
  exact z_mem_Wq z hk

theorem Wq_mono (z : Fin n → (Fin n → ℤ)) {j j' : ℕ} (h : j ≤ j') : Wq z j ≤ Wq z j' := by
  refine Submodule.span_mono ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨⟨k.1, le_trans k.2 h⟩, rfl⟩

theorem Wr_mono (z : Fin n → (Fin n → ℤ)) {j j' : ℕ} (h : j ≤ j') : Wr z j ≤ Wr z j' := by
  refine Submodule.span_mono ?_
  rintro _ ⟨k, rfl⟩
  exact ⟨⟨k.1, le_trans k.2 h⟩, rfl⟩

theorem Ksat_mono (z : Fin n → (Fin n → ℤ)) {j j' : ℕ} (h : j ≤ j') : Ksat z j ≤ Ksat z j' := by
  intro x hx
  rw [mem_Ksat] at hx ⊢
  exact Wq_mono z h hx

/-- `Ksat z j` is pure (saturated) in `ℤⁿ`. -/
theorem Ksat_pure (z : Fin n → (Fin n → ℤ)) (j : ℕ) {m : ℤ} (hm : m ≠ 0) {x : Fin n → ℤ}
    (hx : m • x ∈ Ksat z j) : x ∈ Ksat z j := by
  rw [mem_Ksat] at hx ⊢
  have hcast : (fun i => ((m • x) i : ℚ)) = (m : ℚ) • (fun i => (x i : ℚ)) := by
    ext i; simp [zsmul_eq_mul]
  rw [hcast] at hx
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have := Submodule.smul_mem (Wq z j) (m : ℚ)⁻¹ hx
  rwa [smul_smul, inv_mul_cancel₀ hmq, one_smul] at this

end Work.BW.Minkowski2
