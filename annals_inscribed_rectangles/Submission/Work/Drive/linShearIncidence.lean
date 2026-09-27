import Mathlib
import Submission.Work.Drive.linShearCharts
import Submission.Work.Drive.exists_hrank_hgen_trans

/-!
# The incidence data of the sheared linear charts (the pair row `PairReg lin₀ lin₁`)

`Work.Drive.linBase A k = (linShear k).trans ((coordPermCLM (coordPerms k)).trans A)` is the *sheared*
linear chart family of `NOTES_LEAD_hodd_faces.md` §3 (Hugelmeyer's ends clause, the pair row).

The criterion `Work.Drive.pairReg_linPlaneCharts_of_incidence`
(`Submission/Work/Drive/pairReg_linPlaneCharts_of_incidence.lean`) reduces the spanning condition
`PairReg` of the two linear disk charts — the only pair row of the ends clause that is *not* covered by
the triple rows — to **six purely linear conditions** on `Φ₀ = linBase A 0` and `Φ₁ = linBase A 1`: the
two boundary lines `linBdry Φ = Φ (span {e₀, e₁})` miss each other, neither lies in the other's plane
`linSub Φ = Φ (linStd)`, the two corner directions `Φ₀ (e₀ ± e₁)`, `Φ₁ (e₀ ± e₁)` avoid the other
plane, and the two planes are distinct.

This file proves that **all six hold for every `A`** — the incidence of the sheared family is not a
genericity statement at all, and the `φ`-chooser of the design needs no incidence clause (the `hgood`
clause, which *is* generic, belongs to the three-chart family of
`Work.Drive.exists_linPlaneCharts_hgen`).  The verification is a coordinate computation on
`Eucl 3 = ℝ⁴`: with `ρ_k = coordPerms k` one has

* `linSub (linBase A k) = {v : (A⁻¹ v) (ρ_k 3) = 0}` — so `k = 0` gives `(A⁻¹ v) 1 = 0` and `k = 1`
  gives `(A⁻¹ v) 2 = 0`;
* `linBdry (linBase A 0) = A '' span {e₂, e₃}` and `linBdry (linBase A 1) = A '' span {e₁, e₀ + e₃}`;
* `span {e₂, e₃} ⊓ span {e₁, e₀ + e₃} = ⊥`, `e₂ ∉ span {e₁, e₀ + e₃}`, `e₁ ∉ span {e₂, e₃}`;

and the two corner evaluations `linBase A 0 (e₀ + s e₁) = A (e₂ + s e₃)`,
`linBase A 1 (e₀ + s e₁) = A (e₁ + s (e₀ + e₃))`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-! ## 1. Coordinates and the fourth basis vector -/

/-- The `j`-th coordinate functional of `Eucl 3 = ℝ⁴`. -/
def coordFun (j : Fin 4) : Eucl 3 →ₗ[ℝ] ℝ :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 4 => ℝ) j).toLinearMap

lemma coordFun_apply (j : Fin 4) (v : Eucl 3) : coordFun j v = v j := rfl

/-- The fourth standard basis vector `e₃ = single 3 1` of `Eucl 3 = ℝ⁴`. -/
abbrev linE3 : Eucl 3 := (EuclideanSpace.single 3 (1 : ℝ) : Eucl 3)

/-! ## 2. The shear and the coordinate permutation on the standard basis -/

/-- A coordinate permutation carries `eᵢ` to `e_{ρ i}`. -/
lemma coordPermCLM_single (ρ : Equiv.Perm (Fin 4)) (i : Fin 4) :
    coordPermCLM ρ (EuclideanSpace.single i (1 : ℝ) : Eucl 3)
      = (EuclideanSpace.single (ρ i) (1 : ℝ) : Eucl 3) := by
  ext j
  rw [coordPermCLM_apply, PiLp.single_apply, PiLp.single_apply]
  by_cases h : j = ρ i
  · rw [if_pos h]
    have h' : ρ.symm j = i := by rw [h, Equiv.symm_apply_apply]
    rw [if_pos h']
  · rw [if_neg h]
    have h' : ρ.symm j ≠ i := fun hh => h (by rw [← hh, Equiv.apply_symm_apply])
    rw [if_neg h']

lemma coordPerms_zero_zero : coordPerms 0 0 = 2 := by decide
lemma coordPerms_zero_one : coordPerms 0 1 = 3 := by decide
lemma coordPerms_one_zero : coordPerms 1 0 = 1 := by decide
lemma coordPerms_one_one : coordPerms 1 1 = 3 := by decide
lemma coordPerms_one_two : coordPerms 1 2 = 0 := by decide

/-- The shear fixes `e₀` (it moves only the coordinate `2` by a multiple of the coordinate `1`). -/
lemma linShear_linE0 (k : Fin 3) : linShear k linE0 = linE0 := by
  ext i
  fin_cases i <;> simp [linShearFun, linE0, linE2]

/-- The shear moves `e₁` to `e₁ + α_k e₂`. -/
lemma linShear_linE1 (k : Fin 3) : linShear k linE1 = linE1 + linAlpha k • linE2 := by
  ext i
  fin_cases i <;>
    simp [linShearFun, linE1, linE2, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]

/-- The shear at `k = 1` fixes `e₀` and sends `e₁` to `e₁ + e₂`. -/
lemma linShear_one_linE1 : linShear 1 linE1 = linE1 + linE2 := by
  rw [linShear_linE1, linAlpha_one, one_smul]

/-- The shear at `k = 0` is the identity on the plane `span {e₀, e₁}`. -/
lemma linShear_zero_linE1 : linShear 0 linE1 = linE1 := by
  rw [linShear_linE1, linAlpha_zero, zero_smul, add_zero]

/-! ## 3. The chart `linBase0` (the sheared family at `A = 1`) -/

/-- The sheared coordinate-permutation chart with the permutation applied last: `linBase 1 k`
definitionally, and the chart whose boundary line is computed below. -/
abbrev linBase0 (k : Fin 3) : Eucl 3 ≃L[ℝ] Eucl 3 :=
  (linShear k).trans (coordPermCLM (coordPerms k))

lemma linBase0_apply (k : Fin 3) (x : Eucl 3) :
    linBase0 k x = coordPermCLM (coordPerms k) (linShear k x) := rfl

lemma linBase0_zero_linE0 : linBase0 0 linE0 = linE2 := by
  rw [linBase0_apply, linShear_linE0, coordPermCLM_single, coordPerms_zero_zero]

lemma linBase0_zero_linE1 : linBase0 0 linE1 = linE3 := by
  rw [linBase0_apply, linShear_zero_linE1, coordPermCLM_single, coordPerms_zero_one]

lemma linBase0_one_linE0 : linBase0 1 linE0 = linE1 := by
  rw [linBase0_apply, linShear_linE0, coordPermCLM_single, coordPerms_one_zero]

lemma linBase0_one_linE1 : linBase0 1 linE1 = linE0 + linE3 := by
  have hinner : coordPermCLM (coordPerms 1) (linE1 + linE2) = linE0 + linE3 := by
    rw [map_add, coordPermCLM_single (coordPerms 1) 1, coordPermCLM_single (coordPerms 1) 2,
      coordPerms_one_one, coordPerms_one_two]
    rw [show (EuclideanSpace.single 3 (1 : ℝ) : Eucl 3) + EuclideanSpace.single 0 (1 : ℝ)
        = (EuclideanSpace.single 0 (1 : ℝ) : Eucl 3) + EuclideanSpace.single 3 (1 : ℝ)
        from add_comm _ _]
  rw [linBase0_apply, linShear_one_linE1, hinner]

/-! ## 4. Membership in the image of a submodule under a linear equivalence -/

lemma mem_map_toLinearMap (p : Submodule ℝ (Eucl 3)) (e : Eucl 3 ≃L[ℝ] Eucl 3) (v : Eucl 3) :
    v ∈ p.map e.toLinearEquiv.toLinearMap ↔ e.symm v ∈ p := by
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, hwv⟩
    have hwv' : e w = v := hwv
    rw [← hwv', ContinuousLinearEquiv.symm_apply_apply]
    exact hw
  · rintro hv
    exact ⟨e.symm v, hv, by simpa using e.apply_symm_apply v⟩

/-- The boundary line behaves like `linSub` under composition. -/
lemma linBdry_trans (e f : Eucl 3 ≃L[ℝ] Eucl 3) :
    linBdry (e.trans f) = (linBdry e).map f.toLinearEquiv.toLinearMap := by
  rw [linBdry, linBdry, ← Submodule.map_comp]
  rfl

/-! ## 5. The membership characterisations of the two charts -/

theorem mem_linSub_linBase_iff (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) (v : Eucl 3) :
    v ∈ linSub (linBase A k) ↔ (A.symm v) (coordPerms k 3) = 0 := by
  rw [linSub_linBase, linSub_trans, mem_map_toLinearMap, mem_linSub_coordPermCLM_iff]

theorem mem_linBdry_linBase_iff (A : Eucl 3 ≃L[ℝ] Eucl 3) (k : Fin 3) (v : Eucl 3) :
    v ∈ linBdry (linBase A k) ↔ A.symm v ∈ linBdry (linBase0 k) := by
  have hmap : linBdry (linBase A k) = (linBdry (linBase0 k)).map A.toLinearEquiv.toLinearMap := by
    have hbase : linBase A k = (linBase0 k).trans A := rfl
    rw [hbase]
    exact linBdry_trans (linBase0 k) A
  rw [hmap, mem_map_toLinearMap]

theorem mem_linSub_linBase_zero_iff (A : Eucl 3 ≃L[ℝ] Eucl 3) (v : Eucl 3) :
    v ∈ linSub (linBase A 0) ↔ (A.symm v) 1 = 0 := by
  rw [mem_linSub_linBase_iff, coordPerms_three_zero]

theorem mem_linSub_linBase_one_iff (A : Eucl 3 ≃L[ℝ] Eucl 3) (v : Eucl 3) :
    v ∈ linSub (linBase A 1) ↔ (A.symm v) 2 = 0 := by
  rw [mem_linSub_linBase_iff, coordPerms_three_one]

/-- **The boundary line of `linBase0 0` is `span {e₂, e₃}`.** -/
theorem mem_linBdry_linBase0_zero_iff (v : Eucl 3) :
    v ∈ linBdry (linBase0 0) ↔ v ∈ Submodule.span ℝ ({linE2, linE3} : Set (Eucl 3)) := by
  rw [linBdry, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, hwv⟩
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hw
    have hwv' : linBase0 0 w = v := hwv
    rw [Submodule.mem_span_pair]
    refine ⟨a, b, ?_⟩
    rw [← hwv', ← hab, map_add, map_smul, map_smul, linBase0_zero_linE0, linBase0_zero_linE1]
  · intro hv
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hv
    refine ⟨a • linE0 + b • linE1, Submodule.mem_span_pair.mpr ⟨a, b, rfl⟩, ?_⟩
    have hval : linBase0 0 (a • linE0 + b • linE1) = a • linE2 + b • linE3 := by
      rw [map_add, map_smul, map_smul, linBase0_zero_linE0, linBase0_zero_linE1]
    have hco : (linBase0 0).toLinearEquiv.toLinearMap (a • linE0 + b • linE1)
        = linBase0 0 (a • linE0 + b • linE1) := rfl
    rw [hco, hval, hab]

/-- **The boundary line of `linBase0 1` is `span {e₁, e₀ + e₃}`.** -/
theorem mem_linBdry_linBase0_one_iff (v : Eucl 3) :
    v ∈ linBdry (linBase0 1) ↔
      v ∈ Submodule.span ℝ ({linE1, linE0 + linE3} : Set (Eucl 3)) := by
  rw [linBdry, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, hwv⟩
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hw
    have hwv' : linBase0 1 w = v := hwv
    rw [Submodule.mem_span_pair]
    refine ⟨a, b, ?_⟩
    rw [← hwv', ← hab, map_add, map_smul, map_smul, linBase0_one_linE0, linBase0_one_linE1]
  · intro hv
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hv
    refine ⟨a • linE0 + b • linE1, Submodule.mem_span_pair.mpr ⟨a, b, rfl⟩, ?_⟩
    have hval : linBase0 1 (a • linE0 + b • linE1) = a • linE1 + b • (linE0 + linE3) := by
      rw [map_add, map_smul, map_smul, linBase0_one_linE0, linBase0_one_linE1]
    have hco : (linBase0 1).toLinearEquiv.toLinearMap (a • linE0 + b • linE1)
        = linBase0 1 (a • linE0 + b • linE1) := rfl
    rw [hco, hval, hab]

theorem mem_linBdry_linBase_zero_iff (A : Eucl 3 ≃L[ℝ] Eucl 3) (v : Eucl 3) :
    v ∈ linBdry (linBase A 0) ↔
      A.symm v ∈ Submodule.span ℝ ({linE2, linE3} : Set (Eucl 3)) := by
  rw [mem_linBdry_linBase_iff, mem_linBdry_linBase0_zero_iff]

theorem mem_linBdry_linBase_one_iff (A : Eucl 3 ≃L[ℝ] Eucl 3) (v : Eucl 3) :
    v ∈ linBdry (linBase A 1) ↔
      A.symm v ∈ Submodule.span ℝ ({linE1, linE0 + linE3} : Set (Eucl 3)) := by
  rw [mem_linBdry_linBase_iff, mem_linBdry_linBase0_one_iff]

/-! ## 6. The numerical facts about the two spans -/

/-- A linear functional vanishing on `s` and `t` vanishes on `span {s, t}`. -/
lemma eq_zero_of_mem_span_pair_of_linear {s t x : Eucl 3} (ℓ : Eucl 3 →ₗ[ℝ] ℝ)
    (hs : ℓ s = 0) (ht : ℓ t = 0) (h : x ∈ Submodule.span ℝ ({s, t} : Set (Eucl 3))) :
    ℓ x = 0 := by
  have hle : Submodule.span ℝ ({s, t} : Set (Eucl 3)) ≤ LinearMap.ker ℓ := by
    rw [Submodule.span_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl
    · exact LinearMap.mem_ker.mpr hs
    · exact LinearMap.mem_ker.mpr ht
  exact LinearMap.mem_ker.mp (hle h)

/-- A vector on which such a functional is nonzero does not lie in `span {s, t}`. -/
lemma notMem_span_pair_of_linear {s t x : Eucl 3} (ℓ : Eucl 3 →ₗ[ℝ] ℝ)
    (hs : ℓ s = 0) (ht : ℓ t = 0) (hx : ℓ x ≠ 0) :
    x ∉ Submodule.span ℝ ({s, t} : Set (Eucl 3)) :=
  fun h => hx (eq_zero_of_mem_span_pair_of_linear ℓ hs ht h)

lemma coordFun_two_linE1 : coordFun 2 linE1 = 0 := by simp [coordFun, linE1]
lemma coordFun_two_e0_add_e3 : coordFun 2 (linE0 + linE3) = 0 := by
  simp [coordFun, linE0, linE3]
lemma coordFun_two_linE2 : coordFun 2 linE2 = 1 := by simp [coordFun, linE2]
lemma coordFun_two_linE3 : coordFun 2 linE3 = 0 := by simp [coordFun, linE3]
lemma coordFun_one_linE2 : coordFun 1 linE2 = 0 := by simp [coordFun, linE2]
lemma coordFun_one_linE3 : coordFun 1 linE3 = 0 := by simp [coordFun, linE3]
lemma coordFun_one_linE1 : coordFun 1 linE1 = 1 := by simp [coordFun, linE1]
lemma coordFun_zero_sub_three_linE1 : (coordFun 0 - coordFun 3) linE1 = 0 := by
  simp [coordFun, linE1]
lemma coordFun_zero_sub_three_e0_add_e3 : (coordFun 0 - coordFun 3) (linE0 + linE3) = 0 := by
  simp [coordFun, linE0, linE3]
lemma coordFun_zero_sub_three_linE3 : (coordFun 0 - coordFun 3) linE3 = -1 := by
  simp [coordFun, linE3]

/-- **The two boundary lines of `linBase0 0` and `linBase0 1` meet only in `0`.** -/
theorem inf_span_e23_span_e1_e03_eq_bot :
    (Submodule.span ℝ ({linE2, linE3} : Set (Eucl 3))) ⊓
      (Submodule.span ℝ ({linE1, linE0 + linE3} : Set (Eucl 3))) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨hvL, hvR⟩ := hv
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hvL
  have h2 : coordFun 2 v = 0 :=
    eq_zero_of_mem_span_pair_of_linear (coordFun 2) coordFun_two_linE1 coordFun_two_e0_add_e3 hvR
  have hval : coordFun 2 v = a := by
    rw [← hab, map_add, map_smul, map_smul, coordFun_two_linE2, coordFun_two_linE3]
    simp
  have ha : a = 0 := by rw [← hval]; exact h2
  have hv3 : v = b • linE3 := by rw [← hab, ha, zero_smul, zero_add]
  have h30 : (coordFun 0 - coordFun 3) v = 0 :=
    eq_zero_of_mem_span_pair_of_linear (coordFun 0 - coordFun 3)
      coordFun_zero_sub_three_linE1 coordFun_zero_sub_three_e0_add_e3 hvR
  have hb : b = 0 := by
    rw [hv3, map_smul, coordFun_zero_sub_three_linE3] at h30
    simpa using h30
  rw [hv3, hb, zero_smul]

/-- `e₂` is not in the second boundary line. -/
theorem notMem_linE2_span_e1_e03 :
    linE2 ∉ Submodule.span ℝ ({linE1, linE0 + linE3} : Set (Eucl 3)) :=
  notMem_span_pair_of_linear (coordFun 2) coordFun_two_linE1 coordFun_two_e0_add_e3 (by
    rw [coordFun_two_linE2]; exact one_ne_zero)

/-- `e₁` is not in the first boundary line. -/
theorem notMem_linE1_span_e23 :
    linE1 ∉ Submodule.span ℝ ({linE2, linE3} : Set (Eucl 3)) :=
  notMem_span_pair_of_linear (coordFun 1) coordFun_one_linE2 coordFun_one_linE3 (by
    rw [coordFun_one_linE1]; exact one_ne_zero)

/-! ## 7. The two corner evaluations -/

lemma linBase_zero_add_smul (A : Eucl 3 ≃L[ℝ] Eucl 3) (s : ℝ) :
    linBase A 0 (linE0 + s • linE1) = A (linE2 + s • linE3) := by
  have hS : linShear 0 (linE0 + s • linE1) = linE0 + s • linE1 := by
    rw [map_add, map_smul, linShear_linE0, linShear_zero_linE1]
  have hinner : coordPermCLM (coordPerms 0) (linE0 + s • linE1) = linE2 + s • linE3 := by
    rw [map_add, map_smul, coordPermCLM_single (coordPerms 0) 0,
      coordPermCLM_single (coordPerms 0) 1, coordPerms_zero_zero, coordPerms_zero_one]
  rw [linBase_apply, hS, hinner]

lemma linBase_one_add_smul (A : Eucl 3 ≃L[ℝ] Eucl 3) (s : ℝ) :
    linBase A 1 (linE0 + s • linE1) = A (linE1 + s • (linE0 + linE3)) := by
  have hS : linShear 1 (linE0 + s • linE1) = linE0 + s • (linE1 + linE2) := by
    rw [map_add, map_smul, linShear_linE0, linShear_one_linE1]
  have hinner : coordPermCLM (coordPerms 1) (linE0 + s • (linE1 + linE2))
      = linE1 + s • (linE0 + linE3) := by
    rw [map_add, map_smul, coordPermCLM_single (coordPerms 1) 0]
    rw [map_add, coordPermCLM_single (coordPerms 1) 1, coordPermCLM_single (coordPerms 1) 2,
      coordPerms_one_zero, coordPerms_one_one, coordPerms_one_two]
    rw [show (EuclideanSpace.single 3 (1 : ℝ) : Eucl 3) + EuclideanSpace.single 0 (1 : ℝ)
        = (EuclideanSpace.single 0 (1 : ℝ) : Eucl 3) + EuclideanSpace.single 3 (1 : ℝ)
        from add_comm _ _]
  rw [linBase_apply, hS, hinner]

/-! ## 8. The incidence bundle -/

/-- **The incidence data of the sheared linear charts.**  All six conditions of the pair-row criterion
`Work.Drive.pairReg_linPlaneCharts_of_incidence` hold for the two charts `linBase A 0` and
`linBase A 1`, for **every** `A`. -/
theorem linIncidence_linBase (A : Eucl 3 ≃L[ℝ] Eucl 3) :
    linBdry (linBase A 0) ⊓ linBdry (linBase A 1) = ⊥ ∧
    ¬ linBdry (linBase A 0) ≤ linSub (linBase A 1) ∧
    ¬ linBdry (linBase A 1) ≤ linSub (linBase A 0) ∧
    (∀ s : ℝ, (s = 1 ∨ s = -1) →
      linBase A 0 (linE0 + s • linE1) ∉ linSub (linBase A 1)) ∧
    (∀ s : ℝ, (s = 1 ∨ s = -1) →
      linBase A 1 (linE0 + s • linE1) ∉ linSub (linBase A 0)) ∧
    linSub (linBase A 0) ≠ linSub (linBase A 1) := by
  have hsym : ∀ v : Eucl 3, A.symm (A v) = v := fun v => A.symm_apply_apply v
  have hmem2 : A linE2 ∈ linBdry (linBase A 0) :=
    (mem_linBdry_linBase_zero_iff A (A linE2)).mpr (by
      rw [hsym]; exact Submodule.subset_span (by simp))
  have hmem1 : A linE1 ∈ linBdry (linBase A 1) :=
    (mem_linBdry_linBase_one_iff A (A linE1)).mpr (by
      rw [hsym]; exact Submodule.subset_span (by simp))
  have hsub0 : A linE2 ∈ linSub (linBase A 0) :=
    (mem_linSub_linBase_zero_iff A (A linE2)).mpr (by rw [hsym]; simp [linE2])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hv1, hv2⟩ := hv
    rw [mem_linBdry_linBase_zero_iff] at hv1
    rw [mem_linBdry_linBase_one_iff] at hv2
    have hu : A.symm v = 0 :=
      (Submodule.eq_bot_iff _).mp inf_span_e23_span_e1_e03_eq_bot (A.symm v)
        (Submodule.mem_inf.mpr ⟨hv1, hv2⟩)
    have hv0 : v = 0 := by rw [← A.apply_symm_apply v, hu, map_zero]
    exact hv0
  · intro hle
    have h1 : (A.symm (A linE2)) 2 = 0 :=
      (mem_linSub_linBase_one_iff A (A linE2)).mp (hle hmem2)
    rw [hsym] at h1
    have h2 : (1 : ℝ) = 0 := by simpa [linE2] using h1
    exact one_ne_zero h2
  · intro hle
    have h1 : (A.symm (A linE1)) 1 = 0 :=
      (mem_linSub_linBase_zero_iff A (A linE1)).mp (hle hmem1)
    rw [hsym] at h1
    have h2 : (1 : ℝ) = 0 := by simpa [linE1] using h1
    exact one_ne_zero h2
  · intro s _ hmem
    have h1 : (A.symm (linBase A 0 (linE0 + s • linE1))) 2 = 0 :=
      (mem_linSub_linBase_one_iff A _).mp hmem
    rw [linBase_zero_add_smul, hsym] at h1
    have h2 : (1 : ℝ) = 0 := by simpa [linE2, linE3] using h1
    exact one_ne_zero h2
  · intro s _ hmem
    have h1 : (A.symm (linBase A 1 (linE0 + s • linE1))) 1 = 0 :=
      (mem_linSub_linBase_zero_iff A _).mp hmem
    rw [linBase_one_add_smul, hsym] at h1
    have h2 : (1 : ℝ) = 0 := by simpa [linE1, linE0, linE3] using h1
    exact one_ne_zero h2
  · intro h
    have h1 : (A.symm (A linE2)) 2 = 0 :=
      (mem_linSub_linBase_one_iff A (A linE2)).mp (h ▸ hsub0)
    rw [hsym] at h1
    have h2 : (1 : ℝ) = 0 := by simpa [linE2] using h1
    exact one_ne_zero h2


/-! ## 9. The second pair row: the charts `linBase A 0` and `linBase A 2`

The row `Work.Drive.hpairL0P2` of `hasClassLinearization_of_endData` pairs the *first* linear chart with
the *third* (the reference plane's chart): at `t = 0` the perturbed block `2` is the linear chart
`refPlanePres φ lam hlam = diskPlane (linPlaneChart (φ 2) lam hlam)`, so the row is the pair `(0,2)` of
the sheared family.  Its incidence data is computed here; the pair `(1,2)` (which shares the vector `e₁`
between its two boundary lines, so that `hl` fails) is the only pair that never occurs.
-/

lemma coordPerms_two_zero : coordPerms 2 0 = 1 := by decide
lemma coordPerms_two_one : coordPerms 2 1 = 2 := by decide
lemma coordPerms_two_two : coordPerms 2 2 = 0 := by decide

/-- The shear at `k = 2` also sends `e₁` to `e₁ + e₂`. -/
lemma linShear_two_linE1 : linShear 2 linE1 = linE1 + linE2 := by
  rw [linShear_linE1, linAlpha_two, one_smul]

lemma linBase0_two_linE0 : linBase0 2 linE0 = linE1 := by
  rw [linBase0_apply, linShear_linE0, coordPermCLM_single, coordPerms_two_zero]

lemma linBase0_two_linE1 : linBase0 2 linE1 = linE0 + linE2 := by
  have hinner : coordPermCLM (coordPerms 2) (linE1 + linE2) = linE0 + linE2 := by
    rw [map_add, coordPermCLM_single (coordPerms 2) 1, coordPermCLM_single (coordPerms 2) 2,
      coordPerms_two_one, coordPerms_two_two]
    rw [show (EuclideanSpace.single 2 (1 : ℝ) : Eucl 3) + EuclideanSpace.single 0 (1 : ℝ)
        = (EuclideanSpace.single 0 (1 : ℝ) : Eucl 3) + EuclideanSpace.single 2 (1 : ℝ)
        from add_comm _ _]
  rw [linBase0_apply, linShear_two_linE1, hinner]

theorem mem_linSub_linBase_two_iff (A : Eucl 3 ≃L[ℝ] Eucl 3) (v : Eucl 3) :
    v ∈ linSub (linBase A 2) ↔ (A.symm v) 3 = 0 := by
  rw [mem_linSub_linBase_iff, coordPerms_three_two]

/-- **The boundary line of `linBase0 2` is `span {e₁, e₀ + e₂}`.** -/
theorem mem_linBdry_linBase0_two_iff (v : Eucl 3) :
    v ∈ linBdry (linBase0 2) ↔
      v ∈ Submodule.span ℝ ({linE1, linE0 + linE2} : Set (Eucl 3)) := by
  rw [linBdry, Submodule.mem_map]
  constructor
  · rintro ⟨w, hw, hwv⟩
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hw
    have hwv' : linBase0 2 w = v := hwv
    rw [Submodule.mem_span_pair]
    refine ⟨a, b, ?_⟩
    rw [← hwv', ← hab, map_add, map_smul, map_smul, linBase0_two_linE0, linBase0_two_linE1]
  · intro hv
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hv
    refine ⟨a • linE0 + b • linE1, Submodule.mem_span_pair.mpr ⟨a, b, rfl⟩, ?_⟩
    have hval : linBase0 2 (a • linE0 + b • linE1) = a • linE1 + b • (linE0 + linE2) := by
      rw [map_add, map_smul, map_smul, linBase0_two_linE0, linBase0_two_linE1]
    have hco : (linBase0 2).toLinearEquiv.toLinearMap (a • linE0 + b • linE1)
        = linBase0 2 (a • linE0 + b • linE1) := rfl
    rw [hco, hval, hab]

theorem mem_linBdry_linBase_two_iff (A : Eucl 3 ≃L[ℝ] Eucl 3) (v : Eucl 3) :
    v ∈ linBdry (linBase A 2) ↔
      A.symm v ∈ Submodule.span ℝ ({linE1, linE0 + linE2} : Set (Eucl 3)) := by
  rw [mem_linBdry_linBase_iff, mem_linBdry_linBase0_two_iff]

lemma coordFun_zero_linE2 : coordFun 0 linE2 = 0 := by simp [coordFun, linE2]
lemma coordFun_zero_linE3 : coordFun 0 linE3 = 0 := by simp [coordFun, linE3]
lemma coordFun_three_linE2 : coordFun 3 linE2 = 0 := by simp [coordFun, linE2]
lemma coordFun_three_linE3 : coordFun 3 linE3 = 1 := by simp [coordFun, linE3]
lemma coordFun_zero_sub_two_linE1 : (coordFun 0 - coordFun 2) linE1 = 0 := by
  simp [coordFun, linE1]
lemma coordFun_zero_sub_two_e0_add_e2 : (coordFun 0 - coordFun 2) (linE0 + linE2) = 0 := by
  simp [coordFun, linE0, linE2]
lemma coordFun_zero_sub_two_linE2 : (coordFun 0 - coordFun 2) linE2 = -1 := by
  simp [coordFun, linE2]
lemma coordFun_zero_sub_two_linE3 : (coordFun 0 - coordFun 2) linE3 = 0 := by
  simp [coordFun, linE3]
lemma coordFun_three_linE1' : coordFun 3 linE1 = 0 := by simp [coordFun, linE1]
lemma coordFun_three_e0_add_e2 : coordFun 3 (linE0 + linE2) = 0 := by
  simp [coordFun, linE0, linE2]

/-- **The boundary lines of `linBase0 0` and `linBase0 2` meet only in `0`.** -/
theorem inf_span_e23_span_e1_e02_eq_bot :
    (Submodule.span ℝ ({linE2, linE3} : Set (Eucl 3))) ⊓
      (Submodule.span ℝ ({linE1, linE0 + linE2} : Set (Eucl 3))) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨hvL, hvR⟩ := hv
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hvL
  have h2 : (coordFun 0 - coordFun 2) v = 0 :=
    eq_zero_of_mem_span_pair_of_linear (coordFun 0 - coordFun 2)
      coordFun_zero_sub_two_linE1 coordFun_zero_sub_two_e0_add_e2 hvR
  have hval : (coordFun 0 - coordFun 2) v = -a := by
    rw [← hab, map_add, map_smul, map_smul, coordFun_zero_sub_two_linE2,
      coordFun_zero_sub_two_linE3]
    simp
  have ha : a = 0 := by
    have : -a = 0 := by rw [← hval]; exact h2
    linarith
  have hv3 : v = b • linE3 := by rw [← hab, ha, zero_smul, zero_add]
  have h30 : coordFun 3 v = 0 :=
    eq_zero_of_mem_span_pair_of_linear (coordFun 3)
      coordFun_three_linE1' coordFun_three_e0_add_e2 hvR
  have hb : b = 0 := by
    rw [hv3, map_smul, coordFun_three_linE3] at h30
    simpa [smul_eq_mul] using h30
  rw [hv3, hb, zero_smul]

lemma linBase_two_add_smul (A : Eucl 3 ≃L[ℝ] Eucl 3) (s : ℝ) :
    linBase A 2 (linE0 + s • linE1) = A (linE1 + s • (linE0 + linE2)) := by
  have hS : linShear 2 (linE0 + s • linE1) = linE0 + s • (linE1 + linE2) := by
    rw [map_add, map_smul, linShear_linE0, linShear_two_linE1]
  have hinner : coordPermCLM (coordPerms 2) (linE0 + s • (linE1 + linE2))
      = linE1 + s • (linE0 + linE2) := by
    rw [map_add, map_smul, coordPermCLM_single (coordPerms 2) 0]
    rw [map_add, coordPermCLM_single (coordPerms 2) 1, coordPermCLM_single (coordPerms 2) 2,
      coordPerms_two_zero, coordPerms_two_one, coordPerms_two_two]
    rw [show (EuclideanSpace.single 2 (1 : ℝ) : Eucl 3) + EuclideanSpace.single 0 (1 : ℝ)
        = (EuclideanSpace.single 0 (1 : ℝ) : Eucl 3) + EuclideanSpace.single 2 (1 : ℝ)
        from add_comm _ _]
  rw [linBase_apply, hS, hinner]

/-- **The incidence data of the pair `(0, 2)` of the sheared linear charts**: the same six
conditions, for every `A`. -/
theorem linIncidence_linBase_02 (A : Eucl 3 ≃L[ℝ] Eucl 3) :
    linBdry (linBase A 0) ⊓ linBdry (linBase A 2) = ⊥ ∧
    ¬ linBdry (linBase A 0) ≤ linSub (linBase A 2) ∧
    ¬ linBdry (linBase A 2) ≤ linSub (linBase A 0) ∧
    (∀ s : ℝ, (s = 1 ∨ s = -1) →
      linBase A 0 (linE0 + s • linE1) ∉ linSub (linBase A 2)) ∧
    (∀ s : ℝ, (s = 1 ∨ s = -1) →
      linBase A 2 (linE0 + s • linE1) ∉ linSub (linBase A 0)) ∧
    linSub (linBase A 0) ≠ linSub (linBase A 2) := by
  have hsym : ∀ v : Eucl 3, A.symm (A v) = v := fun v => A.symm_apply_apply v
  have hmem3 : A linE3 ∈ linBdry (linBase A 0) :=
    (mem_linBdry_linBase_zero_iff A (A linE3)).mpr (by
      rw [hsym]; exact Submodule.subset_span (by simp))
  have hmem1 : A linE1 ∈ linBdry (linBase A 2) :=
    (mem_linBdry_linBase_two_iff A (A linE1)).mpr (by
      rw [hsym]; exact Submodule.subset_span (by simp))
  have hne3 : A linE3 ∉ linSub (linBase A 2) := by
    intro h
    have h1 : (A.symm (A linE3)) 3 = 0 := (mem_linSub_linBase_two_iff A (A linE3)).mp h
    rw [hsym] at h1
    have h2 : (1 : ℝ) = 0 := by simpa [linE3] using h1
    exact one_ne_zero h2
  have hsub3 : A linE3 ∈ linSub (linBase A 0) :=
    (mem_linSub_linBase_zero_iff A (A linE3)).mpr (by rw [hsym]; simp [linE3])
  have hne1 : A linE1 ∉ linSub (linBase A 0) := by
    intro h
    have h1 : (A.symm (A linE1)) 1 = 0 := (mem_linSub_linBase_zero_iff A (A linE1)).mp h
    rw [hsym] at h1
    have h2 : (1 : ℝ) = 0 := by simpa [linE1] using h1
    exact one_ne_zero h2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hv1, hv2⟩ := hv
    rw [mem_linBdry_linBase_zero_iff] at hv1
    rw [mem_linBdry_linBase_two_iff] at hv2
    have hu : A.symm v = 0 :=
      (Submodule.eq_bot_iff _).mp inf_span_e23_span_e1_e02_eq_bot (A.symm v)
        (Submodule.mem_inf.mpr ⟨hv1, hv2⟩)
    have hv0 : v = 0 := by rw [← A.apply_symm_apply v, hu, map_zero]
    exact hv0
  · intro hle
    exact hne3 (hle hmem3)
  · intro hle
    exact hne1 (hle hmem1)
  · intro s hs hmem
    have h1 : (A.symm (linBase A 0 (linE0 + s • linE1))) 3 = 0 :=
      (mem_linSub_linBase_two_iff A _).mp hmem
    rw [linBase_zero_add_smul, hsym] at h1
    have h2 : s = 0 := by simpa [linE2, linE3, smul_eq_mul] using h1
    rcases hs with rfl | rfl
    · exact one_ne_zero h2
    · norm_num at h2
  · intro s _ hmem
    have h1 : (A.symm (linBase A 2 (linE0 + s • linE1))) 1 = 0 :=
      (mem_linSub_linBase_zero_iff A _).mp hmem
    rw [linBase_two_add_smul, hsym] at h1
    have h2 : (1 : ℝ) = 0 := by simpa [linE1, linE0, linE2] using h1
    exact one_ne_zero h2
  · intro h
    exact hne3 (h ▸ hsub3)
end

end Work.Drive
