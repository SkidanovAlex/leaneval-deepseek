import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.sigPos_toQuadraticForm_eq_card_pos_roots
import Submission.Commons.LinearAlgebra.Matrix.strictQuad_perron_vector
import Submission.Commons.LinearAlgebra.Matrix.posDef_perron_decomp

noncomputable section
open Matrix Polynomial Set Topology Filter
open scoped BigOperators

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedTactic false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Commons.LinearAlgebra.Matrix

/-- The set of strictly Lorentzian quadric matrices: symmetric, positive entries, invertible,
whose characteristic polynomial has exactly one positive root (counting multiplicity). -/
def strictQuadSet (n : ℕ) : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {A | A.IsSymm ∧ (∀ i j, 0 < A i j) ∧ IsUnit A ∧
    (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 1}

lemma in_strictQuadSet_iff_sigPos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A ∈ strictQuadSet n ↔
      A.IsSymm ∧ (∀ i j, 0 < A i j) ∧ IsUnit A ∧
        QuadraticForm.sigPos A.toQuadraticForm' = 1 := by
  classical
  unfold strictQuadSet
  constructor
  · rintro ⟨hA, hpos, hunit, hcard⟩
    exact ⟨hA, hpos, hunit, by
      rw [sigPos_toQuadraticForm_eq_card_pos_roots A hA]
      exact hcard⟩
  · rintro ⟨hA, hpos, hunit, hsig⟩
    exact ⟨hA, hpos, hunit, by
      rw [← sigPos_toQuadraticForm_eq_card_pos_roots A hA]
      exact hsig⟩

theorem sigPos_eq_one_of_pos_u_nonpos_uorth {n : ℕ} (hn : 0 < n)
    (Q : QuadraticForm ℝ (Fin n → ℝ)) (u : Fin n → ℝ)
    (hQpos : 0 < Q u)
    (hQnonpos : ∀ x : Fin n → ℝ, (∑ i : Fin n, u i * x i) = 0 → Q x ≤ 0) :
    QuadraticForm.sigPos Q = 1 := by
  classical
  have hu_ne : u ≠ 0 := by
    intro hu0
    have : Q u = 0 := by simp [hu0]
    linarith
  have hQspan_pos : (QuadraticMap.restrict Q (ℝ ∙ u)).PosDef := by
    intro v hv
    have hv_mem : (v : Fin n → ℝ) ∈ ℝ ∙ u := v.property
    rcases (Submodule.mem_span_singleton.mp hv_mem) with ⟨c, hc⟩
    have hc_ne : c ≠ 0 := by
      intro hc0
      apply hv
      apply Subtype.ext
      simpa [hc0] using hc.symm
    have hQc : Q (v : Fin n → ℝ) = (c * c) * Q u := by
      rw [← hc]
      simpa [mul_assoc] using (QuadraticMap.map_smul Q c u)
    have hc2 : 0 < c * c := mul_self_pos.mpr hc_ne
    have : 0 < (c * c) * Q u := mul_pos hc2 hQpos
    simpa [hQc] using this
  have hge : 1 ≤ QuadraticForm.sigPos Q := by
    have hnonzero : Nontrivial ↥(ℝ ∙ u) := by
      refine ⟨⟨u, Submodule.mem_span_singleton.mpr ⟨1, by simp⟩⟩, 0, ?_⟩
      intro h
      apply hu_ne
      exact congrArg Subtype.val h
    have hpos : 0 < Module.finrank ℝ ↥(ℝ ∙ u) := Module.finrank_pos_iff.mpr hnonzero
    have hle := le_sigPos_of_posDef Q (V := ℝ ∙ u) hQspan_pos
    exact (Nat.succ_le_of_lt hpos).trans hle
  let φ : (Fin n → ℝ) →ₗ[ℝ] ℝ := {
    toFun := fun x => ∑ i : Fin n, u i * x i
    map_add' := by
      intro x y
      simp [Finset.sum_add_distrib, mul_add]
    map_smul' := by
      intro a x
      simp [Finset.mul_sum, mul_left_comm, mul_comm]
  }
  have hVnonpos : ∀ x ∈ φ.ker, Q x ≤ 0 := by
    intro x hx
    have hφ0 : φ x = 0 := (LinearMap.mem_ker.mp hx)
    have horth : (∑ i : Fin n, u i * x i) = 0 := by simpa [φ] using hφ0
    exact hQnonpos x horth
  have hsurj : Function.Surjective φ := by
    intro y
    have hnorm2 : 0 < ∑ i : Fin n, u i * u i := by
      have hne : ∑ i : Fin n, u i ^ 2 ≠ 0 := by
        intro hz
        apply hu_ne
        funext i
        have hterm : u i ^ 2 = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg (f := fun i => u i ^ 2) (fun i hi => sq_nonneg (u i))).mp hz i (Finset.mem_univ i)
        exact sq_eq_zero_iff.mp hterm
      have hnonneg : 0 ≤ ∑ i : Fin n, u i * u i :=
        Finset.sum_nonneg (fun i hi => mul_self_nonneg (u i))
      exact lt_of_le_of_ne hnonneg (Ne.symm (by simpa [pow_two] using hne))
    let den : ℝ := ∑ i : Fin n, u i * u i
    have hden_ne : den ≠ 0 := ne_of_gt hnorm2
    refine ⟨(y / den) • u, ?_⟩
    change (∑ i : Fin n, u i * ((y / den) • u) i) = y
    calc
      (∑ i : Fin n, u i * ((y / den) • u) i) = (y / den) * (∑ i : Fin n, u i * u i) := by
        simp
        rw [Finset.mul_sum]
        congr 1 with i
        ring
      _ = y := by
        exact div_mul_cancel₀ y hden_ne
  have hrange_top : φ.range = ⊤ := (LinearMap.range_eq_top.mpr hsurj)
  have hfin_ker : Module.finrank ℝ ↥φ.ker = n - 1 := by
    have hfinrange : Module.finrank ℝ ↥φ.range = 1 := by
      rw [hrange_top]
      simp
    have htotal := LinearMap.finrank_range_add_finrank_ker (f := φ)
    rw [Module.finrank_fin_fun ℝ] at htotal
    omega
  have hle1 := QuadraticForm.sigPos_add_finrank_le_of_nonpos (Q := Q) (V := φ.ker) hVnonpos
  rw [Module.finrank_fin_fun ℝ] at hle1
  have hle : QuadraticForm.sigPos Q ≤ 1 := by
    rw [hfin_ker] at hle1
    have hsub : QuadraticForm.sigPos Q ≤ n - (n - 1) := by
      exact Nat.le_sub_of_add_le hle1
    have hid : n - (n - 1) = 1 := by omega
    simpa [hid] using hsub
  exact le_antisymm hle hge

lemma toQuadraticForm'_apply_dot {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    A.toQuadraticForm' x = x ⬝ᵥ A.mulVec x := by
  simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply']


lemma outer_mulVec {n : ℕ} (u x : Fin n → ℝ) :
    (Matrix.vecMulVec u u).mulVec x = (u ⬝ᵥ x) • u := by
  rw [Matrix.vecMulVec_mulVec]
  simp

lemma dot_rankOne_sub_smul {n : ℕ} (u x : Fin n → ℝ) (α β : ℝ) :
    x ⬝ᵥ ((α • Matrix.vecMulVec u u - β • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec x) =
      α * (x ⬝ᵥ u)^2 - β * (x ⬝ᵥ x) := by
  classical
  calc
    x ⬝ᵥ ((α • Matrix.vecMulVec u u - β • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec x)
        = x ⬝ᵥ (α • (Matrix.vecMulVec u u).mulVec x - β • x) := by
          rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    _ = α • (x ⬝ᵥ (Matrix.vecMulVec u u).mulVec x) - β • (x ⬝ᵥ x) := by
          simp [dotProduct_sub, dotProduct_smul]
    _ = α • (x ⬝ᵥ ((u ⬝ᵥ x) • u)) - β • (x ⬝ᵥ x) := by
          rw [outer_mulVec]
    _ = α * ((u ⬝ᵥ x) * (x ⬝ᵥ u)) - β * (x ⬝ᵥ x) := by
          simp [dotProduct_smul, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
    _ = α * (x ⬝ᵥ u)^2 - β * (x ⬝ᵥ x) := by
          rw [dotProduct_comm]
          congr 1
          ring

lemma isUnit_of_mulVec_eq_zero_of_eq_zero {n : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ)
    (hker : ∀ z : Fin n → ℝ, A.mulVec z = 0 → z = 0) : IsUnit A := by
  classical
  have hinj : Function.Injective A.mulVec := by
    intro x y hxy
    have hz : A.mulVec (x - y) = 0 := by
      rw [Matrix.mulVec_sub, hxy, sub_self]
    have hxy0 : x - y = 0 := hker (x - y) hz
    funext i
    have hi : x i - y i = 0 := by simpa using congrFun hxy0 i
    linarith
  exact Matrix.mulVec_injective_iff_isUnit.1 hinj

theorem strictQuad_pencil_mem {n : ℕ} (hn : 0 < n)
    (u : Fin n → ℝ) (α β : ℝ)
    (hu_pos : ∀ i : Fin n, 0 < u i)
    (hu_unit : (∑ i : Fin n, u i * u i) = 1)
    (hα : 0 < α) (hβpos : 0 < β) (hαβ : β < α)
    (hβlt : ∀ i : Fin n, β < α * (u i)^2) :
    let P : Matrix (Fin n) (Fin n) ℝ := α • Matrix.vecMulVec u u - β • 1
    P.IsSymm ∧ (∀ i j : Fin n, 0 < P i j) ∧ IsUnit P ∧
      ((P.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 1) := by
  classical
  intro P
  have hsymm : P.IsSymm := by
    change ((α • Matrix.vecMulVec u u - β • (1 : Matrix (Fin n) (Fin n) ℝ)).IsSymm)
    rw [Matrix.IsSymm.ext_iff]
    intro i j
    by_cases hij : i = j
    · subst j
      simp
    · have hji : ¬ j = i := by intro h; exact hij h.symm
      simp [hij, hji, Matrix.vecMulVec_apply, mul_comm, mul_left_comm, mul_assoc]
  have hpos_entries : ∀ i j : Fin n, 0 < P i j := by
    intro i j
    change 0 < (α • Matrix.vecMulVec u u - β • (1 : Matrix (Fin n) (Fin n) ℝ)) i j
    by_cases hij : i = j
    · subst j
      change 0 < (α • Matrix.vecMulVec u u - β • (1 : Matrix (Fin n) (Fin n) ℝ)) i i
      rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.one_apply]
      simp
      have hlt : β < α * (u i * u i) := by simpa [pow_two] using hβlt i
      linarith
    · change 0 < (α • Matrix.vecMulVec u u - β • (1 : Matrix (Fin n) (Fin n) ℝ)) i j
      rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.one_apply, if_neg hij]
      simp
      exact mul_pos hα (mul_pos (hu_pos i) (hu_pos j))
  have hPu : P.mulVec u = (α - β) • u := by
    change ((α • Matrix.vecMulVec u u - β • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec u = (α - β) • u)
    calc
      (α • Matrix.vecMulVec u u - β • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec u
          = α • ((u ⬝ᵥ u) • u) - β • u := by
            rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, outer_mulVec]
      _ = (α * (u ⬝ᵥ u) - β) • u := by
            rw [smul_smul, ← sub_smul]
      _ = (α - β) • u := by
            have huu : u ⬝ᵥ u = 1 := by simpa [dotProduct] using hu_unit
            simp [huu]
  have hunit : IsUnit P := by
    refine isUnit_of_mulVec_eq_zero_of_eq_zero P ?_
    intro x hx0
    have hxu0 : x ⬝ᵥ u = 0 := by
      have h1 : u ⬝ᵥ P.mulVec x = 0 := by rw [hx0]; simp
      have h2 : x ⬝ᵥ P.mulVec u = u ⬝ᵥ P.mulVec x := dotProduct_mulVec_symm_eq P hsymm x u
      have h4 : x ⬝ᵥ P.mulVec u = 0 := by rw [h2, h1]
      have h5 : x ⬝ᵥ ((α - β) • u) = 0 := by simpa [hPu] using h4
      have hαβ_ne : α - β ≠ 0 := sub_ne_zero.mpr (ne_of_gt hαβ)
      have hmain : (α - β) * (x ⬝ᵥ u) = 0 := by
        simpa [smul_eq_mul] using (by
          have h6 : x ⬝ᵥ ((α - β) • u) = (α - β) • (x ⬝ᵥ u) := dotProduct_smul (α - β) x u
          simpa [h6] using h5)
      exact (mul_eq_zero.mp hmain).resolve_left hαβ_ne
    have hxP : x ⬝ᵥ P.mulVec x = 0 := by rw [hx0]; simp
    have hquad : x ⬝ᵥ P.mulVec x = α * (x ⬝ᵥ u)^2 - β * (x ⬝ᵥ x) := by
      change x ⬝ᵥ ((α • Matrix.vecMulVec u u - β • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec x) =
        α * (x ⬝ᵥ u)^2 - β * (x ⬝ᵥ x)
      exact dot_rankOne_sub_smul u x α β
    have h0 : α * (x ⬝ᵥ u)^2 - β * (x ⬝ᵥ x) = 0 := by
      rw [← hquad]
      exact hxP
    have hxx : x ⬝ᵥ x = 0 := by
      have hb : -β * (x ⬝ᵥ x) = 0 := by
        simpa [hxu0] using h0
      have hb'' : -(β * (x ⬝ᵥ x)) = 0 := by simpa [neg_mul] using hb
      have hb' : β * (x ⬝ᵥ x) = 0 := neg_eq_zero.mp hb''
      exact (mul_eq_zero.mp hb').resolve_left (ne_of_gt hβpos)
    funext i
    have hxx_sum : (∑ j : Fin n, x j * x j) = 0 := by simpa [dotProduct] using hxx
    have hterm : x i * x i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (f := fun j : Fin n => x j * x j)
        (fun j hj => mul_self_nonneg (x j))).mp hxx_sum i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp hterm
  have hQpos : 0 < P.toQuadraticForm' u := by
    rw [toQuadraticForm'_apply_dot P u]
    have hq := dot_rankOne_sub_smul u u α β
    have huu : u ⬝ᵥ u = 1 := by simpa [dotProduct] using hu_unit
    rw [hq, huu]
    norm_num
    linarith
  have hQnonpos : ∀ x : Fin n → ℝ, (∑ i : Fin n, u i * x i) = 0 → P.toQuadraticForm' x ≤ 0 := by
    intro x hx
    have hxdot : x ⬝ᵥ u = 0 := by
      simpa [dotProduct, mul_comm] using hx
    rw [toQuadraticForm'_apply_dot P x]
    have hq := dot_rankOne_sub_smul u x α β
    rw [hq, hxdot]
    have hxx_nonneg : 0 ≤ x ⬝ᵥ x := by
      simpa [dotProduct] using (Finset.sum_nonneg (fun j hj => mul_self_nonneg (x j)))
    norm_num
    nlinarith
  have hsig : QuadraticForm.sigPos P.toQuadraticForm' = 1 :=
    sigPos_eq_one_of_pos_u_nonpos_uorth hn P.toQuadraticForm' u hQpos hQnonpos
  have hcard : (P.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 1 := by
    rw [← sigPos_toQuadraticForm_eq_card_pos_roots P hsymm]
    exact hsig
  exact ⟨hsymm, hpos_entries, hunit, hcard⟩


lemma dot_mulVec_eq_double_sum {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x y : Fin n → ℝ) :
    x ⬝ᵥ A.mulVec y = ∑ i : Fin n, ∑ j : Fin n, x i * A i j * y j := by
  classical
  simp only [dotProduct, Matrix.mulVec_apply_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Convex combinations `(1-s)•A + s•M` (`M = (ρ+β)•uuᵀ - β•1`, `0 < s ≤ 1`) of a strict-type
symmetric positive matrix `A` (with Perron data `(u, ρ)`) stay in the strict set. -/
theorem strictQuad_convexCombo_mem {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (ρ β s : ℝ)
    (hA_symm : A.IsSymm) (hA_pos : ∀ i j : Fin n, 0 < A i j)
    (hu_pos : ∀ i : Fin n, 0 < u i)
    (hu_unit : (∑ i : Fin n, u i * u i) = 1)
    (hρ : 0 < ρ) (hβ : 0 < β)
    (hs_pos : 0 < s) (hs_le : s ≤ 1)
    (hAu : A.mulVec u = ρ • u)
    (hAquad : ∀ x : Fin n → ℝ, (∑ i : Fin n, u i * x i) = 0 →
        (∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j) ≤ 0)
    (hβlt : ∀ i : Fin n, β < (ρ + β) * (u i)^2) :
    let M : Matrix (Fin n) (Fin n) ℝ := (ρ + β) • Matrix.vecMulVec u u - β • 1
    let C : Matrix (Fin n) (Fin n) ℝ := (1 - s) • A + s • M
    C.IsSymm ∧ (∀ i j : Fin n, 0 < C i j) ∧ IsUnit C ∧
      ((C.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 1) := by
  classical
  intro M C
  have hM_def : M = (ρ + β) • Matrix.vecMulVec u u - β • 1 := rfl
  have hC_def : C = (1 - s) • A + s • M := rfl
  have hM_symm : M.IsSymm := by
    change ((ρ + β) • Matrix.vecMulVec u u - β • (1 : Matrix (Fin n) (Fin n) ℝ)).IsSymm
    rw [Matrix.IsSymm.ext_iff]
    intro i j
    by_cases hij : i = j
    · subst j
      simp
    · have hji : ¬ j = i := by intro h; exact hij h.symm
      simp [hij, hji, Matrix.vecMulVec_apply, mul_comm, mul_left_comm, mul_assoc]
  have hC_symm : C.IsSymm := by
    change ((1 - s) • A + s • ((ρ + β) • Matrix.vecMulVec u u - β • 1)).IsSymm
    exact Matrix.IsSymm.add (Matrix.IsSymm.smul hA_symm (1 - s)) (Matrix.IsSymm.smul hM_symm s)
  have hM_pos_entries : ∀ i j : Fin n, 0 < M i j := by
    intro i j
    change 0 < ((ρ + β) • Matrix.vecMulVec u u - β • (1 : Matrix (Fin n) (Fin n) ℝ)) i j
    by_cases hij : i = j
    · subst j
      change 0 < ((ρ + β) • Matrix.vecMulVec u u - β • (1 : Matrix (Fin n) (Fin n) ℝ)) i i
      rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.one_apply]
      simp
      have hlt : β < (ρ + β) * (u i * u i) := by simpa [pow_two] using hβlt i
      linarith
    · change 0 < ((ρ + β) • Matrix.vecMulVec u u - β • (1 : Matrix (Fin n) (Fin n) ℝ)) i j
      rw [Matrix.sub_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.one_apply, if_neg hij]
      simp
      exact mul_pos (add_pos hρ hβ) (mul_pos (hu_pos i) (hu_pos j))
  have hC_pos : ∀ i j : Fin n, 0 < C i j := by
    intro i j
    change 0 < ((1 - s) • A + s • ((ρ + β) • Matrix.vecMulVec u u - β • 1)) i j
    rw [Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply]
    rw [smul_eq_mul, smul_eq_mul]
    have h1s : 0 ≤ 1 - s := by linarith
    have ht1 : 0 ≤ (1 - s) * A i j := mul_nonneg h1s (le_of_lt (hA_pos i j))
    have ht2 : 0 < s * M i j := mul_pos hs_pos (hM_pos_entries i j)
    nlinarith
  have hM_u : M.mulVec u = ρ • u := by
    change ((ρ + β) • Matrix.vecMulVec u u - β • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec u = ρ • u
    calc
      ((ρ + β) • Matrix.vecMulVec u u - β • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec u
          = (ρ + β) • ((u ⬝ᵥ u) • u) - β • u := by
            rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, outer_mulVec]
      _ = ((ρ + β) * (u ⬝ᵥ u) - β) • u := by
            rw [smul_smul, ← sub_smul]
      _ = ρ • u := by
            have huu : u ⬝ᵥ u = 1 := by simpa [dotProduct] using hu_unit
            simp [huu]

  have hC_u : C.mulVec u = ρ • u := by
    change ((1 - s) • A + s • ((ρ + β) • Matrix.vecMulVec u u - β • 1)).mulVec u = ρ • u
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, hAu, hM_u]
    rw [smul_smul, smul_smul]
    rw [← add_smul]
    congr 1
    ring
  have hquad_decomp : ∀ x : Fin n → ℝ,
      x ⬝ᵥ C.mulVec x = (1 - s) * (x ⬝ᵥ A.mulVec x) + s * (x ⬝ᵥ M.mulVec x) := by
    intro x
    change x ⬝ᵥ (((1 - s) • A + s • ((ρ + β) • Matrix.vecMulVec u u - β • 1)).mulVec x) =
      (1 - s) * (x ⬝ᵥ A.mulVec x) + s * (x ⬝ᵥ M.mulVec x)
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec]
    rw [dotProduct_add, dotProduct_smul, dotProduct_smul]
    simp only [smul_eq_mul]
    rw [hM_def]
  have hA_quad_dot : ∀ x : Fin n → ℝ, x ⬝ᵥ u = 0 → x ⬝ᵥ A.mulVec x ≤ 0 := by
    intro x hxdot
    have hxsum : (∑ i : Fin n, u i * x i) = 0 := by
      have hx : (∑ i : Fin n, x i * u i) = 0 := by simpa [dotProduct] using hxdot
      simpa [mul_comm] using hx
    have hq := hAquad x hxsum
    have hb := dot_mulVec_eq_double_sum A x x
    nlinarith
  have hunit : IsUnit C := by
    refine isUnit_of_mulVec_eq_zero_of_eq_zero C ?_
    intro x hx0
    have hxu0 : x ⬝ᵥ u = 0 := by
      have h1 : u ⬝ᵥ C.mulVec x = 0 := by rw [hx0]; simp
      have h2 : x ⬝ᵥ C.mulVec u = u ⬝ᵥ C.mulVec x := dotProduct_mulVec_symm_eq C hC_symm x u
      have h4 : x ⬝ᵥ C.mulVec u = 0 := by rw [h2, h1]
      have h5 : x ⬝ᵥ (ρ • u) = 0 := by simpa [hC_u] using h4
      have hmain : ρ * (x ⬝ᵥ u) = 0 := by
        simpa [smul_eq_mul] using (by
          have h6 : x ⬝ᵥ (ρ • u) = ρ • (x ⬝ᵥ u) := dotProduct_smul ρ x u
          simpa [h6] using h5)
      exact (mul_eq_zero.mp hmain).resolve_left (ne_of_gt hρ)
    have hxAx_le : (1 - s) * (x ⬝ᵥ A.mulVec x) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (hA_quad_dot x hxu0)
    have hxMx : x ⬝ᵥ M.mulVec x = -β * (x ⬝ᵥ x) := by
      have hq := dot_rankOne_sub_smul u x (ρ + β) β
      rw [← hM_def] at hq
      rw [hxu0] at hq
      simpa using hq
    have hxx_nonneg : 0 ≤ x ⬝ᵥ x := by
      simpa [dotProduct] using (Finset.sum_nonneg (fun j hj => mul_self_nonneg (x j)))
    have hsum0 : (1 - s) * (x ⬝ᵥ A.mulVec x) + s * (x ⬝ᵥ M.mulVec x) = 0 := by
      have hd := hquad_decomp x
      have hxP : x ⬝ᵥ C.mulVec x = 0 := by rw [hx0]; simp
      linarith
    have hle0 : 0 ≤ s * (x ⬝ᵥ M.mulVec x) := by
      linarith
    have hle1 : s * (x ⬝ᵥ M.mulVec x) ≤ 0 := by
      rw [hxMx]
      exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hs_pos)
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_of_lt hβ)) hxx_nonneg)
    have hsM0 : s * (x ⬝ᵥ M.mulVec x) = 0 := le_antisymm hle1 hle0
    have hxx0 : x ⬝ᵥ x = 0 := by
      have hneg0 : -β * (x ⬝ᵥ x) = 0 := by
        have : s * (-β * (x ⬝ᵥ x)) = 0 := by simpa [hxMx] using hsM0
        exact (mul_eq_zero.mp (by simpa [smul_eq_mul] using this)).resolve_left (ne_of_gt hs_pos)
      have hb0 : β * (x ⬝ᵥ x) = 0 := by
        have : -(β * (x ⬝ᵥ x)) = 0 := by simpa [neg_mul] using hneg0
        exact neg_eq_zero.mp this
      exact (mul_eq_zero.mp hb0).resolve_left (ne_of_gt hβ)
    funext i
    have hxx_sum : (∑ j : Fin n, x j * x j) = 0 := by simpa [dotProduct] using hxx0
    have hterm : x i * x i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (f := fun j : Fin n => x j * x j)
        (fun j hj => mul_self_nonneg (x j))).mp hxx_sum i (Finset.mem_univ i)
    exact mul_self_eq_zero.mp hterm
  have hQpos : 0 < C.toQuadraticForm' u := by
    rw [toQuadraticForm'_apply_dot C u, hC_u]
    rw [dotProduct_smul]
    have huu : u ⬝ᵥ u = 1 := by simpa [dotProduct] using hu_unit
    simp [huu, smul_eq_mul]
    exact hρ
  have hQnonpos : ∀ x : Fin n → ℝ, (∑ i : Fin n, u i * x i) = 0 → C.toQuadraticForm' x ≤ 0 := by
    intro x hx
    have hxdot : x ⬝ᵥ u = 0 := by
      have hx' : (∑ i : Fin n, x i * u i) = 0 := by simpa [mul_comm] using hx
      simpa [dotProduct] using hx'
    rw [toQuadraticForm'_apply_dot C x]
    have hd := hquad_decomp x
    have hxAx_le : (1 - s) * (x ⬝ᵥ A.mulVec x) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos (by linarith) (hA_quad_dot x hxdot)
    have hxMx : x ⬝ᵥ M.mulVec x = -β * (x ⬝ᵥ x) := by
      have hq := dot_rankOne_sub_smul u x (ρ + β) β
      rw [← hM_def] at hq
      rw [hxdot] at hq
      simpa using hq
    have hxx_nonneg : 0 ≤ x ⬝ᵥ x := by
      simpa [dotProduct] using (Finset.sum_nonneg (fun j hj => mul_self_nonneg (x j)))
    have hsum : (1 - s) * (x ⬝ᵥ A.mulVec x) + s * (x ⬝ᵥ M.mulVec x) ≤ 0 := by
      rw [hxMx]
      have ht1 : (1 - s) * (x ⬝ᵥ A.mulVec x) ≤ 0 := hxAx_le
      have ht2 : s * (-β * (x ⬝ᵥ x)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hs_pos)
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (le_of_lt hβ)) hxx_nonneg)
      exact add_nonpos ht1 ht2
    rw [hd]
    exact hsum
  have hsig : QuadraticForm.sigPos C.toQuadraticForm' = 1 :=
    sigPos_eq_one_of_pos_u_nonpos_uorth hn C.toQuadraticForm' u hQpos hQnonpos
  have hcard : (C.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 1 := by
    rw [← sigPos_toQuadraticForm_eq_card_pos_roots C hC_symm]
    exact hsig
  exact ⟨hC_symm, hC_pos, hunit, hcard⟩


section connectivity

lemma exists_pos_lower_bound {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) (hf : ∀ i, 0 < f i) :
    ∃ c : ℝ, 0 < c ∧ ∀ i, c ≤ f i := by
  classical
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  let s : Finset ℝ := Finset.univ.image f
  have hs_nonempty : s.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  let c : ℝ := s.min' hs_nonempty
  refine ⟨c, ?_, ?_⟩
  · have hc_mem : c ∈ s := Finset.min'_mem s hs_nonempty
    rcases (Finset.mem_image.mp hc_mem) with ⟨i, _hi, hfi⟩
    rw [← hfi]
    exact hf i
  · intro i
    dsimp [c]
    exact Finset.min'_le s (f i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- the all-ones vector normalized to unit length (for `n ≥ 1`) -/
def hubVec (n : ℕ) : Fin n → ℝ := fun _ => 1 / Real.sqrt n

lemma hubVec_pos {n : ℕ} (hn : 0 < n) (i : Fin n) : 0 < hubVec n i := by
  dsimp [hubVec]
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn_pos
  positivity

lemma hubVec_sq {n : ℕ} (hn : 0 < n) (i : Fin n) : hubVec n i * hubVec n i = 1 / (n : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
  dsimp [hubVec]
  field_simp
  rw [Real.sq_sqrt hn_nonneg]

lemma hubVec_unit {n : ℕ} (hn : 0 < n) : (∑ i : Fin n, hubVec n i * hubVec n i) = 1 := by
  classical
  have hc : ∀ i : Fin n, hubVec n i * hubVec n i = 1 / (n : ℝ) := fun i => hubVec_sq hn i
  simp_rw [hc]
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
  field_simp

lemma hubVec_le_one {n : ℕ} (hn : 0 < n) (i : Fin n) : hubVec n i ≤ 1 := by
  have hn_ge : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hsqrt : 1 ≤ Real.sqrt (n : ℝ) := by
    exact (Real.le_sqrt (by norm_num) (by positivity : 0 ≤ (n : ℝ))).2 (by nlinarith)
  dsimp [hubVec]
  exact (div_le_one (by positivity : 0 < Real.sqrt (n : ℝ))).2 hsqrt

/-- the canonical hub matrix `(n : ℝ) • uH uHᵀ - (1/2) • 1 = J - (1/2)I` -/
def strictQuad_hub (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  (n : ℝ) • Matrix.vecMulVec (hubVec n) (hubVec n) - (1 / 2 : ℝ) • 1

end connectivity

/-- convert a four-tuple of strict-type conditions into set membership -/
lemma strictQuadSet_of_tuple {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : A.IsSymm ∧ (∀ i j : Fin n, 0 < A i j) ∧ IsUnit A ∧
      ((A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 1)) :
    A ∈ strictQuadSet n := by
  unfold strictQuadSet
  exact h

/-- membership of the hub matrix -/
lemma strictQuad_hub_mem (n : ℕ) (hn : 0 < n) : strictQuad_hub n ∈ strictQuadSet n := by
  classical
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hn)
  have hmem := strictQuad_pencil_mem hn (hubVec n) (n : ℝ) (1 / 2 : ℝ)
      (fun i => hubVec_pos hn i) (hubVec_unit hn) (by exact_mod_cast hn) (by norm_num) (by linarith) ?hβlt
  · have hmem' : strictQuad_hub n ∈ strictQuadSet n := by
      apply strictQuadSet_of_tuple (strictQuad_hub n)
      simpa [strictQuad_hub] using hmem
    exact hmem'
  · intro i
    have hs := hubVec_sq hn i
    have hsq : (hubVec n i)^2 = 1 / (n : ℝ) := by simpa [pow_two] using hs
    have hprod : (n : ℝ) * (hubVec n i)^2 = 1 := by
      rw [hsq]
      field_simp
    linarith

lemma divsqrt_sq {c a : ℝ} (hc : 0 < c) : (a / Real.sqrt c) * (a / Real.sqrt c) = a^2 / c := by
  have hc_nonneg : 0 ≤ c := le_of_lt hc
  have hsq : (Real.sqrt c)^2 = c := Real.sq_sqrt hc_nonneg
  field_simp [hsq]
  rw [hsq]

lemma strictQuad_pencil_w_mem {n : ℕ} (hn : 0 < n)
    (w : Fin n → ℝ) (α β : ℝ)
    (hw_pos : ∀ i : Fin n, 0 < w i)
    (hc_pos : 0 < ∑ j : Fin n, (w j)^2)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : β < α)
    (hβlt : ∀ i : Fin n, β * (∑ j : Fin n, (w j)^2) < α * (w i)^2) :
    ((α / (∑ j : Fin n, (w j)^2)) • Matrix.vecMulVec w w - β • 1 : Matrix (Fin n) (Fin n) ℝ) ∈
      strictQuadSet n := by
  classical
  let c : ℝ := ∑ j : Fin n, (w j)^2
  have hc_pos' : 0 < c := by simpa [c] using hc_pos
  have hc_nonneg : 0 ≤ c := le_of_lt hc_pos'
  have hscale : ∀ a : ℝ, (a / Real.sqrt c) * (a / Real.sqrt c) = a^2 / c := by
    intro a
    exact divsqrt_sq (c := c) (a := a) hc_pos' 
  let uhat : Fin n → ℝ := fun i => w i / Real.sqrt c
  have hsqrt_pos : 0 < Real.sqrt c := Real.sqrt_pos.2 hc_pos'
  have huhat_pos : ∀ i : Fin n, 0 < uhat i := by
    intro i
    dsimp [uhat]
    exact div_pos (hw_pos i) hsqrt_pos
  have huhat_unit : (∑ i : Fin n, uhat i * uhat i) = 1 := by
    dsimp [uhat]
    calc
      (∑ i : Fin n, (w i / Real.sqrt c) * (w i / Real.sqrt c)) = (∑ i : Fin n, (w i)^2 / c) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hscale (w i)
      _ = (∑ i : Fin n, (w i)^2) / c := by
        rw [Finset.sum_div]
      _ = 1 := by
        have hcsum : (∑ i : Fin n, (w i)^2) = c := rfl
        rw [hcsum]
        exact div_self (ne_of_gt hc_pos')
  have huhat_βlt : ∀ i : Fin n, β < α * (uhat i)^2 := by
    intro i
    have h1 : β < (α * (w i)^2) / c := (lt_div_iff₀ hc_pos').2 (by simpa [c] using hβlt i)
    have hsq : (uhat i)^2 = (w i)^2 / c := by
      dsimp [uhat]
      rw [← hscale (w i)]
      ring
    rw [hsq]
    rw [← mul_div_assoc]
    exact h1
  have hE := strictQuad_pencil_mem hn uhat α β huhat_pos huhat_unit hα hβ hαβ huhat_βlt
  have hE_mem : (α • Matrix.vecMulVec uhat uhat - β • 1) ∈ strictQuadSet n := by
    exact strictQuadSet_of_tuple (α • Matrix.vecMulVec uhat uhat - β • 1) hE
  have hEq : α • Matrix.vecMulVec uhat uhat - β • 1 =
      (α / c) • Matrix.vecMulVec w w - β • 1 := by
    ext i j
    dsimp [uhat]
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst j
      simp
      field_simp [Real.sq_sqrt hc_nonneg]
      rw [Real.sq_sqrt hc_nonneg]
    · simp [hij]
      field_simp [Real.sq_sqrt hc_nonneg]
      rw [Real.sq_sqrt hc_nonneg]
      ring
  rw [hEq] at hE_mem
  dsimp [c] at hE_mem
  exact hE_mem

section joined
open unitInterval Topology

/-- membership of convex combinations `(1-t)A + t•M0`, `0 ≤ t ≤ 1` -/
lemma strictQuad_mix_mem {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (ρ β0 t : ℝ)
    (hA_mem : A ∈ strictQuadSet n)
    (hu_pos : ∀ i : Fin n, 0 < u i)
    (hu_unit : (∑ i : Fin n, u i * u i) = 1)
    (hρ : 0 < ρ) (hβ : 0 < β0)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hAu : A.mulVec u = ρ • u)
    (hAquad : ∀ x : Fin n → ℝ, (∑ i : Fin n, u i * x i) = 0 →
        (∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j) ≤ 0)
    (hβlt : ∀ i : Fin n, β0 < (ρ + β0) * (u i)^2) :
    ((1 - t) • A + t • ((ρ + β0) • Matrix.vecMulVec u u - β0 • (1 : Matrix (Fin n) (Fin n) ℝ))) ∈
      strictQuadSet n := by
  classical
  rcases hA_mem with ⟨hA_symm, hA_pos, hA_unit, hA_card⟩
  by_cases ht : t = 0
  · subst t
    simp
    exact strictQuadSet_of_tuple A ⟨hA_symm, hA_pos, hA_unit, hA_card⟩
  · have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    have hmem := strictQuad_convexCombo_mem hn A u ρ β0 t hA_symm hA_pos hu_pos hu_unit hρ hβ
      ht_pos ht1 hAu hAquad hβlt
    exact strictQuadSet_of_tuple ((1 - t) • A + t • ((ρ + β0) • Matrix.vecMulVec u u - β0 • 1)) hmem

/-- leg 1: from `A` to the pencil `(ρ+β0)•uuᵀ - β0•1` -/
lemma strictQuad_leg1_joined {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) (ρ β0 : ℝ)
    (hA_mem : A ∈ strictQuadSet n)
    (hu_pos : ∀ i : Fin n, 0 < u i)
    (hu_unit : (∑ i : Fin n, u i * u i) = 1)
    (hρ : 0 < ρ) (hβ : 0 < β0)
    (hAu : A.mulVec u = ρ • u)
    (hAquad : ∀ x : Fin n → ℝ, (∑ i : Fin n, u i * x i) = 0 →
        (∑ i : Fin n, ∑ j : Fin n, x i * A i j * x j) ≤ 0)
    (hβlt : ∀ i : Fin n, β0 < (ρ + β0) * (u i)^2) :
    JoinedIn (strictQuadSet n) A ((ρ + β0) • Matrix.vecMulVec u u - β0 • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
  classical
  let M0 : Matrix (Fin n) (Fin n) ℝ := (ρ + β0) • Matrix.vecMulVec u u - β0 • 1
  let f : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t => (1 - t) • A + t • M0
  apply JoinedIn.ofLine (F := strictQuadSet n) (f := f)
  · -- continuous on I
    refine (continuousOn_pi).2 ?_
    intro i
    refine (continuousOn_pi).2 ?_
    intro j
    dsimp [f, M0]
    fun_prop
  · simp [f]
  · simp [f, M0]
  · -- image ⊆ F: pointwise membership
    intro B hB
    rcases (Set.mem_image f I B).mp hB with ⟨t, ht, rfl⟩
    have ht0 : 0 ≤ t := (Set.mem_Icc.mp ht).1
    have ht1 : t ≤ 1 := (Set.mem_Icc.mp ht).2
    exact strictQuad_mix_mem hn A u ρ β0 t hA_mem hu_pos hu_unit hρ hβ ht0 ht1 hAu hAquad hβlt

end joined

section glue

lemma convex_between_pos {a b t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ha : 0 < a) (hb : 0 < b) : 0 < (1 - t) * a + t * b := by
  by_cases ht : t = 0
  · subst t
    simpa using ha
  · have ht_pos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht)
    by_cases ht' : t = 1
    · subst t
      simpa using hb
    · have ht_lt : t < 1 := lt_of_le_of_ne ht1 ht'
      have h1 : 0 < (1 - t) * a := mul_pos (by linarith) ha
      have h2 : 0 ≤ t * b := mul_nonneg (le_of_lt ht_pos) (le_of_lt hb)
      nlinarith

lemma convex_between_le {a b t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hab : a ≤ b) :
    (1 - t) * a + t * b ≤ b := by
  nlinarith

lemma convex_between_ge {a b t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (hab : b ≤ a) :
    b ≤ (1 - t) * a + t * b := by
  nlinarith

lemma sq_le_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : a^2 ≤ b^2 := by
  have hb : 0 ≤ b := le_trans ha hab
  rw [pow_two, pow_two]
  exact mul_le_mul hab hab ha hb

/-- the mixed vector entries are bounded below by `δ` for `t ∈ [0,1]` -/
lemma mixVec_lower {n : ℕ} (u uH : Fin n → ℝ) (δ t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hδ_u : ∀ i : Fin n, δ ≤ u i) (hδ_uH : ∀ i : Fin n, δ ≤ uH i) :
    ∀ i : Fin n, δ ≤ (1 - t) * u i + t * uH i := by
  intro i
  have h1 : (1 - t) * δ ≤ (1 - t) * u i := mul_le_mul_of_nonneg_left (hδ_u i) (by linarith)
  have h2 : t * δ ≤ t * uH i := mul_le_mul_of_nonneg_left (hδ_uH i) ht0
  have hsum : (1 - t) * δ + t * δ ≤ (1 - t) * u i + t * uH i := add_le_add h1 h2
  have : (1 - t) * δ + t * δ = δ := by ring
  linarith

/-- the mixed vector entries are at most `1` for `t ∈ [0,1]` (given the endpoints are ≤ 1) -/
lemma mixVec_upper {n : ℕ} (u uH : Fin n → ℝ) (t : ℝ)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hu_le1 : ∀ i : Fin n, u i ≤ 1) (huH_le1 : ∀ i : Fin n, uH i ≤ 1) :
    ∀ i : Fin n, (1 - t) * u i + t * uH i ≤ 1 := by
  intro i
  have h1 : (1 - t) * u i ≤ (1 - t) * 1 := mul_le_mul_of_nonneg_left (hu_le1 i) (by linarith)
  have h2 : t * uH i ≤ t * 1 := mul_le_mul_of_nonneg_left (huH_le1 i) ht0
  have hsum : (1 - t) * u i + t * uH i ≤ (1 - t) * 1 + t * 1 := add_le_add h1 h2
  have : (1 - t) * 1 + t * 1 = 1 := by ring
  linarith

/-- entrywise membership of the rotating-pencil path at a single time -/
lemma strictQuad_mixPencil_mem {n : ℕ} (hn : 0 < n)
    (u uH : Fin n → ℝ) (α β δ t : ℝ)
    (hu_pos : ∀ i : Fin n, 0 < u i) (huH_pos : ∀ i : Fin n, 0 < uH i)
    (hu_unit : (∑ i : Fin n, u i * u i) = 1)
    (huH_unit : (∑ i : Fin n, uH i * uH i) = 1)
    (hu_le1 : ∀ i : Fin n, u i ≤ 1) (huH_le1 : ∀ i : Fin n, uH i ≤ 1)
    (hδ_pos : 0 < δ) (hδ_u : ∀ i : Fin n, δ ≤ u i) (hδ_uH : ∀ i : Fin n, δ ≤ uH i)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : β < α)
    (hβsmall : β < α * δ^2 / (n : ℝ))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let v : Fin n → ℝ := fun i => (1 - t) * u i + t * uH i
    ((α / (∑ j : Fin n, (v j)^2)) • Matrix.vecMulVec v v - β • 1 : Matrix (Fin n) (Fin n) ℝ) ∈
      strictQuadSet n := by
  classical
  intro v
  have hv_pos : ∀ i : Fin n, 0 < v i := by
    intro i
    have hδv : δ ≤ v i := mixVec_lower u uH δ t ht0 ht1 hδ_u hδ_uH i
    exact lt_of_lt_of_le hδ_pos hδv
  have hv_le1 : ∀ i : Fin n, v i ≤ 1 := mixVec_upper u uH t ht0 ht1 hu_le1 huH_le1
  have hv_sq_le1 : ∀ j : Fin n, (v j)^2 ≤ 1 := by
    intro j
    have h1 : 0 ≤ v j := le_of_lt (hv_pos j)
    have hsq : (v j)^2 ≤ (1 : ℝ)^2 := sq_le_of_nonneg h1 (hv_le1 j)
    simpa using hsq
  -- positive scalar product bound `β * c < α * vᵢ²`
  have hβlt : ∀ i : Fin n, β * (∑ j : Fin n, (v j)^2) < α * (v i)^2 := by
    intro i
    have hc_le : (∑ j : Fin n, (v j)^2) ≤ (n : ℝ) := by
      have hsum_le : (∑ j : Fin n, (v j)^2) ≤ ∑ j : Fin n, (1 : ℝ) :=
        Finset.sum_le_sum (fun j hj => hv_sq_le1 j)
      simpa [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin] using hsum_le
    have h1 : β * (∑ j : Fin n, (v j)^2) ≤ β * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hc_le (le_of_lt hβ)
    have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
    have h2 : β * (n : ℝ) < α * δ^2 := by
      calc
        β * (n : ℝ) < (α * δ^2 / (n : ℝ)) * (n : ℝ) := mul_lt_mul_of_pos_right hβsmall hnp
        _ = α * δ^2 := by field_simp
    have hδsq : δ^2 ≤ (v i)^2 := sq_le_of_nonneg (le_of_lt hδ_pos) (mixVec_lower u uH δ t ht0 ht1 hδ_u hδ_uH i)
    have h3 : α * δ^2 ≤ α * (v i)^2 := mul_le_mul_of_nonneg_left hδsq (le_of_lt hα)
    exact lt_of_le_of_lt h1 (lt_of_lt_of_le h2 h3)
  have hc_pos : 0 < ∑ j : Fin n, (v j)^2 := by
    let i0 : Fin n := ⟨0, hn⟩
    have hterm_pos : 0 < (v i0)^2 := sq_pos_of_ne_zero (ne_of_gt (hv_pos i0))
    have hle_term : (v i0)^2 ≤ ∑ j : Fin n, (v j)^2 :=
      Finset.single_le_sum (fun j hj => sq_nonneg (v j)) (Finset.mem_univ i0)
    exact lt_of_lt_of_le hterm_pos hle_term
  exact strictQuad_pencil_w_mem hn v α β hv_pos hc_pos hα hβ hαβ hβlt

end glue

/-- rotating pencil path function -/
def mixPencil {n : ℕ} (u uH : Fin n → ℝ) (α β : ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  let v : Fin n → ℝ := fun i => (1 - t) * u i + t * uH i
  let c : ℝ := ∑ j : Fin n, (v j)^2
  (α / c) • Matrix.vecMulVec v v - β • 1

/-- adjusting path function on `(α,β)` with `uH` fixed -/
def adjustPencil {n : ℕ} (uH : Fin n → ℝ) (α0 β0 : ℝ) (t : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  let αt : ℝ := (1 - t) * α0 + t * (n : ℝ)
  let βt : ℝ := (1 - t) * β0 + t * (1 / 2 : ℝ)
  αt • Matrix.vecMulVec uH uH - βt • 1

section paths
open unitInterval Topology Set
open scoped BigOperators

lemma term_le_sum_sq {n : ℕ} (w : Fin n → ℝ) (i0 : Fin n) :
    (w i0)^2 ≤ ∑ j : Fin n, (w j)^2 := by
  classical
  rw [← Finset.sum_erase_add (s := Finset.univ) (a := i0) (f := fun j : Fin n => (w j)^2) (Finset.mem_univ i0)]
  have hnonneg : 0 ≤ ∑ x ∈ (Finset.univ.erase i0), (w x)^2 :=
    Finset.sum_nonneg (fun j hj => sq_nonneg (w j))
  exact le_add_of_nonneg_left hnonneg

lemma abs_le_one_of_sq_le {a : ℝ} (h : a^2 ≤ 1) : |a| ≤ 1 := by
  have hnonneg_abs : 0 ≤ |a| := abs_nonneg a
  by_contra hnot
  have hgt : 1 < |a| := lt_of_not_ge hnot
  have hfac : 0 < (|a| - 1) * (|a| + 1) := mul_pos (sub_pos.mpr hgt) (by positivity)
  have heq : (|a| - 1) * (|a| + 1) = |a|^2 - 1 := by ring
  have hpow : 1 < |a|^2 := by
    have : 0 < |a|^2 - 1 := by simpa [heq] using hfac
    linarith
  have hsq : |a|^2 = a^2 := by rw [sq_abs]
  linarith

lemma le_one_of_sq_le {a : ℝ} (ha0 : 0 ≤ a) (h : a^2 ≤ 1) : a ≤ 1 := by
  have habs : |a| ≤ 1 := abs_le_one_of_sq_le h
  have : a ≤ |a| := le_abs_self a
  linarith

lemma unit_vector_le_one {n : ℕ} (u : Fin n → ℝ)
    (hu_unit : (∑ i : Fin n, u i * u i) = 1) (hu_nonneg : ∀ i : Fin n, 0 ≤ u i) :
    ∀ i : Fin n, u i ≤ 1 := by
  classical
  intro i
  have hterm : (u i)^2 ≤ ∑ j : Fin n, (u j)^2 := by
    exact Finset.single_le_sum (fun j hj => sq_nonneg (u j)) (Finset.mem_univ i)
  have hsum : (∑ j : Fin n, (u j)^2) = 1 := by simpa [pow_two] using hu_unit
  have hs : (u i)^2 ≤ 1 := by simpa [hsum] using hterm
  exact le_one_of_sq_le (hu_nonneg i) hs

lemma mixPencil_continuousOn {n : ℕ} (hn : 0 < n) (u uH : Fin n → ℝ) (α β δ : ℝ)
    (hδ_pos : 0 < δ) (hδ_u : ∀ i : Fin n, δ ≤ u i) (hδ_uH : ∀ i : Fin n, δ ≤ uH i) :
    ContinuousOn (fun t : ℝ => mixPencil u uH α β t) I := by
  classical
  have hδ_nonneg : 0 ≤ δ := le_of_lt hδ_pos
  have hc_ne : ∀ t : ℝ, t ∈ I → (∑ j : Fin n, ((1 - t) * u j + t * uH j)^2) ≠ 0 := by
    intro t ht
    have ht0 : 0 ≤ t := (Set.mem_Icc.mp ht).1
    have ht1 : t ≤ 1 := (Set.mem_Icc.mp ht).2
    have hv_low : ∀ j : Fin n, δ ≤ (1 - t) * u j + t * uH j :=
      mixVec_lower u uH δ t ht0 ht1 hδ_u hδ_uH
    let i0 : Fin n := ⟨0, hn⟩
    have hterm_pos : 0 < ((1 - t) * u i0 + t * uH i0)^2 :=
      sq_pos_of_ne_zero (ne_of_gt (lt_of_lt_of_le hδ_pos (hv_low i0)))
    have hsum_ge : ((1 - t) * u i0 + t * uH i0)^2 ≤
        ∑ j : Fin n, ((1 - t) * u j + t * uH j)^2 :=
      term_le_sum_sq (fun j : Fin n => (1 - t) * u j + t * uH j) i0
    exact ne_of_gt (lt_of_lt_of_le hterm_pos hsum_ge)
  -- coordinate-wise
  apply (continuousOn_pi).2
  intro i
  apply (continuousOn_pi).2
  intro j
  change ContinuousOn (fun t : ℝ => mixPencil u uH α β t i j) I
  unfold mixPencil
  dsimp
  by_cases hij : i = j
  · subst j
    have hv_i : ContinuousOn (fun t : ℝ => (1 - t) * u i + t * uH i) I := by fun_prop
    have hc : ContinuousOn (fun t : ℝ => (∑ k : Fin n, ((1 - t) * u k + t * uH k)^2)) I := by
      -- c is a continuous polynomial
      have hc_global : Continuous (fun t : ℝ => ∑ k : Fin n, ((1 - t) * u k + t * uH k)^2) := by
        refine continuous_finsetSum Finset.univ ?_
        intro k hk
        fun_prop
      exact hc_global.continuousOn
    -- entry: α / c * (v_i)^2 - β
    have hnum : ContinuousOn (fun t : ℝ => α * ((1 - t) * u i + t * uH i) * ((1 - t) * u i + t * uH i)) I := by
      exact (continuousOn_const.mul hv_i).mul hv_i
    have hdiv : ContinuousOn (fun t : ℝ => (α * ((1 - t) * u i + t * uH i) * ((1 - t) * u i + t * uH i)) /
        (∑ k : Fin n, ((1 - t) * u k + t * uH k)^2)) I :=
      ContinuousOn.div hnum hc hc_ne
    -- entry minus β:
    have he : ContinuousOn (fun t : ℝ =>
        α * ((1 - t) * u i + t * uH i) * ((1 - t) * u i + t * uH i) /
          (∑ k : Fin n, ((1 - t) * u k + t * uH k)^2) - β) I := hdiv.sub continuousOn_const
    have heq : Set.EqOn (fun t : ℝ => mixPencil u uH α β t i i)
        (fun t : ℝ =>
          α * ((1 - t) * u i + t * uH i) * ((1 - t) * u i + t * uH i) /
            (∑ k : Fin n, ((1 - t) * u k + t * uH k)^2) - β) I := by
      intro t ht
      simp [mixPencil, Matrix.vecMulVec_apply]
      have h1 : (∑ k : Fin n, ((1 - t) * u k + t * uH k)^2) ≠ 0 := hc_ne t ht
      try field_simp
      try ring
    exact he.congr heq
  · have hv_i : ContinuousOn (fun t : ℝ => (1 - t) * u i + t * uH i) I := by fun_prop
    have hv_j : ContinuousOn (fun t : ℝ => (1 - t) * u j + t * uH j) I := by fun_prop
    have hc : ContinuousOn (fun t : ℝ => (∑ k : Fin n, ((1 - t) * u k + t * uH k)^2)) I := by
      have hc_global : Continuous (fun t : ℝ => ∑ k : Fin n, ((1 - t) * u k + t * uH k)^2) := by
        refine continuous_finsetSum Finset.univ ?_
        intro k hk
        fun_prop
      exact hc_global.continuousOn
    have hnum : ContinuousOn (fun t : ℝ => α * ((1 - t) * u i + t * uH i) * ((1 - t) * u j + t * uH j)) I := by
      exact (continuousOn_const.mul hv_i).mul hv_j
    have hdiv : ContinuousOn (fun t : ℝ => (α * ((1 - t) * u i + t * uH i) * ((1 - t) * u j + t * uH j)) /
        (∑ k : Fin n, ((1 - t) * u k + t * uH k)^2)) I :=
      ContinuousOn.div hnum hc hc_ne
    have heq : Set.EqOn (fun t : ℝ => mixPencil u uH α β t i j)
        (fun t : ℝ =>
          α * ((1 - t) * u i + t * uH i) * ((1 - t) * u j + t * uH j) /
            (∑ k : Fin n, ((1 - t) * u k + t * uH k)^2)) I := by
      intro t ht
      simp [mixPencil, hij, Matrix.vecMulVec_apply]
      have h1 : (∑ k : Fin n, ((1 - t) * u k + t * uH k)^2) ≠ 0 := hc_ne t ht
      try field_simp
      try ring
    exact hdiv.congr heq

end paths

section pathlemma
open unitInterval Topology Set
open scoped BigOperators

lemma mixPencil_zero {n : ℕ} (u uH : Fin n → ℝ) (α β : ℝ)
    (hu_unit : (∑ i : Fin n, u i * u i) = 1) :
    mixPencil u uH α β 0 = α • Matrix.vecMulVec u u - β • 1 := by
  classical
  ext i j
  unfold mixPencil
  dsimp
  simp
  have hu1 : (∑ x : Fin n, (u x)^2) = 1 := by simpa [pow_two] using hu_unit
  rw [hu1]
  simp

lemma mixPencil_one {n : ℕ} (u uH : Fin n → ℝ) (α β : ℝ)
    (huH_unit : (∑ i : Fin n, uH i * uH i) = 1) :
    mixPencil u uH α β 1 = α • Matrix.vecMulVec uH uH - β • 1 := by
  classical
  ext i j
  unfold mixPencil
  dsimp
  simp
  have hu1 : (∑ x : Fin n, (uH x)^2) = 1 := by simpa [pow_two] using huH_unit
  rw [hu1]
  simp

/-- leg B: rotate `u` to `uH` inside the strict set -/
lemma strictQuad_legB_joined {n : ℕ} (hn : 0 < n)
    (u uH : Fin n → ℝ) (α β δ : ℝ)
    (hu_pos : ∀ i : Fin n, 0 < u i) (huH_pos : ∀ i : Fin n, 0 < uH i)
    (hu_unit : (∑ i : Fin n, u i * u i) = 1)
    (huH_unit : (∑ i : Fin n, uH i * uH i) = 1)
    (hu_le1 : ∀ i : Fin n, u i ≤ 1) (huH_le1 : ∀ i : Fin n, uH i ≤ 1)
    (hδ_pos : 0 < δ) (hδ_u : ∀ i : Fin n, δ ≤ u i) (hδ_uH : ∀ i : Fin n, δ ≤ uH i)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : β < α)
    (hβsmall : β < α * δ^2 / (n : ℝ)) :
    JoinedIn (strictQuadSet n)
      (α • Matrix.vecMulVec u u - β • 1)
      (α • Matrix.vecMulVec uH uH - β • 1) := by
  classical
  let f : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t => mixPencil u uH α β t
  apply JoinedIn.ofLine (F := strictQuadSet n) (f := f)
  · exact mixPencil_continuousOn hn u uH α β δ hδ_pos hδ_u hδ_uH
  · exact mixPencil_zero u uH α β hu_unit
  · exact mixPencil_one u uH α β huH_unit
  · -- image ⊆ F
    intro B hB
    rcases (Set.mem_image f I B).mp hB with ⟨t, ht, rfl⟩
    have ht0 : 0 ≤ t := (Set.mem_Icc.mp ht).1
    have ht1 : t ≤ 1 := (Set.mem_Icc.mp ht).2
    dsimp [f]
    exact strictQuad_mixPencil_mem hn u uH α β δ t hu_pos huH_pos hu_unit huH_unit
      hu_le1 huH_le1 hδ_pos hδ_u hδ_uH hα hβ hαβ hβsmall ht0 ht1

end pathlemma

section adjust
open unitInterval Topology Set
open scoped BigOperators

/-- membership of the `(α,β)`-adjusting path at a single time -/
lemma strictQuad_adjust_mem {n : ℕ} (hn : 0 < n)
    (uH : Fin n → ℝ) (α0 β0 t : ℝ)
    (huH_pos : ∀ i : Fin n, 0 < uH i)
    (huH_unit : (∑ i : Fin n, uH i * uH i) = 1)
    (huH_sq : ∀ i : Fin n, (uH i)^2 = 1 / (n : ℝ))
    (hα0 : 0 < α0) (hβ0 : 0 < β0)
    (hβ0n : β0 < α0 / (n : ℝ))
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    let αt : ℝ := (1 - t) * α0 + t * (n : ℝ)
    let βt : ℝ := (1 - t) * β0 + t * (1 / 2 : ℝ)
    (αt • Matrix.vecMulVec uH uH - βt • 1 : Matrix (Fin n) (Fin n) ℝ) ∈ strictQuadSet n := by
  classical
  intro αt βt
  have hαt_pos : 0 < αt := by
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
    exact convex_between_pos ht0 ht1 hα0 hn_pos
  have hβt_pos : 0 < βt := by
    exact convex_between_pos ht0 ht1 hβ0 (by norm_num)
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn
  have hA0 : 0 < α0 / (n : ℝ) - β0 := sub_pos.mpr hβ0n
  have hβt_lt : βt < αt / (n : ℝ) := by
    have htmp : αt / (n : ℝ) - βt = (1 - t) * (α0 / (n : ℝ) - β0) + t * (1 / 2 : ℝ) := by
      field_simp
      ring
    have hpos : 0 < αt / (n : ℝ) - βt := by
      rw [htmp]
      exact convex_between_pos ht0 ht1 hA0 (by norm_num)
    linarith
  have hβt_lt_α : βt < αt := by
    have hn_ge1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hrec : (1 : ℝ) / (n : ℝ) ≤ 1 := (div_le_one hn_pos).2 hn_ge1
    have hle : αt / (n : ℝ) ≤ αt := by
      calc
        αt / (n : ℝ) = αt * (1 / (n : ℝ)) := by field_simp
        _ ≤ αt * 1 := mul_le_mul_of_nonneg_left hrec (le_of_lt hαt_pos)
        _ = αt := by ring
    exact lt_of_lt_of_le hβt_lt hle
  have hβlt : ∀ i : Fin n, βt < αt * (uH i)^2 := by
    intro i
    have hu : (uH i)^2 = 1 / (n : ℝ) := huH_sq i
    calc
      βt < αt / (n : ℝ) := hβt_lt
      _ = αt * (uH i)^2 := by
        rw [hu]
        try field_simp
        try ring
  have hmem := strictQuad_pencil_mem hn uH αt βt huH_pos huH_unit hαt_pos hβt_pos hβt_lt_α hβlt
  exact strictQuadSet_of_tuple (αt • Matrix.vecMulVec uH uH - βt • 1) hmem

lemma adjustPencil_continuousOn {n : ℕ} (uH : Fin n → ℝ) (α0 β0 : ℝ) :
    ContinuousOn (fun t : ℝ => adjustPencil uH α0 β0 t) I := by
  apply (continuousOn_pi).2
  intro i
  apply (continuousOn_pi).2
  intro j
  change ContinuousOn (fun t : ℝ => adjustPencil uH α0 β0 t i j) I
  unfold adjustPencil
  dsimp
  fun_prop

/-- leg C: adjust `(α,β)` to `(n,1/2)` at the fixed vector `uH` -/
lemma strictQuad_adjust_joined {n : ℕ} (hn : 0 < n)
    (uH : Fin n → ℝ) (α0 β0 : ℝ)
    (huH_pos : ∀ i : Fin n, 0 < uH i)
    (huH_unit : (∑ i : Fin n, uH i * uH i) = 1)
    (huH_sq : ∀ i : Fin n, (uH i)^2 = 1 / (n : ℝ))
    (huH_mul : ∀ i j : Fin n, uH i * uH j = 1 / (n : ℝ))
    (hα0 : 0 < α0) (hβ0 : 0 < β0)
    (hβ0n : β0 < α0 / (n : ℝ)) :
    JoinedIn (strictQuadSet n)
      (α0 • Matrix.vecMulVec uH uH - β0 • 1)
      (fun i j : Fin n => if i = j then (1 / 2 : ℝ) else 1) := by
  classical
  let f : ℝ → Matrix (Fin n) (Fin n) ℝ := fun t => adjustPencil uH α0 β0 t
  apply JoinedIn.ofLine (F := strictQuadSet n) (f := f)
  · exact adjustPencil_continuousOn uH α0 β0
  · -- f 0 = α0 • uH uHᵀ - β0 • 1
    ext i j
    dsimp [f, adjustPencil]
    ring
  · -- f 1 = (fun i j => if i=j then 1/2 else 1)
    ext i j
    dsimp [f, adjustPencil]
    simp [Matrix.vecMulVec_apply]
    by_cases hij : i = j
    · subst j
      rw [huH_mul i i]
      simp
      field_simp
      norm_num
    · rw [huH_mul i j]
      simp [hij]
      field_simp
  · -- image ⊆ F
    intro B hB
    rcases (Set.mem_image f I B).mp hB with ⟨t, ht, rfl⟩
    have ht0 : 0 ≤ t := (Set.mem_Icc.mp ht).1
    have ht1 : t ≤ 1 := (Set.mem_Icc.mp ht).2
    dsimp [f]
    exact strictQuad_adjust_mem hn uH α0 β0 t huH_pos huH_unit huH_sq hα0 hβ0 hβ0n ht0 ht1

end adjust

section final
open unitInterval Topology Set
open scoped BigOperators

lemma hubVec_mul {n : ℕ} (hn : 0 < n) (i j : Fin n) :
    hubVec n i * hubVec n j = 1 / (n : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hn_nonneg : 0 ≤ (n : ℝ) := le_of_lt hn_pos
  dsimp [hubVec]
  field_simp [Real.sq_sqrt hn_nonneg]
  rw [Real.sq_sqrt hn_nonneg]

/-- the adjust endpoint equals the hub matrix `(n : ℝ) • uH uHᵀ - (1/2)•1` -/
lemma adjust_end_eq {n : ℕ} (hn : 0 < n) :
    (fun i j : Fin n => if i = j then (1 / 2 : ℝ) else 1) = strictQuad_hub n := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    unfold strictQuad_hub
    dsimp
    simp [Matrix.vecMulVec_apply]
    rw [hubVec_mul hn i i]
    field_simp
    norm_num
  · unfold strictQuad_hub
    dsimp
    simp [Matrix.vecMulVec_apply]
    rw [hubVec_mul hn i j]
    simp [hij]
    field_simp

lemma hub_end_mem {n : ℕ} (hn : 0 < n) :
    (fun i j : Fin n => if i = j then (1 / 2 : ℝ) else 1) ∈ strictQuadSet n := by
  rw [adjust_end_eq hn]
  exact strictQuad_hub_mem n hn

/-- every pencil element with the small-`β` hypotheses joins the hub -/
lemma strictQuad_pencil_joins_hub {n : ℕ} (hn : 0 < n)
    (u : Fin n → ℝ) (α β δ : ℝ)
    (hu_pos : ∀ i : Fin n, 0 < u i)
    (hu_unit : (∑ i : Fin n, u i * u i) = 1)
    (hu_le1 : ∀ i : Fin n, u i ≤ 1)
    (hα : 0 < α) (hβ : 0 < β) (hαβ : β < α)
    (hβlt : ∀ i : Fin n, β < α * (u i)^2)
    (hδ_pos : 0 < δ)
    (hδ_u : ∀ i : Fin n, δ ≤ u i)
    (hδ_hub : ∀ i : Fin n, δ ≤ 1 / Real.sqrt n)
    (hβsmall : β < α * δ^2 / (n : ℝ)) :
    JoinedIn (strictQuadSet n)
      (α • Matrix.vecMulVec u u - β • 1)
      (fun i j : Fin n => if i = j then (1 / 2 : ℝ) else 1) := by
  classical
  let uH : Fin n → ℝ := hubVec n
  have huH_pos : ∀ i : Fin n, 0 < uH i := by intro i; dsimp [uH]; exact hubVec_pos hn i
  have huH_unit : (∑ i : Fin n, uH i * uH i) = 1 := by simpa [uH] using hubVec_unit hn
  have huH_le1 : ∀ i : Fin n, uH i ≤ 1 := by intro i; dsimp [uH]; exact hubVec_le_one hn i
  have hδ_uH : ∀ i : Fin n, δ ≤ uH i := by
    intro i
    dsimp [uH, hubVec]
    exact hδ_hub i
  have hδ1 : δ ≤ 1 :=
    le_trans (hδ_hub ⟨0, hn⟩) (by simpa [hubVec] using hubVec_le_one hn ⟨0, hn⟩)
  have hδ2 : δ^2 ≤ 1 := by
    simpa using sq_le_of_nonneg (le_of_lt hδ_pos) hδ1
  have hβ0n : β < α / (n : ℝ) := by
    have h2 : α * δ^2 / (n : ℝ) ≤ α / (n : ℝ) := by
      have hmul : α * δ^2 ≤ α * 1 := mul_le_mul_of_nonneg_left hδ2 (le_of_lt hα)
      have hnp : 0 < (n : ℝ) := by exact_mod_cast hn
      exact div_le_div_of_nonneg_right (by simpa using hmul) hnp.le
    exact lt_of_lt_of_le hβsmall h2
  -- rotate
  have hlegB := strictQuad_legB_joined hn u uH α β δ hu_pos huH_pos hu_unit huH_unit
    hu_le1 huH_le1 hδ_pos hδ_u hδ_uH hα hβ hαβ hβsmall
  -- adjust
  have huH_sq : ∀ i : Fin n, (uH i)^2 = 1 / (n : ℝ) := by
    intro i
    dsimp [uH]
    simpa [pow_two] using hubVec_sq hn i
  have huH_mul : ∀ i j : Fin n, uH i * uH j = 1 / (n : ℝ) := by
    intro i j
    dsimp [uH]
    exact hubVec_mul hn i j
  have hlegC := strictQuad_adjust_joined hn uH α β huH_pos huH_unit huH_sq huH_mul hα hβ hβ0n
  -- adjust ends at the hub matrix (since uH = hubVec n, endpoint defeq): 
  have hC : JoinedIn (strictQuadSet n) (α • Matrix.vecMulVec uH uH - β • 1)
      (fun i j : Fin n => if i = j then (1 / 2 : ℝ) else 1) := hlegC
  -- compose
  exact JoinedIn.trans hlegB hC

end final

lemma strictQuad_joined_hub {n : ℕ} (hn : 0 < n)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : A ∈ strictQuadSet n) :
    JoinedIn (strictQuadSet n) A
      (fun i j : Fin n => if i = j then (1 / 2 : ℝ) else 1) := by
  classical
  rcases hA with ⟨hA_symm, hA_pos, hA_unit, hA_card⟩
  obtain ⟨u, ρ, hρ, hu_pos, hu_unit, hAu, hAquad⟩ :=
    strictQuad_perron_vector hn A hA_symm hA_pos hA_card
  obtain ⟨mu, hmu_pos, hmu_le⟩ := exists_pos_lower_bound hn u hu_pos
  let δ : ℝ := min mu (1 / Real.sqrt (n : ℝ))
  have hδ_pos : 0 < δ := lt_min hmu_pos (by
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    positivity)
  have hδ_u : ∀ i : Fin n, δ ≤ u i := by
    intro i
    exact le_trans (min_le_left mu (1 / Real.sqrt (n : ℝ))) (hmu_le i)
  have hδ_hub : ∀ i : Fin n, δ ≤ 1 / Real.sqrt (n : ℝ) := by
    intro i
    exact min_le_right mu (1 / Real.sqrt (n : ℝ))
  have hu_nonneg : ∀ i : Fin n, 0 ≤ u i := fun i => le_of_lt (hu_pos i)
  have hu_le1 : ∀ i : Fin n, u i ≤ 1 := unit_vector_le_one u hu_unit hu_nonneg
  let β0 : ℝ := ρ * δ^2 / (2 * (n : ℝ))
  have hβ0_pos : 0 < β0 := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    dsimp [β0]
    positivity
  let α0 : ℝ := ρ + β0
  have hα0 : 0 < α0 := by dsimp [α0]; positivity
  have hαβ : β0 < α0 := by dsimp [α0]; linarith
  have hβlt : ∀ i : Fin n, β0 < (ρ + β0) * (u i)^2 := by
    intro i
    have hδ2 : δ^2 ≤ (u i)^2 := sq_le_of_nonneg (le_of_lt hδ_pos) (hδ_u i)
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hρδ_pos : 0 < ρ * δ^2 := mul_pos hρ (sq_pos_of_ne_zero (ne_of_gt hδ_pos))
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hn)
    have hβle : β0 ≤ ρ * δ^2 / 2 := by
      dsimp [β0]
      rw [div_le_div_iff₀ (by positivity : 0 < 2 * (n : ℝ)) (by norm_num : 0 < (2 : ℝ))]
      have h2n : (2 : ℝ) ≤ 2 * (n : ℝ) := by nlinarith
      nlinarith
    have hβlt0 : β0 < ρ * δ^2 := lt_of_le_of_lt hβle (by nlinarith)
    have h1 : ρ * δ^2 ≤ (ρ + β0) * (u i)^2 := by
      have hle1 : ρ * δ^2 ≤ (ρ + β0) * δ^2 := by
        have hρle : ρ ≤ ρ + β0 := by dsimp [β0]; linarith
        exact mul_le_mul_of_nonneg_right hρle (sq_nonneg δ)
      have hle2 : (ρ + β0) * δ^2 ≤ (ρ + β0) * (u i)^2 := by
        exact mul_le_mul_of_nonneg_left hδ2 (by dsimp [β0]; linarith)
      exact le_trans hle1 hle2
    exact lt_of_lt_of_le hβlt0 h1
  have hβsmall : β0 < (ρ + β0) * δ^2 / (n : ℝ) := by
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hρδ_pos : 0 < ρ * δ^2 := mul_pos hρ (sq_pos_of_ne_zero (ne_of_gt hδ_pos))
    have hs1 : ρ * δ^2 / (2 * (n : ℝ)) < ρ * δ^2 / (n : ℝ) := by
      rw [div_lt_div_iff₀ (by positivity : 0 < 2 * (n : ℝ)) (by positivity : 0 < (n : ℝ))]
      nlinarith
    have hs2 : ρ * δ^2 / (n : ℝ) ≤ (ρ + β0) * δ^2 / (n : ℝ) := by
      have hle : ρ * δ^2 ≤ (ρ + β0) * δ^2 := by
        have hρle : ρ ≤ ρ + β0 := by dsimp [β0]; linarith
        exact mul_le_mul_of_nonneg_right hρle (sq_nonneg δ)
      exact div_le_div_of_nonneg_right hle (le_of_lt hn_pos)
    exact lt_of_lt_of_le (by dsimp [β0]; simpa using hs1) hs2
  have hleg1 := strictQuad_leg1_joined hn A u ρ β0
    (strictQuadSet_of_tuple A ⟨hA_symm, hA_pos, hA_unit, hA_card⟩)
    hu_pos hu_unit hρ hβ0_pos hAu hAquad hβlt
  have hpen := strictQuad_pencil_joins_hub hn u (ρ + β0) β0 δ
    hu_pos hu_unit hu_le1 (by dsimp [β0]; positivity) hβ0_pos hαβ hβlt
    hδ_pos hδ_u hδ_hub hβsmall
  exact JoinedIn.trans hleg1 hpen

theorem strictQuad_preconnected_set (n : ℕ) (hn : 0 < n) :
    IsPathConnected (strictQuadSet n) := by
  rw [isPathConnected_iff]
  constructor
  · exact ⟨(fun i j : Fin n => if i = j then (1 / 2 : ℝ) else 1), hub_end_mem hn⟩
  · intro A hA B hB
    exact JoinedIn.trans (strictQuad_joined_hub hn A hA)
      (JoinedIn.symm (strictQuad_joined_hub hn B hB))

theorem strictQuad_preconnected (n : ℕ) (hn : 0 < n) :
    IsPathConnected {A : Matrix (Fin n) (Fin n) ℝ |
      A.IsSymm ∧ (∀ i j, 0 < A i j) ∧ IsUnit A ∧
        (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card = 1} := by
  simpa [strictQuadSet] using strictQuad_preconnected_set n hn

end Commons.LinearAlgebra.Matrix
