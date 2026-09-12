import Mathlib
import Mathlib.Algebra.Module.ZLattice.Covolume
import Mathlib.MeasureTheory.Group.GeometryOfNumbers
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.LinearAlgebra.BilinearForm.DualLattice
import Submission.LatticeDefs
import Submission.CovRadius

noncomputable section

open scoped BigOperators RealInnerProductSpace
open Module Submodule MeasureTheory MeasureTheory.Measure Metric Filter

/-! Proof of `Submission.GeoFinal.geo_core_main`. -/


namespace Submission.GeoFinal

open scoped Matrix
open Submission.LatticeDefs
open Submission.CovRadius


abbrev Euc (n : ℕ) := EuclideanSpace ℝ (Fin n)

def toE {n : ℕ} (f : Fin n → ℝ) : Euc n := WithLp.toLp 2 f

def eucEquiv (n : ℕ) : Euc n ≃ₗ[ℝ] (Fin n → ℝ) := WithLp.linearEquiv 2 ℝ (Fin n → ℝ)

lemma toE_apply {n : ℕ} (f : Fin n → ℝ) (j : Fin n) : (toE f) j = f j := by
  simp [toE]

def colv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) : Euc n := toE (A.col k)

lemma colv_eq_comp {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    colv A = (eucEquiv n).symm ∘ A.col := by
  funext k
  rfl

noncomputable def colBasis {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) [Invertible A] :
    Basis (Fin n) ℝ (Euc n) := by
  have hliF : LinearIndependent ℝ A.col := Matrix.linearIndependent_cols_of_invertible A
  have hli : LinearIndependent ℝ (colv A) := by
    rw [colv_eq_comp]
    exact hliF.map' (eucEquiv n).symm.toLinearMap (by simp)
  have hsurj : Function.Surjective (A.mulVec) := Matrix.mulVec_surjective_of_invertible A
  have hspF : span ℝ (Set.range A.col) = ⊤ := by
    rw [← Matrix.range_mulVecLin]
    exact LinearMap.range_eq_top.mpr (by simpa [Matrix.coe_mulVecLin] using hsurj)
  have hsp : ⊤ ≤ span ℝ (Set.range (colv A)) := by
    intro x hx
    let fx : Fin n → ℝ := (eucEquiv n) x
    have hxspanF : fx ∈ span ℝ (Set.range A.col) := by
      simp [hspF]
    have hxmap : x ∈ (span ℝ (Set.range A.col)).map (eucEquiv n).symm.toLinearMap := by
      refine ⟨fx, hxspanF, ?_⟩
      simp [fx]
    have hmap : (span ℝ (Set.range A.col)).map (eucEquiv n).symm.toLinearMap = span ℝ (Set.range (colv A)) := by
      rw [Submodule.map_span, colv_eq_comp]
      congr 1
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        rcases hz with ⟨k, rfl⟩
        exact ⟨k, rfl⟩
      · rintro ⟨k, rfl⟩
        refine ⟨A.col k, ⟨k, rfl⟩, rfl⟩
    rwa [hmap] at hxmap
  exact Basis.mk hli hsp

@[simp]
lemma colBasis_apply {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) [Invertible A] (k : Fin n) :
    (colBasis A k : Euc n) = colv A k := by
  simp [colBasis]

lemma finrank_Euc (n : ℕ) : finrank ℝ (Euc n) = n := by
  simp [Euc]

lemma inner_colv {n : ℕ} (A M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    ⟪colv A i, colv M j⟫ = ∑ r : Fin n, A r i * M r j := by
  rw [PiLp.inner_apply]
  simp [colv, toE, mul_comm]

lemma abs_coord_le_norm {n : ℕ} (x : Euc n) (i : Fin n) : |x i| ≤ ‖x‖ := by
  have hx2 : (x i) ^ 2 ≤ ‖x‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (fun j hj => sq_nonneg (x j)) (Finset.mem_univ i)
  have hsq := (sq_le_sq.mp hx2)
  rwa [abs_of_nonneg (norm_nonneg x)] at hsq

lemma sum_abs_le_card_norm {n : ℕ} (x : Euc n) :
    ∑ i : Fin n, |x i| ≤ (Fintype.card (Fin n) : ℝ) * ‖x‖ := by
  calc
    ∑ i : Fin n, |x i| ≤ ∑ i : Fin n, ‖x‖ := Finset.sum_le_sum (fun i hi => abs_coord_le_norm x i)
    _ = (Fintype.card (Fin n) : ℝ) * ‖x‖ := by simp

lemma euclForm_col_delta {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℝ) (h : Bᵀ * C = 1)
    (i j : Fin n) : euclForm (Euc n) (colv B i) (colv C j) = if j = i then (1 : ℝ) else 0 := by
  by_cases hij : j = i
  · have hsum : ⟪colv B i, colv C j⟫ = (Bᵀ * C) i j := by
      rw [inner_colv, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro r hr
      rfl
    have h1 : ⟪colv B i, colv C j⟫ = (1 : ℝ) := by
      calc
        ⟪colv B i, colv C j⟫ = (Bᵀ * C) i j := hsum
        _ = 1 := by rw [h, hij]; simp
    simpa [euclForm_apply, hij] using h1
  · have hsum : ⟪colv B i, colv C j⟫ = (Bᵀ * C) i j := by
      rw [inner_colv, Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro r hr
      rfl
    have hnij : ¬ i = j := fun h => hij h.symm
    have h0 : ⟪colv B i, colv C j⟫ = (0 : ℝ) := by
      calc
        ⟪colv B i, colv C j⟫ = (Bᵀ * C) i j := hsum
        _ = 0 := by rw [h]; simp [Matrix.one_apply, hnij]
    simpa [euclForm_apply, hij] using h0

lemma ldual_span_colC {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℝ) [Invertible C]
    (hprod : Bᵀ * C = 1) :
    ldual (Euc n) (span ℤ (Set.range (colBasis C))) = span ℤ (Set.range (colv B)) := by
  let bC : Basis (Fin n) ℝ (Euc n) := colBasis C
  have hspan1 : span ℤ (Set.range (colBasis C)) = span ℤ (Set.range bC) := by
    dsimp [bC]
  rw [hspan1]
  rw [ldual_span_basis bC]
  congr 1
  have hdb : ((euclForm (Euc n)).dualBasis (euclForm_nondegenerate (Euc n)) bC : Fin n → Euc n) =
      fun k => colv B k := by
    rw [LinearMap.BilinForm.dualBasis_eq_iff]
    intro i j
    have hbCj : (bC j : Euc n) = colv C j := by simp [bC]
    rw [hbCj]
    have hinner := euclForm_col_delta B C hprod i j
    simpa [euclForm_apply] using hinner
  exact congrArg Set.range hdb

lemma dual_min {n : ℕ} (B C : Matrix (Fin n) (Fin n) ℝ) [Invertible B] [Invertible C]
    (hprod : Bᵀ * C = 1)
    (hdual : ∀ d : Fin n → ℤ, d ≠ 0 → ∃ i : Fin n, (1 : ℝ) ≤ |∑ j : Fin n, B i j * (d j : ℝ)|) :
    ∀ ⦃y : Euc n⦄, y ∈ ldual (Euc n) (span ℤ (Set.range (colBasis C))) → y ≠ 0 → 1 ≤ ‖y‖ := by
  intro y hy hy0
  have hspan_eq : span ℤ (Set.range (colBasis B)) = span ℤ (Set.range (colv B)) := by
    exact congrArg (fun f : Fin n → Euc n => span ℤ (Set.range f))
      (funext (fun k => colBasis_apply B k))
  have hyB : y ∈ span ℤ (Set.range (colv B)) := by
    rw [← ldual_span_colC B C hprod]
    exact hy
  have hybB : y ∈ span ℤ (Set.range (colBasis B)) := by
    rwa [hspan_eq]
  have hmem := (Module.Basis.mem_span_iff_repr_mem ℤ (colBasis B) y).mp hybB
  let z : Fin n → ℤ := fun i => Classical.choose (hmem i)
  have hz : ∀ i, (z i : ℝ) = (colBasis B).repr y i := by
    intro i
    exact Classical.choose_spec (hmem i)
  have hyeq : y = ∑ k : Fin n, (z k : ℝ) • colv B k := by
    calc
      y = ∑ k : Fin n, ((colBasis B).repr y) k • ((colBasis B) k : Euc n) :=
        (Basis.sum_repr (colBasis B) y).symm
      _ = ∑ k : Fin n, (z k : ℝ) • colv B k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hz k, colBasis_apply]
  have hz0 : z ≠ 0 := by
    intro hzeq
    apply hy0
    rw [hyeq]
    simp [hzeq]
  rcases hdual z hz0 with ⟨i, hi⟩
  have hyi : y i = ∑ j : Fin n, B i j * (z j : ℝ) := by
    rw [hyeq]
    simp [colv, toE, mul_comm]
  have h1 : (1 : ℝ) ≤ |y i| := by
    rw [hyi]
    exact hi
  have hnorm : |y i| ≤ ‖y‖ := abs_coord_le_norm y i
  linarith

/-- integer coordinates of a lattice point -/
lemma intColRep {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) [Invertible M] {x : Euc n}
    (hx : x ∈ span ℤ (Set.range (colBasis M))) :
    ∃ z : Fin n → ℤ, x = toE (M *ᵥ fun k => (z k : ℝ)) := by
  have hmem := (Module.Basis.mem_span_iff_repr_mem ℤ (colBasis M) x).mp hx
  let z : Fin n → ℤ := fun i => Classical.choose (hmem i)
  have hz : ∀ i, (z i : ℝ) = (colBasis M).repr x i := by
    intro i
    exact Classical.choose_spec (hmem i)
  refine ⟨z, ?_⟩
  have hx2 : x = ∑ k : Fin n, (z k : ℝ) • colv M k := by
    calc
      x = ∑ k : Fin n, ((colBasis M).repr x) k • ((colBasis M) k : Euc n) :=
        (Basis.sum_repr (colBasis M) x).symm
      _ = ∑ k : Fin n, (z k : ℝ) • colv M k := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hz k, colBasis_apply]
  ext i
  calc
    x i = (∑ k : Fin n, (z k : ℝ) • colv M k) i := by rw [hx2]
    _ = (M *ᵥ fun k => (z k : ℝ)) i := by
      simp [colv, toE, Matrix.mulVec_eq_sum, mul_comm]

noncomputable def invertible_of_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (h : M.det ≠ 0) :
    Invertible M := by
  letI : Invertible M.det := invertibleOfNonzero h
  exact Matrix.invertibleOfDetInvertible M

lemma pow_bound {a : ℝ} (ha : 2 ≤ a) : a * (a ^ 5 + 1) ≤ a ^ 100 := by
  have hge1 : (1 : ℝ) ≤ a := by linarith
  have h0 : 0 ≤ a := by linarith
  have hprod : a * a ^ 5 = a ^ 6 := by
    calc a * a ^ 5 = a ^ 5 * a := by rw [mul_comm]
         _ = a ^ 6 := by simpa using (pow_succ a 5).symm
  have ha_le_a6 : a ≤ a ^ 6 := by
    have := pow_le_pow_right₀ hge1 (by omega : (1 : ℕ) ≤ 6)
    simpa using this
  have h94 : (2 : ℝ) ≤ a ^ 94 := by
    calc (2 : ℝ) = (2 : ℝ) ^ 1 := by simp
         _ ≤ a ^ 1 := pow_le_pow_left₀ (by norm_num : 0 ≤ (2 : ℝ)) ha 1
         _ ≤ a ^ 94 := pow_le_pow_right₀ hge1 (by omega : 1 ≤ 94)
  have h2mul : (2 : ℝ) * a ^ 6 ≤ a ^ 100 := by
    calc (2 : ℝ) * a ^ 6 ≤ a ^ 94 * a ^ 6 := mul_le_mul_of_nonneg_right h94 (pow_nonneg h0 6)
         _ = a ^ 100 := by exact (pow_add a 94 6).symm
  nlinarith [hprod, ha_le_a6, h2mul]

lemma n_mul_n5p1_le {n : ℕ} (hn : 2 ≤ n) : (n : ℝ) * ((n : ℝ) ^ 5 + 1) ≤ (n : ℝ) ^ 100 := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  exact pow_bound hnR
/-- main -/
theorem geo_core_main (n : ℕ) (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℝ)
    (hB : B.det ≠ 0)
    (hdual : ∀ d : Fin n → ℤ, d ≠ 0 → ∃ i : Fin n, (1 : ℝ) ≤ |∑ j : Fin n, B i j * (d j : ℝ)|) :
    ∃ C0 : ℝ, 0 < C0 ∧ C0 ≤ 100 ∧
      ∀ p : Fin n → ℝ,
        ∃ β : Fin n → ℝ,
          (∀ i : Fin n, ∃ z : ℤ, (p i - ∑ j : Fin n, B j i * β j) = (z : ℝ)) ∧
          (∑ i : Fin n, |β i|) ≤ (n : ℝ) ^ C0 := by
  classical
  by_cases h2n : 2 ≤ n
  · -- general case n ≥ 2
    let A : Matrix (Fin n) (Fin n) ℝ := Bᵀ
    let C : Matrix (Fin n) (Fin n) ℝ := A⁻¹
    haveI : Invertible B := invertible_of_det B hB
    have hAt : A.det ≠ 0 := by
      dsimp [A]
      simpa [Matrix.det_transpose] using hB
    haveI : Invertible A := invertible_of_det A hAt
    have huA : IsUnit A.det := isUnit_iff_ne_zero.mpr hAt
    have hAC : A * C = 1 := by
      dsimp [C]
      exact Matrix.mul_nonsing_inv A huA
    have hCA : C * A = 1 := by
      dsimp [C]
      exact Matrix.nonsing_inv_mul A huA
    have hprod : Bᵀ * C = 1 := by simpa [A] using hAC
    haveI : Invertible C := ⟨A, hprod, hCA⟩
    have hmin : ∀ ⦃y : Euc n⦄,
        y ∈ ldual (Euc n) (span ℤ (Set.range (colBasis C))) → y ≠ 0 → 1 ≤ ‖y‖ := by
      intro y hy hy0
      exact dual_min B C hprod hdual hy hy0
    refine ⟨100, by norm_num, by norm_num, ?_⟩
    intro p
    let x : Euc n := toE (C *ᵥ p)
    rcases coverRadius_bound (E := Euc n) (span ℤ (Set.range (colBasis C))) hmin x with
      ⟨m, hmL, hb⟩
    rcases intColRep (M := C) (x := m) hmL with ⟨zc, hzc⟩
    let zf : Fin n → ℝ := fun k => (zc k : ℝ)
    have hBx : Bᵀ *ᵥ (fun j : Fin n => x j) = p := by
      have hxc : (fun j : Fin n => x j) = C *ᵥ p := by
        funext j
        dsimp [x]
        rw [toE_apply]
      calc
        Bᵀ *ᵥ (fun j : Fin n => x j) = Bᵀ *ᵥ (C *ᵥ p) := by rw [hxc]
        _ = (Bᵀ * C) *ᵥ p := by rw [← Matrix.mulVec_mulVec]
        _ = (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ p := by rw [hprod]
        _ = p := by simp
    have hmc : (fun j : Fin n => m j) = C *ᵥ zf := by
      funext j
      rw [hzc]
      rw [toE_apply]
    have hmfun : Bᵀ *ᵥ (fun j : Fin n => m j) = zf := by
      calc
        Bᵀ *ᵥ (fun j : Fin n => m j) = Bᵀ *ᵥ (C *ᵥ zf) := by rw [hmc]
        _ = (Bᵀ * C) *ᵥ zf := by rw [← Matrix.mulVec_mulVec]
        _ = (1 : Matrix (Fin n) (Fin n) ℝ) *ᵥ zf := by rw [hprod]
        _ = zf := by simp
    let β : Fin n → ℝ := fun j => (x - m) j
    have hβeq : Bᵀ *ᵥ (fun j : Fin n => β j) = fun i : Fin n => p i - (zf i) := by
      calc
        Bᵀ *ᵥ (fun j : Fin n => β j) = Bᵀ *ᵥ ((fun j : Fin n => x j) - (fun j : Fin n => m j)) := rfl
        _ = Bᵀ *ᵥ (fun j : Fin n => x j) - Bᵀ *ᵥ (fun j : Fin n => m j) := by
          rw [Matrix.mulVec_sub]
        _ = p - zf := by rw [hBx, hmfun]
    refine ⟨β, ?_, ?_⟩
    · intro i
      refine ⟨zc i, ?_⟩
      have hcoord : (Bᵀ *ᵥ (fun j : Fin n => β j)) i = ∑ j : Fin n, B j i * β j := by
        simp [Matrix.mulVec_eq_sum, mul_comm]
      have hβi : (Bᵀ *ᵥ (fun j : Fin n => β j)) i = p i - (zf i) := by
        rw [hβeq]
      have hmain : p i - (Bᵀ *ᵥ (fun j : Fin n => β j)) i = (zf i) := by
        rw [hβi]
        ring
      rw [hcoord] at hmain
      simpa [zf] using hmain
    · have hb' : ‖x - m‖ ≤ (n : ℝ) ^ 5 + 1 := by
        have hfin : (finrank ℝ (Euc n) : ℝ) = (n : ℝ) := by rw [finrank_Euc]
        simpa [hfin] using hb
      have hsum1 : ∑ i : Fin n, |β i| ≤ (Fintype.card (Fin n) : ℝ) * ‖x - m‖ := by
        simpa [β] using sum_abs_le_card_norm (x - m)
      have hsum2 : ∑ i : Fin n, |β i| ≤ (n : ℝ) * ((n : ℝ) ^ 5 + 1) := by
        calc
          ∑ i : Fin n, |β i| ≤ (Fintype.card (Fin n) : ℝ) * ‖x - m‖ := hsum1
          _ = (n : ℝ) * ‖x - m‖ := by simp
          _ ≤ (n : ℝ) * ((n : ℝ) ^ 5 + 1) :=
            mul_le_mul_of_nonneg_left hb' (by positivity)
      calc
        ∑ i : Fin n, |β i| ≤ (n : ℝ) * ((n : ℝ) ^ 5 + 1) := hsum2
        _ ≤ (n : ℝ) ^ 100 := n_mul_n5p1_le h2n
        _ = (n : ℝ) ^ (100 : ℝ) := by exact (Real.rpow_natCast (n : ℝ) 100).symm
  · -- case n = 1
    have hn1 : n = 1 := by omega
    subst n
    refine ⟨100, by norm_num, by norm_num, ?_⟩
    intro p
    let b : ℝ := B 0 0
    have hb0 : (1 : ℝ) ≤ |B 0 0| := by
      let d : Fin 1 → ℤ := fun _ => 1
      have hd0 : d ≠ 0 := by
        intro hd
        have h := congrFun hd 0
        norm_num at h
      rcases hdual d hd0 with ⟨i, hi⟩
      have hi' : (1 : ℝ) ≤ |B i 0| := by
        simpa [d] using hi
      have hi0 : i = (0 : Fin 1) := by
        fin_cases i <;> rfl
      simpa [hi0] using hi'
    have hb1 : (1 : ℝ) ≤ |b| := by simpa [b] using hb0
    have hb_ne : b ≠ 0 := by
      intro hbe
      have : |b| = 0 := by rw [hbe]; norm_num
      linarith
    rcases Submission.CovRec.exists_int_close (p 0) with ⟨z0, hz0⟩
    let β : Fin 1 → ℝ := fun _ => (p 0 - (z0 : ℝ)) / b
    refine ⟨β, ?_, ?_⟩
    · intro i
      have hi0 : i = (0 : Fin 1) := by fin_cases i <;> rfl
      rw [hi0]
      refine ⟨z0, ?_⟩
      have hsingle : (∑ j : Fin 1, B j 0 * β j) = B 0 0 * β 0 := by simp
      rw [hsingle]
      have hβ0 : β 0 = (p 0 - (z0 : ℝ)) / b := rfl
      have hbz : b * β 0 = p 0 - (z0 : ℝ) := by
        rw [hβ0]
        field_simp [hb_ne]
      rw [hbz]
      ring
    · have hz0' : |p 0 - (z0 : ℝ)| ≤ (1 / 2 : ℝ) := hz0
      have hβ0 : |β 0| ≤ (1 : ℝ) := by
        have hβe : |β 0| = |p 0 - (z0 : ℝ)| / |b| := by
          simp [β]
          rw [abs_div]
        have hdvd : |p 0 - (z0 : ℝ)| / |b| ≤ (1 / 2) / (1 : ℝ) :=
          div_le_div₀ (by norm_num : 0 ≤ (1 / 2 : ℝ)) hz0' (by positivity : 0 < (1 : ℝ)) hb1
        calc
          |β 0| = |p 0 - (z0 : ℝ)| / |b| := hβe
          _ ≤ (1 / 2) / (1 : ℝ) := hdvd
          _ = 1 / 2 := by norm_num
          _ ≤ (1 : ℝ) := by norm_num
      have hbound1 : (∑ i : Fin 1, |β i|) ≤ (1 : ℝ) := by
        calc
          (∑ i : Fin 1, |β i|) = |β 0| := by simp
          _ ≤ (1 : ℝ) := hβ0
      have hpow : ((1 : ℕ) : ℝ) ^ (100 : ℝ) = 1 := by
        calc
          ((1 : ℕ) : ℝ) ^ (100 : ℝ) = ((1 : ℕ) : ℝ) ^ 100 := Real.rpow_natCast ((1 : ℕ) : ℝ) 100
          _ = 1 := by norm_num
      rw [hpow]
      exact hbound1



end Submission.GeoFinal
