import Mathlib
import Submission.Work.ZassenhausSuzuki.SingerModelDefs
import Submission.Work.Models.PSL2.pslEquiv
import Submission.Work.Hering.AppVIII.QuadExtNorm

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The Singer cycle in `SL(2, F)`: the Frobenius involution, the norm/power identity, and the
centralizer of `qalphaMat`

This file collects the vocabulary shared by the several lemmas that build the Singer cycle
`V = singerSubgroup ε` (the image of the norm-one subgroup of `L = QuadExt F ε`) inside
`SL(2, F)`, `F` a finite field of characteristic two:

* `frobSL ε` — the matrix `τ = !![1, ε; 0, 1]` of the Frobenius `x ↦ x ^ |F|` of `L` in the
  `F`-basis `(1, α)`; it satisfies `τ² = 1` and conjugates the regular representation by the
  Frobenius (`frobSL_conj_quadAlgHom`);
* `alphaSL ε` — the matrix `qalphaMat ε` of `α`, which lies in the Singer cycle;
* `norm_eq_pow` — the field norm of `L/F` is the `(|F| + 1)`-st power map;
* `mem_singerSubgroup_of_coe_eq` — an element of `SL(2,F)` whose matrix is
  `a • 1 + b • qalphaMat ε` is the regular representation of a norm-one element, hence lies
  in the Singer cycle.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option linter.unnecessarySeqFocus false

namespace Work.ZassenhausSuzuki.SingerModelCycle

open Work.Hering.AppVIII
open Work.ZassenhausSuzuki

variable {F : Type*} [Field F] [CharP F 2] [Finite F]

/-! ## The Frobenius matrix `τ` -/

/-- The matrix of the `F`-linear Frobenius map `x ↦ x ^ |F|` of `QuadExt F ε` in the basis
`(1, α)`: it sends `1 ↦ 1` and `α ↦ α + ε`. -/
def frobSL (ε : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, ε; 0, 1], by simp [Matrix.det_fin_two]⟩

@[simp] theorem frobSL_coe (ε : F) :
    (frobSL ε : Matrix (Fin 2) (Fin 2) F) = !![1, ε; 0, 1] := rfl

theorem frobSL_mul_self (ε : F) : frobSL ε * frobSL ε = 1 := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two,
      CharTwo.add_self_eq_zero]

theorem frobSL_mat_mul_self (ε : F) :
    (frobSL ε : Matrix (Fin 2) (Fin 2) F) * (frobSL ε : Matrix (Fin 2) (Fin 2) F) = 1 := by
  have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
    (g : Matrix (Fin 2) (Fin 2) F)) (frobSL_mul_self ε)
  simpa using h

theorem frobSL_inv (ε : F) : (frobSL ε)⁻¹ = frobSL ε :=
  inv_eq_of_mul_eq_one_right (frobSL_mul_self ε)

/-! ## The matrix of `α` -/

/-- The unit `α` of `L = QuadExt F ε`, with inverse `α + ε`. -/
noncomputable def qalphaUnit (ε : F) : (QuadExt F ε)ˣ :=
  ⟨qalpha F ε, qalpha F ε + algebraMap F (QuadExt F ε) ε,
    by
      rw [mul_add, qalpha_sq, mul_comm (qalpha F ε) (algebraMap F (QuadExt F ε) ε)]
      rw [show (algebraMap F (QuadExt F ε) ε * qalpha F ε + 1)
          + algebraMap F (QuadExt F ε) ε * qalpha F ε
          = 1 + (algebraMap F (QuadExt F ε) ε * qalpha F ε
              + algebraMap F (QuadExt F ε) ε * qalpha F ε) by abel,
        quadExt_add_self, add_zero]
    , by
      rw [add_mul, qalpha_sq]
      rw [show (algebraMap F (QuadExt F ε) ε * qalpha F ε + 1)
          + algebraMap F (QuadExt F ε) ε * qalpha F ε
          = 1 + (algebraMap F (QuadExt F ε) ε * qalpha F ε
              + algebraMap F (QuadExt F ε) ε * qalpha F ε) by abel,
        quadExt_add_self, add_zero]⟩

theorem qalpha_ne_zero (ε : F) : qalpha F ε ≠ 0 := by
  intro h0
  have h := qalpha_sq F ε
  rw [h0] at h
  simp only [mul_zero, zero_mul, zero_add] at h
  haveI : Nontrivial (QuadExt F ε) := quadExt_nontrivial F ε
  exact one_ne_zero h.symm

@[simp] theorem qalphaUnit_coe (ε : F) :
    ((qalphaUnit ε : (QuadExt F ε)ˣ) : QuadExt F ε) = qalpha F ε := rfl

/-- The norm of `α` is `1` (`α` is a root of `X² + εX + 1`). -/
theorem norm_qalpha (ε : F) : Algebra.norm F (qalpha F ε) = 1 := by
  rw [← det_quadAlgHom ε (qalpha F ε), quadAlgHom_qalpha, qalphaMat_det]

theorem qalphaUnit_mem_normOne (ε : F) : qalphaUnit ε ∈ normOne ε := by
  rw [mem_normOne_iff, qalphaUnit_coe, norm_qalpha]

/-- The matrix of `α` as an element of `SL(2, F)`. -/
noncomputable def alphaSL (ε : F) : Matrix.SpecialLinearGroup (Fin 2) F :=
  normOneToSL ε ⟨qalphaUnit ε, qalphaUnit_mem_normOne ε⟩

theorem alphaSL_coe (ε : F) :
    (alphaSL ε : Matrix (Fin 2) (Fin 2) F) = qalphaMat ε := by
  change (quadAlgHom ε) (qalpha F ε) = qalphaMat ε
  rw [quadAlgHom_qalpha]

/-- `α` lies in the Singer cycle. -/
theorem alphaSL_mem_singerSubgroup (ε : F) : alphaSL ε ∈ singerSubgroup ε :=
  ⟨_, rfl⟩

/-! ## The regular representation in coordinates -/

theorem quadAlgHom_smul_one_add (ε : F) (a b : F) :
    (quadAlgHom ε) (algebraMap F (QuadExt F ε) a + algebraMap F (QuadExt F ε) b * qalpha F ε)
      = a • (1 : Matrix (Fin 2) (Fin 2) F) + b • qalphaMat ε := by
  rw [map_add, map_mul, AlgHom.commutes, AlgHom.commutes, quadAlgHom_qalpha]
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  simp

/-- The determinant of `a • 1 + b • qalphaMat ε` is the norm form `a² + εab + b²`. -/
theorem det_smul_one_add_qalphaMat (ε : F) (a b : F) :
    (a • (1 : Matrix (Fin 2) (Fin 2) F) + b • qalphaMat ε).det
      = a * a + ε * (a * b) + b * b := by
  have hmat : a • (1 : Matrix (Fin 2) (Fin 2) F) + b • qalphaMat ε
      = !![a, b; b, a + b * ε] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [qalphaMat, Matrix.add_apply, Matrix.smul_apply]
  rw [hmat, Matrix.det_fin_two]
  simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  rw [CharTwo.sub_eq_add]
  ring

/-- The matrices commuting with `qalphaMat ε` are exactly the elements of the image of the
regular representation: the two-dimensional algebra `{a • 1 + b • qalphaMat ε}`. -/
theorem eq_smul_one_add_of_mul_qalphaMat_comm {ε : F} {X : Matrix (Fin 2) (Fin 2) F}
    (h : X * qalphaMat ε = qalphaMat ε * X) :
    X = X 0 0 • (1 : Matrix (Fin 2) (Fin 2) F) + X 0 1 • qalphaMat ε := by
  have h1 : X 0 1 = X 1 0 := by
    have hh := congrFun (congrFun h 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, qalphaMat] using hh
  have h2 : X 1 1 = X 0 0 + ε * X 0 1 := by
    have hh := congrFun (congrFun h 0) 1
    simp only [Matrix.mul_apply, Fin.sum_univ_two, qalphaMat, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply, Matrix.empty_val',
      Fin.isValue, Matrix.cons_val_fin_one, mul_one, one_mul, zero_mul, mul_zero,
      zero_add, add_zero] at hh
    rw [← hh, mul_comm (X 0 1) ε]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.smul_apply, qalphaMat, h1, h2, mul_comm]

theorem exists_eq_smul_one_add_of_mul_qalphaMat_comm {ε : F} {X : Matrix (Fin 2) (Fin 2) F}
    (h : X * qalphaMat ε = qalphaMat ε * X) :
    ∃ a b : F, X = a • (1 : Matrix (Fin 2) (Fin 2) F) + b • qalphaMat ε :=
  ⟨_, _, eq_smul_one_add_of_mul_qalphaMat_comm h⟩

/-! ## The norm is the `(|F|+1)`-st power -/

/-- **The norm of the quadratic extension is the `(|F|+1)`-st power map.**  Equivalently
`x ^ |F|` is the nontrivial element of `Gal(L/F)`. -/
theorem norm_eq_pow {ε : F} (h : Anisotropic F ε) (x : QuadExt F ε) :
    algebraMap F (QuadExt F ε) (Algebra.norm F x) = x ^ (Nat.card F + 1) := by
  obtain ⟨p, hp⟩ := exists_repr F ε x
  obtain ⟨a, b⟩ := p
  rw [hp]
  haveI : Fact (Irreducible (quadPoly F ε)) := ⟨quadPoly_irreducible F h⟩
  rw [pow_succ', ← det_quadAlgHom, quadAlgHom_smul_one_add, det_smul_one_add_qalphaMat]
  exact (normRepr F h a b).symm

/-! ## The Frobenius conjugates the regular representation -/

theorem frobSL_mul_qalphaMat_mul_frobSL (ε : F) :
    (frobSL ε : Matrix (Fin 2) (Fin 2) F) * qalphaMat ε
        * (frobSL ε : Matrix (Fin 2) (Fin 2) F)
      = qalphaMat ε + ε • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [frobSL_coe, qalphaMat]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.add_apply, Matrix.smul_apply] <;>
    (have h : ε * ε + ε * ε = 0 := CharTwo.add_self_eq_zero _; linear_combination h)

/-- **`τ` conjugates the regular representation by the Frobenius**: for every `x : L`,
`τ φ(x) τ = φ(x ^ |F|)`. -/
theorem frobSL_conj_quadAlgHom {ε : F} (h : Anisotropic F ε) (x : QuadExt F ε) :
    (frobSL ε : Matrix (Fin 2) (Fin 2) F) * (quadAlgHom ε x)
        * (frobSL ε : Matrix (Fin 2) (Fin 2) F)
      = quadAlgHom ε (x ^ Nat.card F) := by
  haveI : Fact (Irreducible (quadPoly F ε)) := ⟨quadPoly_irreducible F h⟩
  obtain ⟨p, hp⟩ := exists_repr F ε x
  obtain ⟨a, b⟩ := p
  rw [hp]
  have hL : (frobSL ε : Matrix (Fin 2) (Fin 2) F)
      * (quadAlgHom ε ((algebraMap F (QuadExt F ε)) a
          + (algebraMap F (QuadExt F ε)) b * qalpha F ε))
      * (frobSL ε : Matrix (Fin 2) (Fin 2) F)
      = a • (1 : Matrix (Fin 2) (Fin 2) F)
        + b • (qalphaMat ε + ε • (1 : Matrix (Fin 2) (Fin 2) F)) := by
    rw [quadAlgHom_smul_one_add, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul]
    rw [Matrix.mul_one, frobSL_mat_mul_self, frobSL_mul_qalphaMat_mul_frobSL]
  have hpow : ((algebraMap F (QuadExt F ε)) a + (algebraMap F (QuadExt F ε)) b * qalpha F ε)
        ^ Nat.card F
      = (algebraMap F (QuadExt F ε)) a + (algebraMap F (QuadExt F ε)) b
          * (qalpha F ε + (algebraMap F (QuadExt F ε)) ε) := by
    haveI : Fintype F := Fintype.ofFinite F
    obtain ⟨n, -, hn⟩ := FiniteField.card F 2
    have hcard : Nat.card F = 2 ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card, hn]
    have ha : a ^ (2 ^ (n : ℕ)) = a := by
      rw [show (2 : ℕ) ^ (n : ℕ) = Fintype.card F from hn.symm]
      exact FiniteField.pow_card a
    have hb : b ^ (2 ^ (n : ℕ)) = b := by
      rw [show (2 : ℕ) ^ (n : ℕ) = Fintype.card F from hn.symm]
      exact FiniteField.pow_card b
    have hx : qalpha F ε ^ (2 ^ (n : ℕ)) = qalpha F ε + (algebraMap F (QuadExt F ε)) ε := by
      rw [← hcard]; exact qalpha_pow_natCard F h
    rw [hcard, add_pow_char_pow (p := 2) (n := (n : ℕ)), mul_pow, ← map_pow, ← map_pow,
      ha, hb, hx]
  have hR : (quadAlgHom ε)
      (((algebraMap F (QuadExt F ε)) a + (algebraMap F (QuadExt F ε)) b * qalpha F ε)
        ^ Nat.card F)
      = a • (1 : Matrix (Fin 2) (Fin 2) F)
        + b • (qalphaMat ε + ε • (1 : Matrix (Fin 2) (Fin 2) F)) := by
    rw [hpow, map_add, map_mul, AlgHom.commutes, AlgHom.commutes, map_add, AlgHom.commutes,
      quadAlgHom_qalpha]
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      Algebra.algebraMap_eq_smul_one]
    rw [Matrix.smul_mul, Matrix.one_mul]
  rw [hL, hR]

/-! ## Membership criterion for the Singer cycle -/

/-- An element of `SL(2,F)` whose matrix is `a • 1 + b • qalphaMat ε` lies in the Singer
cycle: it is the regular representation of the norm-one element `a + bα`. -/
theorem mem_singerSubgroup_of_coe_eq {ε : F} (h : Anisotropic F ε)
    {g : Matrix.SpecialLinearGroup (Fin 2) F} {a b : F}
    (hg : (g : Matrix (Fin 2) (Fin 2) F)
      = a • (1 : Matrix (Fin 2) (Fin 2) F) + b • qalphaMat ε) :
    g ∈ singerSubgroup ε := by
  set u : QuadExt F ε := algebraMap F (QuadExt F ε) a
    + algebraMap F (QuadExt F ε) b * qalpha F ε with hu
  have hnorm : Algebra.norm F u = 1 := by
    have hdet : Algebra.norm F u = (g : Matrix (Fin 2) (Fin 2) F).det := by
      rw [hu, ← det_quadAlgHom, quadAlgHom_smul_one_add, hg]
    rw [hdet, Matrix.SpecialLinearGroup.det_coe]
  have h1 : u ^ (Nat.card F + 1) = 1 := by
    rw [← norm_eq_pow h u, hnorm, map_one]
  let y : (QuadExt F ε)ˣ :=
    ⟨u, u ^ Nat.card F, by rw [← pow_succ']; exact h1, by rw [← pow_succ]; exact h1⟩
  have hyc : (y : QuadExt F ε) = u := rfl
  refine ⟨⟨y, ?_⟩, ?_⟩
  · rw [mem_normOne_iff, hyc]
    exact hnorm
  · apply Subtype.ext
    show (quadAlgHom ε) (y : QuadExt F ε) = (g : Matrix (Fin 2) (Fin 2) F)
    rw [hyc, hu, quadAlgHom_smul_one_add, hg]

/-! ## The norm-one subgroup, powers, and membership -/

/-- An element of the Singer cycle is the regular representation of `a + bα`. -/
theorem exists_eq_smul_one_add_of_mem_singerSubgroup {ε : F}
    {g : Matrix.SpecialLinearGroup (Fin 2) F} (hg : g ∈ singerSubgroup ε) :
    ∃ a b : F,
      (g : Matrix (Fin 2) (Fin 2) F) = a • (1 : Matrix (Fin 2) (Fin 2) F) + b • qalphaMat ε := by
  obtain ⟨x, rfl⟩ := hg
  obtain ⟨p, hp⟩ := exists_repr F ε (((x : ↥(normOne ε)) : (QuadExt F ε)ˣ) : QuadExt F ε)
  refine ⟨p.1, p.2, ?_⟩
  show (quadAlgHom ε) (((x : ↥(normOne ε)) : (QuadExt F ε)ˣ) : QuadExt F ε)
      = p.1 • (1 : Matrix (Fin 2) (Fin 2) F) + p.2 • qalphaMat ε
  rw [hp, quadAlgHom_smul_one_add]

/-- A unit of `L` has norm one iff it is a `(|F|+1)`-st root of unity. -/
theorem mem_normOne_iff_pow {ε : F} (h : Anisotropic F ε) (y : (QuadExt F ε)ˣ) :
    y ∈ normOne ε ↔ y ^ (Nat.card F + 1) = 1 := by
  haveI : Fact (Irreducible (quadPoly F ε)) := ⟨quadPoly_irreducible F h⟩
  have hinj : Function.Injective (algebraMap F (QuadExt F ε)) := RingHom.injective _
  rw [mem_normOne_iff]
  constructor
  · intro hy
    apply Units.ext
    show ((y : QuadExt F ε)) ^ (Nat.card F + 1) = 1
    rw [← norm_eq_pow h (y : QuadExt F ε), hy, map_one]
  · intro hy
    have h2 : ((y : QuadExt F ε)) ^ (Nat.card F + 1) = 1 := by
      rw [← Units.val_pow_eq_pow_val]
      exact congrArg (fun u : (QuadExt F ε)ˣ => (u : QuadExt F ε)) hy
    rw [← norm_eq_pow h (y : QuadExt F ε)] at h2
    exact hinj (by rw [h2, map_one])

/-- The `|F|`-th power of a norm-one unit is again norm one (it is its inverse). -/
theorem normOne_pow_mem {ε : F} (h : Anisotropic F ε) {y : (QuadExt F ε)ˣ}
    (hy : y ∈ normOne ε) : y ^ Nat.card F ∈ normOne ε := by
  rw [mem_normOne_iff_pow h]
  have hy1 : y ^ (Nat.card F + 1) = 1 := (mem_normOne_iff_pow h y).mp hy
  calc (y ^ Nat.card F) ^ (Nat.card F + 1) = (y ^ (Nat.card F + 1)) ^ Nat.card F := by
        rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    _ = 1 := by rw [hy1, one_pow]

/-- The `|F|`-th power of a norm-one element is its inverse (in `L`). -/
theorem normOne_pow_mul {ε : F} (h : Anisotropic F ε) {y : (QuadExt F ε)ˣ}
    (hy : y ∈ normOne ε) : (y : QuadExt F ε) ^ Nat.card F * (y : QuadExt F ε) = 1 := by
  have hy1 : y ^ (Nat.card F + 1) = 1 := (mem_normOne_iff_pow h y).mp hy
  have h2 := congrArg (fun u : (QuadExt F ε)ˣ => (u : QuadExt F ε)) hy1
  simpa [Units.val_pow_eq_pow_val, pow_succ] using h2

/-- The `|F|`-th power of a norm-one unit is its inverse (in `Lˣ`). -/
theorem normOne_pow_eq_inv {ε : F} (h : Anisotropic F ε) {y : (QuadExt F ε)ˣ}
    (hy : y ∈ normOne ε) : y ^ Nat.card F = y⁻¹ := by
  have hy1 : y ^ (Nat.card F + 1) = 1 := (mem_normOne_iff_pow h y).mp hy
  have h2 : y ^ Nat.card F * y = 1 := by rw [← pow_succ]; exact hy1
  exact eq_inv_of_mul_eq_one_left h2

end Work.ZassenhausSuzuki.SingerModelCycle
