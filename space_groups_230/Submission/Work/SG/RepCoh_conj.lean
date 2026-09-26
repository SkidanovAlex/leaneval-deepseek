import Mathlib
import Submission.Work.SG.SGRepDefs

/-!
# `RepCoh_conj`: the certificate congruence is clause 2 of `IntEquiv`

`Data.ConjCert.chk` — the kernel-checked certificate attached to the `h`-th `H¹` class of the
`j`-th arithmetic class — says, after multiplying by `n²`, that

`n z_k(img i) - n U (B[i] y) - σ + (U Aᵢ U⁻¹) σ ≡ 0 (mod n²)`

where `z_k = repZ[k]` is the target cocycle, `U = Uc j h`, `σ = sigc j h` and
`img i = imgc j h i` is the index of `U Aᵢ U⁻¹`.  Dividing by `n²`, this is exactly the
integral-equivalence congruence for the cocycles `srcZ j h` (which evaluates on `e j i` to
`applyB(B[i], y)/n`) and `tgtZ j h` (which evaluates on `e j i` to `repZ[k][i]/n`), with
translation `s = σ / n²`.  That is clause 2 of `IntEquiv`.  Clause 1 — that `U` conjugates the
point group `arithRep j` onto itself — comes from the same certificate together with the fact
that `U` is invertible (it has determinant `1`).
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem
open scoped Matrix

/-! ## Abbreviations for the certificate of the `h`-th class -/

/-- `n²`, the modulus of the certificate congruence. -/
private def rcConjNsq (j : Fin 73) : ℤ := ((RC.Ad j).n : ℤ) * ((RC.Ad j).n : ℤ)

/-- The vector whose coordinates are the left-hand side of the certificate congruence, for the
generator coordinate vector `Y` and the target cocycle values `Z`. -/
private def rcConjW (j : Fin 73) (h : ℕ) (i : ℕ) (Z Y : Data.V3) : Data.V3 :=
  Data.V3.add
    (Data.V3.sub
      (Data.V3.sub (Data.V3.smul ((RC.Ad j).n : ℤ) Z)
        (Data.V3.smul ((RC.Ad j).n : ℤ) (Data.M3.mulV (RC.Uc j h) Y)))
      (RC.sigc j h))
    (Data.M3.mulV (RC.eM j i) (RC.sigc j h))

/-! ## Membership in `arithRep j` through the certified table -/

/-- Membership in `arithRep j` via the indexed element table `e j ·`. -/
private theorem rcConj_memE (j : Fin 73) (A : IMat) :
    A ∈ arithRep j ↔ ∃ i, i < RC.N j ∧ RC.e j i = A := by
  have hmain : A ∈ arithRep j ↔ ∃ i, i < (RC.Ad j).n ∧ RC.e j i = A := by
    have harith : arithRep j = {A | ∃ e ∈ (RC.Ad j).elems, A = e.toIMat} := arithRep_eq_data j
    rw [harith]
    constructor
    · rintro ⟨ee, hee, hA⟩
      obtain ⟨i, hi, hii⟩ := List.mem_iff_getElem.mp hee
      refine ⟨i, ?_, ?_⟩
      · have hlen := RC.Ad_elems_len j; omega
      · simp only [RC.e, RC.eM]
        rw [List.getD_eq_getElem _ _ hi, hii, hA]
    · rintro ⟨i, hi, rfl⟩
      have hlen := RC.Ad_elems_len j
      refine ⟨RC.eM j i, ?_, ?_⟩
      · simp only [RC.eM]
        rw [List.getD_eq_getElem _ _ (by omega)]
        exact List.getElem_mem _
      · rfl
  simpa only [RC.N] using hmain

/-! ## Bridging matrix-vector products -/

/-- An integer matrix applied to an integer vector, as a real matrix-vector product. -/
private theorem rcConj_intVec (A : Data.M3) (w : Data.V3) :
    ((A.toIMat).map (Int.cast : ℤ → ℝ)).mulVec (intVec w.toFun) = intVec (A.mulV w).toFun := by
  funext c
  fin_cases c <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Data.M3.toIMat, Data.M3.mulV,
      Data.V3.toFun, intVec]

/-- An integer matrix applied to a vector with a common real denominator. -/
private theorem rcConj_bridge (A : Data.M3) (w : Data.V3) (r : ℝ) :
    ((A.toIMat).map (Int.cast : ℤ → ℝ)).mulVec (fun c => (w.toFun c : ℝ) / r)
      = fun c => ((A.mulV w).toFun c : ℝ) / r := by
  have h1 : (fun c : Fin 3 => (w.toFun c : ℝ) / r) = r⁻¹ • intVec w.toFun := by
    funext c; simp [intVec, div_eq_mul_inv, mul_comm]
  rw [h1, Matrix.mulVec_smul, rcConj_intVec]
  funext c
  simp [intVec, div_eq_mul_inv, mul_comm]

/-! ## The certificate congruence, divided by `n²` -/

/-- Componentwise expansion of `rcConjW`. -/
private theorem rcConj_coord (j : Fin 73) (h : ℕ) (i : ℕ) (Z Y : Data.V3) (c : Fin 3) :
    ((rcConjW j h i Z Y).toFun c : ℝ)
      = ((RC.Ad j).n : ℝ) * (Z.toFun c : ℝ)
        - ((RC.Ad j).n : ℝ) * ((Data.M3.mulV (RC.Uc j h) Y).toFun c : ℝ)
        - (RC.sigc j h).toFun c
        + ((Data.M3.mulV (RC.eM j i) (RC.sigc j h)).toFun c : ℝ) := by
  fin_cases c <;>
    simp only [rcConjW, Data.V3.add, Data.V3.sub, Data.V3.smul, Data.V3.toFun, Data.M3.mulV] <;>
    push_cast <;> ring

/-- `n²` as a real number. -/
private theorem rcConj_NsqR (j : Fin 73) : (rcConjNsq j : ℝ) = ((RC.Ad j).n : ℝ) ^ 2 := by
  rw [rcConjNsq]; push_cast; ring

/-- The certificate congruence, divided by `n²`: the left hand side is the value of the target
cocycle and the right hand side is the integral-equivalence congruence of the source cocycle. -/
private theorem rcConj_alg (j : Fin 73) (h : ℕ) (i : ℕ) (Z Y : Data.V3)
    (hdvd : Data.V3.dvd (rcConjNsq j) (rcConjW j h i Z Y) = true) :
    (fun c => (Z.toFun c : ℝ) / ((RC.Ad j).n : ℝ))
      = (fun c => ((Data.M3.mulV (RC.Uc j h) Y).toFun c : ℝ) / ((RC.Ad j).n : ℝ))
        + (fun c => (RC.sigc j h).toFun c / ((RC.Ad j).n : ℝ) ^ 2)
        - (fun c => ((Data.M3.mulV (RC.eM j i) (RC.sigc j h)).toFun c : ℝ) / ((RC.Ad j).n : ℝ) ^ 2)
        + intVec (fun c => (rcConjW j h i Z Y).toFun c / rcConjNsq j) := by
  funext c
  have hdvdc : rcConjNsq j ∣ (rcConjW j h i Z Y).toFun c :=
    (RC.dvd_iff_toFun _ _).mp hdvd c
  have hn : ((RC.Ad j).n : ℝ) ≠ 0 := by
    have := RC.N_pos j
    exact_mod_cast this.ne'
  have hm : (rcConjNsq j : ℝ) ≠ 0 := by rw [rcConj_NsqR]; positivity
  have hcast : (((rcConjW j h i Z Y).toFun c / rcConjNsq j : ℤ) : ℝ)
      = ((rcConjW j h i Z Y).toFun c : ℝ) / (rcConjNsq j : ℝ) :=
    Int.cast_div hdvdc hm
  have hWc := rcConj_coord j h i Z Y c
  simp only [Pi.add_apply, Pi.sub_apply, intVec]
  rw [hcast, rcConj_NsqR, hWc]
  field_simp
  ring

/-! ## Clause 2 from the certificate -/

/-- Clause 2 of `IntEquiv` for the cocycles `srcZ j h` and `tgtZ j h`, read off the certificate
congruence. -/
private theorem rcConj_clause2 (j : Fin 73) (h : ℕ) (i : ℕ) (hi : i < (RC.Ad j).n)
    (himg_lt : RC.imgc j h i < (RC.Ad j).n)
    (hconj : (RC.Uc j h).toIMat * RC.e j i * ((RC.Uc j h).toIMat)⁻¹ = RC.e j (RC.imgc j h i))
    (hdvd : Data.V3.dvd (((RC.Ad j).n : ℤ) * ((RC.Ad j).n : ℤ))
        (Data.V3.add
          (Data.V3.sub
            (Data.V3.sub
              (Data.V3.smul ((RC.Ad j).n : ℤ) (RC.repZvec (RC.tgtK j h) (RC.imgc j h i)))
              (Data.V3.smul ((RC.Ad j).n : ℤ)
                (Data.M3.mulV (RC.Uc j h)
                  (Data.applyB ((Data.bmats (RC.Ad j)).getD i []) ((RC.Cd j).reps.getD h [])))))
            (RC.sigc j h))
          (Data.M3.mulV (RC.eM j (RC.imgc j h i)) (RC.sigc j h))) = true) :
    ∃ n' : Fin 3 → ℤ,
      RC.tauOnP j (RC.tgtZ j h) ((RC.Uc j h).toIMat * RC.e j i * ((RC.Uc j h).toIMat)⁻¹)
        = ((RC.Uc j h).toIMat.map (Int.cast : ℤ → ℝ)).mulVec
            (RC.tauOnP j (RC.srcZ j h) (RC.e j i))
          + (fun c => (RC.sigc j h).toFun c / ((RC.Ad j).n : ℝ) ^ 2)
          - (((RC.Uc j h).toIMat * RC.e j i * ((RC.Uc j h).toIMat)⁻¹).map
              (Int.cast : ℤ → ℝ)).mulVec
              (fun c => (RC.sigc j h).toFun c / ((RC.Ad j).n : ℝ) ^ 2)
          + intVec n' := by
  have hdvd' : Data.V3.dvd (rcConjNsq j)
      (rcConjW j h (RC.imgc j h i) (RC.repZvec (RC.tgtK j h) (RC.imgc j h i))
        (Data.applyB ((Data.bmats (RC.Ad j)).getD i []) ((RC.Cd j).reps.getD h []))) = true :=
    hdvd
  refine ⟨fun c => (rcConjW j h (RC.imgc j h i) (RC.repZvec (RC.tgtK j h) (RC.imgc j h i))
      (Data.applyB ((Data.bmats (RC.Ad j)).getD i []) ((RC.Cd j).reps.getD h []))).toFun c
        / rcConjNsq j, ?_⟩
  rw [hconj, RC.tauOnP_e j (RC.tgtZ j h) (RC.imgc j h i) himg_lt,
    RC.tauOnP_e j (RC.srcZ j h) i hi]
  simp only [RC.e]
  unfold RC.srcZ RC.tgtZ
  rw [rcConj_bridge, rcConj_bridge]
  exact rcConj_alg j h (RC.imgc j h i) (RC.repZvec (RC.tgtK j h) (RC.imgc j h i))
    (Data.applyB ((Data.bmats (RC.Ad j)).getD i []) ((RC.Cd j).reps.getD h [])) hdvd'

/-! ## Clause 1: `U` conjugates the point group to itself -/

/-- Cancellation of a conjugation sandwich. -/
private lemma rcConj_sandwich {M : Type*} [Monoid M] {U V X Y : M} (hVU : V * U = 1)
    (h : U * X * V = U * Y * V) : X = Y := by
  have key : ∀ Z : M, V * (U * Z * V) * U = Z := by
    intro Z
    calc V * (U * Z * V) * U = (V * U) * Z * (V * U) := by simp only [mul_assoc]
      _ = Z := by simp only [hVU, one_mul, mul_one]
  have h' : V * (U * X * V) * U = V * (U * Y * V) * U := by rw [h]
  rw [key X, key Y] at h'
  exact h'

/-- Clause 1 of `IntEquiv`: conjugation by `U = Uc j h` permutes `arithRep j`. -/
private theorem rcConj_part1 (j : Fin 73) (h : ℕ)
    (hUU : Data.M3.mul (RC.Uc j h) ((RC.Cd j).targets.getD h default).Uinv = Data.M3.one)
    (hall : ∀ i, i < (RC.Ad j).n →
      RC.imgc j h i < (RC.Ad j).n ∧
      Data.M3.mul (Data.M3.mul (RC.Uc j h) (RC.eM j i))
        ((RC.Cd j).targets.getD h default).Uinv = RC.eM j (RC.imgc j h i)) :
    ∀ A, A ∈ arithRep j ↔ ∃ B ∈ arithRep j,
      A = (RC.Uc j h).toIMat * B * ((RC.Uc j h).toIMat)⁻¹ := by
  have hUV : (RC.Uc j h).toIMat * ((RC.Cd j).targets.getD h default).Uinv.toIMat = 1 := by
    rw [← CZ.toIMat_mul, hUU, CZ.toIMat_one]
  have hUinv : ((RC.Uc j h).toIMat)⁻¹ = ((RC.Cd j).targets.getD h default).Uinv.toIMat :=
    Matrix.inv_eq_right_inv hUV
  have hVU : ((RC.Cd j).targets.getD h default).Uinv.toIMat * (RC.Uc j h).toIMat = 1 :=
    mul_eq_one_comm.mp hUV
  have hVU' : ((RC.Uc j h).toIMat)⁻¹ * (RC.Uc j h).toIMat = 1 := by rw [hUinv]; exact hVU
  have hconj : ∀ i, i < (RC.Ad j).n →
      (RC.Uc j h).toIMat * RC.e j i * ((RC.Uc j h).toIMat)⁻¹ = RC.e j (RC.imgc j h i) := by
    intro i hi
    have h3 := (hall i hi).2
    rw [hUinv]
    simp only [RC.e]
    rw [← CZ.toIMat_mul, ← CZ.toIMat_mul, h3]
  have hinj : ∀ i i', i < (RC.Ad j).n → i' < (RC.Ad j).n → RC.imgc j h i = RC.imgc j h i' → i = i' := by
    intro i i' hi hi' heq
    have h1 := hconj i hi
    have h2 := hconj i' hi'
    rw [heq] at h1
    exact RC.e_inj j hi hi' (rcConj_sandwich hVU' (h1.trans h2.symm))
  have hsurj : ∀ i, i < (RC.Ad j).n → ∃ i', i' < (RC.Ad j).n ∧ RC.imgc j h i' = i := by
    intro i hi
    have hf : Function.Injective
        (fun k : Fin ((RC.Ad j).n) =>
          (⟨RC.imgc j h k.val, (hall k.val k.isLt).1⟩ : Fin ((RC.Ad j).n))) := by
      intro k k' hkk
      exact Fin.ext (hinj k.val k'.val k.isLt k'.isLt (congrArg Fin.val hkk))
    obtain ⟨k', hk'⟩ := Finite.surjective_of_injective hf ⟨i, hi⟩
    exact ⟨k'.val, k'.isLt, congrArg Fin.val hk'⟩
  intro A
  constructor
  · intro hA
    obtain ⟨i, hi, hAi⟩ := (rcConj_memE j A).mp hA
    obtain ⟨i', hi', hii'⟩ := hsurj i hi
    refine ⟨RC.e j i', RC.e_mem j i' hi', ?_⟩
    rw [← hAi, ← hii', hconj i' hi']
  · rintro ⟨B, hB, hAB⟩
    obtain ⟨i, hi, hBi⟩ := (rcConj_memE j B).mp hB
    rw [hAB, ← hBi, hconj i hi]
    exact RC.e_mem j (RC.imgc j h i) (hall i hi).1

/-! ## Unpacking the kernel-checked certificate -/

/-- The facts exported by `Data.ConjCert.chk` for the `h`-th class: `U · Uinv = 1`, and for each
table index `i` the image index `imgc j h i` with `U Aᵢ U⁻¹ = A_{img i}` and the congruence
multiplied by `n²`. -/
private theorem rcConj_unpack (j : Fin 73) (h : ℕ) (hh : h < (RC.Cd j).reps.length) :
    Data.M3.mul (RC.Uc j h) ((RC.Cd j).targets.getD h default).Uinv = Data.M3.one ∧
    (∀ i, i < (RC.Ad j).n →
      RC.imgc j h i < (RC.Ad j).n ∧
      Data.M3.mul (Data.M3.mul (RC.Uc j h) (RC.eM j i))
        ((RC.Cd j).targets.getD h default).Uinv = RC.eM j (RC.imgc j h i) ∧
      Data.V3.dvd (((RC.Ad j).n : ℤ) * ((RC.Ad j).n : ℤ))
        (Data.V3.add
          (Data.V3.sub
            (Data.V3.sub
              (Data.V3.smul ((RC.Ad j).n : ℤ) (RC.repZvec (RC.tgtK j h) (RC.imgc j h i)))
              (Data.V3.smul ((RC.Ad j).n : ℤ)
                (Data.M3.mulV (RC.Uc j h)
                  (Data.applyB ((Data.bmats (RC.Ad j)).getD i []) ((RC.Cd j).reps.getD h [])))))
            (RC.sigc j h))
          (Data.M3.mulV (RC.eM j (RC.imgc j h i)) (RC.sigc j h))) = true) := by
  have hchk := RC.Cd_tgt_chk j h hh
  simp only [Data.ConjCert.chk, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.all_eq_true, List.mem_range] at hchk
  obtain ⟨⟨hUU, himglen⟩, hall⟩ := hchk
  refine ⟨hUU, fun i hi => ?_⟩
  obtain ⟨⟨hlt, hmul⟩, hdvd⟩ := hall i hi
  refine ⟨hlt, hmul, ?_⟩
  have hzk : RC.repZvec (RC.tgtK j h) (RC.imgc j h i)
      = (Data.repZ.getD ((RC.Cd j).targets.getD h default).k []).getD
          (RC.imgc j h i) Data.V3.zero := by
    unfold RC.repZvec RC.tgtK
    simp only [dif_pos hh]
  rw [hzk]
  simpa only [RC.Uc, RC.sigc, RC.imgc, RC.eM] using hdvd

/-! ## The main statement -/

theorem RepCoh_conj (j : Fin 73) (h : ℕ) (hh : h < (Work.SG.RC.Cd j).reps.length) :
    IntEquiv (arithRep j) (Work.SG.RC.tauOnP j (Work.SG.RC.srcZ j h)) (arithRep j) (Work.SG.RC.tauOnP j (Work.SG.RC.tgtZ j h))
      (Work.SG.RC.Uc j h).toIMat (fun c => (Work.SG.RC.sigc j h).toFun c / ((Work.SG.RC.Ad j).n : ℝ) ^ 2) := by
  obtain ⟨hUU, hall⟩ := rcConj_unpack j h hh
  have hallA : ∀ i, i < (RC.Ad j).n → RC.imgc j h i < (RC.Ad j).n ∧
      Data.M3.mul (Data.M3.mul (RC.Uc j h) (RC.eM j i))
        ((RC.Cd j).targets.getD h default).Uinv = RC.eM j (RC.imgc j h i) :=
    fun i hi => ⟨(hall i hi).1, (hall i hi).2.1⟩
  have hallD : ∀ i, i < (RC.Ad j).n →
      Data.V3.dvd (((RC.Ad j).n : ℤ) * ((RC.Ad j).n : ℤ))
        (Data.V3.add
          (Data.V3.sub
            (Data.V3.sub
              (Data.V3.smul ((RC.Ad j).n : ℤ) (RC.repZvec (RC.tgtK j h) (RC.imgc j h i)))
              (Data.V3.smul ((RC.Ad j).n : ℤ)
                (Data.M3.mulV (RC.Uc j h)
                  (Data.applyB ((Data.bmats (RC.Ad j)).getD i []) ((RC.Cd j).reps.getD h [])))))
            (RC.sigc j h))
          (Data.M3.mulV (RC.eM j (RC.imgc j h i)) (RC.sigc j h))) = true :=
    fun i hi => (hall i hi).2.2
  have hUV : (RC.Uc j h).toIMat * ((RC.Cd j).targets.getD h default).Uinv.toIMat = 1 := by
    rw [← CZ.toIMat_mul, hUU, CZ.toIMat_one]
  have hUinv : ((RC.Uc j h).toIMat)⁻¹ = ((RC.Cd j).targets.getD h default).Uinv.toIMat :=
    Matrix.inv_eq_right_inv hUV
  have hconj : ∀ i, i < (RC.Ad j).n →
      (RC.Uc j h).toIMat * RC.e j i * ((RC.Uc j h).toIMat)⁻¹ = RC.e j (RC.imgc j h i) := by
    intro i hi
    have h3 := (hallA i hi).2
    rw [hUinv]
    simp only [RC.e]
    rw [← CZ.toIMat_mul, ← CZ.toIMat_mul, h3]
  refine ⟨rcConj_part1 j h hUU hallA, ?_⟩
  intro B hB
  obtain ⟨i, hi, hBi⟩ := (rcConj_memE j B).mp hB
  rw [← hBi]
  exact rcConj_clause2 j h i hi (hallA i hi).1 (hconj i hi) (hallD i hi)

end Work.SG
