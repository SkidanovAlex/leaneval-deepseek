import Mathlib
import Submission.Work.MotAS.ASRulingMainAux
import Submission.Work.MotAS.ASRulingVec
import Submission.Work.MotAS.ASRul.kernel_basis
import Submission.Work.MotAS.ASRulV2.Defs
import Submission.Work.MotAS.ASRulV2M.hparam_kernel
import Submission.Work.MotAS.ASRulV2M.fwVecAS2_three_notMem_x
import Submission.Work.MotAS.CensusAS2Aux
import Submission.Work.MotAS.CensusLinAS
import Submission.Work.MotAS.ASChart2Defs
import Submission.Work.MotAS.ASChartGeo
import Submission.Work.MotAS.KleinTwScalarAS
import Submission.Work.MotAS.KleinTwScalarASv
import Submission.Work.MotAS.ASResidual
import Submission.Work.MotAS.CensusAS2
import Submission.Work.MotAS.AK
import Submission.Work.MotAS.ASRulV2M.injective_of_trdeg_of_subfield_closure
import Submission.Work.MotAS.ASRulV2M.trdeg_quotient_add_height
import Submission.Work.MotAS.ASRulV2M.trdeg_span_prime_eq_two
import Submission.Work.MotAS.ASRulV2M.height_radical_ZIAS
import Submission.Work.MotA.coheight_eq_one_iff

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Work.MotAS.RouteZ

open MvPolynomial

/-- **The AS stereographic source point** (local copy of `Work.MotAS.ASrulYv`; the hub
`ASRulingMain.lean` is not importable here because it is *below* this module). -/
noncomputable def ASrulYv (K : Type*) [CommRing K] (a b : K) : Fin 5 → MvPolynomial (Fin 3) K :=
  kleinStereoAS (MvPolynomial.C a) (MvPolynomial.C b) (pAS0 K) (Work.MotK.chart3 K)

theorem ASrulYv_apply (K : Type*) [Field K] (a b : K) (i : Fin 5) :
    ASrulYv K a b i
      = kleinQAS (MvPolynomial.C a) (MvPolynomial.C b) (Work.MotK.chart3 K) * (pAS0 K i)
        + MvPolynomial.C (2 * (a ^ 2 - a * b - b ^ 2)) * (Work.MotK.chart3 K i) := by
  have h := congrFun (kleinStereoAS_pAS0_chart3 (K := K) a b) i
  simpa [ASrulYv, azA] using h

theorem ASrulYv_four (K : Type*) [Field K] (a b : K) :
    ASrulYv K a b 4 = MvPolynomial.C (2 * (a ^ 2 - a * b - b ^ 2)) := by
  rw [ASrulYv_apply]
  simp [pAS0, Work.MotK.chart3]

theorem ASrulYv_ch3 (K : Type*) [Field K] (a b : K) (j : Fin 3) :
    ASrulYv K a b (asCh3 j) = ASrulYv K a b 4 * (MvPolynomial.X j) := by
  rw [ASrulYv_apply, ASrulYv_four]
  fin_cases j <;>
    (simp [pAS0, Work.MotK.chart3, asCh3] <;> ring)

/-- Naturality of the first AS ruling vector under `MvPolynomial.map`. -/
theorem map_kbRv_s {K L : Type*} [Field K] [Field L] (φ : K →+* L) (a b g : K) (i : Fin 5) :
    MvPolynomial.map φ (ASRul.kbRv a b g i) = ASRul.kbRv (φ a) (φ b) (φ g) i := by
  fin_cases i <;> simp [ASRul.kbRv, map_ofNat]

theorem map_kbRw_s {K L : Type*} [Field K] [Field L] (φ : K →+* L) (a b g : K) (i : Fin 5) :
    MvPolynomial.map φ (ASRul.kbRw a b g i) = ASRul.kbRw (φ a) (φ b) (φ g) i := by
  fin_cases i <;> simp [ASRul.kbRw, map_ofNat]

theorem map_zcubAS_s {K L : Type*} [Field K] [Field L] (φ : K →+* L) (a b g : K) (j : Fin 5) :
    MvPolynomial.map φ (zcubAS a b g j) = zcubAS (φ a) (φ b) (φ g) j := by
  have h := congrFun (KleinTwScalarAS_map_kleinRAS
    (φ := MvPolynomial.map φ) (a := MvPolynomial.C a) (b := MvPolynomial.C b)
    (g := MvPolynomial.C g)
    (z := (![1, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 0] :
      Fin 5 → MvPolynomial (Fin 3) K))) j
  rw [MvPolynomial.map_C, MvPolynomial.map_C, MvPolynomial.map_C] at h
  have hz : (fun i => MvPolynomial.map φ ((![1, MvPolynomial.X 0, MvPolynomial.X 1,
        MvPolynomial.X 2, 0] : Fin 5 → MvPolynomial (Fin 3) K) i))
      = (![1, MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, 0] :
          Fin 5 → MvPolynomial (Fin 3) L) := by
    funext i
    fin_cases i <;> simp
  rw [hz] at h
  exact h.symm

/-- Clearing denominators in the parametrisation of the AS ruling line. -/
theorem div_key_s {F : Type*} [Field F] (A B W p R S : F)
    (hA : A ≠ 0) (hB : B ≠ 0) (hW : W ≠ 0) :
    (A * B ^ 2 * W) * (p * R / (A * B * W) + S / (A * B ^ 2 * W)) = R * (B * p) + S := by
  field_simp

/-- The coordinate ring of the AS residual curve in the chart `(1,X₀,X₁,X₂,0)`, as a
*reducible* `abbrev` (so instance search sees through it). -/
abbrev RZA (K : Type*) [Field K] (a b g : K) : Type _ :=
  MvPolynomial (Fin 3) K ⧸ Ideal.radical (ZIAS a b g)

theorem isFractionRing_of_closure_range_s {K L : Type*} [Field K] [Field L]
    [Algebra K L] (S : Subalgebra K L)
    (h : Subfield.closure (Set.range (algebraMap S L)) = ⊤) : IsFractionRing S L := by
  refine IsFractionRing.of_field S L fun z => ?_
  have hz : z ∈ Subfield.closure (Set.range (algebraMap S L)) := by
    rw [h]; exact Subfield.mem_top z
  rw [Subfield.mem_closure_iff] at hz
  obtain ⟨y, hy, w, hw, hyw⟩ := hz
  have hclos : Subring.closure (Set.range (algebraMap S L)) = S.toSubring := by
    refine le_antisymm ?_ ?_
    · rw [Subring.closure_le]
      rintro x ⟨r, rfl⟩
      exact Subalgebra.mem_toSubring.mpr r.2
    · intro x hx
      exact Subring.subset_closure ⟨⟨x, Subalgebra.mem_toSubring.mp hx⟩, rfl⟩
  have hyR : y ∈ S := Subalgebra.mem_toSubring.mp (by rw [← hclos]; exact hy)
  have hwR : w ∈ S := Subalgebra.mem_toSubring.mp (by rw [← hclos]; exact hw)
  exact ⟨⟨y, hyR⟩, ⟨w, hwR⟩, by simpa using hyw.symm⟩

theorem fractionRing_algEquiv_of_closure_eq_top_s {K L : Type*} [Field K] [Field L]
    [Algebra K L] (S : Subalgebra K L)
    (h : Subfield.closure (Set.range (algebraMap S L)) = ⊤) :
    Nonempty (FractionRing S ≃ₐ[K] L) := by
  haveI : IsFractionRing S L := isFractionRing_of_closure_range_s S h
  exact ⟨AlgEquiv.restrictScalars K
    (IsLocalization.algEquiv (nonZeroDivisors S) (FractionRing S) L)⟩

/-! ## Copies of the hub lemmas (the hub `ASRulingMain.lean` lies below this module) -/

/-- `AmatAS2` is linear in its base-point argument. -/
theorem AmatAS2_smul {R : Type*} [CommRing R] (a b g c : R) (x : Fin 5 → R) :
    AmatAS2 a b g (c • x) = c • AmatAS2 a b g x := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    (simp [AmatAS2, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul] <;> ring)

/-- The ruling system of a scaled base point. -/
theorem AmatAS2_mulVec_smul {R : Type*} [CommRing R] (a b g c : R) (x y : Fin 5 → R) :
    Matrix.mulVec (AmatAS2 a b g (c • x)) y = c • Matrix.mulVec (AmatAS2 a b g x) y := by
  rw [AmatAS2_smul, Matrix.smul_mulVec]

/-- The five cubics `zcubAS` of the residual curve, evaluated at a base point `(u,v,w)`, are the
components of `kleinRAS a b g ![1,u,v,w,0]`. -/
theorem zcubAS_eval_eq {K : Type*} [Field K] (a b g : K) (u v w : K) (j : Fin 5) :
    MvPolynomial.eval ![u, v, w] (zcubAS a b g j) = kleinRAS a b g ![1, u, v, w, 0] j := by
  have h := congrFun (KleinTwScalarAS_map_kleinRAS (MvPolynomial.eval ![u, v, w])
    (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (asBaseVec K)) j
  rw [MvPolynomial.eval_C, MvPolynomial.eval_C, MvPolynomial.eval_C] at h
  have hv : (fun i => (MvPolynomial.eval ![u, v, w]) (asBaseVec K i)) = ![1, u, v, w, 0] := by
    funext i
    fin_cases i <;> simp [asBaseVec, Work.MotK.chart3]
  rw [hv] at h
  have hz : zcubAS a b g j
      = kleinRAS (MvPolynomial.C a) (MvPolynomial.C b) (MvPolynomial.C g) (asBaseVec K) j := rfl
  rw [hz]
  exact h.symm

/-- **Homogeneity descent for the base curve**. -/
theorem kleinRAS_chart_eq_zero {K : Type*} [Field K] (a b g c0 c1 c2 c3 : K) (hc0 : c0 ≠ 0)
    (h : kleinRAS a b g ![c0, c1, c2, c3, 0] = 0) :
    kleinRAS a b g ![1, c1 / c0, c2 / c0, c3 / c0, 0] = 0 := by
  have hz : (fun i => c0 * (![1, c1 / c0, c2 / c0, c3 / c0, 0] : Fin 5 → K) i)
      = ![c0, c1, c2, c3, 0] := by
    funext i
    fin_cases i <;> (simp <;> field_simp)
  funext i
  have hhom := congrFun (kleinRAS_smul a b g c0 ![1, c1 / c0, c2 / c0, c3 / c0, 0]) i
  rw [hz, h] at hhom
  exact (mul_eq_zero.mp hhom.symm).resolve_left (pow_ne_zero 3 hc0)

/-- The evaluation of the third component of `kbRv`: `(2a-b)(a+2b)·w²`. -/
theorem eval_kbRv_three {K : Type*} [Field K] (a b g u v w : K) :
    MvPolynomial.eval ![u, v, w] (ASRul.kbRv a b g 3)
      = (2 * a - b) * (a + 2 * b) * w ^ 2 := by
  have h : ASRul.kbRv a b g 3
      = MvPolynomial.C (2 * a - b) * MvPolynomial.C (a + 2 * b) * (MvPolynomial.X 2) ^ 2 := by
    simp [ASRul.kbRv]
  rw [h]
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] <;> ring

/-- The evaluation of the fourth component of `kbRw`: `(2a-b)(a+2b)²·w²`. -/
theorem eval_kbRw_four {K : Type*} [Field K] (a b g u v w : K) :
    MvPolynomial.eval ![u, v, w] (ASRul.kbRw a b g 4)
      = (2 * a - b) * (a + 2 * b) ^ 2 * w ^ 2 := by
  have h : ASRul.kbRw a b g 4
      = MvPolynomial.C ((a + 2 * b) ^ 2) * MvPolynomial.C (2 * a - b) * (MvPolynomial.X 2) ^ 2 := by
    simp [ASRul.kbRw]
  rw [h]
  simp only [MvPolynomial.eval_mul, MvPolynomial.eval_pow, MvPolynomial.eval_C,
    MvPolynomial.eval_X, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] <;> ring

end Work.MotAS.RouteZ
