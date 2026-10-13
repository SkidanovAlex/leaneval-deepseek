/-
  Area `WilC4aRW`: real simultaneous Weierstrass preparation.

  This is the shared vocabulary for the area.  It fixes:

  * `cplxIncl` — the coordinatewise inclusion `ℝ^N ↪ ℂ^N`;
  * `ofRealAmbient` — real points of `Ambient n = (Fin n → ℂ) × ℂ` (lean-pool's
    WPT coordinate space), as the image of `ℝ^{n+1}` under the "snoc" splitting;
  * `conjVec`, `conjAmb` — coordinatewise complex conjugation;
  * `snocCLM` — the continuous `ℂ`-linear map `Ambient n →L[ℂ] (Fin (n+1) → ℂ)`,
    `(y, z) ↦ Fin.snoc y z`;
  * the bridge between the frozen `WilkiesDesign.CG.C4a.wpoly` and lean-pool's
    `ClassicalComplexWPT.preparedPolynomial`.

  Every lemma handed out inside this area is stated against these definitions.
-/
import Submission.Work.Wilkies.CG.C4a.Spec
import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.Main
import LeanPool.LocalComplexGeometry.ClassicalComplexWPT.ExactOrder
import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical Filter Topology
open scoped Topology BigOperators ComplexConjugate

namespace Work.WilC4aRW

open ClassicalComplexWPT

/-! ## 1. The coordinatewise inclusion `ℝ^N → ℂ^N` -/

/-- The coordinatewise inclusion of `ℝ^N` into `ℂ^N`. -/
def cplxIncl {N : ℕ} (x : Fin N → ℝ) : Fin N → ℂ := fun i => (x i : ℂ)

@[simp] theorem cplxIncl_apply {N : ℕ} (x : Fin N → ℝ) (i : Fin N) : cplxIncl x i = (x i : ℂ) := rfl

@[simp] theorem cplxIncl_zero {N : ℕ} : cplxIncl (0 : Fin N → ℝ) = 0 := by
  ext i; simp [cplxIncl]

theorem cplxIncl_injective {N : ℕ} : Function.Injective (cplxIncl : (Fin N → ℝ) → Fin N → ℂ) := by
  intro x y h
  ext i
  have := congrFun h i
  simpa [cplxIncl] using this

@[simp] theorem cplxIncl_add {N : ℕ} (x y : Fin N → ℝ) :
    cplxIncl (x + y) = cplxIncl x + cplxIncl y := by
  ext i; simp [cplxIncl]

@[simp] theorem cplxIncl_neg {N : ℕ} (x : Fin N → ℝ) : cplxIncl (-x) = -cplxIncl x := by
  ext i; simp [cplxIncl]

@[simp] theorem cplxIncl_sub {N : ℕ} (x y : Fin N → ℝ) :
    cplxIncl (x - y) = cplxIncl x - cplxIncl y := by
  ext i; simp [cplxIncl]

@[simp] theorem cplxIncl_smul {N : ℕ} (c : ℝ) (x : Fin N → ℝ) :
    cplxIncl (c • x) = (c : ℂ) • cplxIncl x := by
  ext i; simp [cplxIncl]

@[simp] theorem cplxIncl_sum {N : ℕ} {M : Type*} (s : Finset M) (f : M → Fin N → ℝ) :
    cplxIncl (∑ m ∈ s, f m) = ∑ m ∈ s, cplxIncl (f m) := by
  ext i; simp [cplxIncl]

/-- The inclusion as a continuous real-linear map. -/
def cplxInclCLM (N : ℕ) : (Fin N → ℝ) →L[ℝ] (Fin N → ℂ) :=
  ContinuousLinearMap.pi fun i => Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) i)

@[simp] theorem cplxInclCLM_apply {N : ℕ} (x : Fin N → ℝ) : cplxInclCLM N x = cplxIncl x := rfl

@[simp] theorem cplxInclCLM_zero (N : ℕ) : cplxInclCLM N (0 : Fin N → ℝ) = 0 := by
  rw [cplxInclCLM_apply, cplxIncl_zero]

@[simp] theorem cplxIncl_single {N : ℕ} (i : Fin N) (c : ℝ) :
    cplxIncl (Pi.single i c) = Pi.single i (c : ℂ) := by
  ext j
  rcases eq_or_ne j i with rfl | h
  · simp [cplxIncl]
  · simp [cplxIncl, Pi.single_eq_of_ne h]

@[simp] theorem cplxIncl_oneHot {N : ℕ} (i : Fin N) :
    cplxIncl (Pi.single i (1 : ℝ)) = Pi.single i (1 : ℂ) := cplxIncl_single i 1

/-- Conjugation on `ℂ^N`. -/
def conjVec {N : ℕ} (y : Fin N → ℂ) : Fin N → ℂ := fun i => conj (y i)

@[simp] theorem conjVec_apply {N : ℕ} (y : Fin N → ℂ) (i : Fin N) : conjVec y i = conj (y i) := rfl

@[simp] theorem conjVec_ofReal {N : ℕ} (x : Fin N → ℝ) : conjVec (cplxIncl x) = cplxIncl x := by
  ext i; simp [conjVec, cplxIncl]

@[simp] theorem conjVec_zero {N : ℕ} : conjVec (0 : Fin N → ℂ) = 0 := by
  ext i; simp [conjVec]

theorem conjVec_involutive {N : ℕ} : Function.Involutive (conjVec : (Fin N → ℂ) → Fin N → ℂ) :=
  fun y => by ext i; simp [conjVec]

/-! ## 3. Real points of `Ambient n` and the `snoc` splitting -/

/-- Real points of `Base n = ℂ^n`. -/
abbrev ofRealBase {n : ℕ} (y : Fin n → ℝ) : Base n := cplxIncl y

/-- The real points of the ambient space `Ambient n = Base n × ℂ`, read through the
`(init, last)` splitting of `ℝ^{n+1}`. -/
def ofRealAmbient {n : ℕ} (x : Fin (n + 1) → ℝ) : Ambient n :=
  (cplxIncl (Fin.init x), (x (Fin.last n) : ℂ))

@[simp] theorem ofRealAmbient_fst {n : ℕ} (x : Fin (n + 1) → ℝ) :
    (ofRealAmbient x).1 = cplxIncl (Fin.init x) := rfl

@[simp] theorem ofRealAmbient_snd {n : ℕ} (x : Fin (n + 1) → ℝ) :
    (ofRealAmbient x).2 = (x (Fin.last n) : ℂ) := rfl

@[simp] theorem ofRealAmbient_zero {n : ℕ} : ofRealAmbient (0 : Fin (n + 1) → ℝ) = 0 := by
  ext <;> simp [ofRealAmbient, cplxIncl, Fin.init]

/-- `ofRealAmbient` as a continuous real-linear map. -/
def initCLM (n : ℕ) : (Fin (n + 1) → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i : Fin n => ContinuousLinearMap.proj (R := ℝ) i.castSucc

def lastCLM (n : ℕ) : (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
  ContinuousLinearMap.proj (R := ℝ) (Fin.last n)

def ofRealAmbientCLM (n : ℕ) : (Fin (n + 1) → ℝ) →L[ℝ] Ambient n :=
  ((cplxInclCLM n).comp (initCLM n)).prod (Complex.ofRealCLM.comp (lastCLM n))

theorem ofRealAmbientCLM_apply {n : ℕ} (x : Fin (n + 1) → ℝ) :
    ofRealAmbientCLM n x = ofRealAmbient x := rfl

@[simp] theorem ofRealAmbientCLM_zero (n : ℕ) :
    ofRealAmbientCLM n (0 : Fin (n + 1) → ℝ) = 0 := by
  rw [ofRealAmbientCLM_apply, ofRealAmbient_zero]

/-- Coordinatewise conjugation on `Ambient n`. -/
def conjAmb {n : ℕ} (x : Ambient n) : Ambient n := (conjVec x.1, conj x.2)

@[simp] theorem conjAmb_fst {n : ℕ} (x : Ambient n) : (conjAmb x).1 = conjVec x.1 := rfl

@[simp] theorem conjAmb_snd {n : ℕ} (x : Ambient n) : (conjAmb x).2 = conj x.2 := rfl

@[simp] theorem conjAmb_ofRealAmbient {n : ℕ} (x : Fin (n + 1) → ℝ) :
    conjAmb (ofRealAmbient x) = ofRealAmbient x := by
  ext <;> simp [conjAmb, ofRealAmbient, cplxIncl, conjVec]

@[simp] theorem conjAmb_zero {n : ℕ} : conjAmb (0 : Ambient n) = 0 := by
  ext <;> simp [conjAmb, conjVec]

/-- The continuous `ℂ`-linear "snoc" map `(y, z) ↦ Fin.snoc y z` from the WPT
coordinate space to `Fin (n+1) → ℂ`. -/
def snocCLM (n : ℕ) : Ambient n →L[ℂ] (Fin (n + 1) → ℂ) :=
  ContinuousLinearMap.pi fun i : Fin (n + 1) =>
    Fin.lastCases (ContinuousLinearMap.snd ℂ (Fin n → ℂ) ℂ)
      (fun j => (ContinuousLinearMap.proj (R := ℂ) j).comp
        (ContinuousLinearMap.fst ℂ (Fin n → ℂ) ℂ)) i

theorem snocCLM_apply_last (n : ℕ) (x : Ambient n) : snocCLM n x (Fin.last n) = x.2 := by
  simp [snocCLM]

theorem snocCLM_apply_castSucc (n : ℕ) (x : Ambient n) (j : Fin n) :
    snocCLM n x j.castSucc = x.1 j := by
  simp [snocCLM]

@[simp] theorem snocCLM_apply_ofRealAmbient {n : ℕ} (x : Fin (n + 1) → ℝ) :
    snocCLM n (ofRealAmbient x) = cplxIncl x := by
  funext i
  refine Fin.lastCases ?_ ?_ i
  · simp [snocCLM, ofRealAmbient]
  · intro j
    simp [snocCLM, ofRealAmbient, Fin.init]

/-! ## 4. From the frozen `wpoly` to lean-pool's `preparedPolynomial` -/

/-- Complexification of the real Weierstrass polynomial: the polynomial with the
same real coefficients, read on real points, is the `ℂ`-valued prepared polynomial. -/
theorem preparedPolynomial_complexify {n d : ℕ} (a : Fin d → (Fin n → ℝ) → ℝ)
    (x : Fin (n + 1) → ℝ) :
    preparedPolynomial d (fun j y => (a j (fun k => (y k).re) : ℂ)) (ofRealAmbient x) =
      ((WilkiesDesign.CG.C4a.wpoly a x : ℝ) : ℂ) := by
  have hcoeff : (fun k : Fin n => ((cplxIncl (Fin.init x)) k).re) = Fin.init x := by
    funext k; simp [cplxIncl]
  simp only [preparedPolynomial, ofRealAmbient_fst, ofRealAmbient_snd, hcoeff,
    WilkiesDesign.CG.C4a.wpoly, Complex.ofReal_add, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_pow]

theorem preparedPolynomial_ofReal_re {n d : ℕ} (a : Fin d → (Fin n → ℝ) → ℝ)
    (x : Fin (n + 1) → ℝ) :
    (preparedPolynomial d (fun j y => (a j (fun k => (y k).re) : ℂ)) (ofRealAmbient x)).re =
      WilkiesDesign.CG.C4a.wpoly a x := by
  rw [preparedPolynomial_complexify, Complex.ofReal_re]

/-! ## 5. Restrictions of complex-analytic functions to real points -/

theorem analyticAt_ofRealBase {n : ℕ} {A : Base n → ℂ} (hA : AnalyticAt ℂ A 0) :
    AnalyticAt ℝ (fun y : Fin n → ℝ => A (cplxIncl y)) 0 := by
  have := (AnalyticAt.restrictScalars (𝕜 := ℝ) hA).compContinuousLinearMap
    (u := cplxInclCLM n) (x := 0)
  simpa [Function.comp_def] using this

theorem analyticAt_ofRealBase_re {n : ℕ} {A : Base n → ℂ} (hA : AnalyticAt ℂ A 0) :
    AnalyticAt ℝ (fun y : Fin n → ℝ => (A (cplxIncl y)).re) 0 := by
  simpa [Function.comp_def] using
    (ContinuousLinearMap.analyticAt Complex.reCLM _).comp (analyticAt_ofRealBase hA)

theorem analyticAt_ofRealAmbient {n : ℕ} {A : Ambient n → ℂ} (hA : AnalyticAt ℂ A 0) :
    AnalyticAt ℝ (fun x : Fin (n + 1) → ℝ => A (ofRealAmbient x)) 0 := by
  have := (AnalyticAt.restrictScalars (𝕜 := ℝ) hA).compContinuousLinearMap
    (u := ofRealAmbientCLM n) (x := 0)
  simpa [Function.comp_def, ofRealAmbientCLM_apply] using this

theorem analyticAt_ofRealAmbient_re {n : ℕ} {A : Ambient n → ℂ} (hA : AnalyticAt ℂ A 0) :
    AnalyticAt ℝ (fun x : Fin (n + 1) → ℝ => (A (ofRealAmbient x)).re) 0 := by
  simpa [Function.comp_def] using
    (ContinuousLinearMap.analyticAt Complex.reCLM _).comp (analyticAt_ofRealAmbient hA)

end Work.WilC4aRW
