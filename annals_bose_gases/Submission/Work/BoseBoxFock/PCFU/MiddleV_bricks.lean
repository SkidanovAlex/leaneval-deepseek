import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PCFU.UnivFrames
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.PCFU.MiddleV_bricks` — the elementary frame facts of `MiddleV`

`MiddleV` (`PCFU/UnivFrames.lean`) is the mirror (creation-slot) middle kernel of the cubic row,
whose `k`-sum runs over **all** labels (`univ`) while its `s`-sum runs over `excited`.  Its
four-channel value is `Work.BoseBoxFock.PCFU.MiddleV_eq_four`.  This module collects the
elementary bricks every channel of that derivation needs — the mirror twins of
`Middle_aux`/`Middle_row_c_hold`'s toolkit at the `univ` `k`-frame:

* the complex abbreviations `chiC` (`χ_Λ`), `theC` (`θ = 1_Λ`) and `hatC`/`hatCv` (`χ̂(ℓκ)`),
  with their conjugation-invariance (`conj_chiC`, `conj_theC`, `conj_hatC`);
* the `univ`-sum reindexing `sum_univ_neg` and the evenness of the `univ` `χ̂`-frame
  `KχfrU_neg` (`KχfrU z = KχfrU (−z)`, used by the `(θ,χ)` channel);
* the expansions of the *unconjugated* pins: `pinQ_eq_expC`, and the conjugates
  `conj_pinThetaC`, `conj_pinCondC`;
* the phase-conversion toolbox (`exp_phase_neg_add`, `exp_phase_neg_right`, …, the `Ω`-side
  counterparts of `Middle_aux`'s `phase1`/`phase2`);
* the box-Fourier expansions of the two mirror integrals

  `ℓ⁻³∫_w χ_Λ(w)·Ksfr(w−y)·KfrU(xi−w) = Σ_{s,k} f_L(s)Ŵ₁(k)·χ̂(ℓ(κ_s−κ_k))·e^{−i⟪κ_s,y⟫}e^{i⟪κ_k,xi⟫}`,
  `ℓ⁻³∫_w χ_Λ(w)·Ksfr(w−y)·KχfrU(w)  = Σ_{s,k} f_L(s)Ŵ₁(k)χ̂(ℓκ_k)·χ̂(ℓ(κ_s+κ_k))·e^{−i⟪κ_s,y⟫}`

  (`integral_Ksfr_KfrU_eq`, `integral_Ksfr_KχfrU_eq`), obtained like `rowC_integral_expand` from
  `Work.BoseBoxFock.rowC_integral_chiLam_exp_pair`.

Everything here is `sorry`-free.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock.PCFU

open Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The complex window, indicator and `χ̂` -/

/-- The complex window `χ_Λ(z)` at the box side `ℓ = ellH v μ`. -/
def chiC (v : Ω → ℝ) (μ : ℝ) (z : Ω) : ℂ :=
  ((Work.BoseK15.corpusBox.chiLam (ellH v μ) z : ℝ) : ℂ)

/-- The complex box indicator `θ(z) = 1_Λ(z)`. -/
def theC (v : Ω → ℝ) (μ : ℝ) (z : Ω) : ℂ :=
  Work.BoseK15.corpusBox.thetaFun (ellH v μ) z

/-- The complex `χ̂(ℓ p)` at a vector `p`. -/
def hatCv (v : Ω → ℝ) (μ : ℝ) (p : Ω) : ℂ :=
  ((Work.BoseK15.corpusBox.hatChi ((ellH v μ) • p) : ℝ) : ℂ)

/-- The complex `χ̂(ℓ κ_k)` at a label. -/
def hatC (v : Ω → ℝ) (μ : ℝ) (N : ℕ) (k : Lab N) : ℂ := hatCv v μ (kmomLab (ellH v μ) N k)

/-- `chiC` is real. -/
theorem conj_chiC (v : Ω → ℝ) (μ : ℝ) (z : Ω) : star (chiC v μ z) = chiC v μ z := by
  simp [chiC]

/-- `theC` is real. -/
theorem conj_theC (v : Ω → ℝ) (μ : ℝ) (z : Ω) : star (theC v μ z) = theC v μ z := by
  simp only [theC]
  exact conj_thetaFun_self _ _

/-- `hatC` is real. -/
theorem conj_hatC (v : Ω → ℝ) (μ : ℝ) (N : ℕ) (k : Lab N) : star (hatC v μ N k) = hatC v μ N k := by
  simp [hatC, hatCv]

/-- `hatC` is `hatChih` in complex form. -/
theorem hatC_eq_hatChih (v : Ω → ℝ) (μ : ℝ) (N : ℕ) (k : Lab N) :
    hatC v μ N k = ((hatChih v μ N k : ℝ) : ℂ) := by
  simp only [hatC, hatCv, hatChih]

/-! ## 2. The expansions of the pins -/

/-- The **unconjugated** expansion of `pinQ`: the localised plane wave minus its condensate
component.  (Mirror of `conj_pinQ_eq`.) -/
theorem pinQ_eq_expC (v : Ω → ℝ) (μ : ℝ) (N : ℕ) (k : Lab N) (y : Ω) :
    pinQ v μ N k y
      = (((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ) *
          (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) y : ℂ)) * chiC v μ y
            - hatC v μ N k * theC v μ y) := by
  simp only [pinQ, chiC, hatC, hatCv, theC, Work.BoseB4.BoxData.qVec,
    Work.BoseB4.BoxData.modeVec]

/-- The **conjugate** of `pinTheta`: the reversed-phase `θ`-mode. -/
theorem conj_pinThetaC (v : Ω → ℝ) (μ : ℝ) (N : ℕ) (s : Lab N) (x : Ω) :
    star (pinTheta v μ N s x)
      = (((Real.sqrt ((ellH v μ) ^ 3))⁻¹ : ℝ) : ℂ) *
          (Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) x : ℂ)))
            * theC v μ x) := by
  rw [pinTheta_eq_exp, theC]
  rw [Complex.star_def, map_mul, map_mul, Complex.conj_ofReal, conj_phase, conj_thetaFun_self]

/-- The **conjugate** of `pinCond`: a `c`-number times the indicator. -/
theorem conj_pinCondC (v : Ω → ℝ) (μ : ℝ) (c : ℂ) (u : Ω) :
    star (pinCond v μ c u) = star c * theC v μ u := by
  rw [pinCond, theC, Complex.star_def, map_mul, conj_thetaFun_self]

/-! ## 3. The `univ`-frame parity -/

/-- The `univ`-sum may be reindexed by `k ↦ −k`. -/
lemma sum_univ_neg {N : ℕ} (F : Lab N → ℂ) :
    (∑ k : Lab N, F (-k)) = ∑ k : Lab N, F k := by
  refine Finset.sum_bij' (fun a _ => -a) (fun a _ => -a) (fun a _ => Finset.mem_univ _)
    (fun a _ => Finset.mem_univ _) (fun a _ => by simp) (fun a _ => by simp) (fun a _ => rfl)

/-- The `univ` `χ̂`-frame is even. -/
lemma KχfrU_neg (v : Ω → ℝ) (h : Work.UBB.ScatSol v) (μ : ℝ)
    (fu : Work.BoseBoxFix.LowCut) (N : ℕ) (z : Ω) :
    KχfrU v h μ fu N (-z) = KχfrU v h μ fu N z := by
  simp only [KχfrU]
  rw [← sum_univ_neg (fun k => (((W1h v h μ fu N k * hatChih v μ N k : ℝ)) : ℂ)
    * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [W1h_neg, hatChih_neg, kmomLab_neg, inner_neg_left, inner_neg_right]

/-! ## 4. The phase-conversion toolbox -/

/-- `e^{i⟪p,(−y)+w⟫} = e^{i⟪p,w−y⟫}`. -/
lemma exp_phase_neg_add (p y w : Ω) :
    Complex.exp (Complex.I * (inner ℝ p (-y + w) : ℂ))
      = Complex.exp (Complex.I * (inner ℝ p (w - y) : ℂ)) := by
  congr 1
  rw [show -y + w = w - y from by rw [add_comm, sub_eq_add_neg]]

/-- `e^{i⟪−q,(−xi)+w⟫} = e^{i⟪q,xi−w⟫}`. -/
lemma exp_phase_neg_neg_add (q xi w : Ω) :
    Complex.exp (Complex.I * (inner ℝ (-q) (-xi + w) : ℂ))
      = Complex.exp (Complex.I * (inner ℝ q (xi - w) : ℂ)) := by
  congr 1
  rw [inner_neg_left, show -xi + w = w - xi from by rw [add_comm, sub_eq_add_neg],
    inner_sub_right, neg_sub, inner_sub_right]

/-- `e^{i⟪p,−y⟫} = e^{−i⟪p,y⟫}`. -/
lemma exp_phase_neg_right (p y : Ω) :
    Complex.exp (Complex.I * (inner ℝ p (-y) : ℂ))
      = Complex.exp (-(Complex.I * (inner ℝ p y : ℂ))) := by
  congr 1
  rw [inner_neg_right]
  push_cast
  ring

/-- `e^{i⟪−q,−y⟫} = e^{i⟪q,y⟫}`. -/
lemma exp_phase_neg_neg (q y : Ω) :
    Complex.exp (Complex.I * (inner ℝ (-q) (-y) : ℂ))
      = Complex.exp (Complex.I * (inner ℝ q y : ℂ)) := by
  congr 1
  rw [inner_neg_left, inner_neg_right]
  push_cast
  ring

/-- `e^{−i⟪p,y⟫} = e^{i⟪−p,y⟫}`. -/
lemma exp_phase_neg_left (p y : Ω) :
    Complex.exp (-(Complex.I * (inner ℝ p y : ℂ)))
      = Complex.exp (Complex.I * (inner ℝ (-p) y : ℂ)) := by
  congr 1
  rw [inner_neg_left]
  push_cast
  ring

/-- `e^{i⟪p,y⟫} = e^{i⟪p',y'⟫}` whenever the inner products agree; convenience form for the
`−q ↦ q` conversions in the channel comparisons. -/
lemma exp_phase_congr {a b : ℂ} (h : a = b) :
    Complex.exp (Complex.I * a) = Complex.exp (Complex.I * b) := by rw [h]

/-! ## 4bis. The four monomials of the mirror summand

Expanding the product `pinQ k xi · star(pinTheta s y) · pinQ (s−k) xj` with `pinQ_eq_expC` and
`conj_pinThetaC` gives `((√ℓ³)⁻¹)³` times the four monomials below (in the order
`chsVA − chsVB − chsVC + chsVD`); the `c`-number `star (pinCond v μ c u) = star c · θ(u)` is a
common factor and is handled by the caller. -/

/-- `(χ,χ)` monomial: the two localised plane waves at `xi`, `xj` and the reversed `θ`-mode. -/
def chsVA (v : Ω → ℝ) (μ : ℝ) (N : ℕ) (s k : Lab N) (xi y xj : Ω) : ℂ :=
  Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) xi : ℂ)) * chiC v μ xi
    * (Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) y : ℂ))) * theC v μ y)
    * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N (s - k)) xj : ℂ)) * chiC v μ xj)

/-- `(χ,θ)` monomial: the `χ̂(ℓκ_{s−k})` sits on the `xj`-slot. -/
def chsVB (v : Ω → ℝ) (μ : ℝ) (N : ℕ) (s k : Lab N) (xi y xj : Ω) : ℂ :=
  Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) xi : ℂ)) * chiC v μ xi
    * (Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) y : ℂ))) * theC v μ y)
    * (hatC v μ N (s - k) * theC v μ xj)

/-- `(θ,χ)` monomial: the `χ̂(ℓκ_k)` sits on the `xi`-slot. -/
def chsVC (v : Ω → ℝ) (μ : ℝ) (N : ℕ) (s k : Lab N) (xi y xj : Ω) : ℂ :=
  hatC v μ N k * theC v μ xi
    * (Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) y : ℂ))) * theC v μ y)
    * (Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N (s - k)) xj : ℂ)) * chiC v μ xj)

/-- `(θ,θ)` monomial: both `χ̂`s. -/
def chsVD (v : Ω → ℝ) (μ : ℝ) (N : ℕ) (s k : Lab N) (xi y xj : Ω) : ℂ :=
  hatC v μ N k * theC v μ xi
    * (Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) y : ℂ))) * theC v μ y)
    * (hatC v μ N (s - k) * theC v μ xj)

/-! ## 5. The two mirror integrals -/

/-- **The box Fourier expansion of the `(χ,θ)` mirror integral**:
`ℓ⁻³∫_w χ_Λ(w)Ksfr(w−y)KfrU(xi−w) = Σ_{s,k}f_L(s)Ŵ₁(k)χ̂(ℓ(κ_s−κ_k))e^{−i⟪κ_s,y⟫}e^{i⟪κ_k,xi⟫}`. -/
theorem integral_Ksfr_KfrU_eq (v : Ω → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (xi y : Ω) :
    (((ellH v μ) ^ 3 : ℝ) : ℂ)⁻¹
        * ∫ w : Ω, chiC v μ w * Ksfr v fc μ N (w - y) * KfrU v h μ fu N (xi - w)
      = ∑ s ∈ Work.BoseB7.excited (Lab N), ∑ k : Lab N,
          ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
            * hatCv v μ (kmomLab (ellH v μ) N s - kmomLab (ellH v μ) N k)
            * Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) y : ℂ)))
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) xi : ℂ)) := by
  have hℓ : (0 : ℝ) < ellH v μ := ellH_pos v μ
  have hℓ3 : ((ellH v μ ^ 3 : ℝ) : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ofReal_eq_zero]
    exact pow_ne_zero _ (ne_of_gt hℓ)
  -- integrability of one summand
  have hTerm_int : ∀ s k : Lab N, Integrable fun w : Ω =>
        chiC v μ w
          * (((fLh v fc μ N s : ℝ) : ℂ)
              * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (w - y) : ℂ)))
          * (((W1h v h μ fu N k : ℝ) : ℂ)
              * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (xi - w) : ℂ))) := by
    intro s k
    have hbase := rowC_integrable_chiLam_exp_pair hℓ (kmomLab (ellH v μ) N s)
      (-(kmomLab (ellH v μ) N k)) (-y) (-xi)
    refine (hbase.const_mul (((fLh v fc μ N s : ℝ) : ℂ)
      * ((W1h v h μ fu N k : ℝ) : ℂ))).congr ?_
    filter_upwards with w
    simp only [chiC]
    rw [exp_phase_neg_neg_add, exp_phase_neg_add]
    ring
  -- the pointwise expansion of the integrand
  have hExpand : (fun w : Ω => chiC v μ w * Ksfr v fc μ N (w - y) * KfrU v h μ fu N (xi - w))
      = fun w : Ω => ∑ s ∈ Work.BoseB7.excited (Lab N), ∑ k : Lab N,
          chiC v μ w
            * (((fLh v fc μ N s : ℝ) : ℂ)
                * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (w - y) : ℂ)))
            * (((W1h v h μ fu N k : ℝ) : ℂ)
                * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (xi - w) : ℂ))) := by
    funext w
    rw [Ksfr, KfrU]
    exact rowC_mul_sum_mul_sum (chiC v μ w) _ _ _ _
  rw [hExpand]
  rw [integral_finset_sum _ (fun s _ => integrable_finset_sum _ (fun k _ => hTerm_int s k))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_finset_sum _ (fun k _ => hTerm_int s k)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hval : ∫ w, chiC v μ w
        * (((fLh v fc μ N s : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (w - y) : ℂ)))
        * (((W1h v h μ fu N k : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (xi - w) : ℂ)))
      = ((ellH v μ ^ 3 : ℝ) : ℂ) * (((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ)
          * hatCv v μ (kmomLab (ellH v μ) N s - kmomLab (ellH v μ) N k)
          * Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) y : ℂ)))
          * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) xi : ℂ))) := by
    rw [show (fun w : Ω => chiC v μ w
        * (((fLh v fc μ N s : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (w - y) : ℂ)))
        * (((W1h v h μ fu N k : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (xi - w) : ℂ))))
      = (fun w : Ω => (((fLh v fc μ N s : ℝ) : ℂ) * ((W1h v h μ fu N k : ℝ) : ℂ))
        * (((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (-y + w) : ℂ))
        * Complex.exp (Complex.I * (inner ℝ (-(kmomLab (ellH v μ) N k)) (-xi + w) : ℂ))))
      from funext (fun w => by
        simp only [chiC]
        rw [exp_phase_neg_neg_add, exp_phase_neg_add]
        ring)]
    rw [integral_const_mul]
    rw [rowC_integral_chiLam_exp_pair hℓ (kmomLab (ellH v μ) N s)
      (-(kmomLab (ellH v μ) N k)) (-y) (-xi)]
    simp only [hatCv]
    rw [exp_phase_neg_right, exp_phase_neg_neg, ← sub_eq_add_neg]
    push_cast
    ring
  rw [hval, ← mul_assoc, inv_mul_cancel₀ hℓ3, one_mul]

/-- **The box Fourier expansion of the `(θ,θ)` mirror integral**:
`ℓ⁻³∫_w χ_Λ(w)Ksfr(w−y)KχfrU(w)
  = Σ_{s,k}f_L(s)Ŵ₁(k)χ̂(ℓκ_k)χ̂(ℓ(κ_s+κ_k))e^{−i⟪κ_s,y⟫}`. -/
theorem integral_Ksfr_KχfrU_eq (v : Ω → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (y : Ω) :
    (((ellH v μ) ^ 3 : ℝ) : ℂ)⁻¹
        * ∫ w : Ω, chiC v μ w * Ksfr v fc μ N (w - y) * KχfrU v h μ fu N w
      = ∑ s ∈ Work.BoseB7.excited (Lab N), ∑ k : Lab N,
          ((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ) * hatC v μ N k
            * hatCv v μ (kmomLab (ellH v μ) N s + kmomLab (ellH v μ) N k)
            * Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) y : ℂ))) := by
  have hℓ : (0 : ℝ) < ellH v μ := ellH_pos v μ
  have hℓ3 : ((ellH v μ ^ 3 : ℝ) : ℂ) ≠ 0 := by
    rw [ne_eq, Complex.ofReal_eq_zero]
    exact pow_ne_zero _ (ne_of_gt hℓ)
  have hTerm_int : ∀ s k : Lab N, Integrable fun w : Ω =>
        chiC v μ w
          * (((fLh v fc μ N s : ℝ) : ℂ)
              * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (w - y) : ℂ)))
          * (((W1h v h μ fu N k * hatChih v μ N k : ℝ) : ℂ)
              * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) w : ℂ))) := by
    intro s k
    have hbase := rowC_integrable_chiLam_exp_pair hℓ (kmomLab (ellH v μ) N s)
      (kmomLab (ellH v μ) N k) (-y) 0
    refine (hbase.const_mul (((fLh v fc μ N s : ℝ) : ℂ)
      * ((W1h v h μ fu N k * hatChih v μ N k : ℝ) : ℂ))).congr ?_
    filter_upwards with w
    simp only [chiC]
    rw [show (0 : Ω) + w = w from zero_add w]
    rw [exp_phase_neg_add]
    ring
  have hExpand : (fun w : Ω => chiC v μ w * Ksfr v fc μ N (w - y) * KχfrU v h μ fu N w)
      = fun w : Ω => ∑ s ∈ Work.BoseB7.excited (Lab N), ∑ k : Lab N,
          chiC v μ w
            * (((fLh v fc μ N s : ℝ) : ℂ)
                * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (w - y) : ℂ)))
            * (((W1h v h μ fu N k * hatChih v μ N k : ℝ) : ℂ)
                * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) w : ℂ))) := by
    funext w
    rw [Ksfr, KχfrU]
    exact rowC_mul_sum_mul_sum (chiC v μ w) _ _ _ _
  rw [hExpand]
  rw [integral_finset_sum _ (fun s _ => integrable_finset_sum _ (fun k _ => hTerm_int s k))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [integral_finset_sum _ (fun k _ => hTerm_int s k)]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hval : ∫ w, chiC v μ w
        * (((fLh v fc μ N s : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (w - y) : ℂ)))
        * (((W1h v h μ fu N k * hatChih v μ N k : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) w : ℂ)))
      = ((ellH v μ ^ 3 : ℝ) : ℂ) * (((fLh v fc μ N s * W1h v h μ fu N k : ℝ) : ℂ) * hatC v μ N k
          * hatCv v μ (kmomLab (ellH v μ) N s + kmomLab (ellH v μ) N k)
          * Complex.exp (-(Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) y : ℂ)))) := by
    rw [show (fun w : Ω => chiC v μ w
        * (((fLh v fc μ N s : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (w - y) : ℂ)))
        * (((W1h v h μ fu N k * hatChih v μ N k : ℝ) : ℂ)
            * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) w : ℂ))))
      = (fun w : Ω => (((fLh v fc μ N s : ℝ) : ℂ) * ((W1h v h μ fu N k * hatChih v μ N k : ℝ) : ℂ))
        * (((Work.BoseK15.corpusBox.chiLam (ellH v μ) w : ℝ) : ℂ)
        * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N s) (-y + w) : ℂ))
        * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) (0 + w) : ℂ))))
      from funext (fun w => by
        simp only [chiC]
        rw [exp_phase_neg_add, show (0 : Ω) + w = w from zero_add w]
        ring)]
    rw [integral_const_mul]
    rw [rowC_integral_chiLam_exp_pair hℓ (kmomLab (ellH v μ) N s)
      (kmomLab (ellH v μ) N k) (-y) 0]
    simp only [hatCv, inner_zero_right, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one]
    rw [exp_phase_neg_right]
    simp only [Complex.ofReal_mul]
    rw [← hatC_eq_hatChih]
    ring
  rw [hval, ← mul_assoc, inv_mul_cancel₀ hℓ3, one_mul]

end Work.BoseBoxFock.PCFU
