import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Submission.Work.BoseB7AK.W1rows.chat_neg
import Submission.Work.BoseBoxFock.PotCubicExpansion
import Submission.Work.BoseBoxFock.pcfFrameDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.Middle_aux` — the elementary frame/parity facts for `Middle`

Holder: `Submission/Work/BoseBoxFock/Middle_expansion.lean`.  The framing of the cubic row's
middle kernel `Middle` (see `FINDING_Middle_expansion_FALSE.md`) splits into four channels
(`summand_four_split`); this module collects the *elementary* facts every channel needs:

* the label sum is invariant under negation (`sum_neg_excited`), the weights `fLh`, `W1h` and the
  `χ̂`-weight are even (`fLh_neg`, `W1h_neg`, `hatChih_neg`) and consequently so are the three
  frames (`Ksfr_neg`, `Kfr_neg`, `Kχfr_neg`);
* the plane-wave algebra of the four channels (`phase1`, `phase2`, `exp_diff_phase`, …);
* the box Fourier transform in the `χ̂ = ℓ^{-3}∫` direction (`hatChi_eq_integral`), the
  `zpow`-form of the `ℓ^{-3}` slot (`ellH_zpow_neg_three`), the `ℓ^{-9/2}` arithmetic of the outer
  coefficient (`inv_sqrt_cube`) and the integrability of the `χ_Λ e^{−i⟪p,·⟫}` integrand.

Everything here is `sorry`-free and axiom-clean.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

variable {v : Ω → ℝ} {h : Work.UBB.ScatSol v} {fc fu : Work.BoseBoxFix.LowCut} {μ : ℝ} {N : ℕ}

/-- `excited` is invariant under negation. -/
lemma neg_mem_excited {n : Lab N} (hn : n ∈ Work.BoseB7.excited (Lab N)) :
    -n ∈ Work.BoseB7.excited (Lab N) := by
  simp only [Work.BoseB7.excited, Finset.mem_erase, Finset.mem_univ, and_true] at hn ⊢
  exact fun h => hn (neg_eq_zero.mp h)

/-- A sum over `excited` may be reindexed by `n ↦ -n`. -/
lemma sum_neg_excited (F : Lab N → ℂ) :
    (∑ n ∈ Work.BoseB7.excited (Lab N), F (-n)) = ∑ n ∈ Work.BoseB7.excited (Lab N), F n := by
  refine Finset.sum_bij' (fun a _ => -a) (fun a _ => -a) (fun a ha => neg_mem_excited ha)
    (fun a ha => neg_mem_excited ha) (fun a ha => by simp) (fun a ha => by simp) (fun a ha => rfl)

/-- The `f_L`-weight is even in the label. -/
lemma fLh_neg (s : Lab N) : fLh v fc μ N (-s) = fLh v fc μ N s := by
  simp only [fLh, kmomLab_neg, norm_neg]

/-- The `χ̂(ℓκ)`-weight is even in the label. -/
lemma hatChih_neg (k : Lab N) : hatChih v μ N (-k) = hatChih v μ N k := by
  simp only [hatChih, kmomLab_neg, smul_neg, Work.BoseB4.BoxData.hatChi_neg]

/-- The `W₁`-weight is even in the label (`chat` of a real function is even). -/
lemma W1h_neg (k : Lab N) : W1h v h μ fu N (-k) = W1h v h μ fu N k := by
  simp only [W1h, uvCut, kmomLab_neg, norm_neg, Work.BoseB7AK.W1rows.chat_neg]

/-- The `W₁`-frame is even. -/
lemma Kfr_neg (z : Ω) : Kfr v h μ fu N (-z) = Kfr v h μ fu N z := by
  simp only [Kfr]
  rw [← sum_neg_excited (fun k => ((W1h v h μ fu N k : ℝ) : ℂ)
    * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [W1h_neg, kmomLab_neg, inner_neg_left, inner_neg_right]

/-- The `χ̂`-weighted `W₁`-frame is even. -/
lemma Kχfr_neg (z : Ω) : Kχfr v h μ fu N (-z) = Kχfr v h μ fu N z := by
  simp only [Kχfr]
  rw [← sum_neg_excited (fun k => (((W1h v h μ fu N k * hatChih v μ N k : ℝ)) : ℂ)
    * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [W1h_neg, hatChih_neg, kmomLab_neg, inner_neg_left, inner_neg_right]

/-- The `f_L`-frame is even. -/
lemma Ksfr_neg (z : Ω) : Ksfr v fc μ N (-z) = Ksfr v fc μ N z := by
  simp only [Ksfr]
  rw [← sum_neg_excited (fun k => ((fLh v fc μ N k : ℝ) : ℂ)
    * Complex.exp (Complex.I * (inner ℝ (kmomLab (ellH v μ) N k) z : ℂ)))]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [fLh_neg, kmomLab_neg, inner_neg_left, inner_neg_right]

/-! ## Plane-wave algebra of the channels -/

/-- `e^{−i⟪a−b,z⟫} = e^{−i⟪a,z⟫}e^{i⟪b,z⟫}`. -/
lemma exp_diff_phase (a b z : Ω) :
    Complex.exp (-(Complex.I * (inner ℝ (a - b) z : ℂ)))
      = Complex.exp (-(Complex.I * (inner ℝ a z : ℂ))) * Complex.exp (Complex.I * (inner ℝ b z : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  simp only [inner_sub_left]
  push_cast
  ring

/-- `e^{i⟪a,x⟫}e^{−i⟪a,z⟫} = e^{i⟪a,x−z⟫}`. -/
lemma exp_shift_left (a x z : Ω) :
    Complex.exp (Complex.I * (inner ℝ a x : ℂ)) * Complex.exp (-(Complex.I * (inner ℝ a z : ℂ)))
      = Complex.exp (Complex.I * (inner ℝ a (x - z) : ℂ)) := by
  rw [← Complex.exp_add, inner_sub_right]
  congr 1
  push_cast
  ring

/-- `e^{−i⟪b,u⟫}e^{i⟪b,z⟫} = e^{i⟪b,z−u⟫}`. -/
lemma exp_shift_right (b z u : Ω) :
    Complex.exp (-(Complex.I * (inner ℝ b u : ℂ))) * Complex.exp (Complex.I * (inner ℝ b z : ℂ))
      = Complex.exp (Complex.I * (inner ℝ b (z - u) : ℂ)) := by
  rw [← Complex.exp_add, inner_sub_right]
  congr 1
  push_cast
  ring

/-- Channel (a): after `hsub` the three phases collapse to `e^{i⟪a,x−y⟫}e^{i⟪b,y−u⟫}χ(y)θ(x)χ(u)`. -/
lemma phase1_aux (a b y x u : Ω) :
    Complex.exp (-(Complex.I * (inner ℝ (a - b) y : ℂ)))
      * Complex.exp (Complex.I * (inner ℝ a x : ℂ))
      * Complex.exp (-(Complex.I * (inner ℝ b u : ℂ)))
    = Complex.exp (Complex.I * (inner ℝ a (x - y) : ℂ))
      * Complex.exp (Complex.I * (inner ℝ b (y - u) : ℂ)) := by
  simp only [← Complex.exp_add]
  congr 1
  simp only [inner_sub_left, inner_sub_right]
  push_cast
  ring

/-- Channel (a) in the shape in which it appears in `summand_four_split`. -/
lemma phase1 (a b y x u : Ω) (χy θx χu : ℂ) :
    Complex.exp (-(Complex.I * (inner ℝ (a - b) y : ℂ))) * χy
      * (Complex.exp (Complex.I * (inner ℝ a x : ℂ)) * θx)
      * (Complex.exp (-(Complex.I * (inner ℝ b u : ℂ))) * χu)
    = (Complex.exp (Complex.I * (inner ℝ a (x - y) : ℂ)) * χy * θx)
      * (Complex.exp (Complex.I * (inner ℝ b (y - u) : ℂ)) * χu) := by
  have h := phase1_aux a b y x u
  have key : Complex.exp (-(Complex.I * (inner ℝ (a - b) y : ℂ))) * χy
      * (Complex.exp (Complex.I * (inner ℝ a x : ℂ)) * θx)
      * (Complex.exp (-(Complex.I * (inner ℝ b u : ℂ))) * χu)
    = χy * θx * χu * (Complex.exp (-(Complex.I * (inner ℝ (a - b) y : ℂ)))
        * Complex.exp (Complex.I * (inner ℝ a x : ℂ))
        * Complex.exp (-(Complex.I * (inner ℝ b u : ℂ)))) := by ring
  rw [key, h]
  ring

/-- Channel (b): `e^{−i⟪a−b,y⟫}χ(y)·e^{i⟪a,x⟫}θ(x) = e^{i⟪a,x−y⟫}χ(y)θ(x)·e^{i⟪b,y⟫}`. -/
lemma phase2_aux (a b y x : Ω) :
    Complex.exp (-(Complex.I * (inner ℝ (a - b) y : ℂ)))
      * Complex.exp (Complex.I * (inner ℝ a x : ℂ))
    = Complex.exp (Complex.I * (inner ℝ a (x - y) : ℂ))
      * Complex.exp (Complex.I * (inner ℝ b y : ℂ)) := by
  rw [exp_diff_phase a b y]
  rw [show Complex.exp (-(Complex.I * (inner ℝ a y : ℂ)))
        * Complex.exp (Complex.I * (inner ℝ b y : ℂ))
        * Complex.exp (Complex.I * (inner ℝ a x : ℂ))
      = Complex.exp (Complex.I * (inner ℝ a x : ℂ))
        * Complex.exp (-(Complex.I * (inner ℝ a y : ℂ)))
        * Complex.exp (Complex.I * (inner ℝ b y : ℂ)) from by ring]
  rw [exp_shift_left]

/-- Channel (b) in the shape in which it appears in `summand_four_split`. -/
lemma phase2 (a b y x : Ω) (χy θx χu θu : ℂ) :
    Complex.exp (-(Complex.I * (inner ℝ (a - b) y : ℂ))) * χy
      * (Complex.exp (Complex.I * (inner ℝ a x : ℂ)) * θx)
      * (χu * θu)
    = (Complex.exp (Complex.I * (inner ℝ a (x - y) : ℂ)) * χy * θx)
      * (Complex.exp (Complex.I * (inner ℝ b y : ℂ)) * χu * θu) := by
  have h := phase2_aux a b y x
  have key : Complex.exp (-(Complex.I * (inner ℝ (a - b) y : ℂ))) * χy
        * (Complex.exp (Complex.I * (inner ℝ a x : ℂ)) * θx) * (χu * θu)
      = χy * θx * χu * θu * (Complex.exp (-(Complex.I * (inner ℝ (a - b) y : ℂ)))
          * Complex.exp (Complex.I * (inner ℝ a x : ℂ))) := by ring
  rw [key, h]
  ring

/-! ## The box Fourier transform, the coefficients and integrability -/

/-- FS's box Fourier transform in the direction needed by the `χ̂`-channels:
`χ̂(ℓ•p) = ℓ^{-3}∫ χ_Λ(z) e^{−i⟪p,z⟫}dz`, with the integral in the exact shape of
`Work.BoseBoxFock.integral_chiLam_exp`. -/
lemma hatChi_eq_integral {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Ω) :
    ((Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ)
      = ((ℓ ^ 3 : ℝ) : ℂ)⁻¹ * ∫ z, Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
          * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) := by
  have hmain := Work.BoseBoxFock.integral_chiLam_exp hℓ p
  have hmul : ((Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ) * ((ℓ ^ 3 : ℝ) : ℂ)
      = ((ℓ ^ 3 * Work.BoseK15.corpusBox.hatChi (ℓ • p) : ℝ) : ℂ) := by push_cast; ring
  have h3 : ((ℓ ^ 3 : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact pow_ne_zero _ (ne_of_gt hℓ)
  rw [hmain, ← hmul]
  field_simp

/-- The `ℓ^{-3}` slot of the statement, in the `zpow` form used there. -/
lemma ellH_zpow_neg_three (ℓ : ℝ) :
    (((ℓ ^ (-(3 : ℤ)) : ℝ)) : ℂ) = ((ℓ ^ 3 : ℝ) : ℂ)⁻¹ := by
  have h : ℓ ^ (-(3:ℤ)) = (ℓ ^ 3)⁻¹ := by simp
  rw [h, Complex.ofReal_inv]

/-- The outer coefficient: `((√(ℓ³))⁻¹)³ = ℓ^{-9/2}`. -/
lemma inv_sqrt_cube {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (((Real.sqrt (ℓ ^ 3))⁻¹ : ℝ)) ^ 3 = ℓ ^ (-(9 / 2 : ℝ)) := by
  have h1 : Real.sqrt (ℓ ^ 3) = ℓ ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast ℓ 3, ← Real.rpow_mul hℓ.le]
    norm_num
  have h2 : (ℓ ^ (3/2:ℝ))⁻¹ = ℓ ^ (-(3/2):ℝ) := (Real.rpow_neg hℓ.le (3/2)).symm
  rw [h1, h2, ← Real.rpow_natCast (ℓ ^ (-(3/2):ℝ)) 3, ← Real.rpow_mul hℓ.le]
  norm_num

/-- Integrability of the `χ_Λ·e^{−i⟪p,·⟫}` integrand (via `cos`/`sin`). -/
lemma integrable_chiLam_mul_exp (ℓ : ℝ) (hℓ : 0 < ℓ) (p : Ω) :
    Integrable fun z : Ω => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
      * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) := by
  have h1 : Integrable fun z : Ω =>
      ((Work.BoseK15.corpusBox.chiLam ℓ z * Real.cos (inner ℝ p z) : ℝ) : ℂ) :=
    (Work.BoseB4.BoxData.integrable_chiLam_mul_cos _ hℓ p).ofReal
  have h2 : Integrable fun z : Ω =>
      Complex.I * ((Work.BoseK15.corpusBox.chiLam ℓ z * Real.sin (inner ℝ p z) : ℝ) : ℂ) :=
    (Work.BoseBoxFock.integrable_chiLam_mul_sin _ hℓ p).ofReal.const_mul Complex.I
  have hpt : (fun z : Ω => Complex.exp (-(Complex.I * (inner ℝ p z : ℂ)))
        * ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ))
      = fun z => ((Work.BoseK15.corpusBox.chiLam ℓ z * Real.cos (inner ℝ p z) : ℝ) : ℂ)
          - Complex.I * ((Work.BoseK15.corpusBox.chiLam ℓ z * Real.sin (inner ℝ p z) : ℝ) : ℂ) := by
    funext z
    rw [show -(Complex.I * (inner ℝ p z : ℂ)) = -((inner ℝ p z : ℂ) * Complex.I) from by ring,
      Work.BoseBoxFock.exp_neg_mul_I_ofReal]
    push_cast
    ring
  rw [hpt]
  exact h1.sub h2

end Work.BoseBoxFock
