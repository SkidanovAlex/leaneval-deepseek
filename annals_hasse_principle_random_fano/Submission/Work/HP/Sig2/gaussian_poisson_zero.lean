import Mathlib
import Submission.Work.HP.Sig2.GaussPoissonDefs
import Submission.Work.HP.Sig2.peel_tail_schur
import Submission.Work.HP.Sig2.peel_det
import Submission.Work.HP.Sig2.peel_quad
import Submission.Work.HP.Sig2.peel_inv_quad
import Submission.Work.HP.Sig2.summable_shifted_gauss
import Submission.Work.HP.Sig2.gauss_poisson_1d
import Submission.Work.HP.Sig2.gauss_poisson_transport

noncomputable section
open Matrix

namespace Work.HP.Sig2

open scoped BigOperators

/-! ### Summands -/


def gaussL {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (s : ℝ) (u : ι → ℝ) (n : ι → ℤ) : ℂ :=
  Complex.exp (((-(Real.pi / s ^ 2) * qForm G (fun i => (n i : ℝ) + u i)) : ℝ))

def gaussR {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (s : ℝ) (u : ι → ℝ) (m : ι → ℤ) : ℂ :=
  Complex.exp (((-(Real.pi * s ^ 2) * qForm G (fun i => (m i : ℝ))) : ℝ)
    + 2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * u j : ℝ) : ℂ))

def g0 {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) (s : ℝ) (u : Fin (R + 1) → ℝ)
    (a : ℤ) : ℝ := -(Real.pi / s ^ 2) * pSchur G * ((a : ℝ) + u 0) ^ 2

def gaussQ {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) (s : ℝ) (u : Fin (R + 1) → ℝ)
    (m' : Fin R → ℤ) (a : ℤ) : ℂ :=
  Complex.exp (-(Real.pi * (pSchur G / s ^ 2 : ℝ)) * ((a : ℂ) + (u 0 : ℂ)) ^ 2
    + 2 * Real.pi * Complex.I * (((∑ j, (m' j : ℝ) * pWind G j) : ℝ) : ℂ)
        * ((a : ℂ) + (u 0 : ℂ)))

def gaussQ3 {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) (s : ℝ) (u : Fin (R + 1) → ℝ)
    (m' : Fin R → ℤ) (m0 : ℤ) : ℂ :=
  Complex.exp (-(Real.pi / (pSchur G / s ^ 2 : ℝ)) *
      ((m0 : ℂ) - (((∑ j, (m' j : ℝ) * pWind G j) : ℝ) : ℂ)) ^ 2)
    * Complex.exp (2 * Real.pi * Complex.I * (m0 : ℂ) * ((u 0 : ℝ) : ℂ))

def gaussP0 {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) (s : ℝ) (u : Fin (R + 1) → ℝ)
    (a : ℤ) : (Fin R → ℤ) → ℂ := fun m' =>
  Complex.exp (g0 G s u a) *
    gaussR (pTail G)⁻¹ s (fun i => u i.succ + ((a : ℝ) + u 0) * pWind G i) m'

def gaussP1 {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) (s : ℝ) (u : Fin (R + 1) → ℝ)
    (m' : Fin R → ℤ) : ℂ := gaussR (pTail G)⁻¹ s (fun i => u i.succ) m'

def gaussP2 {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) (s : ℝ) (u : Fin (R + 1) → ℝ)
    (a : ℤ) (m' : Fin R → ℤ) : ℂ := gaussP1 G s u m' * gaussQ G s u m' a

def gaussP3 {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) (s : ℝ) (u : Fin (R + 1) → ℝ)
    (m0 : ℤ) (m' : Fin R → ℤ) : ℂ := gaussP1 G s u m' * gaussQ3 G s u m' m0

def finStatementG (n : ℕ) : Prop :=
  ∀ (G : Matrix (Fin n) (Fin n) ℝ), G.PosDef → ∀ (s : ℝ), 0 < s → ∀ (u : Fin n → ℝ),
    (∑' m : Fin n → ℤ, gaussL G s u m)
      = ((s : ℂ) ^ n / ((Real.sqrt G.det : ℝ) : ℂ)) * ∑' m : Fin n → ℤ, gaussR G⁻¹ s u m

/-! ### Generic helpers -/

def gpzConsEquiv (R : ℕ) : (Fin (R + 1) → ℤ) ≃ ℤ × (Fin R → ℤ) where
  toFun n := (n 0, fun i => n i.succ)
  invFun p := Fin.cons p.1 p.2
  left_inv n := by funext i; exact congrFun (Fin.cons_self_tail n) i
  right_inv p := by
    refine Prod.ext ?_ ?_
    · simp [Fin.cons_zero]
    · funext i; simp [Fin.cons_succ]

def gpzConsEquiv' (R : ℕ) : ((Fin R → ℤ) × ℤ) ≃ (Fin (R + 1) → ℤ) where
  toFun p := Fin.cons p.2 p.1
  invFun n := (fun i => n i.succ, n 0)
  left_inv p := by
    rcases p with ⟨c, a⟩
    refine Prod.ext ?_ ?_
    · funext i; simp [Fin.cons_succ]
    · simp [Fin.cons_zero]
  right_inv n := by funext i; exact congrFun (Fin.cons_self_tail n) i

lemma gpz_summable_cons_iff {R : ℕ} (F : (Fin (R + 1) → ℤ) → ℂ) :
    Summable (fun p : ℤ × (Fin R → ℤ) => F (Fin.cons p.1 p.2)) ↔ Summable F := by
  have h := Equiv.summable_iff (gpzConsEquiv R).symm (f := F)
  rw [show (F ∘ ⇑(gpzConsEquiv R).symm) = fun p : ℤ × (Fin R → ℤ) => F (Fin.cons p.1 p.2)
      from funext fun p => rfl] at h
  exact h

lemma gpz_tsum_cons {R : ℕ} (F : (Fin (R + 1) → ℤ) → ℂ)
    (hF : Summable (fun p : ℤ × (Fin R → ℤ) => F (Fin.cons p.1 p.2))) :
    (∑' n : Fin (R + 1) → ℤ, F n) = ∑' a : ℤ, ∑' c : Fin R → ℤ, F (Fin.cons a c) := by
  have key : (∑' p : ℤ × (Fin R → ℤ), F (Fin.cons p.1 p.2))
      = ∑' a : ℤ, ∑' c : Fin R → ℤ, F (Fin.cons a c) := Summable.tsum_prod hF
  rw [← key]
  exact (Equiv.tsum_eq (gpzConsEquiv R).symm F).symm

lemma gpz_tsum_cons' {R : ℕ} (E : (Fin (R + 1) → ℤ) → ℂ) (hE : Summable E) :
    (∑' c : Fin R → ℤ, ∑' a : ℤ, E (Fin.cons a c)) = ∑' n : Fin (R + 1) → ℤ, E n := by
  have hE' : Summable (fun p : (Fin R → ℤ) × ℤ => E (Fin.cons p.2 p.1)) := by
    have h := Equiv.summable_iff (gpzConsEquiv' R) (f := E)
    rw [show (E ∘ ⇑(gpzConsEquiv' R)) = fun p : (Fin R → ℤ) × ℤ => E (Fin.cons p.2 p.1)
        from funext fun p => rfl] at h
    exact h.mpr hE
  have key : (∑' p : (Fin R → ℤ) × ℤ, E (Fin.cons p.2 p.1))
      = ∑' c : Fin R → ℤ, ∑' a : ℤ, E (Fin.cons a c) := Summable.tsum_prod hE'
  rw [← key]
  exact Equiv.tsum_eq (gpzConsEquiv' R) E

lemma gpz_summable_shift_gauss_int (γ t : ℝ) (hγ : 0 < γ) :
    Summable (fun a : ℤ => Real.exp (-γ * ((a : ℝ) + t) ^ 2)) := by
  have hg : Summable (fun a : ℤ => Real.exp (γ * t ^ 2) * Real.exp (-(γ / 2) * (a : ℝ) ^ 2)) :=
    (summable_gauss_int (γ / 2) (by linarith)).mul_left _
  refine Summable.of_nonneg_of_le (fun a => Real.exp_nonneg _) (fun a => ?_) hg
  rw [← Real.exp_add, Real.exp_le_exp]
  nlinarith [sq_nonneg ((a : ℝ) + 2 * t), hγ.le]

lemma gpz_one_div_sqrt_div (c s : ℝ) (hc : 0 < c) (hs : 0 < s) :
    (1 : ℂ) / ((Real.sqrt (c / s ^ 2) : ℝ) : ℂ) = (s : ℂ) / ((Real.sqrt c : ℝ) : ℂ) := by
  have h1 : Real.sqrt (c / s ^ 2) = Real.sqrt c / s := by
    rw [Real.sqrt_div (le_of_lt hc), Real.sqrt_sq_eq_abs, abs_of_pos hs]
  rw [h1]
  push_cast
  rw [one_div_div]

lemma gpz_phase_canon (z : ℝ) :
    2 * Real.pi * Complex.I * (z : ℂ) = ((2 * Real.pi * z : ℝ) : ℂ) * Complex.I := by
  push_cast; ring

lemma gpz_norm_gaussL {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (s : ℝ) (u : ι → ℝ)
    (n : ι → ℤ) :
    ‖gaussL G s u n‖ = Real.exp (-(Real.pi / s ^ 2) * qForm G (fun i => (n i : ℝ) + u i)) := by
  rw [gaussL, Complex.norm_exp, Complex.ofReal_re]

lemma gpz_norm_gaussR {ι : Type*} [Fintype ι] (G : Matrix ι ι ℝ) (s : ℝ) (w : ι → ℝ)
    (m : ι → ℤ) :
    ‖gaussR G s w m‖ = Real.exp (-(Real.pi * s ^ 2) * qForm G (fun i => (m i : ℝ))) := by
  rw [gaussR, Complex.norm_exp]
  congr 1
  rw [gpz_phase_canon, Complex.add_re, Complex.ofReal_re, Complex.mul_I_re, Complex.ofReal_im,
    neg_zero, add_zero]

lemma gpz_sum_cons {R : ℕ} (a : ℤ) (m' : Fin R → ℤ) (u : Fin (R + 1) → ℝ) :
    (∑ j, (((Fin.cons a m' : Fin (R + 1) → ℤ) j : ℝ)) * u j)
      = (a : ℝ) * u 0 + ∑ j, (m' j : ℝ) * u j.succ := by
  rw [Fin.sum_univ_succ]
  simp

lemma gpz_sum_swap {R : ℕ} (w : Fin R → ℝ) (m' : Fin R → ℤ) :
    (∑ j, w j * (m' j : ℝ)) = ∑ j, (m' j : ℝ) * w j :=
  Finset.sum_congr rfl fun j _ => mul_comm _ _

lemma gpz_gaussR_split {R : ℕ} (G' : Matrix (Fin R) (Fin R) ℝ) (s : ℝ)
    (u' w : Fin R → ℝ) (σ : ℝ) (m' : Fin R → ℤ) :
    gaussR G' s (fun i => u' i + σ * w i) m'
      = gaussR G' s u' m' * Complex.exp (2 * Real.pi * Complex.I *
          ((σ * (∑ j, (m' j : ℝ) * w j) : ℝ) : ℂ)) := by
  have hph : ∀ j, (m' j : ℝ) * (u' j + σ * w j)
      = (m' j : ℝ) * u' j + σ * ((m' j : ℝ) * w j) := fun j => by ring
  have hsum : (∑ j, (m' j : ℝ) * (u' j + σ * w j))
      = (∑ j, (m' j : ℝ) * u' j) + σ * (∑ j, (m' j : ℝ) * w j) := by
    rw [Finset.sum_congr rfl (fun j _ => hph j), Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [gaussR]
  rw [hsum]
  have harg : (((-(Real.pi * s ^ 2) * qForm G' (fun i => (m' i : ℝ))) : ℝ) : ℂ)
        + 2 * Real.pi * Complex.I * (((∑ j, (m' j : ℝ) * u' j)
            + σ * (∑ j, (m' j : ℝ) * w j) : ℝ) : ℂ)
      = (((-(Real.pi * s ^ 2) * qForm G' (fun i => (m' i : ℝ))) : ℝ) : ℂ)
          + 2 * Real.pi * Complex.I * (((∑ j, (m' j : ℝ) * u' j) : ℝ) : ℂ)
        + 2 * Real.pi * Complex.I * ((σ * (∑ j, (m' j : ℝ) * w j) : ℝ) : ℂ) := by
    push_cast; ring
  rw [harg, Complex.exp_add]

lemma gpz_one_dim_sum {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) (hG : G.PosDef)
    (s : ℝ) (hs : 0 < s) (u : Fin (R + 1) → ℝ) (m' : Fin R → ℤ) :
    (∑' a : ℤ, gaussQ G s u m' a)
      = (s : ℂ) / ((Real.sqrt (pSchur G) : ℝ) : ℂ) * ∑' m0 : ℤ, gaussQ3 G s u m' m0 := by
  obtain ⟨hG'pos, hcpos⟩ := peel_tail_schur G hG
  have hc1 : (0 : ℝ) < pSchur G / s ^ 2 := by positivity
  have h := gauss_poisson_1d (pSchur G / s ^ 2) hc1 (∑ j, (m' j : ℝ) * pWind G j) (u 0)
  rw [gpz_one_div_sqrt_div (pSchur G) s hcpos hs] at h
  simp only [gaussQ, gaussQ3]
  exact h

lemma gpz_P0_eq_P2 {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) (s : ℝ)
    (u : Fin (R + 1) → ℝ) (a : ℤ) (m' : Fin R → ℤ) :
    gaussP0 G s u a m' = gaussP2 G s u a m' := by
  simp only [gaussP0, gaussP2, gaussP1, gaussQ, g0, gpz_gaussR_split]
  simp only [gaussR]
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma gpz_fold {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) (hG : G.PosDef)
    (s : ℝ) (hs : 0 < s) (u : Fin (R + 1) → ℝ) (m0 : ℤ) (m' : Fin R → ℤ) :
    gaussP3 G s u m0 m' = gaussR G⁻¹ s u (Fin.cons m0 m') := by
  obtain ⟨hG'pos, hcpos⟩ := peel_tail_schur G hG
  have hsne : s ≠ 0 := ne_of_gt hs
  have hcne : pSchur G ≠ 0 := ne_of_gt hcpos
  have hv : qForm G⁻¹ (fun i => (((Fin.cons m0 m' : Fin (R + 1) → ℤ) i) : ℝ))
      = ((m0 : ℝ) - (∑ j, (m' j : ℝ) * pWind G j)) ^ 2 / pSchur G
        + qForm (pTail G)⁻¹ (fun i => (m' i : ℝ)) := by
    have h := peel_inv_quad G hG (fun i => (((Fin.cons m0 m' : Fin (R + 1) → ℤ) i) : ℝ))
    rw [h]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [gpz_sum_swap (pWind G) m']
  rw [gaussP3, gaussP1, gaussQ3, gaussR, gaussR, hv, gpz_sum_cons m0 m' u]
  simp only [← Complex.exp_add]
  congr 1
  push_cast
  field_simp
  ring

lemma gpz_const {R : ℕ} (G : Matrix (Fin (R + 1)) (Fin (R + 1)) ℝ) (hG : G.PosDef)
    (s : ℝ) (hs : 0 < s) :
    ((s : ℂ) ^ R / ((Real.sqrt (pTail G).det : ℝ) : ℂ)) *
        ((s : ℂ) / ((Real.sqrt (pSchur G) : ℝ) : ℂ))
      = (s : ℂ) ^ (R + 1) / ((Real.sqrt G.det : ℝ) : ℂ) := by
  obtain ⟨hG'pos, hcpos⟩ := peel_tail_schur G hG
  have hdet := peel_det G hG
  have hA : (0 : ℝ) < (pTail G).det := hG'pos.det_pos
  have hsqrt : Real.sqrt G.det = Real.sqrt (pSchur G) * Real.sqrt (pTail G).det := by
    rw [hdet, Real.sqrt_mul (le_of_lt hcpos)]
  have h1 : (Real.sqrt (pSchur G) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hcpos)
  have h2 : ((Real.sqrt (pTail G).det : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hA)
  have h3 : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  rw [hsqrt, pow_succ]
  push_cast
  field_simp

/-! ### The induction -/

lemma finStatementG_zero : finStatementG 0 := by
  intro G hG s hs u
  haveI : Subsingleton (Fin 0 → ℤ) :=
    ⟨fun f g => funext fun i => i.elim0⟩
  have hq : ∀ (A : Matrix (Fin 0) (Fin 0) ℝ) (x : Fin 0 → ℝ), qForm A x = 0 := by
    intro A x; simp [qForm]
  have hL : (∑' m : Fin 0 → ℤ, gaussL G s u m) = 1 := by
    rw [tsum_eq_single (fun i : Fin 0 => i.elim0)
      (fun b hb => absurd (Subsingleton.elim b _) hb)]
    rw [gaussL, hq G]
    simp
  have hR : (∑' m : Fin 0 → ℤ, gaussR G⁻¹ s u m) = 1 := by
    rw [tsum_eq_single (fun i : Fin 0 => i.elim0)
      (fun b hb => absurd (Subsingleton.elim b _) hb)]
    rw [gaussR, hq G⁻¹]
    simp
  rw [hL, hR, Matrix.det_fin_zero]
  simp

lemma finStatementG_succ {R : ℕ} (ih : finStatementG R) : finStatementG (R + 1) := by
  intro G hG s hs u
  obtain ⟨hG'pos, hcpos⟩ := peel_tail_schur G hG
  have hc1pos : (0 : ℝ) < pSchur G / s ^ 2 := by positivity
  have hβpos : (0 : ℝ) < Real.pi / s ^ 2 := by positivity
  have hpi2pos : (0 : ℝ) < Real.pi * s ^ 2 := by positivity
  -- #1 summability
  have hsumL : Summable (fun n : Fin (R + 1) → ℤ => gaussL G s u n) := by
    refine Summable.of_norm_bounded (summable_shifted_gauss G hG (Real.pi / s ^ 2) hβpos u)
      (fun n => ?_)
    exact le_of_eq (gpz_norm_gaussL G s u n)
  have hcons : Summable (fun p : ℤ × (Fin R → ℤ) => gaussL G s u (Fin.cons p.1 p.2)) :=
    (gpz_summable_cons_iff (gaussL G s u)).mpr hsumL
  -- #2 split the first coordinate
  rw [gpz_tsum_cons (gaussL G s u) hcons]
  -- #3 induction hypothesis
  have hB : ∀ a : ℤ, (∑' m' : Fin R → ℤ, gaussL G s u (Fin.cons a m'))
      = ((s : ℂ) ^ R / ((Real.sqrt (pTail G).det : ℝ) : ℂ)) *
          ∑' m' : Fin R → ℤ, gaussP0 G s u a m' := by
    intro a
    have hpoint : ∀ m' : Fin R → ℤ, gaussL G s u (Fin.cons a m')
        = Complex.exp (g0 G s u a) *
            gaussL (pTail G) s (fun i => u i.succ + ((a : ℝ) + u 0) * pWind G i) m' := by
      intro m'
      have hpeel : qForm G (fun i => (((Fin.cons a m' : Fin (R + 1) → ℤ) i) : ℝ) + u i)
          = qForm (pTail G) (fun i => (m' i : ℝ) + (u i.succ + ((a : ℝ) + u 0) * pWind G i))
            + pSchur G * ((a : ℝ) + u 0) ^ 2 := by
        have hf : (fun i : Fin R =>
              (fun i : Fin (R + 1) => (((Fin.cons a m' : Fin (R + 1) → ℤ) i) : ℝ) + u i) i.succ
              + (fun i : Fin (R + 1) => (((Fin.cons a m' : Fin (R + 1) → ℤ) i) : ℝ) + u i) 0
                * pWind G i)
            = (fun i : Fin R => (m' i : ℝ) + (u i.succ + ((a : ℝ) + u 0) * pWind G i)) := by
          funext i
          simp only [Fin.cons_zero, Fin.cons_succ]
          push_cast
          ring
        have h0 : ((fun i : Fin (R + 1) => (((Fin.cons a m' : Fin (R + 1) → ℤ) i) : ℝ) + u i) 0)
            = (a : ℝ) + u 0 := by
          simp only [Fin.cons_zero]
        have h := peel_quad G hG (fun i => (((Fin.cons a m' : Fin (R + 1) → ℤ) i) : ℝ) + u i)
        rw [h, congrArg (qForm (pTail G)) hf, congrArg (fun t : ℝ => pSchur G * t ^ 2) h0]
      simp only [gaussL, g0]
      rw [hpeel, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [tsum_congr hpoint, tsum_mul_left]
    rw [ih (pTail G) hG'pos s hs (fun i => u i.succ + ((a : ℝ) + u 0) * pWind G i)]
    have hfin : (∑' m' : Fin R → ℤ, gaussP0 G s u a m')
        = Complex.exp (g0 G s u a) * ∑' m' : Fin R → ℤ,
            gaussR (pTail G)⁻¹ s (fun i => u i.succ + ((a : ℝ) + u 0) * pWind G i) m' := by
      simp only [gaussP0]
      exact tsum_mul_left
    rw [hfin]
    ring
  rw [tsum_congr hB]
  -- #4 pull the constant out
  have hC : (∑' a : ℤ, ((s : ℂ) ^ R / ((Real.sqrt (pTail G).det : ℝ) : ℂ)) *
        ∑' m' : Fin R → ℤ, gaussP0 G s u a m')
      = ((s : ℂ) ^ R / ((Real.sqrt (pTail G).det : ℝ) : ℂ)) *
        ∑' a : ℤ, ∑' m' : Fin R → ℤ, gaussP0 G s u a m' := tsum_mul_left
  rw [hC]
  -- #5 swap
  have hsumP0 : Summable (fun p : ℤ × (Fin R → ℤ) => gaussP0 G s u p.1 p.2) := by
    have h1 : Summable (fun a : ℤ =>
        Real.exp (-((Real.pi / s ^ 2) * pSchur G) * ((a : ℝ) + u 0) ^ 2)) :=
      gpz_summable_shift_gauss_int ((Real.pi / s ^ 2) * pSchur G) (u 0) (by positivity)
    have h2 : Summable (fun m' : Fin R → ℤ =>
        Real.exp (-(Real.pi * s ^ 2) * qForm (pTail G)⁻¹ (fun i => (m' i : ℝ)))) := by
      have h := summable_shifted_gauss (pTail G)⁻¹ hG'pos.inv (Real.pi * s ^ 2) hpi2pos
        (fun _ => (0 : ℝ))
      simpa using h
    refine Summable.of_norm_bounded
      (Summable.mul_of_nonneg h1 h2 (fun _ => Real.exp_nonneg _) (fun _ => Real.exp_nonneg _))
      (fun p => ?_)
    simp only [gaussP0, g0]
    rw [Complex.norm_mul, Complex.norm_exp, Complex.ofReal_re, gpz_norm_gaussR]
    have he : Real.exp (-(Real.pi / s ^ 2) * pSchur G * ((p.1 : ℝ) + u 0) ^ 2)
        = Real.exp (-((Real.pi / s ^ 2) * pSchur G) * ((p.1 : ℝ) + u 0) ^ 2) := by
      congr 1; ring
    rw [he]
  have hsumP0' : Summable (fun q : (Fin R → ℤ) × ℤ => gaussP0 G s u q.2 q.1) := by
    have h := Equiv.summable_iff (Equiv.prodComm ℤ (Fin R → ℤ))
      (f := fun q : (Fin R → ℤ) × ℤ => gaussP0 G s u q.2 q.1)
    rw [show ((fun q : (Fin R → ℤ) × ℤ => gaussP0 G s u q.2 q.1) ∘
        ⇑(Equiv.prodComm ℤ (Fin R → ℤ))) = fun p : ℤ × (Fin R → ℤ) => gaussP0 G s u p.1 p.2
        from funext fun p => rfl] at h
    exact h.mp hsumP0
  rw [show (∑' a : ℤ, ∑' m' : Fin R → ℤ, gaussP0 G s u a m')
      = ∑' m' : Fin R → ℤ, ∑' a : ℤ, gaussP0 G s u a m'
      from (Summable.tsum_prod hsumP0).symm.trans
        ((Equiv.tsum_eq (Equiv.prodComm ℤ (Fin R → ℤ))
            (fun q : (Fin R → ℤ) × ℤ => gaussP0 G s u q.2 q.1)).trans
          (Summable.tsum_prod hsumP0'))]
  -- #6 rewrite and apply the 1-dimensional identity
  have hE : ∀ m' : Fin R → ℤ, (∑' a : ℤ, gaussP0 G s u a m')
      = gaussP1 G s u m' * ((s : ℂ) / ((Real.sqrt (pSchur G) : ℝ) : ℂ) *
          ∑' m0 : ℤ, gaussQ3 G s u m' m0) := by
    intro m'
    rw [show (∑' a : ℤ, gaussP0 G s u a m') = ∑' a : ℤ, gaussP2 G s u a m'
      from tsum_congr (fun a => gpz_P0_eq_P2 G s u a m')]
    have step : (∑' a : ℤ, gaussP2 G s u a m')
        = gaussP1 G s u m' * (∑' a : ℤ, gaussQ G s u m' a) := by
      simp only [gaussP2]
      exact tsum_mul_left
    rw [step, gpz_one_dim_sum G hG s hs u m']
  rw [tsum_congr hE]
  -- #7 pull out the constant
  have hK : (∑' m' : Fin R → ℤ, gaussP1 G s u m' *
        ((s : ℂ) / ((Real.sqrt (pSchur G) : ℝ) : ℂ) * ∑' m0 : ℤ, gaussQ3 G s u m' m0))
      = (s : ℂ) / ((Real.sqrt (pSchur G) : ℝ) : ℂ) *
        ∑' m' : Fin R → ℤ, gaussP1 G s u m' * ∑' m0 : ℤ, gaussQ3 G s u m' m0 := by
    rw [← tsum_mul_left]
    refine tsum_congr (fun m' => ?_)
    ring
  rw [hK]
  -- #8 push the constant inside
  have hK2 : (∑' m' : Fin R → ℤ, gaussP1 G s u m' * ∑' m0 : ℤ, gaussQ3 G s u m' m0)
      = ∑' m' : Fin R → ℤ, ∑' m0 : ℤ, gaussP3 G s u m0 m' := by
    refine tsum_congr (fun m' => ?_)
    simp only [gaussP3]
    rw [tsum_mul_left]
  rw [hK2]
  -- #9 fold back
  have hsumGinv : Summable (fun m : Fin (R + 1) → ℤ => gaussR G⁻¹ s u m) := by
    refine Summable.of_norm_bounded (g := fun m : Fin (R + 1) → ℤ =>
      Real.exp (-(Real.pi * s ^ 2) * qForm G⁻¹ (fun i => (m i : ℝ)))) ?_
      (fun m => le_of_eq (gpz_norm_gaussR G⁻¹ s u m))
    have h := summable_shifted_gauss G⁻¹ hG.inv (Real.pi * s ^ 2) hpi2pos (fun _ => (0 : ℝ))
    simpa using h
  have hfold : (∑' m' : Fin R → ℤ, ∑' m0 : ℤ, gaussP3 G s u m0 m')
      = ∑' m : Fin (R + 1) → ℤ, gaussR G⁻¹ s u m := by
    rw [← gpz_tsum_cons' (fun m : Fin (R + 1) → ℤ => gaussR G⁻¹ s u m) hsumGinv]
    refine tsum_congr (fun m' => tsum_congr (fun m0 => ?_))
    exact gpz_fold G hG s hs u m0 m'
  rw [hfold]
  -- #10 constants
  rw [← mul_assoc, gpz_const G hG s hs]

lemma finStatementG_all : ∀ n, finStatementG n
  | 0 => finStatementG_zero
  | (n + 1) => finStatementG_succ (finStatementG_all n)

/-- The `Fin n` Poisson identity in the form used by the transport to a general finite type. -/
lemma finStatement_all : ∀ n, finStatement n := fun n => by
  have h := finStatementG_all n
  simpa only [finStatement, finStatementG, gaussL, gaussR] using h

/-- 0-phase Gaussian Poisson summation on `ℤ^κ` for a positive definite quadratic form: for
`G : Matrix κ κ ℝ` positive definite, `s > 0` and a shift `u : κ → ℝ`,
`∑'_{n∈ℤ^κ} exp(-π/s² (n+u)ᵀG(n+u)) = (s^card κ/√det G) ∑'_{m∈ℤ^κ} exp(-π s² mᵀG⁻¹m + 2πi m·u)`.
This is the `c = 0` case of the general shifted Gaussian Poisson summation
(`Submission/Work/HP/Tr/gaussian_poisson_matrix.lean`, where the LHS phase `2πi c·(n+u)` is absent),
stated with a general finite index type rather than `Fin R`.  It is proved here by the peeling
induction on `Fin n` (`finStatementG_all`) together with the transport to a general finite type
(`gauss_poisson_transport`). -/
theorem gaussian_poisson_zero {κ : Type*} [Fintype κ] [DecidableEq κ]
    (G : Matrix κ κ ℝ) (hG : G.PosDef) (s : ℝ) (hs : 0 < s) (u : κ → ℝ) :
    (∑' n : κ → ℤ,
      Complex.exp (((-(Real.pi / s ^ 2) *
        (∑ i, ∑ j, ((n i : ℝ) + u i) * G i j * ((n j : ℝ) + u j))) : ℝ)))
      = ((s : ℂ) ^ Fintype.card κ / ((Real.sqrt G.det : ℝ) : ℂ)) *
        ∑' m : κ → ℤ,
          Complex.exp (((-(Real.pi * s ^ 2) *
              (∑ i, ∑ j, (m i : ℝ) * G⁻¹ i j * (m j : ℝ))) : ℝ)
            + 2 * Real.pi * Complex.I * ((∑ j, (m j : ℝ) * u j : ℝ) : ℂ)) := by
  have hF : ∀ n, finStatement n := finStatement_all
  exact gauss_poisson_transport hF G hG s hs u

end Work.HP.Sig2
