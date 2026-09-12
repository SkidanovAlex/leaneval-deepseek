import Mathlib
import Submission.Commons.LorentzianPolynomials.hessian_aeval_eq
import Submission.Commons.LorentzianPolynomials.strict_subset_L
import Submission.Commons.LorentzianPolynomials.S_closed
import Submission.Commons.LorentzianPolynomials.strict_lorentzian_quadratic_stable
import Submission.Commons.LorentzianPolynomials.closure_diagonalize
import Submission.Commons.LorentzianPolynomials.pderiv_stable_mem_S
import Submission.Commons.Analysis.MvPolynomial.pderiv_stable
import Submission.Commons.Analysis.MvPolynomial.gch_complexHurwitz
import Submission.Commons.Analysis.Complex.Polynomial.plus_x_mul_deriv_stable
import Submission.Commons.Analysis.Complex.Polynomial.deriv_stable_of_stable
import Submission.Commons.Analysis.MvPolynomial.isStable_of_degree_le_one
import Submission.Commons.Combinatorics.MvPolynomial.symmetric_exchange_const_weight

open Finsupp Matrix MvPolynomial UpperHalfPlane Polynomial Topology Set Filter
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.LorentzianPolynomials

/-- second partial derivatives commute -/
lemma ttd_pderiv_comm (n : ℕ) (a b : Fin n) (f : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.pderiv a (MvPolynomial.pderiv b f) =
      MvPolynomial.pderiv b (MvPolynomial.pderiv a f) := by
  classical
  by_cases hab : a = b
  · subst b
    rfl
  · apply MvPolynomial.ext
    intro m
    simp only [MvPolynomial.coeff_pderiv]
    have h1 : (m + (Finsupp.single a (1 : ℕ) : Fin n →₀ ℕ)) b = m b := by
      simp [Finsupp.add_apply, Finsupp.single_apply, hab]
    have h2 : (m + (Finsupp.single b (1 : ℕ) : Fin n →₀ ℕ)) a = m a := by
      simp [Finsupp.add_apply, Finsupp.single_apply, Ne.symm hab]
    rw [h1, h2]
    have hidx : (m + (Finsupp.single a (1 : ℕ) : Fin n →₀ ℕ)) + (Finsupp.single b (1 : ℕ) : Fin n →₀ ℕ)
        = (m + (Finsupp.single b (1 : ℕ) : Fin n →₀ ℕ)) + (Finsupp.single a (1 : ℕ) : Fin n →₀ ℕ) := by
      rw [add_assoc, add_assoc, add_comm (Finsupp.single a (1 : ℕ) : Fin n →₀ ℕ)
        (Finsupp.single b (1 : ℕ) : Fin n →₀ ℕ)]
    rw [hidx]
    ring

/-- Multiplication by a strictly positive real scalar preserves stability. -/
lemma ttd_stable_scalar_pos {n : ℕ} (c : ℝ) (hc : 0 < c) (p : MvPolynomial (Fin n) ℝ)
    (hp : IsStable p) : IsStable (MvPolynomial.C c * p) := by
  rcases hp with hz | hf
  · left
    rw [hz]
    simp
  · right
    intro z
    let zc : Fin n → ℂ := fun i => ((z i : UpperHalfPlane) : ℂ)
    have hz' : MvPolynomial.aeval (R := ℝ) zc p ≠ 0 := by
      have hfun : (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) =
          (UpperHalfPlane.coe ∘ z) := by
        funext i
        rfl
      dsimp [zc]
      rw [hfun]
      exact hf z
    have hcz : ((c : ℂ) ≠ 0) := by exact_mod_cast (ne_of_gt hc)
    have hmain : MvPolynomial.aeval (R := ℝ) zc (MvPolynomial.C c * p) =
        (c : ℂ) * MvPolynomial.aeval (R := ℝ) zc p := by
      simp only [map_mul, MvPolynomial.aeval_C]
      norm_num
    change MvPolynomial.aeval (R := ℝ) zc (MvPolynomial.C c * p) ≠ 0
    exact (hmain ▸ mul_ne_zero hcz hz')



/-! ## Stability and embeddings
Local (side-A) copies of the embedding lemmas: stability is invariant under the
rename `Fin n ↪ Fin (n+1)` given by `Fin.castSucc`. -/

/-- Stability is preserved by renaming along any map (forward direction). -/
lemma ttd_IsStable_rename {n m : ℕ} (e : Fin n → Fin m) (p : MvPolynomial (Fin n) ℝ)
    (h : IsStable p) : IsStable (MvPolynomial.rename e p) := by
  rcases h with hz | hf
  · left
    rw [hz]
    simp
  · right
    intro z
    rw [MvPolynomial.aeval_rename]
    exact hf (fun i : Fin n => z (e i))

/-- Stability is preserved by embedding in one more variable (via `castSucc`). -/
lemma ttd_IsStable_rename_castSucc {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (h : IsStable (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) p)) :
    IsStable p := by
  classical
  let I : UpperHalfPlane := ⟨Complex.I, by simp⟩
  rcases h with hz | hf
  · left
    exact MvPolynomial.rename_injective (Fin.castSucc : Fin n → Fin (n + 1))
      (by intro a b hab; apply Fin.ext; simpa using congrArg Fin.val hab) hz
  · right
    intro z
    let g : Fin (n + 1) → UpperHalfPlane := fun j =>
      if hj : j.1 < n then z ⟨j.1, hj⟩ else I
    have hge : ∀ i : Fin n, g (Fin.castSucc i) = z i := by
      intro i
      dsimp [g]
      simp
    have hfun : ((fun j : Fin (n + 1) => ((g j : UpperHalfPlane) : ℂ)) ∘
          (Fin.castSucc : Fin n → Fin (n + 1))) = (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) := by
      funext i
      simp [hge i]
    have heq : MvPolynomial.aeval (fun i : Fin n => (z i : ℂ)) p =
        MvPolynomial.aeval (fun j : Fin (n + 1) => ((g j : UpperHalfPlane) : ℂ))
          (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) p) := by
      rw [MvPolynomial.aeval_rename]
      rw [hfun]
    change MvPolynomial.aeval (fun i : Fin n => ((z i : ℍ) : ℂ)) p ≠ 0
    rw [heq]
    exact hf g

/-- Embedding via `castSucc` preserves stability in both directions. -/
lemma ttd_IsStable_rename_castSucc_iff {n : ℕ} (p : MvPolynomial (Fin n) ℝ) :
    IsStable (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) p) ↔ IsStable p := by
  constructor
  · exact ttd_IsStable_rename_castSucc p
  · exact ttd_IsStable_rename (Fin.castSucc : Fin n → Fin (n + 1)) p

/-! ## Derivatives of `L n 3` elements -/

/-- Partial derivatives of an `L n 3` element lie in `L n 2` (`= S n 2`). -/
lemma ttd_pderiv_mem_L_of_mem_L_three (n : ℕ) (f : H n 3) (hf : f ∈ L n 3) (j : Fin n) :
    (⟨f.1.pderiv j, f.2.pderiv⟩ : H n 2) ∈ L n 2 := by
  unfold L at hf ⊢
  simp at hf ⊢
  exact hf.2 j

lemma ttd_pderiv_mem_S_of_mem_L_three (n : ℕ) (f : H n 3) (hf : f ∈ L n 3) (j : Fin n) :
    (⟨f.1.pderiv j, f.2.pderiv⟩ : H n 2) ∈ S n 2 := by
  simpa [L] using ttd_pderiv_mem_L_of_mem_L_three n f hf j

end Commons.LorentzianPolynomials
namespace Commons.LorentzianPolynomials

noncomputable section

/-- "slice" polynomial: substitute complex constants `z` in all variables but `i` -/
def ttdD_slicePoly {n : ℕ} (i : Fin n) (z : Fin n → ℂ) (f : MvPolynomial (Fin n) ℝ) : Polynomial ℂ :=
  MvPolynomial.aeval (R := ℝ)
    (fun j : Fin n => if j = i then Polynomial.X else Polynomial.C (z j)) f

/-- evaluating the slice at `w` evaluates `f` at the point whose `i`-th coordinate is `w`. -/
lemma ttdD_slicePoly_eval {n : ℕ} (i : Fin n) (z : Fin n → ℂ) (f : MvPolynomial (Fin n) ℝ) (w : ℂ) :
    (ttdD_slicePoly i z f).eval w =
      MvPolynomial.aeval (R := ℝ) (fun j : Fin n => if j = i then w else z j) f := by
  classical
  unfold ttdD_slicePoly
  let a : Fin n → Polynomial ℂ := fun j => if j = i then Polynomial.X else Polynomial.C (z j)
  let b : Fin n → ℂ := fun j => if j = i then w else z j
  induction f using MvPolynomial.induction_on with
  | C c => simp [a, b]
  | add p q hp hq => simp [hp, hq, b, Polynomial.eval_add]
  | mul_X p j hp =>
      have hmain : Polynomial.eval w ((MvPolynomial.aeval (R := ℝ) a) (p * MvPolynomial.X j)) =
          (MvPolynomial.aeval (R := ℝ) b) (p * MvPolynomial.X j) := by
        rw [show (MvPolynomial.aeval (R := ℝ) a) (p * MvPolynomial.X j) =
            (MvPolynomial.aeval (R := ℝ) a) p * a j by simp [a]]
        rw [show (MvPolynomial.aeval (R := ℝ) b) (p * MvPolynomial.X j) =
            (MvPolynomial.aeval (R := ℝ) b) p * b j by simp [b]]
        rw [Polynomial.eval_mul]
        rw [hp]
        congr 1
        · by_cases hj : j = i
          · subst j
            simp [a, b]
          · simp [a, b, hj]
      simpa [a, b] using hmain

/-- the derivative of the slice is the slice of the partial derivative -/
lemma ttdD_slicePoly_deriv {n : ℕ} (i : Fin n) (z : Fin n → ℂ) (f : MvPolynomial (Fin n) ℝ) :
    (ttdD_slicePoly i z f).derivative = ttdD_slicePoly i z (MvPolynomial.pderiv i f) := by
  classical
  unfold ttdD_slicePoly
  let a : Fin n → Polynomial ℂ := fun j => if j = i then Polynomial.X else Polynomial.C (z j)
  induction f using MvPolynomial.induction_on with
  | C c => simp [a]
  | add p q hp hq =>
      simp only [map_add, map_add]
      rw [hp, hq]
  | mul_X p j hp =>
      by_cases hj : j = i
      · subst j
        have hpm : (MvPolynomial.aeval (R := ℝ) a) (p * MvPolynomial.X i)
            = (MvPolynomial.aeval (R := ℝ) a) p * a i := by simp [a]
        have hdpm : ((MvPolynomial.pderiv i) (p * MvPolynomial.X i))
            = (MvPolynomial.pderiv i) p * MvPolynomial.X i + p := by
          rw [MvPolynomial.pderiv_mul]
          simp [MvPolynomial.pderiv_X]
        rw [hpm, hdpm]
        rw [Polynomial.derivative_mul]
        rw [map_add]
        simp [a, hp]
      · have hX0 : (MvPolynomial.pderiv i) (MvPolynomial.X j) = (0 : MvPolynomial (Fin n) ℝ) := by
          simp [MvPolynomial.pderiv_X, hj]
        have haC : a j = Polynomial.C (z j) := by simp [a, hj]
        have hpm : (MvPolynomial.aeval (R := ℝ) a) (p * MvPolynomial.X j)
            = (MvPolynomial.aeval (R := ℝ) a) p * a j := by simp [a]
        have hdpm : ((MvPolynomial.pderiv i) (p * MvPolynomial.X j))
            = (MvPolynomial.pderiv i) p * MvPolynomial.X j := by
          rw [MvPolynomial.pderiv_mul]
          simp [hX0]
        rw [hpm, hdpm]
        rw [Polynomial.derivative_mul]
        rw [map_mul, MvPolynomial.aeval_X]
        rw [show derivative ((MvPolynomial.aeval (R := ℝ) a) p) * a j =
            (MvPolynomial.aeval (R := ℝ) a) ((MvPolynomial.pderiv i) p) * a j by rw [hp]]
        have hda0 : (a j).derivative = 0 := by
          rw [haC]
          simp
        rw [hda0, mul_zero, add_zero]

/-- the second conjunct of `ttdD_closure_derivative_precedes` (the `≺` part) -/
lemma ttdD_precedes_second_conjunct {n : ℕ} (i : Fin n) (f : MvPolynomial (Fin n) ℝ)
    (hf : Commons.LorentzianPolynomials.IsStable f) :
    Commons.LorentzianPolynomials.IsStable
        (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f +
          MvPolynomial.X (Fin.last n) *
            MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1))
              (MvPolynomial.pderiv i f)) := by
  by_cases hf0 : f = 0
  · left
    subst f
    simp
  · right
    have hstab : ∀ z : Fin n → ℍ,
        MvPolynomial.aeval (R := ℝ) (fun j : Fin n => ((z j : ℍ) : ℂ)) f ≠ 0 := by
      rcases hf with hz | hz
      · exact False.elim (hf0 hz)
      · exact hz
    intro zz
    let zc : Fin n → ℂ := fun j => ((zz (Fin.castSucc j) : ℍ) : ℂ)
    let xc : ℂ := ((zz (Fin.last n) : ℍ) : ℂ)
    let P : Polynomial ℂ := ttdD_slicePoly i zc f
    have him (j : Fin n) : 0 < (zc j).im := by
      dsimp [zc]
      simpa using (zz (Fin.castSucc j)).im_pos
    let u : ℍ := ⟨zc i, him i⟩
    let xh : ℍ := ⟨xc, by
      dsimp [xc]
      simpa using (zz (Fin.last n)).im_pos⟩
    -- slice evaluation at u equals aeval zc f
    have hslice_u : P.eval (u : ℂ) =
        MvPolynomial.aeval (R := ℝ) (fun j : Fin n => zc j) f := by
      dsimp [P, u]
      rw [ttdD_slicePoly_eval]
      apply congrArg (fun g : Fin n → ℂ => MvPolynomial.aeval (R := ℝ) g f)
      funext j
      by_cases hj : j = i
      · subst j
        simp [zc]
      · simp [hj, zc]
    -- P has no zeroes on the upper half plane
    have hPstab : ∀ u₀ : ℍ, P.eval (u₀ : ℂ) ≠ 0 := by
      intro u₀
      -- value at the H-point with coordinate i replaced by u₀
      let pt : Fin n → ℍ := fun j => if h : j = i then u₀ else ⟨zc j, him j⟩
      have hfun : (fun j : Fin n => if j = i then (u₀ : ℂ) else zc j) =
          (fun j : Fin n => ((pt j : ℍ) : ℂ)) := by
        funext j
        by_cases hj : j = i
        · subst j
          simp [pt, zc]
        · simp [hj, pt, zc]
      rw [ttdD_slicePoly_eval]
      rw [hfun]
      exact hstab pt
    -- P is not the zero polynomial
    have hP0 : P ≠ 0 := by
      intro hP0
      have hP0' : P.eval (u : ℂ) = 0 := by rw [hP0]; simp
      have h : MvPolynomial.aeval (R := ℝ) (fun j : Fin n => zc j) f = 0 := by
        rw [← hslice_u]
        exact hP0'
      have hpt : MvPolynomial.aeval (R := ℝ) (fun j : Fin n => (zc j : ℂ)) f ≠ 0 := by
        let pt : Fin n → ℍ := fun j => ⟨zc j, him j⟩
        have hh := hstab pt
        -- aeval over coercion of pt equals aeval over zc
        convert hh using 1
      exact hpt h
    have hU2 := Commons.Analysis.Complex.Polynomial.plus_x_mul_deriv_stable P hP0 hPstab u xh
    -- now relate aeval of the whole expression to the slice quantities
    have hne : P.eval (u : ℂ) + (xh : ℂ) * P.derivative.eval (u : ℂ) ≠ 0 := hU2
    dsimp [xh, u] at hne
    -- the big evaluation
    have hval :
        MvPolynomial.aeval (R := ℝ) (fun j : Fin (n + 1) => ((zz j : ℍ) : ℂ))
          (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f +
            MvPolynomial.X (Fin.last n) *
              MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1))
                (MvPolynomial.pderiv i f)) ≠ 0 := by
      -- expand via aeval lemmas
      rw [map_add, map_mul]
      rw [MvPolynomial.aeval_X]
      rw [MvPolynomial.aeval_rename, MvPolynomial.aeval_rename]
      change MvPolynomial.aeval (R := ℝ) (fun j : Fin n => zc j) f +
          xc * MvPolynomial.aeval (R := ℝ) (fun j : Fin n => zc j) (MvPolynomial.pderiv i f) ≠ 0
      rw [← hslice_u]
      -- derivative slice:
      have hder : (ttdD_slicePoly i zc (MvPolynomial.pderiv i f)).eval (zc i) =
          P.derivative.eval (u : ℂ) := by
        dsimp [P, u]
        rw [← ttdD_slicePoly_deriv]
      have hB : MvPolynomial.aeval (R := ℝ) (fun j : Fin n => zc j) (MvPolynomial.pderiv i f) =
          (ttdD_slicePoly i zc (MvPolynomial.pderiv i f)).eval (zc i) := by
        rw [ttdD_slicePoly_eval]
        apply congrArg (fun g : Fin n → ℂ => MvPolynomial.aeval (R := ℝ) g (MvPolynomial.pderiv i f))
        funext j
        by_cases hj : j = i
        · subst j; simp [zc]
        · simp [hj, zc]
      rw [hB, hder]
      -- hne with the dsimp already applied: zc i = (u : ℂ)?
      simpa [P, zc, xc] using hne
    exact hval
end
end Commons.LorentzianPolynomials

/-! ## Sum above (Lemma 2.5 (4)) -/
namespace Commons.LorentzianPolynomials

open Finsupp Matrix MvPolynomial UpperHalfPlane
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

/-! Helpers: `pderiv` of the "last" variable kills polynomials that do not involve it. -/

private lemma ttdA_pderiv_last_rename_castSucc (n : ℕ) (q : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.pderiv (Fin.last n)
      (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) q) = 0 := by
  classical
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [map_add, hp, hq]
  | mul_X p i hp =>
      have hx : MvPolynomial.pderiv (Fin.last n)
          (MvPolynomial.X (Fin.castSucc i) : MvPolynomial (Fin (n + 1)) ℝ) = 0 := by
        exact MvPolynomial.pderiv_X_of_ne (i := Fin.last n) (j := Fin.castSucc i)
          (σ := Fin (n + 1)) (R := ℝ) (Fin.castSucc_ne_last i)
      rw [map_mul, MvPolynomial.rename_X, pderiv_mul, hp, hx]
      simp

/-- `∂_last (X_last * rename f) = rename f`, when `rename f` does not involve `X_last`. -/
private lemma ttdA_pderiv_last_X_mul_rename (n : ℕ) (f : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.pderiv (Fin.last n)
      (MvPolynomial.X (Fin.last n) *
        MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f) =
      MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f := by
  classical
  rw [pderiv_mul]
  rw [MvPolynomial.pderiv_X_self]
  rw [ttdA_pderiv_last_rename_castSucc n f]
  ring

private lemma ttdA_rename_castSucc_ne_zero (n : ℕ) (f : MvPolynomial (Fin n) ℝ) (hf : f ≠ 0) :
    MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f ≠ 0 := by
  exact (MvPolynomial.rename_injective (Fin.castSucc : Fin n → Fin (n + 1))
    (Fin.castSucc_injective n)).ne hf

/-- Evaluation of a polynomial lifted by the last variable at an appended point. -/
private lemma ttdA_aeval_lastCases_rename (n : ℕ) (u : Fin n → UpperHalfPlane) (w : UpperHalfPlane)
    (q : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.aeval (R := ℝ)
        (fun i : Fin (n + 1) => ((Fin.lastCases w u i : UpperHalfPlane) : ℂ))
        (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) q) =
      MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((u i : UpperHalfPlane) : ℂ)) q := by
  have hfun : (fun i : Fin (n + 1) => ((Fin.lastCases w u i : UpperHalfPlane) : ℂ)) ∘
        (Fin.castSucc : Fin n → Fin (n + 1)) =
      fun i : Fin n => ((u i : UpperHalfPlane) : ℂ) := by
    funext i
    simp [Fin.lastCases_castSucc]
  rw [MvPolynomial.aeval_rename, hfun]

/-- Evaluation of the polynomial `rename g + X_last * rename f`. -/
private lemma ttdA_aeval_linear_last (n : ℕ) (g f : MvPolynomial (Fin n) ℝ)
    (z : Fin (n + 1) → ℂ) :
    MvPolynomial.aeval (R := ℝ) z
        (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) g +
          MvPolynomial.X (Fin.last n) *
            MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f) =
      MvPolynomial.aeval (R := ℝ) (fun i : Fin n => z (Fin.castSucc i)) g +
        z (Fin.last n) *
          MvPolynomial.aeval (R := ℝ) (fun i : Fin n => z (Fin.castSucc i)) f := by
  rw [map_add, map_mul, MvPolynomial.aeval_X]
  rw [MvPolynomial.aeval_rename, MvPolynomial.aeval_rename]
  rfl

/-- Evaluation of the target (positively combined) polynomial. -/
private lemma ttdA_aeval_target (n : ℕ) (f g₁ g₂ : MvPolynomial (Fin n) ℝ) (θ₁ θ₂ : ℝ)
    (z : Fin (n + 1) → ℂ) :
    MvPolynomial.aeval (R := ℝ) z
        (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) (θ₁ • g₁ + θ₂ • g₂) +
          MvPolynomial.X (Fin.last n) *
            MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f) =
      (θ₁ • MvPolynomial.aeval (R := ℝ) (fun i : Fin n => z (Fin.castSucc i)) g₁ +
        θ₂ • MvPolynomial.aeval (R := ℝ) (fun i : Fin n => z (Fin.castSucc i)) g₂) +
        z (Fin.last n) *
          MvPolynomial.aeval (R := ℝ) (fun i : Fin n => z (Fin.castSucc i)) f := by
  rw [map_add, map_mul, MvPolynomial.aeval_X]
  rw [MvPolynomial.aeval_rename]
  rw [map_add, map_smul, map_smul]
  rw [MvPolynomial.aeval_rename]
  abel

/-- The complex core of the argument: if `a + w·c` and `b + w·c` never vanish for
`w` in the upper half plane (with `c ≠ 0`), then the same holds for the positive
combination `(θ₁·a + θ₂·b) + w·c`.  This is the convexity of the closed half-plane
`{z : ℂ | 0 ≤ Im(z/c)}`. -/
private lemma ttdA_upper_linear_comb_ne_zero {a b c : ℂ} {θ₁ θ₂ : ℝ}
    (hθ₁ : 0 ≤ θ₁) (hθ₂ : 0 ≤ θ₂) (hc : c ≠ 0)
    (ha : ∀ w : UpperHalfPlane, a + (w : ℂ) * c ≠ 0)
    (hb : ∀ w : UpperHalfPlane, b + (w : ℂ) * c ≠ 0) :
    ∀ w₀ : UpperHalfPlane, (θ₁ • a + θ₂ • b) + (w₀ : ℂ) * c ≠ 0 := by
  intro w₀ hz
  have haim : 0 ≤ (a / c).im := by
    by_contra hnot
    have hlt : (a / c).im < 0 := lt_of_not_ge hnot
    let w : UpperHalfPlane := ⟨-(a / c), by simpa using (neg_pos.mpr hlt)⟩
    have hz1 : a + (w : ℂ) * c = 0 := by
      dsimp [w]
      field_simp [hc]
      ring
    exact ha w hz1
  have hbim : 0 ≤ (b / c).im := by
    by_contra hnot
    have hlt : (b / c).im < 0 := lt_of_not_ge hnot
    let w : UpperHalfPlane := ⟨-(b / c), by simpa using (neg_pos.mpr hlt)⟩
    have hz1 : b + (w : ℂ) * c = 0 := by
      dsimp [w]
      field_simp [hc]
      ring
    exact hb w hz1
  let u : ℂ := θ₁ • (a / c) + θ₂ • (b / c) + (w₀ : ℂ)
  have huim : 0 < u.im := by
    have hlin : u.im = θ₁ * (a / c).im + θ₂ * (b / c).im + w₀.im := by
      dsimp [u]
      simp
    rw [hlin]
    have hw : 0 < w₀.im := by simpa using w₀.2
    nlinarith
  have hu : u ≠ 0 := by
    intro hu0
    rw [hu0] at huim
    norm_num at huim
  have hfac : (θ₁ • a + θ₂ • b) + (w₀ : ℂ) * c = c * u := by
    dsimp [u]
    field_simp [hc]
  exact (mul_ne_zero hc hu) (hfac ▸ hz)

theorem ttdA_closure_sum_above {n : ℕ} (f g₁ g₂ : MvPolynomial (Fin n) ℝ) (θ₁ θ₂ : ℝ)
    (hθ₁ : 0 ≤ θ₁) (hθ₂ : 0 ≤ θ₂) (hf0 : f ≠ 0)
    (hg₁ : Commons.LorentzianPolynomials.IsStable g₁)
    (hg₂ : Commons.LorentzianPolynomials.IsStable g₂)
    (h₁ : Commons.LorentzianPolynomials.IsStable
      (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) g₁ +
        MvPolynomial.X (Fin.last n) *
          MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f))
    (h₂ : Commons.LorentzianPolynomials.IsStable
      (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) g₂ +
        MvPolynomial.X (Fin.last n) *
          MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f)) :
    Commons.LorentzianPolynomials.IsStable
      (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) (θ₁ • g₁ + θ₂ • g₂) +
        MvPolynomial.X (Fin.last n) *
          MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f) := by
  classical
  let k : Fin n → Fin (n + 1) := Fin.castSucc
  let j : Fin (n + 1) := Fin.last n
  let F : MvPolynomial (Fin (n + 1)) ℝ := MvPolynomial.rename k f
  let P₁ : MvPolynomial (Fin (n + 1)) ℝ := MvPolynomial.rename k g₁ + MvPolynomial.X j * F
  let P₂ : MvPolynomial (Fin (n + 1)) ℝ := MvPolynomial.rename k g₂ + MvPolynomial.X j * F
  have hF0 : F ≠ 0 := by
    simpa [F] using ttdA_rename_castSucc_ne_zero n f hf0
  have hp₁ : MvPolynomial.pderiv (Fin.last n) P₁ = F := by
    dsimp [P₁, F, k, j]
    rw [map_add, ttdA_pderiv_last_rename_castSucc n g₁, ttdA_pderiv_last_X_mul_rename n f]
    simp
  have hp₂ : MvPolynomial.pderiv (Fin.last n) P₂ = F := by
    dsimp [P₂, F, k, j]
    rw [map_add, ttdA_pderiv_last_rename_castSucc n g₂, ttdA_pderiv_last_X_mul_rename n f]
    simp
  have hP₁0 : P₁ ≠ 0 := by
    intro hP0
    apply hF0
    rw [← hp₁, hP0]
    simp
  have hP₂0 : P₂ ≠ 0 := by
    intro hP0
    apply hF0
    rw [← hp₂, hP0]
    simp
  -- stability of the "above" part `F = rename k f`
  have hFstab : Commons.LorentzianPolynomials.IsStable F := by
    have hsp := Commons.Analysis.MvPolynomial.pderiv_stable P₁ (Fin.last n) h₁
    rwa [hp₁] at hsp
  have hFz : ∀ z : Fin (n + 1) → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin (n + 1) => ((z i : UpperHalfPlane) : ℂ)) F ≠ 0 := by
    rcases hFstab with h0 | hnz
    · exact False.elim (hF0 h0)
    · exact hnz
  have hfU : ∀ u : Fin n → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((u i : UpperHalfPlane) : ℂ)) f ≠ 0 := by
    intro u
    let z : Fin (n + 1) → UpperHalfPlane := fun i => Fin.lastCases UpperHalfPlane.I u i
    have hz := hFz z
    have heq : MvPolynomial.aeval (R := ℝ)
        (fun i : Fin (n + 1) => ((z i : UpperHalfPlane) : ℂ)) F =
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((u i : UpperHalfPlane) : ℂ)) f := by
      dsimp [F, z, k]
      exact ttdA_aeval_lastCases_rename n u UpperHalfPlane.I f
    rw [heq] at hz
    exact hz
  have hP₁z : ∀ z : Fin (n + 1) → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin (n + 1) => ((z i : UpperHalfPlane) : ℂ)) P₁ ≠ 0 := by
    rcases h₁ with h0 | hnz
    · exact False.elim (hP₁0 h0)
    · exact hnz
  have hP₂z : ∀ z : Fin (n + 1) → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin (n + 1) => ((z i : UpperHalfPlane) : ℂ)) P₂ ≠ 0 := by
    rcases h₂ with h0 | hnz
    · exact False.elim (hP₂0 h0)
    · exact hnz
  -- main: prove the nonvanishing disjunct of `IsStable`
  right
  intro z
  change MvPolynomial.aeval (R := ℝ)
        (fun i : Fin (n + 1) => ((z i : UpperHalfPlane) : ℂ))
        (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) (θ₁ • g₁ + θ₂ • g₂) +
          MvPolynomial.X (Fin.last n) *
            MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f) ≠ 0
  let u : Fin n → UpperHalfPlane := fun i => z (Fin.castSucc i)
  let w : UpperHalfPlane := z (Fin.last n)
  let zc : Fin n → ℂ := fun i => ((u i : UpperHalfPlane) : ℂ)
  let a : ℂ := MvPolynomial.aeval (R := ℝ) zc g₁
  let b : ℂ := MvPolynomial.aeval (R := ℝ) zc g₂
  let c : ℂ := MvPolynomial.aeval (R := ℝ) zc f
  have hc' : c ≠ 0 := by
    dsimp [c]
    simpa [zc] using hfU u
  have ha : ∀ w' : UpperHalfPlane, a + (w' : ℂ) * c ≠ 0 := by
    intro w'
    let z' : Fin (n + 1) → UpperHalfPlane := fun i => Fin.lastCases w' u i
    have hz' : MvPolynomial.aeval (R := ℝ)
        (fun i : Fin (n + 1) => ((z' i : UpperHalfPlane) : ℂ)) P₁ ≠ 0 := hP₁z z'
    have heq : MvPolynomial.aeval (R := ℝ)
        (fun i : Fin (n + 1) => ((z' i : UpperHalfPlane) : ℂ)) P₁ = a + (w' : ℂ) * c := by
      dsimp [z', P₁, F, k, j, u, zc, a, c]
      rw [ttdA_aeval_linear_last]
      simp [Fin.lastCases_castSucc, Fin.lastCases_last]
    rwa [heq] at hz'
  have hb : ∀ w' : UpperHalfPlane, b + (w' : ℂ) * c ≠ 0 := by
    intro w'
    let z' : Fin (n + 1) → UpperHalfPlane := fun i => Fin.lastCases w' u i
    have hz' : MvPolynomial.aeval (R := ℝ)
        (fun i : Fin (n + 1) => ((z' i : UpperHalfPlane) : ℂ)) P₂ ≠ 0 := hP₂z z'
    have heq : MvPolynomial.aeval (R := ℝ)
        (fun i : Fin (n + 1) => ((z' i : UpperHalfPlane) : ℂ)) P₂ = b + (w' : ℂ) * c := by
      dsimp [z', P₂, F, k, j, u, zc, b, c]
      rw [ttdA_aeval_linear_last]
      simp [Fin.lastCases_castSucc, Fin.lastCases_last]
    rwa [heq] at hz'
  -- the core convexity step
  have hcore := ttdA_upper_linear_comb_ne_zero (a := a) (b := b) (c := c) (θ₁ := θ₁) (θ₂ := θ₂)
    hθ₁ hθ₂ hc' ha hb w
  -- the value of the target polynomial at z is exactly the core expression
  have hval : MvPolynomial.aeval (R := ℝ)
        (fun i : Fin (n + 1) => ((z i : UpperHalfPlane) : ℂ))
        (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) (θ₁ • g₁ + θ₂ • g₂) +
          MvPolynomial.X (Fin.last n) *
            MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f) =
      (θ₁ • a + θ₂ • b) + (w : ℂ) * c := by
    rw [ttdA_aeval_target]
  rw [hval]
  exact hcore

end

end Commons.LorentzianPolynomials

/-! ## Coefficientwise limits of stable polynomials (bounded degree) -/
namespace Commons.Analysis.MvPolynomial

/-! The slice of a multivariate polynomial along an affine complex line. -/

/-- The univariate polynomial `t ↦ p(z + t v)`, viewed as a complex polynomial in `t`. -/
def ttdT_slicePoly (n : ℕ) (z v : Fin n → ℂ) (p : MvPolynomial (Fin n) ℝ) : Polynomial ℂ :=
  MvPolynomial.aeval (R := ℝ)
    (fun i : Fin n => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X) p

lemma ttdT_slicePoly_eval (n : ℕ) (z v : Fin n → ℂ) (p : MvPolynomial (Fin n) ℝ) (b : ℂ) :
    Polynomial.eval b (ttdT_slicePoly n z v p) =
      MvPolynomial.aeval (R := ℝ) (fun i : Fin n => z i + b * v i) p := by
  unfold ttdT_slicePoly
  let a : Fin n → Polynomial ℂ :=
    fun i => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X
  let φ : Polynomial ℂ →ₐ[ℝ] ℂ := (Polynomial.aeval (R := ℂ) b).restrictScalars ℝ
  have h := MvPolynomial.comp_aeval_apply (f := a) (φ := φ) (p := p)
  change φ (MvPolynomial.aeval (R := ℝ) a p) =
    MvPolynomial.aeval (R := ℝ) (fun i => z i + b * v i) p
  have hfun : (fun i => φ (a i)) = (fun i => z i + b * v i) := by
    funext i
    dsimp [φ, a]
    change Polynomial.eval b (Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X) = z i + b * v i
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    ring
  rw [h, hfun]

/-- The slice monomial factor `∏_i (C (z i) + C (v i) X) ^ (m i)`. -/
def ttdT_sliceMon (n : ℕ) (z v : Fin n → ℂ) (m : Fin n →₀ ℕ) : Polynomial ℂ :=
  m.prod fun i k => (Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X) ^ k

lemma ttdT_sliceMon_natDegree_le {n : ℕ} (z v : Fin n → ℂ) (m : Fin n →₀ ℕ) :
    (ttdT_sliceMon n z v m).natDegree ≤ Finsupp.degree m := by
  classical
  let a : Fin n → Polynomial ℂ := fun i => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X
  have hlin : ∀ i, (a i).natDegree ≤ 1 := by
    intro i
    dsimp [a]
    rw [add_comm]
    exact Polynomial.natDegree_linear_le
  calc
    (ttdT_sliceMon n z v m).natDegree = (m.prod fun i k => a i ^ k).natDegree := by rfl
    _ ≤ ∑ i ∈ m.support, (a i ^ m i).natDegree := by
      simpa [Finsupp.prod] using
        (Polynomial.natDegree_prod_le m.support (fun i => a i ^ m i))
    _ ≤ ∑ i ∈ m.support, m i * 1 := by
      apply Finset.sum_le_sum
      intro i hi
      exact (Polynomial.natDegree_pow_le (p := a i) (n := m i)).trans
        (Nat.mul_le_mul_left (m i) (hlin i))
    _ = Finsupp.degree m := by
      rw [Finsupp.degree_apply]
      simp

lemma ttdT_sliceMon_coeff_eq_zero_of_weight_lt {n : ℕ} (z v : Fin n → ℂ) (m : Fin n →₀ ℕ)
    {j : ℕ} (hj : Finsupp.degree m < j) : (ttdT_sliceMon n z v m).coeff j = 0 :=
  Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (ttdT_sliceMon_natDegree_le z v m) hj)

lemma ttdT_slicePoly_coeff_eq_sum_support (n : ℕ) (z v : Fin n → ℂ) (p : MvPolynomial (Fin n) ℝ) (j : ℕ) :
    (ttdT_slicePoly n z v p).coeff j =
      ∑ m ∈ p.support, ((p.coeff m : ℝ) : ℂ) * (ttdT_sliceMon n z v m).coeff j := by
  classical
  let a : Fin n → Polynomial ℂ :=
    fun i => Polynomial.C (z i) + Polynomial.C (v i) * Polynomial.X
  have hae : MvPolynomial.aeval (R := ℝ) a p =
      ∑ m ∈ p.support, Polynomial.C ((p.coeff m : ℝ) : ℂ) * ttdT_sliceMon n z v m := by
    conv_lhs => rw [← MvPolynomial.support_sum_monomial_coeff p]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro m hm
    rw [MvPolynomial.aeval_monomial]
    rfl
  unfold ttdT_slicePoly
  rw [hae]
  rw [Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Polynomial.coeff_C_mul]

lemma ttdT_slicePoly_natDegree_le (n : ℕ) (z v : Fin n → ℂ) (p : MvPolynomial (Fin n) ℝ) :
    (ttdT_slicePoly n z v p).natDegree ≤ p.totalDegree := by
  classical
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [ttdT_slicePoly_coeff_eq_sum_support]
  apply Finset.sum_eq_zero
  intro m hm
  have hdeg_le : Finsupp.degree m ≤ p.totalDegree := by
    have h := MvPolynomial.le_totalDegree (p := p) hm
    simpa [Finsupp.degree_apply, Finsupp.sum] using h
  have hlt : Finsupp.degree m < N := lt_of_le_of_lt hdeg_le hN
  rw [ttdT_sliceMon_coeff_eq_zero_of_weight_lt (m := m) (j := N) (z := z) (v := v) hlt]
  simp

lemma ttdT_slicePoly_eq_partialSum {n D : ℕ} (z v : Fin n → ℂ) (p : MvPolynomial (Fin n) ℝ)
    (hdeg : p.totalDegree ≤ D) :
    ttdT_slicePoly n z v p =
      ∑ i : Fin (D + 1), Polynomial.monomial (i : ℕ) ((ttdT_slicePoly n z v p).coeff (i : ℕ)) := by
  classical
  have hnd : (ttdT_slicePoly n z v p).natDegree ≤ D :=
    le_trans (ttdT_slicePoly_natDegree_le n z v p) hdeg
  have hndlt : (ttdT_slicePoly n z v p).natDegree < D + 1 := Nat.lt_succ_of_le hnd
  have h := Polynomial.as_sum_range' (ttdT_slicePoly n z v p) (D + 1) hndlt
  calc
    ttdT_slicePoly n z v p =
        ∑ i ∈ Finset.range (D + 1), Polynomial.monomial i ((ttdT_slicePoly n z v p).coeff i) := h
    _ = ∑ i : Fin (D + 1), Polynomial.monomial (i : ℕ) ((ttdT_slicePoly n z v p).coeff (i : ℕ)) := by
      exact (Fin.sum_univ_eq_sum_range
        (fun i : ℕ => Polynomial.monomial i ((ttdT_slicePoly n z v p).coeff i)) (D + 1)).symm

/-! The (finite) set of monomials of total degree at most `D`. -/

/-- All monomials in `n` variables of total degree at most `D`, as a finset. -/
def ttdT_monomialsLE (n D : ℕ) : Finset (Fin n →₀ ℕ) := by
  classical
  exact (Finset.range (D + 1)).biUnion
    (fun d : ℕ => (Finset.univ : Finset (Fin n)).finsuppAntidiag d)

lemma mem_ttdT_monomialsLE {n D : ℕ} (m : Fin n →₀ ℕ) :
    m ∈ ttdT_monomialsLE n D ↔ Finsupp.degree m ≤ D := by
  classical
  rw [ttdT_monomialsLE, Finset.mem_biUnion]
  constructor
  · rintro ⟨d, hd, hm⟩
    have hmem := (Finset.mem_finsuppAntidiag).mp hm
    have hd_le : d ≤ D := Nat.le_of_lt_succ (Finset.mem_range.mp hd)
    have hdeg : Finsupp.degree m = d := by
      rw [Finsupp.degree_eq_sum]
      exact hmem.1
    exact le_trans (le_of_eq hdeg) hd_le
  · intro hdeg
    refine ⟨Finsupp.degree m, Finset.mem_range.mpr (Nat.lt_succ_of_le hdeg), ?_⟩
    rw [Finset.mem_finsuppAntidiag]
    simp [Finsupp.degree_eq_sum]

lemma support_subset_ttdT_monomialsLE {n D : ℕ} (p : MvPolynomial (Fin n) ℝ) (hdeg : p.totalDegree ≤ D) :
    p.support ⊆ ttdT_monomialsLE n D := by
  classical
  intro m hm
  rw [mem_ttdT_monomialsLE]
  have h := MvPolynomial.le_totalDegree (p := p) hm
  exact le_trans h hdeg

lemma ttdT_slicePoly_coeff_eq_sum_ttdT_monomialsLE {n D : ℕ} (z v : Fin n → ℂ) (p : MvPolynomial (Fin n) ℝ)
    (hdeg : p.totalDegree ≤ D) (j : ℕ) :
    (ttdT_slicePoly n z v p).coeff j =
      ∑ m ∈ ttdT_monomialsLE n D, ((p.coeff m : ℝ) : ℂ) * (ttdT_sliceMon n z v m).coeff j := by
  classical
  rw [ttdT_slicePoly_coeff_eq_sum_support]
  exact Finset.sum_subset (support_subset_ttdT_monomialsLE p hdeg) (by
    intro m hmS hmnot
    have hc : p.coeff m = 0 := by
      by_contra h
      exact hmnot (MvPolynomial.mem_support_iff.mpr h)
    simp [hc])

lemma ttdT_slicePoly_coeff_tendsto {n D : ℕ} (z v : Fin n → ℂ) (u : ℕ → MvPolynomial (Fin n) ℝ)
    (g : MvPolynomial (Fin n) ℝ)
    (huD : ∀ k : ℕ, (u k).totalDegree ≤ D) (hgD : g.totalDegree ≤ D)
    (hconv : ∀ m : Fin n →₀ ℕ, Tendsto (fun k : ℕ => (u k).coeff m) atTop (𝓝 (g.coeff m)))
    (j : ℕ) :
    Tendsto (fun k : ℕ => (ttdT_slicePoly n z v (u k)).coeff j) atTop
      (𝓝 ((ttdT_slicePoly n z v g).coeff j)) := by
  classical
  rw [show (fun k : ℕ => (ttdT_slicePoly n z v (u k)).coeff j) =
      fun k : ℕ => ∑ m ∈ ttdT_monomialsLE n D,
        (((u k).coeff m : ℝ) : ℂ) * (ttdT_sliceMon n z v m).coeff j by
        funext k
        exact (ttdT_slicePoly_coeff_eq_sum_ttdT_monomialsLE z v (u k) (huD k) j)]
  rw [show (𝓝 ((ttdT_slicePoly n z v g).coeff j)) =
      𝓝 (∑ m ∈ ttdT_monomialsLE n D,
        ((g.coeff m : ℝ) : ℂ) * (ttdT_sliceMon n z v m).coeff j) by
        congr 1
        exact (ttdT_slicePoly_coeff_eq_sum_ttdT_monomialsLE z v g hgD j)]
  refine tendsto_finsetSum (ttdT_monomialsLE n D) ?_
  intro m hm
  have hmc : Tendsto (fun k : ℕ => (((u k).coeff m : ℝ) : ℂ)) atTop (𝓝 (((g.coeff m : ℝ) : ℂ))) := by
    exact (continuous_algebraMap ℝ ℂ).continuousAt.tendsto.comp (hconv m)
  have hcst : Tendsto (fun k : ℕ => (ttdT_sliceMon n z v m).coeff j) atTop
      (𝓝 ((ttdT_sliceMon n z v m).coeff j)) := tendsto_const_nhds
  simpa [mul_comm, mul_left_comm, mul_assoc] using hmc.mul hcst

/-! Convergence of coefficients, a good slice direction, root isolation. -/

lemma exists_monomial_ne_zero_of_ne_zero {n : ℕ} (g : MvPolynomial (Fin n) ℝ) (hg : g ≠ 0) :
    ∃ m : Fin n →₀ ℕ, g.coeff m ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hg
  ext m
  exact h m

lemma coeff_tendsto_of_deg_le {n D : ℕ} (u : ℕ → MvPolynomial (Fin n) ℝ)
    (g : MvPolynomial (Fin n) ℝ)
    (hconv : ∀ m : Fin n →₀ ℕ, Tendsto (fun k : ℕ => (u k).coeff m) atTop (𝓝 (g.coeff m)))
    (hg : g ≠ 0) :
    ∀ᶠ k in atTop, u k ≠ 0 := by
  classical
  rcases exists_monomial_ne_zero_of_ne_zero g hg with ⟨m, hm⟩
  have ht : Tendsto (fun k : ℕ => (u k).coeff m) atTop (𝓝 (g.coeff m)) := hconv m
  have hev : ∀ᶠ k in atTop, (u k).coeff m ≠ 0 := by
    exact ht.eventually_ne hm
  filter_upwards [hev] with k hk
  intro hk0
  apply hk
  rw [hk0]
  simp

lemma exists_ttdT_slicePoly_ne_zero {n : ℕ} (z : Fin n → ℂ) (g : MvPolynomial (Fin n) ℝ)
    (hg : g ≠ 0) :
    ∃ v : Fin n → ℂ, ttdT_slicePoly n z v g ≠ 0 := by
  classical
  by_contra h
  push Not at h
  apply hg
  apply MvPolynomial.funext (p := g) (q := 0)
  intro x
  have hx : MvPolynomial.aeval (R := ℝ) (fun i : Fin n => (x i : ℂ)) g = 0 := by
    have hv := h (fun i : Fin n => (x i : ℂ) - z i)
    have hslice := ttdT_slicePoly_eval n z (fun i : Fin n => (x i : ℂ) - z i) g 1
    rw [hv] at hslice
    have hfun : (fun i : Fin n => z i + 1 * ((x i : ℂ) - z i)) = fun i : Fin n => (x i : ℂ) := by
      funext i
      ring
    simpa [hfun] using hslice.symm
  have h3 := MvPolynomial.aeval_algebraMap_apply (R := ℝ) (A := ℝ) (B := ℂ) (x := x) (p := g)
  have hx0 : (algebraMap ℝ ℂ (MvPolynomial.aeval x g)) = 0 := by
    rw [← h3]
    simpa [Function.comp_def] using hx
  have hx0' : MvPolynomial.aeval x g = 0 := Complex.ofReal_eq_zero.mp hx0
  simpa using hx0'

lemma exists_lt_norm_of_finite_nonzero {s : Finset ℂ} (hs : ∀ z ∈ s, z ≠ 0)
    (hsne : s.Nonempty) : ∃ ρ : ℝ, 0 < ρ ∧ ∀ z ∈ s, ρ < ‖z‖ := by
  classical
  let N : Finset ℝ := s.image (fun z : ℂ => ‖z‖)
  have hNne : N.Nonempty := by
    rcases hsne with ⟨z, hz⟩
    exact ⟨‖z‖, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩
  let m : ℝ := N.min' hNne
  have hm_mem : m ∈ N := Finset.min'_mem N hNne
  have hm_pos : 0 < m := by
    rcases Finset.mem_image.mp hm_mem with ⟨z, hz, hzN⟩
    rw [← hzN]
    exact norm_pos_iff.mpr (hs z hz)
  refine ⟨m / 2, by positivity, ?_⟩
  intro z hz
  have hzn : ‖z‖ ∈ N := Finset.mem_image.mpr ⟨z, hz, rfl⟩
  have hmle : m ≤ ‖z‖ := Finset.min'_le N ‖z‖ hzn
  linarith

lemma exists_root_isolated {p : Polynomial ℂ} (hp : p ≠ 0) (hp0 : p.eval 0 = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, z ∈ Metric.closedBall 0 ρ → z ≠ 0 → p.eval z ≠ 0 := by
  classical
  let S : Set ℂ := {z | z ≠ 0 ∧ p.eval z = 0}
  have hSfin : S.Finite := by
    refine (Polynomial.finite_setOfPred_isRoot hp).subset ?_
    intro z hz
    exact hz.2
  by_cases hS : S = ∅
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz hz0 hroot
    have hzS : z ∈ S := ⟨hz0, hroot⟩
    rw [hS] at hzS
    exact hzS
  · have hSne : S.Nonempty := Set.nonempty_iff_ne_empty.mpr hS
    let T : Finset ℂ := hSfin.toFinset
    have hT : T.Nonempty := by
      rcases hSne with ⟨z, hz⟩
      exact ⟨z, (hSfin.mem_toFinset).mpr hz⟩
    have hTz : ∀ z ∈ T, z ≠ 0 := by
      intro z hz
      exact ((hSfin.mem_toFinset).mp hz).1
    rcases exists_lt_norm_of_finite_nonzero hTz hT with ⟨ρ, hρ0, hρ⟩
    refine ⟨ρ, hρ0, ?_⟩
    intro z hz hz0 hroot
    have hzS : z ∈ S := ⟨hz0, hroot⟩
    have hzT : z ∈ T := (hSfin.mem_toFinset).mpr hzS
    have hzρ : ‖z‖ ≤ ρ := by
      have hzball := Metric.mem_closedBall.mp hz
      simpa using hzball
    have hlt := hρ z hzT  -- ρ < ‖z‖
    linarith

/-- For every `i`, `z i + t (v i)` stays in the upper half plane for `‖t‖`
sufficiently small, uniformly in `i`. -/
lemma exists_stay_upper (n : ℕ) (z v : Fin n → ℂ)
    (hz : ∀ i : Fin n, 0 < (z i).im) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℂ, ‖t‖ < ρ → ∀ i : Fin n, 0 < (z i + t * v i).im := by
  classical
  by_cases hn : Nonempty (Fin n)
  · let ratio : Fin n → ℝ := fun i => (z i).im / (‖v i‖ + 1)
    have hratio_pos : ∀ i, 0 < ratio i := by
      intro i
      dsimp [ratio]
      exact div_pos (hz i) (by positivity)
    let ρ : ℝ := (Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty) ratio) / 2
    have hinf_pos : 0 < Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty) ratio := by
      rw [Finset.lt_inf'_iff]
      intro i hi
      exact hratio_pos i
    have hρpos : 0 < ρ := by
      dsimp [ρ]
      exact div_pos hinf_pos zero_lt_two
    have hρ_lt : ∀ i, ρ < ratio i := by
      intro i
      have hhalf : (Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty) ratio) / 2 <
          Finset.univ.inf' (Finset.univ_nonempty : (Finset.univ : Finset (Fin n)).Nonempty) ratio := by
        rw [div_lt_iff₀ zero_lt_two]
        linarith
      have hle := Finset.inf'_le ratio (Finset.mem_univ i)
      exact lt_of_lt_of_le hhalf hle
    refine ⟨ρ, hρpos, ?_⟩
    intro t ht i
    have h_lt_ratio : ‖t‖ < ratio i := lt_trans ht (hρ_lt i)
    have hden : 0 < ‖v i‖ + 1 := by positivity
    have hmul_lt : ‖t‖ * ‖v i‖ < (z i).im := by
      have hmul : ‖t‖ * ‖v i‖ ≤ ‖t‖ * (‖v i‖ + 1) := by
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right zero_le_one) (norm_nonneg t)
      have hlt' : ‖t‖ * (‖v i‖ + 1) < (z i).im := by
        exact (lt_div_iff₀ hden).mp h_lt_ratio
      exact lt_of_le_of_lt hmul hlt'
    have him : ‖t * v i‖ < (z i).im := by
      simpa [norm_mul] using hmul_lt
    have h_abs_im : |(t * v i).im| < (z i).im :=
      (Complex.abs_im_le_norm (t * v i)).trans_lt him
    have hlow : -((z i).im) < (t * v i).im := (abs_lt.mp h_abs_im).1
    have him_sum : (z i + t * v i).im = (z i).im + (t * v i).im := by
      simp [Complex.add_im]
    rw [him_sum]
    linarith
  · refine ⟨1, by norm_num, ?_⟩
    intro t ht i
    exact False.elim (hn ⟨i⟩)


theorem ttdT_isStable_tendsto_of_degree_le (n D : ℕ) (u : ℕ → MvPolynomial (Fin n) ℝ)
    (g : MvPolynomial (Fin n) ℝ)
    (huD : ∀ k : ℕ, (u k).totalDegree ≤ D) (hgD : g.totalDegree ≤ D)
    (hconv : ∀ m : Fin n →₀ ℕ, Tendsto (fun k : ℕ => (u k).coeff m) atTop (𝓝 (g.coeff m)))
    (hstab : ∀ k : ℕ, (u k) = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) (u k) ≠ 0) :
    g = 0 ∨ ∀ z : Fin n → UpperHalfPlane,
        MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) g ≠ 0 := by
  classical
  by_cases hg : g = 0
  · exact Or.inl hg
  · right
    intro z
    by_contra hz0
    let zc : Fin n → ℂ := fun i => ((z i : UpperHalfPlane) : ℂ)
    have hz0' : MvPolynomial.aeval (R := ℝ) zc g = 0 := by
      simpa [zc] using hz0
    have hz_im : ∀ i : Fin n, 0 < (zc i).im := by
      intro i
      dsimp [zc]
      exact UpperHalfPlane.im_pos (z i)
    obtain ⟨v, hv⟩ := exists_ttdT_slicePoly_ne_zero zc g hg
    let Q : Polynomial ℂ := ttdT_slicePoly n zc v g
    have hQ0 : Q.eval 0 = 0 := by
      change Polynomial.eval 0 (ttdT_slicePoly n zc v g) = 0
      simpa [hz0'] using ttdT_slicePoly_eval n zc v g 0
    obtain ⟨ρ₁, hρ₁0, hiso⟩ := exists_root_isolated (p := Q) hv hQ0
    obtain ⟨ρ₂, hρ₂0, hup⟩ := exists_stay_upper n zc v hz_im
    let ρ : ℝ := min ρ₁ ρ₂
    have hρ0 : 0 < ρ := lt_min hρ₁0 hρ₂0
    have hρ_le₁ : ρ ≤ ρ₁ := min_le_left ρ₁ ρ₂
    have hρ_le₂ : ρ ≤ ρ₂ := min_le_right ρ₁ ρ₂
    have hlim : ∀ i : Fin (D + 1),
        Tendsto (fun k : ℕ => (ttdT_slicePoly n zc v (u k)).coeff (i : ℕ)) atTop
          (𝓝 ((ttdT_slicePoly n zc v g).coeff (i : ℕ))) := by
      intro i
      exact ttdT_slicePoly_coeff_tendsto zc v u g huD hgD hconv (i : ℕ)
    let c : ℕ → Fin (D + 1) → ℂ := fun k i => (ttdT_slicePoly n zc v (u k)).coeff (i : ℕ)
    let cf : Fin (D + 1) → ℂ := fun i => (ttdT_slicePoly n zc v g).coeff (i : ℕ)
    have hsum_eq_g : (∑ i : Fin (D + 1), Polynomial.monomial (i : ℕ) (cf i)) = Q := by
      dsimp [cf, Q]
      exact (ttdT_slicePoly_eq_partialSum zc v g hgD).symm
    have hroot0 : Polynomial.eval 0 (∑ i : Fin (D + 1), Polynomial.monomial (i : ℕ) (cf i)) = 0 := by
      rw [hsum_eq_g]
      exact hQ0
    have hpunct : ∀ w : ℂ, w ∈ Metric.closedBall 0 ρ → w ≠ 0 →
        Polynomial.eval w (∑ i : Fin (D + 1), Polynomial.monomial (i : ℕ) (cf i)) ≠ 0 := by
      intro w hw hw0
      rw [hsum_eq_g]
      have hw₁ : w ∈ Metric.closedBall 0 ρ₁ := by
        exact (Metric.closedBall_subset_closedBall hρ_le₁) hw
      exact hiso w hw₁ hw0
    obtain ⟨N, hN⟩ := gch_complexHurwitz D c cf hlim (0 : ℂ) (ρ := ρ) hρ0 hroot0 hpunct
    have hnev : ∀ᶠ k in atTop, u k ≠ 0 := coeff_tendsto_of_deg_le (n := n) (D := D) u g hconv hg
    have hevge : ∀ᶠ k in atTop, N ≤ k := Filter.eventually_ge_atTop N
    have hevall : ∀ᶠ k in atTop, u k ≠ 0 ∧ N ≤ k := hnev.and hevge
    rw [Filter.eventually_atTop] at hevall
    rcases hevall with ⟨N₀, hN₀⟩
    let k : ℕ := max N₀ N
    have hkprop := hN₀ k (le_max_left N₀ N)
    have huk0 : u k ≠ 0 := hkprop.1
    have hkN : N ≤ k := le_max_right N₀ N
    rcases hN k hkN with ⟨w, hwd, hwroot⟩
    have hwρ : ‖w‖ < ρ := by
      simpa [dist_eq_norm] using hwd
    have hwρ₂ : ‖w‖ < ρ₂ := lt_of_lt_of_le hwρ hρ_le₂
    let z' : Fin n → UpperHalfPlane := fun i => ⟨zc i + w * v i, hup w hwρ₂ i⟩
    have hstabk := hstab k
    cases hstabk with
    | inl hk0 =>
        exact huk0 hk0
    | inr hstable =>
        -- hstable : ∀ z' : Fin n → UpperHalfPlane, aeval (fun i => (z' i : ℂ)) (u k) ≠ 0
        have hcontra : MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z' i : UpperHalfPlane) : ℂ)) (u k) = 0 := by
          have hz'eval : MvPolynomial.aeval (R := ℝ) (fun i : Fin n => zc i + w * v i) (u k) = 0 := by
            have heq : (ttdT_slicePoly n zc v (u k)) = ∑ j : Fin (D + 1),
                Polynomial.monomial (j : ℕ) ((ttdT_slicePoly n zc v (u k)).coeff (j : ℕ)) := by
              exact ttdT_slicePoly_eq_partialSum zc v (u k) (huD k)
            have hwroot' : Polynomial.eval w (ttdT_slicePoly n zc v (u k)) = 0 := by
              -- hwroot is about the c-sum; the c-sum equals the slice
              have hsum_eq_uk : (∑ j : Fin (D + 1), Polynomial.monomial (j : ℕ) (c k j)) =
                  ttdT_slicePoly n zc v (u k) := by
                rw [heq]
              rw [← hsum_eq_uk]
              exact hwroot
            have hslice := ttdT_slicePoly_eval n zc v (u k) w
            simpa using (hslice.symm.trans hwroot')
          simpa [z'] using hz'eval
        exact hstable z' hcontra

end Commons.Analysis.MvPolynomial

/-! # Two-term degenerate: local stability engine -/
namespace Commons.LorentzianPolynomials

/-- Evaluation of the dilated polynomial. -/
lemma ttd_dil_aeval_eval (n : ℕ) (b : Fin n → ℝ) (z : Fin n → ℂ)
    (p : MvPolynomial (Fin n) ℝ) :
    MvPolynomial.aeval (R := ℝ) z
        (MvPolynomial.aeval (R := ℝ) (fun j : Fin n => MvPolynomial.C (b j) * MvPolynomial.X j) p)
      = MvPolynomial.aeval (R := ℝ) (fun j : Fin n => (b j : ℂ) * z j) p := by
  classical
  let φ : MvPolynomial (Fin n) ℝ →ₐ[ℝ] ℂ := MvPolynomial.aeval (R := ℝ) z
  have h := MvPolynomial.comp_aeval_apply
    (f := (fun j : Fin n => MvPolynomial.C (b j) * MvPolynomial.X j)) (φ := φ) (p := p)
  have hφfun : (fun i : Fin n => φ (MvPolynomial.C (b i) * MvPolynomial.X i)) =
      (fun i : Fin n => (b i : ℂ) * z i) := by
    funext i
    dsimp [φ]
    rw [map_mul]
    rw [MvPolynomial.aeval_C, MvPolynomial.aeval_X]
    rfl
  rw [h, hφfun]

/-- Positive dilations preserve stability (direct). -/
lemma ttd_dilate_pos {n : ℕ} (b : Fin n → ℝ) (hb : ∀ j : Fin n, 0 < b j)
    (p : MvPolynomial (Fin n) ℝ) (hp : IsStable p) :
    IsStable (MvPolynomial.aeval (fun j : Fin n => MvPolynomial.C (b j) * MvPolynomial.X j) p) := by
  rcases hp with hz | hf
  · left
    rw [hz]
    simp
  · right
    intro z
    let z' : Fin n → UpperHalfPlane := fun j => ⟨(b j : ℂ) * (z j : ℂ), by
      rw [Complex.mul_im]
      simp
      exact mul_pos (hb j) (z j).im_pos⟩
    have hfun : (fun j : Fin n => ((z' j : UpperHalfPlane) : ℂ)) =
        (fun j : Fin n => (b j : ℂ) * ((z j : UpperHalfPlane) : ℂ)) := by
      funext j
      rfl
    have hmain : MvPolynomial.aeval (R := ℝ) (fun j : Fin n => ((z j : UpperHalfPlane) : ℂ))
          (MvPolynomial.aeval (R := ℝ) (fun j : Fin n => MvPolynomial.C (b j) * MvPolynomial.X j) p) =
        MvPolynomial.aeval (R := ℝ) (fun j : Fin n => ((z' j : UpperHalfPlane) : ℂ)) p := by
      rw [ttd_dil_aeval_eval]
    have hne : MvPolynomial.aeval (R := ℝ) (fun j : Fin n => ((z' j : UpperHalfPlane) : ℂ)) p ≠ 0 :=
      hf z'
    rwa [← hmain] at hne

/-- Diagonalization in `n` variables: substituting `X_a := X_i`. -/
lemma ttd_aeval_diag (n : ℕ) (i a : Fin n) (hia : i ≠ a) (p : MvPolynomial (Fin n) ℝ)
    (hp : IsStable p) : IsStable
    (MvPolynomial.aeval (fun k : Fin n => if k = a then MvPolynomial.X i else MvPolynomial.X k) p) := by
  exact Commons.LorentzianPolynomials.closure_diagonalize i a hia p hp

end Commons.LorentzianPolynomials

/-- Evaluation identity: the value at `w` of `rename g + X_last * rename f`
equals the value of `g` at the first `n` coordinates plus the last coordinate
times the value of `f`. -/
lemma ttd_aeval_linear_last {n : ℕ} (g f : MvPolynomial (Fin n) ℝ)
    (z : Fin (n + 1) → ℂ) :
    MvPolynomial.aeval (R := ℝ) z
        (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) g +
          MvPolynomial.X (Fin.last n) *
            MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f) =
      MvPolynomial.aeval (R := ℝ) (fun i : Fin n => z (Fin.castSucc i)) g +
        z (Fin.last n) *
          MvPolynomial.aeval (R := ℝ) (fun i : Fin n => z (Fin.castSucc i)) f := by
  rw [map_add, map_mul, MvPolynomial.aeval_X]
  rw [MvPolynomial.aeval_rename, MvPolynomial.aeval_rename]
  rfl


namespace Commons.LorentzianPolynomials

/-- The polynomial `rename g + X_last · rename (∂_a g)` is nonzero when `g` is
nonvanishing on the upper half plane. -/
lemma ttd_precedes_P_ne_zero_of_nonzero {n : ℕ} (a : Fin n) (g : MvPolynomial (Fin n) ℝ)
    (hgz : ∀ z : Fin n → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) g ≠ 0) :
    MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) g +
        MvPolynomial.X (Fin.last n) *
          MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) (MvPolynomial.pderiv a g) ≠ 0 := by
  classical
  intro hP0
  let z : Fin n → UpperHalfPlane := fun _ => UpperHalfPlane.I
  let pt : Fin (n + 1) → ℂ := fun j => Fin.lastCases (0 : ℂ)
      (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) j
  have hpt0 : MvPolynomial.aeval (R := ℝ) pt
      (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) g +
        MvPolynomial.X (Fin.last n) *
          MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) (MvPolynomial.pderiv a g)) = 0 := by
    rw [hP0]
    simp
  have hlin := ttd_aeval_linear_last (n := n) g (MvPolynomial.pderiv a g) pt
  rw [hlin] at hpt0
  have hptcast : ∀ i : Fin n, pt (Fin.castSucc i) = ((z i : UpperHalfPlane) : ℂ) := by
    intro i
    simp [pt, z, Fin.lastCases_castSucc]
  have hptlast : pt (Fin.last n) = 0 := by
    simp [pt, Fin.lastCases_last]
  have h0 : MvPolynomial.aeval (R := ℝ) (fun i : Fin n => ((z i : UpperHalfPlane) : ℂ)) g = 0 := by
    simpa [hptcast, hptlast] using hpt0
  exact hgz z h0

/-- If `g` is stable and `c ≥ 0`, then `g + c·X_i·∂_a g` is stable.  (Proof by
evaluating the derivative-precedes polynomial at a point whose last coordinate
equals `c·z_i`.) -/
lemma ttd_stable_X_mul_pderiv {n : ℕ} (i a : Fin n) (c : ℝ) (hc : 0 ≤ c)
    (g : MvPolynomial (Fin n) ℝ) (hg : IsStable g) :
    IsStable (g + MvPolynomial.C c * MvPolynomial.X i * MvPolynomial.pderiv a g) := by
  classical
  by_cases hc0 : c = 0
  · subst c
    simpa using hg
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    let P : MvPolynomial (Fin (n + 1)) ℝ :=
      MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) g +
        MvPolynomial.X (Fin.last n) *
          MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) (MvPolynomial.pderiv a g)
    have hP : IsStable P := by
      simpa [P] using (ttdD_precedes_second_conjunct a g hg)
    rcases hg with hgz0 | hgz
    · left
      rw [hgz0]
      simp
    · right
      have hPne : P ≠ 0 := by
        intro hP0
        have hz0 := ttd_precedes_P_ne_zero_of_nonzero a g hgz
        exact hz0 hP0
      have hPval : ∀ w : Fin (n + 1) → UpperHalfPlane,
          MvPolynomial.aeval (R := ℝ) (fun j : Fin (n + 1) => ((w j : UpperHalfPlane) : ℂ)) P ≠ 0 := by
        rcases hP with h0 | hf
        · exact False.elim (hPne h0)
        · exact hf
      intro z
      let zc : Fin n → ℂ := fun i => ((z i : UpperHalfPlane) : ℂ)
      let wlast : UpperHalfPlane := ⟨c * (zc i), by
        have hzi : 0 < (zc i).im := by simpa [zc] using (z i).im_pos
        rw [Complex.mul_im]
        simp
        exact mul_pos hcpos hzi⟩
      let w : Fin (n + 1) → UpperHalfPlane := fun j => Fin.lastCases wlast z j
      have hwlast : (w (Fin.last n) : ℂ) = c * zc i := by
        simp [w, wlast, Fin.lastCases_last]
      have hwe : ∀ i0 : Fin n, (w (Fin.castSucc i0) : ℂ) = zc i0 := by
        intro i0
        simp [w, zc, Fin.lastCases_castSucc]
      have hPw : MvPolynomial.aeval (R := ℝ) (fun j : Fin (n + 1) => ((w j : UpperHalfPlane) : ℂ)) P ≠ 0 :=
        hPval w
      have hval : MvPolynomial.aeval (R := ℝ) (fun j : Fin (n + 1) => ((w j : UpperHalfPlane) : ℂ)) P =
          MvPolynomial.aeval (R := ℝ) zc g + c * zc i * MvPolynomial.aeval (R := ℝ) zc (MvPolynomial.pderiv a g) := by
        dsimp [P]
        rw [ttd_aeval_linear_last]
        have hfc : (fun i0 : Fin n => ((w (Fin.castSucc i0) : UpperHalfPlane) : ℂ)) = zc := by
          funext i0
          simpa using hwe i0
        rw [hfc, hwlast]
      have hmain : MvPolynomial.aeval (R := ℝ) zc g + c * zc i * MvPolynomial.aeval (R := ℝ) zc (MvPolynomial.pderiv a g) ≠ 0 := by
        rwa [hval] at hPw
      -- target polynomial evaluates to the big sum
      have htarget : MvPolynomial.aeval (R := ℝ) zc
          (g + MvPolynomial.C c * MvPolynomial.X i * MvPolynomial.pderiv a g) =
          MvPolynomial.aeval (R := ℝ) zc g + c * zc i * MvPolynomial.aeval (R := ℝ) zc (MvPolynomial.pderiv a g) := by
        simp only [map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
        norm_num [mul_assoc, mul_comm, mul_left_comm]
      change MvPolynomial.aeval (R := ℝ) zc
          (g + MvPolynomial.C c * MvPolynomial.X i * MvPolynomial.pderiv a g) ≠ 0
      rwa [← htarget] at hmain

/-- `rename castSucc` never produces a monomial with a nonzero last coordinate. -/
lemma ttd_rename_coeff_last_eq_zero {n : ℕ} {q : MvPolynomial (Fin n) ℝ} {m : Fin (n + 1) →₀ ℕ}
    (hm : 1 ≤ m (Fin.last n)) :
    MvPolynomial.coeff m (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) q) = 0 := by
  classical
  apply MvPolynomial.coeff_rename_eq_zero
  intro u hu
  have hz : (u.mapDomain (Fin.castSucc : Fin n → Fin (n + 1))) (Fin.last n) = 0 := by
    rw [Finsupp.mapDomain_of_notMem_range]
    rw [Set.mem_range]
    rintro ⟨a, ha⟩
    exact (Fin.castSucc_ne_last a) ha
  have : m (Fin.last n) = 0 := by
    rw [← hu]
    exact hz
  omega

/-- Coefficient of `X_last * p` at a monomial with positive last coordinate
equals the coefficient of `p` at the monomial with last coordinate decreased. -/
lemma ttd_coeff_X_last_mul {n : ℕ} (p : MvPolynomial (Fin (n + 1)) ℝ)
    (m : Fin (n + 1) →₀ ℕ) (hm : 1 ≤ m (Fin.last n)) :
    MvPolynomial.coeff m (MvPolynomial.X (Fin.last n) * p) =
      MvPolynomial.coeff (m - Finsupp.single (Fin.last n) 1) p := by
  classical
  rw [MvPolynomial.coeff_X_mul']
  have hmem : Fin.last n ∈ m.support := by
    rw [Finsupp.mem_support_iff]
    exact ne_of_gt hm
  simp [hmem]

/-- `rename g' + X_last · rename f` is nonzero when `f ≠ 0`. -/
lemma ttd_ren_X_last_ne_zero {n : ℕ} (g' f : MvPolynomial (Fin n) ℝ) (hf0 : f ≠ 0) :
    MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) g' +
      MvPolynomial.X (Fin.last n) *
        MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f ≠ 0 := by
  classical
  intro hS0
  apply hf0
  apply MvPolynomial.ext
  intro m0
  let m : Fin (n + 1) →₀ ℕ :=
    Finsupp.single (Fin.last n) 1 + m0.mapDomain (Fin.castSucc : Fin n → Fin (n + 1))
  have hm_last : 1 ≤ m (Fin.last n) := by
    dsimp [m]
    have hz : (m0.mapDomain (Fin.castSucc : Fin n → Fin (n + 1))) (Fin.last n) = 0 := by
      rw [Finsupp.mapDomain_of_notMem_range]
      rw [Set.mem_range]
      rintro ⟨a, ha⟩
      exact (Fin.castSucc_ne_last a) ha
    simp [hz]
  have hcS : MvPolynomial.coeff m (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) g' +
      MvPolynomial.X (Fin.last n) *
        MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f) = 0 := by
    rw [hS0]
    simp
  have hcA : MvPolynomial.coeff m (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) g') = 0 :=
    ttd_rename_coeff_last_eq_zero hm_last
  have hcB : MvPolynomial.coeff m (MvPolynomial.X (Fin.last n) *
        MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f) =
      MvPolynomial.coeff m0 f := by
    rw [ttd_coeff_X_last_mul _ _ hm_last]
    have hdecomp : m - Finsupp.single (Fin.last n) 1 =
        m0.mapDomain (Fin.castSucc : Fin n → Fin (n + 1)) := by
      dsimp [m]
      rw [add_tsub_cancel_left]
    rw [hdecomp]
    exact (MvPolynomial.coeff_rename_mapDomain (Fin.castSucc : Fin n → Fin (n + 1))
      (Fin.castSucc_injective n) f m0)
  have hcadd : MvPolynomial.coeff m (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) g') +
      MvPolynomial.coeff m (MvPolynomial.X (Fin.last n) *
        MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f) = 0 := by
    simpa [MvPolynomial.coeff_add] using hcS
  rw [hcA, hcB] at hcadd
  simpa using hcadd

/-- Stability of `θ₁g₁ + θ₂g₂ + c·X_i·f` (the "sum above f, then multiply by `X_i`"
insertion).  `f` interlaces below both `g₁` and `g₂` (encoded by `h₁`, `h₂`). -/
lemma ttd_stable_sum_X_mul {n : ℕ} (f g₁ g₂ : MvPolynomial (Fin n) ℝ) (i : Fin n)
    (θ₁ θ₂ c : ℝ) (hθ₁ : 0 ≤ θ₁) (hθ₂ : 0 ≤ θ₂) (hc : 0 < c) (hf0 : f ≠ 0)
    (hg₁ : IsStable g₁) (hg₂ : IsStable g₂)
    (h₁ : IsStable
      (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) g₁ +
        MvPolynomial.X (Fin.last n) *
          MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f))
    (h₂ : IsStable
      (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) g₂ +
        MvPolynomial.X (Fin.last n) *
          MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f)) :
    IsStable (θ₁ • g₁ + θ₂ • g₂ + MvPolynomial.C c * MvPolynomial.X i * f) := by
  classical
  let S : MvPolynomial (Fin (n + 1)) ℝ :=
    MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) (θ₁ • g₁ + θ₂ • g₂) +
      MvPolynomial.X (Fin.last n) *
        MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) f
  have hS : IsStable S := by
    simpa [S] using (ttdA_closure_sum_above (n := n) f g₁ g₂ θ₁ θ₂ hθ₁ hθ₂ hf0 hg₁ hg₂ h₁ h₂)
  have hSne : S ≠ 0 := by
    simpa [S] using (ttd_ren_X_last_ne_zero (n := n) (θ₁ • g₁ + θ₂ • g₂) f hf0)
  have hSval : ∀ w : Fin (n + 1) → UpperHalfPlane,
      MvPolynomial.aeval (R := ℝ) (fun j : Fin (n + 1) => ((w j : UpperHalfPlane) : ℂ)) S ≠ 0 := by
    rcases hS with h0 | hf
    · exact False.elim (hSne h0)
    · exact hf
  right
  intro z
  let zc : Fin n → ℂ := fun i0 => ((z i0 : UpperHalfPlane) : ℂ)
  let wlast : UpperHalfPlane := ⟨c * (zc i), by
    have hzi : 0 < (zc i).im := by simpa [zc] using (z i).im_pos
    rw [Complex.mul_im]
    simp
    exact mul_pos hc (z i).im_pos⟩
  let w : Fin (n + 1) → UpperHalfPlane := fun j => Fin.lastCases wlast z j
  have hwlast : (w (Fin.last n) : ℂ) = c * zc i := by
    simp [w, wlast, Fin.lastCases_last]
  have hwe : ∀ i0 : Fin n, (w (Fin.castSucc i0) : ℂ) = zc i0 := by
    intro i0
    simp [w, zc, Fin.lastCases_castSucc]
  have hSw : MvPolynomial.aeval (R := ℝ) (fun j : Fin (n + 1) => ((w j : UpperHalfPlane) : ℂ)) S ≠ 0 :=
    hSval w
  have hval : MvPolynomial.aeval (R := ℝ) (fun j : Fin (n + 1) => ((w j : UpperHalfPlane) : ℂ)) S =
      MvPolynomial.aeval (R := ℝ) zc (θ₁ • g₁ + θ₂ • g₂) + c * zc i * MvPolynomial.aeval (R := ℝ) zc f := by
    dsimp [S]
    rw [ttd_aeval_linear_last]
    have hfc : (fun i0 : Fin n => ((w (Fin.castSucc i0) : UpperHalfPlane) : ℂ)) = zc := by
      funext i0
      simpa using hwe i0
    rw [hfc, hwlast]
  have hmain : MvPolynomial.aeval (R := ℝ) zc (θ₁ • g₁ + θ₂ • g₂) + c * zc i * MvPolynomial.aeval (R := ℝ) zc f ≠ 0 := by
    rwa [hval] at hSw
  have htarget : MvPolynomial.aeval (R := ℝ) zc
      (θ₁ • g₁ + θ₂ • g₂ + MvPolynomial.C c * MvPolynomial.X i * f) =
      MvPolynomial.aeval (R := ℝ) zc (θ₁ • g₁ + θ₂ • g₂) + c * zc i * MvPolynomial.aeval (R := ℝ) zc f := by
    simp only [map_add, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
    norm_num [mul_assoc, mul_comm, mul_left_comm]
  change MvPolynomial.aeval (R := ℝ) zc
      (θ₁ • g₁ + θ₂ • g₂ + MvPolynomial.C c * MvPolynomial.X i * f) ≠ 0
  rwa [← htarget] at hmain

/-! # Two-term degenerate: local stability engine -/


lemma ttd_tendsto_one_div_succ (𝕜 : Type*) [DivisionSemiring 𝕜] [CharZero 𝕜]
    [TopologicalSpace 𝕜] [ContinuousSMul ℚ≥0 𝕜] :
    Tendsto (fun k : ℕ => (1 : 𝕜) / (((k : ℕ) : 𝕜) + 1)) atTop (𝓝 0) := by
  simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := 𝕜))

lemma ttd_coeff_C_mul {n : ℕ} (a : ℝ) (p : MvPolynomial (Fin n) ℝ) (m : Fin n →₀ ℕ) :
    (MvPolynomial.C a * p).coeff m = a * p.coeff m :=
  MvPolynomial.coeff_C_mul m a p

lemma ttd_tendsto_coeff_succ {n : ℕ} (poly W : MvPolynomial (Fin n) ℝ) (m : Fin n →₀ ℕ) :
    Tendsto (fun k : ℕ => (poly + MvPolynomial.C ((1 : ℝ) / (((k : ℕ) : ℝ) + 1)) * W).coeff m)
      atTop (𝓝 (poly.coeff m)) := by
  have hs0 : Tendsto (fun k : ℕ => ((1 : ℝ) / (((k : ℕ) : ℝ) + 1)) * W.coeff m) atTop
      (𝓝 ((0 : ℝ) * W.coeff m)) :=
    (ttd_tendsto_one_div_succ ℝ).mul tendsto_const_nhds
  have hs : Tendsto (fun k : ℕ => ((1 : ℝ) / (((k : ℕ) : ℝ) + 1)) * W.coeff m) atTop (𝓝 (0 : ℝ)) := by
    simpa using hs0
  have hconv : Tendsto (fun k : ℕ =>
      poly.coeff m + ((1 : ℝ) / (((k : ℕ) : ℝ) + 1)) * W.coeff m) atTop
      (𝓝 (poly.coeff m + 0)) := tendsto_const_nhds.add hs
  have hk : ∀ k : ℕ, (poly + MvPolynomial.C ((1 : ℝ) / (((k : ℕ) : ℝ) + 1)) * W).coeff m =
      poly.coeff m + ((1 : ℝ) / (((k : ℕ) : ℝ) + 1)) * W.coeff m := by
    intro k
    rw [MvPolynomial.coeff_add, ttd_coeff_C_mul]
  simpa [hk, add_zero] using hconv

/-- partial derivatives of an `L n 3` element are stable quadratics -/
lemma ttd_stable_partial (n : ℕ) (h : H n 3) (hh : h ∈ L n 3) (k : Fin n) :
    IsStable (h.1.pderiv k) := by
  have hS : (⟨h.1.pderiv k, h.2.pderiv⟩ : H n 2) ∈ S n 2 := ttd_pderiv_mem_S_of_mem_L_three n h hh k
  exact hS.1

/-- nonnegativity of coefficients of partials of `h`. -/
lemma ttd_nonneg_partial (n : ℕ) (h : H n 3) (hh : h ∈ L n 3) (k : Fin n) (m : Fin n →₀ ℕ) :
    0 ≤ (h.1.pderiv k).coeff m := by
  have hS : (⟨h.1.pderiv k, h.2.pderiv⟩ : H n 2) ∈ S n 2 := ttd_pderiv_mem_S_of_mem_L_three n h hh k
  exact hS.2 m

/-- the stability of `h.1 + C s · X_i · ∂_{i'} h.1` follows from the derivative-precedes
facts via the deformed-quadratic corollaries. -/
lemma ttd_deformed_two_term_stable (n : ℕ) (i j i' : Fin n) (hij : i ≠ j)
    (h : H n 3) (hh : h ∈ L n 3)
    (hℓ : MvPolynomial.pderiv i (MvPolynomial.pderiv j h.1) = 0)
    (hi0 : MvPolynomial.pderiv i (MvPolynomial.pderiv i' h.1) ≠ 0)
    (hi1 : MvPolynomial.pderiv i' (MvPolynomial.pderiv j h.1) ≠ 0)
    (φ s : ℝ) (hφ : 0 < φ) (hs : 0 < s) :
    IsStable (h.1.pderiv i + MvPolynomial.C φ * h.1.pderiv j
      + MvPolynomial.C s * (h.1.pderiv i'
        + MvPolynomial.X i * MvPolynomial.pderiv i (MvPolynomial.pderiv i' h.1)
        + MvPolynomial.C (2 * φ) * MvPolynomial.X i * MvPolynomial.pderiv i' (MvPolynomial.pderiv j h.1))) := by
  classical
  let A : MvPolynomial (Fin n) ℝ := h.1.pderiv i
  let B : MvPolynomial (Fin n) ℝ := h.1.pderiv j
  let D : MvPolynomial (Fin n) ℝ := h.1.pderiv i'
  let l0 : MvPolynomial (Fin n) ℝ := MvPolynomial.pderiv i (MvPolynomial.pderiv i' h.1)
  let l1 : MvPolynomial (Fin n) ℝ := MvPolynomial.pderiv i' (MvPolynomial.pderiv j h.1)
  let qs : MvPolynomial (Fin n) ℝ := A + MvPolynomial.C s * D + MvPolynomial.C s * (MvPolynomial.X i * l0)
  let rs : MvPolynomial (Fin n) ℝ := B + MvPolynomial.C s * (MvPolynomial.X i * l1)
  have hA : IsStable A := ttd_stable_partial n h hh i
  have hB : IsStable B := ttd_stable_partial n h hh j
  have hD : IsStable D := ttd_stable_partial n h hh i'
  have h_l0_A : MvPolynomial.pderiv i' A = l0 := by
    dsimp [A, l0]
    exact ttd_pderiv_comm n i' i h.1
  have h_l0_D : MvPolynomial.pderiv i D = l0 := by
    dsimp [D, l0]
  have h_l1_B : MvPolynomial.pderiv i' B = l1 := by
    dsimp [B, l1]
  have hq : IsStable qs := by
    have hpre_A : IsStable
        (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) A +
          MvPolynomial.X (Fin.last n) *
            MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) l0) := by
      simpa [h_l0_A] using (ttdD_precedes_second_conjunct i' A hA)
    have hpre_D : IsStable
        (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) D +
          MvPolynomial.X (Fin.last n) *
            MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) l0) := by
      simpa [h_l0_D] using (ttdD_precedes_second_conjunct i D hD)
    have hsum := ttd_stable_sum_X_mul (n := n) l0 A D i (1 : ℝ) s s (by norm_num) (le_of_lt hs) hs
      hi0 hA hD hpre_A hpre_D
    have hconv : IsStable (A + MvPolynomial.C s * D + MvPolynomial.C s * (MvPolynomial.X i * l0)) := by
      simpa [MvPolynomial.smul_eq_C_mul, mul_assoc] using hsum
    simpa [qs] using hconv
  have hr : IsStable rs := by
    have hX : IsStable (B + MvPolynomial.C s * MvPolynomial.X i * MvPolynomial.pderiv i' B) :=
      ttd_stable_X_mul_pderiv i i' s (le_of_lt hs) B hB
    have hconv : IsStable (B + MvPolynomial.C s * (MvPolynomial.X i * l1)) := by
      simpa [h_l1_B, mul_assoc] using hX
    simpa [rs] using hconv
  have hdq : MvPolynomial.pderiv j qs = MvPolynomial.C s * l1 := by
    dsimp [qs]
    rw [map_add, map_add]
    rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_C_mul]
    -- pderiv j (X i * l0) via product rule; X_i independent of j
    have hpX : MvPolynomial.pderiv j (MvPolynomial.X i * l0) = MvPolynomial.X i * MvPolynomial.pderiv j l0 := by
      rw [MvPolynomial.pderiv_mul]
      have hX : MvPolynomial.pderiv j (MvPolynomial.X i : MvPolynomial (Fin n) ℝ) = 0 := by
        exact MvPolynomial.pderiv_X_of_ne (i := j) (j := i) hij
      rw [hX]
      simp
    rw [hpX]
    have hA : MvPolynomial.pderiv j A = 0 := by
      dsimp [A]
      rw [ttd_pderiv_comm n j i h.1]
      rw [hℓ]
    have hD : MvPolynomial.pderiv j D = l1 := by
      dsimp [D, l1]
      exact ttd_pderiv_comm n j i' h.1
    have hl0 : MvPolynomial.pderiv j l0 = 0 := by
      dsimp [l0]
      rw [ttd_pderiv_comm n j i]
      rw [ttd_pderiv_comm n j i']
      rw [ttd_pderiv_comm n i i']
      rw [hℓ]
      simp
    rw [hA, hD, hl0]
    simp
  have hdr : MvPolynomial.pderiv i rs = MvPolynomial.C s * l1 := by
    dsimp [rs]
    rw [map_add]
    rw [MvPolynomial.pderiv_C_mul]
    -- pderiv i (X i * l1) = l1 + X i * pderiv i l1 = l1
    have hB : MvPolynomial.pderiv i B = 0 := by
      dsimp [B]
      rw [hℓ]
    have hl1 : MvPolynomial.pderiv i l1 = 0 := by
      dsimp [l1]
      rw [ttd_pderiv_comm n i i']
      rw [hℓ]
      simp
    have hpX : MvPolynomial.pderiv i (MvPolynomial.X i * l1) = l1 := by
      rw [MvPolynomial.pderiv_mul]
      rw [MvPolynomial.pderiv_X_self]
      rw [hl1]
      simp
    rw [hB, hpX]
    simp
  have hl0s : MvPolynomial.C s * l1 ≠ 0 := by
    have hC : (MvPolynomial.C s : MvPolynomial (Fin n) ℝ) ≠ 0 := by
      intro h
      have := congrArg (fun p : MvPolynomial (Fin n) ℝ => MvPolynomial.coeff 0 p) h
      have hs0 : s = 0 := by
        simpa [MvPolynomial.coeff_C] using this
      exact (ne_of_gt hs) hs0
    exact mul_ne_zero hC hi1
  have hpre_q : IsStable
      (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) qs +
        MvPolynomial.X (Fin.last n) *
          MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) (MvPolynomial.C s * l1)) := by
    simpa [hdq] using (ttdD_precedes_second_conjunct j qs hq)
  have hpre_r : IsStable
      (MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) rs +
        MvPolynomial.X (Fin.last n) *
          MvPolynomial.rename (Fin.castSucc : Fin n → Fin (n + 1)) (MvPolynomial.C s * l1)) := by
    simpa [hdr] using (ttdD_precedes_second_conjunct i rs hr)
  have hsum := ttd_stable_sum_X_mul (n := n) (MvPolynomial.C s * l1) qs rs i (1 : ℝ) φ φ
    (by norm_num) (le_of_lt hφ) hφ hl0s hq hr hpre_q hpre_r
  have hmain : IsStable (qs + MvPolynomial.C φ * rs + MvPolynomial.C φ * MvPolynomial.X i * (MvPolynomial.C s * l1)) := by
    simpa [MvPolynomial.smul_eq_C_mul, mul_assoc] using hsum
  have hid : qs + MvPolynomial.C φ * rs + MvPolynomial.C φ * MvPolynomial.X i * (MvPolynomial.C s * l1)
      = A + MvPolynomial.C φ * B + MvPolynomial.C s * (D + MvPolynomial.X i * l0
        + MvPolynomial.C (2 * φ) * MvPolynomial.X i * l1) := by
    apply MvPolynomial.ext
    intro m
    dsimp [qs, rs]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, MvPolynomial.coeff_add, ttd_coeff_C_mul, MvPolynomial.coeff_add, ttd_coeff_C_mul,
      ttd_coeff_C_mul]
    rw [show MvPolynomial.C φ * MvPolynomial.X i * (MvPolynomial.C s * l1) =
        MvPolynomial.C φ * (MvPolynomial.X i * (MvPolynomial.C s * l1)) by ring]
    rw [ttd_coeff_C_mul, MvPolynomial.coeff_add, ttd_coeff_C_mul]
    rw [show MvPolynomial.X i * (MvPolynomial.C s * l1) = MvPolynomial.C s * (MvPolynomial.X i * l1) by ring]
    rw [ttd_coeff_C_mul, MvPolynomial.coeff_add, ttd_coeff_C_mul]
    rw [ttd_coeff_C_mul]
    -- RHS
    have hC2 : coeff m (MvPolynomial.C (2 * φ) * MvPolynomial.X i * l1) =
        (2 * φ) * coeff m (MvPolynomial.X i * l1) := by
      rw [mul_assoc, ttd_coeff_C_mul]
    rw [MvPolynomial.coeff_add, MvPolynomial.coeff_add]
    rw [hC2]
    ring
  rwa [hid] at hmain



/-- homogeneous degree 3 membership of `h`. -/
lemma ttd_hom3 (n : ℕ) (h : H n 3) : h.1.IsHomogeneous 3 := by
  rw [← MvPolynomial.mem_homogeneousSubmodule]
  exact h.2

/-- partials of a cubic are homogeneous of degree 2. -/
lemma ttd_hom2_pderiv (n : ℕ) (h : H n 3) (k : Fin n) : (h.1.pderiv k).IsHomogeneous 2 := by
  simpa using ((ttd_hom3 n h).pderiv (i := k))

/-- `X_i * (second partial)` is homogeneous of degree 2. -/
lemma ttd_hom2_X_mul_pderiv2 (n : ℕ) (h : H n 3) (i i' : Fin n) :
    (MvPolynomial.X i * MvPolynomial.pderiv i (MvPolynomial.pderiv i' h.1)).IsHomogeneous 2 := by
  have hC : (MvPolynomial.X i : MvPolynomial (Fin n) ℝ).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X (σ := Fin n) (R := ℝ) i
  have hl : (MvPolynomial.pderiv i (MvPolynomial.pderiv i' h.1)).IsHomogeneous 1 := by
    have h1 : (h.1.pderiv i').IsHomogeneous 2 := ttd_hom2_pderiv n h i'
    simpa using (h1.pderiv (i := i))
  have hdeg : 1 + 1 = 2 := by norm_num
  simpa [hdeg] using hC.mul hl




/-- The polynomial `∂_i h + φ · ∂_j h` is homogeneous of degree 2. -/
lemma ttd_hom2_two_term (n : ℕ) (h : H n 3) (i j : Fin n) (φ : ℝ) :
    (h.1.pderiv i + MvPolynomial.C φ * h.1.pderiv j).IsHomogeneous 2 := by
  refine MvPolynomial.IsHomogeneous.add (ttd_hom2_pderiv n h i) ?_
  refine MvPolynomial.IsHomogeneous.mul ?_ (ttd_hom2_pderiv n h j)
  exact MvPolynomial.isHomogeneous_C (σ := Fin n) (R := ℝ) φ

/-- The element of `H n 2` underlying the two-term polynomial. -/
noncomputable def ttd_u_two_term (n : ℕ) (h : H n 3) (i j : Fin n) (φ : ℝ) : H n 2 :=
  ⟨h.1.pderiv i + MvPolynomial.C φ * h.1.pderiv j, by
    rw [MvPolynomial.mem_homogeneousSubmodule]
    exact ttd_hom2_two_term n h i j φ⟩

/-- combinatorial core: if both `∂_i h`, `∂_j h` are nonzero and `∂_i ∂_j h = 0`,
there is an index `i'` whose mixed derivatives with both `i` and `j` are nonzero. -/
lemma ttd_support_degree_three {n : ℕ} (h : H n 3) {m : Fin n →₀ ℕ}
    (hm : m ∈ (h.1.support : Set (Fin n →₀ ℕ))) : Finsupp.degree m = 3 := by
  have hhom : h.1.IsHomogeneous 3 := by
    rw [← MvPolynomial.mem_homogeneousSubmodule]
    exact h.2
  have hmne : h.1.coeff m ≠ 0 := by
    exact (MvPolynomial.mem_support_iff.mp (Finset.mem_coe.mp hm))
  have hw : Finsupp.weight (1 : Fin n → ℕ) m = 3 := hhom hmne
  have hw2 : Finsupp.weight (fun _ : Fin n => 1) m = 3 := by
    change Finsupp.weight (1 : Fin n → ℕ) m = 3
    exact hw
  calc
    Finsupp.degree m = Finsupp.weight (fun _ : Fin n => 1) m := by rw [Finsupp.degree_eq_weight_one]
    _ = 3 := hw2

/-- nonzero polynomial has a nonzero coefficient -/
lemma ttd_exists_coeff_ne_zero {n : ℕ} (f : MvPolynomial (Fin n) ℝ) (hf : f ≠ 0) :
    ∃ m : Fin n →₀ ℕ, f.coeff m ≠ 0 := by
  by_contra h
  apply hf
  apply MvPolynomial.ext
  intro m
  have hz : f.coeff m = 0 := by
    by_contra hc
    exact h ⟨m, hc⟩
  simpa using hz

/-- if `∂_i f ≠ 0` then some monomial of `f` has positive `i`-exponent -/
lemma ttd_pderiv_ne_zero_of_monomial {n : ℕ} (f : MvPolynomial (Fin n) ℝ) (i : Fin n)
    (hf : MvPolynomial.pderiv i f ≠ 0) :
    ∃ m : Fin n →₀ ℕ, m ∈ (f.support : Set (Fin n →₀ ℕ)) ∧ 1 ≤ m i := by
  classical
  rcases ttd_exists_coeff_ne_zero (MvPolynomial.pderiv i f) hf with ⟨m', hm'⟩
  have hc : f.coeff (m' + Finsupp.single i (1 : ℕ)) ≠ 0 := by
    have hformula := MvPolynomial.coeff_pderiv (i := i) f m'
    have : f.coeff (m' + Finsupp.single i (1 : ℕ)) * (m' i + 1) ≠ 0 := by
      simpa [MvPolynomial.coeff_pderiv] using hm'
    exact left_ne_zero_of_mul this
  refine ⟨m' + Finsupp.single i (1 : ℕ), ?_, ?_⟩
  · rw [Finset.mem_coe]
    exact MvPolynomial.mem_support_iff.mpr hc
  · simp


/-- (m - e_i) + e_i = m when m_i ≥ 1 -/
lemma ttd_sub_add_self {n : ℕ} (m : Fin n →₀ ℕ) (i : Fin n) (hi : 1 ≤ m i) :
    (m - Finsupp.single i (1 : ℕ)) + Finsupp.single i (1 : ℕ) = m := by
  ext t
  by_cases hti : t = i
  · subst t
    simp [Finsupp.add_apply, Finsupp.single_apply]
    omega
  · simp [Finsupp.add_apply, Finsupp.single_apply, hti]

/-- coefficient of the single derivative at `m - e_i` is nonzero when `m ∈ support` -/
lemma ttd_coeff_pderiv_single {n : ℕ} (f : MvPolynomial (Fin n) ℝ) (i : Fin n)
    {m : Fin n →₀ ℕ} (hm : m ∈ (f.support : Set (Fin n →₀ ℕ))) (hi : 1 ≤ m i) :
    (MvPolynomial.pderiv i f).coeff (m - Finsupp.single i (1 : ℕ)) ≠ 0 := by
  classical
  have hmc : f.coeff m ≠ 0 := by
    exact (MvPolynomial.mem_support_iff.mp (Finset.mem_coe.mp hm))
  have hformula := MvPolynomial.coeff_pderiv (i := i) f (m - Finsupp.single i (1 : ℕ))
  -- coeff (m - e_i) (pderiv i f) = coeff m f * (m i)
  have hu : (m - Finsupp.single i (1 : ℕ)) + Finsupp.single i (1 : ℕ) = m := ttd_sub_add_self m i hi
  have hmc' : f.coeff ((m - Finsupp.single i (1 : ℕ)) + Finsupp.single i (1 : ℕ)) ≠ 0 := by
    rwa [hu]
  have huinat : (((m - Finsupp.single i (1 : ℕ)) i : ℕ)) = m i - 1 := by simp
  have hfactor : ((((m - Finsupp.single i (1 : ℕ)) i : ℕ) : ℝ) + 1) = (m i : ℝ) := by
    rw [huinat]
    rw [Nat.cast_sub hi]
    ring
  rw [hformula]
  rw [hfactor]
  have hni : (m i : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one hi))
  exact mul_ne_zero hmc' hni

/-- if a monomial of `f` has positive `i`-exponent, then `∂_i f ≠ 0` -/
lemma ttd_pderiv_of_mem {n : ℕ} (f : MvPolynomial (Fin n) ℝ) (i : Fin n)
    {m : Fin n →₀ ℕ} (hm : m ∈ (f.support : Set (Fin n →₀ ℕ))) (hi : 1 ≤ m i) :
    MvPolynomial.pderiv i f ≠ 0 := by
  have hc : (MvPolynomial.pderiv i f).coeff (m - Finsupp.single i (1 : ℕ)) ≠ 0 :=
    ttd_coeff_pderiv_single f i hm hi
  intro hz
  apply hc
  rw [hz]
  simp

/-- coefficient of the mixed derivative at `m - e_a - e_b` is nonzero when both present -/
lemma ttd_coeff_mixed {n : ℕ} (f : MvPolynomial (Fin n) ℝ) (a b : Fin n) (hab : a ≠ b)
    {m : Fin n →₀ ℕ} (hm : m ∈ (f.support : Set (Fin n →₀ ℕ)))
    (hmi : 1 ≤ m a) (hmb : 1 ≤ m b) :
    (MvPolynomial.pderiv a (MvPolynomial.pderiv b f)).coeff (m - Finsupp.single a (1 : ℕ) - Finsupp.single b (1 : ℕ)) ≠ 0 := by
  classical
  -- u := m - e_b is in the support of pderiv b f with u_a ≥ 1
  let u : Fin n →₀ ℕ := m - Finsupp.single b (1 : ℕ)
  have hu_a : 1 ≤ u a := by
    dsimp [u]
    simp [Finsupp.single_apply, hab]
    exact hmi
  have hu_supp : u ∈ ((MvPolynomial.pderiv b f).support : Set (Fin n →₀ ℕ)) := by
    rw [Finset.mem_coe]
    exact MvPolynomial.mem_support_iff.mpr (ttd_coeff_pderiv_single f b hm hmb)
  -- pderiv a (pderiv b f) has nonzero coefficient at u - e_a
  have hc := ttd_coeff_pderiv_single (MvPolynomial.pderiv b f) a hu_supp hu_a
  -- u - e_a = m - e_a - e_b (since a ≠ b)
  have heq : u - Finsupp.single a (1 : ℕ) = m - Finsupp.single a (1 : ℕ) - Finsupp.single b (1 : ℕ) := by
    ext t
    by_cases hta : t = a <;> by_cases htb : t = b
    all_goals
      simp [Finsupp.sub_apply, Finsupp.single_apply, hta, htb, u]
      try omega
  simpa [heq] using hc

/-- mixed derivative is nonzero when a monomial has both variables -/
lemma ttd_mixed_deriv_ne_zero {n : ℕ} (f : MvPolynomial (Fin n) ℝ) (a b : Fin n) (hab : a ≠ b)
    {m : Fin n →₀ ℕ} (hm : m ∈ (f.support : Set (Fin n →₀ ℕ))) (hmi : 1 ≤ m a) (hmb : 1 ≤ m b) :
    MvPolynomial.pderiv a (MvPolynomial.pderiv b f) ≠ 0 := by
  have hc : (MvPolynomial.pderiv a (MvPolynomial.pderiv b f)).coeff
      (m - Finsupp.single a (1 : ℕ) - Finsupp.single b (1 : ℕ)) ≠ 0 :=
    ttd_coeff_mixed f a b hab hm hmi hmb
  intro hz
  apply hc
  rw [hz]
  simp

/-- no monomial contains both `i` and `j` when the mixed derivative vanishes -/
lemma ttd_no_both_of_mixed_zero {n : ℕ} (f : MvPolynomial (Fin n) ℝ) (i j : Fin n)
    (hij : i ≠ j) (hℓ : MvPolynomial.pderiv i (MvPolynomial.pderiv j f) = 0) :
    ∀ m : Fin n →₀ ℕ, m ∈ (f.support : Set (Fin n →₀ ℕ)) → ¬ (1 ≤ m i ∧ 1 ≤ m j) := by
  intro m hm hboth
  have hne := ttd_mixed_deriv_ne_zero f i j hij hm hboth.1 hboth.2
  apply hne
  exact hℓ




lemma ttd_combo_from_se (n : ℕ) (h : H n 3) (hh : h ∈ L n 3) (i j : Fin n) (hij : i ≠ j)
    (hℓ : MvPolynomial.pderiv i (MvPolynomial.pderiv j h.1) = 0)
    (hAi : MvPolynomial.pderiv i h.1 ≠ 0) (hBj : MvPolynomial.pderiv j h.1 ≠ 0) :
    ∃ i' : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i' h.1) ≠ 0 ∧
      MvPolynomial.pderiv i' (MvPolynomial.pderiv j h.1) ≠ 0 := by
  classical
  let J : Set (Fin n →₀ ℕ) := (h.1.support : Set (Fin n →₀ ℕ))
  have hM : h ∈ M n 3 := hh.1
  have hJ : ∀ x ∈ J, ∀ y ∈ J, ∀ i0 : Fin n, x i0 > y i0 →
      ∃ j0 : Fin n, x j0 < y j0 ∧ x - Finsupp.single i0 (1 : ℕ) + Finsupp.single j0 (1 : ℕ) ∈ J := by
    intro x hx y hy i0 hgt
    exact hM.1 x hx y hy i0 hgt
  have hcw : ∀ x ∈ J, Finsupp.degree x = 3 := by
    intro x hx
    exact ttd_support_degree_three h hx
  rcases ttd_pderiv_ne_zero_of_monomial h.1 i hAi with ⟨a, haJ, hai⟩
  rcases ttd_pderiv_ne_zero_of_monomial h.1 j hBj with ⟨b, hbJ, hbj⟩
  have hnoboth : ∀ m : Fin n →₀ ℕ, m ∈ J → ¬ (1 ≤ m i ∧ 1 ≤ m j) := by
    intro m hm
    exact (ttd_no_both_of_mixed_zero h.1 i j hij hℓ) m hm
  have hgt_ab : a i > b i := by
    have hbi0 : b i = 0 := by
      by_contra hbi
      have hbip : 1 ≤ b i := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hbi)
      exact (hnoboth b hbJ) ⟨hbip, hbj⟩
    omega
  rcases Commons.Combinatorics.MvPolynomial.symmetric_exchange_const_weight J hJ hcw a haJ b hbJ i hgt_ab with ⟨k, hklt, hamove, hbmove⟩
  have hkn_i : k ≠ i := by
    intro hki
    have : a k < b k := hklt
    rw [hki] at this
    omega
  have hkj : k = j := by
    by_contra hk
    have hbj1 : 1 ≤ (b - Finsupp.single k (1 : ℕ) + Finsupp.single i (1 : ℕ)) j := by
      have hk0 : (Finsupp.single k (1 : ℕ) : Fin n →₀ ℕ) j = 0 :=
        Finsupp.single_eq_of_ne (a := k) (a' := j) (Ne.symm hk)
      have hi0 : (Finsupp.single i (1 : ℕ) : Fin n →₀ ℕ) j = 0 :=
        Finsupp.single_eq_of_ne (a := i) (a' := j) (Ne.symm hij)
      have hv : (b - Finsupp.single k (1 : ℕ) + Finsupp.single i (1 : ℕ)) j = b j := by
        simp [Finsupp.add_apply, hk0, hi0]
      rw [hv]
      exact hbj
    have hbi0 : b i = 0 := by
      by_contra hbi
      have hbip : 1 ≤ b i := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hbi)
      exact (hnoboth b hbJ) ⟨hbip, hbj⟩
    have hbi1 : 1 ≤ (b - Finsupp.single k (1 : ℕ) + Finsupp.single i (1 : ℕ)) i := by
      have hk0 : (Finsupp.single k (1 : ℕ) : Fin n →₀ ℕ) i = 0 :=
        Finsupp.single_eq_of_ne (a := k) (a' := i) (Ne.symm hkn_i)
      have hv : (b - Finsupp.single k (1 : ℕ) + Finsupp.single i (1 : ℕ)) i = 1 := by
        simp [Finsupp.add_apply, hk0, hbi0]
      rw [hv]
    exact (hnoboth (b - Finsupp.single k (1 : ℕ) + Finsupp.single i (1 : ℕ))) hbmove ⟨hbi1, hbj1⟩
  subst k
  have hamove_j : a - Finsupp.single i (1 : ℕ) + Finsupp.single j (1 : ℕ) ∈ J := hamove
  have hne3 : a ≠ Finsupp.single i (3 : ℕ) := by
    intro h3
    have hb2i : 1 ≤ (a - Finsupp.single i (1 : ℕ) + Finsupp.single j (1 : ℕ)) i := by
      rw [h3]
      simp
      omega
    have hb2j : 1 ≤ (a - Finsupp.single i (1 : ℕ) + Finsupp.single j (1 : ℕ)) j := by
      rw [h3]
      simp
    exact (hnoboth (a - Finsupp.single i (1 : ℕ) + Finsupp.single j (1 : ℕ))) hamove_j ⟨hb2i, hb2j⟩
  have hex : ∃ i' : Fin n, 1 ≤ a i' ∧ i' ≠ i := by
    by_contra hn
    have hoth : ∀ t0 : Fin n, t0 ≠ i → a t0 = 0 := by
      intro t0 ht0
      by_contra hz0
      have hp : 1 ≤ a t0 := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hz0)
      exact hn ⟨t0, hp, ht0⟩
    have ha_only : a = Finsupp.single i (a i) := by
      apply Finsupp.ext
      intro t
      by_cases ht : t = i
      · subst t
        simp
      · have : a t = 0 := hoth t ht
        simp [this, ht]
    have hdeg3 : a i = 3 := by
      have hdega : Finsupp.degree a = a i := by
        rw [ha_only]
        simp [Finsupp.degree_single]
      have hadeg : Finsupp.degree a = 3 := hcw a haJ
      rw [hdega] at hadeg
      exact hadeg
    apply hne3
    rw [ha_only, hdeg3]
  rcases hex with ⟨i', hai', hinei⟩
  have hinej : i' ≠ j := by
    intro hij'
    have haj : 1 ≤ a j := by simpa [hij'] using hai'
    exact (hnoboth a haJ) ⟨hai, haj⟩
  refine ⟨i', ?_, ?_⟩
  · -- pderiv i (pderiv i' h) ≠ 0 via monomial a
    exact ttd_mixed_deriv_ne_zero h.1 i i' (by omega) haJ hai hai'
  · -- pderiv i' (pderiv j h) ≠ 0 via monomial a - e_i + e_j
    have hδi' : 1 ≤ (a - Finsupp.single i (1 : ℕ) + Finsupp.single j (1 : ℕ)) i' := by
      have h1 : (Finsupp.single i (1 : ℕ) : Fin n →₀ ℕ) i' = 0 :=
        Finsupp.single_eq_of_ne (a := i) (a' := i') (by omega)
      have h2 : (Finsupp.single j (1 : ℕ) : Fin n →₀ ℕ) i' = 0 :=
        Finsupp.single_eq_of_ne (a := j) (a' := i') (by omega)
      have hv : (a - Finsupp.single i (1 : ℕ) + Finsupp.single j (1 : ℕ)) i' = a i' := by
        simp [Finsupp.add_apply, h1, h2]
      rw [hv]
      exact hai'
    have haj0 : a j = 0 := by
      by_contra haj
      have hajp : 1 ≤ a j := Nat.succ_le_of_lt (Nat.pos_of_ne_zero haj)
      exact (hnoboth a haJ) ⟨hai, hajp⟩
    have hδj : 1 ≤ (a - Finsupp.single i (1 : ℕ) + Finsupp.single j (1 : ℕ)) j := by
      have h1 : (Finsupp.single i (1 : ℕ) : Fin n →₀ ℕ) j = 0 :=
        Finsupp.single_eq_of_ne (a := i) (a' := j) (Ne.symm hij)
      have hv : (a - Finsupp.single i (1 : ℕ) + Finsupp.single j (1 : ℕ)) j = 1 := by
        simp [Finsupp.add_apply, h1, haj0]
      rw [hv]
    exact ttd_mixed_deriv_ne_zero h.1 i' j (by omega) hamove_j hδi' hδj



lemma ttd_combo_index (n : ℕ) (h : H n 3) (hh : h ∈ L n 3) (i j : Fin n) (hij : i ≠ j)
    (hℓ : MvPolynomial.pderiv i (MvPolynomial.pderiv j h.1) = 0)
    (hAi : MvPolynomial.pderiv i h.1 ≠ 0) (hBj : MvPolynomial.pderiv j h.1 ≠ 0) :
    ∃ i' : Fin n, MvPolynomial.pderiv i (MvPolynomial.pderiv i' h.1) ≠ 0 ∧
      MvPolynomial.pderiv i' (MvPolynomial.pderiv j h.1) ≠ 0 := by
  exact ttd_combo_from_se n h hh i j hij hℓ hAi hBj


/-- total degree bound for the candidate `u` and its deformations -/
lemma ttd_hom2_C_mul_X_pderiv2 (n : ℕ) (h : H n 3) (φ : ℝ) (i a b : Fin n) :
    ((MvPolynomial.C φ * (MvPolynomial.X i * MvPolynomial.pderiv a (MvPolynomial.pderiv b h.1))) :
        MvPolynomial (Fin n) ℝ).IsHomogeneous 2 := by
  have hin : ((MvPolynomial.X i * MvPolynomial.pderiv a (MvPolynomial.pderiv b h.1)) :
        MvPolynomial (Fin n) ℝ).IsHomogeneous 2 := by
    have hC : (MvPolynomial.X i : MvPolynomial (Fin n) ℝ).IsHomogeneous 1 :=
      MvPolynomial.isHomogeneous_X (σ := Fin n) (R := ℝ) i
    have hl : (MvPolynomial.pderiv a (MvPolynomial.pderiv b h.1) : MvPolynomial (Fin n) ℝ).IsHomogeneous 1 := by
      have h1 : (h.1.pderiv b).IsHomogeneous 2 := ttd_hom2_pderiv n h b
      simpa using (h1.pderiv (i := a))
    have hdeg : 1 + 1 = 2 := by norm_num
    simpa [hdeg] using hC.mul hl
  simpa using (MvPolynomial.IsHomogeneous.mul
    (MvPolynomial.isHomogeneous_C (σ := Fin n) (R := ℝ) φ) hin)

/-- the deformed two-term polynomial `poly + C s * W` is stable for every s > 0 -/
lemma ttd_deformed_stable_affine (n : ℕ) (i j i' : Fin n) (hij : i ≠ j)
    (h : H n 3) (hh : h ∈ L n 3)
    (hℓ : MvPolynomial.pderiv i (MvPolynomial.pderiv j h.1) = 0)
    (hi0 : MvPolynomial.pderiv i (MvPolynomial.pderiv i' h.1) ≠ 0)
    (hi1 : MvPolynomial.pderiv i' (MvPolynomial.pderiv j h.1) ≠ 0)
    (φ s : ℝ) (hφ : 0 < φ) (hs : 0 < s) :
    IsStable (h.1.pderiv i + MvPolynomial.C φ * h.1.pderiv j
      + MvPolynomial.C s * (h.1.pderiv i'
        + MvPolynomial.X i * MvPolynomial.pderiv i (MvPolynomial.pderiv i' h.1)
        + MvPolynomial.C (2 * φ) * MvPolynomial.X i * MvPolynomial.pderiv i' (MvPolynomial.pderiv j h.1))) := by
  exact ttd_deformed_two_term_stable n i j i' hij h hh hℓ hi0 hi1 φ s hφ hs


/-- the correction polynomial `W` is homogeneous of degree 2 -/
lemma ttd_hom2_W (n : ℕ) (h : H n 3) (i i' j : Fin n) (φ : ℝ) :
    ((h.1.pderiv i'
      + MvPolynomial.X i * MvPolynomial.pderiv i (MvPolynomial.pderiv i' h.1)
      + MvPolynomial.C (2 * φ) * MvPolynomial.X i * MvPolynomial.pderiv i' (MvPolynomial.pderiv j h.1)) :
        MvPolynomial (Fin n) ℝ).IsHomogeneous 2 := by
  have hAB : ((h.1.pderiv i'
      + MvPolynomial.X i * MvPolynomial.pderiv i (MvPolynomial.pderiv i' h.1)) :
        MvPolynomial (Fin n) ℝ).IsHomogeneous 2 :=
    MvPolynomial.IsHomogeneous.add (ttd_hom2_pderiv n h i') (ttd_hom2_X_mul_pderiv2 n h i i')
  have hC3 : ((MvPolynomial.C (2 * φ) * MvPolynomial.X i * MvPolynomial.pderiv i' (MvPolynomial.pderiv j h.1)) :
        MvPolynomial (Fin n) ℝ).IsHomogeneous 2 := by
    rw [mul_assoc]
    exact ttd_hom2_C_mul_X_pderiv2 n h (2 * φ) i i' j
  exact MvPolynomial.IsHomogeneous.add hAB hC3

/-- a homogeneous degree-2 polynomial has total degree at most 2 -/
lemma ttd_totalDegree_le_two_of_hom_two {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous 2) : p.totalDegree ≤ 2 := hp.totalDegree_le

/-- Main: the degenerate two-term quadratic is a stable homogeneous polynomial
with nonnegative coefficients. -/
lemma ttd_degenerate_two_term_mem_S (n : ℕ) (hn : 0 < n) (i j : Fin n)
    (h : H n 3) (hh : h ∈ L n 3)
    (hℓ : MvPolynomial.pderiv i (MvPolynomial.pderiv j h.1) = 0)
    (φ : ℝ) (hφ : 0 ≤ φ) :
    ∃ u : H n 2, u ∈ S n 2 ∧
      u.1 = MvPolynomial.pderiv i h.1 + MvPolynomial.C φ * MvPolynomial.pderiv j h.1 := by
  classical
  let poly : MvPolynomial (Fin n) ℝ := h.1.pderiv i + MvPolynomial.C φ * h.1.pderiv j
  let u : H n 2 := ttd_u_two_term n h i j φ
  refine ⟨u, ?_, ?_⟩
  · change IsStable u.1 ∧ ∀ m : Fin n →₀ ℕ, 0 ≤ u.1.coeff m
    constructor
    · change IsStable poly
      by_cases hφ0 : φ = 0
      · subst φ
        have hA : IsStable (h.1.pderiv i) := ttd_stable_partial n h hh i
        simpa [poly] using hA
      · have hφp : 0 < φ := lt_of_le_of_ne hφ (Ne.symm hφ0)
        by_cases hij : i = j
        · subst j
          have hsc : IsStable (MvPolynomial.C (1 + φ) * h.1.pderiv i) :=
            ttd_stable_scalar_pos (1 + φ) (by positivity) (h.1.pderiv i) (ttd_stable_partial n h hh i)
          have hid : h.1.pderiv i + MvPolynomial.C φ * h.1.pderiv i =
              MvPolynomial.C (1 + φ) * h.1.pderiv i := by
            apply MvPolynomial.ext
            intro m
            rw [MvPolynomial.coeff_add, ttd_coeff_C_mul, ttd_coeff_C_mul]
            ring
          have hpoly : poly = MvPolynomial.C (1 + φ) * h.1.pderiv i := by
            simpa [poly] using hid
          rwa [hpoly]
        · by_cases hAi0 : h.1.pderiv i = 0
          · have hsc : IsStable (MvPolynomial.C φ * h.1.pderiv j) :=
              ttd_stable_scalar_pos φ hφp (h.1.pderiv j) (ttd_stable_partial n h hh j)
            have hpoly : poly = MvPolynomial.C φ * h.1.pderiv j := by
              dsimp [poly]
              rw [hAi0]
              simp
            rwa [hpoly]
          · by_cases hBj0 : h.1.pderiv j = 0
            · have hA : IsStable (h.1.pderiv i) := ttd_stable_partial n h hh i
              have hpoly : poly = h.1.pderiv i := by
                dsimp [poly]
                rw [hBj0]
                simp
              rwa [hpoly]
            · rcases ttd_combo_index n h hh i j hij hℓ hAi0 hBj0 with ⟨i', hi0, hi1⟩
              let W : MvPolynomial (Fin n) ℝ := h.1.pderiv i'
                + MvPolynomial.X i * MvPolynomial.pderiv i (MvPolynomial.pderiv i' h.1)
                + MvPolynomial.C (2 * φ) * MvPolynomial.X i * MvPolynomial.pderiv i' (MvPolynomial.pderiv j h.1)
              have hdef : ∀ s : ℝ, 0 < s → IsStable (poly + MvPolynomial.C s * W) := by
                intro s hs
                have hx := ttd_deformed_stable_affine n i j i' hij h hh hℓ hi0 hi1 φ s hφp hs
                simpa [poly, W] using hx
              have hstab : ∀ k : ℕ, (poly + MvPolynomial.C ((1 : ℝ) / (((k : ℕ) : ℝ) + 1)) * W) = 0 ∨
                  ∀ z : Fin n → UpperHalfPlane,
                    MvPolynomial.aeval (R := ℝ) (fun a : Fin n => ((z a : UpperHalfPlane) : ℂ))
                      (poly + MvPolynomial.C ((1 : ℝ) / (((k : ℕ) : ℝ) + 1)) * W) ≠ 0 := by
                intro k
                have hs : 0 < (1 : ℝ) / (((k : ℕ) : ℝ) + 1) := by positivity
                exact hdef ((1 : ℝ) / (((k : ℕ) : ℝ) + 1)) hs
              have hconv : ∀ m : Fin n →₀ ℕ,
                  Tendsto (fun k : ℕ => (poly + MvPolynomial.C ((1 : ℝ) / (((k : ℕ) : ℝ) + 1)) * W).coeff m)
                    atTop (𝓝 (poly.coeff m)) := by
                intro m
                exact ttd_tendsto_coeff_succ poly W m
              have hhomseq : ∀ k : ℕ, (poly + MvPolynomial.C ((1 : ℝ) / (((k : ℕ) : ℝ) + 1)) * W).IsHomogeneous 2 := by
                intro k
                refine MvPolynomial.IsHomogeneous.add (ttd_hom2_two_term n h i j φ) ?_
                refine MvPolynomial.IsHomogeneous.mul ?_ (ttd_hom2_W n h i i' j φ)
                exact MvPolynomial.isHomogeneous_C (σ := Fin n) (R := ℝ) ((1 : ℝ) / (((k : ℕ) : ℝ) + 1))
              have hdegseq : ∀ k : ℕ, (poly + MvPolynomial.C ((1 : ℝ) / (((k : ℕ) : ℝ) + 1)) * W).totalDegree ≤ 2 := by
                intro k
                exact ttd_totalDegree_le_two_of_hom_two _ (hhomseq k)
              have hdegpoly : poly.totalDegree ≤ 2 := ttd_totalDegree_le_two_of_hom_two poly (ttd_hom2_two_term n h i j φ)
              have hlim := Commons.Analysis.MvPolynomial.ttdT_isStable_tendsto_of_degree_le n 2
                (fun k : ℕ => poly + MvPolynomial.C ((1 : ℝ) / (((k : ℕ) : ℝ) + 1)) * W) poly
                hdegseq hdegpoly hconv hstab
              exact hlim
    · -- nonnegativity
      intro m
      dsimp [u, poly, ttd_u_two_term]
      rw [MvPolynomial.coeff_add, ttd_coeff_C_mul]
      exact add_nonneg (ttd_nonneg_partial n h hh i m) (mul_nonneg hφ (ttd_nonneg_partial n h hh j m))
  · rfl

/-- The degenerate two-term case of the degree-three deformation lemma:
if `h ∈ L n 3` and the mixed second derivative `∂ᵢ∂ⱼh` vanishes, then for every
`φ ≥ 0` the quadratic `∂ᵢh + φ·∂ⱼh` is a stable homogeneous polynomial with
nonnegative coefficients. -/
theorem two_term_degenerate_mem_S (n : ℕ) (hn : 0 < n) (i j : Fin n)
    (h : Commons.LorentzianPolynomials.H n 3)
    (hh : h ∈ Commons.LorentzianPolynomials.L n 3)
    (hℓ : MvPolynomial.pderiv i (MvPolynomial.pderiv j h.1) = 0)
    (φ : ℝ) (hφ : 0 ≤ φ) :
    ∃ u : Commons.LorentzianPolynomials.H n 2,
      u ∈ Commons.LorentzianPolynomials.S n 2 ∧
        u.1 = MvPolynomial.pderiv i h.1 +
          MvPolynomial.C φ * MvPolynomial.pderiv j h.1 := by
  exact ttd_degenerate_two_term_mem_S n hn i j h hh hℓ φ hφ

end Commons.LorentzianPolynomials
