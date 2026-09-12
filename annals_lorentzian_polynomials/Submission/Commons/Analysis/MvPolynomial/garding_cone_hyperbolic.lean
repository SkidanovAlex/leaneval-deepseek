import Mathlib
import Submission.Commons.Analysis.MvPolynomial.isStable_closed
import Submission.Commons.Analysis.MvPolynomial.realRooted_limit_closed
import Submission.Commons.Analysis.MvPolynomial.gch_complexHurwitz
import Submission.Commons.Analysis.MvPolynomial.gch_bivariate

noncomputable section
open MvPolynomial Polynomial BigOperators
open scoped BigOperators Topology ComplexConjugate

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Commons.Analysis.MvPolynomial

/-- The real univariate polynomial obtained by restricting `H` to the real affine line
`a + ℝe`, i.e. `t ↦ H (a + t•e)`. -/
def gchRealLine {m : ℕ} (H : MvPolynomial (Fin m) ℝ) (a e : Fin m → ℝ) : Polynomial ℝ :=
  MvPolynomial.aeval (R := ℝ)
    (fun i : Fin m => Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X) H

/-- The complex univariate polynomial obtained by restricting `H` to the complex affine
line `a + ℂe` (with `a e : Fin m → ℂ`). -/
def gchCLine {m : ℕ} (H : MvPolynomial (Fin m) ℝ) (a e : Fin m → ℂ) : Polynomial ℂ :=
  MvPolynomial.aeval (R := ℝ)
    (fun i : Fin m => Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X) H

/-- Complexified real evaluation equals `aeval`. -/
lemma gch_eval_map_eq_aeval (p : Polynomial ℝ) (z : ℂ) :
    Polynomial.eval z (Polynomial.map (algebraMap ℝ ℂ) p) = Polynomial.aeval z p := by
  exact Polynomial.eval_map_algebraMap p z

/-- Evaluating the complex line polynomial at `t` equals evaluating `H` at `a + t•e`. -/
lemma gch_cLine_eval {m : ℕ} (H : MvPolynomial (Fin m) ℝ) (a e : Fin m → ℂ) (t : ℂ) :
    Polynomial.eval t (gchCLine H a e) =
      MvPolynomial.aeval (R := ℝ) (fun i : Fin m => a i + t * e i) H := by
  classical
  unfold gchCLine
  let f : Fin m → Polynomial ℂ := fun i => Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X
  let φ : Polynomial ℂ →ₐ[ℝ] ℂ := (Polynomial.aeval (R := ℂ) t).restrictScalars ℝ
  have h := MvPolynomial.comp_aeval_apply (f := f) (φ := φ) (p := H)
  change φ (MvPolynomial.aeval (R := ℝ) f H) =
      MvPolynomial.aeval (R := ℝ) (fun i : Fin m => a i + t * e i) H
  have hfun : (fun i : Fin m => φ (f i)) = (fun i : Fin m => a i + t * e i) := by
    funext i
    change Polynomial.aeval (R := ℂ) t
      ((Polynomial.C (a i)) + (Polynomial.C (e i)) * Polynomial.X) = a i + t * e i
    rw [Polynomial.aeval_add, Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X]
    simp [mul_comm]
  rw [h, hfun]

/-- Evaluating the complexified real line polynomial at `z` equals evaluating `H` at the
complex point `a + z•e`. -/
lemma gch_realLine_map_eval {m : ℕ} (H : MvPolynomial (Fin m) ℝ) (a e : Fin m → ℝ) (z : ℂ) :
    Polynomial.eval z (Polynomial.map (algebraMap ℝ ℂ) (gchRealLine H a e)) =
      MvPolynomial.aeval (R := ℝ) (fun i : Fin m => (a i : ℂ) + z * (e i : ℂ)) H := by
  classical
  rw [gch_eval_map_eq_aeval]
  -- now: aeval z (gchRealLine H a e) with z : ℂ viewed as ℝ-algebra target
  unfold gchRealLine
  let f : Fin m → Polynomial ℝ := fun i => Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X
  let φ : Polynomial ℝ →ₐ[ℝ] ℂ := Polynomial.aeval (R := ℝ) z
  have h := MvPolynomial.comp_aeval_apply (f := f) (φ := φ) (p := H)
  change φ (MvPolynomial.aeval (R := ℝ) f H) =
      MvPolynomial.aeval (R := ℝ) (fun i : Fin m => (a i : ℂ) + z * (e i : ℂ)) H
  have hfun : (fun i : Fin m => φ (f i)) = (fun i : Fin m => (a i : ℂ) + z * (e i : ℂ)) := by
    funext i
    change Polynomial.aeval (R := ℝ) z
      ((Polynomial.C (a i)) + (Polynomial.C (e i)) * Polynomial.X) = (a i : ℂ) + z * (e i : ℂ)
    calc
      Polynomial.aeval (R := ℝ) z (Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X)
          = Polynomial.aeval (R := ℝ) z (Polynomial.C (a i)) +
            Polynomial.aeval (R := ℝ) z (Polynomial.C (e i) * Polynomial.X) := by
              rw [Polynomial.aeval_add]
      _ = (a i : ℂ) + Polynomial.aeval (R := ℝ) z (Polynomial.C (e i) * Polynomial.X) := by
              simp
      _ = (a i : ℂ) + (e i : ℂ) * z := by
              rw [Polynomial.aeval_mul, Polynomial.aeval_C, Polynomial.aeval_X]
              simp
      _ = (a i : ℂ) + z * (e i : ℂ) := by
              simp [mul_comm, mul_left_comm, add_comm, add_left_comm]
  rw [h, hfun]

/-- Evaluating the complexified real line polynomial at a real `s` equals the real
evaluation `H (a + s•e)`. -/
lemma gch_realLine_map_eval_real {m : ℕ} (H : MvPolynomial (Fin m) ℝ) (a e : Fin m → ℝ) (s : ℝ) :
    Polynomial.eval (s : ℂ) (Polynomial.map (algebraMap ℝ ℂ) (gchRealLine H a e)) =
      (MvPolynomial.eval (fun i : Fin m => a i + s * e i) H : ℂ) := by
  rw [gch_realLine_map_eval]
  have hreal : (fun i : Fin m => (a i : ℂ) + (s : ℂ) * (e i : ℂ)) =
      fun i : Fin m => (((a i + s * e i : ℝ) : ℂ)) := by
    funext i
    simp [Complex.ofReal_add, Complex.ofReal_mul, mul_comm, add_comm, add_left_comm, mul_left_comm,
      mul_assoc]
  rw [hreal]
  exact MvPolynomial.aeval_algebraMap_apply (B := ℂ) (x := fun i : Fin m => a i + s * e i) (p := H)

/-- Evaluating `H` at a real vector, complexified, equals casting the real evaluation. -/
lemma gch_aeval_ofReal {m : ℕ} (H : MvPolynomial (Fin m) ℝ) (v : Fin m → ℝ) :
    MvPolynomial.aeval (R := ℝ) (fun i : Fin m => (v i : ℂ)) H = (MvPolynomial.eval v H : ℂ) := by
  change MvPolynomial.aeval (R := ℝ) (Complex.ofReal ∘ v) H = _
  exact MvPolynomial.aeval_algebraMap_apply (B := ℂ) (x := v) (p := H)

/-- Real-coefficient conjugation of evaluations. -/
lemma gch_aeval_conj (p : Polynomial ℝ) (z : ℂ) :
    Polynomial.aeval (starRingEnd ℂ z) p = starRingEnd ℂ (Polynomial.aeval z p) := by
  simpa using (Polynomial.aeval_conj (p := p) (z := z))

/-- If a real polynomial has no roots in the open upper half-plane, all its complex roots
are real. -/
lemma gch_root_real_of_no_upper (p : Polynomial ℝ)
    (hno : ∀ z : ℂ, 0 < z.im → Polynomial.eval z (Polynomial.map (algebraMap ℝ ℂ) p) ≠ 0) :
    ∀ r : ℂ, Polynomial.eval r (Polynomial.map (algebraMap ℝ ℂ) p) = 0 → ∃ s : ℝ, r = (s : ℂ) := by
  intro r hr
  by_contra hnot
  have hzIm : r.im ≠ 0 := by
    intro him0
    exact hnot ((rrl_exists_ofReal_eq_iff r).mpr him0)
  have hroot_aeval : Polynomial.aeval r p = 0 := by
    simpa [gch_eval_map_eq_aeval] using hr
  by_cases hpos : 0 < r.im
  · exact hno r hpos (by simpa [gch_eval_map_eq_aeval] using hr)
  · have hneg : r.im < 0 := lt_of_not_ge (fun h => hpos (lt_of_le_of_ne h (Ne.symm hzIm)))
    have hconjroot : Polynomial.aeval (starRingEnd ℂ r) p = 0 := by
      rw [gch_aeval_conj, hroot_aeval]
      simp
    have hconjIm : 0 < (starRingEnd ℂ r).im := by
      simpa [Complex.conj_im] using (neg_pos.mpr hneg)
    have hconjEv : Polynomial.eval (starRingEnd ℂ r) (Polynomial.map (algebraMap ℝ ℂ) p) ≠ 0 :=
      hno (starRingEnd ℂ r) hconjIm
    exact hconjEv (by simpa [gch_eval_map_eq_aeval] using hconjroot)

/-- For a homogeneous polynomial, the complex line polynomial has degree at most `d`,
with top coefficient the value at the direction. -/
lemma gch_cLine_natDegree_le {m d : ℕ} (H : MvPolynomial (Fin m) ℝ) (hhom : H.IsHomogeneous d)
    (a e : Fin m → ℂ) : (gchCLine H a e).natDegree ≤ d := by
  change (slicePoly m d a e (⟨H, hhom⟩ : homogeneousSubmodule (Fin m) ℝ d)).natDegree ≤ d
  exact slicePoly_natDegree_le m d a e ⟨H, hhom⟩

/-- Top coefficient of a complex line polynomial of a homogeneous polynomial. -/
lemma gch_cLine_coeff_d {m d : ℕ} (H : MvPolynomial (Fin m) ℝ) (hhom : H.IsHomogeneous d)
    (a e : Fin m → ℂ) : (gchCLine H a e).coeff d = MvPolynomial.aeval (R := ℝ) e H := by
  change (slicePoly m d a e (⟨H, hhom⟩ : homogeneousSubmodule (Fin m) ℝ d)).coeff d =
      MvPolynomial.aeval (R := ℝ) e H
  exact slicePoly_coeff_d m d a e ⟨H, hhom⟩

/-- For a homogeneous polynomial of degree `d`, the complex line polynomial in direction
`e` has degree exactly `d` provided `H(e) ≠ 0`. -/
lemma gch_cLine_natDegree_eq {m d : ℕ} (H : MvPolynomial (Fin m) ℝ) (hhom : H.IsHomogeneous d)
    (a e : Fin m → ℂ) (he : MvPolynomial.aeval (R := ℝ) e H ≠ 0) :
    (gchCLine H a e).natDegree = d := by
  change (slicePoly m d a e (⟨H, hhom⟩ : homogeneousSubmodule (Fin m) ℝ d)).natDegree = d
  exact slicePoly_natDegree_eq_of_aeval_ne_zero m d a e ⟨H, hhom⟩ he

/-- A degree-`d` homogeneous polynomial with `0 < d` and `H(e) ≠ 0` restricts to a nonzero
complex line polynomial in direction `e`. -/
lemma gch_cLine_ne_zero {m d : ℕ} (H : MvPolynomial (Fin m) ℝ) (hhom : H.IsHomogeneous d)
    (a e : Fin m → ℂ) (hdpos : 0 < d) (he : MvPolynomial.aeval (R := ℝ) e H ≠ 0) :
    gchCLine H a e ≠ 0 := by
  intro hz
  have hnd : (gchCLine H a e).natDegree = d := gch_cLine_natDegree_eq H hhom a e he
  have hnd0 : (gchCLine H a e).natDegree = 0 := by simp [hz]
  linarith

/-- A polynomial which is homogeneous of degree zero is constant. -/
lemma gch_isHom_zero_eq_C {m : ℕ} (H : MvPolynomial (Fin m) ℝ) (hhom : H.IsHomogeneous 0) :
    H = MvPolynomial.C (MvPolynomial.coeff 0 H) := by
  classical
  apply MvPolynomial.ext
  intro M
  by_cases hM : M = 0
  · subst M
    simp [MvPolynomial.coeff_C]
  · have hdeg : M.degree ≠ 0 := by
      intro hd0
      exact hM (((Finsupp.degree_eq_zero_iff (R := ℕ) M).mp) hd0)
    have hc : MvPolynomial.coeff M H = 0 := IsHomogeneous.coeff_eq_zero hhom (d := M) hdeg
    rw [hc]
    rw [MvPolynomial.coeff_C]
    rw [if_neg (show ¬ 0 = M from fun hz => hM hz.symm)]

/-- If all complex roots of the (complexified) `u`-line in direction `e` are real and
`H (u + s•e) ≠ 0` for all `s ≥ 0`, then all those roots are negative. -/
lemma gch_roots_negative_of_no_nonneg_real_root {m : ℕ} (H : MvPolynomial (Fin m) ℝ)
    (e u : Fin m → ℝ)
    (hrealrooted : ∀ r : ℂ,
      Polynomial.eval r (Polynomial.map (algebraMap ℝ ℂ) (gchRealLine H u e)) = 0 → r.im = 0)
    (hu : ∀ s : ℝ, 0 ≤ s → MvPolynomial.eval (fun i : Fin m => u i + s * e i) H ≠ 0) :
    ∀ r : ℂ, Polynomial.eval r (Polynomial.map (algebraMap ℝ ℂ) (gchRealLine H u e)) = 0 →
      r.im = 0 ∧ r.re < 0 := by
  classical
  intro r hr
  have him0 : r.im = 0 := hrealrooted r hr
  refine ⟨him0, ?_⟩
  by_contra hnot
  have hge : 0 ≤ r.re := le_of_not_gt hnot
  have hrre : r = (r.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using him0
  have hr' : Polynomial.eval (r.re : ℂ) (Polynomial.map (algebraMap ℝ ℂ) (gchRealLine H u e)) = 0 := by
    rwa [hrre] at hr
  have hr'' : Polynomial.eval (r.re : ℂ) (Polynomial.map (algebraMap ℝ ℂ) (gchRealLine H u e)) =
      (MvPolynomial.eval (fun i : Fin m => u i + r.re * e i) H : ℂ) :=
    gch_realLine_map_eval_real H u e (r.re)
  have hval : (MvPolynomial.eval (fun i : Fin m => u i + r.re * e i) H : ℂ) = 0 := by
    rw [← hr'']
    exact hr'
  have hz : MvPolynomial.eval (fun i : Fin m => u i + r.re * e i) H = 0 := by
    exact_mod_cast hval
  exact hu (r.re) hge hz



/-- Coefficients of the affine `z`-dependent line polynomials depend continuously on `z`.
(Companion helper; the coefficients of a linear factor are continuous.) -/
lemma gch_lincoef_cont {m : ℕ} (a b w : Fin m → ℂ) (i : Fin m) (u : ℕ) :
    Continuous (fun z : ℂ =>
      (Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X).coeff u) := by
  classical
  by_cases hu0 : u = 0
  · subst hu0
    have heq : (fun z : ℂ =>
          (Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X).coeff 0) =
        fun z : ℂ => a i + z * b i := by
      funext z
      simp
    rw [heq]
    exact continuous_const.add (continuous_id.mul continuous_const)
  · by_cases hu1 : u = 1
    · subst hu1
      have heq : (fun z : ℂ =>
            (Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X).coeff 1) =
          fun _ : ℂ => w i := by
        funext z
        simp
      rw [heq]
      exact continuous_const
    · have hge2 : 2 ≤ u := by omega
      have heq : (fun z : ℂ =>
            (Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X).coeff u) =
          fun _ : ℂ => 0 := by
        funext z
        have hnd : (Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X).natDegree ≤ 1 := by
          rw [add_comm]
          exact Polynomial.natDegree_linear_le
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hnd (by omega))
      rw [heq]
      exact continuous_const

/-- Coefficient continuity of sections. -/
lemma gch_coeffContinuous_local (m : ℕ) (H : MvPolynomial (Fin m) ℝ)
    (a b w : Fin m → ℂ) :
    ∀ j : ℕ, Continuous (fun z : ℂ =>
      (MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X) H).coeff j) := by
  classical
  induction H using MvPolynomial.induction_on with
  | C c =>
      intro j
      have hcst : (fun z : ℂ =>
          (MvPolynomial.aeval (R := ℝ)
            (fun i : Fin m => Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X)
            (MvPolynomial.C c)).coeff j) = fun _ : ℂ => (Polynomial.C (c : ℂ)).coeff j := by
        funext z
        rw [MvPolynomial.aeval_C]
        simp
      rw [hcst]
      exact continuous_const
  | add p q hfp hfq =>
      intro j
      have heq : (fun z : ℂ =>
          (MvPolynomial.aeval (R := ℝ)
            (fun i : Fin m => Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X)
            (p + q)).coeff j) =
          (fun z : ℂ =>
            (MvPolynomial.aeval (R := ℝ)
              (fun i : Fin m => Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X) p).coeff j
            + (MvPolynomial.aeval (R := ℝ)
              (fun i : Fin m => Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X) q).coeff j) := by
        funext z
        rw [map_add (MvPolynomial.aeval (R := ℝ)
          (fun i : Fin m => Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X)) p q]
        rw [Polynomial.coeff_add]
      rw [heq]
      exact (hfp j).add (hfq j)
  | mul_X p i hfp =>
      intro j
      have heq : (fun z : ℂ =>
          (MvPolynomial.aeval (R := ℝ)
            (fun i0 : Fin m => Polynomial.C (a i0 + z * b i0) + Polynomial.C (w i0) * Polynomial.X)
            (p * MvPolynomial.X i)).coeff j) =
          (fun z : ℂ => ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal j : Finset (ℕ × ℕ)),
            (MvPolynomial.aeval (R := ℝ)
              (fun i0 : Fin m => Polynomial.C (a i0 + z * b i0) + Polynomial.C (w i0) * Polynomial.X) p).coeff x.1
              * (Polynomial.C (a i + z * b i) + Polynomial.C (w i) * Polynomial.X).coeff x.2) := by
        funext z
        rw [map_mul (MvPolynomial.aeval (R := ℝ)
          (fun i0 : Fin m => Polynomial.C (a i0 + z * b i0) + Polynomial.C (w i0) * Polynomial.X))
          p (MvPolynomial.X i)]
        rw [MvPolynomial.aeval_X]
        rw [Polynomial.coeff_mul]
      rw [heq]
      apply continuous_finsetSum (s := (Finset.HasAntidiagonal.antidiagonal j : Finset (ℕ × ℕ)))
      intro x hx
      exact (hfp x.1).mul (gch_lincoef_cont a b w i x.2)

/-- A nonzero complex polynomial with a root in the upper half-plane has a small radius
around that root containing no other roots (and staying in the upper half-plane). -/
lemma gch_exists_isolated_root_radius (q : Polynomial ℂ) (hq : q ≠ 0) (r : ℂ) (him : 0 < r.im)
    (hroot : q.eval r = 0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ < r.im ∧
      ∀ w : ℂ, w ∈ Metric.closedBall r ρ → w ≠ r → q.eval w ≠ 0 := by
  classical
  have hSfin : ({z : ℂ | q.eval z = 0} : Set ℂ).Finite := by
    simpa [Polynomial.IsRoot] using q.finite_setOfPred_isRoot hq
  let S : Finset ℂ := hSfin.toFinset
  have hS_mem : ∀ w : ℂ, w ∈ S ↔ q.eval w = 0 := by
    intro w
    simpa [S, Set.Finite.mem_toFinset]
  let T : Finset ℂ := S.erase r
  have hT_mem : ∀ w : ℂ, w ∈ T ↔ q.eval w = 0 ∧ w ≠ r := by
    intro w
    rw [Finset.mem_erase]
    simp [hS_mem w]
    tauto
  by_cases hT : T = ∅
  · refine ⟨r.im / 2, by positivity, by linarith, ?_⟩
    intro w hw hwr hwz
    have hwT : w ∈ T := (hT_mem w).mpr ⟨hwz, hwr⟩
    simpa [hT] using hwT
  · have hTne : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
    let dists : Finset ℝ := T.image (fun w : ℂ => ‖w - r‖)
    have hdists_ne : dists.Nonempty := by
      rcases hTne with ⟨w, hw⟩
      refine ⟨‖w - r‖, ?_⟩
      exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
    have hdists_pos : ∀ x ∈ dists, 0 < x := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨w, hw, rfl⟩
      have hwr : w ≠ r := (hT_mem w).mp hw |>.2
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hwr)
    let m : ℝ := dists.min' hdists_ne
    have hm_pos : 0 < m := by
      have hm_mem : m ∈ dists := Finset.min'_mem dists hdists_ne
      exact hdists_pos m hm_mem
    have hm_le : ∀ x ∈ dists, m ≤ x := by
      intro x hx
      change dists.min' hdists_ne ≤ x
      exact Finset.min'_le dists x hx
    let ρ : ℝ := min (r.im / 2) (m / 2)
    refine ⟨ρ, ?_, ?_, ?_⟩
    · dsimp [ρ]
      positivity
    · dsimp [ρ]
      have h1 : r.im / 2 < r.im := by linarith
      exact lt_of_le_of_lt (min_le_left _ _) h1
    · intro w hw hwr hwz
      have hwT : w ∈ T := (hT_mem w).mpr ⟨hwz, hwr⟩
      have hmemdist : ‖w - r‖ ∈ dists := Finset.mem_image.mpr ⟨w, hwT, rfl⟩
      have hmle : m ≤ ‖w - r‖ := by
        simpa using hm_le ‖w - r‖ hmemdist
      have hwball : ‖w - r‖ ≤ ρ := by
        simpa [dist_eq_norm] using (Metric.mem_closedBall.mp hw)
      have hρlt : ρ < m := by
        dsimp [ρ]
        have h2 : m / 2 < m := by linarith
        exact lt_of_le_of_lt (min_le_right _ _) h2
      linarith

/-- A degree-`d` complex polynomial equals the sum of its first `d+1` monomials. -/
lemma gch_poly_eq_sum_coeff (p : Polynomial ℂ) (d : ℕ) (hnd : p.natDegree ≤ d) :
    p = Finset.sum Finset.univ (fun i : Fin (d + 1) => Polynomial.monomial (i : ℕ) (p.coeff i)) := by
  classical
  apply Polynomial.ext
  intro j
  rw [rrl_coeff_sum_monomial (R := ℂ) (a := fun i : Fin (d + 1) => p.coeff i) j]
  by_cases hj : j < d + 1
  · simp [hj]
  · have hgt : d < j := by omega
    have hc0 : p.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hnd hgt)
    rw [dif_neg hj]
    exact hc0



/-- Gårding: hyperbolicity with respect to `e`, together with cone membership of `u`,
imply that the restriction of `H` to any real line in direction `u` avoids the open upper
half-plane. -/
lemma gch_uLine_no_upper {m d : ℕ} (H : MvPolynomial (Fin m) ℝ) (e u : Fin m → ℝ)
    (hhom : H.IsHomogeneous d) (hdpos : 0 < d)
    (he_ne : MvPolynomial.eval e H ≠ 0)
    (hu0 : MvPolynomial.eval u H ≠ 0)
    (hcone : ∀ r : ℂ,
      Polynomial.eval r (Polynomial.map (algebraMap ℝ ℂ) (gchRealLine H u e)) = 0 →
        r.im = 0 ∧ r.re < 0)
    (hhyp : ∀ a : Fin m → ℝ,
      MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X) H = 0 ∨
        ∀ r : Complex, Polynomial.eval r (Polynomial.map (algebraMap ℝ Complex)
          (MvPolynomial.aeval (R := ℝ)
            (fun i : Fin m => Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X) H)) = 0 →
          ∃ s : ℝ, r = (s : Complex)) :
    ∀ x : Fin m → ℝ, ∀ z : ℂ, 0 < z.im →
      Polynomial.eval z (Polynomial.map (algebraMap ℝ ℂ) (gchRealLine H x u)) ≠ 0 := by
  classical
  -- cone membership in the cLine form needed by the bivariate lemma
  have hcone_c : ∀ r : ℂ,
      Polynomial.eval r (MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => Polynomial.C ((u i : ℂ)) + Polynomial.C ((e i : ℂ)) * Polynomial.X) H) = 0 →
        r.im = 0 ∧ r.re < 0 := by
    intro r hr
    exact hcone r (by
      have hraw : Polynomial.eval r (MvPolynomial.aeval (R := ℝ)
          (fun i : Fin m => Polynomial.C ((u i : ℂ)) + Polynomial.C ((e i : ℂ)) * Polynomial.X) H) =
          Polynomial.eval r (Polynomial.map (algebraMap ℝ ℂ) (gchRealLine H u e)) := by
        change Polynomial.eval r (gchCLine H (fun i : Fin m => (u i : ℂ))
            (fun i : Fin m => (e i : ℂ))) =
          Polynomial.eval r (Polynomial.map (algebraMap ℝ ℂ) (gchRealLine H u e))
        rw [gch_cLine_eval, gch_realLine_map_eval]
      rwa [hraw] at hr)
  have hbiv := gch_bivariate H e u hhom hdpos he_ne hu0 hcone_c hhyp
  intro x z hzIm
  by_contra hzroot
  have hz : Polynomial.eval z (Polynomial.map (algebraMap ℝ ℂ) (gchRealLine H x u)) = 0 := by
    exact hzroot
  let q : Polynomial ℂ := gchCLine H (fun i : Fin m => (x i : ℂ)) (fun i : Fin m => (u i : ℂ))
  have hzq : q.eval z = 0 := by
    have hev := gch_realLine_map_eval H x u z
    change (gchCLine H (fun i : Fin m => (x i : ℂ)) (fun i : Fin m => (u i : ℂ))).eval z = 0
    rw [gch_cLine_eval]
    rw [← hev]
    exact hz
  have q_ne0 : q ≠ 0 := by
    apply gch_cLine_ne_zero H hhom (fun i : Fin m => (x i : ℂ)) (fun i : Fin m => (u i : ℂ)) hdpos
    rw [gch_aeval_ofReal]
    exact_mod_cast hu0
  rcases gch_exists_isolated_root_radius q q_ne0 z hzIm hzq with ⟨ρ, hρpos, hρlt, hiso⟩
  let zfun : ℕ → ℂ := fun k : ℕ => Complex.I * ((1 / (((k : ℕ) : ℝ) + 1) : ℝ) : ℂ)
  have hzfun : Filter.Tendsto zfun Filter.atTop (nhds 0) := by
    have hr : Filter.Tendsto (fun k : ℕ => (1 / (((k : ℕ) : ℝ) + 1) : ℝ)) Filter.atTop
        (nhds (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hcast : Filter.Tendsto (fun k : ℕ => ((1 / (((k : ℕ) : ℝ) + 1) : ℝ) : ℂ))
        Filter.atTop (nhds (0 : ℂ)) := (Complex.continuous_ofReal.tendsto 0).comp hr
    have hmul := Filter.Tendsto.mul (tendsto_const_nhds (x := (Complex.I : ℂ))) hcast
    simpa [zfun] using hmul
  let c : ℕ → Fin (d + 1) → ℂ := fun k i =>
    (gchCLine H (fun i0 : Fin m => (x i0 : ℂ) + zfun k * (e i0 : ℂ))
      (fun i0 : Fin m => (u i0 : ℂ))).coeff (i : ℕ)
  let cf : Fin (d + 1) → ℂ := fun i => q.coeff (i : ℕ)
  have hlim : ∀ i : Fin (d + 1),
      Filter.Tendsto (fun k : ℕ => c k i) Filter.atTop (nhds (cf i)) := by
    intro i
    have hc : Continuous (fun z : ℂ => (gchCLine H (fun i0 : Fin m => (x i0 : ℂ) + z * (e i0 : ℂ))
        (fun i0 : Fin m => (u i0 : ℂ))).coeff (i : ℕ)) := by
      -- via gch_coeffContinuous_local
      simpa [gchCLine] using
        (gch_coeffContinuous_local m H (fun i0 : Fin m => (x i0 : ℂ))
          (fun i0 : Fin m => (e i0 : ℂ)) (fun i0 : Fin m => (u i0 : ℂ)) (i : ℕ))
    have ht0 : Filter.Tendsto (fun k : ℕ => c k i) Filter.atTop
        (nhds ((fun z : ℂ => (gchCLine H (fun i0 : Fin m => (x i0 : ℂ) + z * (e i0 : ℂ))
          (fun i0 : Fin m => (u i0 : ℂ))).coeff (i : ℕ)) 0)) := by
      dsimp [c]
      exact hc.continuousAt.tendsto.comp hzfun
    -- value at 0 is cf i
    simpa [cf, q] using ht0
  have hqnd : q.natDegree ≤ d := by
    dsimp [q]
    exact gch_cLine_natDegree_le H hhom (fun i : Fin m => (x i : ℂ)) (fun i : Fin m => (u i : ℂ))
  have hqeq : q = Finset.sum Finset.univ (fun i : Fin (d + 1) => Polynomial.monomial (i : ℕ) (q.coeff i)) :=
    gch_poly_eq_sum_coeff q d hqnd
  have hroot' : Polynomial.eval z (Finset.sum Finset.univ (fun i : Fin (d + 1) => Polynomial.monomial (i : ℕ) (cf i))) = 0 := by
    dsimp [cf]
    rwa [← hqeq]
  have hpunct' : ∀ w : ℂ, w ∈ Metric.closedBall z ρ → w ≠ z →
      Polynomial.eval w (Finset.sum Finset.univ (fun i : Fin (d + 1) => Polynomial.monomial (i : ℕ) (cf i))) ≠ 0 := by
    intro w hw hwz
    have hwne := hiso w hw hwz
    dsimp [cf]
    rwa [← hqeq]
  rcases gch_complexHurwitz d c cf hlim z hρpos hroot' hpunct' with ⟨N, hN⟩
  -- pick k := N
  rcases hN N (le_rfl) with ⟨w, hwd, hwroot⟩
  have hSnd : (gchCLine H (fun i0 : Fin m => (x i0 : ℂ) + zfun N * (e i0 : ℂ))
      (fun i0 : Fin m => (u i0 : ℂ))).natDegree ≤ d := by
    exact gch_cLine_natDegree_le H hhom (fun i0 : Fin m => (x i0 : ℂ) + zfun N * (e i0 : ℂ))
      (fun i0 : Fin m => (u i0 : ℂ))
  have hSeq : gchCLine H (fun i0 : Fin m => (x i0 : ℂ) + zfun N * (e i0 : ℂ))
      (fun i0 : Fin m => (u i0 : ℂ)) =
      Finset.sum Finset.univ (fun i : Fin (d + 1) => Polynomial.monomial (i : ℕ) (c N i)) := by
    dsimp [c]
    exact gch_poly_eq_sum_coeff (gchCLine H (fun i0 : Fin m => (x i0 : ℂ) + zfun N * (e i0 : ℂ))
      (fun i0 : Fin m => (u i0 : ℂ))) d hSnd
  have hwq : Polynomial.eval w (gchCLine H (fun i0 : Fin m => (x i0 : ℂ) + zfun N * (e i0 : ℂ))
      (fun i0 : Fin m => (u i0 : ℂ))) = 0 := by
    rwa [hSeq]
  have hzIm_pos : 0 < (zfun N).im := by
    let sN : ℝ := 1 / (((N : ℕ) : ℝ) + 1)
    have hgen : ∀ s : ℝ, (Complex.I * (s : ℂ)).im = s := by
      intro s
      simp [Complex.I_mul]
    have hmain : (zfun N).im = sN := by
      dsimp [zfun, sN]
      exact hgen (1 / (((N : ℕ) : ℝ) + 1))
    rw [hmain]
    dsimp [sN]
    positivity
  have hwIm_pos : 0 < w.im := by
    have hb : |(w - z).im| ≤ ‖w - z‖ := Complex.abs_im_le_norm (w - z)
    have hdistlt : ‖w - z‖ < ρ := by
      simpa [dist_eq_norm] using hwd
    have hzsub : |(w - z).im| < ρ := lt_of_le_of_lt hb hdistlt
    have hneg : -ρ < (w - z).im := by
      have h := abs_lt.mp hzsub
      exact h.1
    have hwz : w.im = z.im + (w - z).im := by simp
    rw [hwz]
    have hzρ : 0 < z.im - ρ := by linarith
    have hlt : z.im - ρ < z.im + (w - z).im := by linarith
    linarith
  have hbiv_val : MvPolynomial.aeval (R := ℝ)
      (fun i : Fin m => (x i : ℂ) + zfun N * (e i : ℂ) + w * (u i : ℂ)) H ≠ 0 :=
    hbiv x (zfun N) hzIm_pos w hwIm_pos
  -- but hwq says it equals 0 via gch_cLine_eval
  have hzeroval : MvPolynomial.aeval (R := ℝ)
      (fun i : Fin m => (x i : ℂ) + zfun N * (e i : ℂ) + w * (u i : ℂ)) H = 0 := by
    have := gch_cLine_eval H (fun i0 : Fin m => (x i0 : ℂ) + zfun N * (e i0 : ℂ))
      (fun i0 : Fin m => (u i0 : ℂ)) w
    -- this : eval w (cLine ...) = aeval (fun i => (x i:ℂ) + zfun N*(e i:ℂ) + w*(u i:ℂ)) H
    rwa [← this]
  exact hbiv_val hzeroval

/-- The main theorem: hyperbolic w.r.t. `u`, in the problem's weak form. -/
theorem garding_cone_hyperbolic {m d : ℕ} (H : MvPolynomial (Fin m) ℝ) (e u : Fin m → ℝ)
    (hhom : H.IsHomogeneous d) (hH0 : H ≠ 0)
    (he_ne : MvPolynomial.eval e H ≠ 0)
    (hhyp : ∀ a : Fin m → ℝ,
      MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X) H = 0 ∨
        ∀ r : Complex, Polynomial.eval r (Polynomial.map (algebraMap ℝ Complex)
          (MvPolynomial.aeval (R := ℝ)
            (fun i : Fin m => Polynomial.C (a i) + Polynomial.C (e i) * Polynomial.X) H)) = 0 →
          ∃ s : ℝ, r = (s : Complex))
    (hu : ∀ s : ℝ, 0 ≤ s → MvPolynomial.eval (fun i : Fin m => u i + s * e i) H ≠ 0) :
    ∀ x : Fin m → ℝ,
      MvPolynomial.aeval (R := ℝ)
        (fun i : Fin m => Polynomial.C (x i) + Polynomial.C (u i) * Polynomial.X) H = 0 ∨
        ∀ r : Complex, Polynomial.eval r (Polynomial.map (algebraMap ℝ Complex)
          (MvPolynomial.aeval (R := ℝ)
            (fun i : Fin m => Polynomial.C (x i) + Polynomial.C (u i) * Polynomial.X) H)) = 0 →
          ∃ s : ℝ, r = (s : Complex) := by
  classical
  by_cases hd : d = 0
  · subst hd
    -- constant case
    have hc : H = MvPolynomial.C (MvPolynomial.coeff (0 : Fin m →₀ ℕ) H) :=
      gch_isHom_zero_eq_C H hhom
    have hc0 : MvPolynomial.coeff (0 : Fin m →₀ ℕ) H ≠ 0 := by
      intro hz
      apply hH0
      rw [hc, hz]
      simp
    intro x
    right
    intro r hr
    have hline : gchRealLine H x u = Polynomial.C (MvPolynomial.coeff (0 : Fin m →₀ ℕ) H) := by
      unfold gchRealLine
      rw [hc]
      simp
    have hval : Polynomial.eval r (Polynomial.map (algebraMap ℝ ℂ) (gchRealLine H x u)) ≠ 0 := by
      rw [hline]
      simp
      exact_mod_cast hc0
    exact False.elim (hval hr)
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
    -- hu at zero gives eval u H ≠ 0
    have hu0 : MvPolynomial.eval u H ≠ 0 := by
      have hu0' : MvPolynomial.eval (fun i : Fin m => u i + 0 * e i) H ≠ 0 := hu 0 (le_rfl)
      simpa using hu0' 
    -- real-rootedness of the e-line through u (discard the zero case)
    have hline_ne : gchRealLine H u e ≠ 0 := by
      intro hz
      have hzval : Polynomial.eval 0 (Polynomial.map (algebraMap ℝ ℂ) (gchRealLine H u e)) = 0 := by
        simp [hz]
      have hval_ne : Polynomial.eval 0 (Polynomial.map (algebraMap ℝ ℂ) (gchRealLine H u e)) ≠ 0 := by
        have hu0c : (MvPolynomial.eval u H : ℂ) ≠ 0 := by exact_mod_cast hu0
        have hev := gch_realLine_map_eval H u e (0 : ℂ)
        have harg : (fun i : Fin m => (u i : ℂ) + 0 * (e i : ℂ)) = fun i : Fin m => (u i : ℂ) := by
          funext i
          simp
        rw [hev, harg, gch_aeval_ofReal]
        exact hu0c
      exact hval_ne hzval
    rcases hhyp u with hz0 | hrr
    · exact False.elim (hline_ne hz0)
    · have hrealroot : ∀ r : ℂ,
        Polynomial.eval r (Polynomial.map (algebraMap ℝ ℂ) (gchRealLine H u e)) = 0 → r.im = 0 := by
        intro r hr
        exact (rrl_exists_ofReal_eq_iff r).mp (hrr r hr)
      have hcone : ∀ r : ℂ,
          Polynomial.eval r (Polynomial.map (algebraMap ℝ ℂ) (gchRealLine H u e)) = 0 →
            r.im = 0 ∧ r.re < 0 :=
        gch_roots_negative_of_no_nonneg_real_root H e u hrealroot hu
      have hnoUpper := gch_uLine_no_upper H e u hhom hdpos he_ne hu0 hcone hhyp
      intro x
      right
      -- real-rootedness of the u-line through x
      apply gch_root_real_of_no_upper (gchRealLine H x u)
      intro z hzIm
      exact hnoUpper x z hzIm

end Commons.Analysis.MvPolynomial
