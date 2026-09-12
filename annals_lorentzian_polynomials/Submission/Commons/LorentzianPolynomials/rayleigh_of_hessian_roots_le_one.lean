import Mathlib.Data.Int.Star
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Topology.Algebra.MvPolynomial
import Submission.Commons.LinearAlgebra.Matrix.quadratic_stable_iff_roots_card_le_one
import Submission.Commons.LinearAlgebra.Matrix.sigPos_toQuadraticForm_eq_card_pos_roots
import Submission.Commons.LinearAlgebra.Matrix.perron_vector_of_nonneg_symm_card_pos_le_one_pos

open Matrix Polynomial Set
open MvPolynomial Finsupp
open Commons.LinearAlgebra.Matrix
open Filter Topology Set
open scoped BigOperators Topology

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Commons.LorentzianPolynomials

noncomputable section

namespace rayleigh_pre

-- ############################################################################
-- 1. Quadratic-form machinery for symmetric matrices (reverse Cauchy-Schwarz)
-- ############################################################################

lemma quadReal_smul_right {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x y : Fin n → ℝ) :
    quadReal A x (c • y) = c * quadReal A x y := by
  rw [quadReal_mulVec A x (c • y), quadReal_mulVec A x y]
  rw [Matrix.mulVec_smul]
  rw [dotProduct_smul]
  simp [smul_eq_mul]

lemma quadReal_smul_left {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (x y : Fin n → ℝ) :
    quadReal A (c • x) y = c * quadReal A x y := by
  rw [quadReal_mulVec A (c • x) y, quadReal_mulVec A x y]
  rw [smul_dotProduct]
  simp [smul_eq_mul]

lemma quadReal_mixed {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (a b : ℝ) (x y : Fin n → ℝ) :
    quadReal A (a • x) (b • y) = (a * b) * quadReal A x y := by
  rw [quadReal_smul_left, quadReal_smul_right]
  ring

lemma quadReal_bilin {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (u v : Fin n → ℝ) (a b c d : ℝ) :
    quadReal A (a • u + b • v) (c • u + d • v) =
      a * c * quadReal A u u + a * d * quadReal A u v +
        b * c * quadReal A v u + b * d * quadReal A v v := by
  rw [quadReal_add_left A (a • u) (b • v) (c • u + d • v)]
  rw [quadReal_add_right A (a • u) (c • u) (d • v)]
  rw [quadReal_add_right A (b • v) (c • u) (d • v)]
  rw [quadReal_mixed A a c u u]
  rw [quadReal_mixed A a d u v]
  rw [quadReal_mixed A b c v u]
  rw [quadReal_mixed A b d v v]
  ring

lemma quadReal_expand {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (x z : Fin n → ℝ) (a b : ℝ) :
    quadReal A (a • x + b • z) (a • x + b • z) =
      a ^ 2 * quadReal A x x + 2 * a * b * quadReal A x z + b ^ 2 * quadReal A z z := by
  rw [quadReal_bilin A x z a b a b]
  rw [quadReal_symm A hA x z]
  ring

lemma quadReal_toQuadraticForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    A.toQuadraticForm' x = quadReal A x x := by
  rw [quadReal_mulVec]
  simp [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply']

/-- vectors x,z with Q x x > 0, Q z z > 0, Q x z = 0 are linearly independent over ℝ -/
lemma linInd_orth_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (x z : Fin n → ℝ) (hxx : 0 < quadReal A x x) (hzz : 0 < quadReal A z z)
    (hxz : quadReal A x z = 0) : LinearIndependent ℝ (fun i : Fin 2 => if i = 0 then x else z) := by
  rw [linearIndependent_fin2]
  constructor
  · intro hz0
    have hz0' : z = 0 := by simpa using hz0
    have hzz0 : quadReal A z z = 0 := by
      rw [hz0']
      unfold quadReal
      simp
    linarith
  · intro a ha
    have hx_eq : x = a • z := ha.symm
    have hxzx : quadReal A x x = quadReal A x (a • z) := by rw [hx_eq]
    have hright : quadReal A x (a • z) = a * quadReal A x z := quadReal_smul_right A a x z
    rw [hxzx, hright, hxz, mul_zero] at hxx
    linarith

lemma posDef_restrict_span_of_orth_pos {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (x z : Fin n → ℝ) (hxx : 0 < quadReal A x x) (hzz : 0 < quadReal A z z)
    (hxz : quadReal A x z = 0) :
    (QuadraticMap.restrict A.toQuadraticForm' (Submodule.span ℝ ({x, z} : Set (Fin n → ℝ)))).PosDef := by
  classical
  intro v hv
  have hvmem : (v : Fin n → ℝ) ∈ Submodule.span ℝ ({x, z} : Set (Fin n → ℝ)) := v.property
  obtain ⟨a, b, hab⟩ := (Submodule.mem_span_pair (x := x) (y := z) (z := (v : Fin n → ℝ))).mp hvmem
  have hne : a ≠ 0 ∨ b ≠ 0 := by
    by_contra h
    have ha0 : a = 0 := by tauto
    have hb0 : b = 0 := by tauto
    have hv0 : (v : Fin n → ℝ) = 0 := by
      rw [← hab]
      simp [ha0, hb0]
    exact hv (Subtype.ext hv0)
  have hcalc : A.toQuadraticForm' (v : Fin n → ℝ) =
      a ^ 2 * quadReal A x x + b ^ 2 * quadReal A z z := by
    rw [← hab]
    rw [quadReal_toQuadraticForm]
    rw [quadReal_expand A hA x z a b]
    rw [hxz]
    ring
  have hval : A.toQuadraticForm' (v : Fin n → ℝ) = QuadraticMap.restrict A.toQuadraticForm'
      (Submodule.span ℝ ({x, z} : Set (Fin n → ℝ))) v := by rfl
  rw [← hval, hcalc]
  rcases hne with ha | hb
  · have ha2 : 0 < a ^ 2 := sq_pos_of_ne_zero ha
    nlinarith [mul_pos ha2 hxx, mul_nonneg (sq_nonneg b) hzz.le]
  · have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
    nlinarith [mul_pos hb2 hzz, mul_nonneg (sq_nonneg a) hxx.le]

lemma orth_comp_le_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (hcard : (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1)
    (x z : Fin n → ℝ) (hxx : 0 < quadReal A x x) (hxz : quadReal A x z = 0) :
    quadReal A z z ≤ 0 := by
  classical
  by_contra hz
  have hzz : 0 < quadReal A z z := lt_of_not_ge hz
  let Q : QuadraticForm ℝ (Fin n → ℝ) := A.toQuadraticForm'
  haveI : Module.Finite ℝ (Fin n → ℝ) := Module.Finite.pi
  haveI : StrongRankCondition ℝ := by infer_instance
  have hsig1 : QuadraticForm.sigPos Q ≤ 1 := by
    change QuadraticForm.sigPos A.toQuadraticForm' ≤ 1
    have hsig := (Commons.LinearAlgebra.Matrix.sigPos_toQuadraticForm_eq_card_pos_roots
      (n := n) A hA)
    rw [hsig]
    exact hcard
  let V : Submodule ℝ (Fin n → ℝ) := Submodule.span ℝ ({x, z} : Set (Fin n → ℝ))
  have hVpos : (QuadraticMap.restrict Q V).PosDef := by
    simpa [V, Q] using posDef_restrict_span_of_orth_pos A hA x z hxx hzz hxz
  have hfin : Module.finrank ℝ V ≤ QuadraticForm.sigPos Q := by
    simpa using (le_sigPos_of_posDef Q hVpos)
  have hfin2 : 2 ≤ Module.finrank ℝ V := by
    let b : Fin 2 → Fin n → ℝ := fun i => if i = 0 then x else z
    have hb_lin : LinearIndependent ℝ b := by
      simpa [b] using linInd_orth_pos A hA x z hxx hzz hxz
    have hspan_eq : Submodule.span ℝ (Set.range b) = V := by
      dsimp [V]
      apply le_antisymm
      · exact Submodule.span_mono (by
          intro y hy
          rcases hy with ⟨i, rfl⟩
          fin_cases i <;> simp [b])
      · exact Submodule.span_mono (by
          intro y hy
          rcases hy with rfl | rfl
          · exact ⟨(0 : Fin 2), by simp [b]⟩
          · exact ⟨(1 : Fin 2), by simp [b]⟩)
    have hfr : Module.finrank ℝ (Submodule.span ℝ (Set.range b)) = 2 := by
      rw [finrank_span_eq_card hb_lin]
      simp
    rw [← hspan_eq, hfr]
  linarith

lemma quadReal_sq_ge_self_mul {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.IsSymm)
    (hcard : (A.charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1)
    (x y : Fin n → ℝ) (hxx : 0 < quadReal A x x) :
    (quadReal A x y) ^ 2 ≥ quadReal A x x * quadReal A y y := by
  classical
  let Qxx : ℝ := quadReal A x x
  let Qxy : ℝ := quadReal A x y
  let s : ℝ := Qxy / Qxx
  let e : Fin n → ℝ := fun k => y k - s * x k
  have hQxx_ne : Qxx ≠ 0 := by
    dsimp [Qxx]
    exact ne_of_gt hxx
  have hy_decomp : y = e + s • x := by
    funext k
    dsimp [e, s, Qxy]
    ring
  have hxze : quadReal A x e = 0 := by
    have heq : e = y + (-s) • x := by
      funext k
      dsimp [e, s, Qxy]
      ring
    rw [heq]
    rw [quadReal_add_right A x y ((-s) • x)]
    rw [quadReal_smul_right]
    dsimp [s, Qxy, Qxx]
    field_simp [hQxx_ne]
    ring
  have hze : quadReal A e e ≤ 0 := orth_comp_le_zero A hA hcard x e hxx hxze
  have hQyy : quadReal A y y = quadReal A e e + s ^ 2 * Qxx := by
    rw [hy_decomp]
    rw [show e + s • x = (1 : ℝ) • e + s • x by ext k; simp]
    calc
      quadReal A ((1 : ℝ) • e + s • x) ((1 : ℝ) • e + s • x)
          = (1 : ℝ) ^ 2 * quadReal A e e + (2 : ℝ) * 1 * s * quadReal A e x +
              s ^ 2 * quadReal A x x := by
              exact quadReal_expand A hA e x (1 : ℝ) s
      _ = quadReal A e e + s ^ 2 * Qxx := by
          have hex : quadReal A e x = 0 := by
            rw [quadReal_symm A hA e x, hxze]
          rw [hex]
          dsimp [Qxx]
          ring
  have hQxy : Qxy = s * Qxx := by
    dsimp [s, Qxy, Qxx]
    field_simp [hQxx_ne]
  have hsub : Qxy ^ 2 - Qxx * quadReal A y y = - (Qxx * quadReal A e e) := by
    rw [hQyy, hQxy]
    dsimp [Qxx]
    ring
  have hle : 0 ≤ Qxy ^ 2 - Qxx * quadReal A y y := by
    rw [hsub]
    have hQxx_pos : 0 < Qxx := by simpa [Qxx] using hxx
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hQxx_pos.le hze]
  dsimp [Qxy, Qxx] at hle
  nlinarith

-- ############################################################################
-- 2. Polynomial calculus
-- ############################################################################

abbrev ei {n : ℕ} (i : Fin n) : Fin n →₀ ℕ := Finsupp.single i 1

lemma pderiv_comm {n : ℕ} (i j : Fin n) (p : MvPolynomial (Fin n) ℝ) :
    pderiv i (pderiv j p) = pderiv j (pderiv i p) := by
  classical
  ext m
  by_cases hij : i = j
  · subst j
    rfl
  · have hji : j ≠ i := fun h => hij h.symm
    have hL : (pderiv i (pderiv j p)).coeff m =
        p.coeff ((m + ei i) + ei j) * ((m j : ℝ) + 1) * ((m i : ℝ) + 1) := by
      have h1 : (pderiv i (pderiv j p)).coeff m =
          (pderiv j p).coeff (m + ei i) * ((m i : ℝ) + 1) := by
        rw [MvPolynomial.coeff_pderiv]
      rw [h1]
      have h2 : (pderiv j p).coeff (m + ei i) =
          p.coeff ((m + ei i) + ei j) * (((m + ei i) j : ℝ) + 1) := by
        rw [MvPolynomial.coeff_pderiv]
      rw [h2]
      have hsim : (m + ei i) j = m j := by
        rw [Finsupp.add_apply]
        have hz : (ei i) j = 0 := Finsupp.single_eq_of_ne hji
        rw [hz, add_zero]
      rw [hsim]
    have hR : (pderiv j (pderiv i p)).coeff m =
        p.coeff ((m + ei j) + ei i) * ((m i : ℝ) + 1) * ((m j : ℝ) + 1) := by
      have h1 : (pderiv j (pderiv i p)).coeff m =
          (pderiv i p).coeff (m + ei j) * ((m j : ℝ) + 1) := by
        rw [MvPolynomial.coeff_pderiv]
      rw [h1]
      have h2 : (pderiv i p).coeff (m + ei j) =
          p.coeff ((m + ei j) + ei i) * (((m + ei j) i : ℝ) + 1) := by
        rw [MvPolynomial.coeff_pderiv]
      rw [h2]
      have hsim : (m + ei j) i = m i := by
        rw [Finsupp.add_apply]
        have hz : (ei j) i = 0 := Finsupp.single_eq_of_ne hij
        rw [hz, add_zero]
      rw [hsim]
    rw [hL, hR]
    have hcoeff : p.coeff ((m + ei i) + ei j) = p.coeff ((m + ei j) + ei i) := by
      congr 1
      abel
    rw [hcoeff]
    ring

lemma eval_nonneg_of_coeff_nonneg {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m) {w : Fin n → ℝ} (hw : ∀ k : Fin n, 0 ≤ w k) :
    0 ≤ MvPolynomial.eval w p := by
  classical
  rw [← MvPolynomial.support_sum_monomial_coeff p]
  rw [MvPolynomial.eval_sum]
  apply Finset.sum_nonneg
  intro m hm
  rw [MvPolynomial.eval_monomial]
  exact mul_nonneg (hp m) (by
    rw [Finsupp.prod_pow]
    apply Finset.prod_nonneg
    intro a _
    exact pow_nonneg (hw a) (m a))

lemma coeff_pderiv_nonneg {n : ℕ} (i : Fin n) (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m) :
    ∀ m : Fin n →₀ ℕ, 0 ≤ (pderiv i p).coeff m := by
  intro m
  rw [MvPolynomial.coeff_pderiv]
  exact mul_nonneg (hp (m + ei i)) (by positivity)

lemma eval_pderiv_nonneg {n : ℕ} (i : Fin n) (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m) {w : Fin n → ℝ} (hw : ∀ k : Fin n, 0 ≤ w k) :
    0 ≤ MvPolynomial.eval w (pderiv i p) :=
  eval_nonneg_of_coeff_nonneg (pderiv i p) (coeff_pderiv_nonneg i p hp) hw

lemma eval_pderiv_pderiv_nonneg {n : ℕ} (i j : Fin n) (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m) {w : Fin n → ℝ} (hw : ∀ k : Fin n, 0 ≤ w k) :
    0 ≤ MvPolynomial.eval w (pderiv i (pderiv j p)) := by
  apply eval_nonneg_of_coeff_nonneg (pderiv i (pderiv j p)) ?_ hw
  intro m
  apply coeff_pderiv_nonneg i (pderiv j p)
  exact coeff_pderiv_nonneg j p hp

lemma euler_eval {n : ℕ} (w : Fin n → ℝ) (q : MvPolynomial (Fin n) ℝ) (k : ℕ)
    (hq : q.IsHomogeneous k) :
    (∑ i : Fin n, w i * MvPolynomial.eval w (pderiv i q)) = (k : ℝ) * MvPolynomial.eval w q := by
  have heq := MvPolynomial.IsHomogeneous.sum_X_mul_pderiv (φ := q) hq
  have hae := congrArg (MvPolynomial.eval w) heq
  rw [map_sum] at hae
  simp only [map_mul, MvPolynomial.eval_X] at hae
  have hsmul : MvPolynomial.eval w ((k : ℕ) • q) = (k : ℕ) • MvPolynomial.eval w q := map_nsmul (MvPolynomial.eval w) k q
  rw [hsmul] at hae
  simpa [nsmul_eq_mul] using hae

-- ############################################################################
-- 3. Hessian matrix of p at w and Euler identities
-- ############################################################################

/-- the Hessian matrix (second partials) of `p` evaluated at `w` -/
def hess {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of (fun a b : Fin n => MvPolynomial.eval w (pderiv a (pderiv b p)))

lemma hess_symm {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (w : Fin n → ℝ) :
    (hess p w).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro a b
  dsimp [hess]
  congr 1
  rw [pderiv_comm]

/-- `(H w)_b = (d-1) ∂_b p(w)` (Euler) -/
lemma hess_mulVec_w {n d : ℕ} (p : MvPolynomial (Fin n) ℝ) (w : Fin n → ℝ)
    (hd : 1 ≤ d) (hp : p.IsHomogeneous d) (b : Fin n) :
    ((hess p w) *ᵥ w) b = ((d - 1 : ℕ) : ℝ) * MvPolynomial.eval w (pderiv b p) := by
  classical
  rw [Matrix.mulVec_apply_eq_sum]
  dsimp [hess]
  have hq : (pderiv b p).IsHomogeneous (d - 1) := by
    simpa using (hp.pderiv (i := b))
  have heu := euler_eval w (pderiv b p) (d - 1) hq
  calc
    (∑ a : Fin n, MvPolynomial.eval w (pderiv b (pderiv a p)) * w a)
        = ∑ a : Fin n, w a * MvPolynomial.eval w (pderiv a (pderiv b p)) := by
          apply Finset.sum_congr rfl
          intro a _
          have hswap : pderiv a (pderiv b p) = pderiv b (pderiv a p) := pderiv_comm a b p
          rw [hswap]
          ring
    _ = ((d - 1 : ℕ) : ℝ) * MvPolynomial.eval w (pderiv b p) := heu

/-- bilinear form of the Hessian on (w, u) -/
lemma quadReal_hess_w {n d : ℕ} (p : MvPolynomial (Fin n) ℝ) (w u : Fin n → ℝ)
    (hd : 1 ≤ d) (hp : p.IsHomogeneous d) :
    quadReal (hess p w) w u = ((d - 1 : ℕ) : ℝ) *
      (∑ b : Fin n, u b * MvPolynomial.eval w (pderiv b p)) := by
  classical
  rw [quadReal_symm (hess p w) (hess_symm p w) w u]
  rw [quadReal_mulVec (hess p w) u w]
  dsimp [dotProduct]
  calc
    (∑ i : Fin n, u i * ((hess p w *ᵥ w) i))
        = ∑ i : Fin n, u i * (((d - 1 : ℕ) : ℝ) * MvPolynomial.eval w (pderiv i p)) := by
          apply Finset.sum_congr rfl
          intro i _
          rw [hess_mulVec_w p w hd hp i]
    _ = ∑ i : Fin n, ((d - 1 : ℕ) : ℝ) * (u i * MvPolynomial.eval w (pderiv i p)) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = ((d - 1 : ℕ) : ℝ) * (∑ b : Fin n, u b * MvPolynomial.eval w (pderiv b p)) := by
          rw [Finset.mul_sum]

lemma sum_evec_mul {n : ℕ} (i : Fin n) (g : Fin n → ℝ) :
    (∑ b : Fin n, evec i b * g b) = g i := by
  classical
  calc
    (∑ b : Fin n, evec i b * g b) = ∑ b : Fin n, (if b = i then 1 else 0) * g b := by
      apply Finset.sum_congr rfl
      intro b _
      simp [evec]
    _ = g i := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hbi
        simp [hbi]
      · intro hi
        exact False.elim (hi (Finset.mem_univ i))

lemma sum_smul_evec_mul {n : ℕ} (i : Fin n) (c : ℝ) (g : Fin n → ℝ) :
    (∑ b : Fin n, (c • evec i) b * g b) = c * g i := by
  classical
  calc
    (∑ b : Fin n, (c • evec i) b * g b) = ∑ b : Fin n, c * (evec i b * g b) := by
      apply Finset.sum_congr rfl
      intro b _
      simp [Pi.smul_apply]
      ring
    _ = c * ∑ b : Fin n, evec i b * g b := by rw [Finset.mul_sum]
    _ = c * g i := by rw [sum_evec_mul]

/-- (w · H · u) for u = e_i + t e_j -/
lemma quadReal_hess_w_evec {n d : ℕ} (p : MvPolynomial (Fin n) ℝ) (w : Fin n → ℝ)
    (i j : Fin n) (t : ℝ) (hd : 1 ≤ d) (hp : p.IsHomogeneous d) :
    quadReal (hess p w) w (evec i + t • evec j) =
      ((d - 1 : ℕ) : ℝ) * (MvPolynomial.eval w (pderiv i p) + t * MvPolynomial.eval w (pderiv j p)) := by
  rw [quadReal_hess_w p w (evec i + t • evec j) hd hp]
  have hsum : (∑ b : Fin n, (evec i + t • evec j) b * MvPolynomial.eval w (pderiv b p)) =
      MvPolynomial.eval w (pderiv i p) + t * MvPolynomial.eval w (pderiv j p) := by
    calc
      (∑ b : Fin n, (evec i + t • evec j) b * MvPolynomial.eval w (pderiv b p))
          = ∑ b : Fin n, (evec i b * MvPolynomial.eval w (pderiv b p) +
              (t • evec j) b * MvPolynomial.eval w (pderiv b p)) := by
            apply Finset.sum_congr rfl
            intro b _
            rw [Pi.add_apply]
            ring
      _ = (∑ b : Fin n, evec i b * MvPolynomial.eval w (pderiv b p)) +
          ∑ b : Fin n, (t • evec j) b * MvPolynomial.eval w (pderiv b p) := by
            rw [Finset.sum_add_distrib]
      _ = MvPolynomial.eval w (pderiv i p) + t * MvPolynomial.eval w (pderiv j p) := by
            rw [sum_evec_mul, sum_smul_evec_mul]
  rw [hsum]

/-- (u · H · u) for u = e_i + t e_j -/
lemma quadReal_hess_evec {n : ℕ} (p : MvPolynomial (Fin n) ℝ) (w : Fin n → ℝ)
    (i j : Fin n) (t : ℝ) :
    quadReal (hess p w) (evec i + t • evec j) (evec i + t • evec j) =
      MvPolynomial.eval w (pderiv i (pderiv i p)) +
        2 * t * MvPolynomial.eval w (pderiv i (pderiv j p)) +
          t ^ 2 * MvPolynomial.eval w (pderiv j (pderiv j p)) := by
  classical
  calc
    quadReal (hess p w) (evec i + t • evec j) (evec i + t • evec j)
        = quadReal (hess p w) ((1 : ℝ) • evec i + t • evec j)
            ((1 : ℝ) • evec i + t • evec j) := by
          rw [show evec i + t • evec j = (1 : ℝ) • evec i + t • evec j by ext k; simp]
    _ = (1 : ℝ) ^ 2 * quadReal (hess p w) (evec i) (evec i) +
          2 * (1 : ℝ) * t * quadReal (hess p w) (evec i) (evec j) +
          t ^ 2 * quadReal (hess p w) (evec j) (evec j) := by
          rw [quadReal_expand (hess p w) (hess_symm p w) (evec i) (evec j) (1 : ℝ) t]
    _ = MvPolynomial.eval w (pderiv i (pderiv i p)) +
          2 * t * MvPolynomial.eval w (pderiv i (pderiv j p)) +
          t ^ 2 * MvPolynomial.eval w (pderiv j (pderiv j p)) := by
          rw [quadReal_single (hess p w) i, quadReal_single_off (hess p w) i j,
              quadReal_single (hess p w) j]
          dsimp [hess]
          ring

-- ############################################################################
-- 4. Pure algebra: from the reverse Cauchy-Schwarz quadratic in t to Rayleigh
-- ############################################################################

/-- Rayleigh-style algebra.  If for all t, (α+tβ)² ≥ δ(Z+2tH+t²X) and
δ,H,Z,X,α,β are all nonnegative, then δH ≤ 2αβ. -/
lemma rayleigh_algebra (α β δ H Z X : ℝ) (hδ : 0 ≤ δ) (hH : 0 ≤ H) (hZ : 0 ≤ Z) (hX : 0 ≤ X)
    (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hall : ∀ t : ℝ, (α + t * β) ^ 2 ≥ δ * (Z + 2 * t * H + t ^ 2 * X)) :
    δ * H ≤ 2 * α * β := by
  have hδH : 0 ≤ δ * H := mul_nonneg hδ hH
  have hall2 : ∀ t : ℝ, (α + t * β) ^ 2 ≥ 2 * t * (δ * H) := by
    intro t
    have ht2 : 0 ≤ t ^ 2 := sq_nonneg t
    have hmul : 0 ≤ δ * (Z + t ^ 2 * X) := by
      have hzx : 0 ≤ Z + t ^ 2 * X := add_nonneg hZ (mul_nonneg ht2 hX)
      exact mul_nonneg hδ hzx
    specialize hall t
    nlinarith
  by_cases hβ0 : β = 0
  · by_cases hα0 : α = 0
    · have ht1 := hall2 1
      have ht1' : 2 * (δ * H) ≤ 0 := by
        simpa [hβ0, hα0] using ht1
      nlinarith
    · have hαpos : 0 < α := lt_of_le_of_ne' hα hα0
      have htarget0 : 2 * α * β = 0 := by rw [hβ0]; ring
      by_contra hneg
      have hneg0 : ¬ δ * H ≤ 0 := by simpa [htarget0] using hneg
      have hδHpos : 0 < δ * H := lt_of_not_ge hneg0
      let t : ℝ := α ^ 2 / (2 * (δ * H)) + 1
      have ht := hall2 t
      have ht1 : α ^ 2 ≥ 2 * t * (δ * H) := by
        simpa [hβ0] using ht
      dsimp [t] at ht1
      have hd1 : 2 * (δ * H) ≠ 0 := by positivity
      have hd2 : δ * H ≠ 0 := ne_of_gt hδHpos
      field_simp [hd1, hd2] at ht1
      have hd : δ ≠ 0 := by
        intro hz
        apply (ne_of_gt hδHpos)
        rw [hz]
        simp
      have hHn : H ≠ 0 := by
        intro hz
        apply (ne_of_gt hδHpos)
        rw [hz]
        simp
      have hsplit : δ * H * (α ^ 2 / (δ * H) + 2) = α ^ 2 + 2 * (δ * H) := by
        field_simp [hd, hHn]
      rw [hsplit] at ht1
      nlinarith
  · have hβpos : 0 < β := lt_of_le_of_ne' hβ hβ0
    by_cases hα0 : α = 0
    · have htarget0 : 2 * α * β = 0 := by rw [hα0]; ring
      by_contra hneg
      have hneg0 : ¬ δ * H ≤ 0 := by simpa [htarget0] using hneg
      have hδHpos : 0 < δ * H := lt_of_not_ge hneg0
      let t : ℝ := δ * H / (2 * β ^ 2)
      have ht := hall2 t
      have ht1 : (t * β) ^ 2 ≥ 2 * t * (δ * H) := by
        simpa [hα0] using ht
      dsimp [t] at ht1
      have hd1 : 2 * β ^ 2 ≠ 0 := by positivity
      have hd2 : δ * H ≠ 0 := ne_of_gt hδHpos
      have hd3 : β ≠ 0 := hβ0
      field_simp [hd1, hd2, hd3] at ht1
      nlinarith
    · have hαpos : 0 < α := lt_of_le_of_ne' hα hα0
      have hβne : β ≠ 0 := hβ0
      let t : ℝ := α / β
      have ht := hall2 t
      dsimp [t] at ht
      have hαβ : α / β * β = α := by
        field_simp [hβne]
      rw [hαβ] at ht
      have hleft : (α + α) ^ 2 = 4 * α ^ 2 := by ring
      rw [hleft] at ht
      have hβpos2 : 0 ≤ β := le_of_lt hβpos
      have hmul := mul_le_mul_of_nonneg_right ht hβpos2
      have hsimpl : (2 * (α / β) * (δ * H)) * β = 2 * α * (δ * H) := by
        field_simp [hβne]
      rw [hsimpl] at hmul
      have hfactor : (2 * α) * (2 * α * β) = 4 * α ^ 2 * β := by ring
      have hle : (2 * α) * (δ * H) ≤ (2 * α) * (2 * α * β) := by
        rw [hfactor]
        exact hmul
      exact le_of_mul_le_mul_left hle (by positivity : 0 < 2 * α)

-- ############################################################################
-- 5. positivity of eval and the main strict-orthant Rayleigh lemma
-- ############################################################################

/-- nonzero polynomial with nonnegative coefficients is positive on the open orthant -/
lemma eval_pos_of_ne_zero {n : ℕ} (p : MvPolynomial (Fin n) ℝ)
    (hp : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m) {w : Fin n → ℝ} (hw : ∀ k : Fin n, 0 < w k)
    (hne : p ≠ 0) : 0 < MvPolynomial.eval w p := by
  classical
  have hsm : ∃ m : Fin n →₀ ℕ, p.coeff m ≠ 0 := by
    by_contra h
    apply hne
    ext m
    exact not_not.mp (fun hz => h ⟨m, hz⟩)
  obtain ⟨m, hm⟩ := hsm
  have hmpos : 0 < p.coeff m := lt_of_le_of_ne' (hp m) hm
  rw [← MvPolynomial.support_sum_monomial_coeff p]
  rw [MvPolynomial.eval_sum]
  refine Finset.sum_pos' (fun a ha => ?_) ⟨m, ?_, ?_⟩
  · have hma : m ∈ p.support := MvPolynomial.mem_support_iff.mpr hm
    -- a ∈ p.support: term ≥ 0
    rw [MvPolynomial.eval_monomial]
    exact mul_nonneg (hp a) (by
      rw [Finsupp.prod_pow]
      exact Finset.prod_nonneg (fun k _ => pow_nonneg (le_of_lt (hw k)) (a k)))
  · exact MvPolynomial.mem_support_iff.mpr hm
  · rw [MvPolynomial.eval_monomial]
    apply mul_pos hmpos
    rw [Finsupp.prod_pow]
    exact Finset.prod_pos (fun k _ => pow_pos (hw k) (m k))

/-- Rayleigh inequality at strictly positive `w`. -/
lemma rayleigh_pos {n d : ℕ} (hd : 2 ≤ d) (p : MvPolynomial (Fin n) ℝ)
    (hp : p.IsHomogeneous d)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m)
    (hindex : ∀ w : Fin n → ℝ, (∀ k : Fin n, 0 < w k) →
      ((hess p w).charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1) :
    ∀ i j : Fin n, ∀ w : Fin n → ℝ, (∀ k : Fin n, 0 < w k) →
      MvPolynomial.eval w p * MvPolynomial.eval w (pderiv i (pderiv j p)) ≤
        (2 : ℝ) * (1 - 1 / (d : ℝ)) *
          (MvPolynomial.eval w (pderiv i p) * MvPolynomial.eval w (pderiv j p)) := by
  classical
  intro i j w hw
  by_cases hp0 : p = 0
  · subst p
    simp
  · have hw0 : ∀ k : Fin n, 0 ≤ w k := fun k => le_of_lt (hw k)
    have hpv : 0 ≤ MvPolynomial.eval w p := eval_nonneg_of_coeff_nonneg p hnn hw0
    have hpvpos : 0 < MvPolynomial.eval w p := eval_pos_of_ne_zero p hnn hw hp0
    have hd1 : 1 ≤ d := by omega
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast (by omega : 0 < d)
    have hdR_ne : (d : ℝ) ≠ 0 := ne_of_gt hdR
    have hmpos : 0 < ((d - 1 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : 0 < d - 1)
    have hm_ne : ((d - 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hmpos
    have hcast : (((d - 1 : ℕ) : ℝ)) = (d : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : (1 : ℕ) ≤ d)]
      norm_num
    let di : ℝ := MvPolynomial.eval w (pderiv i p)
    let dj : ℝ := MvPolynomial.eval w (pderiv j p)
    let dij : ℝ := MvPolynomial.eval w (pderiv i (pderiv j p))
    let dii : ℝ := MvPolynomial.eval w (pderiv i (pderiv i p))
    let djj : ℝ := MvPolynomial.eval w (pderiv j (pderiv j p))
    let pv : ℝ := MvPolynomial.eval w p
    let α : ℝ := ((d - 1 : ℕ) : ℝ) * di
    let β : ℝ := ((d - 1 : ℕ) : ℝ) * dj
    let δ : ℝ := (d : ℝ) * ((d - 1 : ℕ) : ℝ) * pv
    have hdi : 0 ≤ di := by simpa [di] using eval_pderiv_nonneg i p hnn hw0
    have hdj : 0 ≤ dj := by simpa [dj] using eval_pderiv_nonneg j p hnn hw0
    have hdij : 0 ≤ dij := by simpa [dij] using eval_pderiv_pderiv_nonneg i j p hnn hw0
    have hdii : 0 ≤ dii := by simpa [dii] using eval_pderiv_pderiv_nonneg i i p hnn hw0
    have hdjj : 0 ≤ djj := by simpa [djj] using eval_pderiv_pderiv_nonneg j j p hnn hw0
    have hα : 0 ≤ α := by
      dsimp [α]
      exact mul_nonneg hmpos.le hdi
    have hβ : 0 ≤ β := by
      dsimp [β]
      exact mul_nonneg hmpos.le hdj
    have hδ : 0 ≤ δ := by
      dsimp [δ]
      exact mul_nonneg (mul_nonneg hdR.le hmpos.le) hpv
    have hA_symm : (hess p w).IsSymm := hess_symm p w
    have hA_card : ((hess p w).charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1 := hindex w hw
    have hww : quadReal (hess p w) w w = δ := by
      calc
        quadReal (hess p w) w w
            = ((d - 1 : ℕ) : ℝ) * (∑ b : Fin n, w b * MvPolynomial.eval w (pderiv b p)) := by
                rw [quadReal_hess_w p w w hd1 hp]
        _ = ((d - 1 : ℕ) : ℝ) * ((d : ℝ) * MvPolynomial.eval w p) := by
                rw [euler_eval w p d hp]
        _ = (d : ℝ) * ((d - 1 : ℕ) : ℝ) * MvPolynomial.eval w p := by ring
        _ = δ := by rfl
    have hxx : 0 < quadReal (hess p w) w w := by
      rw [hww]
      dsimp [δ]
      positivity
    have hqwu : ∀ t : ℝ, quadReal (hess p w) w (evec i + t • evec j) = α + t * β := by
      intro t
      have h := quadReal_hess_w_evec p w i j t hd1 hp
      -- h : quadReal ... = ((d-1:ℕ):ℝ) * (eval (pderiv i p) + t * eval (pderiv j p))
      dsimp [α, β, di, dj] at h ⊢
      ring_nf at h ⊢
      exact h
    have hquu : ∀ t : ℝ, quadReal (hess p w) (evec i + t • evec j) (evec i + t • evec j) =
        dii + 2 * t * dij + t ^ 2 * djj := by
      intro t
      have h := quadReal_hess_evec p w i j t
      dsimp [dii, dij, djj] at h ⊢
      ring_nf at h ⊢
      exact h
    have hall : ∀ t : ℝ, (α + t * β) ^ 2 ≥ δ * (dii + 2 * t * dij + t ^ 2 * djj) := by
      intro t
      have ht := quadReal_sq_ge_self_mul (hess p w) hA_symm hA_card w (evec i + t • evec j) hxx
      rw [hqwu t, hww, hquu t] at ht
      exact ht
    have halg := rayleigh_algebra α β δ dij dii djj hδ hdij hdii hdjj hα hβ hall
    -- halg : δ * dij ≤ 2 * α * β
    have hδH : (d : ℝ) * ((d - 1 : ℕ) : ℝ) * pv * dij ≤
        2 * (((d - 1 : ℕ) : ℝ) * di) * (((d - 1 : ℕ) : ℝ) * dj) := by
      dsimp [δ, α, β] at halg
      exact halg
    -- final transformation to the desired form
    have hδH2 : ((d - 1 : ℕ) : ℝ) * ((d : ℝ) * pv * dij) ≤
        ((d - 1 : ℕ) : ℝ) * (2 * (di * dj) * ((d - 1 : ℕ) : ℝ)) := by
      dsimp [δ, α, β] at halg
      nlinarith
    have hdiv1 : (d : ℝ) * pv * dij ≤ 2 * (di * dj) * ((d - 1 : ℕ) : ℝ) :=
      le_of_mul_le_mul_left hδH2 hmpos
    have hC : (2 : ℝ) * (1 - 1 / (d : ℝ)) = 2 * (((d - 1 : ℕ) : ℝ)) / (d : ℝ) := by
      rw [hcast]
      field_simp [hdR_ne]
    have hfinal : pv * dij ≤ 2 * (1 - 1 / (d : ℝ)) * (di * dj) := by
      rw [hC]
      field_simp [hdR_ne]
      have hgoal : pv * dij * (d : ℝ) ≤ 2 * ((d - 1 : ℕ) : ℝ) * di * dj := by
        nlinarith [hdiv1]
      exact hgoal
    dsimp [pv, dij, di, dj] at hfinal ⊢
    exact hfinal
end rayleigh_pre

/-- Rayleigh inequality, main theorem: Hessian with at most one positive root forces the
Brändén--Huh two-variable bound for all nonnegative evaluation points. -/
theorem rayleigh_of_hessian_roots_le_one {n d : ℕ} (hd : 2 ≤ d)
    (p : MvPolynomial (Fin n) ℝ) (hp : p.IsHomogeneous d)
    (hnn : ∀ m : Fin n →₀ ℕ, 0 ≤ p.coeff m)
    (hindex : ∀ w : Fin n → ℝ, (∀ k : Fin n, 0 < w k) →
      ((Matrix.of (fun a b : Fin n => MvPolynomial.eval w (MvPolynomial.pderiv a (MvPolynomial.pderiv b p)))).charpoly.roots.filter (fun r : ℝ => 0 < r)).card ≤ 1) :
    ∀ i j : Fin n, ∀ w : Fin n → ℝ, (∀ k : Fin n, 0 ≤ w k) →
      MvPolynomial.eval w p * MvPolynomial.eval w (MvPolynomial.pderiv i (MvPolynomial.pderiv j p)) ≤
        (2 : ℝ) * (1 - 1 / (d : ℝ)) *
          (MvPolynomial.eval w (MvPolynomial.pderiv i p) * MvPolynomial.eval w (MvPolynomial.pderiv j p)) := by
  classical
  intro i j w hw
  have hpos_main := rayleigh_pre.rayleigh_pos hd p hp hnn
    (fun w0 hw0 => by
      have hh := hindex w0 hw0
      simpa [rayleigh_pre.hess] using hh)
    i j
  have hposg : ∀ t : ℝ, 0 < t →
      0 ≤ (2 : ℝ) * (1 - 1 / (d : ℝ)) *
            (MvPolynomial.eval (fun a : Fin n => w a + t) (pderiv i p) *
              MvPolynomial.eval (fun a : Fin n => w a + t) (pderiv j p)) -
        MvPolynomial.eval (fun a : Fin n => w a + t) p *
          MvPolynomial.eval (fun a : Fin n => w a + t) (pderiv i (pderiv j p)) := by
    intro t ht
    have h := hpos_main (fun a : Fin n => w a + t) (fun a => by
      have hwa : 0 ≤ w a := hw a
      linarith)
    nlinarith
  have hcont_eval : ∀ q : MvPolynomial (Fin n) ℝ,
      Continuous (fun x : Fin n → ℝ => MvPolynomial.eval x q) := by
    intro q
    exact MvPolynomial.continuous_eval q
  have hF_cont : Continuous (fun x : Fin n → ℝ =>
      (2 : ℝ) * (1 - 1 / (d : ℝ)) *
        (MvPolynomial.eval x (pderiv i p) * MvPolynomial.eval x (pderiv j p)) -
      MvPolynomial.eval x p * MvPolynomial.eval x (pderiv i (pderiv j p))) := by
    exact (continuous_const.mul ((hcont_eval (pderiv i p)).mul (hcont_eval (pderiv j p)))).sub
      ((hcont_eval p).mul (hcont_eval (pderiv i (pderiv j p))))
  have hshift : Continuous (fun t : ℝ => (fun a : Fin n => w a + t)) := by
    exact continuous_pi (fun a : Fin n => continuous_const.add continuous_id)
  have hg : Continuous (fun t : ℝ =>
      (2 : ℝ) * (1 - 1 / (d : ℝ)) *
        (MvPolynomial.eval (fun a : Fin n => w a + t) (pderiv i p) *
          MvPolynomial.eval (fun a : Fin n => w a + t) (pderiv j p)) -
      MvPolynomial.eval (fun a : Fin n => w a + t) p *
        MvPolynomial.eval (fun a : Fin n => w a + t) (pderiv i (pderiv j p))) :=
    hF_cont.comp hshift
  have hev : ∀ᶠ c in 𝓝[>] (0 : ℝ),
      0 ≤ (2 : ℝ) * (1 - 1 / (d : ℝ)) *
            (MvPolynomial.eval (fun a : Fin n => w a + c) (pderiv i p) *
              MvPolynomial.eval (fun a : Fin n => w a + c) (pderiv j p)) -
        MvPolynomial.eval (fun a : Fin n => w a + c) p *
          MvPolynomial.eval (fun a : Fin n => w a + c) (pderiv i (pderiv j p)) := by
    filter_upwards [self_mem_nhdsWithin] with c hc
    exact hposg c hc
  haveI : (𝓝[>] (0 : ℝ)).NeBot := by infer_instance
  have hlim : 0 ≤ (2 : ℝ) * (1 - 1 / (d : ℝ)) *
        (MvPolynomial.eval (fun a : Fin n => w a + 0) (pderiv i p) *
          MvPolynomial.eval (fun a : Fin n => w a + 0) (pderiv j p)) -
      MvPolynomial.eval (fun a : Fin n => w a + 0) p *
        MvPolynomial.eval (fun a : Fin n => w a + 0) (pderiv i (pderiv j p)) :=
    ge_of_tendsto (hg.continuousAt.tendsto.mono_left nhdsWithin_le_nhds) hev
  have hw0 : (fun a : Fin n => w a + 0) = w := by
    ext a
    simp
  rw [hw0] at hlim
  nlinarith

end

end Commons.LorentzianPolynomials