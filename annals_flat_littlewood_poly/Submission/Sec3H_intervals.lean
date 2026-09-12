import Mathlib
import Submission.Sec3H_defs
import Submission.Sec3H_deriv
import Submission.Sec3H_lbounds
import Submission.Sec3H_origin

/-! Lemma 3.6 of the paper (intervals are "nice").

Let `0 < η < 2^(-11)`.  Every closed interval of length `7η` contains a
subinterval of length `η` on which `|Re H(x)| ≥ η^3 / 2^7` everywhere. -/

noncomputable section
open scoped Polynomial BigOperators
open Polynomial Complex

set_option autoImplicit false

namespace Submission
namespace Sec3H

/-! ### Clean (axiom-free) analytic helpers -/

/-- `Re` commutes with one-dimensional `deriv` (chain rule for the real-linear
continuous map `Complex.re`). -/
lemma deriv_re_apply (L : ℂ →L[ℝ] ℝ) {h : ℝ → ℂ} {x : ℝ} (hh : DifferentiableAt ℝ h x) :
    deriv (fun y : ℝ => L (h y)) x = L (deriv h x) := by
  change (fderiv ℝ ((fun z : ℂ => L z) ∘ h) x) 1 = L ((fderiv ℝ h x) 1)
  have hLdiff : DifferentiableAt ℝ (fun z : ℂ => L z) (h x) := by
    exact ContinuousLinearMap.differentiableAt L
  have hcomp := fderiv_comp (𝕜 := ℝ) (f := h) (g := fun z : ℂ => L z)
    (hg := hLdiff) (hf := hh)
  rw [hcomp]
  have hLfderiv : fderiv ℝ (fun z : ℂ => L z) (h x) = L := by
    exact ContinuousLinearMap.fderiv L
  rw [hLfderiv]
  rfl

/-- `iteratedDeriv` commutes with any continuous real-linear map, for `C^k` functions. -/
lemma iteratedDeriv_clm (L : ℂ →L[ℝ] ℝ) (f : ℝ → ℂ) : ∀ (k : ℕ) (x : ℝ),
    ContDiff ℝ (k : ℕ) f →
    iteratedDeriv k (fun y : ℝ => L (f y)) x = L (iteratedDeriv k f x) := by
  intro k
  induction k with
  | zero =>
      intro x hf
      simp
  | succ k ih =>
      intro x hf
      calc
        iteratedDeriv (k + 1) (fun y : ℝ => L (f y)) x
            = deriv (iteratedDeriv k (fun y : ℝ => L (f y))) x := by rw [iteratedDeriv_succ]
        _ = deriv (fun y : ℝ => L (iteratedDeriv k f y)) x := by
            congr 1
            funext y
            have hfk : ContDiff ℝ (k : ℕ) f := by
              exact hf.of_le (by exact_mod_cast (Nat.le_succ k))
            exact ih y hfk
        _ = L (deriv (iteratedDeriv k f) x) := by
            apply deriv_re_apply
            exact (hf.differentiable_iteratedDeriv' (m := k)).differentiableAt
        _ = L (iteratedDeriv (k + 1) f x) := by rw [iteratedDeriv_succ]

/-- `iteratedDeriv k (Re ∘ H) x = Re (iteratedDeriv k H x)`. -/
lemma iteratedDeriv_reH (t : ℕ) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun y : ℝ => (H t y).re) x = (iteratedDeriv k (H t) x).re := by
  have h := iteratedDeriv_clm (L := Complex.reCLM) (f := H t) k x (contDiff_H (n := (k : ℕ)) t)
  simpa [Complex.reCLM_apply] using h

/-- `Re ∘ H t` is smooth. -/
lemma contDiff_reH {n : WithTop ℕ∞} (t : ℕ) : ContDiff ℝ n (fun x : ℝ => (H t x).re) := by
  have h1 := contDiff_H (n := n) t
  have hre : ContDiff ℝ n (Complex.reCLM : ℂ → ℝ) := Complex.reCLM.contDiff
  have hc : ContDiff ℝ n (Complex.reCLM ∘ (H t)) := hre.comp h1
  convert hc using 1
  ext x
  rfl

/-- Clean (no `native_decide`) norm bound `‖H^(k)‖ ≤ 2^k + 2` for `k ≤ 4`. -/
lemma H_iter_deriv_norm_le_clean (t : ℕ) {k : ℕ} (hk4 : k ≤ 4) (x : ℝ) :
    ‖iteratedDeriv k (H t) x‖ ≤ (2 : ℝ) ^ k + 2 := by
  let T1 : ℂ := Complex.I ^ k * Sec3.eθ x * alpha t x
  let T2 : ℂ := ((2 : ℂ) * Complex.I) ^ k * Sec3.eθ (2 * x) * beta t x
  have hdiff : ‖iteratedDeriv k (H t) x - (T1 + T2)‖ ≤ 1 / 8 := by
    have hET : ETerm t x k = T1 + T2 := by
      unfold ETerm T1 T2
      ring
    rw [← hET]
    exact H_iter_deriv_approx_clean t hk4 x
  have hT1 : ‖T1‖ ≤ 1 := by
    unfold T1
    rw [norm_mul]
    rw [norm_eθ_I_pow k x]
    have hα : ‖alpha t x‖ ≤ 1 := norm_alpha_le t x
    nlinarith
  have hT2 : ‖T2‖ ≤ (2 : ℝ) ^ k := by
    unfold T2
    rw [norm_mul]
    rw [norm_eθ_2I_pow k x]
    have hβ : ‖beta t x‖ ≤ 1 := norm_beta_le t x
    have hp : 0 ≤ (2 : ℝ) ^ k := pow_nonneg (by norm_num) k
    have hle : (2 : ℝ) ^ k * ‖beta t x‖ ≤ (2 : ℝ) ^ k * 1 := mul_le_mul_of_nonneg_left hβ hp
    nlinarith
  have hTsum1 : ‖T1 + T2‖ ≤ ‖T1‖ + ‖T2‖ := norm_add_le T1 T2
  have hb : ‖iteratedDeriv k (H t) x‖ ≤ 1 / 8 + (‖T1‖ + ‖T2‖) := by
    calc
      ‖iteratedDeriv k (H t) x‖ = ‖(iteratedDeriv k (H t) x - (T1 + T2)) + (T1 + T2)‖ := by ring_nf
      _ ≤ ‖iteratedDeriv k (H t) x - (T1 + T2)‖ + ‖T1 + T2‖ := norm_add_le _ _
      _ ≤ 1 / 8 + ‖T1 + T2‖ := by nlinarith [hdiff]
      _ ≤ 1 / 8 + (‖T1‖ + ‖T2‖) := by nlinarith [hTsum1]
  calc
    ‖iteratedDeriv k (H t) x‖ ≤ 1 / 8 + (‖T1‖ + ‖T2‖) := hb
    _ ≤ 1 / 8 + (1 + (2 : ℝ) ^ k) := by nlinarith [hT1, hT2]
    _ ≤ (2 : ℝ) ^ k + 2 := by nlinarith

/-- Sup-bound on iterated derivatives of `f = Re ∘ H`. -/
lemma reH_iter_deriv_abs_le (t : ℕ) {m : ℕ} (hm1 : 1 ≤ m) (hm4 : m ≤ 4) (z : ℝ) :
    |iteratedDeriv m (fun y : ℝ => (H t y).re) z| ≤ (2 : ℝ) ^ m + 2 := by
  rw [iteratedDeriv_reH]
  have h1 := Complex.abs_re_le_norm (iteratedDeriv m (H t) z)
  have h2 := H_iter_deriv_norm_le_clean t hm4 z
  nlinarith

/-- iterated derivative of a real polynomial function. -/
lemma iteratedDeriv_polyEvalR (P : ℝ[X]) (k : ℕ) (x : ℝ) :
    iteratedDeriv k (fun y : ℝ => P.eval y) x = (Polynomial.derivative^[k] P).eval x := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      calc
        iteratedDeriv (k + 1) (fun y : ℝ => P.eval y) x
            = deriv (iteratedDeriv k (fun y : ℝ => P.eval y)) x := by rw [iteratedDeriv_succ]
        _ = deriv (fun y : ℝ => (Polynomial.derivative^[k] P).eval y) x := by
            congr 1
            funext y
            exact ih y
        _ = (Polynomial.derivative^[k + 1] P).eval x := by
            have h : (Polynomial.derivative^[k + 1] P) = (Polynomial.derivative^[k] P).derivative := by
              rw [Function.iterate_succ_apply']
            rw [h]
            exact Polynomial.deriv (p := (Polynomial.derivative^[k] P))

/-- Real polynomial functions are smooth. -/
lemma contDiff_polyEvalR (P : ℝ[X]) {n : WithTop ℕ∞} : ContDiff ℝ n (fun x : ℝ => P.eval x) := by
  have h := Polynomial.contDiff_aeval (R := ℝ) (𝕜 := ℝ) P n
  simpa [Polynomial.aeval_def] using h

/-- Repeated Rolle with nodes indexed by naturals: if `g` vanishes at
`w 0, ..., w k` (increasing) then `iteratedDeriv k g` vanishes between
`w 0` and `w k`. -/
lemma exists_iteratedDeriv_eq_zero_of_zeros_Nat : ∀ (k : ℕ) (g : ℝ → ℝ),
    ContDiff ℝ (k + 1 : ℕ) g →
    ∀ (w : ℕ → ℝ),
      (∀ m : ℕ, m < k → w m < w (m + 1)) →
      (∀ m : ℕ, m ≤ k → g (w m) = 0) →
      ∃ ξ : ℝ, w 0 ≤ ξ ∧ ξ ≤ w k ∧ iteratedDeriv k g ξ = 0 := by
  intro k
  induction k with
  | zero =>
      intro g hcd w hwmono hw0
      refine ⟨w 0, le_rfl, ?_, ?_⟩
      · simpa using (le_rfl : w 0 ≤ w 0)
      · simpa using hw0 0 (by norm_num)
  | succ k ih =>
      intro g hcd w hwmono hw0
      have rolle : ∀ m : ℕ, m ≤ k → ∃ c : ℝ, w m < c ∧ c < w (m + 1) ∧ deriv g c = 0 := by
        intro m hm
        have hlt : w m < w (m + 1) := hwmono m (by omega)
        have hcont : ContinuousOn g (Set.Icc (w m) (w (m + 1))) := by
          exact hcd.continuous.continuousOn
        have hfI : g (w m) = g (w (m + 1)) := by
          have h1 : g (w m) = 0 := hw0 m (by omega)
          have h2 : g (w (m + 1)) = 0 := hw0 (m + 1) (by omega)
          rw [h1, h2]
        rcases exists_deriv_eq_zero hlt hcont hfI with ⟨c, hc1, hc2⟩
        exact ⟨c, hc1.1, hc1.2, hc2⟩
      let c : ℕ → ℝ := fun m => if hm : m ≤ k then Classical.choose (rolle m hm) else 0
      have cspec : ∀ m : ℕ, m ≤ k → w m < c m ∧ c m < w (m + 1) ∧ deriv g (c m) = 0 := by
        intro m hm
        simp [c, hm]
        exact Classical.choose_spec (rolle m hm)
      have cmono : ∀ m : ℕ, m < k → c m < c (m + 1) := by
        intro m hm
        have h1 : c m < w (m + 1) := (cspec m (by omega)).2.1
        have h2 : w (m + 1) < c (m + 1) := (cspec (m + 1) (by omega)).1
        exact lt_trans h1 h2
      have cz : ∀ m : ℕ, m ≤ k → deriv g (c m) = 0 := fun m hm => (cspec m hm).2.2
      have hcd' : ContDiff ℝ (k + 1 : ℕ) (deriv g) := by
        exact hcd.deriv'
      rcases ih (deriv g) hcd' c cmono cz with ⟨ξ, hξ1, hξ2, hξ3⟩
      refine ⟨ξ, ?_, ?_, ?_⟩
      · have hw0c0 : w 0 < c 0 := (cspec 0 (by omega)).1
        exact le_trans (le_of_lt hw0c0) hξ1
      · have hckw : c k < w (k + 1) := (cspec k (by omega)).2.1
        exact le_trans hξ2 (le_of_lt hckw)
      · rw [iteratedDeriv_succ']
        exact hξ3

/-- The `k`-th derivative (as a polynomial) of the interpolating polynomial
through `(u i, f (u i))` is bounded by `(k+1)! · M / η^k` wherever evaluated,
provided the `k+1` nodes are pairwise at least `η` apart and `|f| ≤ M` there. -/
lemma interp_deriv_norm_le {k : ℕ} {η M : ℝ} (hη0 : 0 < η)
    (u : Fin (k + 1) → ℝ) (f : ℝ → ℝ)
    (hsep : ∀ i j : Fin (k + 1), i ≠ j → η ≤ |u i - u j|)
    (hval : ∀ i : Fin (k + 1), |f (u i)| ≤ M) (x : ℝ) :
    |(Polynomial.derivative^[k]
        (Lagrange.interpolate (Finset.univ : Finset (Fin (k + 1))) u (fun i => f (u i)))).eval x|
      ≤ (k + 1).factorial * M / η ^ k := by
  let s : Finset (Fin (k + 1)) := Finset.univ
  let P : ℝ[X] := Lagrange.interpolate s u (fun i => f (u i))
  have hM0 : 0 ≤ M := by
    have hz : |f (u (0 : Fin (k + 1)))| ≤ M := hval 0
    exact le_trans (abs_nonneg _) hz
  have hinj : Set.InjOn u (s : Set (Fin (k + 1))) := by
    intro i hi j hj huij
    by_contra hne
    have hz : η ≤ (0 : ℝ) := by
      simpa [huij] using hsep i j hne
    nlinarith
  have hcard : s.card = k + 1 := by simp [s]
  have hdeg : P.degree < ↑s.card := by
    simpa [P] using (Lagrange.degree_interpolate_lt (fun i => f (u i)) (s := s) (v := u) hinj)
  have hklt : k < s.card := by rw [hcard]; omega
  have hformula := Lagrange.eval_iterate_derivative_eq_sum (s := s) (v := u) (hvs := hinj)
      (P := P) (hP := hdeg) (hk := hklt) x
  have hc0 : ∀ i : Fin (k + 1), (s.erase i).powersetCard (s.card - (k + 1)) = {∅} := by
    intro i
    have hc : s.card - (k + 1) = 0 := by rw [hcard]; omega
    rw [hc]
    exact Finset.powersetCard_zero (s.erase i)
  have hformula' :
      eval x (derivative^[k] P) =
        (k.factorial : ℝ) * ∑ i ∈ s, (f (u i) / ∏ j ∈ s.erase i, (u i - u j)) := by
    rw [hformula]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    have hev : Polynomial.eval (u i) P = f (u i) := by
      simp [P]
      exact Lagrange.eval_interpolate_at_node (fun i => f (u i)) hinj hi
    rw [hev]
    have hinner : ∑ t ∈ (s.erase i).powersetCard (s.card - (k + 1)), ∏ a ∈ t, (x - u a) = 1 := by
      rw [hc0 i]
      simp
    rw [hinner, mul_one]
  have hfact0 : 0 ≤ (k.factorial : ℝ) := by exact_mod_cast (Nat.zero_le _)
  have term_le : ∀ i : Fin (k + 1), |f (u i) / ∏ j ∈ s.erase i, (u i - u j)| ≤ M / η ^ k := by
    intro i
    rw [abs_div]
    rw [Finset.abs_prod]
    have hcardErase : (s.erase i).card = k := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), hcard]
      omega
    have hpd : η ^ k ≤ ∏ j ∈ s.erase i, |u i - u j| := by
      calc
        η ^ k = η ^ (s.erase i).card := by rw [hcardErase]
        _ = ∏ _j ∈ s.erase i, η := by rw [Finset.prod_const]
        _ ≤ ∏ j ∈ s.erase i, |u i - u j| := by
            exact Finset.prod_le_prod (s := s.erase i) (f := fun _ : Fin (k+1) => η)
              (g := fun j => |u i - u j|) (fun _ _ => hη0.le)
              (fun j hj => hsep i j (Finset.mem_erase.mp hj).1.symm)
    have hDpos : 0 < ∏ j ∈ s.erase i, |u i - u j| := lt_of_lt_of_le (pow_pos hη0 k) hpd
    have hcross : |f (u i)| * η ^ k ≤ M * (∏ j ∈ s.erase i, |u i - u j|) := by
      exact mul_le_mul (hval i) hpd (pow_nonneg hη0.le k) hM0
    field_simp [hDpos.ne', (pow_pos hη0 k).ne']
    nlinarith [hcross]
  have hsum_le : ∑ i ∈ s, |f (u i) / ∏ j ∈ s.erase i, (u i - u j)| ≤ ∑ i ∈ s, (M / η ^ k) := by
    apply Finset.sum_le_sum
    intro i hi
    exact term_le i
  calc
    |eval x (derivative^[k] P)|
        = |(k.factorial : ℝ) * ∑ i ∈ s, (f (u i) / ∏ j ∈ s.erase i, (u i - u j))| := by rw [hformula']
    _ ≤ |(k.factorial : ℝ)| * |∑ i ∈ s, (f (u i) / ∏ j ∈ s.erase i, (u i - u j))| := (abs_mul _ _).le
    _ = (k.factorial : ℝ) * |∑ i ∈ s, (f (u i) / ∏ j ∈ s.erase i, (u i - u j))| := by
        rw [abs_of_nonneg hfact0]
    _ ≤ (k.factorial : ℝ) * (∑ i ∈ s, |f (u i) / ∏ j ∈ s.erase i, (u i - u j)|) := by
        exact mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs (fun i : Fin (k+1) => f (u i) / ∏ j ∈ s.erase i, (u i - u j)) s)) hfact0
    _ ≤ (k.factorial : ℝ) * (∑ i ∈ s, (M / η ^ k)) := by
        exact mul_le_mul_of_nonneg_left hsum_le hfact0
    _ = (k.factorial : ℝ) * ((k + 1 : ℝ) * (M / η ^ k)) := by
        have hcard2 : s.card = k + 1 := hcard
        rw [Finset.sum_const]
        simp [hcard2]
    _ = ((k + 1).factorial : ℝ) * (M / η ^ k) := by
        have hfact : ((k + 1).factorial : ℝ) = (k + 1 : ℝ) * (k.factorial : ℝ) := by
          rw [Nat.factorial_succ]
          norm_num
        rw [hfact]
        ring
    _ = ((k + 1).factorial : ℝ) * M / η ^ k := by
        field_simp [pow_ne_zero k hη0.ne']

/-- Master estimate: nodes `u 0 < ... < u k` with gaps ≥ η and all inside a
length-`7η` window; small function values and a bound on `f^(k+1)` force
`f^(k)(u 0)` small. -/
lemma real_deriv_bound_nodes_N (f : ℝ → ℝ) {k : ℕ} {η M B : ℝ} (hη0 : 0 < η)
    (hcd : ContDiff ℝ (k + 1 : ℕ) f)
    (u : ℕ → ℝ)
    (hsep : ∀ i j : ℕ, i < j → j ≤ k → η ≤ u j - u i)
    (hspan : u k - u 0 ≤ 7 * η)
    (hval : ∀ i : ℕ, i ≤ k → |f (u i)| ≤ M)
    (hder : ∀ x : ℝ, |iteratedDeriv (k + 1) f x| ≤ B) :
    |iteratedDeriv k f (u 0)| ≤ ((k + 1).factorial : ℝ) * M / η ^ k + 7 * η * B := by
  let v : Fin (k + 1) → ℝ := fun i => u i.1
  let s : Finset (Fin (k + 1)) := Finset.univ
  let P : ℝ[X] := Lagrange.interpolate s v (fun i => f (v i))
  let q : ℝ → ℝ := fun x => P.eval x
  have hM0 : 0 ≤ M := by
    have hz : |f (u 0)| ≤ M := hval 0 (by omega)
    exact le_trans (abs_nonneg _) hz
  have hsepFin : ∀ i j : Fin (k + 1), i ≠ j → η ≤ |v i - v j| := by
    intro i j hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hs : η ≤ u j.1 - u i.1 := hsep i.1 j.1 (by omega) (by omega)
      rw [abs_sub_comm]
      have hnonneg : 0 ≤ u j.1 - u i.1 := by linarith
      rw [abs_of_nonneg hnonneg]
      exact hs
    · have hs : η ≤ u i.1 - u j.1 := hsep j.1 i.1 (by omega) (by omega)
      have hnonneg : 0 ≤ u i.1 - u j.1 := by linarith
      rw [abs_of_nonneg hnonneg]
      exact hs
  have hvalFin : ∀ i : Fin (k + 1), |f (v i)| ≤ M := by
    intro i
    dsimp [v]
    exact hval i.1 (by omega)
  have hinj : Set.InjOn v (s : Set (Fin (k + 1))) := by
    intro i hi j hj hvij
    by_contra hne
    have hz : η ≤ (0 : ℝ) := by
      simpa [hvij] using hsepFin i j hne
    nlinarith
  have hqinterp : ∀ i : Fin (k + 1), q (v i) = f (v i) := by
    intro i
    simp [q, P, v]
    exact Lagrange.eval_interpolate_at_node (fun i => f (v i)) hinj (Finset.mem_univ i)
  let e : ℝ → ℝ := fun x => f x - q x
  have he0 : ∀ m : ℕ, m ≤ k → e (u m) = 0 := by
    intro m hm
    have hq : q (u m) = f (u m) := by
      have := hqinterp ⟨m, by omega⟩
      simpa [v] using this
    simp [e, hq]
  have hcdq : ContDiff ℝ (k + 1 : ℕ) q := by
    simpa [q] using (contDiff_polyEvalR P (n := (k + 1 : ℕ∞)))
  have hcde : ContDiff ℝ (k + 1 : ℕ) e := by
    exact hcd.sub hcdq
  have umono : ∀ m : ℕ, m < k → u m < u (m + 1) := by
    intro m hm
    have hs := hsep m (m + 1) (by omega) (by omega)
    linarith
  rcases exists_iteratedDeriv_eq_zero_of_zeros_Nat k e hcde u umono he0 with ⟨ξ, hξ1, hξ2, hξ3⟩
  have hξ_bounds : u 0 ≤ ξ ∧ ξ ≤ u k := ⟨hξ1, hξ2⟩
  have hcdk : ContDiff ℝ (k : ℕ) f := hcd.of_le (by exact_mod_cast (Nat.le_succ k))
  have hcdqk : ContDiff ℝ (k : ℕ) q := hcdq.of_le (by exact_mod_cast (Nat.le_succ k))
  have hsplit : iteratedDeriv k f ξ = iteratedDeriv k q ξ := by
    have hsubv := iteratedDeriv_sub (n := k) (f := f) (g := q) (x := ξ)
      (hf := hcdk.contDiffAt) (hg := hcdqk.contDiffAt)
    have hz : iteratedDeriv k e ξ = 0 := hξ3
    have heqfun : e = f - q := rfl
    have hmain : iteratedDeriv k f ξ - iteratedDeriv k q ξ = 0 := by
      have hz' : iteratedDeriv k (f - q) ξ = 0 := by
        simpa [heqfun] using hz
      rw [← hsubv]
      exact hz'
    linarith
  have hqk : |iteratedDeriv k q ξ| ≤ ((k + 1).factorial : ℝ) * M / η ^ k := by
    calc
      |iteratedDeriv k q ξ| = |iteratedDeriv k (fun x : ℝ => P.eval x) ξ| := by simp [q]
      _ = |(Polynomial.derivative^[k] P).eval ξ| := by rw [iteratedDeriv_polyEvalR]
      _ ≤ ((k + 1).factorial : ℝ) * M / η ^ k := by
          exact interp_deriv_norm_le hη0 v f hsepFin hvalFin ξ
  have hB0 : 0 ≤ B := by
    have hz := hder ξ
    exact le_trans (abs_nonneg _) hz
  have gdiff : ∀ x : ℝ, DifferentiableAt ℝ (iteratedDeriv k f) x := by
    intro x
    exact (hcd.differentiable_iteratedDeriv' (m := k)).differentiableAt
  have gbnd : ∀ x : ℝ, ‖deriv (iteratedDeriv k f) x‖ ≤ B := by
    intro x
    have hdv : deriv (iteratedDeriv k f) x = iteratedDeriv (k + 1) f x := by
      rw [← iteratedDeriv_succ]
    rw [hdv]
    simpa using hder x
  have hlip := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ) (G := ℝ) (f := iteratedDeriv k f)
      (s := (Set.univ : Set ℝ)) (x := u 0) (y := ξ) (C := B)
      (hf := fun x hx => gdiff x) (bound := fun x hx => gbnd x)
      (hs := convex_univ) (xs := Set.mem_univ _) (ys := Set.mem_univ _)
  have hspanξ : |ξ - u 0| ≤ 7 * η := by
    have h1 : u 0 ≤ ξ := hξ_bounds.1
    have h4 : |ξ - u 0| = ξ - u 0 := abs_of_nonneg (sub_nonneg.mpr h1)
    rw [h4]
    nlinarith [hspan, hξ_bounds.2]
  calc
    |iteratedDeriv k f (u 0)|
        ≤ |iteratedDeriv k f (u 0) - iteratedDeriv k f ξ| + |iteratedDeriv k f ξ| := by
            simpa using (abs_add_le (iteratedDeriv k f (u 0) - iteratedDeriv k f ξ) (iteratedDeriv k f ξ))
    _ ≤ B * |ξ - u 0| + |iteratedDeriv k f ξ| := by
        have hsubn : |iteratedDeriv k f (u 0) - iteratedDeriv k f ξ| = |iteratedDeriv k f ξ - iteratedDeriv k f (u 0)| := abs_sub_comm _ _
        rw [hsubn]
        have hlip' : |iteratedDeriv k f ξ - iteratedDeriv k f (u 0)| ≤ B * |ξ - u 0| := by
          simpa using hlip
        nlinarith [hlip']
    _ ≤ B * (7 * η) + ((k + 1).factorial : ℝ) * M / η ^ k := by
        have h1 := mul_le_mul_of_nonneg_left hspanξ hB0
        have hqk' : |iteratedDeriv k f ξ| ≤ ((k + 1).factorial : ℝ) * M / η ^ k := by
          rw [hsplit]
          exact hqk
        nlinarith [hqk', h1]
    _ = ((k + 1).factorial : ℝ) * M / η ^ k + 7 * η * B := by ring

/-- If `0 < η < 2^-11` then `η^3 / 2^7 < 1/4`. -/
lemma eta_cube_lt_quarter {η : ℝ} (hη0 : 0 < η) (hη : η < (1 : ℝ) / 2 ^ 11) :
    η ^ 3 / 2 ^ 7 < 1 / 4 := by
  have hη3lt : η ^ 3 < (1 / 2 ^ 11) ^ 3 := by
    exact pow_lt_pow_left₀ hη (le_of_lt hη0) (by norm_num : (3 : ℕ) ≠ 0)
  have hdiv : η ^ 3 / 2 ^ 7 < (1 / 2 ^ 11) ^ 3 / 2 ^ 7 := by
    exact div_lt_div_of_pos_right hη3lt (by norm_num)
  have hfin : (1 / 2 ^ 11) ^ 3 / 2 ^ 7 < (1 / 4 : ℝ) := by norm_num
  exact lt_trans hdiv hfin

/-- Every 7η-length interval contains a good η-length subinterval. -/
lemma intervals_nice (t : ℕ) {η a : ℝ} (hη0 : 0 < η) (hη : η < (1 : ℝ) / 2 ^ 11) :
    ∃ j : Fin 7, ∀ x : ℝ,
      x ∈ Set.Icc (a + (j : ℕ) * η) (a + ((j : ℕ) + 1) * η) →
        (η ^ 3 / 2 ^ 7 : ℝ) ≤ |(H t x).re| := by
  by_contra hnot
  classical
  have hbad : ∀ j : Fin 7, ∃ x : ℝ,
      x ∈ Set.Icc (a + (j : ℕ) * η) (a + ((j : ℕ) + 1) * η) ∧
        |(H t x).re| < η ^ 3 / 2 ^ 7 := by
    intro j
    have hnotj : ¬ (∀ x : ℝ, x ∈ Set.Icc (a + (j : ℕ) * η) (a + ((j : ℕ) + 1) * η) →
        (η ^ 3 / 2 ^ 7 : ℝ) ≤ |(H t x).re|) := by
      intro hj
      exact hnot ⟨j, hj⟩
    push_neg at hnotj
    exact hnotj
  let x : Fin 7 → ℝ := fun j => Classical.choose (hbad j)
  have hxI : ∀ j : Fin 7, x j ∈ Set.Icc (a + (j : ℕ) * η) (a + ((j : ℕ) + 1) * η) := by
    intro j
    exact (Classical.choose_spec (hbad j)).1
  have hxsmall : ∀ j : Fin 7, |(H t (x j)).re| < η ^ 3 / 2 ^ 7 := by
    intro j
    exact (Classical.choose_spec (hbad j)).2
  let x0 : ℝ := x 0
  let f : ℝ → ℝ := fun y => (H t y).re
  have hlt_quarter : η ^ 3 / 2 ^ 7 < 1 / 4 := eta_cube_lt_quarter hη0 hη
  -- generic bound on f^(k)(x0) for 1 ≤ k ≤ 3
  have hfderiv (k : ℕ) (hk1 : 1 ≤ k) (hk3 : k ≤ 3) :
      |iteratedDeriv k f x0| ≤
        ((k + 1).factorial : ℝ) * (η ^ 3 / 2 ^ 7) / η ^ k + 7 * η * ((2 : ℝ) ^ (k + 1) + 2) := by
    let u : ℕ → ℝ := fun m => if hm : 2 * m < 7 then x ⟨2 * m, hm⟩ else x 0
    have u_eq_m : ∀ (m : ℕ) (hm : m ≤ k), u m = x ⟨2 * m, by omega⟩ := by
      intro m hm
      have h2m : 2 * m < 7 := by omega
      dsimp [u]
      rw [dif_pos h2m]
    have hval_u : ∀ m : ℕ, m ≤ k → |f (u m)| ≤ η ^ 3 / 2 ^ 7 := by
      intro m hm
      rw [u_eq_m m hm]
      exact le_of_lt (hxsmall ⟨2 * m, by omega⟩)
    have hsep_u : ∀ i j : ℕ, i < j → j ≤ k → η ≤ u j - u i := by
      intro i j hij hjk
      have h2i : 2 * i < 7 := by omega
      have h2j : 2 * j < 7 := by omega
      have hu_i : u i = x ⟨2 * i, h2i⟩ := by
        dsimp [u]
        rw [dif_pos h2i]
      have hu_j : u j = x ⟨2 * j, h2j⟩ := by
        dsimp [u]
        rw [dif_pos h2j]
      rw [hu_i, hu_j]
      have hxiR : x ⟨2 * i, h2i⟩ ≤ a + (((2 * i : ℕ) + 1) * η) := (hxI ⟨2 * i, h2i⟩).2
      have hxjL : a + ((2 * j : ℕ) * η) ≤ x ⟨2 * j, h2j⟩ := (hxI ⟨2 * j, h2j⟩).1
      have hci : ((2 * i : ℕ) : ℝ) = 2 * (i : ℝ) := by
        norm_num [Nat.cast_mul]
      have hcj : ((2 * j : ℕ) : ℝ) = 2 * (j : ℝ) := by
        norm_num [Nat.cast_mul]
      rw [hci] at hxiR
      rw [hcj] at hxjL
      have hn : (2 : ℝ) * (i : ℝ) + 2 ≤ (2 : ℝ) * (j : ℝ) := by
        have hcast : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hij)
        nlinarith
      have hdiff : η ≤ (a + 2 * (j : ℝ) * η) - (a + (2 * (i : ℝ) + 1) * η) := by
        have hpos : 0 ≤ (2 * (j : ℝ) - (2 * (i : ℝ) + 1)) - 1 := by nlinarith
        nlinarith
      nlinarith [hdiff]
    have hspan_u : u k - u 0 ≤ 7 * η := by
      have h2k : 2 * k < 7 := by omega
      have hu_k : u k = x ⟨2 * k, h2k⟩ := by
        dsimp [u]
        rw [dif_pos h2k]
      have h2zero : 2 * 0 < 7 := by norm_num
      have hu_0 : u 0 = x ⟨2 * 0, h2zero⟩ := by
        change (if h : 2 * 0 < 7 then x ⟨2 * 0, h⟩ else x 0) = x ⟨2 * 0, h2zero⟩
        rw [dif_pos h2zero]
      rw [hu_k, hu_0]
      have hxkR : x ⟨2 * k, h2k⟩ ≤ a + (((2 * k : ℕ) + 1) * η) := (hxI ⟨2 * k, h2k⟩).2
      have hx0L : a + ((0 : ℕ) * η) ≤ x ⟨0, by omega⟩ := (hxI ⟨0, by omega⟩).1
      have hck : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by
        norm_num [Nat.cast_mul]
      rw [hck] at hxkR
      have hk7 : 2 * (k : ℝ) + 1 ≤ 7 := by
        have hk : (2 * k : ℕ) + 1 ≤ 7 := by omega
        exact_mod_cast hk
      have hx0L' : a ≤ x ⟨0, by omega⟩ := by
        have : ((0 : ℕ) : ℝ) * η = 0 := by simp
        nlinarith [hx0L]
      nlinarith [hxkR, hx0L', hk7]
    have hder_f : ∀ z : ℝ, |iteratedDeriv (k + 1) f z| ≤ (2 : ℝ) ^ (k + 1) + 2 := by
      intro z
      exact reH_iter_deriv_abs_le t (m := k + 1) (by omega) (by omega) z
    have hmain := real_deriv_bound_nodes_N f (k := k) (η := η)
        (M := η ^ 3 / 2 ^ 7) (B := (2 : ℝ) ^ (k + 1) + 2)
        (hη0 := hη0) (hcd := contDiff_reH (n := (k + 1 : ℕ)) t)
        u hsep_u hspan_u hval_u hder_f
    have hu0 : u 0 = x0 := by
      dsimp [u, x0]
    rwa [hu0] at hmain
  -- the four cases for k
  have hsmall : ∀ k : ℕ, k ≤ 3 → |(iteratedDeriv k (H t) x0).re| < 1 / 4 := by
    intro k hk3
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
    · -- k = 0: |Re H(x0)| < η^3/2^7 < 1/4
      have hz := hxsmall 0
      have hz' : |(iteratedDeriv 0 (H t) x0).re| < η ^ 3 / 2 ^ 7 := by
        simpa [x0, iteratedDeriv_zero] using hz
      exact lt_trans hz' hlt_quarter
    · -- k = 1
      have hb := hfderiv 1 (by norm_num) (by norm_num)
      have hbnd1 : |iteratedDeriv 1 f x0| < 1 / 4 := by
        have hb' : |iteratedDeriv 1 f x0| ≤ η ^ 2 / 2 ^ 6 + 42 * η := by
          have hsimp : (↑(1 + 1).factorial : ℝ) * (η ^ 3 / 2 ^ 7) / η ^ 1 +
              7 * η * ((2 : ℝ) ^ (1 + 1) + 2) = η ^ 2 / 2 ^ 6 + 42 * η := by
            norm_num
            field_simp [hη0.ne']
            ring
          nlinarith [hb, hsimp]
        have hlt : η ^ 2 / 2 ^ 6 + 42 * η < 1 / 4 := by
          have hηle1 : η ≤ 1 := by nlinarith [hη, (by norm_num : (1 : ℝ) / 2 ^ 11 ≤ 1)]
          have hsq : η ^ 2 ≤ η := by
            simpa [pow_two] using (mul_le_mul_of_nonneg_left hηle1 hη0.le)
          have hnum : ((1 : ℝ) / 2 ^ 6 + 42) * ((1 : ℝ) / 2 ^ 11) < (1 / 4 : ℝ) := by norm_num
          nlinarith [hsq, hη, hnum]
        exact lt_of_le_of_lt hb' hlt
      rw [← iteratedDeriv_reH t 1 x0]
      simpa [f] using hbnd1
    · -- k = 2
      have hb := hfderiv 2 (by norm_num) (by norm_num)
      have hbnd2 : |iteratedDeriv 2 f x0| < 1 / 4 := by
        have hb' : |iteratedDeriv 2 f x0| ≤ (6 / 2 ^ 7 + 70) * η := by
          have hsimp : (↑(2 + 1).factorial : ℝ) * (η ^ 3 / 2 ^ 7) / η ^ 2 +
              7 * η * ((2 : ℝ) ^ (2 + 1) + 2) = (6 / 2 ^ 7 + 70) * η := by
            norm_num
            field_simp [hη0.ne']
            ring
          nlinarith [hb, hsimp]
        have hlt : ((6 : ℝ) / 2 ^ 7 + 70) * η < 1 / 4 := by
          have hnum : ((6 : ℝ) / 2 ^ 7 + 70) * ((1 : ℝ) / 2 ^ 11) < (1 / 4 : ℝ) := by norm_num
          nlinarith [hη, hnum]
        exact lt_of_le_of_lt hb' hlt
      rw [← iteratedDeriv_reH t 2 x0]
      simpa [f] using hbnd2
    · -- k = 3
      have hb := hfderiv 3 (by norm_num) (by norm_num)
      have hbnd3 : |iteratedDeriv 3 f x0| < 1 / 4 := by
        have hb' : |iteratedDeriv 3 f x0| ≤ 24 / 2 ^ 7 + 126 * η := by
          have hsimp : (↑(3 + 1).factorial : ℝ) * (η ^ 3 / 2 ^ 7) / η ^ 3 +
              7 * η * ((2 : ℝ) ^ (3 + 1) + 2) = 24 / 2 ^ 7 + 126 * η := by
            norm_num
            field_simp [hη0.ne']
            ring
          nlinarith [hb, hsimp]
        have hlt : (24 / 2 ^ 7 : ℝ) + 126 * η < 1 / 4 := by
          have hnum : ((24 : ℝ) / 2 ^ 7) + 126 * ((1 : ℝ) / 2 ^ 11) < (1 / 4 : ℝ) := by norm_num
          nlinarith [hη, hnum]
        exact lt_of_le_of_lt hb' hlt
      rw [← iteratedDeriv_reH t 3 x0]
      simpa [f] using hbnd3
  rcases H_deriv_lbound t x0 with ⟨k, hk3, hbnd⟩
  have hlt := hsmall k hk3
  exact (not_le_of_gt hlt) hbnd

end Sec3H
end Submission
