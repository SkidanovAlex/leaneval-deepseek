import Mathlib
import Submission.Work.TMC14Core.Assembly
import Submission.Work.TMC14Core.discEven
import Submission.Work.TMC14Core.discRootsReal
import Submission.Work.TMC14Core.discSecondDerivQuant

open Polynomial

namespace Work.TMC14Core

/-!
# TMC14Core: lower bound on the second derivative of the discriminant at `0`

The discriminant `disc p q lam` is a monic, even polynomial of degree `q = 2(m+1)`
all of whose roots are real (`discEven`, `discRootsReal`).  Writing its roots as
`±y_i` (`1 ≤ i ≤ m+1`), one has `disc(z) = ∏_i (z² - y_i²) = γ(z²)` with
`γ(X) = ∏_i (X - y_i²)`, so
`‖disc''(0)‖ = 2·|γ'(0)| = 2·(∏ y_i²)·Σ 1/y_i²`.
`real_root_deriv_bound` gives `(m+1) ≤ |γ'(0)|` as soon as `‖disc(0)‖ ≥ 1`, whence
`‖disc''(0)‖ ≥ 2(m+1) ≥ 2`.  This is the strengthened form of
`even_monic_real_roots_second_deriv`, which only records the bound `1`.
-/

/-- Strengthened second-derivative bound: for a monic even polynomial of degree
`2n` (`n ≥ 1`) with real roots and `‖f(0)‖ ≥ 1`, the second derivative at `0` has
norm at least `2`.  (The weaker bound `1` is `even_monic_real_roots_second_deriv`;
the extra factor comes from `2·A.card ≥ 2·1`.) -/
theorem evenMonicRealRootsSecondDerivTwo (f : Polynomial ℂ) (n : ℕ) (hn : 1 ≤ n)
    (hdeg : f.natDegree = 2 * n) (hmonic : f.Monic)
    (heven : ∀ z, f.eval (-z) = f.eval z) (hreal : ∀ z, f.eval z = 0 → z.im = 0)
    (h0 : f.eval 0 ≠ 0) (hP : 1 ≤ ‖f.eval 0‖) :
    (2:ℝ) ≤ ‖(Polynomial.derivative (Polynomial.derivative f)).eval 0‖ := by
  have hfne : f ≠ 0 := hmonic.ne_zero
  have hRcard : f.roots.card = 2 * n := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hdeg]
  have hfprod : f = (f.roots.map (fun r => Polynomial.X - Polynomial.C r)).prod :=
    (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmonic
      IsAlgClosed.card_roots_eq_natDegree).symm
  have hrealR : ∀ r ∈ f.roots, r.im = 0 := fun r hr =>
    hreal r (by simpa [Polynomial.IsRoot.def] using Polynomial.isRoot_of_mem_roots hr)
  have hne0R : ∀ r ∈ f.roots, r ≠ 0 := by
    intro r hr hrz
    have h1 : f.eval r = 0 := by
      simpa [Polynomial.IsRoot.def] using Polynomial.isRoot_of_mem_roots hr
    rw [hrz] at h1
    exact h0 h1
  have heven_poly : f.comp (-Polynomial.X) = f := by
    apply Polynomial.funext
    intro z
    rw [Polynomial.eval_comp]
    simpa using heven z
  have hcomp : f.comp (-Polynomial.X)
      = ((f.roots.map Neg.neg).map (fun r => Polynomial.X - Polynomial.C r)).prod := by
    conv_lhs => rw [hfprod, comp_multiset_prod, Multiset.map_map]
    rw [show (f.roots.map ((fun p => p.comp (-Polynomial.X)) ∘
            (fun r => Polynomial.X - Polynomial.C r)))
          = (f.roots.map (fun r => Polynomial.X - Polynomial.C (-r))).map Neg.neg from by
        rw [Multiset.map_map]
        apply Multiset.map_congr rfl
        intro r hr
        simp only [Function.comp_apply, Polynomial.sub_comp, Polynomial.X_comp,
          Polynomial.C_comp, Polynomial.C_neg]
        ring]
    rw [show ((f.roots.map Neg.neg).map (fun r => Polynomial.X - Polynomial.C r))
          = f.roots.map (fun r => Polynomial.X - Polynomial.C (-r)) from by
        rw [Multiset.map_map]; rfl]
    rw [Multiset.prod_map_neg]
    rw [show (f.roots.map (fun r => Polynomial.X - Polynomial.C (-r))).card = 2 * n from by
        rw [Multiset.card_map, hRcard], pow_mul]
    simp
  have hmul : ((f.roots.map Neg.neg).map (fun r => Polynomial.X - Polynomial.C r)).prod
      = (f.roots.map (fun r => Polynomial.X - Polynomial.C r)).prod := by
    conv_lhs => rw [← hcomp, heven_poly, hfprod]
  have h2 : ((f.roots.map Neg.neg).map (fun r => Polynomial.X - Polynomial.C r)).prod.roots
      = f.roots.map Neg.neg := Polynomial.roots_multiset_prod_X_sub_C _
  have h3 : (f.roots.map (fun r => Polynomial.X - Polynomial.C r)).prod.roots = f.roots :=
    Polynomial.roots_multiset_prod_X_sub_C _
  have hsymm : f.roots.map Neg.neg = f.roots := by rw [← h2, hmul, h3]
  set Rpos : Multiset ℂ := f.roots.filter (fun r => 0 < r.re) with hRposdef
  have hsplit : f.roots = Rpos + Rpos.map Neg.neg := by
    have hre : ∀ r ∈ f.roots, r.re ≠ 0 := by
      intro r hr h
      exact hne0R r hr (Complex.ext h (hrealR r hr))
    exact multiset_split_pos (f.roots) hsymm hre
  set A : Multiset ℝ := Rpos.map (fun r => r.re * r.re) with hAdef
  have hAcard : A.card = n := by
    have h1 : (Rpos + Rpos.map Neg.neg).card = Rpos.card + Rpos.card := by
      rw [Multiset.card_add, Multiset.card_map]
    have h2 : (Rpos + Rpos.map Neg.neg).card = 2 * n := by rw [← hsplit]; exact hRcard
    have h3 : A.card = Rpos.card := Multiset.card_map _ _
    omega
  have hApos : ∀ a ∈ A, 0 < a := by
    intro a ha
    rw [hAdef, Multiset.mem_map] at ha
    obtain ⟨r, hr, rfl⟩ := ha
    rw [hRposdef, Multiset.mem_filter] at hr
    exact mul_pos hr.2 hr.2
  set γ : ℝ[X] := (A.map (fun a => Polynomial.X - Polynomial.C a)).prod with hγdef
  set G : ℂ[X] := (γ.comp (Polynomial.X ^ 2)).map Complex.ofRealHom with hGdef
  have hG1 : G = (A.map (fun a => (Polynomial.X^2 - Polynomial.C a).map Complex.ofRealHom)).prod := by
    rw [hGdef, hγdef, comp_sq_prod_X_sub_C, Polynomial.map_multiset_prod, Multiset.map_map]
    rfl
  have hf1 : f = (Rpos.map (fun r => Polynomial.X^2 - Polynomial.C (r * r))).prod := by
    rw [hfprod, hsplit, Multiset.map_add, Multiset.prod_add]
    rw [show ((Rpos.map Neg.neg).map (fun r => Polynomial.X - Polynomial.C r))
          = Rpos.map (fun r => Polynomial.X - Polynomial.C (-r)) from by
        rw [Multiset.map_map]; rfl]
    rw [← Multiset.prod_map_mul]
    congr 1
    apply Multiset.map_congr rfl
    intro r hr
    exact X_sub_C_mul_X_sub_C_neg r
  have hG2 : G = (Rpos.map (fun r =>
      (Polynomial.X^2 - Polynomial.C (r.re * r.re)).map Complex.ofRealHom)).prod := by
    rw [hG1, hAdef, Multiset.map_map]
    rfl
  have hfg : f = G := by
    rw [hf1, hG2]
    congr 1
    apply Multiset.map_congr rfl
    intro r hr
    rw [hRposdef, Multiset.mem_filter] at hr
    have hrr : r * r = ((r.re * r.re : ℝ) : ℂ) := by
      have hrr' : r = ((r.re : ℝ) : ℂ) := Complex.ext rfl (hrealR r hr.1)
      rw [hrr', Complex.ofReal_re]; push_cast; ring
    rw [hrr]
    simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_pow, Polynomial.map_C,
      Complex.ofRealHom_eq_coe]
  have hγeval : G.eval 0 = ((γ.eval 0 : ℝ) : ℂ) := by
    rw [hGdef, eval_map_ofReal, Polynomial.eval_comp]
    simp
  have hAprod : 1 ≤ A.prod := by
    have h1 : |γ.eval 0| = A.prod := by
      rw [hγdef, key1 A, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
        abs_of_pos (Multiset.prod_pos hApos)]
    have h2 : ‖f.eval 0‖ = |γ.eval 0| := by rw [hfg, hγeval]; exact RCLike.norm_ofReal _
    rw [← h1, ← h2]; exact hP
  have hbound := real_root_deriv_bound A hApos (by rw [hAcard]; exact hn) hAprod
  have hderiv2 : (Polynomial.derivative (Polynomial.derivative f)).eval 0
      = ((2 * (Polynomial.derivative γ).eval 0 : ℝ) : ℂ) := by
    rw [hfg, hGdef]
    simp only [Polynomial.derivative_map]
    rw [eval_map_ofReal, second_deriv_comp_sq]
  rw [hderiv2]
  have hnorm : ‖(((2 * (Polynomial.derivative γ).eval 0) : ℝ) : ℂ)‖
      = 2 * |(Polynomial.derivative γ).eval 0| := by
    rw [show ‖(((2 * (Polynomial.derivative γ).eval 0) : ℝ) : ℂ)‖
          = |(2 * (Polynomial.derivative γ).eval 0)| from RCLike.norm_ofReal _,
      abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  rw [hnorm]
  have hA1 : (1:ℝ) ≤ (A.card : ℝ) := by rw [hAcard]; exact_mod_cast hn
  have hnn : (0:ℝ) ≤ |(Polynomial.derivative γ).eval 0| := abs_nonneg _
  linarith [hbound, hA1]

/-! ## The requested bound for the rational discriminant -/

theorem discSecondDerivLower (p : ℤ) (q m : ℕ) (hm : q = 2 * m + 2) (hpq : Nat.Coprime p.natAbs q)
    (lam : ℝ) (hlam : 0 < lam) (hVal : ‖(disc p q lam).eval (0 : ℂ)‖ = 2 + 2 * lam ^ q) :
    (2 : ℝ) ≤ ‖(Polynomial.derivative (Polynomial.derivative (disc p q lam))).eval 0‖ := by
  have hq : 1 ≤ q := by omega
  have h0 : (disc p q lam).eval 0 ≠ 0 := by
    intro h
    rw [h, norm_zero] at hVal
    have : (0:ℝ) < 2 + 2 * lam ^ q := by positivity
    linarith
  have hP : 1 ≤ ‖(disc p q lam).eval 0‖ := by
    rw [hVal]
    have := pow_pos hlam q
    linarith
  have hmonic : (disc p q lam).Monic := by
    rw [disc]
    refine Polynomial.Monic.add_of_left (Matrix.charpoly_monic _) ?_
    rw [Polynomial.degree_C (by norm_num : (2:ℂ) ≠ 0), Matrix.charpoly_degree_eq_dim]
    simp
    omega
  have hdeg : (disc p q lam).natDegree = 2 * (m + 1) := by
    have h1 : (disc p q lam).natDegree = q := by
      rw [disc]
      rw [Polynomial.natDegree_add_eq_left_of_degree_lt]
      · rw [Matrix.charpoly_natDegree_eq_dim]; simp
      · rw [Polynomial.degree_C (by norm_num : (2:ℂ) ≠ 0), Matrix.charpoly_degree_eq_dim]
        simp
        omega
    rw [h1, hm]; ring
  have hreal : ∀ z : ℂ, (disc p q lam).eval z = 0 → z.im = 0 := by
    intro z hz
    obtain ⟨x, hx⟩ := discRootsReal p q lam hpq hq hlam 0 (by rw [abs_zero]; positivity) hz
    rw [hx]; simp
  have heven := discEven p q m hm hpq lam
  exact evenMonicRealRootsSecondDerivTwo (disc p q lam) (m + 1) (by omega) hdeg hmonic
    heven hreal h0 hP

end Work.TMC14Core
