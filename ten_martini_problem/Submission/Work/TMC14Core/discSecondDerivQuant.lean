import Mathlib
import Submission.Work.TMC14Core.Assembly
import Submission.Work.TMC14Core.discEven
import Submission.Work.TMC14Core.discRootsReal
import Submission.Work.TMC14Core.dsdqDiscZeroAbs

open Polynomial

namespace Work.TMC14Core

/-! ## 1. AM-GM for a multiset of positive reals -/

lemma amgm_multiset (A : Multiset ℝ) (hA : ∀ a ∈ A, 0 < a) (hn : 1 ≤ A.card) :
    (A.card : ℝ) * A.prod ^ ((A.card : ℝ)⁻¹) ≤ A.sum := by
  have hmem : ∀ b ∈ A.toFinset, b ∈ A := fun b hb => Multiset.mem_toFinset.mp hb
  have hw : ∀ b ∈ A.toFinset, (0:ℝ) ≤ (A.count b : ℝ) := by
    intro b _; exact_mod_cast Nat.zero_le _
  have hcardsum : ∑ b ∈ A.toFinset, (Multiset.count b A : ℝ) = (A.card : ℝ) := by
    have h := Multiset.toFinset_sum_count_eq A
    exact_mod_cast h
  have hcardpos : (0:ℝ) < (A.card : ℝ) := by exact_mod_cast (by omega : 0 < A.card)
  have hw' : 0 < ∑ b ∈ A.toFinset, (A.count b : ℝ) := by rw [hcardsum]; exact hcardpos
  have h := Real.geom_mean_le_arith_mean A.toFinset (fun b => (A.count b : ℝ)) (fun b => b)
      hw hw' (fun b hb => le_of_lt (hA b (hmem b hb)))
  rw [hcardsum] at h
  have hAprod : (∏ b ∈ A.toFinset, b ^ (Multiset.count b A : ℝ)) = A.prod := by
    rw [Finset.prod_multiset_count A]
    refine Finset.prod_congr rfl (fun b hb => ?_)
    rw [Real.rpow_natCast]
  have hAsum : (∑ b ∈ A.toFinset, (Multiset.count b A : ℝ) * b) = A.sum := by
    rw [Finset.sum_multiset_count A]
    refine Finset.sum_congr rfl (fun b hb => ?_)
    rw [nsmul_eq_mul]
  rw [hAprod, hAsum] at h
  rw [le_div_iff₀ hcardpos] at h
  calc (A.card : ℝ) * A.prod ^ ((A.card:ℝ))⁻¹
      = A.prod ^ ((A.card:ℝ))⁻¹ * (A.card : ℝ) := mul_comm _ _
    _ ≤ A.sum := h

/-! ## 2. Evaluation of `∏ (X - C a)` and of its derivative at `0` -/

lemma key1 (A : Multiset ℝ) :
    (Polynomial.eval 0 ((A.map (fun a => Polynomial.X - Polynomial.C a)).prod))
      = (-1) ^ A.card * A.prod := by
  rw [Polynomial.eval_multiset_prod, Multiset.map_map]
  simp only [Function.comp_apply, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  rw [show (fun x : ℝ => 0 - x) = Neg.neg from by funext x; simp,
    Multiset.prod_map_neg]

lemma key2 (A : Multiset ℝ) (hA : ∀ a ∈ A, 0 < a) :
    (Polynomial.eval 0 (Polynomial.derivative ((A.map (fun a => Polynomial.X - Polynomial.C a)).prod)))
      = (-1) ^ (A.card - 1) * A.prod * (A.map (fun a => a⁻¹)).sum := by
  rw [Polynomial.derivative_prod]
  simp only [Polynomial.derivative_X_sub_C, mul_one]
  have hsum0 : (Polynomial.eval 0)
        ((A.map (fun a => (Multiset.map (fun a' => Polynomial.X - Polynomial.C a') (A.erase a)).prod)).sum)
      = (A.map (fun a => Polynomial.eval 0
          ((Multiset.map (fun a' => Polynomial.X - Polynomial.C a') (A.erase a)).prod))).sum := by
    change (Polynomial.evalRingHom (0:ℝ))
        ((A.map (fun a => (Multiset.map (fun a' => Polynomial.X - Polynomial.C a') (A.erase a)).prod)).sum) = _
    rw [map_multiset_sum, Multiset.map_map]; rfl
  rw [hsum0]
  rw [show (A.map (fun a => Polynomial.eval 0
        ((Multiset.map (fun a' => Polynomial.X - Polynomial.C a') (A.erase a)).prod))).sum
      = (A.map (fun a => (-1) ^ (A.card - 1) * (a⁻¹ * A.prod))).sum from by
    congr 1
    apply Multiset.map_congr rfl
    intro a ha
    rw [key1 (A.erase a)]
    have hcard : (A.erase a).card = A.card - 1 := by
      have := Multiset.card_erase_add_one ha; omega
    rw [hcard]
    have hprod : (A.erase a).prod = a⁻¹ * A.prod := by
      have h := Multiset.prod_erase ha
      rw [← h, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt (hA a ha)), one_mul]
    rw [hprod]]
  rw [Multiset.sum_map_mul_left, Multiset.sum_map_mul_right]
  ring

/-! ## 3. The derivative bound for a monic polynomial with positive real roots -/

theorem real_root_deriv_bound (A : Multiset ℝ) (hA : ∀ a ∈ A, 0 < a)
    (hn : 1 ≤ A.card) (hP : 1 ≤ A.prod) :
    (A.card : ℝ)
      ≤ |(Polynomial.derivative ((A.map (fun a => Polynomial.X - Polynomial.C a)).prod)).eval 0| := by
  have hPpos : 0 < A.prod := Multiset.prod_pos hA
  have hPne : A.prod ≠ 0 := ne_of_gt hPpos
  -- the product of the inverses is the inverse of the product
  have hQP : (A.map (fun a => a⁻¹)).prod = (A.prod)⁻¹ := by
    have hmul : A.prod * (A.map (fun a => a⁻¹)).prod = 1 := by
      have h2 : (A.map (fun a => a * a⁻¹)).prod = A.prod * (A.map (fun a => a⁻¹)).prod := by
        rw [Multiset.prod_map_mul]
        rw [show (Multiset.map (fun a : ℝ => a) A).prod = A.prod from by
          rw [show (fun a : ℝ => a) = id from rfl, Multiset.map_id]]
      have h3 : (A.map (fun a => a * a⁻¹)).prod = 1 := by
        rw [Multiset.map_congr rfl (fun a ha => mul_inv_cancel₀ (ne_of_gt (hA a ha)))]
        rw [show (fun _ => (1:ℝ)) = Function.const ℝ 1 from rfl, Multiset.map_const,
          Multiset.prod_replicate, one_pow]
      rw [← h2, h3]
    calc (A.map (fun a => a⁻¹)).prod
        = (A.map (fun a => a⁻¹)).prod * (A.prod * (A.prod)⁻¹) := by
          rw [mul_inv_cancel₀ hPne, mul_one]
      _ = ((A.map (fun a => a⁻¹)).prod * A.prod) * (A.prod)⁻¹ := by rw [mul_assoc]
      _ = 1 * (A.prod)⁻¹ := by rw [mul_comm (A.map (fun a => a⁻¹)).prod A.prod, hmul]
      _ = (A.prod)⁻¹ := one_mul _
  have hA'prod : (A.map (fun a => A.prod * a⁻¹)).prod = A.prod ^ (A.card - 1) := by
    rw [Multiset.prod_map_mul]
    rw [show (Multiset.map (fun _ => A.prod) A).prod = A.prod ^ A.card from by
      rw [show (fun _ : ℝ => A.prod) = Function.const ℝ A.prod from rfl, Multiset.map_const,
        Multiset.prod_replicate]]
    rw [hQP]
    rw [show (A.prod)⁻¹ = ((A.prod)^1)⁻¹ from by rw [pow_one], ← pow_sub₀ A.prod hPne hn]
  -- AM-GM for the multiset of the numbers `A.prod / a`
  have hA'pos : ∀ b ∈ A.map (fun a => A.prod * a⁻¹), 0 < b := by
    intro b hb
    rw [Multiset.mem_map] at hb
    obtain ⟨a, ha, rfl⟩ := hb
    exact mul_pos hPpos (inv_pos.mpr (hA a ha))
  have hA'card : (A.map (fun a => A.prod * a⁻¹)).card = A.card := Multiset.card_map _ _
  have hAM := amgm_multiset (A.map (fun a => A.prod * a⁻¹)) hA'pos (by rw [hA'card]; exact hn)
  rw [hA'prod, hA'card] at hAM
  have hge1 : (1:ℝ) ≤ (A.prod ^ (A.card - 1)) ^ ((A.card : ℝ)⁻¹) :=
    Real.one_le_rpow (one_le_pow₀ hP) (by positivity)
  have hsum_eq : (A.map (fun a => A.prod * a⁻¹)).sum = A.prod * (A.map (fun a => a⁻¹)).sum := by
    rw [Multiset.sum_map_mul_left]
  have hPS : (A.card : ℝ) ≤ A.prod * (A.map (fun a => a⁻¹)).sum :=
    calc (A.card : ℝ) = (A.card : ℝ) * 1 := (mul_one _).symm
      _ ≤ (A.card : ℝ) * (A.prod ^ (A.card - 1)) ^ ((A.card : ℝ)⁻¹) :=
          mul_le_mul_of_nonneg_left hge1 (Nat.cast_nonneg _)
      _ ≤ (A.map (fun a => A.prod * a⁻¹)).sum := hAM
      _ = A.prod * (A.map (fun a => a⁻¹)).sum := hsum_eq
  have hPSpos : 0 < A.prod * (A.map (fun a => a⁻¹)).sum :=
    lt_of_lt_of_le (by exact_mod_cast hn) hPS
  have hderiv := key2 A hA
  have habs : |((-1:ℝ) ^ (A.card - 1)) * (A.prod * (A.map (fun a => a⁻¹)).sum)|
      = A.prod * (A.map (fun a => a⁻¹)).sum := by
    rw [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_pos hPSpos]
  calc (A.card : ℝ) ≤ A.prod * (A.map (fun a => a⁻¹)).sum := hPS
    _ = |((-1:ℝ) ^ (A.card - 1)) * (A.prod * (A.map (fun a => a⁻¹)).sum)| := habs.symm
    _ = |(Polynomial.derivative ((A.map (fun a => Polynomial.X - Polynomial.C a)).prod)).eval 0| := by
        rw [hderiv]; congr 1; ring

/-! ## 4. Even monic polynomials with real roots -/

/-- Composition with a polynomial distributes over a multiset product. -/
lemma comp_multiset_prod {R : Type*} [CommSemiring R] (R' : Multiset R[X]) (q : R[X]) :
    (R'.prod).comp q = (R'.map (fun p => p.comp q)).prod := by
  induction R' using Multiset.induction_on with
  | empty => simp
  | cons p s ih => rw [Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
      Polynomial.mul_comp, ih]

/-- `(X - a)(X + a) = X² - a²`. -/
lemma X_sub_C_mul_X_sub_C_neg (a : ℂ) :
    (Polynomial.X - Polynomial.C a) * (Polynomial.X - Polynomial.C (-a))
      = Polynomial.X ^ 2 - Polynomial.C (a * a) := by
  rw [Polynomial.C_neg, Polynomial.C_mul]; ring

/-- `(∏(X - a)) ∘ X² = ∏(X² - a)`. -/
lemma comp_sq_prod_X_sub_C (A : Multiset ℝ) :
    ((A.map (fun a => Polynomial.X - Polynomial.C a)).prod).comp (Polynomial.X ^ 2)
      = (A.map (fun a => Polynomial.X ^ 2 - Polynomial.C a)).prod := by
  rw [comp_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intro a ha
  simp only [Function.comp_apply, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp]

/-- A multiset of complex numbers with no vanishing real part splits into the positive
reals and their negatives. -/
lemma multiset_split_pos (R : Multiset ℂ) (hsymm : R.map Neg.neg = R)
    (hre : ∀ r ∈ R, r.re ≠ 0) :
    R = R.filter (fun r => 0 < r.re) + (R.filter (fun r => 0 < r.re)).map Neg.neg := by
  have hf : R.filter (fun r => ¬ (0 < r.re)) = R.filter (fun r => r.re < 0) := by
    apply Multiset.filter_congr
    intro r hr
    constructor
    · intro h; exact lt_of_le_of_ne (le_of_not_gt h) (hre r hr)
    · intro h; exact not_lt.mpr (le_of_lt h)
  have hsplit := Multiset.filter_add_not (fun r : ℂ => 0 < r.re) R
  rw [hf] at hsplit
  have hmap : (R.filter (fun r => 0 < r.re)).map Neg.neg = R.filter (fun r => r.re < 0) := by
    have h1 := Multiset.filter_map (fun r : ℂ => r.re < 0) Neg.neg R
    rw [hsymm] at h1
    rw [show R.filter (fun r => 0 < r.re) = R.filter ((fun r : ℂ => r.re < 0) ∘ Neg.neg) from by
      apply Multiset.filter_congr
      intro r hr
      simp]
    rw [← h1]
  rw [← hmap] at hsplit
  exact hsplit.symm

/-- Evaluation of a real polynomial pushed to `ℂ` at `0`. -/
lemma eval_map_ofReal (p : ℝ[X]) :
    (p.map Complex.ofRealHom).eval (0 : ℂ) = ((p.eval 0 : ℝ) : ℂ) := by
  rw [Polynomial.eval_map]
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]
  | monomial n a => simp [Polynomial.eval₂_monomial]

/-- Second derivative at `0` of `g(X²)`, over `ℝ`. -/
lemma second_deriv_comp_sq (g : ℝ[X]) :
    (Polynomial.derivative (Polynomial.derivative (g.comp (Polynomial.X ^ 2)))).eval 0
      = 2 * (Polynomial.derivative g).eval 0 := by
  simp only [Polynomial.derivative_comp, Polynomial.derivative_pow, Polynomial.derivative_X,
    Polynomial.derivative_C, Polynomial.derivative_one, Polynomial.derivative_mul]
  simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow, Polynomial.eval_comp]

theorem even_monic_real_roots_second_deriv (f : ℂ[X]) (n : ℕ) (hn : 1 ≤ n)
    (hdeg : f.natDegree = 2 * n) (hmonic : f.Monic)
    (heven : ∀ z, f.eval (-z) = f.eval z) (hreal : ∀ z, f.eval z = 0 → z.im = 0)
    (h0 : f.eval 0 ≠ 0) (hP : 1 ≤ ‖f.eval 0‖) :
    (1:ℝ) ≤ ‖(Polynomial.derivative (Polynomial.derivative f)).eval 0‖ := by
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
  linarith

/-! ## 5. The requested quantitative bound for the rational discriminant -/

theorem discSecondDerivQuant (p : ℤ) (q m : ℕ) (hm : q = 2*m+2) (hpq : Nat.Coprime p.natAbs q)
    (lam : ℝ) (hlam : 0 < lam) :
    (1:ℝ) ≤ ‖(Polynomial.derivative (Polynomial.derivative (disc p q lam))).eval 0‖ := by
  have hq : 1 ≤ q := by omega
  have hval := dsdqDiscZeroAbs p q m hm hpq lam hlam
  have h0 : (disc p q lam).eval 0 ≠ 0 := by
    intro h; rw [h] at hval; simp at hval; linarith [pow_pos hlam q]
  have hP : 1 ≤ ‖(disc p q lam).eval 0‖ := by
    rw [hval]; linarith [pow_pos hlam q]
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
  exact even_monic_real_roots_second_deriv (disc p q lam) (m + 1) (by omega) hdeg hmonic
    (discEven p q m hm hpq lam) hreal h0 hP

end Work.TMC14Core
