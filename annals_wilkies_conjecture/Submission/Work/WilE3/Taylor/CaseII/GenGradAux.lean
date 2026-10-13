import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.eaEval_analytic
import Submission.Work.WilE3.Taylor.Grad.hinge
import Submission.Work.WilE3.Taylor.CaseII.Defs
import Submission.Work.WilE3.Taylor.CaseII.GenDeficit
import Submission.Work.WilE3.Taylor.CaseII.atomDeg_pertSys_le
import Submission.Work.WilE3.Taylor.CaseII.atomDeg_sphSys_le
import Submission.Work.Taylor.Grad.order_le_of_sumsq_pow_lt

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / CaseII: **the assembly of the replacement route**
  (design `sources/wilkiesE3caseII/wilkies_e3_caseII.md`, §3, node T5 minus the measure theory).

  This module proves the *mathematical core* of node T5: given

  * a bad arc `γ` through a zero `y'` of `Q` carrying the sum-of-squares bad inequality with a
    constant `C > 0`, lying either on the interior perturbed system `pertSys c Q v i₀`
    (with `∂_{i₀}Q` not vanishing along `γ`) or on the boundary system
    `sphSys c Q v y d i₀ j₀` (with the `(i₀,j₀)` minor of `(∇Q, · - y)` not vanishing);
  * the *nondegeneracy* of the corresponding square system along `γ` (the hypothesis `hT4i`/`hT4b`,
    supplied in the caller by the Sard/Fubini genericity of `v` and `d`);
  * the generalised Case A count `squareSystem_deficit` (node T2′), specialized to the polynomial `K₀`
    appearing in the exponents of the bad inequality;

  one derives a contradiction.  The argument is exactly the arithmetic of the hinge
  (`Work.WilE3.Taylor.Grad.ea_grad_of_arcCrux`, Step 8):

  * `T2'` gives a partial `∂ᵢQ` of order `n` with `(B+1)·n ≤ B·m`, `B = K₀.eval (atomDeg Q)`;
  * the bad inequality along the arc gives `(A+1)·m ≤ (A+2)·n`, `A = K₀.eval (atomDeg Φ)`;
  * `atomDeg Q ≤ atomDeg Φ` gives `B ≤ A`, and `A+1 ≤ B ≤ A` is absurd.
-/

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open WilkiesDesign.E

namespace Work.WilE3.Taylor.CaseII

variable {k r : ℕ}

/-- **The interior Lagrange hypotheses** of the perturbed system `pertSys c Q v i₀`, along an arc:
the pivot partial `∂_{i₀}Q` does not vanish, the value `Q` is positive, and all other rows of the
square system vanish identically along the arc. -/
def IntHyp (c : EAChain k r) (Q : EAPoly k r) (v : Fin k → ℝ) (i₀ : Fin k)
    (γ : ℝ → Fin k → ℝ) : Prop :=
  ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
    0 < eaEval c Q (γ t) ∧ eaEval c (eaD c i₀ Q) (γ t) ≠ 0 ∧
      ∀ i : Fin k, i ≠ i₀ → eaEval c (pertMinor c Q v i₀ i) (γ t) = 0

/-- **The boundary Lagrange hypotheses** of the perturbed radial system
`sphSys c Q v y d i₀ j₀`, along an arc: the sphere `∑ (xᵢ - yᵢ)² = d` contains the arc, the
`(i₀,j₀)` minor of `(∇Q, · - y)` does not vanish, and all other rows vanish identically along it. -/
def BdHyp (c : EAChain k r) (Q : EAPoly k r) (v y : Fin k → ℝ) (d : ℝ) (i₀ j₀ : Fin k)
    (γ : ℝ → Fin k → ℝ) : Prop :=
  ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
    0 < eaEval c Q (γ t) ∧ eaEval c (sphereP y d) (γ t) = 0 ∧
      (eaEval c (eaD c i₀ Q) (γ t) * (γ t j₀ - y j₀)
        - eaEval c (eaD c j₀ Q) (γ t) * (γ t i₀ - y i₀)) ≠ 0 ∧
      ∀ l : Fin k, l ≠ i₀ → l ≠ j₀ → eaEval c (pertMinor3 c Q v y i₀ j₀ l) (γ t) = 0

/-- `Polynomial.eval` is monotone in its argument (all coefficients are natural numbers). -/
private lemma eval_le_eval' {K : Polynomial ℕ} {a b : ℕ} (h : a ≤ b) : K.eval a ≤ K.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  exact Finset.sum_le_sum fun i _ => Nat.mul_le_mul_left _ (pow_le_pow_left₀ (Nat.zero_le _) h _)

/-- **Order bookkeeping for the sum-of-squares inequality with a constant factor.**

If `F : Fin k → ℝ → ℝ` and `G` are analytic at `0`, `F i` has order `n`, `G` has positive order
data (`ord G = m`, `G > 0` on a right neighbourhood), and

`(∑ j (F j t)²) ^ q < C * (G t) ^ (2 * p)` for small `t > 0`, `C > 0`, `q > 0`,

then `p * m ≤ q * n`.  Proof: scale the family `F` by `C ^ (-1/(2q))`; the constant disappears and
the constant-free `Work.Taylor.Grad.order_le_of_sumsq_pow_lt` applies. -/
lemma order_le_of_sumsq_pow_lt_const {k : ℕ} {F : Fin k → ℝ → ℝ} {G : ℝ → ℝ} {p q m n : ℕ}
    {i : Fin k} {C : ℝ} (hC : 0 < C) (hq : 0 < q) (hF : AnalyticAt ℝ (F i) 0)
    (hG : AnalyticAt ℝ G 0) (hFord : analyticOrderAt (F i) 0 = n)
    (hGord : analyticOrderAt G 0 = m)
    (hGpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < G t)
    (hineq : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (∑ j, (F j t) ^ 2) ^ q < C * (G t) ^ (2 * p)) :
    p * m ≤ q * n := by
  have h2q : 2 * q ≠ 0 := by omega
  set β : ℝ := (C ^ (((2 * q : ℕ) : ℝ)⁻¹))⁻¹ with hβdef
  have hCpow_pos : 0 < C ^ (((2 * q : ℕ) : ℝ)⁻¹) := Real.rpow_pos_of_pos hC _
  have hβne : β ≠ 0 := by rw [hβdef]; exact inv_ne_zero hCpow_pos.ne'
  have hβpow : β ^ (2 * q) = C⁻¹ := by
    rw [hβdef, inv_pow, Real.rpow_inv_natCast_pow hC.le h2q]
  -- the order of the scaled function `β * F i`
  have heqβ : (fun t : ℝ => β * F i t) = (fun _ : ℝ => β) • F i := by
    funext t; simp [Pi.smul_apply]
  have hFord' : analyticOrderAt (fun t : ℝ => β * F i t) 0 = n := by
    rw [heqβ]
    have hc : analyticOrderAt (fun _ : ℝ => β) (0 : ℝ) = 0 :=
      analyticOrderAt_eq_zero.mpr (Or.inr (by simpa using hβne))
    have hsm := analyticOrderAt_smul (𝕜 := ℝ) (z₀ := (0 : ℝ)) (f := fun _ : ℝ => β) (g := F i)
      analyticAt_const hF
    rw [hc, hFord, zero_add] at hsm
    exact hsm
  have hF' : AnalyticAt ℝ (fun t : ℝ => β * F i t) 0 := by
    rw [heqβ]
    exact analyticAt_const.smul hF
  have hineq' : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      (∑ j, (β * F j t) ^ 2) ^ q < (G t) ^ (2 * p) := by
    filter_upwards [hineq] with t ht
    have hsum : (∑ j, (β * F j t) ^ 2) = β ^ 2 * (∑ j, (F j t) ^ 2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hsum, mul_pow, ← pow_mul, hβpow]
    calc C⁻¹ * (∑ j, (F j t) ^ 2) ^ q < C⁻¹ * (C * (G t) ^ (2 * p)) :=
          mul_lt_mul_of_pos_left ht (inv_pos.mpr hC)
      _ = (G t) ^ (2 * p) := by rw [← mul_assoc, inv_mul_cancel₀ hC.ne', one_mul]
  exact Work.Taylor.Grad.order_le_of_sumsq_pow_lt (F := fun j t => β * F j t) (G := G) (i := i)
    (p := p) (q := q) (m := m) (n := n) hF' hG hFord' hGord hGpos hineq'

/-- **The arithmetic contradiction.**  If `(B+1)·n ≤ B·m`, `(A+1)·m ≤ (A+2)·n`, `B ≤ A` and
`m > 0`, then `A + 1 ≤ B ≤ A`, absurd. -/
private lemma arith_contra {A B m n : ℕ} (hm : 0 < m) (hB : B ≤ A)
    (hbound : (B + 1) * n ≤ B * m) (hbad : (A + 1) * m ≤ (A + 2) * n) : False := by
  have hchain : (B + 1) * ((A + 1) * m) ≤ (A + 2) * (B * m) := by
    calc (B + 1) * ((A + 1) * m) ≤ (B + 1) * ((A + 2) * n) := Nat.mul_le_mul_left _ hbad
      _ = (A + 2) * ((B + 1) * n) := by ring
      _ ≤ (A + 2) * (B * m) := Nat.mul_le_mul_left _ hbound
  have hfin : (B + 1) * (A + 1) ≤ (A + 2) * B := by
    refine Nat.le_of_mul_le_mul_right ?_ hm
    calc (B + 1) * (A + 1) * m = (B + 1) * ((A + 1) * m) := by ring
      _ ≤ (A + 2) * (B * m) := hchain
      _ = ((A + 2) * B) * m := by ring
  have h1 : (A : ℤ) + 1 ≤ (B : ℤ) := by
    have h2 : (((B + 1) * (A + 1) : ℕ) : ℤ) ≤ (((A + 2) * B : ℕ) : ℤ) := by
      exact_mod_cast hfin
    push_cast at h2
    nlinarith
  have h3 : (B : ℤ) ≤ (A : ℤ) := by exact_mod_cast hB
  omega

/-- **The contradiction of the replacement route.**  A bad arc lying on one of the square systems
`pertSys`/`sphSys` (with nondegenerate Jacobian along the arc, in the sense of `hT4i`/`hT4b`) and
carrying the bad sum-of-squares inequality is impossible, given the generalised Case A count. -/
theorem badArc_contradiction
    (F : ℕ) {k r : ℕ} (hkr : k + r ≤ F)
    (K₀ : Polynomial ℕ)
    (hT2 : ∀ (c : EAChain k r) (Q : EAPoly k r) (y : Fin k → ℝ) (γ : ℝ → Fin k → ℝ)
      (P : Fin k → EAPoly k r) (m a : ℕ) (i₀ : Fin k),
      P i₀ = Q → (∀ i, atomDeg (P i) ≤ 3 * atomDeg Q + 3) →
      k + r ≤ F → AnalyticAt ℝ γ 0 → γ 0 = y → 0 < a → 0 < m →
      analyticOrderAt (fun t : ℝ => γ t - y) 0 = a →
      analyticOrderAt (fun t : ℝ => eaEval c Q (γ t)) 0 = m →
      (∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i : Fin k, i ≠ i₀ → eaEval c (P i) (γ t) = 0) →
      (¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (Matrix.of fun i j => eaEval c (eaD c j (P i)) (γ t)).det = 0) →
      ∃ (i : Fin k) (n : ℕ), analyticOrderAt (fun t : ℝ => eaEval c (eaD c i Q) (γ t)) 0 = n ∧
        (K₀.eval (atomDeg Q) + 1) * n ≤ K₀.eval (atomDeg Q) * m)
    (c : EAChain k r) (Φ Q : EAPoly k r) (hQa : atomDeg Q ≤ atomDeg Φ)
    (p q : ℕ) (hpq : p = K₀.eval (atomDeg Φ) + 1) (hqp : q = K₀.eval (atomDeg Φ) + 2)
    (y : Fin k → ℝ) (v : Fin k → ℝ) (d : ℝ)
    (hT4i : ∀ (i₀ : Fin k) (γ : ℝ → Fin k → ℝ), AnalyticAt ℝ γ 0 → eaEval c Q (γ 0) = 0 →
      IntHyp c Q v i₀ γ →
      ¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), sysDet c (pertSys c Q v i₀) (γ t) = 0)
    (hT4b : ∀ (i₀ j₀ : Fin k), i₀ ≠ j₀ → ∀ (γ : ℝ → Fin k → ℝ), AnalyticAt ℝ γ 0 →
      eaEval c Q (γ 0) = 0 → BdHyp c Q v y d i₀ j₀ γ →
      ¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), sysDet c (sphSys c Q v y d i₀ j₀) (γ t) = 0)
    (y' : Fin k → ℝ) (γ : ℝ → Fin k → ℝ) (C : ℝ) (hC : 0 < C)
    (hγan : AnalyticAt ℝ γ 0) (hγ0 : γ 0 = y') (hQy' : eaEval c Q y' = 0)
    (hbad : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < eaEval c Q (γ t) ∧
      (∑ l : Fin k, (eaEval c (eaD c l Q) (γ t)) ^ 2) ^ q
        < C * (eaEval c Q (γ t)) ^ (2 * p))
    (hcase : (∃ i₀ : Fin k, ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        eaEval c (eaD c i₀ Q) (γ t) ≠ 0 ∧
        ∀ i : Fin k, i ≠ i₀ → eaEval c (pertMinor c Q v i₀ i) (γ t) = 0) ∨
      (∃ i₀ j₀ : Fin k, i₀ ≠ j₀ ∧ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        eaEval c (sphereP y d) (γ t) = 0 ∧
        (eaEval c (eaD c i₀ Q) (γ t) * (γ t j₀ - y j₀)
          - eaEval c (eaD c j₀ Q) (γ t) * (γ t i₀ - y i₀)) ≠ 0 ∧
        ∀ l : Fin k, l ≠ i₀ → l ≠ j₀ → eaEval c (pertMinor3 c Q v y i₀ j₀ l) (γ t) = 0)) :
    False := by
  -- ### the order data of the arc
  have hpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < eaEval c Q (γ t) :=
    hbad.mono fun t ht => ht.1
  obtain ⟨m, hm, hord⟩ := Grad.exists_pos_order_of_eventually_pos hγan
    (Work.WilE3.eaEval_analytic c Q y') hQy' hγ0 hpos
  -- ### the ramification order `a` of `γ - y'`
  have hne : ¬ (γ =ᶠ[𝓝 (0 : ℝ)] fun _ => y') := by
    intro hconst
    have htop : analyticOrderAt (fun t : ℝ => eaEval c Q (γ t)) 0 = ⊤ := by
      rw [analyticOrderAt_eq_top]
      filter_upwards [hconst] with t ht
      rw [ht, hQy']
    rw [hord] at htop
    exact absurd htop (ENat.natCast_ne_top m)
  have ha_exists : ∃ a : ℕ, 0 < a ∧ analyticOrderAt (fun t : ℝ => γ t - y') 0 = a := by
    have hsub : AnalyticAt ℝ (fun t : ℝ => γ t - y') 0 := by
      have heq : (fun t : ℝ => γ t - y') = γ - fun _ : ℝ => y' := by
        funext t; simp [Pi.sub_apply]
      rw [heq]
      exact hγan.sub analyticAt_const
    have hne_top : analyticOrderAt (fun t : ℝ => γ t - y') 0 ≠ ⊤ := by
      intro htop
      rw [analyticOrderAt_eq_top] at htop
      exact hne (by filter_upwards [htop] with t ht; exact sub_eq_zero.mp ht)
    obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp hne_top
    refine ⟨a, ?_, ha.symm⟩
    rcases Nat.eq_zero_or_pos a with h0 | hpos'
    · exfalso
      have hz : analyticOrderAt (fun t : ℝ => γ t - y') 0 = 0 := by rw [← ha, h0]; rfl
      rw [analyticOrderAt_eq_zero] at hz
      rcases hz with h | h
      · exact h hsub
      · exact h (by simp [hγ0])
    · exact hpos'
  obtain ⟨a, ha_pos, hram⟩ := ha_exists
  -- ### the bad inequality at any index of order `n`
  have hbadOrder : ∀ (i : Fin k) (n : ℕ),
      analyticOrderAt (fun t : ℝ => eaEval c (eaD c i Q) (γ t)) 0 = n → p * m ≤ q * n := by
    intro i n hn
    refine order_le_of_sumsq_pow_lt_const (F := fun l : Fin k => fun t : ℝ =>
        eaEval c (eaD c l Q) (γ t)) (G := fun t : ℝ => eaEval c Q (γ t)) (i := i)
      (p := p) (q := q) (m := m) (n := n) (C := C) hC (by rw [hqp]; omega) ?_ ?_ hn hord hpos ?_
    · exact AnalyticAt.comp (x := (0 : ℝ)) (f := γ)
        (g := fun z : Fin k → ℝ => eaEval c (eaD c i Q) z)
        (Work.WilE3.eaEval_analytic c (eaD c i Q) (γ 0)) hγan
    · exact AnalyticAt.comp (x := (0 : ℝ)) (f := γ)
        (g := fun z : Fin k → ℝ => eaEval c Q z)
        (Work.WilE3.eaEval_analytic c Q (γ 0)) hγan
    · filter_upwards [hbad] with t ht
      exact ht.2
  -- ### the two cases of the arc
  rcases hcase with ⟨i₀, hi₀⟩ | ⟨i₀, j₀, hij, hj₀⟩
  · -- ## interior case
    have hP : pertSys c Q v i₀ i₀ = Q := by simp [pertSys]
    have hdet : ¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (Matrix.of fun i j => eaEval c (eaD c j (pertSys c Q v i₀ i)) (γ t)).det = 0 :=
      hT4i i₀ γ hγan (by rw [hγ0]; exact hQy') (by
        filter_upwards [hbad, hi₀] with t ht hh
        exact ⟨ht.1, hh⟩)
    have hmin : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i : Fin k, i ≠ i₀ →
        eaEval c (pertSys c Q v i₀ i) (γ t) = 0 := by
      filter_upwards [hi₀] with t ht i hi
      have hPi : pertSys c Q v i₀ i = pertMinor c Q v i₀ i := by
        show (if i = i₀ then Q else pertMinor c Q v i₀ i) = pertMinor c Q v i₀ i
        rw [if_neg hi]
      rw [hPi]
      exact ht.2 i hi
    obtain ⟨i, n, hn, hbound⟩ := hT2 c Q y' γ (pertSys c Q v i₀) m a i₀ hP
      (fun i => atomDeg_pertSys_le c Q v i₀ i) hkr hγan hγ0 ha_pos hm hram hord hmin hdet
    have hbn := hbadOrder i n hn
    rw [hpq, hqp] at hbn
    exact arith_contra hm (eval_le_eval' hQa) hbound hbn
  · -- ## boundary case
    have hP : sphSys c Q v y d i₀ j₀ i₀ = Q := by
      show (if i₀ = i₀ then Q else if i₀ = j₀ then sphereP y d
        else pertMinor3 c Q v y i₀ j₀ i₀) = Q
      rw [if_pos rfl]
    have hdet : ¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (Matrix.of fun i j => eaEval c (eaD c j (sphSys c Q v y d i₀ j₀ i)) (γ t)).det = 0 :=
      hT4b i₀ j₀ hij γ hγan (by rw [hγ0]; exact hQy') (by
        filter_upwards [hbad, hj₀] with t ht hh
        exact ⟨ht.1, hh⟩)
    have hmin : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i : Fin k, i ≠ i₀ →
        eaEval c (sphSys c Q v y d i₀ j₀ i) (γ t) = 0 := by
      filter_upwards [hj₀] with t ht i hi
      rcases eq_or_ne i j₀ with h | h
      · have hPj : sphSys c Q v y d i₀ j₀ i = sphereP y d := by
          rw [h]
          show (if j₀ = i₀ then Q else if j₀ = j₀ then sphereP y d
            else pertMinor3 c Q v y i₀ j₀ j₀) = sphereP y d
          rw [if_neg (Ne.symm hij), if_pos rfl]
        rw [hPj]
        exact ht.1
      · have hPl : sphSys c Q v y d i₀ j₀ i = pertMinor3 c Q v y i₀ j₀ i := by
          show (if i = i₀ then Q else if i = j₀ then sphereP y d
            else pertMinor3 c Q v y i₀ j₀ i) = pertMinor3 c Q v y i₀ j₀ i
          rw [if_neg hi, if_neg h]
        rw [hPl]
        exact ht.2.2 i hi h
    obtain ⟨i, n, hn, hbound⟩ := hT2 c Q y' γ (sphSys c Q v y d i₀ j₀) m a i₀ hP
      (fun i => atomDeg_sphSys_le c Q v y d i₀ j₀ i) hkr hγan hγ0 ha_pos hm hram hord hmin hdet
    have hbn := hbadOrder i n hn
    rw [hpq, hqp] at hbn
    exact arith_contra hm (eval_le_eval' hQa) hbound hbn

end Work.WilE3.Taylor.CaseII
