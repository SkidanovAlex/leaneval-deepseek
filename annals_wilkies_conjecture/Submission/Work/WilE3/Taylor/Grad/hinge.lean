import Mathlib
import Submission.Work.WilE3.Defs
import Submission.Work.WilE3.eaEval_analytic
import Submission.Work.WilE3.Taylor.Grad.PolarDefs
import Submission.Work.WilE3.Taylor.Grad.badSeqOnPolarSet
import Submission.Work.WilE3.Taylor.Grad.arcOnSigma
import Submission.Work.WilE3.Taylor.Grad.sumSqGrad_le_norm_fderiv_sq
import Submission.Work.Taylor.Grad.grad_eaEval
import Submission.Work.Taylor.Grad.arcOnSigma2
import Submission.Work.Taylor.Grad.order_le_of_sumsq_pow_lt

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / Grad: **the hinge**.

  This module reduces the effective gradient inequality for EA functions (`(GRAD)`, Gabrielov 1995
  Theorem 3.3) to the *arc crux* `ArcCrux` (no gradient-polar arc carries the bad inequality).

  Route (see `Taylor/NOTES_hasLoj_of_multiplicity.md`, SESSION 7):

  * `Φ` with `Φ y = 0` is fixed, and `(GRAD)` is proved with `cst = 1` and the exponent
    `κ = min_σ (K.eval (atomDeg (C σ * Φ)) + 1)/(K.eval (atomDeg (C σ * Φ)) + 2)`, `σ ∈ {±1}`.
    The minimum over the two signs is what makes the argument *non-circular*: the bad set of `κ`
    is *equal* to the bad set of the sign `σ₀` attaining the minimum, so the failure of `(GRAD)`
    produces bad points with a definite sign `σ₀ * Φ > 0`, which is exactly the hypothesis of
    `badSeqOnPolarSet` for the polynomial `Ψ := C σ₀ * Φ`;
  * `badSeqOnPolarSet` (Step A: Lagrange at constrained minimisers of `|∇Φ|²` on the level sets)
    followed by `arcOnSigma` / `arcOnSigma2` (Step B: curve selection) produce a real analytic arc
    `γ` through `y` in the `PolarLike` locus carrying the bad inequality for `Ψ`;
  * `ArcCrux` for `Ψ` contradicts it.

  The remaining mathematical input is `ArcCrux` restricted to the arcs which are *not* in Case A;
  Case A (`¬ det J ≡ 0` along a genuine polar branch) is proved in
  `Work.Taylor.Grad.not_bad_of_polar_goodLevel`.
-/

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped Topology
open WilkiesDesign.E

namespace Work.WilE3.Taylor.Grad

variable {k r : ℕ}

/-- **The gradient-polar locus `Σ ∪ Σ₂`, in EA form.**  Along `γ` all the `3 × 3` minors of the
rows `(∇φ, ∇Φ, · - y)` vanish (with `φ = Σᵢ (∂ᵢΦ)²`).  This is the condition produced by Step A
(Lagrange at a constrained minimiser of `φ` on the level sets of `Φ`): the interior case gives
`∇φ ∥ ∇Φ` (`Σ`, and then the minors with third row `· - y` certainly vanish) and the boundary case
gives `∇φ ∈ span{∇Φ, · - y}` (`Σ₂`). -/
def PolarLike (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ) (γ : ℝ → Fin k → ℝ) : Prop :=
  ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i j l : Fin k,
    det3 (fun m => eaEval c (eaD c m (sqGrad c Φ)) (γ t))
      (fun m => eaEval c (eaD c m Φ) (γ t)) (γ t - y) i j l = 0

/-- **The bad inequality of the arc crux**, at the exponents `p = K.eval (atomDeg Φ) + 1`,
`q = K.eval (atomDeg Φ) + 2`, i.e. `κ = p/q`. -/
def ArcBad (c : EAChain k r) (Φ : EAPoly k r) (γ : ℝ → Fin k → ℝ) (K : Polynomial ℕ) : Prop :=
  ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
    (∑ i : Fin k, (eaEval c (eaD c i Φ) (γ t)) ^ 2) ^ (K.eval (atomDeg Φ) + 2)
      < (eaEval c Φ (γ t)) ^ (2 * (K.eval (atomDeg Φ) + 1))

/-- **The arc crux** (Gabrielov 1995 §3, Theorem 3.3 in arc form, *sharp*): for every format
bound there is a polynomial `K` such that every analytic arc `γ` through `y` carrying the
gradient-polar conditions `PolarLike`, with `m = ord₀ (Φ ∘ γ) > 0`, has *some* coordinate partial
`∂ᵢΦ` whose order `n` along `γ` satisfies `(K.eval (atomDeg Φ) + 1) * n ≤ K.eval (atomDeg Φ) * m`,
i.e. `n / m ≤ 1 - 1/(K.eval (atomDeg Φ) + 1)`.  This is the form of the bound that is *monotone in
the exponent* and hence usable in the hinge below. -/
def ArcCrux : Prop :=
  ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (Φ : EAPoly k r) (y : Fin k → ℝ)
    (γ : ℝ → Fin k → ℝ) (m : ℕ),
    k + r ≤ F → AnalyticAt ℝ γ 0 → γ 0 = y → 0 < m →
    analyticOrderAt (fun t : ℝ => eaEval c Φ (γ t)) 0 = m →
    PolarLike c Φ y γ →
    ∃ (i : Fin k) (n : ℕ),
      analyticOrderAt (fun t : ℝ => eaEval c (eaD c i Φ) (γ t)) 0 = n ∧
        (K.eval (atomDeg Φ) + 1) * n ≤ K.eval (atomDeg Φ) * m

/-! ## Elementary preparations -/

/-- `Polynomial.eval` is monotone in the argument (all coefficients are natural numbers). -/
lemma Polynomial.eval_le_eval {K : Polynomial ℕ} {a b : ℕ} (h : a ≤ b) : K.eval a ≤ K.eval b := by
  rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range]
  refine Finset.sum_le_sum fun i _ => ?_
  exact Nat.mul_le_mul_left _ (pow_le_pow_left₀ (Nat.zero_le _) h _)

/-- Evaluation of `C σ * Φ`. -/
lemma eaEval_C_mul (c : EAChain k r) (σ : ℝ) (Φ : EAPoly k r) (x : Fin k → ℝ) :
    eaEval c (MvPolynomial.C σ * Φ) x = σ * eaEval c Φ x := by
  simp [eaEval, MvPolynomial.eval_mul]

/-- Differentiation of `C σ * Φ`. -/
lemma eaD_C_mul (c : EAChain k r) (σ : ℝ) (Φ : EAPoly k r) (i : Fin k) :
    eaD c i (MvPolynomial.C σ * Φ) = MvPolynomial.C σ * eaD c i Φ := by
  rw [eaD, eaD, MvPolynomial.pderiv_C_mul, mul_add, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [MvPolynomial.pderiv_C_mul]; ring

/-- The atom degree does not increase when multiplying by a constant. -/
lemma atomDeg_C_mul_le (σ : ℝ) (Φ : EAPoly k r) : atomDeg (MvPolynomial.C σ * Φ) ≤ atomDeg Φ := by
  have h : (MvPolynomial.C σ * Φ : EAPoly k r) = σ • Φ := by
    rw [MvPolynomial.C_mul']
  rw [h, atomDeg, atomDeg]
  exact Nat.succ_le_succ (MvPolynomial.totalDegree_smul_le σ Φ)

/-- The `i`-th coordinate gradient of `eaEval c Q` is `eaEval c (eaD c i Q)`. -/
lemma grad_eq_eaD (c : EAChain k r) (Q : EAPoly k r) (x : Fin k → ℝ) (i : Fin k) :
    Work.WilE3.Taylor.grad (fun z : Fin k → ℝ => eaEval c Q z) x i = eaEval c (eaD c i Q) x :=
  Work.Taylor.Grad.grad_eaEval c Q x i

/-- The coordinate gradient of the squared gradient norm: `∇(Σₗ (∂ₗQ)²) = ∇(eaEval (sqGrad Q))`. -/
lemma grad_sqGrad (c : EAChain k r) (Q : EAPoly k r) (x : Fin k → ℝ) (i : Fin k) :
    Work.WilE3.Taylor.grad (fun z : Fin k → ℝ => ∑ l : Fin k, (Work.WilE3.Taylor.grad
        (fun w : Fin k → ℝ => eaEval c Q w) z l) ^ 2) x i
      = eaEval c (eaD c i (sqGrad c Q)) x := by
  have hfun : (fun z : Fin k → ℝ => ∑ l : Fin k,
      (Work.WilE3.Taylor.grad (fun w : Fin k → ℝ => eaEval c Q w) z l) ^ 2)
      = fun z : Fin k → ℝ => eaEval c (sqGrad c Q) z := by
    funext z
    rw [eaEval_sqGrad]
    exact Finset.sum_congr rfl fun l _ => by rw [grad_eq_eaD]
  rw [hfun]
  exact grad_eq_eaD c (sqGrad c Q) x i

/-- **The order of an analytic arc with an eventually positive value function.**  If `Φ (γ ·)` is
positive on a right-neighbourhood of `0` and `Φ y = 0`, then `ord₀ (Φ ∘ γ)` is a *positive natural
number* (not `0` and not `⊤`). -/
lemma exists_pos_order_of_eventually_pos {Φ : (Fin k → ℝ) → ℝ} {γ : ℝ → Fin k → ℝ}
    {y : Fin k → ℝ} (hγ : AnalyticAt ℝ γ 0) (hΦ : AnalyticAt ℝ Φ y) (hy : Φ y = 0)
    (hγ0 : γ 0 = y)
    (hpos : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < Φ (γ t)) :
    ∃ m : ℕ, 0 < m ∧ analyticOrderAt (fun t : ℝ => Φ (γ t)) 0 = m := by
  have hcomp : AnalyticAt ℝ (fun t : ℝ => Φ (γ t)) 0 := AnalyticAt.comp (hγ0.symm ▸ hΦ) hγ
  have h0 : (fun t : ℝ => Φ (γ t)) 0 = 0 := by simpa [hγ0] using hy
  have hne0 : analyticOrderAt (fun t : ℝ => Φ (γ t)) 0 ≠ 0 := by
    intro h
    rw [analyticOrderAt_eq_zero] at h
    rcases h with h | h
    · exact h hcomp
    · exact h h0
  have hnetop : analyticOrderAt (fun t : ℝ => Φ (γ t)) 0 ≠ ⊤ := by
    intro h
    rw [analyticOrderAt_eq_top] at h
    have hboth : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), Φ (γ t) = 0 ∧ 0 < Φ (γ t) :=
      (h.filter_mono nhdsWithin_le_nhds).and hpos
    obtain ⟨t, ht⟩ := hboth.exists
    exact absurd ht.1 ht.2.ne'
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hnetop
  refine ⟨m, ?_, hm.symm⟩
  rcases Nat.eq_zero_or_pos m with h0' | hpos'
  · exfalso
    exact hne0 (by rw [← hm, h0']; rfl)
  · exact hpos'


/-- The `3 × 3` determinant `det3` vanishes when its first two rows are parallel. -/
lemma det3_eq_zero_of_parallel {k : ℕ} {U W t : Fin k → ℝ}
    (h : ∀ i j : Fin k, U i * W j - U j * W i = 0) : ∀ i j l : Fin k, det3 W U t i j l = 0 := by
  rcases minors_eq_zero_iff U W |>.mp h with ⟨c, hc⟩ | ⟨d, hd⟩
  · intro i j l
    simp only [det3]
    rw [congrFun hc i, congrFun hc j, congrFun hc l]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  · intro i j l
    simp only [det3]
    rw [congrFun hd i, congrFun hd j, congrFun hd l]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- `Polynomial.eval (atomDeg Φ) (K + 2) = K.eval (atomDeg Φ) + 2`. -/
lemma eval_add_two (K : Polynomial ℕ) (d : ℕ) : (K + 2).eval d = K.eval d + 2 := by
  rw [Polynomial.eval_add]
  congr 1
  simp

/-- The coordinate gradient of `Σₗ (∂ₗQ)²` written with the other order of the summands. -/
lemma grad_sqGrad' (c : EAChain k r) (Q : EAPoly k r) (x : Fin k → ℝ) (i : Fin k) :
    Work.WilE3.Taylor.grad (fun z : Fin k → ℝ => ∑ l : Fin k,
        (eaEval c (eaD c l Q) z) ^ 2) x i = eaEval c (eaD c i (sqGrad c Q)) x := by
  have hfun : (fun z : Fin k → ℝ => ∑ l : Fin k, (eaEval c (eaD c l Q) z) ^ 2)
      = fun z : Fin k → ℝ => ∑ l : Fin k,
          (Work.WilE3.Taylor.grad (fun w : Fin k → ℝ => eaEval c Q w) z l) ^ 2 := by
    funext z
    exact Finset.sum_congr rfl fun l _ => by rw [grad_eq_eaD]
  rw [hfun, grad_sqGrad]

/-- **The hinge: the arc crux implies the effective gradient inequality `(GRAD)`** (Gabrielov 1995,
Theorem 3.3) for EA functions, with `cst = 1` and the exponent `κ = (A+1)/(A+2)`,
`A = K.eval (atomDeg Φ)`.

The sign `σ` of the bad points is handled by applying the crux to `Ψ = C σ * Φ`: since
`atomDeg Ψ ≤ atomDeg Φ`, the crux's bound for `Ψ` (`n/m ≤ B/(B+1)`, `B = K.eval (atomDeg Ψ)`) is
*stronger* than the bound `n/m ≤ A/(A+1)` at `Φ`, and `(A+1)/(A+2) > A/(A+1) ≥ B/(B+1)` — this is
what makes the contradiction strict and the choice of `κ` independent of `σ`. -/
theorem ea_grad_of_arcCrux (hMB : Work.WilE3.MultiplicityBound) (harc : ArcCrux) :
    ∀ F : ℕ, ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : EAChain k r) (Φ : EAPoly k r)
      (y : Fin k → ℝ),
      k + r ≤ F → eaEval c Φ y = 0 →
      ∃ (κ cst : ℝ), 0 ≤ κ ∧ κ < 1 ∧ 0 < cst ∧
        1 / (1 - κ) ≤ ((K.eval (atomDeg Φ) : ℕ) : ℝ) ∧
        (∀ᶠ x in 𝓝 y, cst * |eaEval c Φ x| ^ κ ≤
          ‖fderiv ℝ (fun z : Fin k → ℝ => eaEval c Φ z) x‖) := by
  intro F
  obtain ⟨K, hK⟩ := harc F
  refine ⟨K + 2, ?_⟩
  intro k r c Φ y hkr hΦy
  rcases k with _ | k
  · refine ⟨1 / 2, 1, by norm_num, by norm_num, one_pos, ?_, ?_⟩
    · have hev : (((K + 2).eval (atomDeg Φ) : ℕ) : ℝ)
          = ((K.eval (atomDeg Φ) : ℕ) : ℝ) + 2 := by
        rw [eval_add_two]
        push_cast
        ring
      rw [hev]
      have h2 : (1 : ℝ) / (1 - 1 / 2) = 2 := by norm_num
      rw [h2]
      have h3 : (0 : ℝ) ≤ ((K.eval (atomDeg Φ) : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    · filter_upwards with x
      have hxy : x = y := Subsingleton.elim x y
      have hA0 : |eaEval c Φ y| = 0 := by rw [hΦy]; exact abs_zero
      rw [hxy, hA0, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0), one_mul]
      exact norm_nonneg _
  · set A : ℕ := K.eval (atomDeg Φ) with hA
    set p : ℕ := A + 1 with hp
    set q : ℕ := A + 2 with hq
    set κ : ℝ := (p : ℝ) / (q : ℝ) with hκdef
    have hq_pos : 0 < q := by rw [hq]; omega
    have hp_lt_q : p < q := by rw [hp, hq]; omega
    have hκ_nonneg : 0 ≤ κ := by rw [hκdef]; positivity
    have hκ_pos : 0 < κ := by
      rw [hκdef]
      exact div_pos (by positivity) (by positivity)
    have hκ_lt_one : κ < 1 := by
      rw [hκdef, div_lt_one (by positivity : (0 : ℝ) < (q : ℝ))]
      exact_mod_cast hp_lt_q
    have hκ_bound : 1 / (1 - κ) ≤ (((K + 2).eval (atomDeg Φ) : ℕ) : ℝ) := by
      have h1 : 1 - κ = 1 / (q : ℝ) := by
        rw [hκdef]
        field_simp
        have hqp : q = p + 1 := by omega
        rw [hqp]
        push_cast
        ring
      rw [h1, one_div_one_div]
      have hnat : ((K + 2).eval (atomDeg Φ) : ℕ) = A + 2 := by
        rw [eval_add_two, hA]
      rw [hnat, ← hq]
    refine ⟨κ, 1, hκ_nonneg, hκ_lt_one, one_pos, hκ_bound, ?_⟩
    by_contra hbadEv
    -- ## Step 1: bad points arbitrarily close to `y`
    have hbad_pts : ∀ n : ℕ, ∃ x : Fin (k + 1) → ℝ, dist x y < 1 / (n + 1) ∧
        ‖fderiv ℝ (fun z : Fin (k + 1) → ℝ => eaEval c Φ z) x‖ < |eaEval c Φ x| ^ κ := by
      intro n
      by_contra hcon
      push_neg at hcon
      refine hbadEv ?_
      filter_upwards [Metric.ball_mem_nhds y (by positivity : (0 : ℝ) < 1 / (n + 1))]
        with x hx
      have hxd : dist x y < 1 / (n + 1) := by simpa [Metric.mem_ball] using hx
      have hle : |eaEval c Φ x| ^ κ
          ≤ ‖fderiv ℝ (fun z : Fin (k + 1) → ℝ => eaEval c Φ z) x‖ := hcon x hxd
      simpa using hle
    choose x hx using hbad_pts
    -- ## Step 2: the sum-of-squares bad inequality at every bad point
    have hxsq : ∀ n : ℕ, (∑ i : Fin (k + 1), (eaEval c (eaD c i Φ) (x n)) ^ 2) ^ q
        < |eaEval c Φ (x n)| ^ (2 * p) := by
      intro n
      have h1 : (∑ i : Fin (k + 1),
            (Work.WilE3.Taylor.grad (fun z : Fin (k + 1) → ℝ => eaEval c Φ z) (x n) i) ^ 2)
          ≤ ‖fderiv ℝ (fun z : Fin (k + 1) → ℝ => eaEval c Φ z) (x n)‖ ^ 2 :=
        Work.WilE3.Taylor.Grad.sumSqGrad_le_norm_fderiv_sq (Work.WilE3.eaEval_analytic c Φ (x n))
      have h2 : (∑ i : Fin (k + 1), (eaEval c (eaD c i Φ) (x n)) ^ 2)
          ≤ ‖fderiv ℝ (fun z : Fin (k + 1) → ℝ => eaEval c Φ z) (x n)‖ ^ 2 := by
        simpa only [grad_eq_eaD] using h1
      have h3 : ‖fderiv ℝ (fun z : Fin (k + 1) → ℝ => eaEval c Φ z) (x n)‖ ^ 2
          < (|eaEval c Φ (x n)| ^ κ) ^ 2 :=
        pow_lt_pow_left₀ (hx n).2 (norm_nonneg _) (by norm_num)
      have h4 : (∑ i : Fin (k + 1), (eaEval c (eaD c i Φ) (x n)) ^ 2) ^ q
          < ((|eaEval c Φ (x n)| ^ κ) ^ 2) ^ q :=
        pow_lt_pow_left₀ (lt_of_le_of_lt h2 h3)
          (Finset.sum_nonneg fun i _ => sq_nonneg _) (by omega)
      have h5 : ((|eaEval c Φ (x n)| ^ κ) ^ 2) ^ q = |eaEval c Φ (x n)| ^ (2 * p) := by
        have hκq : κ * ((2 * q : ℕ) : ℝ) = ((2 * p : ℕ) : ℝ) := by
          rw [hκdef]
          have hqne : (q : ℝ) ≠ 0 := by positivity
          field_simp
          push_cast
          ring
        calc ((|eaEval c Φ (x n)| ^ κ) ^ 2) ^ q
            = (|eaEval c Φ (x n)| ^ κ) ^ ((2 * q : ℕ) : ℝ) := by
              rw [← pow_mul, Real.rpow_natCast]
          _ = |eaEval c Φ (x n)| ^ (κ * ((2 * q : ℕ) : ℝ)) :=
              (Real.rpow_mul (abs_nonneg (eaEval c Φ (x n))) κ _).symm
          _ = |eaEval c Φ (x n)| ^ ((2 * p : ℕ) : ℝ) := by rw [hκq]
          _ = |eaEval c Φ (x n)| ^ (2 * p) := Real.rpow_natCast _ _
      rw [h5] at h4
      exact h4
    -- ## Step 3: a definite sign for the bad points
    have hsign : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ᶠ n in atTop, 0 < σ * eaEval c Φ (x n) := by
      by_cases h : ∃ᶠ n in atTop, 0 < eaEval c Φ (x n)
      · exact ⟨1, Or.inl rfl, by simpa using h⟩
      · push_neg at h
        refine ⟨-1, Or.inr rfl, ?_⟩
        by_contra h2
        push_neg at h2
        have h3 : ∀ᶠ n in atTop, eaEval c Φ (x n) = 0 := by
          filter_upwards [h, h2] with n hn1 hn2
          linarith
        obtain ⟨n, hn⟩ := h3.exists
        have hbn := (hx n).2
        rw [hn, abs_zero, Real.zero_rpow hκ_pos.ne'] at hbn
        exact absurd hbn (not_lt_of_ge (norm_nonneg _))
    obtain ⟨σ, hσ, hσfreq⟩ := hsign
    -- ## Step 4: `Ψ := C σ * Φ` and its bad points
    set Ψ : EAPoly (k + 1) r := MvPolynomial.C σ * Φ with hΨ
    have hΨeval : ∀ z : Fin (k + 1) → ℝ, eaEval c Ψ z = σ * eaEval c Φ z := by
      intro z; rw [hΨ, eaEval_C_mul]
    have hyΨ : eaEval c Ψ y = 0 := by rw [hΨeval, hΦy, mul_zero]
    have hσ2 : σ ^ 2 = 1 := by rcases hσ with h | h <;> rw [h] <;> norm_num
    have hbadΨ : ∀ ρ : ℝ, 0 < ρ → ∃ z : Fin (k + 1) → ℝ, dist z y < ρ ∧ 0 < eaEval c Ψ z ∧
        (∑ l : Fin (k + 1),
            (Work.WilE3.Taylor.grad (fun w : Fin (k + 1) → ℝ => eaEval c Ψ w) z l) ^ 2) ^ q
          < (eaEval c Ψ z) ^ (2 * p) := by
      intro ρ hρ
      have hρn : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 1) < ρ :=
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (eventually_lt_nhds hρ)
      obtain ⟨n, hnσ, hnρ⟩ := (hσfreq.and_eventually hρn).exists
      have hnρ' : (1 : ℝ) / (n + 1) < ρ := by push_cast; exact hnρ
      refine ⟨x n, lt_trans (hx n).1 hnρ', ?_, ?_⟩
      · rw [hΨeval]; exact hnσ
      · have hleft : (∑ l : Fin (k + 1),
              (Work.WilE3.Taylor.grad (fun w : Fin (k + 1) → ℝ => eaEval c Ψ w) (x n) l) ^ 2)
            = (∑ i : Fin (k + 1), (eaEval c (eaD c i Φ) (x n)) ^ 2) := by
          refine Finset.sum_congr rfl fun l _ => ?_
          rw [grad_eq_eaD, hΨ, eaD_C_mul, eaEval_C_mul, mul_pow, hσ2, one_mul]
        have hright : (eaEval c Ψ (x n)) ^ (2 * p) = |eaEval c Φ (x n)| ^ (2 * p) := by
          rw [hΨeval, mul_pow]
          have hσpow : σ ^ (2 * p) = 1 := by rw [pow_mul, hσ2, one_pow]
          rw [hσpow, one_mul, pow_mul, pow_mul, sq_abs]
        rw [hleft, hright]
        exact hxsq n
    -- ## Step 5: Step A (Lagrange) + Step B (curve selection)
    have hdich := Work.WilE3.Taylor.Grad.badSeqOnPolarSet
      (Φ := fun z : Fin (k + 1) → ℝ => eaEval c Ψ z) (y := y) (p := p) (q := q)
      (Nat.succ_pos k) (fun z => Work.WilE3.eaEval_analytic c Ψ z) hp_lt_q hbadΨ
    obtain ⟨γ, hγan, hγ0, harcdata, hPolar⟩ : ∃ γ : ℝ → Fin (k + 1) → ℝ,
        AnalyticAt ℝ γ 0 ∧ γ 0 = y ∧
        (∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), γ t ≠ y ∧ 0 < eaEval c Ψ (γ t) ∧
          (∑ l : Fin (k + 1),
              (Work.WilE3.Taylor.grad (fun w : Fin (k + 1) → ℝ => eaEval c Ψ w) (γ t) l) ^ 2) ^ q
            < (eaEval c Ψ (γ t)) ^ (2 * p)) ∧ PolarLike c Ψ y γ := by
      rcases hdich with h | h
      · obtain ⟨γ, hγan, hγ0, hprop⟩ := Work.WilE3.Taylor.Grad.arcOnSigma
          (Φ := fun z : Fin (k + 1) → ℝ => eaEval c Ψ z) (y := y) (p := p) (q := q)
          (fun z => Work.WilE3.eaEval_analytic c Ψ z) hyΨ hp_lt_q (fun n => by
            obtain ⟨x₀, hx₁, hx₂, hx₃, hx₄⟩ := h n
            obtain ⟨hxbad, hx₅⟩ := hx₄
            exact ⟨x₀, hx₁, hx₂, hx₃, hxbad, fun i j => by
              have hh := hx₅ i j
              ring_nf at hh ⊢
              linarith⟩)
        refine ⟨γ, hγan, hγ0, ?_, ?_⟩
        · filter_upwards [hprop] with t ht
          obtain ⟨h1, h2, h3, -⟩ := ht
          exact ⟨h1, h2, h3⟩
        · filter_upwards [hprop] with t ht
          obtain ⟨-, -, -, h4⟩ := ht
          intro i j l
          refine det3_eq_zero_of_parallel
            (U := fun m => eaEval c (eaD c m Ψ) (γ t))
            (W := fun m => eaEval c (eaD c m (sqGrad c Ψ)) (γ t))
            (t := γ t - y) ?_ i j l
          intro a b
          have hh := h4 a b
          rw [grad_sqGrad, grad_eq_eaD, grad_sqGrad, grad_eq_eaD] at hh
          ring_nf at hh ⊢
          linarith
      · obtain ⟨γ, hγan, hγ0, hprop⟩ := Work.Taylor.Grad.arcOnSigma2
          (Φ := fun z : Fin (k + 1) → ℝ => eaEval c Ψ z) (y := y) (p := p) (q := q)
          (fun z => Work.WilE3.eaEval_analytic c Ψ z) hp_lt_q h
        refine ⟨γ, hγan, hγ0, ?_, ?_⟩
        · filter_upwards [hprop] with t ht
          obtain ⟨h1, h2, h3, -⟩ := ht
          exact ⟨h1, h2, h3⟩
        · filter_upwards [hprop] with t ht
          obtain ⟨-, -, -, h4⟩ := ht
          intro i j l
          have e1 : (fun m => Work.WilE3.Taylor.grad (fun z : Fin (k + 1) → ℝ =>
                ∑ t : Fin (k + 1),
                  (Work.WilE3.Taylor.grad (fun w : Fin (k + 1) → ℝ => eaEval c Ψ w) z t) ^ 2)
                (γ t) m) = fun m => eaEval c (eaD c m (sqGrad c Ψ)) (γ t) := by
            funext m; exact grad_sqGrad c Ψ (γ t) m
          have e2 : (fun m => Work.WilE3.Taylor.grad (fun z : Fin (k + 1) → ℝ => eaEval c Ψ z)
                (γ t) m) = fun m => eaEval c (eaD c m Ψ) (γ t) := by
            funext m; exact grad_eq_eaD c Ψ (γ t) m
          rw [← e1, ← e2]
          exact h4 i j l
    -- ## Step 6: the order of `Ψ ∘ γ` and the arc crux
    have hposΨ : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < eaEval c Ψ (γ t) := by
      filter_upwards [harcdata] with t ht
      exact ht.2.1
    obtain ⟨m, hm, hord⟩ := exists_pos_order_of_eventually_pos hγan
      (Work.WilE3.eaEval_analytic c Ψ y) hyΨ hγ0 hposΨ
    obtain ⟨i, n, hn, hbound⟩ := hK (k + 1) r c Ψ y γ m hkr hγan hγ0 hm hord hPolar
    -- ## Step 7: the bad inequality at the index `i` of the crux
    have hineq : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (∑ j : Fin (k + 1), (eaEval c (eaD c j Ψ) (γ t)) ^ 2) ^ q
          < (eaEval c Ψ (γ t)) ^ (2 * p) := by
      filter_upwards [harcdata] with t ht
      obtain ⟨-, -, h3⟩ := ht
      have hsum : (∑ j : Fin (k + 1), (eaEval c (eaD c j Ψ) (γ t)) ^ 2)
          = (∑ l : Fin (k + 1),
              (Work.WilE3.Taylor.grad (fun w : Fin (k + 1) → ℝ => eaEval c Ψ w) (γ t) l) ^ 2) :=
        (Finset.sum_congr rfl fun l _ => by rw [grad_eq_eaD]).symm
      rw [hsum]
      exact h3
    have han_i : AnalyticAt ℝ (fun t : ℝ => eaEval c (eaD c i Ψ) (γ t)) 0 :=
      AnalyticAt.comp (x := (0 : ℝ)) (f := γ)
        (g := fun z : Fin (k + 1) → ℝ => eaEval c (eaD c i Ψ) z)
        (Work.WilE3.eaEval_analytic c (eaD c i Ψ) (γ 0)) hγan
    have han_G : AnalyticAt ℝ (fun t : ℝ => eaEval c Ψ (γ t)) 0 :=
      AnalyticAt.comp (x := (0 : ℝ)) (f := γ) (g := fun z : Fin (k + 1) → ℝ => eaEval c Ψ z)
        (Work.WilE3.eaEval_analytic c Ψ (γ 0)) hγan
    have hbad_i : p * m ≤ q * n :=
      Work.Taylor.Grad.order_le_of_sumsq_pow_lt
        (F := fun j : Fin (k + 1) => fun t : ℝ => eaEval c (eaD c j Ψ) (γ t))
        (G := fun t : ℝ => eaEval c Ψ (γ t)) (i := i) han_i han_G hn hord hposΨ hineq
    -- ## Step 8: the arithmetic contradiction
    have hAle : K.eval (atomDeg Ψ) ≤ A := by
      rw [hA]; exact Polynomial.eval_le_eval (atomDeg_C_mul_le σ Φ)
    have h1 : (A + 1) * m ≤ (A + 2) * n := by
      have hh := hbad_i
      rw [hp, hq] at hh
      exact hh
    have hchain : (K.eval (atomDeg Ψ) + 1) * ((A + 1) * m)
        ≤ (A + 2) * (K.eval (atomDeg Ψ) * m) := by
      calc (K.eval (atomDeg Ψ) + 1) * ((A + 1) * m)
          ≤ (K.eval (atomDeg Ψ) + 1) * ((A + 2) * n) := Nat.mul_le_mul_left _ h1
        _ = (A + 2) * ((K.eval (atomDeg Ψ) + 1) * n) := by ring
        _ ≤ (A + 2) * (K.eval (atomDeg Ψ) * m) := Nat.mul_le_mul_left _ hbound
    have hfin : (K.eval (atomDeg Ψ) + 1) * (A + 1) ≤ (A + 2) * K.eval (atomDeg Ψ) := by
      refine Nat.le_of_mul_le_mul_right ?_ hm
      calc (K.eval (atomDeg Ψ) + 1) * (A + 1) * m
          = (K.eval (atomDeg Ψ) + 1) * ((A + 1) * m) := by ring
        _ ≤ (A + 2) * (K.eval (atomDeg Ψ) * m) := hchain
        _ = ((A + 2) * K.eval (atomDeg Ψ)) * m := by ring
    have hcontra : (A : ℤ) + 1 ≤ ((K.eval (atomDeg Ψ) : ℕ) : ℤ) := by
      have hcast : (((K.eval (atomDeg Ψ) + 1) * (A + 1) : ℕ) : ℤ)
          ≤ (((A + 2) * K.eval (atomDeg Ψ) : ℕ) : ℤ) := by exact_mod_cast hfin
      push_cast at hcast
      nlinarith
    have hAleZ : ((K.eval (atomDeg Ψ) : ℕ) : ℤ) ≤ (A : ℤ) := by exact_mod_cast hAle
    omega

end Work.WilE3.Taylor.Grad
