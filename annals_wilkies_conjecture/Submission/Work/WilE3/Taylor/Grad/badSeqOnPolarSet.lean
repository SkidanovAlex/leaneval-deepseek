import Mathlib
import Submission.Work.WilE3.Taylor.Grad.badMin_of_gradFails
import Submission.Work.WilE3.Taylor.Grad.lagrangeOfInteriorMin
import Submission.Work.WilE3.Taylor.Grad.lagrangeOfBoundaryMin
import Submission.Work.WilE3.Taylor.Polar.Basic

set_option autoImplicit false

namespace Work.WilE3.Taylor.Grad

open Classical Topology Filter

set_option linter.unusedVariables false

/-!
  annals_wilkies_conjecture, AREA E3 / Taylor / Grad: the **bad sequence on the polar set**.

  This is the "Step B" (Lagrange) input of the gradient-polar argument: given an analytic `Φ` whose
  gradient inequality `(‖∇Φ‖²)^q ≥ (Φ)^{2p}` fails arbitrarily close to `y` in the strong sense
  that there are points `x` with `Φ x > 0` and `(‖∇Φ x‖²)^q < (Φ x)^{2p}` in every ball around `y`,
  there is a sequence of such "bad" points tending to `y` along which *either* the two gradients
  `∇Φ` and `∇‖∇Φ‖²` are parallel (the points lie on the *sigma locus* of `Φ`), *or* the three
  vectors `∇‖∇Φ‖²`, `∇Φ` and `x - y` are linearly dependent (the points lie on the *radial polar
  set* of `Φ` about `y`).  The two alternatives are exactly the hypotheses of
  `Work.WilE3.Taylor.Grad.arcOnSigma` and `Work.WilE3.Taylor.Grad.arcOnPolarSet`.

  ## The construction

  Fix a radius `r > 0`.  Choose a bad point `x₀ ≠ y` with `dist x₀ y` small compared with `r`
  (this is possible: if `y` itself is bad, then the bad locus is an *open* neighbourhood of `y`, and
  `k ≥ 1` lets us move away from `y` inside it), and let `c = ∑ᵢ (x₀ᵢ - yᵢ)² > 0`.

  Minimise `G := ∑ₗ (∂ₗ Φ)²` over the compact set

      `S = {z | Φ z = Φ x₀}  ∩  {z | ∑ᵢ (zᵢ - yᵢ)² = c}`

  — the level set of `Φ` through `x₀`, cut by the *smooth* Euclidean sphere about `y` (not the
  metric sphere: the constraint function must be differentiable, and its gradient `2 (z - y)` is
  what makes the third row `x - y` appear in the determinant).  A minimiser `v ∈ S` is again bad
  (`Φ v = Φ x₀` and `G v ≤ G x₀`), and it is automatically `≠ y` since `c > 0`.  At `v`:

  * if `∇Φ v = 0`, then all the `2 × 2` minors of `(∇Φ v, ∇G v)` vanish trivially: first alternative;
  * if `∇Φ v ≠ 0` and some `2 × 2` minor of `(∇Φ v, v - y)` is non-zero, then the two constraints
    `Φ` and `∑ᵢ (·ᵢ - yᵢ)²` have independent gradients at `v`, so the Lagrange multiplier theorem
    (`Work.WilE3.Taylor.Grad.lagrangeOfBoundaryMin`) exhibits `∇G v = a ∇Φ v + b (v - y)`: the
    determinant of the three rows vanishes, second alternative;
  * if `∇Φ v ≠ 0` but all the `2 × 2` minors of `(∇Φ v, v - y)` vanish, then `∇Φ v` and `v - y` are
    linearly dependent (`Work.WilE3.Taylor.minors_eq_zero_iff`), so again the determinant vanishes:
    second alternative.

  The sequence of alternatives for the radii `r = 1/(n+1)` is turned into a *uniform* alternative by
  the usual pigeonhole: if no `r₀`-ball about `y` contains a first-alternative witness, then the
  witnesses produced at radius `min (1/(n+1)) r₀` must all satisfy the second alternative.
-/

/-! ## Elementary helpers -/

/-- The `3 × 3` determinant of the vectors `u`, `w`, `t` in the coordinates `i j l` (expanded along
the first row).  The second alternative of the target is `det3 (∇G) (∇Φ) (x - y) i j l = 0` for all
`i j l`. -/
def det3 {k : ℕ} (u w t : Fin k → ℝ) (i j l : Fin k) : ℝ :=
  u i * (w j * t l - w l * t j) - u j * (w i * t l - w l * t i) + u l * (w i * t j - w j * t i)

/-- The determinant vanishes when the first row is a linear combination of the other two. -/
lemma det3_eq_zero_of_lin {k : ℕ} {u w t : Fin k → ℝ} {a b : ℝ}
    (h : ∀ i, u i = a * w i + b * t i) : ∀ i j l, det3 u w t i j l = 0 := by
  intro i j l
  simp only [det3]
  rw [h i, h j, h l]
  ring

/-- The determinant vanishes when the second and third rows are proportional. -/
lemma det3_eq_zero_of_mid {k : ℕ} {u w t : Fin k → ℝ} {c : ℝ}
    (h : ∀ i, w i = c * t i) : ∀ i j l, det3 u w t i j l = 0 := by
  intro i j l
  simp only [det3]
  rw [h i, h j, h l]
  ring

/-- The determinant vanishes when the second and third rows are proportional (other direction). -/
lemma det3_eq_zero_of_right {k : ℕ} {u w t : Fin k → ℝ} {d : ℝ}
    (h : ∀ i, t i = d * w i) : ∀ i j l, det3 u w t i j l = 0 := by
  intro i j l
  simp only [det3]
  rw [h i, h j, h l]
  ring

/-- On `Fin k → ℝ` (sup norm) the norm is at most the Euclidean norm. -/
lemma norm_le_sqrt_sumSq {k : ℕ} (v : Fin k → ℝ) : ‖v‖ ≤ Real.sqrt (∑ i, v i ^ 2) := by
  rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
  intro i
  rw [Real.norm_eq_abs]
  calc |v i| = Real.sqrt (v i ^ 2) := by rw [Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt (∑ j, v j ^ 2) :=
        Real.sqrt_le_sqrt (Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i))

/-- The square of the sup norm is at most the sum of the squares of the coordinates. -/
lemma sq_norm_le_sumSq {k : ℕ} (v : Fin k → ℝ) : ‖v‖ ^ 2 ≤ ∑ i, v i ^ 2 := by
  have h := norm_le_sqrt_sumSq v
  have h1 : ‖v‖ ^ 2 ≤ (Real.sqrt (∑ i, v i ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  rwa [Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)] at h1

/-- The sum of the squares of the coordinates is at most `k` times the square of the sup norm. -/
lemma sumSq_le_card_mul_sq_norm {k : ℕ} (v : Fin k → ℝ) : ∑ i, v i ^ 2 ≤ k * ‖v‖ ^ 2 := by
  have h : ∀ i : Fin k, v i ^ 2 ≤ ‖v‖ ^ 2 := by
    intro i
    have hh := norm_le_pi_norm v i
    rw [Real.norm_eq_abs] at hh
    have h2 : |v i| ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hh 2
    rwa [sq_abs] at h2
  calc ∑ i, v i ^ 2 ≤ ∑ _i : Fin k, ‖v‖ ^ 2 := Finset.sum_le_sum (fun i _ => h i)
    _ = k * ‖v‖ ^ 2 := by simp [Finset.sum_const, Finset.card_univ]

/-! ## The theorem -/

theorem badSeqOnPolarSet {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {y : Fin k → ℝ} {p q : ℕ}
    (hk : 0 < k)
    (hΦ : ∀ x, AnalyticAt ℝ Φ x) (hpq : p < q)
    (hbad : ∀ ρ : ℝ, 0 < ρ → ∃ x : Fin k → ℝ, dist x y < ρ ∧ 0 < Φ x ∧
      (∑ l, (Work.WilE3.Taylor.grad Φ x l) ^ 2) ^ q < (Φ x) ^ (2 * p)) :
    (∀ n : ℕ, ∃ x : Fin k → ℝ, x ≠ y ∧ dist x y < 1 / (n + 1) ∧ 0 < Φ x ∧
      (∑ l, (Work.WilE3.Taylor.grad Φ x l) ^ 2) ^ q < (Φ x) ^ (2 * p) ∧
      (∀ i j : Fin k,
        Work.WilE3.Taylor.grad (fun z => ∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) x i *
            Work.WilE3.Taylor.grad Φ x j
          - Work.WilE3.Taylor.grad (fun z => ∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2) x j *
            Work.WilE3.Taylor.grad Φ x i = 0))
    ∨
    (∀ n : ℕ, ∃ x : Fin k → ℝ, x ≠ y ∧ dist x y < 1 / (n + 1) ∧ 0 < Φ x ∧
      (∑ l, (Work.WilE3.Taylor.grad Φ x l) ^ 2) ^ q < (Φ x) ^ (2 * p) ∧
      (∀ i j l : Fin k,
        Work.WilE3.Taylor.grad (fun z => ∑ t, (Work.WilE3.Taylor.grad Φ z t) ^ 2) x i *
            (Work.WilE3.Taylor.grad Φ x j * (x l - y l) - Work.WilE3.Taylor.grad Φ x l * (x j - y j))
          - Work.WilE3.Taylor.grad (fun z => ∑ t, (Work.WilE3.Taylor.grad Φ z t) ^ 2) x j *
            (Work.WilE3.Taylor.grad Φ x i * (x l - y l) - Work.WilE3.Taylor.grad Φ x l * (x i - y i))
          + Work.WilE3.Taylor.grad (fun z => ∑ t, (Work.WilE3.Taylor.grad Φ z t) ^ 2) x l *
            (Work.WilE3.Taylor.grad Φ x i * (x j - y j) - Work.WilE3.Taylor.grad Φ x j * (x i - y i))
          = 0)) := by
  classical
  have hΦcont : Continuous Φ := continuous_iff_continuousAt.mpr fun z => (hΦ z).continuousAt
  have hG0 : Continuous fun z : Fin k → ℝ => ∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2 := by
    refine continuous_finsetSum _ fun l _ => ?_
    exact (continuous_iff_continuousAt.mpr fun z =>
      (analyticAt_grad_comp hΦ l z).continuousAt).pow 2
  set G : (Fin k → ℝ) → ℝ := fun z => ∑ l, (Work.WilE3.Taylor.grad Φ z l) ^ 2 with hG
  have hGcont : Continuous G := by rw [hG]; exact hG0
  -- ## Step 1: bad points arbitrarily close to `y`, and different from `y`
  have hbad' : ∀ ρ : ℝ, 0 < ρ → ∃ x : Fin k → ℝ, x ≠ y ∧ dist x y < ρ ∧ 0 < Φ x ∧
      (G x) ^ q < (Φ x) ^ (2 * p) := by
    intro ρ hρ
    obtain ⟨x₀, hx₀d, hx₀p, hx₀b⟩ := hbad ρ hρ
    by_cases hx₀ : x₀ = y
    · -- `y` itself is bad, so the bad locus is an open neighbourhood of `y`; move away from `y`
      rw [hx₀] at hx₀p hx₀b
      have hopen : IsOpen {z : Fin k → ℝ | 0 < Φ z ∧ (G z) ^ q < (Φ z) ^ (2 * p)} :=
        (isOpen_lt continuous_const hΦcont).inter
          (isOpen_lt (hGcont.pow q) (hΦcont.pow (2 * p)))
      obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hopen y ⟨hx₀p, hx₀b⟩
      set i : Fin k := ⟨0, hk⟩ with hi
      set u : Fin k → ℝ := Pi.single i 1 with hu
      have hu_ne : u ≠ 0 := by
        intro h
        have h1 := congrFun h i
        simp [hu] at h1
      set t : ℝ := (min ε ρ / 2) / (‖u‖ + 1) with ht
      have hden : (‖u‖ + 1 : ℝ) ≠ 0 := by positivity
      have htpos : 0 < t := by
        rw [ht]
        exact div_pos (by positivity) (by positivity)
      set z : Fin k → ℝ := y + t • u with hz
      have hzdist : dist z y < min ε ρ := by
        have hnorm : ‖t • u‖ = t * ‖u‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
        have hb : t * ‖u‖ < min ε ρ := by
          have h1 : t * ‖u‖ ≤ t * (‖u‖ + 1) := by
            have := norm_nonneg u
            nlinarith
          have h2 : t * (‖u‖ + 1) = min ε ρ / 2 := by
            rw [ht]
            exact div_mul_cancel₀ _ hden
          rw [h2] at h1
          have hδpos : (0 : ℝ) < min ε ρ := lt_min hε hρ
          linarith
        rw [hz, dist_eq_norm, add_sub_cancel_left, hnorm]
        exact hb
      have hzne : z ≠ y := by
        intro hzy
        have h2 : y + t • u = y + 0 := by rw [add_zero, ← hz]; exact hzy
        have h3 : t • u = 0 := add_left_cancel h2
        rcases smul_eq_zero.mp h3 with h | h
        · exact absurd h htpos.ne'
        · exact absurd h hu_ne
      have hzmem : z ∈ Metric.ball y ε := by
        rw [Metric.mem_ball]
        exact lt_of_lt_of_le hzdist (min_le_left _ _)
      obtain ⟨hz1, hz2⟩ := hεsub hzmem
      exact ⟨z, hzne, lt_of_lt_of_le hzdist (min_le_right _ _), hz1, hz2⟩
    · exact ⟨x₀, hx₀, hx₀d, hx₀p, hx₀b⟩
  -- ## Step 2: at every scale, a witness satisfying one of the two alternatives
  have hwit : ∀ r : ℝ, 0 < r → ∃ x : Fin k → ℝ, x ≠ y ∧ dist x y < r ∧ 0 < Φ x ∧
      (G x) ^ q < (Φ x) ^ (2 * p) ∧
      ((∀ i j : Fin k, grad G x i * grad Φ x j - grad G x j * grad Φ x i = 0) ∨
        (∀ i j l : Fin k, det3 (grad G x) (grad Φ x) (x - y) i j l = 0)) := by
    intro r hr
    -- a bad point `x₀ ≠ y` with small Euclidean distance to `y`
    obtain ⟨x₀, hx₀ne, hx₀d, hx₀Φ, hx₀bad⟩ :=
      hbad' (r / (Real.sqrt k + 1)) (by positivity)
    set c : ℝ := ∑ i, (x₀ i - y i) ^ 2 with hc
    have hcpos : 0 < c := by
      obtain ⟨i, hi⟩ : ∃ i : Fin k, x₀ i - y i ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hx₀ne (funext fun i => sub_eq_zero.mp (hcon i))
      rw [hc]
      exact Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨i, Finset.mem_univ i, sq_pos_of_ne_zero hi⟩
    have hsumSqCont : Continuous fun z : Fin k → ℝ => ∑ i, (z i - y i) ^ 2 := by
      apply continuous_finsetSum
      intro i _
      exact ((continuous_apply i).sub continuous_const).pow 2
    -- the constraint set: level set of `Φ` through `x₀`, cut by the Euclidean sphere about `y`
    set S : Set (Fin k → ℝ) :=
      {z | Φ z = Φ x₀} ∩ {z | ∑ i, (z i - y i) ^ 2 = c} with hS
    have hSclosed : IsClosed S := by
      rw [hS]
      exact (isClosed_eq hΦcont continuous_const).inter
        (isClosed_eq hsumSqCont continuous_const)
    have hScpt : IsCompact S := by
      refine (isCompact_closedBall y (Real.sqrt c)).of_isClosed_subset hSclosed ?_
      intro z hz
      rw [Metric.mem_closedBall, dist_eq_norm]
      have h3 : ‖z - y‖ ^ 2 ≤ c := by
        calc ‖z - y‖ ^ 2 ≤ ∑ i, (z i - y i) ^ 2 := by
              simpa [Pi.sub_apply] using sq_norm_le_sumSq (z - y)
          _ = c := hz.2
      have h5 : Real.sqrt (‖z - y‖ ^ 2) ≤ Real.sqrt c := Real.sqrt_le_sqrt h3
      rwa [Real.sqrt_sq (norm_nonneg _)] at h5
    have hSne : S.Nonempty := ⟨x₀, rfl, hc.symm⟩
    obtain ⟨v, hvS, hvmin⟩ := hScpt.exists_isMinOn hSne hGcont.continuousOn
    have hvS1 : Φ v = Φ x₀ := hvS.1
    have hvS2 : (∑ i, (v i - y i) ^ 2) = c := hvS.2
    have hvΦpos : 0 < Φ v := by rw [hvS1]; exact hx₀Φ
    have hGvle : G v ≤ G x₀ := hvmin ⟨rfl, hc.symm⟩
    have hvbad : (G v) ^ q < (Φ v) ^ (2 * p) := by
      have hGvnn : (0 : ℝ) ≤ G v := by
        rw [hG]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
      have h1 : (G v) ^ q ≤ (G x₀) ^ q := pow_le_pow_left₀ hGvnn hGvle q
      calc (G v) ^ q ≤ (G x₀) ^ q := h1
        _ < (Φ x₀) ^ (2 * p) := hx₀bad
        _ = (Φ v) ^ (2 * p) := by rw [hvS1]
    have hvne : v ≠ y := by
      intro hvy
      have : c = 0 := by rw [← hvS2, hvy]; simp
      exact absurd this hcpos.ne'
    -- the size estimate: `dist v y < r`
    have hvdist : dist v y < r := by
      have h2 : dist v y ≤ Real.sqrt c := by
        rw [dist_eq_norm]
        have h3 : ‖v - y‖ ^ 2 ≤ c := by
          calc ‖v - y‖ ^ 2 ≤ ∑ i, (v i - y i) ^ 2 := by
                simpa [Pi.sub_apply] using sq_norm_le_sumSq (v - y)
            _ = c := hvS2
        have h5 : Real.sqrt (‖v - y‖ ^ 2) ≤ Real.sqrt c := Real.sqrt_le_sqrt h3
        rwa [Real.sqrt_sq (norm_nonneg _)] at h5
      have h5 : Real.sqrt c ≤ Real.sqrt k * dist x₀ y := by
        have hcsq : c ≤ k * (dist x₀ y) ^ 2 := by
          rw [hc]
          have hterm : ∀ i : Fin k, (x₀ i - y i) ^ 2 ≤ (dist x₀ y) ^ 2 := by
            intro i
            have hh : |x₀ i - y i| ≤ dist x₀ y := by
              have hh' := norm_le_pi_norm (x₀ - y) i
              rw [Real.norm_eq_abs] at hh'
              simpa [dist_eq_norm, Pi.sub_apply] using hh'
            have h2 := pow_le_pow_left₀ (abs_nonneg _) hh 2
            rwa [sq_abs] at h2
          calc ∑ i, (x₀ i - y i) ^ 2 ≤ ∑ _i : Fin k, (dist x₀ y) ^ 2 :=
                Finset.sum_le_sum (fun i _ => hterm i)
            _ = k * (dist x₀ y) ^ 2 := by simp [Finset.sum_const, Finset.card_univ]
        calc Real.sqrt c ≤ Real.sqrt (k * (dist x₀ y) ^ 2) := Real.sqrt_le_sqrt hcsq
          _ = Real.sqrt k * dist x₀ y := by
              rw [Real.sqrt_mul (Nat.cast_nonneg k), Real.sqrt_sq dist_nonneg]
      have h6 : Real.sqrt k * dist x₀ y < r := by
        have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by exact_mod_cast hk)
        have hden : 0 < Real.sqrt k + 1 := by linarith
        have hfrac : Real.sqrt k / (Real.sqrt k + 1) < 1 := by
          rw [div_lt_one hden]; linarith [Real.sqrt_nonneg (k : ℝ)]
        have hprod : Real.sqrt k * (r / (Real.sqrt k + 1)) < r := by
          calc Real.sqrt k * (r / (Real.sqrt k + 1))
              = (Real.sqrt k / (Real.sqrt k + 1)) * r := by ring
            _ < 1 * r := mul_lt_mul_of_pos_right hfrac hr
            _ = r := one_mul r
        calc Real.sqrt k * dist x₀ y < Real.sqrt k * (r / (Real.sqrt k + 1)) :=
              mul_lt_mul_of_pos_left hx₀d hsk
          _ < r := hprod
      exact lt_of_le_of_lt h2 (lt_of_le_of_lt h5 h6)
    -- ## the classification at the minimiser
    have hclass :
        (∀ i j : Fin k, grad G v i * grad Φ v j - grad G v j * grad Φ v i = 0) ∨
          (∀ i j l : Fin k, det3 (grad G v) (grad Φ v) (v - y) i j l = 0) := by
      by_cases hg0 : grad Φ v = 0
      · -- a critical point of `Φ`: the gradients are trivially parallel
        left
        intro i j
        rw [show grad Φ v i = 0 by rw [hg0]; rfl,
          show grad Φ v j = 0 by rw [hg0]; rfl]
        ring
      · by_cases hdep : ∃ i j : Fin k,
            grad Φ v i * (v j - y j) - grad Φ v j * (v i - y i) ≠ 0
        · -- two independent active constraints: Lagrange gives `∇G v ∈ span{∇Φ v, v - y}`
          right
          have hcrit : ∀ z : Fin k → ℝ, Φ z = Φ v →
              (∑ i, (z i - y i) ^ 2) = (∑ i, (v i - y i) ^ 2) →
              (∑ l, (grad Φ v l) ^ 2) ≤ (∑ l, (grad Φ z l) ^ 2) := by
            intro z hz hzc
            have hzS : z ∈ S := by
              refine ⟨?_, ?_⟩
              · show Φ z = Φ x₀
                rw [hz, hvS1]
              · show (∑ i, (z i - y i) ^ 2) = c
                rw [hzc, hvS2]
            have h := hvmin hzS
            simpa [hG] using h
          obtain ⟨a, b, hab⟩ :=
            lagrangeOfBoundaryMin (Φ := Φ) (u := v) (y := y) hΦ hg0 hdep hcrit
          have hab' : ∀ i : Fin k, grad G v i = a * grad Φ v i + b * (v i - y i) :=
            fun i => hab i
          exact det3_eq_zero_of_lin hab'
        · -- otherwise `∇Φ v` and `v - y` are linearly dependent
          right
          push_neg at hdep
          have hdep' : ∀ i j : Fin k, grad Φ v i * (v - y) j - grad Φ v j * (v - y) i = 0 := by
            intro i j
            simpa [Pi.sub_apply] using hdep i j
          rcases (minors_eq_zero_iff (grad Φ v) (v - y)).mp hdep' with ⟨c₁, hc₁⟩ | ⟨d, hd⟩
          · have hc₁' : ∀ i : Fin k, grad Φ v i = c₁ * (v - y) i :=
              fun i => by simpa [Pi.smul_apply, smul_eq_mul] using congrFun hc₁ i
            exact det3_eq_zero_of_mid hc₁'
          · have hd' : ∀ i : Fin k, (v - y) i = d * grad Φ v i :=
              fun i => by simpa [Pi.smul_apply, smul_eq_mul] using congrFun hd i
            exact det3_eq_zero_of_right hd'
    exact ⟨v, hvne, hvdist, hvΦpos, hvbad, hclass⟩
  -- ## Step 3: the pigeonhole
  by_cases hA : ∀ r : ℝ, 0 < r → ∃ x : Fin k → ℝ, x ≠ y ∧ dist x y < r ∧ 0 < Φ x ∧
      (G x) ^ q < (Φ x) ^ (2 * p) ∧
      (∀ i j : Fin k, grad G x i * grad Φ x j - grad G x j * grad Φ x i = 0)
  · left
    intro n
    obtain ⟨x, hxne, hxd, hxΦ, hxbd, hxA⟩ := hA (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨x, hxne, hxd, hxΦ, hxbd, hxA⟩
  · right
    have hA' : ∃ r : ℝ, 0 < r ∧ ∀ x : Fin k → ℝ, x ≠ y → dist x y < r → 0 < Φ x →
        (G x) ^ q < (Φ x) ^ (2 * p) →
        ¬ (∀ i j : Fin k, grad G x i * grad Φ x j - grad G x j * grad Φ x i = 0) := by
      by_contra hcon
      push_neg at hcon
      exact hA hcon
    obtain ⟨ρ₀, hρ₀, hA₀⟩ := hA'
    intro n
    obtain ⟨x, hxne, hxd, hxΦ, hxbd, hxAB⟩ :=
      hwit (min (1 / ((n : ℝ) + 1)) ρ₀) (by positivity)
    refine ⟨x, hxne, ?_, hxΦ, hxbd, ?_⟩
    · exact lt_of_lt_of_le hxd (min_le_left _ _)
    · rcases hxAB with h | h
      · exact absurd h (hA₀ x hxne (lt_of_lt_of_le hxd (min_le_right _ _)) hxΦ hxbd)
      · simpa only [det3, Pi.sub_apply] using h

end Work.WilE3.Taylor.Grad
