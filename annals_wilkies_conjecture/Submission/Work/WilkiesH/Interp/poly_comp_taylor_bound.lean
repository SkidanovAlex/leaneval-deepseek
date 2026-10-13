import Mathlib
import Submission.Work.WilkiesH.Interp.taylor_diag_bound_le
import Submission.Work.WilkiesH.Interp.taylor_diag_bound_sharp
import Submission.Work.WilkiesH.Interp.iteratedDeriv_prod_bound_sharp
import Submission.Work.WilkiesH.Interp.iteratedDeriv_eval_eq_sum

/-!
# Taylor bound for a polynomial composed with a chart

This file proves `poly_comp_taylor_bound`: the Taylor expansion of `s ↦ P (ψ s)` at a point `t₀`
up to order `b`, with an explicit remainder estimate in the spirit of Binyamini–Novikov–Zak,
*Wilkie's conjecture for Pfaffian structures*.

The single-jet hypothesis bounds the jets of `P ∘ ψ` at `t₀` (evaluated on `t - t₀`), so the
Taylor polynomial itself is bounded by `β * ∑_{j ≤ b} ‖t - t₀‖^j / j!`.  The remainder is bounded
via Lagrange's form of Taylor's theorem together with the sharp chain-rule estimate

`|(P ∘ ψ)^{(b+1)}(ξ)| ≤ (∑ m ∈ P.support, |P.coeff m|) · ((totalDegree P) · ‖t - t₀‖)^{b+1}`,

which is where the factor `(max 1 ‖t - t₀‖)^{b+1} · ‖t - t₀‖^{b+1}` comes from after relaxing the
degree and collecting the `max`-factor needed to make the constant independent of `ξ`.

## Main result

* `poly_comp_taylor_bound`

## Auxiliary results

* `iteratedDeriv_affineCurve_at` — chain rule for `iteratedDeriv` along the affine curve
  `s ↦ x + s • v`.
* `norm_iteratedFDeriv_coord_le` — the jet of a coordinate of `ψ` is bounded by the jet of `ψ`.
* `iteratedDeriv_chart_coord_le` — the `k`-th derivative of `σ ↦ ψ (t₀ + σ • v) i` at `s` is
  bounded by `‖v‖^k`.
* `iteratedDeriv_poly_comp_bound_sharp` — the sharp `j`-th derivative bound for `P ∘ ψ` along a
  curve, using `|ψ^{(k)}| ≤ c^k` rather than `|ψ^{(k)}| ≤ c`.  It uses the sharp product bound
  `iteratedDeriv_prod_bound_sharp` (a separate file) and `iteratedDeriv_eval_eq_sum`.
-/

namespace Work.WilkiesH.Interp

/-- Chain rule for `iteratedDeriv` along the affine curve `s ↦ x + s • v`.

If `F` is `C^n` on the open set `U` and `x + t • v ∈ U`, then for `j ≤ n` the `j`-th iterated
derivative at `t` of the parametrised curve is the `j`-th iterated derivative of `F` at
`x + t • v`, evaluated on the constant vector `v`. -/
theorem iteratedDeriv_affineCurve_at {m N : ℕ} {F : (Fin m → ℝ) → ℝ} {U : Set (Fin m → ℝ)}
    (hU : IsOpen U) (hF : ContDiffOn ℝ (N : ℕ) F U) {x v : Fin m → ℝ} {t : ℝ}
    (ht : x + t • v ∈ U) {j : ℕ} (hj : j ≤ N) :
    iteratedDeriv j (fun s : ℝ => F (x + s • v)) t
      = (iteratedFDeriv ℝ j F (x + t • v)) (fun _ : Fin j => v) := by
  rw [iteratedDeriv, iteratedFDerivAlongLine (n := N) hU hF (i := j) hj ht,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp [ContinuousLinearMap.toSpanSingleton_apply]

/-- The jet of a coordinate of `ψ` is bounded by the jet of `ψ`. -/
theorem norm_iteratedFDeriv_coord_le {μ N : ℕ} {U : Set (Fin μ → ℝ)}
    {ψ : (Fin μ → ℝ) → (Fin (μ + 1) → ℝ)} (hU : IsOpen U) (hψ : ContDiffOn ℝ (N : ℕ) ψ U)
    {s : Fin μ → ℝ} (hs : s ∈ U) {j : ℕ} (hj : j ≤ N) (i : Fin (μ + 1)) :
    ‖iteratedFDeriv ℝ j (fun u => ψ u i) s‖ ≤ ‖iteratedFDeriv ℝ j ψ s‖ := by
  let π : (Fin (μ + 1) → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hπ : ‖π‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound π zero_le_one (fun v => ?_)
    rw [one_mul, ContinuousLinearMap.proj_apply]
    exact norm_le_pi_norm v i
  have hcd : ContDiffAt ℝ (j : ℕ) ψ s :=
    (hψ.contDiffAt (hU.mem_nhds hs)).of_le (by exact_mod_cast hj)
  have hcomp := ContinuousLinearMap.iteratedFDeriv_comp_left π hcd (i := j) le_rfl
  have hfun : (fun u => ψ u i) = π ∘ ψ := by
    funext u; rw [Function.comp_apply, ContinuousLinearMap.proj_apply]
  rw [hfun, hcomp]
  calc ‖π.compContinuousMultilinearMap (iteratedFDeriv ℝ j ψ s)‖
      ≤ ‖π‖ * ‖iteratedFDeriv ℝ j ψ s‖ :=
        ContinuousLinearMap.norm_compContinuousMultilinearMap_le π _
    _ ≤ 1 * ‖iteratedFDeriv ℝ j ψ s‖ := mul_le_mul_of_nonneg_right hπ (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ j ψ s‖ := one_mul _

/-- For a chart `ψ` whose jets of order `≤ N` are bounded by `1` on the open set `U`, the `k`-th
derivative at `s` of the coordinate `σ ↦ ψ (t₀ + σ • v) i` is bounded by `‖v‖^k`. -/
theorem iteratedDeriv_chart_coord_le {μ N : ℕ} {U : Set (Fin μ → ℝ)}
    {ψ : (Fin μ → ℝ) → (Fin (μ + 1) → ℝ)}
    (hU : IsOpen U) (hψ : ContDiffOn ℝ (N : ℕ) ψ U)
    (hψjet : ∀ k, k ≤ N → ∀ t ∈ U, ‖iteratedFDeriv ℝ k ψ t‖ ≤ 1)
    {t₀ v : Fin μ → ℝ} {s : ℝ} (hs : t₀ + s • v ∈ U) (i : Fin (μ + 1)) {k : ℕ} (hk : k ≤ N) :
    |iteratedDeriv k (fun σ : ℝ => ψ (t₀ + σ • v) i) s| ≤ ‖v‖ ^ k := by
  have hψi : ContDiffOn ℝ (N : ℕ) (fun u => ψ u i) U := by
    simpa [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (((ContinuousLinearMap.proj i).contDiff).comp_contDiffOn hψ)
  have hchain := iteratedDeriv_affineCurve_at hU hψi hs hk
  rw [hchain, ← Real.norm_eq_abs]
  calc ‖(iteratedFDeriv ℝ k (fun u => ψ u i) (t₀ + s • v)) (fun _ : Fin k => v)‖
      ≤ ‖iteratedFDeriv ℝ k (fun u => ψ u i) (t₀ + s • v)‖ * (∏ _ : Fin k, ‖v‖) :=
        ContinuousMultilinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ k (fun u => ψ u i) (t₀ + s • v)‖ * ‖v‖ ^ k := by
        simp [Finset.prod_const]
    _ ≤ ‖iteratedFDeriv ℝ k ψ (t₀ + s • v)‖ * ‖v‖ ^ k := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact norm_iteratedFDeriv_coord_le hU hψ hs hk i
    _ ≤ 1 * ‖v‖ ^ k := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact hψjet k hk (t₀ + s • v) hs
    _ = ‖v‖ ^ k := one_mul _

/-- **Sharp derivative bound for a polynomial composed with `C^j` functions.**

If `Ψ i` is `C^j` at `s₀` with `|Ψ i s₀| ≤ 1` and `|Ψ i^{(k)}(s₀)| ≤ c^k` for `1 ≤ k ≤ j`
(no lower bound on `c`), then the `j`-th derivative of `s ↦ P (Ψ s)` at `s₀` is bounded by
`(∑ m ∈ P.support, |P.coeff m|) · (totalDegree P · c)^j`. -/
theorem iteratedDeriv_poly_comp_bound_sharp {n j : ℕ} (P : MvPolynomial (Fin n) ℝ)
    (Ψ : Fin n → ℝ → ℝ) (s₀ : ℝ) {c : ℝ} (hc : 0 ≤ c)
    (hdiff : ∀ i, ContDiffAt ℝ (j : ℕ) (Ψ i) s₀)
    (hval : ∀ i, |Ψ i s₀| ≤ 1)
    (hder : ∀ i, ∀ k, 1 ≤ k → k ≤ j → |iteratedDeriv k (Ψ i) s₀| ≤ c ^ k) :
    |iteratedDeriv j (fun s => P.eval (fun i => Ψ i s)) s₀| ≤
      (∑ m ∈ P.support, |P.coeff m|) * (((P.totalDegree : ℕ) : ℝ) * c) ^ j := by
  rw [iteratedDeriv_eval_eq_sum P Ψ s₀ hdiff]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hb : ∀ m ∈ P.support,
      |P.coeff m * iteratedDeriv j (fun s => ∏ i, (Ψ i s) ^ (m i)) s₀|
        ≤ |P.coeff m| * ((((P.totalDegree : ℕ) : ℝ) * c) ^ j) := by
    intro m hm
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    -- Reindex the monomial as a product over the sigma-type of `m`, of cardinality `∑ i, m i`.
    have hreindex : (fun s : ℝ => ∏ i, (Ψ i s) ^ (m i))
        = fun s => ∏ p : Sigma (fun i : Fin n => Fin (m i)), Ψ p.1 s := by
      funext s
      rw [Fintype.prod_sigma (f := fun p : Sigma (fun i : Fin n => Fin (m i)) => Ψ p.1 s)]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      rw [show (∏ y : Fin (m i), Ψ (⟨i, y⟩ : Sigma (fun i : Fin n => Fin (m i))).1 s)
            = ∏ _y : Fin (m i), Ψ i s from Finset.prod_congr rfl (fun y _ => rfl)]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hreindex]
    have hcard : Fintype.card (Sigma (fun i : Fin n => Fin (m i))) = ∑ i, m i := by
      rw [Fintype.card_sigma]; simp [Fintype.card_fin]
    have hmain := iteratedDeriv_prod_bound_sharp
        (Finset.univ : Finset (Sigma (fun i : Fin n => Fin (m i))))
        (fun p => Ψ p.1) s₀ (c := c) hc (j := j)
        (fun p _ => hdiff p.1) (fun p _ => hval p.1)
        (fun p _ k h1 h2 => hder p.1 k h1 h2) j le_rfl
    refine hmain.trans ?_
    rw [Finset.card_univ, hcard]
    have hle : ((∑ i, m i : ℕ) : ℝ) ≤ ((P.totalDegree : ℕ) : ℝ) := by
      have h2 : (∑ i, m i) ≤ P.totalDegree := by
        rw [← Finsupp.degree_eq_sum]
        exact MvPolynomial.le_totalDegree hm
      exact_mod_cast h2
    apply pow_le_pow_left₀
    · exact mul_nonneg (Nat.cast_nonneg _) hc
    · exact mul_le_mul_of_nonneg_right hle hc
  calc ∑ m ∈ P.support, |P.coeff m * iteratedDeriv j (fun s => ∏ i, (Ψ i s) ^ (m i)) s₀|
      ≤ ∑ m ∈ P.support, |P.coeff m| * ((((P.totalDegree : ℕ) : ℝ) * c) ^ j) :=
        Finset.sum_le_sum hb
    _ = (∑ m ∈ P.support, |P.coeff m|) * ((((P.totalDegree : ℕ) : ℝ) * c) ^ j) := by
        rw [Finset.sum_mul]

theorem poly_comp_taylor_bound {μ b : ℕ} {U : Set (Fin μ → ℝ)}
    (hU : IsOpen U) (hconv : Convex ℝ U)
    {ψ : (Fin μ → ℝ) → (Fin (μ + 1) → ℝ)} (hψ : ContDiffOn ℝ (b + 1 : ℕ) ψ U)
    (hψjet : ∀ k, k ≤ b + 1 → ∀ t ∈ U, ‖iteratedFDeriv ℝ k ψ t‖ ≤ 1)
    (hψval : ∀ t ∈ U, ∀ i, |ψ t i| ≤ 1)
    (P : MvPolynomial (Fin (μ + 1)) ℝ) {t₀ t : Fin μ → ℝ} (ht₀ : t₀ ∈ U) (ht : t ∈ U)
    {β : ℝ} (hβ : 0 ≤ β)
    (hjet : ∀ j ≤ b,
      ‖iteratedFDeriv ℝ j (fun s => P.eval (ψ s)) t₀ (fun _ => t - t₀)‖ ≤ β * ‖t - t₀‖ ^ j) :
    |P.eval (ψ t)| ≤ β * (∑ j ∈ Finset.range (b + 1), ‖t - t₀‖ ^ j / (((j.factorial : ℕ) : ℝ)))
      + (∑ m ∈ P.support, |P.coeff m|) * (((P.totalDegree + 1 : ℕ) : ℝ)) ^ (b + 1)
        * (max 1 ‖t - t₀‖) ^ (b + 1) * ‖t - t₀‖ ^ (b + 1)
        / ((((b + 1).factorial : ℕ) : ℝ)) := by
  set A : ℝ := ∑ m ∈ P.support, |P.coeff m| with hA
  set r : ℝ := ‖t - t₀‖ with hr
  have hA0 : 0 ≤ A := by rw [hA]; exact Finset.sum_nonneg (fun m _ => abs_nonneg _)
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  -- `P ∘ ψ` is `C^{b+1}` on `U`
  have hF : ContDiffOn ℝ (b + 1 : ℕ) (fun s => P.eval (ψ s)) U := by
    have hp : ContDiffOn ℝ (b + 1 : ℕ) (fun y : Fin (μ + 1) → ℝ => P.eval y) Set.univ :=
      (AnalyticOnNhd.eval_mvPolynomial P).contDiffOn uniqueDiffOn_univ
    simpa only [Function.comp_def] using hp.comp hψ (fun s _ => Set.mem_univ s)
  -- the remainder bound on the whole segment
  have hRbd : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDeriv (b + 1) (fun σ : ℝ => P.eval (ψ (t₀ + σ • (t - t₀)))) s| ≤
        A * (((P.totalDegree + 1 : ℕ) : ℝ)) ^ (b + 1) * (max 1 r) ^ (b + 1) * r ^ (b + 1) := by
    intro s hs
    have hsU : t₀ + s • (t - t₀) ∈ U := by
      have hmem : (1 - s) • t₀ + s • t ∈ U :=
        (hconv.starConvex ht₀) ht (by linarith [hs.2]) hs.1 (by ring)
      have heq : t₀ + s • (t - t₀) = (1 - s) • t₀ + s • t := by
        rw [smul_sub, sub_smul, one_smul]; abel
      rw [heq]; exact hmem
    have hdiff : ∀ i, ContDiffAt ℝ (b + 1 : ℕ) (fun σ : ℝ => ψ (t₀ + σ • (t - t₀)) i) s := by
      intro i
      have hψat : ContDiffAt ℝ (b + 1 : ℕ) ψ (t₀ + s • (t - t₀)) :=
        hψ.contDiffAt (hU.mem_nhds hsU)
      fun_prop
    have hval : ∀ i, |ψ (t₀ + s • (t - t₀)) i| ≤ 1 := fun i => hψval _ hsU i
    have hder : ∀ i, ∀ k, 1 ≤ k → k ≤ b + 1 →
        |iteratedDeriv k (fun σ : ℝ => ψ (t₀ + σ • (t - t₀)) i) s| ≤ r ^ k := by
      intro i k _ hk
      have hc := iteratedDeriv_chart_coord_le (N := b + 1) hU hψ hψjet hsU i hk
      simpa only [hr] using hc
    have h2 := iteratedDeriv_poly_comp_bound_sharp (j := b + 1) P
        (fun i σ => ψ (t₀ + σ • (t - t₀)) i) s (c := r) hr0 hdiff hval hder
    -- relax `totalDegree` to `totalDegree + 1` and add the `(max 1 r)` factor
    have hD1 : ((P.totalDegree : ℕ) : ℝ) ≤ ((P.totalDegree + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    have h3 : A * (((P.totalDegree : ℕ) : ℝ) * r) ^ (b + 1)
        ≤ A * (((P.totalDegree + 1 : ℕ) : ℝ)) ^ (b + 1) * (max 1 r) ^ (b + 1) * r ^ (b + 1) := by
      have hinner : (((P.totalDegree : ℕ) : ℝ) * r) ^ (b + 1)
          ≤ (((P.totalDegree + 1 : ℕ) : ℝ)) ^ (b + 1) * (max 1 r) ^ (b + 1) * r ^ (b + 1) := by
        calc (((P.totalDegree : ℕ) : ℝ) * r) ^ (b + 1)
            = ((P.totalDegree : ℕ) : ℝ) ^ (b + 1) * r ^ (b + 1) := by rw [mul_pow]
          _ ≤ (((P.totalDegree + 1 : ℕ) : ℝ)) ^ (b + 1) * r ^ (b + 1) :=
              mul_le_mul_of_nonneg_right
                (pow_le_pow_left₀ (Nat.cast_nonneg _) hD1 _) (by positivity)
          _ ≤ (((P.totalDegree + 1 : ℕ) : ℝ)) ^ (b + 1) * r ^ (b + 1) * (max 1 r) ^ (b + 1) :=
              le_mul_of_one_le_right (by positivity) (one_le_pow₀ (le_max_left 1 r))
          _ = (((P.totalDegree + 1 : ℕ) : ℝ)) ^ (b + 1) * (max 1 r) ^ (b + 1) * r ^ (b + 1) := by
              ring
      exact (mul_le_mul_of_nonneg_left hinner hA0).trans_eq (by ring)
    exact h2.trans h3
  -- Taylor's theorem with Lagrange remainder
  have hmain := taylor_diag_bound_sharp (m := μ) (F := fun s => P.eval (ψ s)) (U := U)
      (b := b) (x := t₀) (y := t) (β := β) hU hconv hF ht₀ ht hβ hjet hRbd
  simpa only [hr, hA] using hmain

end Work.WilkiesH.Interp
