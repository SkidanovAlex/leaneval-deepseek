import Mathlib
import Submission.Work.WilkiesH.Interp.poly_comp_taylor_bound
import Submission.Work.WilkiesH.Interp.taylor_diag_bound_per_order

/-!
# Taylor bound for a polynomial composed with a chart, with *per-order* jet bounds

This is the per-order refinement of `Interp.poly_comp_taylor_bound`: the jets of `P ∘ ψ` at `t₀`
are bounded *order by order* (`‖D^j (P ∘ ψ)(t₀)(t - t₀)^j‖ ≤ β j * ‖t - t₀‖^j`), and the Taylor
part of the bound is correspondingly the sum `∑_{j ≤ b} β j * ‖t - t₀‖^j / j!`.  The remainder
estimate is unchanged from the sharp chain-rule bound

`|(P ∘ ψ)^{(b+1)}(ξ)| ≤ (∑ m ∈ P.support, |P.coeff m|) · (totalDegree P + 1)^{b+1}
   · (max 1 ‖t - t₀‖)^{b+1} · ‖t - t₀‖^{b+1}`,

so the same factor `(max 1 ‖t - t₀‖)^{b+1} · ‖t - t₀‖^{b+1}` appears in the conclusion.

This per-order form is what the Siegel–Wilkie interpolation step consumes: the jet bound
produced by the approximate Siegel lemma is itself order-dependent
(`|D^j F(t₀)(v^j)| ≤ ρ^{b-j}·√monoCount·d^j·μ^j·‖v‖^j`), and only the sum
`∑_j ((√μ)^{3j} d^j)/j!` — with its factorial — stays within the numerical budget.
-/

namespace Work.WilkiesH.Interp

theorem poly_comp_taylor_per_order {μ b : ℕ} {U : Set (Fin μ → ℝ)}
    (hU : IsOpen U) (hconv : Convex ℝ U)
    {ψ : (Fin μ → ℝ) → (Fin (μ + 1) → ℝ)} (hψ : ContDiffOn ℝ (b + 1 : ℕ) ψ U)
    (hψjet : ∀ k, k ≤ b + 1 → ∀ t ∈ U, ‖iteratedFDeriv ℝ k ψ t‖ ≤ 1)
    (hψval : ∀ t ∈ U, ∀ i, |ψ t i| ≤ 1)
    (P : MvPolynomial (Fin (μ + 1)) ℝ) {t₀ t : Fin μ → ℝ} (ht₀ : t₀ ∈ U) (ht : t ∈ U)
    {β : ℕ → ℝ}
    (hjet : ∀ j, j ≤ b →
      ‖iteratedFDeriv ℝ j (fun s => P.eval (ψ s)) t₀ (fun _ => t - t₀)‖ ≤ β j * ‖t - t₀‖ ^ j) :
    |P.eval (ψ t)| ≤ (∑ j ∈ Finset.range (b + 1),
        β j * ‖t - t₀‖ ^ j / (((j.factorial : ℕ) : ℝ)))
      + (∑ m ∈ P.support, |P.coeff m|) * (((P.totalDegree : ℕ) : ℝ) + 1) ^ (b + 1)
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
  -- Taylor's theorem with Lagrange remainder, with the per-order jet bounds
  have hmain := taylor_diag_bound_per_order (F := fun s => P.eval (ψ s)) (U := U)
      (b := b) (x := t₀) (y := t) hU hconv hF ht₀ ht
      (fun j hj => hjet j hj) hRbd
  simpa only [hr, hA, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using hmain

end Work.WilkiesH.Interp
