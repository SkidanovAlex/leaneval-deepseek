import Mathlib
import Submission.Work.Diff.C.Setup
import Submission.Work.Diff.C.cap_avoid

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Lemma S: the ray stays in the smooth region, with the model comparison

`Work.Diff.C.ray_model_stay` is the *bootstrap* step of the classical endgame.  Along the geodesic
ray `σ ↦ GExp hmet q (σ • u)` the function `g σ = f (GExp hmet q (σ • u))` is compared with the
model `Md σ = f q · cos σ + ⟪∇f(q), u⟫ · sin σ`.  The hypothesis `hcmp` says: *as long as* `g`
stays above `-1 + c` on `[0,t]`, the model comparison `|g t - Md t| ≤ 2 ε₁ t` holds at `t`.  Since
the model `Md ≥ -1 + 3c` and `2 ε₁ π < c`, the comparison forces `g > -1 + 2c` whenever it applies,
so the condition is self-reproducing: `g` never leaves the region `{f > -1 + c}`, and the estimate
holds on all of `[0,s]`.

The mathematical content is entirely one-dimensional real analysis (a continuity/continuation
argument); it is isolated in `ray_model_bootstrap` below so that `ray_model_stay` only has to supply
the value `g 0 = f q` of the geodesic ray at time `0`.
-/

namespace Work.Diff.C

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

/-- **The one-dimensional bootstrap.**  Let `g` be continuous on `[0,s]`, let the model `Md`
satisfy `Md ≥ -1 + 3c` on `[0,s]`, and assume the model comparison `|g t - Md t| ≤ 2εt` at every
`t ∈ [0,s]` *at which* `g > -1 + c` on the whole of `[0,t]`.  If `2επ < c` and `g 0 > -1 + c`, then
`g > -1 + c` on the whole of `[0,s]`; consequently `g > -1 + 2c` and `|g - Md| ≤ 2εs` on `[0,s]`.

The point of the statement is that the hypothesis `hcmp` is applied *only* on prefixes where the
lower bound is already known; the strictness of the conclusion at every point is what makes the
argument run, and the case `t = 0` is covered by the separate hypothesis `hbase`. -/
theorem ray_model_bootstrap {g Md : ℝ → ℝ} {s c ε : ℝ}
    (hsπ : s ≤ Real.pi) (hc : 0 < c) (hε : 0 ≤ ε) (hεπ : 2 * ε * Real.pi < c)
    (hcont : ContinuousOn g (Set.Icc 0 s))
    (hbase : -1 + c < g 0)
    (htrig : ∀ σ ∈ Set.Icc (0 : ℝ) s, -1 + 3 * c ≤ Md σ)
    (hcmp : ∀ t ∈ Set.Icc (0 : ℝ) s,
      (∀ σ ∈ Set.Icc (0 : ℝ) t, -1 + c < g σ) → |g t - Md t| ≤ 2 * ε * t) :
    (∀ σ ∈ Set.Icc (0 : ℝ) s, -1 + 2 * c < g σ) ∧
    (∀ σ ∈ Set.Icc (0 : ℝ) s, |g σ - Md σ| ≤ 2 * ε * s) := by
  -- the comparison error is always `< c`
  have h2ε : ∀ t ∈ Set.Icc (0 : ℝ) s, 2 * ε * t < c := by
    intro t ht
    have h1 : t ≤ Real.pi := le_trans ht.2 hsπ
    have h2 : 2 * ε * t ≤ 2 * ε * Real.pi :=
      mul_le_mul_of_nonneg_left h1 (by linarith : (0 : ℝ) ≤ 2 * ε)
    linarith
  -- where the comparison applies, `g > -1 + 2c`
  have hstep : ∀ t ∈ Set.Icc (0 : ℝ) s,
      (∀ σ ∈ Set.Icc (0 : ℝ) t, -1 + c < g σ) → -1 + 2 * c < g t := by
    intro t ht hpre
    have h1 := (abs_le.mp (hcmp t ht hpre)).1
    have h2 := htrig t ht
    have h3 := h2ε t ht
    linarith
  -- the heart: `g > -1 + c` on `[0,s]`
  have hgood : ∀ σ ∈ Set.Icc (0 : ℝ) s, -1 + c < g σ := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨σ₁, hσ₁, hσ₁le⟩ := hcon
    -- the closed set of bad times
    set C : Set ℝ := Set.Icc (0 : ℝ) s ∩ g ⁻¹' Set.Iic (-1 + c) with hCdef
    have hCne : C.Nonempty := by
      refine ⟨σ₁, ?_⟩
      rw [hCdef]
      exact ⟨hσ₁, hσ₁le⟩
    have hCclosed : IsClosed C := by
      rw [hCdef]
      exact hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hCbdd : BddBelow C := by
      rw [hCdef]
      exact (bddBelow_Icc (a := s) (b := (0 : ℝ))).mono (fun x hx => hx.1)
    have hmem : sInf C ∈ C := hCclosed.csInf_mem hCne hCbdd
    rw [hCdef] at hmem
    have hσ₀mem : sInf C ∈ Set.Icc (0 : ℝ) s := hmem.1
    have hσ₀le : g (sInf C) ≤ -1 + c := hmem.2
    -- strictly before the first bad time the bound holds
    have hleft : ∀ σ : ℝ, σ ∈ Set.Icc (0 : ℝ) s → σ < sInf C → -1 + c < g σ := by
      intro σ hσ hlt
      by_contra hcon'
      push_neg at hcon'
      have hmem' : σ ∈ C := by
        rw [hCdef]
        exact ⟨hσ, hcon'⟩
      have hle := csInf_le hCbdd hmem'
      linarith
    rcases lt_or_eq_of_le hσ₀mem.1 with hpos | hzero
    · -- `sInf C > 0`: approach `sInf C` from the left
      set d : ℝ := sInf C with hd
      have hdpos : 0 < d := by rw [hd]; exact hpos
      have hdmem : d ∈ Set.Icc (0 : ℝ) s := by rw [hd]; exact hσ₀mem
      have hdle : g d ≤ -1 + c := by rw [hd]; exact hσ₀le
      have hleft_d : ∀ σ : ℝ, σ ∈ Set.Icc (0 : ℝ) s → σ < d → -1 + c < g σ := by
        intro σ hσ hlt
        rw [hd] at hlt
        exact hleft σ hσ hlt
      have hseq_mem : ∀ n : ℕ, d * ((n : ℝ) / ((n : ℝ) + 1)) ∈ Set.Icc (0 : ℝ) s ∧
          d * ((n : ℝ) / ((n : ℝ) + 1)) < d := by
        intro n
        have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        have hfrac_le : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
          rw [div_le_one hn1]; linarith
        have hfrac_lt : (n : ℝ) / ((n : ℝ) + 1) < 1 := by
          rw [div_lt_one hn1]; linarith
        constructor
        · refine ⟨?_, ?_⟩
          · positivity
          · calc d * ((n : ℝ) / ((n : ℝ) + 1)) ≤ d * 1 :=
                mul_le_mul_of_nonneg_left hfrac_le hdpos.le
              _ = d := mul_one d
              _ ≤ s := hdmem.2
        · calc d * ((n : ℝ) / ((n : ℝ) + 1)) < d * 1 :=
              mul_lt_mul_of_pos_left hfrac_lt hdpos
            _ = d := mul_one d
      have hvals : ∀ n : ℕ, -1 + 2 * c ≤ g (d * ((n : ℝ) / ((n : ℝ) + 1))) := by
        intro n
        obtain ⟨hmem_n, hlt_n⟩ := hseq_mem n
        exact (hstep _ hmem_n (fun σ' hσ' =>
          hleft_d σ' ⟨hσ'.1, le_trans hσ'.2 hmem_n.2⟩ (lt_of_le_of_lt hσ'.2 hlt_n))).le
      have htend : Tendsto (fun n : ℕ => d * ((n : ℝ) / ((n : ℝ) + 1))) atTop (𝓝 d) := by
        have h1 : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 1) := by
          simpa using tendsto_natCast_div_add_atTop (x := (1 : ℝ))
        simpa using (tendsto_const_nhds (x := d)).mul h1
      have htend' : Tendsto (fun n : ℕ => d * ((n : ℝ) / ((n : ℝ) + 1))) atTop
          (𝓝[Set.Icc (0 : ℝ) s] d) := by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨htend, Eventually.of_forall (fun n => (hseq_mem n).1)⟩
      have hcw : ContinuousWithinAt g (Set.Icc (0 : ℝ) s) d := by
        rw [hd]; exact hcont.continuousWithinAt hσ₀mem
      have hat : Tendsto (fun n : ℕ => g (d * ((n : ℝ) / ((n : ℝ) + 1)))) atTop (𝓝 (g d)) :=
        hcw.tendsto.comp htend'
      have hle' := le_of_tendsto_of_tendsto'
        (f := fun _ : ℕ => -1 + 2 * c)
        (g := fun n : ℕ => g (d * ((n : ℝ) / ((n : ℝ) + 1))))
        tendsto_const_nhds hat hvals
      linarith
    · -- `sInf C = 0`: then `g 0 ≤ -1 + c`, contradicting `hbase`
      have hzero_le : g 0 ≤ -1 + c := by rw [hzero]; exact hσ₀le
      linarith
  constructor
  · intro σ hσ
    exact hstep σ hσ (fun σ' hσ' => hgood σ' ⟨hσ'.1, le_trans hσ'.2 hσ.2⟩)
  · intro σ hσ
    have h1 := hcmp σ hσ (fun σ' hσ' => hgood σ' ⟨hσ'.1, le_trans hσ'.2 hσ.2⟩)
    have h2 : 2 * ε * σ ≤ 2 * ε * s :=
      mul_le_mul_of_nonneg_left hσ.2 (by linarith : (0 : ℝ) ≤ 2 * ε)
    linarith

theorem ray_model_stay
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M]
    {cov : CovariantDerivative I E (TangentSpace I (M := M))}
    [ContMDiffCovariantDerivative cov ∞]
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    {q : M} {f : M → ℝ} {u : TangentSpace I q} (hu : Inner.inner ℝ u u = 1)
    {s c ε₁ : ℝ} (hs0 : 0 ≤ s) (hsπ : s ≤ Real.pi) (hc : 0 < c) (hε₁ : 0 ≤ ε₁)
    (hεπ : 2 * ε₁ * Real.pi < c)
    (hcont : ContinuousOn (fun σ : ℝ => f (Submission.GlobalExp.GExp (cov := cov) hmet q (σ • u)))
      (Set.Icc 0 s))
    (htrig : ∀ σ ∈ Set.Icc (0 : ℝ) s,
      -1 + 3 * c ≤ f q * Real.cos σ
        + Inner.inner ℝ (rgrad (I := I) (M := M) f q) u * Real.sin σ)
    (hcmp : ∀ t ∈ Set.Icc (0 : ℝ) s,
      (∀ σ ∈ Set.Icc (0 : ℝ) t, -1 + c < f (Submission.GlobalExp.GExp (cov := cov) hmet q (σ • u))) →
      |f (Submission.GlobalExp.GExp (cov := cov) hmet q (t • u))
        - (f q * Real.cos t + Inner.inner ℝ (rgrad (I := I) (M := M) f q) u * Real.sin t)|
        ≤ 2 * ε₁ * t) :
    (∀ σ ∈ Set.Icc (0 : ℝ) s,
      -1 + 2 * c < f (Submission.GlobalExp.GExp (cov := cov) hmet q (σ • u))) ∧
    (∀ σ ∈ Set.Icc (0 : ℝ) s,
      |f (Submission.GlobalExp.GExp (cov := cov) hmet q (σ • u))
        - (f q * Real.cos σ + Inner.inner ℝ (rgrad (I := I) (M := M) f q) u * Real.sin σ)|
        ≤ 2 * ε₁ * s) := by
  -- the ray starts at `q`, where the model takes the value `f q` and the trig bound gives `> -1+c`
  have hbase : -1 + c < f (Submission.GlobalExp.GExp (cov := cov) hmet q ((0 : ℝ) • u)) := by
    have h0 : Submission.GlobalExp.GExp (cov := cov) hmet q ((0 : ℝ) • u) = q := by simp
    rw [h0]
    have ht0 := htrig 0 (by constructor <;> linarith [hs0])
    simp only [Real.cos_zero, Real.sin_zero, mul_one, mul_zero, add_zero] at ht0
    linarith
  exact ray_model_bootstrap (g := fun σ : ℝ =>
      f (Submission.GlobalExp.GExp (cov := cov) hmet q (σ • u)))
    (Md := fun σ : ℝ => f q * Real.cos σ
      + Inner.inner ℝ (rgrad (I := I) (M := M) f q) u * Real.sin σ)
    hsπ hc hε₁ hεπ hcont hbase htrig hcmp

end Work.Diff.C
