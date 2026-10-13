import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_RegExport.RXT.cone_max_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option maxHeartbeats 1600000

namespace Work.FTS_RegExport.RXT

open ConeAux

/-- **Cone maximum principle for a first-order transport equation with bounded coefficients.**

`φ` is a `C¹` scalar field on `ℝ² × [0,T]` (spatial variables `s, ψ`), whose `τ`-derivative
satisfies the transport equation `∂_τ φ = f − (a·∂_sφ + b·∂_ψφ + c·φ)` for `τ ∈ (0,T]`, with
BOUNDED coefficients (`|a|,|b| ≤ A`, `|c| ≤ C`, `|f| ≤ F`) that are only assumed bounded
pointwise in all variables (no regularity at all in `τ`), and with data bounded by `K₀` at
`τ = 0`. Then `|φ| ≤ exp(2·C·τ)·(K₀ + τ·F)` for all times `τ ∈ [0,T]` and all points.

Proof route (verified on paper): for a fixed target point `(s₀,ψ₀,τ₀)` and a fixed `ε > 0`,
one discretises `[0,τ₀]` with mesh `h = τ₀/N` and proves by induction on `k` that `|φ| ≤ M(kh)`
on the shrinking cone `C(kh) = {(s,ψ) : |s-s₀| ≤ A(τ₀-kh), |ψ-ψ₀| ≤ A(τ₀-kh)}`, where
`M(t) = exp(2Ct)(K₀ + t(F+ε))`.  The one-step (backward) ingredient: taking the MVT point
`τ* ∈ (τ,τ+h)` for the `τ`-difference at `(s,ψ)` and putting
`(s',ψ') = (s,ψ) - h·(a,b)(s,ψ,τ*)` one has `|s'-s| ≤ Ah`; the two spatial MVTs at time `τ`
give
`φ(s,ψ,τ+h) - φ(s',ψ',τ) = h·f(s,ψ,τ*) - h·c(s,ψ,τ*)·φ(s,ψ,τ*)`
`  - h·a(s,ψ,τ*)·(∂_sφ(s,ψ,τ*) - ∂_sφ(σ₁,ψ,τ)) - h·b(s,ψ,τ*)·(∂_ψφ(s,ψ,τ*) - ∂_ψφ(s',σ₂,τ))`
with `σ₁ ∈ (s',s)`, `σ₂ ∈ (ψ',ψ)`.  All the differences are small by (uniform) continuity of
`∂_sφ, ∂_ψφ` and of `φ` on compact boxes (`Heine–Cantor`), whence
`|φ(s,ψ,τ+h)| ≤ M + h(C·B + F) + ε·h` where `M` bounds `|φ|` at `(s',ψ',τ)` and `B` at
`(s,ψ,τ+h)`; solving for `B` (instantiate the universally quantified `B` at the actual value)
and using `(1-Ch)·exp(2Ch) ≥ 1` for `Ch ≤ 1/2` gives `M(τ+h)`.  Finally `ε → 0`.
Note there is NO hypothesis on the `τ`-continuity of `a,b,c,f` — that is exactly the point.

WARNING (do not be tempted by the naive Gronwall): the term `a·∂_sφ` is a first-order term and
`∂_sφ` is NOT bounded, so `|∂_τφ| ≤ F + C|φ|` is FALSE and the pointwise-in-`(s,ψ)` Gronwall
does not apply.  The whole content is that the *sup over the backward cone* obeys the
inequality, which is what the discretisation achieves. -/
theorem cone_max_principle
    {φ φs φψ a b c f : ℝ → ℝ → ℝ → ℝ} {T A C F K₀ : ℝ}
    (hT : 0 < T) (hA : 0 ≤ A) (hC : 0 ≤ C) (hF : 0 ≤ F) (hK₀ : 0 ≤ K₀)
    (hφcont : ContinuousOn (fun p : ℝ × ℝ × ℝ => φ p.1 p.2.1 p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) T))
    (hφscont : ContinuousOn (fun p : ℝ × ℝ × ℝ => φs p.1 p.2.1 p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) T))
    (hφψcont : ContinuousOn (fun p : ℝ × ℝ × ℝ => φψ p.1 p.2.1 p.2.2)
      (Set.univ ×ˢ Set.univ ×ˢ Set.Icc (0:ℝ) T))
    (hs : ∀ s ψ τ, τ ∈ Set.Icc (0:ℝ) T → HasDerivAt (fun s' => φ s' ψ τ) (φs s ψ τ) s)
    (hψ : ∀ s ψ τ, τ ∈ Set.Icc (0:ℝ) T → HasDerivAt (fun ψ' => φ s ψ' τ) (φψ s ψ τ) ψ)
    (hEq : ∀ s ψ τ, 0 < τ → τ ≤ T →
      HasDerivAt (fun σ => φ s ψ σ)
        (f s ψ τ - (a s ψ τ * φs s ψ τ + b s ψ τ * φψ s ψ τ + c s ψ τ * φ s ψ τ)) τ)
    (ha : ∀ s ψ τ, 0 < τ → τ ≤ T → |a s ψ τ| ≤ A)
    (hb : ∀ s ψ τ, 0 < τ → τ ≤ T → |b s ψ τ| ≤ A)
    (hc : ∀ s ψ τ, 0 < τ → τ ≤ T → |c s ψ τ| ≤ C)
    (hf : ∀ s ψ τ, 0 < τ → τ ≤ T → |f s ψ τ| ≤ F)
    (h0 : ∀ s ψ, |φ s ψ 0| ≤ K₀) :
    ∀ s ψ τ, τ ∈ Set.Icc (0:ℝ) T → |φ s ψ τ| ≤ Real.exp (2 * C * τ) * (K₀ + τ * F) := by
  intro s₀ ψ₀ τ₀ hτ₀
  rcases eq_or_lt_of_le hτ₀.1 with h0τ | hpos
  · rw [← h0τ]
    simpa using h0 s₀ ψ₀
  suffices hmain : ∀ η : ℝ, 0 < η →
      |φ s₀ ψ₀ τ₀| ≤ Real.exp (2 * C * τ₀) * (K₀ + τ₀ * (F + η)) by
    have hE : 0 < Real.exp (2 * C * τ₀) := Real.exp_pos _
    refine le_of_forall_pos_le_add (fun ε hε => ?_)
    have hden : 0 < Real.exp (2 * C * τ₀) * τ₀ := mul_pos hE hpos
    have h1 := hmain (ε / (Real.exp (2 * C * τ₀) * τ₀)) (div_pos hε hden)
    have halg : Real.exp (2 * C * τ₀) *
        (K₀ + τ₀ * (F + ε / (Real.exp (2 * C * τ₀) * τ₀)))
        = Real.exp (2 * C * τ₀) * (K₀ + τ₀ * F) + ε := by
      have hEne : Real.exp (2 * C * τ₀) ≠ 0 := Real.exp_ne_zero _
      have hτne : τ₀ ≠ 0 := ne_of_gt hpos
      field_simp
      ring
    rw [halg] at h1
    linarith
  intro η hη
  have hFη : 0 ≤ F + η := by linarith
  have hA1 : 0 < A + 1 := by linarith
  have hAτ : 0 ≤ A * τ₀ := mul_nonneg hA hτ₀.1
  -- ## The compact box and the a priori bound `S₀` on it
  let Box : Set (ℝ × ℝ × ℝ) :=
    Set.Icc (s₀ - A*τ₀) (s₀ + A*τ₀) ×ˢ (Set.Icc (ψ₀ - A*τ₀) (ψ₀ + A*τ₀) ×ˢ Set.Icc 0 τ₀)
  have hBoxc : IsCompact Box := isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hBoxne : Box.Nonempty := ⟨(s₀, ψ₀, 0), by
    refine ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, ⟨le_refl _, hτ₀.1⟩⟩⟩
  have hmemBox : ∀ q₁ q₂ t, |q₁ - s₀| ≤ A*τ₀ → |q₂ - ψ₀| ≤ A*τ₀ → t ∈ Set.Icc 0 τ₀ →
      (q₁, q₂, t) ∈ Box := by
    intro q₁ q₂ t h1 h2 h3
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1
    obtain ⟨h2a, h2b⟩ := abs_le.mp h2
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩, h3⟩
  have hBoxcont : ContinuousOn (fun p : ℝ × ℝ × ℝ => |φ p.1 p.2.1 p.2.2|) Box :=
    hφcont.abs.mono (fun p hp => ⟨trivial, trivial, ⟨hp.2.2.1, le_trans hp.2.2.2 hτ₀.2⟩⟩)
  obtain ⟨pstar, _, hmax⟩ := hBoxc.exists_isMaxOn hBoxne hBoxcont
  set S₀ : ℝ := |φ pstar.1 pstar.2.1 pstar.2.2| with hS₀def
  have hS₀b : ∀ q₁ q₂ t, |q₁ - s₀| ≤ A*τ₀ → |q₂ - ψ₀| ≤ A*τ₀ → t ∈ Set.Icc 0 τ₀ →
      |φ q₁ q₂ t| ≤ S₀ := fun q₁ q₂ t h1 h2 h3 =>
    (isMaxOn_iff.mp hmax) (q₁, q₂, t) (hmemBox q₁ q₂ t h1 h2 h3)
  -- ## Uniform continuity of `φs` and `φψ` on the box (Heine–Cantor)
  have hucs : ∀ ε > 0, ∃ δ > 0, ∀ p ∈ Box, ∀ q ∈ Box, dist p q < δ →
      |φs p.1 p.2.1 p.2.2 - φs q.1 q.2.1 q.2.2| < ε := by
    intro ε hε
    have hcont : ContinuousOn (fun p : ℝ × ℝ × ℝ => φs p.1 p.2.1 p.2.2) Box :=
      hφscont.mono (fun p hp => ⟨trivial, trivial, ⟨hp.2.2.1, le_trans hp.2.2.2 hτ₀.2⟩⟩)
    exact (Metric.uniformContinuousOn_iff.mp
      (hBoxc.uniformContinuousOn_of_continuous hcont)) ε hε
  have hucw : ∀ ε > 0, ∃ δ > 0, ∀ p ∈ Box, ∀ q ∈ Box, dist p q < δ →
      |φψ p.1 p.2.1 p.2.2 - φψ q.1 q.2.1 q.2.2| < ε := by
    intro ε hε
    have hcont : ContinuousOn (fun p : ℝ × ℝ × ℝ => φψ p.1 p.2.1 p.2.2) Box :=
      hφψcont.mono (fun p hp => ⟨trivial, trivial, ⟨hp.2.2.1, le_trans hp.2.2.2 hτ₀.2⟩⟩)
    exact (Metric.uniformContinuousOn_iff.mp
      (hBoxc.uniformContinuousOn_of_continuous hcont)) ε hε
  have hεη : 0 < η / (2 * (A + 1)) := by positivity
  obtain ⟨δs, hδspos, hδs⟩ := hucs (η / (2 * (A + 1))) hεη
  obtain ⟨δw, hδwpos, hδw⟩ := hucw (η / (2 * (A + 1))) hεη
  -- ## Choice of the mesh
  set δ' : ℝ := min δs δw with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδspos hδwpos
  have hδ's : δ' ≤ δs := min_le_left _ _
  have hδ'w : δ' ≤ δw := min_le_right _ _
  set R : ℝ := max ((A + 1) * τ₀ / δ') (2 * C * τ₀) with hRdef
  have hRpos : 0 < R := lt_of_lt_of_le (div_pos (mul_pos hA1 hpos) hδ'pos) (le_max_left _ _)
  obtain ⟨N, hNlt⟩ := exists_nat_gt R
  have hNpos : (0:ℝ) < (N:ℝ) := lt_of_lt_of_le hRpos (le_of_lt hNlt)
  set h : ℝ := τ₀ / (N:ℝ) with hhdef
  have hhpos : 0 < h := div_pos hpos hNpos
  have hNh : (N:ℝ) * h = τ₀ := by rw [hhdef]; field_simp
  have hdh_lt : (A + 1) * h < δ' := by
    have hR1 : (A + 1) * τ₀ / δ' ≤ R := le_max_left _ _
    have hkey : (A + 1) * τ₀ ≤ δ' * R := by
      have h2 := mul_le_mul_of_nonneg_left hR1 (le_of_lt hδ'pos)
      have h3 : δ' * ((A + 1) * τ₀ / δ') = (A + 1) * τ₀ := by field_simp
      linarith [h2, h3]
    have hkey2 : (A + 1) * τ₀ < δ' * (N:ℝ) := by
      have := mul_lt_mul_of_pos_left hNlt hδ'pos
      linarith [hkey, this]
    rw [hhdef, ← mul_div_assoc, div_lt_iff₀ hNpos]
    linarith
  have hCh : C * h ≤ 1 / 2 := by
    have hR2 : 2 * C * τ₀ ≤ R := le_max_right _ _
    rw [hhdef, ← mul_div_assoc, div_le_iff₀ hNpos]
    linarith [hR2, hNlt]
  -- ## The level sets `Z k` (cylinder over the shrinking cone)
  let Mfun : ℝ → ℝ := fun t => Real.exp (2 * C * t) * (K₀ + t * (F + η))
  let Z : ℕ → Set ℝ := fun k => {x : ℝ | ∃ q₁ q₂ t : ℝ,
      |q₁ - s₀| ≤ A * (τ₀ - (k:ℝ) * h) ∧ |q₂ - ψ₀| ≤ A * (τ₀ - (k:ℝ) * h) ∧
      t ∈ Set.Icc 0 ((k:ℝ) * h) ∧ x = |φ q₁ q₂ t|}
  have hkh_le : ∀ k : ℕ, k ≤ N → (k:ℝ) * h ≤ τ₀ := by
    intro k hk
    calc (k:ℝ) * h ≤ (N:ℝ) * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hhpos.le
      _ = τ₀ := hNh
  have hZcone : ∀ k : ℕ, k ≤ N → ∀ q₁ q₂ t : ℝ,
      |q₁ - s₀| ≤ A * (τ₀ - (k:ℝ) * h) → |q₂ - ψ₀| ≤ A * (τ₀ - (k:ℝ) * h) →
      t ∈ Set.Icc 0 ((k:ℝ) * h) → |φ q₁ q₂ t| ∈ Z k :=
    fun k _ q₁ q₂ t h1 h2 h3 => ⟨q₁, q₂, t, h1, h2, h3, rfl⟩
  have hZne : ∀ k : ℕ, k ≤ N → (Z k).Nonempty := by
    intro k hk
    refine ⟨|φ s₀ ψ₀ 0|, ?_⟩
    refine hZcone k hk s₀ ψ₀ 0 ?_ ?_ ?_
    · rw [sub_self, abs_zero]; exact mul_nonneg hA (by linarith [hkh_le k hk, hτ₀.1])
    · rw [sub_self, abs_zero]; exact mul_nonneg hA (by linarith [hkh_le k hk, hτ₀.1])
    · exact ⟨le_refl _, mul_nonneg (Nat.cast_nonneg k) hhpos.le⟩
  have hZbd : ∀ k : ℕ, k ≤ N → BddAbove (Z k) := by
    intro k hk
    refine ⟨S₀, fun x hx => ?_⟩
    obtain ⟨q₁, q₂, t, h1, h2, h3, rfl⟩ := hx
    have hnn : 0 ≤ (k:ℝ) * h := mul_nonneg (Nat.cast_nonneg k) hhpos.le
    have hτk : τ₀ - (k:ℝ) * h ≤ τ₀ := by linarith
    exact hS₀b q₁ q₂ t (le_trans h1 (mul_le_mul_of_nonneg_left hτk hA))
      (le_trans h2 (mul_le_mul_of_nonneg_left hτk hA))
      ⟨h3.1, le_trans h3.2 (hkh_le k hk)⟩
  have hZle : ∀ k : ℕ, k ≤ N → ∀ x ∈ Z k, x ≤ sSup (Z k) :=
    fun k hk x hx => le_csSup (hZbd k hk) hx
  have hZnn : ∀ k : ℕ, k ≤ N → ∀ x ∈ Z k, 0 ≤ x := by
    intro k hk x hx
    obtain ⟨q₁, q₂, t, h1, h2, h3, rfl⟩ := hx
    exact abs_nonneg _
  have hBnn : ∀ k : ℕ, k ≤ N → 0 ≤ sSup (Z k) := by
    intro k hk
    obtain ⟨x, hx⟩ := hZne k hk
    exact le_trans (hZnn k hk x hx) (hZle k hk x hx)
  -- ## The induction
  have hkey : ∀ k : ℕ, k ≤ N → sSup (Z k) ≤ Mfun ((k:ℝ) * h) := by
    intro k
    induction k with
    | zero =>
      intro _
      have h0' : sSup (Z 0) ≤ K₀ := by
        refine csSup_le (hZne 0 (Nat.zero_le _)) (fun x hx => ?_)
        obtain ⟨q₁, q₂, t, h1, h2, h3, rfl⟩ := hx
        have ht : t = 0 := le_antisymm (by simpa using h3.2) h3.1
        rw [ht]
        exact h0 q₁ q₂
      simpa only [Mfun, Nat.cast_zero, zero_mul, mul_zero, add_zero, Real.exp_zero,
        one_mul] using h0'
    | succ k ih =>
      intro hk1
      have hk : k ≤ N := le_trans (Nat.le_succ k) hk1
      have hIH : sSup (Z k) ≤ Mfun ((k:ℝ) * h) := ih hk
      have hBk1nn : 0 ≤ sSup (Z (k+1)) := hBnn (k+1) hk1
      have hkhk1 : (k:ℝ) * h ≤ ((k+1:ℕ):ℝ) * h := by push_cast; linarith [hhpos.le]
      have hk1_le_τ : ((k+1:ℕ):ℝ) * h ≤ τ₀ := hkh_le (k+1) hk1
      have hk_le_τ : (k:ℝ) * h ≤ τ₀ := le_trans hkhk1 hk1_le_τ
      have hknn : 0 ≤ (k:ℝ) * h := mul_nonneg (Nat.cast_nonneg k) hhpos.le
      have haux : sSup (Z (k+1)) ≤ Mfun ((k:ℝ)*h) + h*(F+η) + h*C*sSup (Z (k+1)) := by
        refine csSup_le (hZne (k+1) hk1) (fun x hx => ?_)
        obtain ⟨q₁, q₂, t, hc1, hc2, htmem, rfl⟩ := hx
        by_cases htle : t ≤ (k:ℝ)*h
        · have hmem : |φ q₁ q₂ t| ∈ Z k :=
            hZcone k hk q₁ q₂ t
              (le_trans hc1 (mul_le_mul_of_nonneg_left (by push_cast; linarith [hhpos.le]) hA))
              (le_trans hc2 (mul_le_mul_of_nonneg_left (by push_cast; linarith [hhpos.le]) hA))
              ⟨htmem.1, htle⟩
          have h1 := hZle k hk _ hmem
          have h3 : 0 ≤ h * (F + η) := mul_nonneg hhpos.le hFη
          have h4 : 0 ≤ h * C * sSup (Z (k+1)) :=
            mul_nonneg (mul_nonneg hhpos.le hC) hBk1nn
          linarith [h1, hIH, h3, h4]
        · -- ### the mean-value step
          have hdep_pos : 0 < t - (k:ℝ)*h := sub_pos.mpr (lt_of_not_ge htle)
          have hdep_le : t - (k:ℝ)*h ≤ h := by
            have h2 : t ≤ ((k+1:ℕ):ℝ) * h := htmem.2
            push_cast at h2
            linarith
          have htT : t ≤ T := le_trans (le_trans htmem.2 hk1_le_τ) hτ₀.2
          -- continuity of the time slice
          have hcontτ : ContinuousOn (fun σ : ℝ => φ q₁ q₂ σ) (Set.Icc ((k:ℝ)*h) t) :=
            hφcont.comp' (f := fun σ : ℝ => (q₁, q₂, σ)) (by fun_prop)
              (by intro σ hσ; exact ⟨trivial, trivial,
                ⟨by linarith [hσ.1, hknn], by linarith [hσ.2, htT]⟩⟩)
          obtain ⟨τstar, hτsmem, hτseq⟩ := mvt_slope
            (f := fun σ : ℝ => φ q₁ q₂ σ)
            (fs := fun σ : ℝ => f q₁ q₂ σ -
              (a q₁ q₂ σ * φs q₁ q₂ σ + b q₁ q₂ σ * φψ q₁ q₂ σ
                + c q₁ q₂ σ * φ q₁ q₂ σ))
            (a := (k:ℝ)*h) (b := t) (by linarith) hcontτ (fun σ hσ =>
              hEq q₁ q₂ σ (by linarith [hσ.1, hknn]) (by linarith [hσ.2, htT]))
          have hτs_gt : (k:ℝ)*h < τstar := hτsmem.1
          have hτs_lt : τstar < t := hτsmem.2
          have hτs0 : 0 < τstar := by linarith [hτs_gt, hknn]
          have hτsT : τstar ≤ T := by linarith [hτs_lt, htT]
          have hτs_in : τstar ∈ Set.Icc 0 τ₀ :=
            ⟨by linarith, le_trans (le_of_lt hτs_lt) (le_trans htmem.2 hk1_le_τ)⟩
          have hq₁τ₀ : |q₁ - s₀| ≤ A * τ₀ :=
            le_trans hc1 (mul_le_mul_of_nonneg_left (by linarith) hA)
          have hq₂τ₀ : |q₂ - ψ₀| ≤ A * τ₀ :=
            le_trans hc2 (mul_le_mul_of_nonneg_left (by linarith) hA)
          have hkhτ : ((k:ℝ)*h) ∈ Set.Icc 0 τ₀ := ⟨hknn, hk_le_τ⟩
          have hkhT : ((k:ℝ)*h) ∈ Set.Icc (0:ℝ) T := ⟨hknn, le_trans hk_le_τ hτ₀.2⟩
          -- the backward point
          set q₁' : ℝ := q₁ - (t - (k:ℝ)*h) * a q₁ q₂ τstar with hq₁'def
          set q₂' : ℝ := q₂ - (t - (k:ℝ)*h) * b q₁ q₂ τstar with hq₂'def
          have hq₁'eq : q₁ - q₁' = (t - (k:ℝ)*h) * a q₁ q₂ τstar := by rw [hq₁'def]; ring
          have hq₂'eq : q₂ - q₂' = (t - (k:ℝ)*h) * b q₁ q₂ τstar := by rw [hq₂'def]; ring
          have hqq₁ : |q₁ - q₁'| ≤ (t - (k:ℝ)*h) * A := by
            rw [hq₁'eq, abs_mul, abs_of_pos hdep_pos]
            exact mul_le_mul_of_nonneg_left (ha q₁ q₂ τstar hτs0 hτsT) hdep_pos.le
          have hqq₂ : |q₂ - q₂'| ≤ (t - (k:ℝ)*h) * A := by
            rw [hq₂'eq, abs_mul, abs_of_pos hdep_pos]
            exact mul_le_mul_of_nonneg_left (hb q₁ q₂ τstar hτs0 hτsT) hdep_pos.le
          have hgap : (t - (k:ℝ)*h) + (τ₀ - ((k+1:ℕ):ℝ)*h) ≤ τ₀ - (k:ℝ)*h := by
            push_cast; linarith
          have h3 : |q₁' - q₁| ≤ (t - (k:ℝ)*h) * A := by
            simpa [abs_sub_comm] using hqq₁
          have h4 : |q₂' - q₂| ≤ (t - (k:ℝ)*h) * A := by
            simpa [abs_sub_comm] using hqq₂
          have hcone1' : |q₁' - s₀| ≤ A * (τ₀ - (k:ℝ)*h) := cone_shift hA hgap h3 hc1
          have hcone2' : |q₂' - ψ₀| ≤ A * (τ₀ - (k:ℝ)*h) := cone_shift hA hgap h4 hc2

          have hbd1 : |φ q₁' q₂' ((k:ℝ)*h)| ≤ sSup (Z k) :=
            hZle k hk _ (hZcone k hk q₁' q₂' ((k:ℝ)*h) hcone1' hcone2'
              ⟨hknn, le_refl _⟩)
          have hbd2 : |φ q₁ q₂ τstar| ≤ sSup (Z (k+1)) :=
            hZle (k+1) hk1 _ (hZcone (k+1) hk1 q₁ q₂ τstar hc1 hc2
              ⟨by linarith, le_trans (le_of_lt hτs_lt) htmem.2⟩)
          -- the spatial slices and their frozen-derivative bounds
          have hslice1 : ContinuousOn (fun s : ℝ => φ s q₂ ((k:ℝ)*h))
              (Set.Icc (min q₁ q₁') (max q₁ q₁')) :=
            hφcont.comp' (f := fun s : ℝ => (s, q₂, (k:ℝ)*h)) (by fun_prop)
              (by intro s _; exact ⟨trivial, trivial, hkhT⟩)
          have hderiv1 : ∀ s, HasDerivAt (fun s' : ℝ => φ s' q₂ ((k:ℝ)*h))
              (φs s q₂ ((k:ℝ)*h)) s :=
            fun s => hs s q₂ ((k:ℝ)*h) hkhT
          have hslice2 : ContinuousOn (fun ψ : ℝ => φ q₁' ψ ((k:ℝ)*h))
              (Set.Icc (min q₂ q₂') (max q₂ q₂')) :=
            hφcont.comp' (f := fun ψ : ℝ => (q₁', ψ, (k:ℝ)*h)) (by fun_prop)
              (by intro ψ _; exact ⟨trivial, trivial, hkhT⟩)
          have hderiv2 : ∀ s, HasDerivAt (fun ψ' : ℝ => φ q₁' ψ' ((k:ℝ)*h))
              (φψ q₁' s ((k:ℝ)*h)) s :=
            fun s => hψ q₁' s ((k:ℝ)*h) hkhT
          have htime : |(k:ℝ)*h - τstar| ≤ t - (k:ℝ)*h := by
            rw [abs_of_nonpos (by linarith), neg_sub]
            linarith [hτs_lt]
          have hq₁'τ₀ : |q₁' - s₀| ≤ A * τ₀ :=
            le_trans hcone1' (mul_le_mul_of_nonneg_left (by linarith) hA)
          have hbdq1 : ∀ l ∈ Set.Icc (min q₁ q₁') (max q₁ q₁'),
              |φs l q₂ ((k:ℝ)*h) - φs q₁ q₂ τstar| ≤ η / (2 * (A + 1)) := by
            intro l hl
            have hl1 : |l - q₁| ≤ (t - (k:ℝ)*h) * A := by
              have hm : max q₁ q₁' - min q₁ q₁' = |q₁' - q₁| := max_sub_min_eq_abs q₁ q₁'
              have hl' : |l - q₁| ≤ max q₁ q₁' - min q₁ q₁' := by
                rw [abs_sub_le_iff]
                exact ⟨by linarith [hl.2, min_le_left q₁ q₁'],
                  by linarith [hl.1, le_max_left q₁ q₁']⟩
              rw [hm] at hl'
              exact le_trans hl' (by rw [abs_sub_comm]; exact hqq₁)
            have hl0 : |l - s₀| ≤ A * τ₀ :=
              le_trans (cone_shift hA hgap hl1 hc1)
                (mul_le_mul_of_nonneg_left (by linarith [hknn]) hA)
            have hzz : |q₂ - q₂| ≤ (t - (k:ℝ)*h) * A := by
              rw [sub_self, abs_zero]
              exact mul_nonneg hdep_pos.le hA
            have hd : dist (l, q₂, (k:ℝ)*h) (q₁, q₂, τstar) ≤ (A + 1) * h :=
              dist_three_le hA hhpos hdep_le hl1 hzz htime
            have hm1 : (l, q₂, (k:ℝ)*h) ∈ Box := hmemBox l q₂ ((k:ℝ)*h) hl0 hq₂τ₀ hkhτ
            have hm2 : (q₁, q₂, τstar) ∈ Box := hmemBox q₁ q₂ τstar hq₁τ₀ hq₂τ₀ hτs_in
            exact le_of_lt (hδs _ hm1 _ hm2 (lt_of_lt_of_le (lt_of_le_of_lt hd hdh_lt) hδ's))
          have hbdq2 : ∀ l ∈ Set.Icc (min q₂ q₂') (max q₂ q₂'),
              |φψ q₁' l ((k:ℝ)*h) - φψ q₁ q₂ τstar| ≤ η / (2 * (A + 1)) := by
            intro l hl
            have hl2 : |l - q₂| ≤ (t - (k:ℝ)*h) * A := by
              have hm : max q₂ q₂' - min q₂ q₂' = |q₂' - q₂| := max_sub_min_eq_abs q₂ q₂'
              have hl' : |l - q₂| ≤ max q₂ q₂' - min q₂ q₂' := by
                rw [abs_sub_le_iff]
                exact ⟨by linarith [hl.2, min_le_left q₂ q₂'],
                  by linarith [hl.1, le_max_left q₂ q₂']⟩
              rw [hm] at hl'
              exact le_trans hl' (by rw [abs_sub_comm]; exact hqq₂)
            have hlψ : |l - ψ₀| ≤ A * τ₀ :=
              le_trans (cone_shift hA hgap hl2 hc2)
                (mul_le_mul_of_nonneg_left (by linarith [hknn]) hA)
            have hq₁'time : |q₁' - q₁| ≤ (t - (k:ℝ)*h) * A := by
              simpa [abs_sub_comm] using hqq₁
            have hd : dist (q₁', l, (k:ℝ)*h) (q₁, q₂, τstar) ≤ (A + 1) * h :=
              dist_three_le hA hhpos hdep_le hq₁'time hl2 htime
            have hm1 : (q₁', l, (k:ℝ)*h) ∈ Box := hmemBox q₁' l ((k:ℝ)*h) hq₁'τ₀ hlψ hkhτ
            have hm2 : (q₁, q₂, τstar) ∈ Box := hmemBox q₁ q₂ τstar hq₁τ₀ hq₂τ₀ hτs_in
            exact le_of_lt (hδw _ hm1 _ hm2 (lt_of_lt_of_le (lt_of_le_of_lt hd hdh_lt) hδ'w))
          have hE1 : |φ q₁ q₂ ((k:ℝ)*h) - φ q₁' q₂ ((k:ℝ)*h) - (q₁ - q₁') * φs q₁ q₂ τstar|
              ≤ η / (2 * (A + 1)) * |q₁ - q₁'| :=
              mvt_diff_bound (g := fun s => φ s q₂ ((k:ℝ)*h))
                (gs := fun s => φs s q₂ ((k:ℝ)*h)) hslice1 hderiv1 hbdq1
          have hE2 : |φ q₁' q₂ ((k:ℝ)*h) - φ q₁' q₂' ((k:ℝ)*h) - (q₂ - q₂') * φψ q₁ q₂ τstar|
              ≤ η / (2 * (A + 1)) * |q₂ - q₂'| :=
              mvt_diff_bound (g := fun ψ => φ q₁' ψ ((k:ℝ)*h))
                (gs := fun ψ => φψ q₁' ψ ((k:ℝ)*h)) hslice2 hderiv2 hbdq2
          have hE1abs : |φ q₁ q₂ ((k:ℝ)*h) - φ q₁' q₂ ((k:ℝ)*h) - (q₁ - q₁') * φs q₁ q₂ τstar|
              ≤ (t - (k:ℝ)*h) * (A * (η / (2 * (A + 1)))) := by
            calc |φ q₁ q₂ ((k:ℝ)*h) - φ q₁' q₂ ((k:ℝ)*h) - (q₁ - q₁') * φs q₁ q₂ τstar|
                ≤ η / (2 * (A + 1)) * |q₁ - q₁'| := hE1
              _ ≤ η / (2 * (A + 1)) * ((t - (k:ℝ)*h) * A) :=
                  mul_le_mul_of_nonneg_left hqq₁ (by positivity)
              _ = (t - (k:ℝ)*h) * (A * (η / (2 * (A + 1)))) := by ring
          have hE2abs : |φ q₁' q₂ ((k:ℝ)*h) - φ q₁' q₂' ((k:ℝ)*h) - (q₂ - q₂') * φψ q₁ q₂ τstar|
              ≤ (t - (k:ℝ)*h) * (A * (η / (2 * (A + 1)))) := by
            calc |φ q₁' q₂ ((k:ℝ)*h) - φ q₁' q₂' ((k:ℝ)*h) - (q₂ - q₂') * φψ q₁ q₂ τstar|
                ≤ η / (2 * (A + 1)) * |q₂ - q₂'| := hE2
              _ ≤ η / (2 * (A + 1)) * ((t - (k:ℝ)*h) * A) :=
                  mul_le_mul_of_nonneg_left hqq₂ (by positivity)
              _ = (t - (k:ℝ)*h) * (A * (η / (2 * (A + 1)))) := by ring
          -- the decomposition identity
          have hδD : φ q₁ q₂ t - φ q₁ q₂ ((k:ℝ)*h)
              = (t - (k:ℝ)*h) * (f q₁ q₂ τstar -
                  (a q₁ q₂ τstar * φs q₁ q₂ τstar + b q₁ q₂ τstar * φψ q₁ q₂ τstar
                    + c q₁ q₂ τstar * φ q₁ q₂ τstar)) := by
            calc φ q₁ q₂ t - φ q₁ q₂ ((k:ℝ)*h)
                = (f q₁ q₂ τstar - (a q₁ q₂ τstar * φs q₁ q₂ τstar
                    + b q₁ q₂ τstar * φψ q₁ q₂ τstar
                    + c q₁ q₂ τstar * φ q₁ q₂ τstar)) * (t - (k:ℝ)*h) := hτseq
              _ = (t - (k:ℝ)*h) * (f q₁ q₂ τstar - (a q₁ q₂ τstar * φs q₁ q₂ τstar
                    + b q₁ q₂ τstar * φψ q₁ q₂ τstar
                    + c q₁ q₂ τstar * φ q₁ q₂ τstar)) := by ring
          have hId : φ q₁ q₂ t
              = φ q₁' q₂' ((k:ℝ)*h)
                + (t - (k:ℝ)*h) * (f q₁ q₂ τstar - c q₁ q₂ τstar * φ q₁ q₂ τstar)
                + (φ q₁ q₂ ((k:ℝ)*h) - φ q₁' q₂ ((k:ℝ)*h) - (q₁ - q₁') * φs q₁ q₂ τstar)
                + (φ q₁' q₂ ((k:ℝ)*h) - φ q₁' q₂' ((k:ℝ)*h)
                    - (q₂ - q₂') * φψ q₁ q₂ τstar) := by
            linear_combination hδD + φs q₁ q₂ τstar * hq₁'eq + φψ q₁ q₂ τstar * hq₂'eq
          have hbdmid : |(t - (k:ℝ)*h) * (f q₁ q₂ τstar - c q₁ q₂ τstar * φ q₁ q₂ τstar)|
              ≤ (t - (k:ℝ)*h) * F + (t - (k:ℝ)*h) * C * |φ q₁ q₂ τstar| := by
            rw [abs_mul, abs_of_pos hdep_pos]
            have h1 : |f q₁ q₂ τstar - c q₁ q₂ τstar * φ q₁ q₂ τstar|
                ≤ F + C * |φ q₁ q₂ τstar| := by
              have h2 : |c q₁ q₂ τstar * φ q₁ q₂ τstar| ≤ C * |φ q₁ q₂ τstar| := by
                rw [abs_mul]
                exact mul_le_mul_of_nonneg_right (hc q₁ q₂ τstar hτs0 hτsT) (abs_nonneg _)
              calc |f q₁ q₂ τstar - c q₁ q₂ τstar * φ q₁ q₂ τstar|
                  ≤ |f q₁ q₂ τstar| + |c q₁ q₂ τstar * φ q₁ q₂ τstar| := by
                    simpa using abs_sub_le (f q₁ q₂ τstar) 0
                      (c q₁ q₂ τstar * φ q₁ q₂ τstar)
                _ ≤ F + C * |φ q₁ q₂ τstar| :=
                    add_le_add (hf q₁ q₂ τstar hτs0 hτsT) h2
            have hb : (t - (k:ℝ)*h) * (F + C * |φ q₁ q₂ τstar|)
                = (t - (k:ℝ)*h) * F + (t - (k:ℝ)*h) * C * |φ q₁ q₂ τstar| := by ring
            exact le_trans (mul_le_mul_of_nonneg_left h1 hdep_pos.le) (le_of_eq hb)
          have hfin : |φ q₁ q₂ t| ≤ Mfun ((k:ℝ)*h) + h*(F+η) + h*C*sSup (Z (k+1)) := by
            have hA4 := abs_add4_le (φ q₁' q₂' ((k:ℝ)*h))
              ((t - (k:ℝ)*h) * (f q₁ q₂ τstar - c q₁ q₂ τstar * φ q₁ q₂ τstar))
              (φ q₁ q₂ ((k:ℝ)*h) - φ q₁' q₂ ((k:ℝ)*h) - (q₁ - q₁') * φs q₁ q₂ τstar)
              (φ q₁' q₂ ((k:ℝ)*h) - φ q₁' q₂' ((k:ℝ)*h)
                - (q₂ - q₂') * φψ q₁ q₂ τstar)
            have hbnd : |φ q₁' q₂' ((k:ℝ)*h)|
                + |(t - (k:ℝ)*h) * (f q₁ q₂ τstar - c q₁ q₂ τstar * φ q₁ q₂ τstar)|
                + |φ q₁ q₂ ((k:ℝ)*h) - φ q₁' q₂ ((k:ℝ)*h) - (q₁ - q₁') * φs q₁ q₂ τstar|
                + |φ q₁' q₂ ((k:ℝ)*h) - φ q₁' q₂' ((k:ℝ)*h)
                    - (q₂ - q₂') * φψ q₁ q₂ τstar|
                ≤ sSup (Z k) + ((t - (k:ℝ)*h) * F + (t - (k:ℝ)*h) * C * sSup (Z (k+1)))
                  + (t - (k:ℝ)*h) * (A * (η / (2 * (A + 1))))
                  + (t - (k:ℝ)*h) * (A * (η / (2 * (A + 1)))) := by
              have hbd2' : (t - (k:ℝ)*h) * C * |φ q₁ q₂ τstar|
                  ≤ (t - (k:ℝ)*h) * C * sSup (Z (k+1)) :=
                mul_le_mul_of_nonneg_left hbd2 (mul_nonneg hdep_pos.le hC)
              linarith [hbd1, hbdmid, hbd2', hE1abs, hE2abs]
            have hlast1 : sSup (Z k) + ((t - (k:ℝ)*h) * F
                  + (t - (k:ℝ)*h) * C * sSup (Z (k+1)))
                + (t - (k:ℝ)*h) * (A * (η / (2 * (A + 1))))
                + (t - (k:ℝ)*h) * (A * (η / (2 * (A + 1))))
                ≤ Mfun ((k:ℝ)*h) + h*(F+η) + h*C*sSup (Z (k+1)) := by
              have h1 : (t - (k:ℝ)*h) * F ≤ h * F :=
                mul_le_mul_of_nonneg_right hdep_le hF
              have h2 : (t - (k:ℝ)*h) * C * sSup (Z (k+1)) ≤ h * C * sSup (Z (k+1)) := by
                apply mul_le_mul_of_nonneg_right _ hBk1nn
                exact mul_le_mul_of_nonneg_right hdep_le hC
              have h3 : (t - (k:ℝ)*h) * (A * (η / (2 * (A + 1))))
                  + (t - (k:ℝ)*h) * (A * (η / (2 * (A + 1)))) ≤ h * η := by
                have h4 : 2 * ((t - (k:ℝ)*h) * A * (η / (2 * (A + 1))))
                    ≤ (t - (k:ℝ)*h) * η := two_mul_div_le hA hη.le hdep_pos.le
                have h5 : (t - (k:ℝ)*h) * (A * (η / (2 * (A + 1))))
                    = (t - (k:ℝ)*h) * A * (η / (2 * (A + 1))) := by ring
                rw [h5]
                linarith [h4, mul_le_mul_of_nonneg_right hdep_le hη.le]
              linarith [hIH, h1, h2, h3]
            calc |φ q₁ q₂ t| = |φ q₁' q₂' ((k:ℝ)*h)
                  + (t - (k:ℝ)*h) * (f q₁ q₂ τstar - c q₁ q₂ τstar * φ q₁ q₂ τstar)
                  + (φ q₁ q₂ ((k:ℝ)*h) - φ q₁' q₂ ((k:ℝ)*h)
                      - (q₁ - q₁') * φs q₁ q₂ τstar)
                  + (φ q₁' q₂ ((k:ℝ)*h) - φ q₁' q₂' ((k:ℝ)*h)
                      - (q₂ - q₂') * φψ q₁ q₂ τstar)| := by rw [hId]
              _ ≤ sSup (Z k) + ((t - (k:ℝ)*h) * F + (t - (k:ℝ)*h) * C * sSup (Z (k+1)))
                    + (t - (k:ℝ)*h) * (A * (η / (2 * (A + 1))))
                    + (t - (k:ℝ)*h) * (A * (η / (2 * (A + 1)))) := le_trans hA4 hbnd
              _ ≤ Mfun ((k:ℝ)*h) + h*(F+η) + h*C*sSup (Z (k+1)) := hlast1
          exact hfin
      have hstep := key_step hK₀ hFη hC hknn hhpos.le hCh haux
      have hidx : ((k+1:ℕ):ℝ) * h = (k:ℝ) * h + h := by push_cast; ring
      rw [hidx]
      simpa only [Mfun] using hstep
  -- ## Conclusion
  have hidxN : (N:ℝ) * h = τ₀ := hNh
  have hmemN : |φ s₀ ψ₀ τ₀| ∈ Z N := by
    refine hZcone N le_rfl s₀ ψ₀ τ₀ ?_ ?_ ?_
    · rw [hidxN, sub_self]
      simp
    · rw [hidxN, sub_self]
      simp
    · rw [hidxN]
      exact ⟨hτ₀.1, le_refl _⟩
  have hlast : |φ s₀ ψ₀ τ₀| ≤ Mfun τ₀ := by
    have h1 := hZle N le_rfl _ hmemN
    have h2 := hkey N le_rfl
    rw [hidxN] at h2
    linarith
  simpa only [Mfun] using hlast

end Work.FTS_RegExport.RXT
