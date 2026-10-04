import Mathlib
import Submission.Work.Diff.EXT.LocalExtDefs
import Submission.Work.Diff.GE.scalar_max_principle
import Submission.Work.Diff.EXT.curvNormK_zero_le_of_curvBound
import Submission.Work.Diff.EXT.exists_bound_curvNormK_slice

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shi's a priori estimate from the analytic interfaces

This file proves `Work.Diff.EXT.ShiBounds` (Shi's a priori estimate in its geometric form: along a
Ricci flow on `[0,T)` with curvature bounded by `C`, every covariant derivative of the curvature is
bounded on `[σ,T)` for every `σ > 0`) from the two analytic interfaces of the `EXT` area:

* `Work.Diff.EXT.EvolK` — the evolution inequality for `u k := |∇^k Rm|²` with the `-2|∇^{k+1}Rm|²`
  term dropped (the reaction terms being estimated by the lower order bounds `A i`);
* `Work.Diff.EXT.NormSmoothK` — joint smoothness of `(t,x) ↦ |∇^k Rm|²(g(t))(x)`, needed for the
  maximum principle,

together with the scalar maximum principle `Submission.Diff.ScalarMaxPrinciple` and
`Submission.Diff.LCSmooth`.

## The argument

Shi's estimate is the classical induction on `k`, run with the scalar maximum principle on the
sub-interval `[σ,T)`.  Write `u k t x = |∇^k Rm|²(g(t))(x)`.

* `k = 0`: `|Rm|²` is the Frobenius square of the curvature array, so `CurvBound (g t) C` bounds it
  by `(n²|C|)²` uniformly (`curvNormK_zero_le_of_curvBound`).
* `k → k+1`: assume bounds `A i` for `u i`, `i < k`, on `[σ,T)`.  `EvolK` supplies, for every
  `(t,x)` with `t ∈ [σ,T)`, a right derivative of `s ↦ u k s x` bounded by
  `Δ u k (t,·) x + K · u k t x + K` with `K := c (1 + ∑_{i<k} A i) ≥ 0`.
  Since `u k t x ≤ max (u k t x) 0`, this is a legitimate input for the scalar maximum principle,
  which we apply on `[σ,T)` (`smp_Ico_of_smp`, a time shift of
  `Submission.Diff.ScalarMaxPrinciple`).  The value at the initial time `σ` is bounded by
  compactness of `M` (`exists_bound_curvNormK_slice`).  This gives
  `u k t x ≤ exp (K (T-σ)) (max B 0 + K (T-σ))` on `[σ,T)`.

The bound produced at stage `k` is `max`-ed with `0` when it is fed to stage `k+1`, as `EvolK`
requires nonnegative lower order bounds.
-/

namespace Work.Diff.EXT

open Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

section Helpers

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- `|∇^k Rm|²` is a sum of squares, hence nonnegative. -/
theorem curvNormK_nonneg (g : Submission.Diff.SMet I M) (x : M) (k : ℕ) :
    0 ≤ curvNormK g x k := by
  rw [curvNormK]
  exact Finset.sum_nonneg fun ι _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun m _ => sq_nonneg _

/-- The scalar maximum principle of `Submission.Diff.ScalarMaxPrinciple`, stated on `[0,T)`, holds
verbatim on an arbitrary initial time `σ < T`: shifting time by `σ` maps the statement for
`(G, T, u, d, C₁, C₂, B)` to the statement for `(t ↦ G (t + σ), T - σ, (t,x) ↦ u (t + σ) x,
(t,x) ↦ d (t + σ) x, C₁, C₂, B)`, and the conclusion is converted back to a bound on `[σ, T)`. -/
theorem smp_Ico_of_smp
    (hSMP : Submission.Diff.ScalarMaxPrinciple I M)
    {G : ℝ → Submission.Diff.SMet I M} {T σ : ℝ} (hσT : σ < T)
    (hJS : Submission.Diff.JointSmooth G (Set.Ico σ T))
    (u d : ℝ → M → ℝ) (C₁ C₂ B : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hu : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M ↦ u p.1 p.2)
        (Set.Ico σ T ×ˢ Set.univ))
    (hineq : ∀ t ∈ Set.Ico σ T, ∀ x : M,
      HasDerivWithinAt (fun s ↦ u s x) (d t x) (Set.Ico σ T) t ∧
        d t x ≤ Submission.Diff.laplAt (G t) (u t) x + C₁ * max (u t x) 0 + C₂)
    (hinit : ∀ x : M, u σ x ≤ B) :
    ∀ t ∈ Set.Ico σ T, ∀ x : M,
      u t x ≤ Real.exp (C₁ * (T - σ)) * (max B 0 + C₂ * (T - σ)) := by
  -- the shift map `p ↦ (p.1 + σ, p.2)`, an order isomorphism of the two time intervals
  have hshift : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × M ↦ (p.1 + σ, p.2)) (Set.Ico 0 (T - σ) ×ˢ (Set.univ : Set M)) :=
    ((contMDiffOn_fst (I := 𝓘(ℝ, ℝ)) (J := I) (s := Set.Ico 0 (T - σ) ×ˢ (Set.univ : Set M))).add
      contMDiffOn_const).prodMk
      (contMDiffOn_snd (I := 𝓘(ℝ, ℝ)) (J := I) (s := Set.Ico 0 (T - σ) ×ˢ (Set.univ : Set M)))
  have hmaps : Set.Ico 0 (T - σ) ×ˢ (Set.univ : Set M) ⊆
      (fun p : ℝ × M ↦ (p.1 + σ, p.2)) ⁻¹' (Set.Ico σ T ×ˢ (Set.univ : Set M)) := by
    intro p hp
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_Ico, Set.mem_univ, and_true] at hp ⊢
    exact ⟨by linarith [hp.1], by linarith [hp.2]⟩
  -- the shifted flow is jointly smooth
  have hJS' : Submission.Diff.JointSmooth (fun s : ℝ ↦ G (s + σ)) (Set.Ico 0 (T - σ)) := by
    unfold Submission.Diff.JointSmooth at hJS ⊢
    have h := hJS.comp hshift hmaps
    simp only [Function.comp_def] at h
    exact h
  -- the shifted function `(t,x) ↦ u (t + σ) x` is smooth
  have hu' : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M ↦ (fun s : ℝ ↦ fun x : M ↦ u (s + σ) x) p.1 p.2)
      (Set.Ico 0 (T - σ) ×ˢ (Set.univ : Set M)) := by
    have h := hu.comp hshift hmaps
    simp only [Function.comp_def] at h
    exact h
  -- the differential inequality, transported by the chain rule for within-derivatives
  have hineq' : ∀ t ∈ Set.Ico 0 (T - σ), ∀ x : M,
      HasDerivWithinAt (fun s ↦ (fun s : ℝ ↦ fun x : M ↦ u (s + σ) x) s x) (d (t + σ) x)
        (Set.Ico 0 (T - σ)) t ∧
      d (t + σ) x ≤ Submission.Diff.laplAt (G (t + σ))
          ((fun s : ℝ ↦ fun x : M ↦ u (s + σ) x) t) x + C₁ * max (u (t + σ) x) 0 + C₂ := by
    intro t ht x
    have htσ : t + σ ∈ Set.Ico σ T := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    obtain ⟨hder, hbnd⟩ := hineq (t + σ) htσ x
    have hder' : HasDerivWithinAt (fun s : ℝ ↦ (fun s : ℝ ↦ fun x : M ↦ u (s + σ) x) s x)
        (d (t + σ) x) (Set.Ico 0 (T - σ)) t := by
      have hcomp := hder.comp (s := Set.Ico 0 (T - σ)) (s' := Set.Ico σ T)
        (x := t) (h := fun s : ℝ ↦ s + σ) (h' := 1)
        ((hasDerivAt_id t).add_const σ).hasDerivWithinAt
        (fun s hs => by
          simp only [Set.mem_Ico] at hs ⊢
          exact ⟨by linarith [hs.1], by linarith [hs.2]⟩)
      simpa only [Function.comp_def, mul_one] using hcomp
    exact ⟨hder', hbnd⟩
  have hinit' : ∀ x : M, (fun s : ℝ ↦ fun x : M ↦ u (s + σ) x) 0 x ≤ B := by
    intro x
    simpa using hinit x
  -- the maximum principle for the shifted data
  have key := hSMP (fun s : ℝ ↦ G (s + σ)) (T - σ)
    (fun s : ℝ ↦ fun x : M ↦ u (s + σ) x) (fun s : ℝ ↦ fun x : M ↦ d (s + σ) x)
    C₁ C₂ B hJS' hC₁ hC₂ hu' hineq' hinit'
  -- back to the original time variable, and `t - σ ≤ T - σ`
  intro t ht x
  have ht' : t - σ ∈ Set.Ico 0 (T - σ) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have h1 := key (t - σ) ht' x
  rw [sub_add_cancel] at h1
  have h2 : Real.exp (C₁ * (t - σ)) ≤ Real.exp (C₁ * (T - σ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [ht.2]) hC₁)
  have h3 : max B 0 + C₂ * (t - σ) ≤ max B 0 + C₂ * (T - σ) := by
    have h := mul_le_mul_of_nonneg_left (show t - σ ≤ T - σ by linarith [ht.2]) hC₂
    linarith
  have h4 : 0 ≤ max B 0 + C₂ * (t - σ) := by
    have hC₂s : 0 ≤ C₂ * (t - σ) := mul_nonneg hC₂ (by linarith [ht.1])
    linarith [le_max_right B 0]
  calc u t x ≤ Real.exp (C₁ * (t - σ)) * (max B 0 + C₂ * (t - σ)) := h1
    _ ≤ Real.exp (C₁ * (T - σ)) * (max B 0 + C₂ * (T - σ)) :=
        mul_le_mul h2 h3 h4 (Real.exp_pos _).le

end Helpers

/-- **Shi's a priori estimate** (`Work.Diff.EXT.ShiBounds`), from the evolution inequality `EvolK`
and the joint smoothness `NormSmoothK` of the curvature norms, via the scalar maximum principle. -/
theorem shibounds_of_interfaces
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    (hSMP : Submission.Diff.ScalarMaxPrinciple I M)
    (hreg : Work.Diff.EXT.NormSmoothK (I := I) (M := M))
    (hev : Work.Diff.EXT.EvolK (I := I) (M := M)) :
    Work.Diff.EXT.ShiBounds (I := I) (M := M) := by
  intro G T C σ hT hflow hbound hσ hσT k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · -- `k = 0`: a componentwise bound for the curvature array
      subst hk0
      refine ⟨((Module.finrank ℝ E : ℝ) ^ 2 * |C|) ^ 2, fun t ht x => ?_⟩
      exact curvNormK_zero_le_of_curvBound (G t) x C
        (hbound t ⟨le_of_lt (lt_of_lt_of_le hσ ht.1), ht.2⟩)
    · -- `k ≥ 1`: the maximum principle on `[σ,T)` for `u = |∇^k Rm|²`
      classical
      have hsubT : Set.Ico σ T ⊆ Set.Ico (0 : ℝ) T := by
        intro t ht
        simp only [Set.mem_Ico] at ht ⊢
        exact ⟨by linarith [hσ, ht.1], ht.2⟩
      have hsub : Set.Ico σ T ×ˢ (Set.univ : Set M) ⊆ Set.Ico (0 : ℝ) T ×ˢ (Set.univ : Set M) :=
        Set.prod_mono hsubT (Subset.refl _)
      -- the lower order bounds `A i`, `i < k`, made nonnegative
      let A : ℕ → ℝ := fun i => max (if hi : i < k then Classical.choose (ih i hi) else 0) 0
      have hA_nn : ∀ i, i ≤ k → 0 ≤ A i := by
        intro i _
        exact le_max_right _ _
      have hA_low : ∀ i, i < k → ∀ t ∈ Set.Ico σ T, ∀ x : M, curvNormK (G t) x i ≤ A i := by
        intro i hi t ht x
        have hAi : A i = max (Classical.choose (ih i hi)) 0 := by
          simp only [A, dif_pos hi]
        rw [hAi]
        exact le_trans (Classical.choose_spec (ih i hi) t ht x) (le_max_left _ _)
      -- the evolution inequality for `|∇^k Rm|²`
      obtain ⟨c, hc, hspec⟩ := hev k hkpos
      set K : ℝ := c * (1 + Finset.sum (Finset.range k) (fun i => A i)) with hKdef
      have hK_nn : 0 ≤ K := by
        rw [hKdef]
        refine mul_nonneg hc (by
          have h := Finset.sum_nonneg (fun i hi => hA_nn i (le_of_lt (Finset.mem_range.mp hi)))
          linarith)
      have hex : ∀ t : ℝ, ∀ x : M, ∃ D : ℝ,
          (t ∈ Set.Ico σ T → HasDerivWithinAt (fun s => curvNormK (G s) x k) D (Set.Ico σ T) t) ∧
          (t ∈ Set.Ico σ T → D ≤ Submission.Diff.laplAt (G t) (fun y => curvNormK (G t) y k) x
              + K * max (curvNormK (G t) x k) 0 + K) := by
        intro t x
        by_cases ht : t ∈ Set.Ico σ T
        · obtain ⟨D, hD1, hD2⟩ := hspec A hA_nn G σ T hflow hσT hA_low t ht x
          refine ⟨D, fun _ => ?_, fun _ => ?_⟩
          · exact hD1.mono hsubT
          · rw [← hKdef] at hD2
            have hmul : K * curvNormK (G t) x k ≤ K * max (curvNormK (G t) x k) 0 :=
              mul_le_mul_of_nonneg_left (le_max_left _ _) hK_nn
            linarith
        · exact ⟨0, fun h => absurd h ht, fun h => absurd h ht⟩
      let d : ℝ → M → ℝ := fun t x => Classical.choose (hex t x)
      have hd : ∀ t x, (t ∈ Set.Ico σ T →
            HasDerivWithinAt (fun s => curvNormK (G s) x k) (d t x) (Set.Ico σ T) t) ∧
          (t ∈ Set.Ico σ T → d t x ≤ Submission.Diff.laplAt (G t) (fun y => curvNormK (G t) y k) x
              + K * max (curvNormK (G t) x k) 0 + K) :=
        fun t x => Classical.choose_spec (hex t x)
      -- the value at the initial time `σ`, from compactness of `M`
      obtain ⟨B, hB⟩ := exists_bound_curvNormK_slice hreg G T hflow k ⟨le_of_lt hσ, hσT⟩
      have hureg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞
          (fun p : ℝ × M => curvNormK (G p.1) p.2 k) (Set.Ico σ T ×ˢ Set.univ) :=
        (hreg G T hflow k).mono hsub
      have hJS : Submission.Diff.JointSmooth G (Set.Ico σ T) := hflow.1.mono hsub
      refine ⟨Real.exp (K * (T - σ)) * (max B 0 + K * (T - σ)), fun t ht x => ?_⟩
      exact smp_Ico_of_smp hSMP hσT hJS (fun t x => curvNormK (G t) x k) d K K B hK_nn hK_nn hureg
        (fun t ht x => ⟨(hd t x).1 ht, (hd t x).2 ht⟩) hB t ht x

end Work.Diff.EXT
