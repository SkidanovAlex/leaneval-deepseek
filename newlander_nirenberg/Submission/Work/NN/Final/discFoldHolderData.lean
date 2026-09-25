/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# Hölder data for the disc folding `discFold`

The folding map `discFold p = ((p.1, p.2), discTau p.2)`, with `discTau z = (1 - ‖z‖²)/2`,
is smooth; it is the identity linear map in the `X`-variable and a quadratic polynomial in the
`ℂ`-variable.  This file shows that on every region `U × ball(0,c)` (with `U` open in `X` and
`c > 1`) the map is Lipschitz, that all of its iterated derivatives of order `≥ 1` are bounded
uniformly (independently of `U`), and that those derivatives are Hölder continuous with
exponent `α` for every `0 < α ≤ 1`.

Everything is reduced to one-variable statements about `discTau : ℂ → ℝ`: as a quadratic
polynomial, its `m`-th iterated derivative of orders `≥ 3` vanishes, so the iterated derivatives
are bounded on the compact set `closedBall 0 c` (compactness of the ball plus continuity of
`z ↦ iteratedFDeriv ℝ m discTau z`), and the mean value inequality on the convex ball
`ball 0 c` turns these bounds into the Lipschitz and Hölder bounds.  The two components of
`discFold` are then assembled with the product rule for iterated derivatives.
-/
import Mathlib
import Submission.Work.NN.Final.DiscExtFlat

noncomputable section
open Set Metric
open scoped ContDiff Topology

set_option linter.unusedVariables false

namespace Work.NN.Final

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## `discTau` is smooth in the strong sense -/

private lemma contDiff_top_discTau : ContDiff ℝ (⊤ : ℕ∞ω) discTau := by
  have h : discTau = fun z : ℂ => (1 - (Complex.reCLM z * Complex.reCLM z
      + Complex.imCLM z * Complex.imCLM z)) / 2 := by
    funext z; rw [discTau, Complex.normSq_apply]; rfl
  rw [h]; fun_prop

private lemma contDiff_discTau_snd : ContDiff ℝ (⊤ : ℕ∞ω) (fun q : X × ℂ => discTau q.2) :=
  contDiff_top_discTau.comp (ContinuousLinearMap.snd ℝ X ℂ).contDiff

/-! ## Elementary lemmas about continuous (multi)linear maps -/

private lemma norm_id_le_one : ‖ContinuousLinearMap.id ℝ (X × ℂ)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x => by simp)

private lemma norm_iteratedFDeriv_coe_clm_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {i : ℕ} (hi : 1 ≤ i) (x : E) :
    ‖iteratedFDeriv ℝ i (⇑L) x‖ ≤ ‖L‖ := by
  rcases eq_or_lt_of_le hi with h | h
  · subst h
    rw [← iteratedFDerivWithin_univ, norm_iteratedFDerivWithin_one _ uniqueDiffWithinAt_univ,
      fderivWithin_univ, ContinuousLinearMap.fderiv]
  · obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    have hn : n ≠ 0 := by omega
    rw [← iteratedFDerivWithin_univ,
      ← norm_iteratedFDerivWithin_fderivWithin (𝕜 := ℝ) (s := Set.univ) (f := ⇑L)
        (n := n) (x := x) uniqueDiffOn_univ (Set.mem_univ x)]
    rw [show fderivWithin ℝ (⇑L) Set.univ = (fun _ : E => L) from by
      rw [fderivWithin_univ]; exact funext fun y => ContinuousLinearMap.fderiv L]
    rw [iteratedFDerivWithin_const_of_ne hn L]
    simp

private lemma iteratedFDeriv_clm_sub_eq_zero {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (L : E →L[ℝ] F) {n : ℕ} (hn : 1 ≤ n) (x y : E) :
    iteratedFDeriv ℝ n (fun z => L z) x - iteratedFDeriv ℝ n (fun z => L z) y = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hf : (fun z : E => fderiv ℝ (fun w => L w) z) = fun _ => L := by
    funext z
    rw [ContinuousLinearMap.fderiv]
  rw [iteratedFDeriv_succ_eq_comp_right (f := fun z : E => L z) (x := x) (n := m),
    iteratedFDeriv_succ_eq_comp_right (f := fun z : E => L z) (x := y) (n := m), hf]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp [iteratedFDeriv_zero_eq_comp]
  · rw [iteratedFDeriv_const_of_ne (by omega : m ≠ 0) L]
    simp

private lemma norm_prod_le_max {ι : Type*} [Fintype ι] {M' : ι → Type*}
    [∀ i, NormedAddCommGroup (M' i)] [∀ i, NormedSpace ℝ (M' i)]
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A : ContinuousMultilinearMap ℝ M' F) (B : ContinuousMultilinearMap ℝ M' G) :
    ‖A.prod B‖ ≤ max ‖A‖ ‖B‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (f := A.prod B) (M := max ‖A‖ ‖B‖)
    (le_max_of_le_left (norm_nonneg A)) fun v => ?_
  rw [ContinuousMultilinearMap.prod_apply, Prod.norm_def]
  refine max_le ?_ ?_
  · calc ‖A v‖ ≤ ‖A‖ * ∏ i, ‖v i‖ := A.le_opNorm v
      _ ≤ max ‖A‖ ‖B‖ * ∏ i, ‖v i‖ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Finset.prod_nonneg fun i _ => norm_nonneg _)
  · calc ‖B v‖ ≤ ‖B‖ * ∏ i, ‖v i‖ := B.le_opNorm v
      _ ≤ max ‖A‖ ‖B‖ * ∏ i, ‖v i‖ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (Finset.prod_nonneg fun i _ => norm_nonneg _)

private lemma norm_prod_sub_prod_le {ι : Type*} [Fintype ι] {M' : ι → Type*}
    [∀ i, NormedAddCommGroup (M' i)] [∀ i, NormedSpace ℝ (M' i)]
    {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (A A' : ContinuousMultilinearMap ℝ M' F) (B B' : ContinuousMultilinearMap ℝ M' G) :
    ‖A.prod B - A'.prod B'‖ ≤ max ‖A - A'‖ ‖B - B'‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (f := A.prod B - A'.prod B')
    (M := max ‖A - A'‖ ‖B - B'‖) (le_max_of_le_left (norm_nonneg _)) fun v => ?_
  have h1 : ‖(A - A') v‖ ≤ ‖A - A'‖ * ∏ i, ‖v i‖ := ContinuousMultilinearMap.le_opNorm _ v
  have h2 : ‖(B - B') v‖ ≤ ‖B - B'‖ * ∏ i, ‖v i‖ := ContinuousMultilinearMap.le_opNorm _ v
  have h3 : (0:ℝ) ≤ ∏ i, ‖v i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
  rw [sub_apply, ContinuousMultilinearMap.prod_apply, ContinuousMultilinearMap.prod_apply,
    Prod.mk_sub_mk, Prod.norm_def, max_mul_of_nonneg _ _ h3]
  exact max_le_max h1 h2

private lemma compContinuousLinearMap_sub {ι : Type*} [Fintype ι] {M₁ : ι → Type*}
    [∀ i, NormedAddCommGroup (M₁ i)] [∀ i, NormedSpace ℝ (M₁ i)]
    {G E' : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup E']
    [NormedSpace ℝ E']
    (g g' : ContinuousMultilinearMap ℝ M₁ G) (f : ∀ i, E' →L[ℝ] M₁ i) :
    g.compContinuousLinearMap f - g'.compContinuousLinearMap f
      = (g - g').compContinuousLinearMap f := by
  ext m
  simp [ContinuousMultilinearMap.compContinuousLinearMap_apply]

private lemma norm_snd_le_one : ‖ContinuousLinearMap.snd ℝ X ℂ‖ ≤ 1 := by
  rw [ContinuousLinearMap.opNorm_le_iff zero_le_one]
  intro v
  rw [one_mul]
  simpa [Prod.norm_def] using le_max_right ‖v.1‖ ‖v.2‖

/-! ## The composite `discTau ∘ snd` -/

private lemma iteratedFDeriv_discTau_snd (k : ℕ) (p : X × ℂ) :
    iteratedFDeriv ℝ k (fun q : X × ℂ => discTau q.2) p
      = (iteratedFDeriv ℝ k discTau p.2).compContinuousLinearMap
          (fun _ => ContinuousLinearMap.snd ℝ X ℂ) := by
  have hfun : (fun q : X × ℂ => discTau q.2)
      = discTau ∘ ⇑(ContinuousLinearMap.snd ℝ X ℂ) := rfl
  rw [hfun]
  rw [← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ)
        (f := discTau ∘ ⇑(ContinuousLinearMap.snd ℝ X ℂ)) (s := univ) k isOpen_univ (mem_univ p),
      ← iteratedFDerivWithin_of_isOpen (𝕜 := ℝ) (f := discTau) (s := univ) k isOpen_univ
        (mem_univ p.2)]
  exact ContinuousLinearMap.iteratedFDerivWithin_comp_right (𝕜 := ℝ)
    (g := ContinuousLinearMap.snd ℝ X ℂ) (f := discTau) (s := univ)
    (contDiff_top_discTau.contDiffOn) uniqueDiffOn_univ uniqueDiffOn_univ
    (x := p) (mem_univ p.2) (i := k) le_top

private lemma norm_iteratedFDeriv_discTau_snd_le (k : ℕ) (p : X × ℂ) {A : ℝ}
    (hA : ‖iteratedFDeriv ℝ k discTau p.2‖ ≤ A) :
    ‖iteratedFDeriv ℝ k (fun q : X × ℂ => discTau q.2) p‖ ≤ A := by
  rw [iteratedFDeriv_discTau_snd k p]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : (∏ _ : Fin k, ‖ContinuousLinearMap.snd ℝ X ℂ‖) ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) norm_snd_le_one
  calc ‖iteratedFDeriv ℝ k discTau p.2‖ * ∏ _ : Fin k, ‖ContinuousLinearMap.snd ℝ X ℂ‖
      ≤ ‖iteratedFDeriv ℝ k discTau p.2‖ * 1 := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ k discTau p.2‖ := mul_one _
    _ ≤ A := hA

private lemma norm_iteratedFDeriv_discTau_snd_sub_le (k : ℕ) (p q : X × ℂ) :
    ‖iteratedFDeriv ℝ k (fun r : X × ℂ => discTau r.2) p
      - iteratedFDeriv ℝ k (fun r : X × ℂ => discTau r.2) q‖
    ≤ ‖iteratedFDeriv ℝ k discTau p.2 - iteratedFDeriv ℝ k discTau q.2‖ := by
  rw [iteratedFDeriv_discTau_snd k p, iteratedFDeriv_discTau_snd k q,
    compContinuousLinearMap_sub]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hprod : (∏ _ : Fin k, ‖ContinuousLinearMap.snd ℝ X ℂ‖) ≤ 1 := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_one₀ (norm_nonneg _) norm_snd_le_one
  calc ‖iteratedFDeriv ℝ k discTau p.2 - iteratedFDeriv ℝ k discTau q.2‖
        * ∏ _ : Fin k, ‖ContinuousLinearMap.snd ℝ X ℂ‖
      ≤ ‖iteratedFDeriv ℝ k discTau p.2 - iteratedFDeriv ℝ k discTau q.2‖ * 1 :=
        mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ k discTau p.2 - iteratedFDeriv ℝ k discTau q.2‖ := mul_one _

/-! ## One-variable Hölder data for `discTau` on the disc of radius `c`

The bounds on the iterated derivatives come from compactness of `closedBall 0 c`; the
Lipschitz and Hölder statements then follow from the mean value inequality on the convex ball
`ball 0 c`. -/

private lemma discTau_holderData {c α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ L : ℝ, ∃ D E : ℕ → ℝ, 0 ≤ L ∧ (∀ m, 0 ≤ D m) ∧ (∀ m, 0 ≤ E m) ∧
      (∀ z w : ℂ, z ∈ ball (0:ℂ) c → w ∈ ball (0:ℂ) c →
        ‖discTau z - discTau w‖ ≤ L * ‖z - w‖) ∧
      (∀ m, 1 ≤ m → ∀ z : ℂ, z ∈ ball (0:ℂ) c →
        ‖iteratedFDeriv ℝ m discTau z‖ ≤ D m) ∧
      (∀ m, 1 ≤ m → ∀ z w : ℂ, z ∈ ball (0:ℂ) c → w ∈ ball (0:ℂ) c →
        ‖iteratedFDeriv ℝ m discTau z - iteratedFDeriv ℝ m discTau w‖ ≤ E m * ‖z - w‖ ^ α) := by
  have hcont : ∀ m : ℕ, Continuous fun z : ℂ => iteratedFDeriv ℝ m discTau z := fun m =>
    continuousOn_univ.mp (ContinuousOn.continuousOn_iteratedFDeriv (f := discTau) (s := univ)
      (contDiff_top_discTau.contDiffOn) isOpen_univ le_top)
  choose D0 hD0raw using fun m =>
    (isCompact_closedBall (0 : ℂ) c).exists_bound_of_continuousOn (hcont m).continuousOn
  set D : ℕ → ℝ := fun m => max (D0 m) 0 with hDdef
  have hD0 : ∀ m, 0 ≤ D m := fun m => le_max_right _ _
  have hD : ∀ m (z : ℂ), z ∈ closedBall (0 : ℂ) c → ‖iteratedFDeriv ℝ m discTau z‖ ≤ D m :=
    fun m z hz => (hD0raw m z hz).trans (le_max_left _ _)
  refine ⟨D 1, D, (fun m => max (D (m+1)) (2 * D m)), hD0 1, hD0,
    fun m => le_trans (hD0 (m+1)) (le_max_left _ _), ?_, ?_, ?_⟩
  · intro z w hz hw
    have hsub : ball (0:ℂ) c ⊆ closedBall (0:ℂ) c := ball_subset_closedBall
    have hdiff : ∀ u ∈ ball (0:ℂ) c, DifferentiableAt ℝ discTau u :=
      fun u _ => (contDiff_top_discTau.differentiable (by simp)).differentiableAt
    have hb : ∀ u ∈ ball (0:ℂ) c, ‖fderiv ℝ discTau u‖ ≤ D 1 := by
      intro u hu
      rw [← norm_iteratedFDeriv_one discTau]
      exact hD 1 u (hsub hu)
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := discTau)
      (C := D 1) (s := ball (0:ℂ) c) hdiff hb (convex_ball _ _) hz hw
    rw [norm_sub_rev z w, norm_sub_rev (discTau z) (discTau w)]
    exact h
  · intro m hm z hz
    exact hD m z (ball_subset_closedBall hz)
  · intro m hm z w hz hw
    have hsub : ball (0:ℂ) c ⊆ closedBall (0:ℂ) c := ball_subset_closedBall
    have hdiff : ∀ u ∈ ball (0:ℂ) c,
        DifferentiableAt ℝ (fun u => iteratedFDeriv ℝ m discTau u) u := by
      intro u hu
      exact (contDiff_top_discTau.contDiffAt.differentiableAt_iteratedFDeriv
        (WithTop.coe_lt_top (m : ℕ∞)))
    have hb : ∀ u ∈ ball (0:ℂ) c,
        ‖fderiv ℝ (fun u => iteratedFDeriv ℝ m discTau u) u‖ ≤ D (m+1) := by
      intro u hu
      rw [norm_fderiv_iteratedFDeriv]
      exact hD (m+1) u (hsub hu)
    have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ)
      (f := fun u => iteratedFDeriv ℝ m discTau u) (C := D (m+1)) (s := ball (0:ℂ) c)
      hdiff hb (convex_ball _ _) hz hw
    rcases le_total ‖z - w‖ 1 with h1 | h1
    · have hle : ‖z - w‖ ≤ ‖z - w‖ ^ α := by
        rcases eq_or_lt_of_le (norm_nonneg (z - w)) with h0 | h0
        · rw [← h0, Real.zero_rpow hα.ne']
        · have h2 : ‖z - w‖ ^ (1:ℝ) ≤ ‖z - w‖ ^ α :=
            Real.rpow_le_rpow_of_exponent_ge h0 h1 hα1
          rwa [Real.rpow_one] at h2
      calc ‖iteratedFDeriv ℝ m discTau z - iteratedFDeriv ℝ m discTau w‖
          = ‖(fun u => iteratedFDeriv ℝ m discTau u) w
             - (fun u => iteratedFDeriv ℝ m discTau u) z‖ := by rw [norm_sub_rev]
        _ ≤ D (m+1) * ‖w - z‖ := h
        _ = D (m+1) * ‖z - w‖ := by rw [norm_sub_rev]
        _ ≤ D (m+1) * ‖z - w‖ ^ α := mul_le_mul_of_nonneg_left hle (hD0 (m+1))
        _ ≤ max (D (m+1)) (2 * D m) * ‖z - w‖ ^ α :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) α)
    · have h2 : ‖iteratedFDeriv ℝ m discTau z - iteratedFDeriv ℝ m discTau w‖ ≤ 2 * D m := by
        refine (norm_sub_le _ _).trans ?_
        linarith [hD m z (hsub hz), hD m w (hsub hw)]
      have h3 : (1:ℝ) ≤ ‖z - w‖ ^ α := Real.one_le_rpow h1 hα.le
      calc ‖iteratedFDeriv ℝ m discTau z - iteratedFDeriv ℝ m discTau w‖
          ≤ 2 * D m := h2
        _ ≤ 2 * D m * ‖z - w‖ ^ α :=
            le_mul_of_one_le_right (mul_nonneg (by norm_num) (hD0 m)) h3
        _ ≤ max (D (m+1)) (2 * D m) * ‖z - w‖ ^ α :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg (norm_nonneg _) α)

/-! ## The target -/

theorem discFoldHolderData {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {c : ℝ} (hc : 1 < c) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    ∃ L : ℝ, ∃ D E : ℕ → ℝ,
      (∀ (U : Set X), IsOpen U → ∀ p : X × ℂ, p ∈ U ×ˢ Metric.ball (0 : ℂ) c →
        ∀ q : X × ℂ, q ∈ U ×ˢ Metric.ball (0 : ℂ) c →
        ‖Work.NN.Final.discFold p - Work.NN.Final.discFold q‖ ≤ L * ‖p - q‖) ∧
      (∀ (U : Set X), IsOpen U → ∀ m : ℕ, 1 ≤ m → ∀ p : X × ℂ,
        p ∈ U ×ˢ Metric.ball (0 : ℂ) c →
        ‖iteratedFDerivWithin ℝ m Work.NN.Final.discFold (U ×ˢ Metric.ball (0 : ℂ) c) p‖
          ≤ D m) ∧
      (∀ (U : Set X), IsOpen U → ∀ m : ℕ, 1 ≤ m → ∀ p : X × ℂ,
        p ∈ U ×ˢ Metric.ball (0 : ℂ) c → ∀ q : X × ℂ, q ∈ U ×ˢ Metric.ball (0 : ℂ) c →
        ‖iteratedFDerivWithin ℝ m Work.NN.Final.discFold (U ×ˢ Metric.ball (0 : ℂ) c) p
          - iteratedFDerivWithin ℝ m Work.NN.Final.discFold (U ×ˢ Metric.ball (0 : ℂ) c) q‖
          ≤ E m * ‖p - q‖ ^ α) := by
  obtain ⟨Lτ, Dτ, Eτ, hLτ0, hDτ0, hEτ0, hLipτ, hDτ, hEτ⟩ := discTau_holderData (c := c) hα hα1
  refine ⟨max 1 Lτ, (fun m => max 1 (Dτ m)), (fun m => max 0 (Eτ m)), ?_, ?_, ?_⟩
  · intro U hU p hp q hq
    rw [mem_prod] at hp hq
    have hdiff : discFold p - discFold q = (p - q, discTau p.2 - discTau q.2) := rfl
    rw [hdiff, Prod.norm_def]
    have hpq : ‖p.2 - q.2‖ ≤ ‖p - q‖ := by
      rw [show p - q = (p.1 - q.1, p.2 - q.2) from Prod.mk_sub_mk p.1 q.1 p.2 q.2, Prod.norm_def]
      exact le_max_right _ _
    have hτ : ‖discTau p.2 - discTau q.2‖ ≤ Lτ * ‖p.2 - q.2‖ := hLipτ p.2 q.2 hp.2 hq.2
    refine max_le ?_ ?_
    · calc ‖p - q‖ = 1 * ‖p - q‖ := (one_mul _).symm
        _ ≤ max 1 Lτ * ‖p - q‖ := mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
    · calc ‖discTau p.2 - discTau q.2‖ ≤ Lτ * ‖p.2 - q.2‖ := hτ
        _ ≤ Lτ * ‖p - q‖ := mul_le_mul_of_nonneg_left hpq hLτ0
        _ ≤ max 1 Lτ * ‖p - q‖ := mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _)
  · intro U hU m hm p hp
    rw [mem_prod] at hp
    have hS : IsOpen (U ×ˢ ball (0:ℂ) c) := hU.prod isOpen_ball
    rw [iteratedFDerivWithin_of_isOpen m hS hp]
    have hpair : iteratedFDeriv ℝ m discFold p
        = (iteratedFDeriv ℝ m (fun q : X × ℂ => q) p).prod
          (iteratedFDeriv ℝ m (fun q : X × ℂ => discTau q.2) p) := by
      have hfun : discFold = fun q : X × ℂ =>
          ((fun r : X × ℂ => r) q, (fun r : X × ℂ => discTau r.2) q) := rfl
      rw [hfun]
      exact iteratedFDeriv_prodMk (x := p)
        ((contDiff_id (𝕜 := ℝ) (n := (m : ℕ∞ω))).contDiffAt)
        ((contDiff_discTau_snd (X := X)).contDiffAt.of_le le_top) (i := m) le_rfl
    rw [hpair]
    refine (norm_prod_le_max _ _).trans ?_
    rw [max_le_iff]
    refine ⟨?_, ?_⟩
    · refine ((norm_iteratedFDeriv_coe_clm_le (ContinuousLinearMap.id ℝ (X × ℂ)) hm p).trans
        norm_id_le_one).trans ?_
      exact le_max_left _ _
    · exact (norm_iteratedFDeriv_discTau_snd_le m p (hDτ m hm p.2 hp.2)).trans (le_max_right _ _)
  · intro U hU m hm p hp q hq
    rw [mem_prod] at hp hq
    have hS : IsOpen (U ×ˢ ball (0:ℂ) c) := hU.prod isOpen_ball
    rw [iteratedFDerivWithin_of_isOpen m hS hp, iteratedFDerivWithin_of_isOpen m hS hq]
    have hpairp : iteratedFDeriv ℝ m discFold p
        = (iteratedFDeriv ℝ m (fun r : X × ℂ => r) p).prod
          (iteratedFDeriv ℝ m (fun r : X × ℂ => discTau r.2) p) := by
      have hfun : discFold = fun r : X × ℂ =>
          ((fun s : X × ℂ => s) r, (fun s : X × ℂ => discTau s.2) r) := rfl
      rw [hfun]
      exact iteratedFDeriv_prodMk (x := p)
        ((contDiff_id (𝕜 := ℝ) (n := (m : ℕ∞ω))).contDiffAt)
        ((contDiff_discTau_snd (X := X)).contDiffAt.of_le le_top) (i := m) le_rfl
    have hpairq : iteratedFDeriv ℝ m discFold q
        = (iteratedFDeriv ℝ m (fun r : X × ℂ => r) q).prod
          (iteratedFDeriv ℝ m (fun r : X × ℂ => discTau r.2) q) := by
      have hfun : discFold = fun r : X × ℂ =>
          ((fun s : X × ℂ => s) r, (fun s : X × ℂ => discTau s.2) r) := rfl
      rw [hfun]
      exact iteratedFDeriv_prodMk (x := q)
        ((contDiff_id (𝕜 := ℝ) (n := (m : ℕ∞ω))).contDiffAt)
        ((contDiff_discTau_snd (X := X)).contDiffAt.of_le le_top) (i := m) le_rfl
    rw [hpairp, hpairq]
    refine (norm_prod_sub_prod_le _ _ _ _).trans ?_
    rw [max_le_iff]
    refine ⟨?_, ?_⟩
    · have h0 : iteratedFDeriv ℝ m (fun r : X × ℂ => r) p
          - iteratedFDeriv ℝ m (fun r : X × ℂ => r) q = 0 :=
        iteratedFDeriv_clm_sub_eq_zero (ContinuousLinearMap.id ℝ (X × ℂ)) hm p q
      rw [h0, norm_zero]
      exact mul_nonneg (le_max_left _ _) (Real.rpow_nonneg (norm_nonneg _) α)
    · have hpq : ‖p.2 - q.2‖ ^ α ≤ ‖p - q‖ ^ α := by
        refine Real.rpow_le_rpow (norm_nonneg _) ?_ hα.le
        rw [show p - q = (p.1 - q.1, p.2 - q.2) from Prod.mk_sub_mk p.1 q.1 p.2 q.2,
          Prod.norm_def]
        exact le_max_right _ _
      refine (norm_iteratedFDeriv_discTau_snd_sub_le m p q).trans ?_
      refine ((hEτ m hm p.2 q.2 hp.2 hq.2).trans
        (mul_le_mul_of_nonneg_left hpq (hEτ0 m))).trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_right 0 (Eτ m))
        (Real.rpow_nonneg (norm_nonneg _) α)

end Work.NN.Final
