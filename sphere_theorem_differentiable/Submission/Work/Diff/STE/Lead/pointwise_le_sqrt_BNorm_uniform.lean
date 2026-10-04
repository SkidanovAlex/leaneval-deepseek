import Mathlib
import Submission.Work.Diff.STE.B3.Pointwise

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: the pointwise control of a section by the composite norm, uniformly in the section

`Work.Diff.STE.B3Data.pointwise_bound` controls the value of a section `h` at a point by
`√(D.BNorm k h)`, but its constant is extracted from
`D.Rper_norm_le_sqrt_BNorm k hk h hsm hper` and is therefore allowed to depend on `h`.

The present file removes that dependence.  The reason it can be removed is that the Sobolev-type
constant of `Work.Diff.STE.norm_seriesFun_le` is uniform in the coefficient family: it is
`√(Σ_k ⟨k⟩^{-2s})`, a function of the index type and `k` only.  Re-running the extraction of
`D.Rper_norm_le_sqrt_BNorm` with the quantifier over `h` inside gives a single constant `C₁` with

  `‖D.Rper i h a b z‖ ≤ C₁ √(D.BNorm k h)`   for all `h`, `i`, `a`, `b`, `z`,

and then the (verbatim) pointwise assembly of `pointwise_bound` produces a single `C` valid for
every section `h`.
-/

noncomputable section

namespace Work.Diff.STE.Lead

/-- **Uniform sup-norm bound for the localised periodised components.**  The constant of
`Work.Diff.STE.B3Data.Rper_norm_le_sqrt_BNorm` can be chosen independently of the section `h`
(and of its smoothness/periodicity proofs). -/
lemma Rper_norm_le_sqrt_BNorm_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (hk : Fintype.card (Fin (Module.finrank ℝ E)) < 2 * k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hsm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        ContDiff ℝ (⊤ : ℕ∞) (D.Rper i h a b))
      (hper : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        Work.Diff.STE.Periodic1 (D.Rper i h a b))
      (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖D.Rper i h a b z‖ ≤ C * Real.sqrt (D.BNorm k h) := by
  obtain ⟨C, hC, hCb⟩ := Work.Diff.STE.norm_seriesFun_le (ι := Fin (Module.finrank ℝ E)) k hk
  refine ⟨C, hC, ?_⟩
  intro h hsm hper i a b z
  have hinv : Work.Diff.STE.seriesFun (Work.Diff.STE.fourierCoeff (D.Rper i h a b)) z
      = D.Rper i h a b z :=
    Work.Diff.STE.flat.seriesFun_fourierCoeff (D.Rper i h a b) (hsm i a b) (hper i a b) z
  rw [← hinv]
  refine (hCb _ (Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff _ (hsm i a b)
    (hper i a b) k) z).trans (mul_le_mul_of_nonneg_left ?_ hC)
  refine Real.sqrt_le_sqrt ?_
  have hle : Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b))
      ≤ D.BNorm k h := by
    change Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b))
      ≤ ∑ i' : ι₀, ∑ a' : Fin (Module.finrank ℝ E),
          ∑ b' : Fin (Module.finrank ℝ E),
          Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i' h a' b'))
    exact Work.Diff.STE.sum3_single_le
      (fun i' a' b' => Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i' h a' b')))
      (fun i' a' b' => Work.Diff.STE.CSq_nonneg k _) i a b
  exact hle

theorem pointwise_le_sqrt_BNorm_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ)
    (hk : Fintype.card (Fin (Module.finrank ℝ E)) < 2 * k)
    (hdens : ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ 2 * D.σ i → d₀ ≤ D.dens i z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M)),
      (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        ContDiff ℝ (⊤ : ℕ∞) (D.Rper i h a b)) →
      (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        Work.Diff.STE.Periodic1 (D.Rper i h a b)) →
      ∀ (x : M) (u v : TangentSpace I x),
      |h x u v| ≤ C * Real.sqrt (D.BNorm k h)
        * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) := by
  obtain ⟨C₁, hC₁, hC₁b⟩ := Rper_norm_le_sqrt_BNorm_uniform (I := I) (M := M) D k hk
  obtain ⟨d₀, hd₀pos, hd₀b⟩ := hdens
  refine ⟨C₁ * (Module.finrank ℝ E : ℝ) * Real.sqrt (Fintype.card ι₀) * (Real.sqrt d₀)⁻¹,
    by positivity, ?_⟩
  intro h hsm hper x u v
  have hsqrtpos : 0 < Real.sqrt d₀ := Real.sqrt_pos.mpr hd₀pos
  have hKn : (0 : ℝ) ≤ C₁ * Real.sqrt (D.BNorm k h) * Real.sqrt (Fintype.card ι₀) :=
    mul_nonneg (mul_nonneg hC₁ (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hK' : (0 : ℝ) ≤
      C₁ * Real.sqrt (D.BNorm k h) * Real.sqrt (Fintype.card ι₀) * (Real.sqrt d₀)⁻¹ :=
    mul_nonneg hKn (inv_nonneg.mpr (Real.sqrt_nonneg _))
  haveI hne : Nonempty ι₀ := by
    by_contra hι
    have hsum := D.hζsq x
    have hempty : (Finset.univ : Finset ι₀) = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr fun i _ => hι ⟨i⟩
    rw [hempty, Finset.sum_empty] at hsum
    exact one_ne_zero hsum.symm
  have hNpos : (0 : ℝ) < (Fintype.card ι₀ : ℝ) := by exact_mod_cast Fintype.card_pos
  obtain ⟨i, hi⟩ : ∃ i : ι₀, (Fintype.card ι₀ : ℝ)⁻¹ ≤ (D.ζ i x) ^ 2 := by
    by_contra hcon
    push_neg at hcon
    have hlt := Finset.sum_lt_sum_of_nonempty (Finset.univ_nonempty) (fun i _ => hcon i)
    rw [D.hζsq x] at hlt
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hlt
    rw [mul_inv_cancel₀ (ne_of_gt hNpos)] at hlt
    exact lt_irrefl _ hlt
  have hζpos : 0 < D.ζ i x := by
    have hp : 0 < (Fintype.card ι₀ : ℝ)⁻¹ := inv_pos.mpr hNpos
    nlinarith [D.hζnn i x, sq_nonneg (D.ζ i x), hi, hp]
  have hζge : (Real.sqrt (Fintype.card ι₀))⁻¹ ≤ D.ζ i x := by
    rw [← Real.sqrt_inv, ← Real.sqrt_sq hζpos.le]
    exact Real.sqrt_le_sqrt hi
  obtain ⟨hsrc, hlt⟩ := D.hζsupp i x (ne_of_gt hζpos)
  have hlt' : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) x‖ ≤ 2 * D.σ i :=
    le_of_lt (lt_of_lt_of_le hlt (by linarith [D.hσ i, D.hσ2 i]))
  have hON : Submission.Diff.IsONFrame g₀ x (fun a => D.e i a x) := by
    have h0 := D.heON i (Work.Diff.STE.coord (I := I) (D.x₀ i) x) hlt'
    rw [D.symm_flatToE_coord i hsrc] at h0
    exact h0
  have hcoord : ∀ j, Work.Diff.STE.coord (I := I) (D.x₀ i) x j
        ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    intro j
    have h1 : |Work.Diff.STE.coord (I := I) (D.x₀ i) x j|
        ≤ ‖Work.Diff.STE.coord (I := I) (D.x₀ i) x‖ := by
      simpa only [Real.norm_eq_abs] using
        norm_le_pi_norm (Work.Diff.STE.coord (I := I) (D.x₀ i) x) j
    have h2 : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) x‖ < (1 / 2 : ℝ) :=
      lt_of_lt_of_le hlt (by linarith [D.hσ i, D.hσ2 i])
    exact abs_lt.mp (lt_of_le_of_lt h1 h2)
  have hdensge : Real.sqrt d₀ ≤ Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)) :=
    Real.sqrt_le_sqrt (hd₀b i _ hlt')
  have sqpos : 0 < Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)) :=
    lt_of_lt_of_le (Real.sqrt_pos.mpr hd₀pos) hdensge
  have hmat : ∀ a b : Fin (Module.finrank ℝ E),
      |D.mat i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)|
        ≤ C₁ * Real.sqrt (D.BNorm k h) * Real.sqrt (Fintype.card ι₀) * (Real.sqrt d₀)⁻¹ := by
    intro a b
    have hpsi : D.psi i (Work.Diff.STE.coord (I := I) (D.x₀ i) x) = D.ζ i x :=
      D.psi_coord_eq_zeta i (ne_of_gt hζpos)
    have hR : D.R i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
        = D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
          * D.mat i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x) := by
      simp only [Work.Diff.STE.B3Data.R, hpsi]
    have hnorm : ‖D.Rper i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)‖
        = D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
          * |D.mat i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)| := by
      have h1 : D.Rper i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
          = ((D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
              * D.mat i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x) : ℝ) : ℂ) := by
        rw [D.Rper_eq_R i h a b hcoord, hR]
      have hnormC : ∀ r : ℝ, ‖((r : ℝ) : ℂ)‖ = |r| := fun r => by
        rw [← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, Complex.normSq_ofReal,
          ← sq, Real.sqrt_sq_eq_abs]
      rw [h1, hnormC, abs_mul, abs_mul, abs_of_pos hζpos, abs_of_pos sqpos]
    have hub := hC₁b h hsm hper i a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
    rw [hnorm] at hub
    have hkey : |D.mat i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)|
        ≤ (Real.sqrt (Fintype.card ι₀)) * (Real.sqrt d₀)⁻¹
          * (D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
              * |D.mat i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)|) := by
      have h1 : (Real.sqrt (Fintype.card ι₀)) * (Real.sqrt (Fintype.card ι₀))⁻¹ = 1 :=
        mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hNpos))
      have h2 : 1 ≤ (Real.sqrt (Fintype.card ι₀)) * D.ζ i x := by
        calc (1 : ℝ)
            = (Real.sqrt (Fintype.card ι₀)) * (Real.sqrt (Fintype.card ι₀))⁻¹ := h1.symm
          _ ≤ (Real.sqrt (Fintype.card ι₀)) * D.ζ i x :=
              mul_le_mul_of_nonneg_left hζge (Real.sqrt_nonneg _)
      have h3 : 1 ≤ Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
          * (Real.sqrt d₀)⁻¹ := by
        calc (1 : ℝ) = Real.sqrt d₀ * (Real.sqrt d₀)⁻¹ :=
              (mul_inv_cancel₀ hsqrtpos.ne').symm
          _ ≤ Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
                * (Real.sqrt d₀)⁻¹ :=
              mul_le_mul_of_nonneg_right hdensge (inv_nonneg.mpr (Real.sqrt_nonneg _))
      have h4 : 1 ≤ (Real.sqrt (Fintype.card ι₀)) * (Real.sqrt d₀)⁻¹
          * (D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x))) := by
        calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
          _ ≤ ((Real.sqrt (Fintype.card ι₀)) * D.ζ i x)
                * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
                  * (Real.sqrt d₀)⁻¹) :=
              mul_le_mul h2 h3 (by positivity) (by positivity)
          _ = (Real.sqrt (Fintype.card ι₀)) * (Real.sqrt d₀)⁻¹
                * (D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x))) := by
              ring
      nlinarith [h4, abs_nonneg (D.mat i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x))]
    calc |D.mat i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)|
        ≤ (Real.sqrt (Fintype.card ι₀)) * (Real.sqrt d₀)⁻¹
          * (D.ζ i x * Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x))
              * |D.mat i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)|) := hkey
      _ ≤ (Real.sqrt (Fintype.card ι₀)) * (Real.sqrt d₀)⁻¹
            * (C₁ * Real.sqrt (D.BNorm k h)) :=
          mul_le_mul_of_nonneg_left hub
            (mul_nonneg (Real.sqrt_nonneg _) (inv_nonneg.mpr (Real.sqrt_nonneg _)))
      _ = C₁ * Real.sqrt (D.BNorm k h) * Real.sqrt (Fintype.card ι₀) * (Real.sqrt d₀)⁻¹ := by
          ring
  rw [D.apply_eq_sum_mat i h hsrc hON u v]
  have hsum1 := D.sum_abs_inner_le i hON u
  have hsum2 := D.sum_abs_inner_le i hON v
  have hmain : |∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        D.mat i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
          * g₀.inner x u (D.e i a x) * g₀.inner x v (D.e i b x)|
      ≤ (C₁ * Real.sqrt (D.BNorm k h) * Real.sqrt (Fintype.card ι₀) * (Real.sqrt d₀)⁻¹)
        * (∑ a : Fin (Module.finrank ℝ E), |g₀.inner x u (D.e i a x)|)
        * (∑ b : Fin (Module.finrank ℝ E), |g₀.inner x v (D.e i b x)|) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hswap : (∑ a : Fin (Module.finrank ℝ E), |∑ b : Fin (Module.finrank ℝ E),
          D.mat i h a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
            * g₀.inner x u (D.e i a x) * g₀.inner x v (D.e i b x)|)
        ≤ ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (C₁ * Real.sqrt (D.BNorm k h) * Real.sqrt (Fintype.card ι₀) * (Real.sqrt d₀)⁻¹)
            * |g₀.inner x u (D.e i a x)| * |g₀.inner x v (D.e i b x)| := by
      refine Finset.sum_le_sum fun a _ => ?_
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      refine Finset.sum_le_sum fun b _ => ?_
      rw [abs_mul, abs_mul]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hmat a b) (abs_nonneg _))
        (abs_nonneg _)
    refine hswap.trans (le_of_eq ?_)
    rw [← Finset.sum_mul_sum, ← Finset.mul_sum]
  refine hmain.trans ?_
  have hstep : (C₁ * Real.sqrt (D.BNorm k h) * Real.sqrt (Fintype.card ι₀) * (Real.sqrt d₀)⁻¹)
        * (∑ a : Fin (Module.finrank ℝ E), |g₀.inner x u (D.e i a x)|)
        * (∑ b : Fin (Module.finrank ℝ E), |g₀.inner x v (D.e i b x)|)
      ≤ (C₁ * Real.sqrt (D.BNorm k h) * Real.sqrt (Fintype.card ι₀) * (Real.sqrt d₀)⁻¹)
        * (Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x u u))
        * (Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x v v)) := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left hsum1 hK') hsum2 ?_ ?_
    · exact Finset.sum_nonneg fun _ _ => abs_nonneg _
    · exact mul_nonneg hK' (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  refine hstep.trans (le_of_eq ?_)
  ring_nf
  rw [Real.sq_sqrt (Nat.cast_nonneg _)]
  ring

end Work.Diff.STE.Lead
