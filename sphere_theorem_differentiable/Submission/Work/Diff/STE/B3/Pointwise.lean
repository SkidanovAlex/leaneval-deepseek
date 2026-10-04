import Mathlib
import Submission.Work.Diff.STE.B3.Recon

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Layer B3: the pointwise control of a section by the composite norm

For `card ι < 2 k` and a section `h` whose localised periodised components are `C^∞` and
`1`-periodic, the value of `h` at a point is controlled by the composite norm:

  `|h x u v| ≤ C √(BNorm k h) √(g₀.inner x u u) √(g₀.inner x v v)`.

The proof picks a chart `i` for which `ζ i x` is maximal (so `ζ i x ≥ 1/√(card ι₀)`, using
`Σ i, ζ i x ^ 2 = 1`), expands `h x u v` in the `g₀`-orthonormal frame `e i` at `x`, and bounds each
chart-matrix entry by `Rper_norm_le_sqrt_BNorm` divided by `ζ i x`.
-/

noncomputable section

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.STE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}

namespace B3Data

variable (D : B3Data (I := I) (M := M) ι₀ g₀)

/-- **Parseval for an orthonormal frame**: the sum of the squares of the coefficients of `u` in the
`g₀`-orthonormal frame `e i` at `x` is the square of the length of `u`. -/
lemma sum_inner_sq (i : ι₀) {x : M} (hON : IsONFrame g₀ x (fun a => D.e i a x))
    (u : TangentSpace I x) :
    ∑ a : Fin (Module.finrank ℝ E), (g₀.inner x u (D.e i a x)) ^ 2 = g₀.inner x u u := by
  have hu : u = ∑ a : Fin (Module.finrank ℝ E),
      g₀.inner x u (D.e i a x) • D.e i a x :=
    (Work.EXT.sum_inner_smul_eq_self_of_isONFrame g₀ x (fun a => D.e i a x) hON u).symm
  have hsplit : (g₀.inner x u) (∑ a : Fin (Module.finrank ℝ E),
        g₀.inner x u (D.e i a x) • D.e i a x)
      = ∑ a : Fin (Module.finrank ℝ E),
        g₀.inner x u (D.e i a x) * g₀.inner x u (D.e i a x) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun a _ => by rw [map_smul, smul_eq_mul]
  have hsplit2 : (g₀.inner x u) u
      = ∑ a : Fin (Module.finrank ℝ E),
        g₀.inner x u (D.e i a x) * g₀.inner x u (D.e i a x) := by
    nth_rewrite 2 [hu]
    rw [hsplit]
  rw [hsplit2]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- The sum of the absolute values of the coefficients of `u` in the orthonormal frame `e i` is at
most `√(card ι₀) · ‖u‖`. -/
lemma sum_abs_inner_le (i : ι₀) {x : M} (hON : IsONFrame g₀ x (fun a => D.e i a x))
    (u : TangentSpace I x) :
    ∑ a : Fin (Module.finrank ℝ E), |g₀.inner x u (D.e i a x)|
      ≤ Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x u u) := by
  have hcs : (∑ a : Fin (Module.finrank ℝ E), |g₀.inner x u (D.e i a x)|) ^ 2
      ≤ (Module.finrank ℝ E : ℝ) * ∑ a : Fin (Module.finrank ℝ E),
          (g₀.inner x u (D.e i a x)) ^ 2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq
      (s := (Finset.univ : Finset (Fin (Module.finrank ℝ E))))
      (f := fun a => |g₀.inner x u (D.e i a x)|) (g := fun _ => (1 : ℝ))
    simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, sq_abs] at h
    linarith [h]
  rw [D.sum_inner_sq i hON u] at hcs
  have hnn : 0 ≤ ∑ a : Fin (Module.finrank ℝ E), |g₀.inner x u (D.e i a x)| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  calc ∑ a : Fin (Module.finrank ℝ E), |g₀.inner x u (D.e i a x)|
      = Real.sqrt ((∑ a : Fin (Module.finrank ℝ E), |g₀.inner x u (D.e i a x)|) ^ 2) :=
        (Real.sqrt_sq hnn).symm
    _ ≤ Real.sqrt ((Module.finrank ℝ E : ℝ) * g₀.inner x u u) := Real.sqrt_le_sqrt hcs
    _ = Real.sqrt (Module.finrank ℝ E) * Real.sqrt (g₀.inner x u u) :=
        Real.sqrt_mul (by positivity) _

/-- **The pointwise control of a section by the composite norm.** -/
theorem pointwise_bound (k : ℕ)
    (hk : Fintype.card (Fin (Module.finrank ℝ E)) < 2 * k)
    (h : Bil (I := I) (M := M))
    (hsm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i h a b))
    (hper : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Periodic1 (D.Rper i h a b))
    (hdens : ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ 2 * D.σ i → d₀ ≤ D.dens i z) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : M) (u v : TangentSpace I x),
      |h x u v| ≤ C * Real.sqrt (D.BNorm k h)
        * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) := by
  obtain ⟨C₁, hC₁, hC₁b⟩ := D.Rper_norm_le_sqrt_BNorm k hk h hsm hper
  obtain ⟨d₀, hd₀pos, hd₀b⟩ := hdens
  have hsqrtpos : 0 < Real.sqrt d₀ := Real.sqrt_pos.mpr hd₀pos
  have hKn : (0 : ℝ) ≤ C₁ * Real.sqrt (D.BNorm k h) * Real.sqrt (Fintype.card ι₀) :=
    mul_nonneg (mul_nonneg hC₁ (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hK' : (0 : ℝ) ≤
      C₁ * Real.sqrt (D.BNorm k h) * Real.sqrt (Fintype.card ι₀) * (Real.sqrt d₀)⁻¹ :=
    mul_nonneg hKn (inv_nonneg.mpr (Real.sqrt_nonneg _))
  refine ⟨C₁ * (Module.finrank ℝ E : ℝ) * Real.sqrt (Fintype.card ι₀) * (Real.sqrt d₀)⁻¹,
    by positivity, ?_⟩
  intro x u v
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
  have hlt' : ‖coord (I := I) (D.x₀ i) x‖ ≤ 2 * D.σ i :=
    le_of_lt (lt_of_lt_of_le hlt (by linarith [D.hσ i, D.hσ2 i]))
  have hON : IsONFrame g₀ x (fun a => D.e i a x) := by
    have h0 := D.heON i (coord (I := I) (D.x₀ i) x) hlt'
    rw [D.symm_flatToE_coord i hsrc] at h0
    exact h0
  have hcoord : ∀ j, coord (I := I) (D.x₀ i) x j ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
    intro j
    have h1 : |coord (I := I) (D.x₀ i) x j| ≤ ‖coord (I := I) (D.x₀ i) x‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (coord (I := I) (D.x₀ i) x) j
    have h2 : ‖coord (I := I) (D.x₀ i) x‖ < (1 / 2 : ℝ) :=
      lt_of_lt_of_le hlt (by linarith [D.hσ i, D.hσ2 i])
    exact abs_lt.mp (lt_of_le_of_lt h1 h2)
  have hdensge : Real.sqrt d₀ ≤ Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) x)) :=
    Real.sqrt_le_sqrt (hd₀b i _ hlt')
  have sqpos : 0 < Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) x)) :=
    lt_of_lt_of_le (Real.sqrt_pos.mpr hd₀pos) hdensge
  have hmat : ∀ a b : Fin (Module.finrank ℝ E),
      |D.mat i h a b (coord (I := I) (D.x₀ i) x)|
        ≤ C₁ * Real.sqrt (D.BNorm k h) * Real.sqrt (Fintype.card ι₀) * (Real.sqrt d₀)⁻¹ := by
    intro a b
    have hpsi : D.psi i (coord (I := I) (D.x₀ i) x) = D.ζ i x :=
      D.psi_coord_eq_zeta i (ne_of_gt hζpos)
    have hR : D.R i h a b (coord (I := I) (D.x₀ i) x)
        = D.ζ i x * Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) x))
          * D.mat i h a b (coord (I := I) (D.x₀ i) x) := by
      simp only [R, hpsi]
    have hnorm : ‖D.Rper i h a b (coord (I := I) (D.x₀ i) x)‖
        = D.ζ i x * Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) x))
          * |D.mat i h a b (coord (I := I) (D.x₀ i) x)| := by
      have h1 : D.Rper i h a b (coord (I := I) (D.x₀ i) x)
          = ((D.ζ i x * Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) x))
              * D.mat i h a b (coord (I := I) (D.x₀ i) x) : ℝ) : ℂ) := by
        rw [D.Rper_eq_R i h a b hcoord, hR]
      have hnormC : ∀ r : ℝ, ‖((r : ℝ) : ℂ)‖ = |r| := fun r => by
        rw [← Real.sqrt_sq (norm_nonneg _), Complex.sq_norm, Complex.normSq_ofReal,
          ← sq, Real.sqrt_sq_eq_abs]
      rw [h1, hnormC, abs_mul, abs_mul, abs_of_pos hζpos, abs_of_pos sqpos]
    have hub := hC₁b i a b (coord (I := I) (D.x₀ i) x)
    rw [hnorm] at hub
    have hkey : |D.mat i h a b (coord (I := I) (D.x₀ i) x)|
        ≤ (Real.sqrt (Fintype.card ι₀)) * (Real.sqrt d₀)⁻¹
          * (D.ζ i x * Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) x))
              * |D.mat i h a b (coord (I := I) (D.x₀ i) x)|) := by
      have h1 : (Real.sqrt (Fintype.card ι₀)) * (Real.sqrt (Fintype.card ι₀))⁻¹ = 1 :=
        mul_inv_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr hNpos))
      have h2 : 1 ≤ (Real.sqrt (Fintype.card ι₀)) * D.ζ i x := by
        calc (1 : ℝ)
            = (Real.sqrt (Fintype.card ι₀)) * (Real.sqrt (Fintype.card ι₀))⁻¹ := h1.symm
          _ ≤ (Real.sqrt (Fintype.card ι₀)) * D.ζ i x :=
              mul_le_mul_of_nonneg_left hζge (Real.sqrt_nonneg _)
      have h3 : 1 ≤ Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) x)) * (Real.sqrt d₀)⁻¹ := by
        calc (1 : ℝ) = Real.sqrt d₀ * (Real.sqrt d₀)⁻¹ :=
              (mul_inv_cancel₀ hsqrtpos.ne').symm
          _ ≤ Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) x)) * (Real.sqrt d₀)⁻¹ :=
              mul_le_mul_of_nonneg_right hdensge (inv_nonneg.mpr (Real.sqrt_nonneg _))
      have h4 : 1 ≤ (Real.sqrt (Fintype.card ι₀)) * (Real.sqrt d₀)⁻¹
          * (D.ζ i x * Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) x))) := by
        calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
          _ ≤ ((Real.sqrt (Fintype.card ι₀)) * D.ζ i x)
                * (Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) x)) * (Real.sqrt d₀)⁻¹) :=
              mul_le_mul h2 h3 (by positivity) (by positivity)
          _ = (Real.sqrt (Fintype.card ι₀)) * (Real.sqrt d₀)⁻¹
                * (D.ζ i x * Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) x))) := by ring
      nlinarith [h4, abs_nonneg (D.mat i h a b (coord (I := I) (D.x₀ i) x))]
    calc |D.mat i h a b (coord (I := I) (D.x₀ i) x)|
        ≤ (Real.sqrt (Fintype.card ι₀)) * (Real.sqrt d₀)⁻¹
          * (D.ζ i x * Real.sqrt (D.dens i (coord (I := I) (D.x₀ i) x))
              * |D.mat i h a b (coord (I := I) (D.x₀ i) x)|) := hkey
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
        D.mat i h a b (coord (I := I) (D.x₀ i) x)
          * g₀.inner x u (D.e i a x) * g₀.inner x v (D.e i b x)|
      ≤ (C₁ * Real.sqrt (D.BNorm k h) * Real.sqrt (Fintype.card ι₀) * (Real.sqrt d₀)⁻¹)
        * (∑ a : Fin (Module.finrank ℝ E), |g₀.inner x u (D.e i a x)|)
        * (∑ b : Fin (Module.finrank ℝ E), |g₀.inner x v (D.e i b x)|) := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    have hswap : (∑ a : Fin (Module.finrank ℝ E), |∑ b : Fin (Module.finrank ℝ E),
          D.mat i h a b (coord (I := I) (D.x₀ i) x)
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

end B3Data

end Work.Diff.STE
