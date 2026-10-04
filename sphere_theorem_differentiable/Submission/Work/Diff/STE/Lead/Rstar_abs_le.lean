import Mathlib
import Submission.Work.Diff.STE.B3.Rstar_apply
import Submission.Work.Diff.STE.B3.Pointwise
import Submission.Work.Diff.STE.B3.BPairDefs
import Submission.Work.Diff.STE.B3.dens_bound_sigma

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

open Bundle

/-! ## Elementary estimates used in the pointwise bound of the reconstruction

The reconstruction `D.Rstar i u` is the bilinear form whose value at `(v,w)` is
`(ζ i x · χ i (coord i x) · (√(dens i (coord i x)))⁻¹) · Σ_{ab} u a b (coord i x) · ⟪v, e i a⟫ ·
⟪w, e i b⟫` (`Work.Diff.STE.B3.Rstar_apply`).  The three estimates below handle the two factors:

* `sum_sq_inner_le_of_isONFrame`: **Bessel's inequality** for a `g`-orthonormal frame,
  `Σ_a ⟪v, e a⟫² ≤ ⟪v,v⟫` (Mathlib's `Orthonormal.sum_inner_products_le` after transporting along
  the inner product space structure induced by `g`);
* `sum_abs_le_sqrt_card_mul_sqrt_sum_sq`: the `ℓ¹`-`ℓ²` Cauchy–Schwarz inequality
  `Σ |f i| ≤ √n · √(Σ (f i)²)`;
* `abs_double_sum_mul_le`: the elementary bound `|Σ_a Σ_b U a b · x a · y b| ≤
  Mv · (Σ_a |x a|) · (Σ_b |y b|)` for `|U a b| ≤ Mv`.

Together they give the sharp `√(finrank) · √⟪v,v⟫` estimate for the frame sum, which is what makes
the claimed bound `Mv · n · √⟪v,v⟫ · √⟪w,w⟫` (rather than the cruder `Mv · n² · ...` of the
`mat_Rstar_bound` estimate) true. -/

/-- **Bessel's inequality for a `g`-orthonormal frame.**  If `e` is `g`-orthonormal at `x`, then
`Σ_a ⟪v, e a⟫² ≤ ⟪v, v⟫`.  (No hypothesis on the cardinality of the frame is needed: the inequality
of Bessel holds for any orthonormal family, and it is the *inequality* that the reconstruction bound
requires.) -/
private theorem sum_sq_inner_le_of_isONFrame
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    (g : Submission.Diff.SMet I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (he : Submission.Diff.IsONFrame g x e) (v : TangentSpace I x) :
    ∑ i, (g.inner x v (e i)) ^ 2 ≤ g.inner x v v := by
  letI : Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  have key : ∀ a b : TangentSpace I x, inner ℝ a b = g.inner x a b := fun a b => rfl
  have hon : Orthonormal ℝ e := by
    rw [orthonormal_iff_ite]
    intro i j
    exact he i j
  have hb : ∑ i : Fin (Module.finrank ℝ E), ‖inner ℝ (e i) v‖ ^ 2 ≤ ‖v‖ ^ 2 :=
    Orthonormal.sum_inner_products_le (𝕜 := ℝ) (s := Finset.univ) v hon
  have hb' : ∑ i : Fin (Module.finrank ℝ E), (g.inner x v (e i)) ^ 2 ≤ ‖v‖ ^ 2 := by
    refine le_of_eq_of_le ?_ hb
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Real.norm_eq_abs, sq_abs, real_inner_comm, key]
  rw [← real_inner_self_eq_norm_sq v, key v v] at hb'
  exact hb'

/-- **The `ℓ¹`-`ℓ²` Cauchy–Schwarz inequality**: `Σ_i |f i| ≤ √n · √(Σ_i (f i)²)`. -/
private theorem sum_abs_le_sqrt_card_mul_sqrt_sum_sq
    {n : ℕ} (f : Fin n → ℝ) :
    ∑ i, |f i| ≤ Real.sqrt (n : ℝ) * Real.sqrt (∑ i, (f i) ^ 2) := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n)))
    (f := fun i => |f i|)
  have h2 : (∑ i, |f i|) ^ 2 ≤ (n : ℝ) * ∑ i, (f i) ^ 2 := by
    simpa only [Finset.card_univ, Fintype.card_fin, sq_abs] using h
  have h0 : 0 ≤ ∑ i, |f i| := Finset.sum_nonneg fun i _ => abs_nonneg _
  calc ∑ i, |f i| = Real.sqrt ((∑ i, |f i|) ^ 2) := (Real.sqrt_sq h0).symm
    _ ≤ Real.sqrt ((n : ℝ) * ∑ i, (f i) ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt (n : ℝ) * Real.sqrt (∑ i, (f i) ^ 2) :=
        Real.sqrt_mul (Nat.cast_nonneg n) _

/-- **The double-sum estimate**: for `|U a b| ≤ Mv`,
`|Σ_a Σ_b U a b · x a · y b| ≤ Mv · (Σ_a |x a|) · (Σ_b |y b|)`. -/
private theorem abs_double_sum_mul_le
    {n : ℕ} (U : Fin n → Fin n → ℝ) (x y : Fin n → ℝ) {Mv : ℝ}
    (hU : ∀ a b, |U a b| ≤ Mv) :
    |∑ a, ∑ b, U a b * x a * y b| ≤ Mv * (∑ a, |x a|) * (∑ b, |y b|) := by
  have h1 : |∑ a, ∑ b, U a b * x a * y b| ≤ ∑ a, ∑ b, Mv * |x a| * |y b| := by
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun a _ => ?_))
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun b _ => ?_))
    rw [abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hU a b) (abs_nonneg _)) (abs_nonneg _)
  have h2 : ∑ a, ∑ b, Mv * |x a| * |y b| = Mv * (∑ a, |x a|) * (∑ b, |y b|) := by
    have hinner : ∀ a, (∑ b, Mv * |x a| * |y b|) = Mv * |x a| * (∑ b, |y b|) := by
      intro a; rw [Finset.mul_sum]
    calc ∑ a, ∑ b, Mv * |x a| * |y b|
        = ∑ a, Mv * |x a| * (∑ b, |y b|) := Finset.sum_congr rfl (fun a _ => hinner a)
      _ = (∑ a, Mv * |x a|) * (∑ b, |y b|) := by rw [Finset.sum_mul]
      _ = Mv * (∑ a, |x a|) * (∑ b, |y b|) := by rw [← Finset.mul_sum]
  exact h1.trans (le_of_eq h2)

/-- The reconstruction `D.Rstar i u` is bounded pointwise by a uniform sup bound `Mv` of the
coefficient family `u`, a lower bound `d₀` for the chart density on the closed `σ i`-ball, and the
`g₀`-lengths of the two arguments: `|Rstar i u x v w| ≤ (√d₀)⁻¹ * Mv * n * √⟪v,v⟫ * √⟪w,w⟫`. -/
theorem Rstar_abs_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (u : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
    (Mv : ℝ) (hMv : 0 ≤ Mv)
    (hu : ∀ (a b : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ), |u a b z| ≤ Mv)
    (d₀ : ℝ) (hd₀ : 0 < d₀)
    (hdens : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ D.σ i → d₀ ≤ D.dens i z) :
    ∀ (x : M) (v w : TangentSpace I x),
      |(D.Rstar i u) x v w| ≤ (Real.sqrt d₀)⁻¹ * Mv * (Module.finrank ℝ E : ℝ)
        * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w) := by
  intro x v w
  -- The numerical factors.
  have hd0pos : 0 < Real.sqrt d₀ := Real.sqrt_pos.mpr hd₀
  have hpd : 0 < (Real.sqrt d₀)⁻¹ := inv_pos.mpr hd0pos
  by_cases hz : D.ζ i x = 0
  · -- Off the support of the weight `ζ i` the reconstruction vanishes identically.
    rw [Work.Diff.STE.B3.Rstar_apply D i u x v w, hz]
    simp only [zero_mul, abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (le_of_lt hpd) hMv)
      (Nat.cast_nonneg _)) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  · -- On the support of `ζ i` the chart `i` is genuine: `‖coord i x‖ < σ i ≤ 2 σ i`, so `χ i = 1`
    -- there and the frame `e i` is `g₀`-orthonormal at `x`.
    have hsupp := D.hζsupp i x hz
    have hle2 : ‖Work.Diff.STE.coord (I := I) (D.x₀ i) x‖ ≤ 2 * D.σ i := by
      have := D.hσ i; linarith [hsupp.2]
    have hpt : D.pt i (Work.Diff.STE.coord (I := I) (D.x₀ i) x) = x := D.pt_coord i hsupp.1
    have hon : Submission.Diff.IsONFrame g₀ x (fun a => D.e i a x) := by
      rw [← hpt]
      exact D.heON i _ hle2
    have hχ : D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) x) = 1 :=
      D.hχ1 i _ (le_of_lt hsupp.2)
    have hζle : D.ζ i x ≤ 1 := by
      have h1 : (D.ζ i x) ^ 2 ≤ 1 := by
        rw [← D.hζsq x]
        exact Finset.single_le_sum (f := fun k : ι₀ => (D.ζ k x) ^ 2)
          (fun k _ => sq_nonneg _) (Finset.mem_univ i)
      nlinarith [D.hζnn i x]
    have hdensx : d₀ ≤ D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x) :=
      hdens _ (le_of_lt hsupp.2)
    have hinv : (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹
        ≤ (Real.sqrt d₀)⁻¹ :=
      inv_anti₀ hd0pos (Real.sqrt_le_sqrt hdensx)
    -- The coefficient `ζ · χ · (√dens)⁻¹` is bounded by `(√d₀)⁻¹`.
    have hcoeff : |D.ζ i x * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
        * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹|
        ≤ (Real.sqrt d₀)⁻¹ := by
      rw [abs_mul, abs_mul, hχ, abs_one, mul_one, abs_of_nonneg (D.hζnn i x),
        abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
      simpa using mul_le_mul hζle hinv (inv_nonneg.mpr (Real.sqrt_nonneg _)) (by norm_num)
    -- The frame sums, by Bessel plus `ℓ¹`-`ℓ²` Cauchy–Schwarz.
    have hSx : ∑ a, |g₀.inner x v (D.e i a x)|
        ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt (g₀.inner x v v) := by
      refine (sum_abs_le_sqrt_card_mul_sqrt_sum_sq (fun a => g₀.inner x v (D.e i a x))).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
      exact sum_sq_inner_le_of_isONFrame g₀ x _ hon v
    have hSw : ∑ b, |g₀.inner x w (D.e i b x)|
        ≤ Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt (g₀.inner x w w) := by
      refine (sum_abs_le_sqrt_card_mul_sqrt_sum_sq (fun b => g₀.inner x w (D.e i b x))).trans ?_
      refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (Real.sqrt_nonneg _)
      exact sum_sq_inner_le_of_isONFrame g₀ x _ hon w
    -- The coefficient double sum.
    have hsum : |∑ a, ∑ b, u a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
          * g₀.inner x v (D.e i a x) * g₀.inner x w (D.e i b x)|
        ≤ Mv * (∑ a, |g₀.inner x v (D.e i a x)|) * (∑ b, |g₀.inner x w (D.e i b x)|) :=
      abs_double_sum_mul_le _ _ _ (fun a b => hu a b _)
    have hsum2 : Mv * (∑ a, |g₀.inner x v (D.e i a x)|) * (∑ b, |g₀.inner x w (D.e i b x)|)
        ≤ Mv * (Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt (g₀.inner x v v))
          * (Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt (g₀.inner x w w)) := by
      refine mul_le_mul (mul_le_mul_of_nonneg_left hSx hMv) hSw
        (Finset.sum_nonneg (fun b _ => abs_nonneg _)) ?_
      exact mul_nonneg hMv (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    -- `√n · √n = n` collects the two frame sums into the factor `n`.
    have hfinal : Mv * (Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt (g₀.inner x v v))
          * (Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt (g₀.inner x w w))
        = Mv * (Module.finrank ℝ E : ℝ) * Real.sqrt (g₀.inner x v v)
          * Real.sqrt (g₀.inner x w w) := by
      have hnn : Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt (Module.finrank ℝ E : ℝ)
          = (Module.finrank ℝ E : ℝ) := Real.mul_self_sqrt (Nat.cast_nonneg _)
      calc Mv * (Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt (g₀.inner x v v))
            * (Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt (g₀.inner x w w))
          = Mv * (Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt (Module.finrank ℝ E : ℝ))
            * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := by ring
        _ = Mv * (Module.finrank ℝ E : ℝ)
            * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x w w)) := by rw [hnn]
        _ = Mv * (Module.finrank ℝ E : ℝ) * Real.sqrt (g₀.inner x v v)
            * Real.sqrt (g₀.inner x w w) := by ring
    rw [Work.Diff.STE.B3.Rstar_apply D i u x v w, abs_mul]
    calc |D.ζ i x * D.χ i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
            * (Real.sqrt (D.dens i (Work.Diff.STE.coord (I := I) (D.x₀ i) x)))⁻¹|
          * |∑ a, ∑ b, u a b (Work.Diff.STE.coord (I := I) (D.x₀ i) x)
              * g₀.inner x v (D.e i a x) * g₀.inner x w (D.e i b x)|
        ≤ (Real.sqrt d₀)⁻¹ * (Mv * (∑ a, |g₀.inner x v (D.e i a x)|)
            * (∑ b, |g₀.inner x w (D.e i b x)|)) :=
          mul_le_mul hcoeff hsum (abs_nonneg _) (le_of_lt hpd)
      _ ≤ (Real.sqrt d₀)⁻¹
            * (Mv * (Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt (g₀.inner x v v))
              * (Real.sqrt (Module.finrank ℝ E : ℝ) * Real.sqrt (g₀.inner x w w))) :=
          mul_le_mul_of_nonneg_left hsum2 (le_of_lt hpd)
      _ = (Real.sqrt d₀)⁻¹ * Mv * (Module.finrank ℝ E : ℝ) * Real.sqrt (g₀.inner x v v)
            * Real.sqrt (g₀.inner x w w) := by rw [hfinal]; ring

end Work.Diff.STE.Lead
